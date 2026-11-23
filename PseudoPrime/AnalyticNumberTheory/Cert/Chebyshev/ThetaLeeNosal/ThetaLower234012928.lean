/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis16384

/-! # Direct theta estimate up to 234012928 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell204712192 :
    ThetaLowerSegment 204712192 204744960 (20469224769031 / 100000) (20472550797011 / 100000) := by
  exact
    packedTile16384 204712192 204744960 12 1738 14307 28 _ _ (191371 / 10000) (1913713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204744960 :
    ThetaLowerSegment 204744960 204777728 (20472550797011 / 100000) (4095160443497 / 20000) := by
  exact
    packedTile16384 204744960 204777728 12 1699 14308 28 _ _ (956863 / 50000) (1913729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204777728 :
    ThetaLowerSegment 204777728 204810496 (4095160443497 / 20000) (20479172317147 / 100000) := by
  exact
    packedTile16384 204777728 204810496 12 1761 14310 28 _ _ (956871 / 50000) (382749 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204810496 :
    ThetaLowerSegment 204810496 204843264 (20479172317147 / 100000) (20482460153391 / 100000) := by
  exact
    packedTile16384 204810496 204843264 12 1718 14311 28 _ _ (956879 / 50000) (1913761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204843264 :
    ThetaLowerSegment 204843264 204876032 (20482460153391 / 100000) (20485761413541 / 100000) := by
  exact
    packedTile16384 204843264 204876032 12 1725 14312 28 _ _ (956887 / 50000) (1913777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204876032 :
    ThetaLowerSegment 204876032 204908800 (20485761413541 / 100000) (20489051218551 / 100000) := by
  exact
    packedTile16384 204876032 204908800 12 1719 14313 28 _ _ (191379 / 10000) (1913793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204908800 :
    ThetaLowerSegment 204908800 204941568 (20489051218551 / 100000) (20492319999199 / 100000) := by
  exact
    packedTile16384 204908800 204941568 12 1708 14314 28 _ _ (956903 / 50000) (1913809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204941568 :
    ThetaLowerSegment 204941568 204974336 (20492319999199 / 100000) (20495565841311 / 100000) := by
  exact
    packedTile16384 204941568 204974336 12 1696 14315 28 _ _ (956911 / 50000) (76553 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell204974336 :
    ThetaLowerSegment 204974336 205007104 (20495565841311 / 100000) (20498888264079 / 100000) := by
  exact
    packedTile16384 204974336 205007104 12 1736 14316 28 _ _ (956919 / 50000) (1913841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205007104 :
    ThetaLowerSegment 205007104 205039872 (20498888264079 / 100000) (20502051864741 / 100000) := by
  exact
    packedTile16384 205007104 205039872 12 1653 14318 28 _ _ (956927 / 50000) (1913857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205039872 :
    ThetaLowerSegment 205039872 205072640 (20502051864741 / 100000) (20505297788261 / 100000) := by
  exact
    packedTile16384 205039872 205072640 12 1696 14319 28 _ _ (191387 / 10000) (1913873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205072640 :
    ThetaLowerSegment 205072640 205105408 (20505297788261 / 100000) (4101730948861 / 20000) := by
  exact
    packedTile16384 205072640 205105408 12 1754 14320 28 _ _ (956943 / 50000) (1913889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205105408 :
    ThetaLowerSegment 205105408 205138176 (4101730948861 / 20000) (20511772490663 / 100000) := by
  exact
    packedTile16384 205105408 205138176 12 1629 14321 28 _ _ (956951 / 50000) (382781 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205138176 :
    ThetaLowerSegment 205138176 205170944 (20511772490663 / 100000) (20515135244589 / 100000) := by
  exact
    packedTile16384 205138176 205170944 12 1757 14322 28 _ _ (956959 / 50000) (1913921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205170944 :
    ThetaLowerSegment 205170944 205203712 (20515135244589 / 100000) (20518352567643 / 100000) := by
  exact
    packedTile16384 205170944 205203712 12 1681 14323 28 _ _ (956967 / 50000) (1913937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205203712 :
    ThetaLowerSegment 205203712 205236480 (20518352567643 / 100000) (20521665615093 / 100000) := by
  exact
    packedTile16384 205203712 205236480 12 1731 14324 28 _ _ (38279 / 2000) (1913953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205236480 :
    ThetaLowerSegment 205236480 205269248 (20521665615093 / 100000) (20524972948341 / 100000) := by
  exact
    packedTile16384 205236480 205269248 12 1728 14326 28 _ _ (956983 / 50000) (1913969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205269248 :
    ThetaLowerSegment 205269248 205302016 (20524972948341 / 100000) (4105651851087 / 20000) := by
  exact
    packedTile16384 205269248 205302016 12 1717 14327 28 _ _ (956991 / 50000) (382797 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205302016 :
    ThetaLowerSegment 205302016 205334784 (4105651851087 / 20000) (20531516880031 / 100000) := by
  exact
    packedTile16384 205302016 205334784 12 1702 14328 28 _ _ (956999 / 50000) (1914001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205334784 :
    ThetaLowerSegment 205334784 205367552 (20531516880031 / 100000) (20534866404531 / 100000) := by
  exact
    packedTile16384 205334784 205367552 12 1750 14329 28 _ _ (957007 / 50000) (1914017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205367552 :
    ThetaLowerSegment 205367552 205400320 (20534866404531 / 100000) (20538173848371 / 100000) := by
  exact
    packedTile16384 205367552 205400320 12 1728 14330 28 _ _ (191403 / 10000) (1914033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205400320 :
    ThetaLowerSegment 205400320 205433088 (20538173848371 / 100000) (20541393273743 / 100000) := by
  exact
    packedTile16384 205400320 205433088 12 1682 14331 28 _ _ (957023 / 50000) (1914049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205433088 :
    ThetaLowerSegment 205433088 205465856 (20541393273743 / 100000) (20544673976011 / 100000) := by
  exact
    packedTile16384 205433088 205465856 12 1714 14332 28 _ _ (957031 / 50000) (382813 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205465856 :
    ThetaLowerSegment 205465856 205498624 (20544673976011 / 100000) (20547992987263 / 100000) := by
  exact
    packedTile16384 205465856 205498624 12 1734 14334 28 _ _ (957039 / 50000) (1914081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205498624 :
    ThetaLowerSegment 205498624 205531392 (20547992987263 / 100000) (1027561294517 / 5000) := by
  exact
    packedTile16384 205498624 205531392 12 1689 14335 28 _ _ (1914093 / 100000) (119631 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205531392 :
    ThetaLowerSegment 205531392 205564160 (1027561294517 / 5000) (2055449901673 / 10000) := by
  exact
    packedTile16384 205531392 205564160 12 1710 14336 28 _ _ (1914109 / 100000) (59816 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205564160 :
    ThetaLowerSegment 205564160 205596928 (2055449901673 / 10000) (4111554816921 / 20000) := by
  exact
    packedTile16384 205564160 205596928 12 1711 14337 28 _ _ (15313 / 800) (119633 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205596928 :
    ThetaLowerSegment 205596928 205629696 (4111554816921 / 20000) (20561039609151 / 100000) := by
  exact
    packedTile16384 205596928 205629696 12 1706 14338 28 _ _ (1914141 / 100000) (59817 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205629696 :
    ThetaLowerSegment 205629696 205662464 (20561039609151 / 100000) (1285266560231 / 6250) := by
  exact
    packedTile16384 205629696 205662464 12 1685 14339 28 _ _ (1914157 / 100000) (23927 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205662464 :
    ThetaLowerSegment 205662464 205695232 (1285266560231 / 6250) (20567570740467 / 100000) := by
  exact
    packedTile16384 205662464 205695232 12 1727 14340 28 _ _ (1914173 / 100000) (59818 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205695232 :
    ThetaLowerSegment 205695232 205728000 (20567570740467 / 100000) (2057083826109 / 10000) := by
  exact
    packedTile16384 205695232 205728000 12 1707 14342 28 _ _ (1914189 / 100000) (119637 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205728000 :
    ThetaLowerSegment 205728000 205760768 (2057083826109 / 10000) (4114822693169 / 20000) := by
  exact
    packedTile16384 205728000 205760768 12 1711 14343 28 _ _ (382841 / 20000) (59819 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205760768 :
    ThetaLowerSegment 205760768 205793536 (4114822693169 / 20000) (4115492670519 / 20000) := by
  exact
    packedTile16384 205760768 205793536 12 1750 14344 28 _ _ (1914221 / 100000) (119639 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205793536 :
    ThetaLowerSegment 205793536 205826304 (4115492670519 / 20000) (20580652471437 / 100000) := by
  exact
    packedTile16384 205793536 205826304 12 1666 14345 28 _ _ (1914237 / 100000) (11964 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205826304 :
    ThetaLowerSegment 205826304 205859072 (20580652471437 / 100000) (5145976196821 / 25000) := by
  exact
    packedTile16384 205826304 205859072 12 1699 14346 28 _ _ (1914253 / 100000) (119641 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205859072 :
    ThetaLowerSegment 205859072 205891840 (5145976196821 / 25000) (20587218386923 / 100000) := by
  exact
    packedTile16384 205859072 205891840 12 1731 14347 28 _ _ (1914269 / 100000) (59821 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205891840 :
    ThetaLowerSegment 205891840 205924608 (20587218386923 / 100000) (20590445871433 / 100000) := by
  exact
    packedTile16384 205891840 205924608 12 1686 14348 28 _ _ (382857 / 20000) (119643 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205924608 :
    ThetaLowerSegment 205924608 205957376 (20590445871433 / 100000) (5148434138713 / 25000) := by
  exact
    packedTile16384 205924608 205957376 12 1719 14350 28 _ _ (1914301 / 100000) (59822 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205957376 :
    ThetaLowerSegment 205957376 205990144 (5148434138713 / 25000) (5149272609121 / 25000) := by
  exact
    packedTile16384 205957376 205990144 12 1752 14351 28 _ _ (478579 / 25000) (1914319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell205990144 :
    ThetaLowerSegment 205990144 206022912 (5149272609121 / 25000) (2575041903653 / 12500) := by
  exact
    packedTile16384 205990144 206022912 12 1695 14352 28 _ _ (478583 / 25000) (382867 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206022912 :
    ThetaLowerSegment 206022912 206055680 (2575041903653 / 12500) (5150889269227 / 25000) := by
  exact
    packedTile16384 206022912 206055680 12 1683 14353 28 _ _ (478587 / 25000) (1914351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206055680 :
    ThetaLowerSegment 206055680 206088448 (5150889269227 / 25000) (5151702873927 / 25000) := by
  exact
    packedTile16384 206055680 206088448 12 1700 14354 28 _ _ (478591 / 25000) (1914367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206088448 :
    ThetaLowerSegment 206088448 206121216 (5151702873927 / 25000) (5152519356997 / 25000) := by
  exact
    packedTile16384 206088448 206121216 12 1706 14355 28 _ _ (95719 / 5000) (1914383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206121216 :
    ThetaLowerSegment 206121216 206153984 (5152519356997 / 25000) (2576669119943 / 12500) := by
  exact
    packedTile16384 206121216 206153984 12 1711 14356 28 _ _ (478599 / 25000) (1914399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206153984 :
    ThetaLowerSegment 206153984 206186752 (2576669119943 / 12500) (257707545389 / 1250) := by
  exact
    packedTile16384 206153984 206186752 12 1698 14358 28 _ _ (478603 / 25000) (382883 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206186752 :
    ThetaLowerSegment 206186752 206219520 (257707545389 / 1250) (5154980333711 / 25000) := by
  exact
    packedTile16384 206186752 206219520 12 1733 14359 28 _ _ (478607 / 25000) (1914431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206219520 :
    ThetaLowerSegment 206219520 206252288 (5154980333711 / 25000) (2577905840509 / 12500) := by
  exact
    packedTile16384 206219520 206252288 12 1737 14360 28 _ _ (478611 / 25000) (1914447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206252288 :
    ThetaLowerSegment 206252288 206285056 (2577905840509 / 12500) (2578315534949 / 12500) := by
  exact
    packedTile16384 206252288 206285056 12 1712 14361 28 _ _ (95723 / 5000) (1914463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206285056 :
    ThetaLowerSegment 206285056 206317824 (2578315534949 / 12500) (1289363573537 / 6250) := by
  exact
    packedTile16384 206285056 206317824 12 1720 14362 28 _ _ (76579 / 4000) (957239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206317824 :
    ThetaLowerSegment 206317824 206350592 (1289363573537 / 6250) (10316518675227 / 50000) := by
  exact
    packedTile16384 206317824 206350592 12 1682 14363 28 _ _ (1914491 / 100000) (957247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206350592 :
    ThetaLowerSegment 206350592 206383360 (10316518675227 / 50000) (1289773276353 / 6250) := by
  exact
    packedTile16384 206350592 206383360 12 1742 14364 28 _ _ (1914507 / 100000) (191451 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206383360 :
    ThetaLowerSegment 206383360 206416128 (1289773276353 / 6250) (20639629025271 / 100000) := by
  exact
    packedTile16384 206383360 206416128 12 1701 14366 28 _ _ (1914523 / 100000) (957263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206416128 :
    ThetaLowerSegment 206416128 206448896 (20639629025271 / 100000) (20642941177741 / 100000) := by
  exact
    packedTile16384 206416128 206448896 12 1730 14367 28 _ _ (1914539 / 100000) (957271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206448896 :
    ThetaLowerSegment 206448896 206481664 (20642941177741 / 100000) (20646192092131 / 100000) := by
  exact
    packedTile16384 206448896 206481664 12 1698 14368 28 _ _ (382911 / 20000) (957279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206481664 :
    ThetaLowerSegment 206481664 206514432 (20646192092131 / 100000) (825978946673 / 4000) := by
  exact
    packedTile16384 206481664 206514432 12 1714 14369 28 _ _ (1914571 / 100000) (957287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206514432 :
    ThetaLowerSegment 206514432 206547200 (825978946673 / 4000) (5163176851067 / 25000) := by
  exact
    packedTile16384 206514432 206547200 12 1689 14370 28 _ _ (1914587 / 100000) (191459 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206547200 :
    ThetaLowerSegment 206547200 206579968 (5163176851067 / 25000) (10328018448573 / 50000) := by
  exact
    packedTile16384 206547200 206579968 12 1739 14371 28 _ _ (957301 / 50000) (382921 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206579968 :
    ThetaLowerSegment 206579968 206612736 (10328018448573 / 50000) (10329607581513 / 50000) := by
  exact
    packedTile16384 206579968 206612736 12 1660 14372 28 _ _ (957309 / 50000) (1914621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206612736 :
    ThetaLowerSegment 206612736 206645504 (10329607581513 / 50000) (10331263739923 / 50000) := by
  exact
    packedTile16384 206612736 206645504 12 1730 14374 28 _ _ (957317 / 50000) (1914637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206645504 :
    ThetaLowerSegment 206645504 206678272 (10331263739923 / 50000) (5166454690799 / 25000) := by
  exact
    packedTile16384 206645504 206678272 12 1719 14375 28 _ _ (38293 / 2000) (1914653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206678272 :
    ThetaLowerSegment 206678272 206711040 (5166454690799 / 25000) (5167268423849 / 25000) := by
  exact
    packedTile16384 206678272 206711040 12 1700 14376 28 _ _ (957333 / 50000) (1914669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206711040 :
    ThetaLowerSegment 206711040 206743808 (5167268423849 / 25000) (1033621410913 / 5000) := by
  exact
    packedTile16384 206711040 206743808 12 1752 14377 28 _ _ (957341 / 50000) (382937 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206743808 :
    ThetaLowerSegment 206743808 206776576 (1033621410913 / 5000) (10337842559779 / 50000) := by
  exact
    packedTile16384 206743808 206776576 12 1701 14378 28 _ _ (957349 / 50000) (1914701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206776576 :
    ThetaLowerSegment 206776576 206809344 (10337842559779 / 50000) (20679007146613 / 100000) := by
  exact
    packedTile16384 206776576 206809344 12 1735 14379 28 _ _ (1914713 / 100000) (478679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206809344 :
    ThetaLowerSegment 206809344 206842112 (20679007146613 / 100000) (10341158856527 / 50000) := by
  exact
    packedTile16384 206809344 206842112 12 1729 14380 28 _ _ (1914729 / 100000) (478683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206842112 :
    ThetaLowerSegment 206842112 206874880 (10341158856527 / 50000) (10342790219267 / 50000) := by
  exact
    packedTile16384 206842112 206874880 12 1704 14382 28 _ _ (382949 / 20000) (478687 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206874880 :
    ThetaLowerSegment 206874880 206907648 (10342790219267 / 50000) (5172209840439 / 25000) := by
  exact
    packedTile16384 206874880 206907648 12 1702 14383 28 _ _ (1914761 / 100000) (478691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206907648 :
    ThetaLowerSegment 206907648 206940416 (5172209840439 / 25000) (20692150011189 / 100000) := by
  exact
    packedTile16384 206907648 206940416 12 1729 14384 28 _ _ (1914777 / 100000) (95739 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206940416 :
    ThetaLowerSegment 206940416 206973184 (20692150011189 / 100000) (20695477921423 / 100000) := by
  exact
    packedTile16384 206940416 206973184 12 1738 14385 28 _ _ (1914793 / 100000) (478699 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell206973184 :
    ThetaLowerSegment 206973184 207005952 (20695477921423 / 100000) (20698735009831 / 100000) := by
  exact
    packedTile16384 206973184 207005952 12 1701 14386 28 _ _ (239351 / 12500) (1914811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207005952 :
    ThetaLowerSegment 207005952 207038720 (20698735009831 / 100000) (4140388850971 / 20000) := by
  exact
    packedTile16384 207005952 207038720 12 1676 14387 28 _ _ (239353 / 12500) (1914827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207038720 :
    ThetaLowerSegment 207038720 207071488 (4140388850971 / 20000) (165641641819 / 800) := by
  exact
    packedTile16384 207038720 207071488 12 1703 14388 28 _ _ (47871 / 2500) (1914843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207071488 :
    ThetaLowerSegment 207071488 207104256 (165641641819 / 800) (828338419303 / 4000) := by
  exact
    packedTile16384 207071488 207104256 12 1700 14389 28 _ _ (239357 / 12500) (1914859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207104256 :
    ThetaLowerSegment 207104256 207137024 (828338419303 / 4000) (20711757892159 / 100000) := by
  exact
    packedTile16384 207104256 207137024 12 1722 14391 28 _ _ (239359 / 12500) (15319 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207137024 :
    ThetaLowerSegment 207137024 207169792 (20711757892159 / 100000) (20714982563551 / 100000) := by
  exact
    packedTile16384 207137024 207169792 12 1684 14392 28 _ _ (239361 / 12500) (1914891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207169792 :
    ThetaLowerSegment 207169792 207202560 (20714982563551 / 100000) (20718264707293 / 100000) := by
  exact
    packedTile16384 207169792 207202560 12 1714 14393 28 _ _ (1914903 / 100000) (957453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207202560 :
    ThetaLowerSegment 207202560 207235328 (20718264707293 / 100000) (20721562197811 / 100000) := by
  exact
    packedTile16384 207202560 207235328 12 1722 14394 28 _ _ (1914919 / 100000) (957461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207235328 :
    ThetaLowerSegment 207235328 207268096 (20721562197811 / 100000) (10362459539433 / 50000) := by
  exact
    packedTile16384 207235328 207268096 12 1753 14395 28 _ _ (382987 / 20000) (957469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207268096 :
    ThetaLowerSegment 207268096 207300864 (10362459539433 / 50000) (1036408150293 / 5000) := by
  exact
    packedTile16384 207268096 207300864 12 1694 14396 28 _ _ (1914951 / 100000) (957477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207300864 :
    ThetaLowerSegment 207300864 207333632 (1036408150293 / 5000) (4146297094721 / 20000) := by
  exact
    packedTile16384 207300864 207333632 12 1735 14397 28 _ _ (1914967 / 100000) (191497 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207333632 :
    ThetaLowerSegment 207333632 207366400 (4146297094721 / 20000) (4146948188601 / 20000) := by
  exact
    packedTile16384 207333632 207366400 12 1700 14399 28 _ _ (957491 / 50000) (382997 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207366400 :
    ThetaLowerSegment 207366400 207399168 (4146948188601 / 20000) (4147606947913 / 20000) := by
  exact
    packedTile16384 207366400 207399168 12 1720 14400 28 _ _ (957499 / 50000) (1915001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207399168 :
    ThetaLowerSegment 207399168 207431936 (4147606947913 / 20000) (20741324733617 / 100000) := by
  exact
    packedTile16384 207399168 207431936 12 1718 14401 28 _ _ (957507 / 50000) (1915017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207431936 :
    ThetaLowerSegment 207431936 207464704 (20741324733617 / 100000) (20744656885817 / 100000) := by
  exact
    packedTile16384 207431936 207464704 12 1740 14402 28 _ _ (191503 / 10000) (1915033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207464704 :
    ThetaLowerSegment 207464704 207497472 (20744656885817 / 100000) (20747973745489 / 100000) := by
  exact
    packedTile16384 207464704 207497472 12 1732 14403 28 _ _ (957523 / 50000) (1915049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207497472 :
    ThetaLowerSegment 207497472 207530240 (20747973745489 / 100000) (10375607971881 / 50000) := by
  exact
    packedTile16384 207497472 207530240 12 1693 14404 28 _ _ (1915061 / 100000) (239383 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207530240 :
    ThetaLowerSegment 207530240 207563008 (10375607971881 / 50000) (20754481150047 / 100000) := by
  exact
    packedTile16384 207530240 207563008 12 1705 14405 28 _ _ (1915077 / 100000) (47877 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207563008 :
    ThetaLowerSegment 207563008 207595776 (20754481150047 / 100000) (2594721170591 / 12500) := by
  exact
    packedTile16384 207563008 207595776 12 1717 14407 28 _ _ (1915093 / 100000) (239387 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207595776 :
    ThetaLowerSegment 207595776 207628544 (2594721170591 / 12500) (1297566459513 / 6250) := by
  exact
    packedTile16384 207595776 207628544 12 1720 14408 28 _ _ (1915109 / 100000) (239389 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207628544 :
    ThetaLowerSegment 207628544 207661312 (1297566459513 / 6250) (20764347791583 / 100000) := by
  exact
    packedTile16384 207628544 207661312 12 1715 14409 28 _ _ (15321 / 800) (239391 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207661312 :
    ThetaLowerSegment 207661312 207694080 (20764347791583 / 100000) (20767680135183 / 100000) := by
  exact
    packedTile16384 207661312 207694080 12 1740 14410 28 _ _ (95757 / 5000) (1915143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207694080 :
    ThetaLowerSegment 207694080 207726848 (20767680135183 / 100000) (20770943561007 / 100000) := by
  exact
    packedTile16384 207694080 207726848 12 1704 14411 28 _ _ (478789 / 25000) (1915159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207726848 :
    ThetaLowerSegment 207726848 207759616 (20770943561007 / 100000) (20774239572019 / 100000) := by
  exact
    packedTile16384 207726848 207759616 12 1721 14412 28 _ _ (478793 / 25000) (76607 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207759616 :
    ThetaLowerSegment 207759616 207792384 (20774239572019 / 100000) (20777522204251 / 100000) := by
  exact
    packedTile16384 207759616 207792384 12 1714 14413 28 _ _ (478797 / 25000) (1915191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207792384 :
    ThetaLowerSegment 207792384 207825152 (20777522204251 / 100000) (20780789540569 / 100000) := by
  exact
    packedTile16384 207792384 207825152 12 1706 14415 28 _ _ (1915203 / 100000) (957603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207825152 :
    ThetaLowerSegment 207825152 207857920 (20780789540569 / 100000) (10392029409701 / 50000) := by
  exact
    packedTile16384 207825152 207857920 12 1707 14416 28 _ _ (1915219 / 100000) (957611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207857920 :
    ThetaLowerSegment 207857920 207890688 (10392029409701 / 50000) (5196818145933 / 25000) := by
  exact
    packedTile16384 207857920 207890688 12 1678 14417 28 _ _ (383047 / 20000) (957619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207890688 :
    ThetaLowerSegment 207890688 207923456 (5196818145933 / 25000) (1039529106873 / 5000) := by
  exact
    packedTile16384 207890688 207923456 12 1728 14418 28 _ _ (1915251 / 100000) (957627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207923456 :
    ThetaLowerSegment 207923456 207956224 (1039529106873 / 5000) (2079385724403 / 10000) := by
  exact
    packedTile16384 207923456 207956224 12 1710 14419 28 _ _ (1915267 / 100000) (191527 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207956224 :
    ThetaLowerSegment 207956224 207988992 (2079385724403 / 10000) (10398548950587 / 50000) := by
  exact
    packedTile16384 207956224 207988992 12 1692 14420 28 _ _ (957641 / 50000) (383057 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell207988992 :
    ThetaLowerSegment 207988992 208021760 (10398548950587 / 50000) (10400184615079 / 50000) := by
  exact
    packedTile16384 207988992 208021760 12 1708 14421 28 _ _ (957649 / 50000) (1915301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208021760 :
    ThetaLowerSegment 208021760 208054528 (10400184615079 / 50000) (2080354482077 / 10000) := by
  exact
    packedTile16384 208021760 208054528 12 1658 14422 28 _ _ (957657 / 50000) (1915317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208054528 :
    ThetaLowerSegment 208054528 208087296 (2080354482077 / 10000) (26008527438 / 125) := by
  exact
    packedTile16384 208054528 208087296 12 1711 14424 28 _ _ (191533 / 10000) (1915333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208087296 :
    ThetaLowerSegment 208087296 208120064 (26008527438 / 125) (83240541989 / 400) := by
  exact
    packedTile16384 208087296 208120064 12 1730 14425 28 _ _ (383069 / 20000) (478837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208120064 :
    ThetaLowerSegment 208120064 208152832 (83240541989 / 400) (20813435664253 / 100000) := by
  exact
    packedTile16384 208120064 208152832 12 1723 14426 28 _ _ (1915361 / 100000) (478841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208152832 :
    ThetaLowerSegment 208152832 208185600 (20813435664253 / 100000) (10408381337051 / 50000) := by
  exact
    packedTile16384 208152832 208185600 12 1737 14427 28 _ _ (1915377 / 100000) (95769 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208185600 :
    ThetaLowerSegment 208185600 208218368 (10408381337051 / 50000) (832801596461 / 4000) := by
  exact
    packedTile16384 208185600 208218368 12 1711 14428 28 _ _ (1915393 / 100000) (478849 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208218368 :
    ThetaLowerSegment 208218368 208251136 (832801596461 / 4000) (20823321005429 / 100000) := by
  exact
    packedTile16384 208218368 208251136 12 1713 14429 28 _ _ (119713 / 6250) (1915411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208251136 :
    ThetaLowerSegment 208251136 208283904 (20823321005429 / 100000) (20826519763509 / 100000) := by
  exact
    packedTile16384 208251136 208283904 12 1670 14430 28 _ _ (59857 / 3125) (1915427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208283904 :
    ThetaLowerSegment 208283904 208316672 (20826519763509 / 100000) (20829821982069 / 100000) := by
  exact
    packedTile16384 208283904 208316672 12 1724 14432 28 _ _ (23943 / 1250) (1915443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208316672 :
    ThetaLowerSegment 208316672 208349440 (20829821982069 / 100000) (5208233649111 / 25000) := by
  exact
    packedTile16384 208316672 208349440 12 1625 14433 28 _ _ (383091 / 20000) (957729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208349440 :
    ThetaLowerSegment 208349440 208382208 (5208233649111 / 25000) (2604523862143 / 12500) := by
  exact
    packedTile16384 208349440 208382208 12 1700 14434 28 _ _ (1915471 / 100000) (957737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208382208 :
    ThetaLowerSegment 208382208 208414976 (2604523862143 / 12500) (10419737020931 / 50000) := by
  exact
    packedTile16384 208382208 208414976 12 1714 14435 28 _ _ (1915487 / 100000) (191549 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208414976 :
    ThetaLowerSegment 208414976 208447744 (10419737020931 / 50000) (4168550293499 / 20000) := by
  exact
    packedTile16384 208414976 208447744 12 1711 14436 28 _ _ (1915503 / 100000) (957753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208447744 :
    ThetaLowerSegment 208447744 208480512 (4168550293499 / 20000) (20846061482599 / 100000) := by
  exact
    packedTile16384 208447744 208480512 12 1728 14437 28 _ _ (957759 / 50000) (1915521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208480512 :
    ThetaLowerSegment 208480512 208513280 (20846061482599 / 100000) (4169857448371 / 20000) := by
  exact
    packedTile16384 208480512 208513280 12 1684 14438 28 _ _ (957767 / 50000) (1915537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208513280 :
    ThetaLowerSegment 208513280 208546048 (4169857448371 / 20000) (4170516780681 / 20000) := by
  exact
    packedTile16384 208513280 208546048 12 1721 14439 28 _ _ (38311 / 2000) (1915553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208546048 :
    ThetaLowerSegment 208546048 208578816 (4170516780681 / 20000) (20855823125511 / 100000) := by
  exact
    packedTile16384 208546048 208578816 12 1691 14441 28 _ _ (957783 / 50000) (1915569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208578816 :
    ThetaLowerSegment 208578816 208611584 (20855823125511 / 100000) (20859083444373 / 100000) := by
  exact
    packedTile16384 208578816 208611584 12 1702 14442 28 _ _ (1915581 / 100000) (59862 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208611584 :
    ThetaLowerSegment 208611584 208644352 (20859083444373 / 100000) (20862405089571 / 100000) := by
  exact
    packedTile16384 208611584 208644352 12 1734 14443 28 _ _ (1915597 / 100000) (4789 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208644352 :
    ThetaLowerSegment 208644352 208677120 (20862405089571 / 100000) (4173139222541 / 20000) := by
  exact
    packedTile16384 208644352 208677120 12 1718 14444 28 _ _ (1915613 / 100000) (59863 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208677120 :
    ThetaLowerSegment 208677120 208709888 (4173139222541 / 20000) (20868877970813 / 100000) := by
  exact
    packedTile16384 208677120 208709888 12 1661 14445 28 _ _ (478907 / 25000) (1915631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208709888 :
    ThetaLowerSegment 208709888 208742656 (20868877970813 / 100000) (20872234179101 / 100000) := by
  exact
    packedTile16384 208709888 208742656 12 1752 14446 28 _ _ (478911 / 25000) (1915647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208742656 :
    ThetaLowerSegment 208742656 208775424 (20872234179101 / 100000) (20875542523921 / 100000) := by
  exact
    packedTile16384 208742656 208775424 12 1727 14447 28 _ _ (95783 / 5000) (1915663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208775424 :
    ThetaLowerSegment 208775424 208808192 (20875542523921 / 100000) (2609865461287 / 12500) := by
  exact
    packedTile16384 208775424 208808192 12 1765 14449 28 _ _ (76627 / 4000) (957839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208808192 :
    ThetaLowerSegment 208808192 208840960 (2609865461287 / 12500) (20882193774833 / 100000) := by
  exact
    packedTile16384 208808192 208840960 12 1707 14450 28 _ _ (1915691 / 100000) (957847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208840960 :
    ThetaLowerSegment 208840960 208873728 (20882193774833 / 100000) (20885396836937 / 100000) := by
  exact
    packedTile16384 208840960 208873728 12 1672 14451 28 _ _ (1915707 / 100000) (191571 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208873728 :
    ThetaLowerSegment 208873728 208906496 (20885396836937 / 100000) (130554096761 / 625) := by
  exact
    packedTile16384 208873728 208906496 12 1701 14452 28 _ _ (1915723 / 100000) (957863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208906496 :
    ThetaLowerSegment 208906496 208939264 (130554096761 / 625) (10445985812119 / 50000) := by
  exact
    packedTile16384 208906496 208939264 12 1731 14453 28 _ _ (957869 / 50000) (1915741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208939264 :
    ThetaLowerSegment 208939264 208972032 (10445985812119 / 50000) (5223800875309 / 25000) := by
  exact
    packedTile16384 208939264 208972032 12 1687 14454 28 _ _ (957877 / 50000) (1915757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell208972032 :
    ThetaLowerSegment 208972032 209004800 (5223800875309 / 25000) (10449248354933 / 50000) := by
  exact
    packedTile16384 208972032 209004800 12 1719 14455 28 _ _ (191577 / 10000) (1915773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209004800 :
    ThetaLowerSegment 209004800 209037568 (10449248354933 / 50000) (20901682660321 / 100000) := by
  exact
    packedTile16384 209004800 209037568 12 1663 14456 28 _ _ (383157 / 20000) (478947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209037568 :
    ThetaLowerSegment 209037568 209070336 (20901682660321 / 100000) (1306559079339 / 6250) := by
  exact
    packedTile16384 209037568 209070336 12 1703 14458 28 _ _ (1915801 / 100000) (478951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209070336 :
    ThetaLowerSegment 209070336 209103104 (1306559079339 / 6250) (20908204074141 / 100000) := by
  exact
    packedTile16384 209070336 209103104 12 1701 14459 28 _ _ (1915817 / 100000) (95791 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209103104 :
    ThetaLowerSegment 209103104 209135872 (20908204074141 / 100000) (20911535705989 / 100000) := by
  exact
    packedTile16384 209103104 209135872 12 1739 14460 28 _ _ (239479 / 12500) (383167 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209135872 :
    ThetaLowerSegment 209135872 209168640 (20911535705989 / 100000) (836592242341 / 4000) := by
  exact
    packedTile16384 209135872 209168640 12 1707 14461 28 _ _ (239481 / 12500) (1915851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209168640 :
    ThetaLowerSegment 209168640 209201408 (836592242341 / 4000) (20918080270101 / 100000) := by
  exact
    packedTile16384 209168640 209201408 12 1709 14462 28 _ _ (239483 / 12500) (1915867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209201408 :
    ThetaLowerSegment 209201408 209234176 (20918080270101 / 100000) (1307580824949 / 6250) := by
  exact
    packedTile16384 209201408 209234176 12 1677 14463 28 _ _ (1915879 / 100000) (957941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209234176 :
    ThetaLowerSegment 209234176 209266944 (1307580824949 / 6250) (20924575127319 / 100000) := by
  exact
    packedTile16384 209234176 209266944 12 1713 14464 28 _ _ (383179 / 20000) (957949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209266944 :
    ThetaLowerSegment 209266944 209299712 (20924575127319 / 100000) (10463940036897 / 50000) := by
  exact
    packedTile16384 209266944 209299712 12 1725 14466 28 _ _ (1915911 / 100000) (957957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209299712 :
    ThetaLowerSegment 209299712 209332480 (10463940036897 / 50000) (10465606892517 / 50000) := by
  exact
    packedTile16384 209299712 209332480 12 1740 14467 28 _ _ (957963 / 50000) (1915929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209332480 :
    ThetaLowerSegment 209332480 209365248 (10465606892517 / 50000) (2616814848123 / 12500) := by
  exact
    packedTile16384 209332480 209365248 12 1725 14468 28 _ _ (957971 / 50000) (383189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209365248 :
    ThetaLowerSegment 209365248 209398016 (2616814848123 / 12500) (2093777016571 / 10000) := by
  exact
    packedTile16384 209365248 209398016 12 1697 14469 28 _ _ (957979 / 50000) (1915961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209398016 :
    ThetaLowerSegment 209398016 209430784 (2093777016571 / 10000) (5235276947669 / 25000) := by
  exact
    packedTile16384 209398016 209430784 12 1742 14470 28 _ _ (1915973 / 100000) (239497 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209430784 :
    ThetaLowerSegment 209430784 209463552 (5235276947669 / 25000) (2094441478769 / 10000) := by
  exact
    packedTile16384 209430784 209463552 12 1726 14471 28 _ _ (1915989 / 100000) (239499 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209463552 :
    ThetaLowerSegment 209463552 209496320 (2094441478769 / 10000) (4189543979263 / 20000) := by
  exact
    packedTile16384 209463552 209496320 12 1725 14472 28 _ _ (383201 / 20000) (239501 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209496320 :
    ThetaLowerSegment 209496320 209529088 (4189543979263 / 20000) (4190182780331 / 20000) := by
  exact
    packedTile16384 209496320 209529088 12 1667 14473 28 _ _ (95801 / 5000) (1916023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209529088 :
    ThetaLowerSegment 209529088 209561856 (4190182780331 / 20000) (20954169246819 / 100000) := by
  exact
    packedTile16384 209529088 209561856 12 1699 14475 28 _ _ (479009 / 25000) (1916039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209561856 :
    ThetaLowerSegment 209561856 209594624 (20954169246819 / 100000) (20957522336069 / 100000) := by
  exact
    packedTile16384 209561856 209594624 12 1750 14476 28 _ _ (1916051 / 100000) (958027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209594624 :
    ThetaLowerSegment 209594624 209627392 (20957522336069 / 100000) (20960863956917 / 100000) := by
  exact
    packedTile16384 209594624 209627392 12 1744 14477 28 _ _ (1916067 / 100000) (191607 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209627392 :
    ThetaLowerSegment 209627392 209660160 (20960863956917 / 100000) (655131006034 / 3125) := by
  exact
    packedTile16384 209627392 209660160 12 1737 14478 28 _ _ (1916083 / 100000) (958043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209660160 :
    ThetaLowerSegment 209660160 209692928 (655131006034 / 3125) (1048377651449 / 5000) := by
  exact
    packedTile16384 209660160 209692928 12 1754 14479 28 _ _ (958049 / 50000) (1916101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209692928 :
    ThetaLowerSegment 209692928 209725696 (1048377651449 / 5000) (1310678765109 / 6250) := by
  exact
    packedTile16384 209692928 209725696 12 1726 14480 28 _ _ (958057 / 50000) (1916117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209725696 :
    ThetaLowerSegment 209725696 209758464 (1310678765109 / 6250) (5243526541491 / 25000) := by
  exact
    packedTile16384 209725696 209758464 12 1694 14481 28 _ _ (191613 / 10000) (1916133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209758464 :
    ThetaLowerSegment 209758464 209791232 (5243526541491 / 25000) (20977423012959 / 100000) := by
  exact
    packedTile16384 209758464 209791232 12 1731 14483 28 _ _ (383229 / 20000) (479037 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209791232 :
    ThetaLowerSegment 209791232 209824000 (20977423012959 / 100000) (5245162936061 / 25000) := by
  exact
    packedTile16384 209791232 209824000 12 1685 14484 28 _ _ (1916161 / 100000) (479041 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209824000 :
    ThetaLowerSegment 209824000 209856768 (5245162936061 / 25000) (5245981143213 / 25000) := by
  exact
    packedTile16384 209824000 209856768 12 1708 14485 28 _ _ (119761 / 6250) (1916179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209856768 :
    ThetaLowerSegment 209856768 209889536 (5245981143213 / 25000) (5246802710533 / 25000) := by
  exact
    packedTile16384 209856768 209889536 12 1715 14486 28 _ _ (59881 / 3125) (383239 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209889536 :
    ThetaLowerSegment 209889536 209922304 (5246802710533 / 25000) (5247633865753 / 25000) := by
  exact
    packedTile16384 209889536 209922304 12 1735 14487 28 _ _ (119763 / 6250) (1916211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209922304 :
    ThetaLowerSegment 209922304 209955072 (5247633865753 / 25000) (10496898437279 / 50000) := by
  exact
    packedTile16384 209922304 209955072 12 1702 14488 28 _ _ (1916223 / 100000) (958113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209955072 :
    ThetaLowerSegment 209955072 209987840 (10496898437279 / 50000) (20997071727009 / 100000) := by
  exact
    packedTile16384 209955072 209987840 12 1709 14489 28 _ _ (1916239 / 100000) (958121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell209987840 :
    ThetaLowerSegment 209987840 210020608 (20997071727009 / 100000) (10500186717187 / 50000) := by
  exact
    packedTile16384 209987840 210020608 12 1723 14490 28 _ _ (383251 / 20000) (958129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210020608 :
    ThetaLowerSegment 210020608 210053376 (10500186717187 / 50000) (2625450772733 / 12500) := by
  exact
    packedTile16384 210020608 210053376 12 1687 14492 28 _ _ (191627 / 10000) (1916273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210053376 :
    ThetaLowerSegment 210053376 210086144 (2625450772733 / 12500) (10503421394459 / 50000) := by
  exact
    packedTile16384 210053376 210086144 12 1689 14493 28 _ _ (958143 / 50000) (1916289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210086144 :
    ThetaLowerSegment 210086144 210118912 (10503421394459 / 50000) (21010090919113 / 100000) := by
  exact
    packedTile16384 210086144 210118912 12 1695 14494 28 _ _ (1916301 / 100000) (119769 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210118912 :
    ThetaLowerSegment 210118912 210151680 (21010090919113 / 100000) (10506686785067 / 50000) := by
  exact
    packedTile16384 210118912 210151680 12 1713 14495 28 _ _ (1916317 / 100000) (11977 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210151680 :
    ThetaLowerSegment 210151680 210184448 (10506686785067 / 50000) (10508323333449 / 50000) := by
  exact
    packedTile16384 210151680 210184448 12 1708 14496 28 _ _ (1916333 / 100000) (119771 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210184448 :
    ThetaLowerSegment 210184448 210217216 (10508323333449 / 50000) (10509969476381 / 50000) := by
  exact
    packedTile16384 210184448 210217216 12 1718 14497 28 _ _ (479087 / 25000) (1916351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210217216 :
    ThetaLowerSegment 210217216 210249984 (10509969476381 / 50000) (10511612758511 / 50000) := by
  exact
    packedTile16384 210217216 210249984 12 1715 14498 28 _ _ (479091 / 25000) (1916367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210249984 :
    ThetaLowerSegment 210249984 210282752 (10511612758511 / 50000) (10513257011693 / 50000) := by
  exact
    packedTile16384 210249984 210282752 12 1716 14499 28 _ _ (1916379 / 100000) (958191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210282752 :
    ThetaLowerSegment 210282752 210315520 (10513257011693 / 50000) (10514885947443 / 50000) := by
  exact
    packedTile16384 210282752 210315520 12 1700 14501 28 _ _ (383279 / 20000) (958199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210315520 :
    ThetaLowerSegment 210315520 210348288 (10514885947443 / 50000) (5258268467329 / 25000) := by
  exact
    packedTile16384 210315520 210348288 12 1723 14502 28 _ _ (191641 / 10000) (1916413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210348288 :
    ThetaLowerSegment 210348288 210381056 (5258268467329 / 25000) (10518149607137 / 50000) := by
  exact
    packedTile16384 210348288 210381056 12 1683 14503 28 _ _ (958213 / 50000) (1916429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210381056 :
    ThetaLowerSegment 210381056 210413824 (10518149607137 / 50000) (5259897436297 / 25000) := by
  exact
    packedTile16384 210381056 210413824 12 1717 14504 28 _ _ (958221 / 50000) (383289 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210413824 :
    ThetaLowerSegment 210413824 210446592 (5259897436297 / 25000) (10521395114189 / 50000) := by
  exact
    packedTile16384 210413824 210446592 12 1670 14505 28 _ _ (1916457 / 100000) (95823 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210446592 :
    ThetaLowerSegment 210446592 210479360 (10521395114189 / 50000) (10523020283293 / 50000) := by
  exact
    packedTile16384 210446592 210479360 12 1696 14506 28 _ _ (1916473 / 100000) (479119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210479360 :
    ThetaLowerSegment 210479360 210512128 (10523020283293 / 50000) (10524638757409 / 50000) := by
  exact
    packedTile16384 210479360 210512128 12 1689 14507 28 _ _ (239561 / 12500) (1916491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210512128 :
    ThetaLowerSegment 210512128 210544896 (10524638757409 / 50000) (10526285992597 / 50000) := by
  exact
    packedTile16384 210512128 210544896 12 1719 14509 28 _ _ (239563 / 12500) (1916507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210544896 :
    ThetaLowerSegment 210544896 210577664 (10526285992597 / 50000) (10527892035519 / 50000) := by
  exact
    packedTile16384 210544896 210577664 12 1676 14510 28 _ _ (1916519 / 100000) (958261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210577664 :
    ThetaLowerSegment 210577664 210610432 (10527892035519 / 50000) (21059139923823 / 100000) := by
  exact
    packedTile16384 210577664 210610432 12 1751 14511 28 _ _ (383307 / 20000) (958269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210610432 :
    ThetaLowerSegment 210610432 210643200 (21059139923823 / 100000) (10531238319557 / 50000) := by
  exact
    packedTile16384 210610432 210643200 12 1741 14512 28 _ _ (1916551 / 100000) (958277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210643200 :
    ThetaLowerSegment 210643200 210675968 (10531238319557 / 50000) (1053282044479 / 5000) := by
  exact
    packedTile16384 210643200 210675968 12 1651 14513 28 _ _ (958283 / 50000) (1916569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210675968 :
    ThetaLowerSegment 210675968 210708736 (1053282044479 / 5000) (10534460080691 / 50000) := by
  exact
    packedTile16384 210675968 210708736 12 1711 14514 28 _ _ (958291 / 50000) (383317 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210708736 :
    ThetaLowerSegment 210708736 210741504 (10534460080691 / 50000) (21072164960103 / 100000) := by
  exact
    packedTile16384 210708736 210741504 12 1693 14515 28 _ _ (1916597 / 100000) (9583 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210741504 :
    ThetaLowerSegment 210741504 210774272 (21072164960103 / 100000) (21075438535107 / 100000) := by
  exact
    packedTile16384 210741504 210774272 12 1708 14516 28 _ _ (1916613 / 100000) (239577 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210774272 :
    ThetaLowerSegment 210774272 210807040 (21075438535107 / 100000) (21078731302011 / 100000) := by
  exact
    packedTile16384 210774272 210807040 12 1718 14518 28 _ _ (479157 / 25000) (1916631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210807040 :
    ThetaLowerSegment 210807040 210839808 (21078731302011 / 100000) (21081966597083 / 100000) := by
  exact
    packedTile16384 210807040 210839808 12 1688 14519 28 _ _ (479161 / 25000) (1916647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210839808 :
    ThetaLowerSegment 210839808 210872576 (21081966597083 / 100000) (10542636416929 / 50000) := by
  exact
    packedTile16384 210839808 210872576 12 1725 14520 28 _ _ (1916659 / 100000) (958331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210872576 :
    ThetaLowerSegment 210872576 210905344 (10542636416929 / 50000) (2636069751851 / 12500) := by
  exact
    packedTile16384 210872576 210905344 12 1714 14521 28 _ _ (76667 / 4000) (958339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210905344 :
    ThetaLowerSegment 210905344 210938112 (2636069751851 / 12500) (10545920652389 / 50000) := by
  exact
    packedTile16384 210905344 210938112 12 1713 14522 28 _ _ (191669 / 10000) (1916693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210938112 :
    ThetaLowerSegment 210938112 210970880 (10545920652389 / 50000) (1318443611767 / 6250) := by
  exact
    packedTile16384 210938112 210970880 12 1699 14523 28 _ _ (958353 / 50000) (1916709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell210970880 :
    ThetaLowerSegment 210970880 211003648 (1318443611767 / 6250) (659324829691 / 3125) := by
  exact
    packedTile16384 210970880 211003648 12 1720 14524 28 _ _ (958361 / 50000) (76669 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211003648 :
    ThetaLowerSegment 211003648 211036416 (659324829691 / 3125) (21101601251113 / 100000) := by
  exact
    packedTile16384 211003648 211036416 12 1673 14525 28 _ _ (1916737 / 100000) (95837 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211036416 :
    ThetaLowerSegment 211036416 211069184 (21101601251113 / 100000) (10552423156971 / 50000) := by
  exact
    packedTile16384 211036416 211069184 12 1693 14527 28 _ _ (1916753 / 100000) (479189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211069184 :
    ThetaLowerSegment 211069184 211101952 (10552423156971 / 50000) (10554052409771 / 50000) := by
  exact
    packedTile16384 211069184 211101952 12 1700 14528 28 _ _ (59899 / 3125) (1916771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211101952 :
    ThetaLowerSegment 211101952 211134720 (10554052409771 / 50000) (10555754513963 / 50000) := by
  exact
    packedTile16384 211101952 211134720 12 1776 14529 28 _ _ (119799 / 6250) (1916787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211134720 :
    ThetaLowerSegment 211134720 211167488 (10555754513963 / 50000) (131967129694 / 625) := by
  exact
    packedTile16384 211134720 211167488 12 1686 14530 28 _ _ (1916799 / 100000) (958401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211167488 :
    ThetaLowerSegment 211167488 211200256 (131967129694 / 625) (2111805684099 / 10000) := by
  exact
    packedTile16384 211167488 211200256 12 1730 14531 28 _ _ (383363 / 20000) (958409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211200256 :
    ThetaLowerSegment 211200256 211233024 (2111805684099 / 10000) (2112131161833 / 10000) := by
  exact
    packedTile16384 211200256 211233024 12 1698 14532 28 _ _ (191683 / 10000) (1916833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211233024 :
    ThetaLowerSegment 211233024 211265792 (2112131161833 / 10000) (10562298546187 / 50000) := by
  exact
    packedTile16384 211233024 211265792 12 1714 14533 28 _ _ (958423 / 50000) (1916849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211265792 :
    ThetaLowerSegment 211265792 211298560 (10562298546187 / 50000) (5281980232337 / 25000) := by
  exact
    packedTile16384 211265792 211298560 12 1734 14534 28 _ _ (1916861 / 100000) (59902 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211298560 :
    ThetaLowerSegment 211298560 211331328 (5281980232337 / 25000) (21131177703371 / 100000) := by
  exact
    packedTile16384 211298560 211331328 12 1699 14536 28 _ _ (1916877 / 100000) (23961 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211331328 :
    ThetaLowerSegment 211331328 211364096 (21131177703371 / 100000) (21134490092747 / 100000) := by
  exact
    packedTile16384 211331328 211364096 12 1728 14537 28 _ _ (479223 / 25000) (383379 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211364096 :
    ThetaLowerSegment 211364096 211396864 (21134490092747 / 100000) (4227567402823 / 20000) := by
  exact
    packedTile16384 211364096 211396864 12 1746 14538 28 _ _ (479227 / 25000) (1916911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211396864 :
    ThetaLowerSegment 211396864 211429632 (4227567402823 / 20000) (21141141789367 / 100000) := by
  exact
    packedTile16384 211396864 211429632 12 1724 14539 28 _ _ (1916923 / 100000) (958463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211429632 :
    ThetaLowerSegment 211429632 211462400 (21141141789367 / 100000) (10572182081913 / 50000) := by
  exact
    packedTile16384 211429632 211462400 12 1681 14540 28 _ _ (1916939 / 100000) (958471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211462400 :
    ThetaLowerSegment 211462400 211495168 (10572182081913 / 50000) (10573863250571 / 50000) := by
  exact
    packedTile16384 211462400 211495168 12 1754 14541 28 _ _ (958477 / 50000) (1916957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211495168 :
    ThetaLowerSegment 211495168 211527936 (10573863250571 / 50000) (10575488841131 / 50000) := by
  exact
    packedTile16384 211495168 211527936 12 1696 14542 28 _ _ (191697 / 10000) (1916973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211527936 :
    ThetaLowerSegment 211527936 211560704 (10575488841131 / 50000) (661071210326 / 3125) := by
  exact
    packedTile16384 211527936 211560704 12 1722 14544 28 _ _ (383397 / 20000) (479247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211560704 :
    ThetaLowerSegment 211560704 211593472 (661071210326 / 3125) (21157482039103 / 100000) := by
  exact
    packedTile16384 211560704 211593472 12 1671 14545 28 _ _ (1917001 / 100000) (479251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211593472 :
    ThetaLowerSegment 211593472 211626240 (21157482039103 / 100000) (4232147043051 / 20000) := by
  exact
    packedTile16384 211593472 211626240 12 1697 14546 28 _ _ (239627 / 12500) (1917019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211626240 :
    ThetaLowerSegment 211626240 211659008 (4232147043051 / 20000) (4232814170187 / 20000) := by
  exact
    packedTile16384 211626240 211659008 12 1740 14547 28 _ _ (239629 / 12500) (383407 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211659008 :
    ThetaLowerSegment 211659008 211691776 (4232814170187 / 20000) (21167341333117 / 100000) := by
  exact
    packedTile16384 211659008 211691776 12 1706 14548 28 _ _ (1917047 / 100000) (38341 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211691776 :
    ThetaLowerSegment 211691776 211724544 (21167341333117 / 100000) (21170581169587 / 100000) := by
  exact
    packedTile16384 211691776 211724544 12 1690 14549 28 _ _ (1917063 / 100000) (958533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211724544 :
    ThetaLowerSegment 211724544 211757312 (21170581169587 / 100000) (4234791428789 / 20000) := by
  exact
    packedTile16384 211724544 211757312 12 1761 14550 28 _ _ (958539 / 50000) (1917081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211757312 :
    ThetaLowerSegment 211757312 211790080 (4234791428789 / 20000) (21177204701181 / 100000) := by
  exact
    packedTile16384 211757312 211790080 12 1694 14551 28 _ _ (958547 / 50000) (1917097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211790080 :
    ThetaLowerSegment 211790080 211822848 (21177204701181 / 100000) (2647545272463 / 12500) := by
  exact
    packedTile16384 211790080 211822848 12 1647 14553 28 _ _ (1917109 / 100000) (239639 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211822848 :
    ThetaLowerSegment 211822848 211855616 (2647545272463 / 12500) (10591866242727 / 50000) := by
  exact
    packedTile16384 211822848 211855616 12 1758 14554 28 _ _ (15337 / 800) (239641 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211855616 :
    ThetaLowerSegment 211855616 211888384 (10591866242727 / 50000) (10593466096057 / 50000) := by
  exact
    packedTile16384 211855616 211888384 12 1669 14555 28 _ _ (95857 / 5000) (1917143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211888384 :
    ThetaLowerSegment 211888384 211921152 (10593466096057 / 50000) (10595102388703 / 50000) := by
  exact
    packedTile16384 211888384 211921152 12 1707 14556 28 _ _ (479289 / 25000) (1917159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211921152 :
    ThetaLowerSegment 211921152 211953920 (10595102388703 / 50000) (2649173889451 / 12500) := by
  exact
    packedTile16384 211921152 211953920 12 1662 14557 28 _ _ (1917171 / 100000) (958587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211953920 :
    ThetaLowerSegment 211953920 211986688 (2649173889451 / 12500) (10598391308821 / 50000) := by
  exact
    packedTile16384 211953920 211986688 12 1769 14558 28 _ _ (958593 / 50000) (1917189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell211986688 :
    ThetaLowerSegment 211986688 212019456 (10598391308821 / 50000) (1325001537889 / 6250) := by
  exact
    packedTile16384 211986688 212019456 12 1691 14559 28 _ _ (958601 / 50000) (383441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212019456 :
    ThetaLowerSegment 212019456 212052224 (1325001537889 / 6250) (4240665594223 / 20000) := by
  exact
    packedTile16384 212019456 212052224 12 1723 14560 28 _ _ (1917217 / 100000) (95861 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212052224 :
    ThetaLowerSegment 212052224 212084992 (4240665594223 / 20000) (10603281171593 / 50000) := by
  exact
    packedTile16384 212052224 212084992 12 1687 14562 28 _ _ (1917233 / 100000) (479309 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212084992 :
    ThetaLowerSegment 212084992 212117760 (10603281171593 / 50000) (2120981783029 / 10000) := by
  exact
    packedTile16384 212084992 212117760 12 1698 14563 28 _ _ (59914 / 3125) (1917251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212117760 :
    ThetaLowerSegment 212117760 212150528 (2120981783029 / 10000) (10606535713649 / 50000) := by
  exact
    packedTile16384 212117760 212150528 12 1697 14564 28 _ _ (119829 / 6250) (1917267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212150528 :
    ThetaLowerSegment 212150528 212183296 (10606535713649 / 50000) (848650394491 / 4000) := by
  exact
    packedTile16384 212150528 212183296 12 1663 14565 28 _ _ (1917279 / 100000) (958641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212183296 :
    ThetaLowerSegment 212183296 212216064 (848650394491 / 4000) (4243903085837 / 20000) := by
  exact
    packedTile16384 212183296 212216064 12 1698 14566 28 _ _ (383459 / 20000) (958649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212216064 :
    ThetaLowerSegment 212216064 212248832 (4243903085837 / 20000) (4244578362419 / 20000) := by
  exact
    packedTile16384 212216064 212248832 12 1761 14567 28 _ _ (191731 / 10000) (1917313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212248832 :
    ThetaLowerSegment 212248832 212281600 (4244578362419 / 20000) (1061307275631 / 5000) := by
  exact
    packedTile16384 212248832 212281600 12 1697 14568 28 _ _ (76693 / 4000) (119833 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212281600 :
    ThetaLowerSegment 212281600 212314368 (1061307275631 / 5000) (5307368504149 / 25000) := by
  exact
    packedTile16384 212281600 212314368 12 1736 14569 28 _ _ (1917341 / 100000) (59917 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212314368 :
    ThetaLowerSegment 212314368 212347136 (5307368504149 / 25000) (5308192008551 / 25000) := by
  exact
    packedTile16384 212314368 212347136 12 1718 14571 28 _ _ (479339 / 25000) (1917359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212347136 :
    ThetaLowerSegment 212347136 212379904 (5308192008551 / 25000) (5309003056907 / 25000) := by
  exact
    packedTile16384 212347136 212379904 12 1692 14572 28 _ _ (479343 / 25000) (15339 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212379904 :
    ThetaLowerSegment 212379904 212412672 (5309003056907 / 25000) (424785665797 / 2000) := by
  exact
    packedTile16384 212379904 212412672 12 1706 14573 28 _ _ (1917387 / 100000) (191739 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212412672 :
    ThetaLowerSegment 212412672 212445440 (424785665797 / 2000) (21242471931039 / 100000) := by
  exact
    packedTile16384 212412672 212445440 12 1663 14574 28 _ _ (1917403 / 100000) (958703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212445440 :
    ThetaLowerSegment 212445440 212478208 (21242471931039 / 100000) (21245800568687 / 100000) := by
  exact
    packedTile16384 212445440 212478208 12 1736 14575 28 _ _ (958709 / 50000) (1917421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212478208 :
    ThetaLowerSegment 212478208 212510976 (21245800568687 / 100000) (10624563657471 / 50000) := by
  exact
    packedTile16384 212478208 212510976 12 1735 14576 28 _ _ (1917433 / 100000) (479359 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212510976 :
    ThetaLowerSegment 212510976 212543744 (10624563657471 / 50000) (10626228003203 / 50000) := by
  exact
    packedTile16384 212510976 212543744 12 1736 14577 28 _ _ (1917449 / 100000) (479363 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212543744 :
    ThetaLowerSegment 212543744 212576512 (10626228003203 / 50000) (10627850177747 / 50000) := by
  exact
    packedTile16384 212543744 212576512 12 1692 14578 28 _ _ (239683 / 12500) (1917467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212576512 :
    ThetaLowerSegment 212576512 212609280 (10627850177747 / 50000) (10629479077007 / 50000) := by
  exact
    packedTile16384 212576512 212609280 12 1699 14580 28 _ _ (47937 / 2500) (1917483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212609280 :
    ThetaLowerSegment 212609280 212642048 (10629479077007 / 50000) (10631112782747 / 50000) := by
  exact
    packedTile16384 212609280 212642048 12 1704 14581 28 _ _ (383499 / 20000) (958749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212642048 :
    ThetaLowerSegment 212642048 212674816 (10631112782747 / 50000) (21265590797299 / 100000) := by
  exact
    packedTile16384 212642048 212674816 12 1755 14582 28 _ _ (1917511 / 100000) (958757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212674816 :
    ThetaLowerSegment 212674816 212707584 (21265590797299 / 100000) (21268777725511 / 100000) := by
  exact
    packedTile16384 212674816 212707584 12 1662 14583 28 _ _ (958763 / 50000) (1917529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212707584 :
    ThetaLowerSegment 212707584 212740352 (21268777725511 / 100000) (10636033154163 / 50000) := by
  exact
    packedTile16384 212707584 212740352 12 1715 14584 28 _ _ (1917541 / 100000) (239693 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212740352 :
    ThetaLowerSegment 212740352 212773120 (10636033154163 / 50000) (21275274381187 / 100000) := by
  exact
    packedTile16384 212740352 212773120 12 1673 14585 28 _ _ (1917557 / 100000) (47939 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212773120 :
    ThetaLowerSegment 212773120 212805888 (21275274381187 / 100000) (21278511242723 / 100000) := by
  exact
    packedTile16384 212773120 212805888 12 1688 14586 28 _ _ (479393 / 25000) (76703 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212805888 :
    ThetaLowerSegment 212805888 212838656 (21278511242723 / 100000) (21281809494083 / 100000) := by
  exact
    packedTile16384 212805888 212838656 12 1720 14587 28 _ _ (479397 / 25000) (1917591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212838656 :
    ThetaLowerSegment 212838656 212871424 (21281809494083 / 100000) (1064249539873 / 5000) := by
  exact
    packedTile16384 212838656 212871424 12 1659 14588 28 _ _ (1917603 / 100000) (958803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212871424 :
    ThetaLowerSegment 212871424 212904192 (1064249539873 / 5000) (2661044287429 / 12500) := by
  exact
    packedTile16384 212871424 212904192 12 1754 14590 28 _ _ (958809 / 50000) (1917621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212904192 :
    ThetaLowerSegment 212904192 212936960 (2661044287429 / 12500) (5322919869197 / 25000) := by
  exact
    packedTile16384 212904192 212936960 12 1734 14591 28 _ _ (958817 / 50000) (1917637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212936960 :
    ThetaLowerSegment 212936960 212969728 (5322919869197 / 25000) (21295018103697 / 100000) := by
  exact
    packedTile16384 212936960 212969728 12 1741 14592 28 _ _ (1917649 / 100000) (479413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell212969728 :
    ThetaLowerSegment 212969728 213002496 (21295018103697 / 100000) (21298331828817 / 100000) := by
  exact
    packedTile16384 212969728 213002496 12 1728 14593 28 _ _ (383533 / 20000) (479417 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213002496 :
    ThetaLowerSegment 213002496 213035264 (21298331828817 / 100000) (21301618732337 / 100000) := by
  exact
    packedTile16384 213002496 213035264 12 1714 14594 28 _ _ (23971 / 1250) (1917683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213035264 :
    ThetaLowerSegment 213035264 213068032 (21301618732337 / 100000) (5326224018273 / 25000) := by
  exact
    packedTile16384 213035264 213068032 12 1709 14595 28 _ _ (383539 / 20000) (958849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213068032 :
    ThetaLowerSegment 213068032 213100800 (5326224018273 / 25000) (10654080008607 / 50000) := by
  exact
    packedTile16384 213068032 213100800 12 1702 14596 28 _ _ (1917711 / 100000) (958857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213100800 :
    ThetaLowerSegment 213100800 213133568 (10654080008607 / 50000) (10655738841597 / 50000) := by
  exact
    packedTile16384 213100800 213133568 12 1730 14597 28 _ _ (958863 / 50000) (1917729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213133568 :
    ThetaLowerSegment 213133568 213166336 (10655738841597 / 50000) (10657376592411 / 50000) := by
  exact
    packedTile16384 213133568 213166336 12 1708 14599 28 _ _ (1917741 / 100000) (119859 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213166336 :
    ThetaLowerSegment 213166336 213199104 (10657376592411 / 50000) (21317969263311 / 100000) := by
  exact
    packedTile16384 213166336 213199104 12 1677 14600 28 _ _ (1917757 / 100000) (11986 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213199104 :
    ThetaLowerSegment 213199104 213231872 (21317969263311 / 100000) (852850099559 / 4000) := by
  exact
    packedTile16384 213199104 213231872 12 1712 14601 28 _ _ (479443 / 25000) (76711 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213231872 :
    ThetaLowerSegment 213231872 213264640 (852850099559 / 4000) (21324501221847 / 100000) := by
  exact
    packedTile16384 213231872 213264640 12 1694 14602 28 _ _ (479447 / 25000) (1917791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213264640 :
    ThetaLowerSegment 213264640 213297408 (21324501221847 / 100000) (21327807514219 / 100000) := by
  exact
    packedTile16384 213264640 213297408 12 1724 14603 28 _ _ (1917803 / 100000) (958903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213297408 :
    ThetaLowerSegment 213297408 213330176 (21327807514219 / 100000) (21331060133547 / 100000) := by
  exact
    packedTile16384 213297408 213330176 12 1696 14604 28 _ _ (958909 / 50000) (1917821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213330176 :
    ThetaLowerSegment 213330176 213362944 (21331060133547 / 100000) (4266872528739 / 20000) := by
  exact
    packedTile16384 213330176 213362944 12 1722 14605 28 _ _ (958917 / 50000) (1917837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213362944 :
    ThetaLowerSegment 213362944 213395712 (4266872528739 / 20000) (10668822041667 / 50000) := by
  exact
    packedTile16384 213362944 213395712 12 1711 14606 28 _ _ (1917849 / 100000) (479463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213395712 :
    ThetaLowerSegment 213395712 213428480 (10668822041667 / 50000) (10670438801019 / 50000) := by
  exact
    packedTile16384 213395712 213428480 12 1686 14608 28 _ _ (239733 / 12500) (1917867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213428480 :
    ThetaLowerSegment 213428480 213461248 (10670438801019 / 50000) (10672104479799 / 50000) := by
  exact
    packedTile16384 213428480 213461248 12 1737 14609 28 _ _ (47947 / 2500) (1917883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213461248 :
    ThetaLowerSegment 213461248 213494016 (10672104479799 / 50000) (667108058554 / 3125) := by
  exact
    packedTile16384 213461248 213494016 12 1694 14610 28 _ _ (383579 / 20000) (958949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213494016 :
    ThetaLowerSegment 213494016 213526784 (667108058554 / 3125) (5337682457047 / 25000) := by
  exact
    packedTile16384 213494016 213526784 12 1706 14611 28 _ _ (191791 / 10000) (1917913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213526784 :
    ThetaLowerSegment 213526784 213559552 (5337682457047 / 25000) (5338487985967 / 25000) := by
  exact
    packedTile16384 213526784 213559552 12 1680 14612 28 _ _ (958963 / 50000) (1917929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213559552 :
    ThetaLowerSegment 213559552 213592320 (5338487985967 / 25000) (10678619647371 / 50000) := by
  exact
    packedTile16384 213559552 213592320 12 1714 14613 28 _ _ (1917941 / 100000) (239743 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213592320 :
    ThetaLowerSegment 213592320 213625088 (10678619647371 / 50000) (10680222099609 / 50000) := by
  exact
    packedTile16384 213592320 213625088 12 1671 14614 28 _ _ (479489 / 25000) (1917959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213625088 :
    ThetaLowerSegment 213625088 213657856 (10680222099609 / 50000) (10681825524201 / 50000) := by
  exact
    packedTile16384 213625088 213657856 12 1672 14615 28 _ _ (479493 / 25000) (76719 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213657856 :
    ThetaLowerSegment 213657856 213690624 (10681825524201 / 50000) (4273389613611 / 20000) := by
  exact
    packedTile16384 213657856 213690624 12 1719 14617 28 _ _ (1917987 / 100000) (191799 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213690624 :
    ThetaLowerSegment 213690624 213723392 (4273389613611 / 20000) (4274037898287 / 20000) := by
  exact
    packedTile16384 213690624 213723392 12 1690 14618 28 _ _ (959001 / 50000) (383601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213723392 :
    ThetaLowerSegment 213723392 213756160 (4274037898287 / 20000) (21373388745459 / 100000) := by
  exact
    packedTile16384 213723392 213756160 12 1668 14619 28 _ _ (959009 / 50000) (1918021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213756160 :
    ThetaLowerSegment 213756160 213788928 (21373388745459 / 100000) (21376676254021 / 100000) := by
  exact
    packedTile16384 213756160 213788928 12 1714 14620 28 _ _ (1918033 / 100000) (479509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213788928 :
    ThetaLowerSegment 213788928 213821696 (21376676254021 / 100000) (21379948443909 / 100000) := by
  exact
    packedTile16384 213788928 213821696 12 1706 14621 28 _ _ (59939 / 3125) (1918051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213821696 :
    ThetaLowerSegment 213821696 213854464 (21379948443909 / 100000) (21383239841733 / 100000) := by
  exact
    packedTile16384 213821696 213854464 12 1716 14622 28 _ _ (119879 / 6250) (1918067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213854464 :
    ThetaLowerSegment 213854464 213887232 (21383239841733 / 100000) (21386527429139 / 100000) := by
  exact
    packedTile16384 213854464 213887232 12 1714 14623 28 _ _ (1918079 / 100000) (959041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213887232 :
    ThetaLowerSegment 213887232 213920000 (21386527429139 / 100000) (21389792025127 / 100000) := by
  exact
    packedTile16384 213887232 213920000 12 1702 14624 28 _ _ (959047 / 50000) (1918097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213920000 :
    ThetaLowerSegment 213920000 213952768 (21389792025127 / 100000) (21393071993227 / 100000) := by
  exact
    packedTile16384 213920000 213952768 12 1710 14626 28 _ _ (191811 / 10000) (1918113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213952768 :
    ThetaLowerSegment 213952768 213985536 (21393071993227 / 100000) (21396348150727 / 100000) := by
  exact
    packedTile16384 213952768 213985536 12 1708 14627 28 _ _ (3069 / 160) (119883 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell213985536 :
    ThetaLowerSegment 213985536 214018304 (21396348150727 / 100000) (21399645433387 / 100000) := by
  exact
    packedTile16384 213985536 214018304 12 1719 14628 28 _ _ (95907 / 5000) (1918143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214018304 :
    ThetaLowerSegment 214018304 214051072 (21399645433387 / 100000) (21402896707807 / 100000) := by
  exact
    packedTile16384 214018304 214051072 12 1695 14629 28 _ _ (479539 / 25000) (1918159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214051072 :
    ThetaLowerSegment 214051072 214083840 (21402896707807 / 100000) (21406157598507 / 100000) := by
  exact
    packedTile16384 214051072 214083840 12 1700 14630 28 _ _ (1918171 / 100000) (959087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214083840 :
    ThetaLowerSegment 214083840 214116608 (21406157598507 / 100000) (4281896362969 / 20000) := by
  exact
    packedTile16384 214083840 214116608 12 1733 14631 28 _ _ (959093 / 50000) (1918189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214116608 :
    ThetaLowerSegment 214116608 214149376 (4281896362969 / 20000) (21412758103861 / 100000) := by
  exact
    packedTile16384 214116608 214149376 12 1708 14632 28 _ _ (959101 / 50000) (383641 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214149376 :
    ThetaLowerSegment 214149376 214182144 (21412758103861 / 100000) (856640149081 / 4000) := by
  exact
    packedTile16384 214149376 214182144 12 1692 14633 28 _ _ (1918217 / 100000) (95911 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214182144 :
    ThetaLowerSegment 214182144 214214912 (856640149081 / 4000) (21419345287169 / 100000) := by
  exact
    packedTile16384 214182144 214214912 12 1742 14634 28 _ _ (239779 / 12500) (383647 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214214912 :
    ThetaLowerSegment 214214912 214247680 (21419345287169 / 100000) (21422585208041 / 100000) := by
  exact
    packedTile16384 214214912 214247680 12 1689 14636 28 _ _ (239781 / 12500) (1918251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214247680 :
    ThetaLowerSegment 214247680 214280448 (21422585208041 / 100000) (2142581364467 / 10000) := by
  exact
    packedTile16384 214247680 214280448 12 1683 14637 28 _ _ (1918263 / 100000) (959133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214280448 :
    ThetaLowerSegment 214280448 214313216 (2142581364467 / 10000) (2678638895569 / 12500) := by
  exact
    packedTile16384 214280448 214313216 12 1719 14638 28 _ _ (959139 / 50000) (1918281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214313216 :
    ThetaLowerSegment 214313216 214345984 (2678638895569 / 12500) (669760913848 / 3125) := by
  exact
    packedTile16384 214313216 214345984 12 1688 14639 28 _ _ (1918293 / 100000) (239787 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214345984 :
    ThetaLowerSegment 214345984 214378752 (669760913848 / 3125) (21435608450127 / 100000) := by
  exact
    packedTile16384 214345984 214378752 12 1699 14640 28 _ _ (1918309 / 100000) (239789 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214378752 :
    ThetaLowerSegment 214378752 214411520 (21435608450127 / 100000) (21438831234447 / 100000) := by
  exact
    packedTile16384 214378752 214411520 12 1680 14641 28 _ _ (479581 / 25000) (1918327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214411520 :
    ThetaLowerSegment 214411520 214444288 (21438831234447 / 100000) (21442165307629 / 100000) := by
  exact
    packedTile16384 214411520 214444288 12 1738 14642 28 _ _ (1918339 / 100000) (959171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214444288 :
    ThetaLowerSegment 214444288 214477056 (21442165307629 / 100000) (2680675676153 / 12500) := by
  exact
    packedTile16384 214444288 214477056 12 1689 14643 28 _ _ (383671 / 20000) (959179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214477056 :
    ThetaLowerSegment 214477056 214509824 (2680675676153 / 12500) (10724368808957 / 50000) := by
  exact
    packedTile16384 214477056 214509824 12 1737 14645 28 _ _ (191837 / 10000) (1918373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214509824 :
    ThetaLowerSegment 214509824 214542592 (10724368808957 / 50000) (21451985443719 / 100000) := by
  exact
    packedTile16384 214509824 214542592 12 1693 14646 28 _ _ (383677 / 20000) (479597 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214542592 :
    ThetaLowerSegment 214542592 214575360 (21451985443719 / 100000) (21455239050119 / 100000) := by
  exact
    packedTile16384 214542592 214575360 12 1696 14647 28 _ _ (2398 / 125) (1918403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214575360 :
    ThetaLowerSegment 214575360 214608128 (21455239050119 / 100000) (4291711965643 / 20000) := by
  exact
    packedTile16384 214575360 214608128 12 1731 14648 28 _ _ (119901 / 6250) (1918419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214608128 :
    ThetaLowerSegment 214608128 214640896 (4291711965643 / 20000) (21461855692673 / 100000) := by
  exact
    packedTile16384 214608128 214640896 12 1718 14649 28 _ _ (1918431 / 100000) (959217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214640896 :
    ThetaLowerSegment 214640896 214673664 (21461855692673 / 100000) (21465157338239 / 100000) := by
  exact
    packedTile16384 214640896 214673664 12 1721 14650 28 _ _ (959223 / 50000) (1918449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214673664 :
    ThetaLowerSegment 214673664 214706432 (21465157338239 / 100000) (21468533829599 / 100000) := by
  exact
    packedTile16384 214673664 214706432 12 1760 14651 28 _ _ (1918461 / 100000) (59952 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214706432 :
    ThetaLowerSegment 214706432 214739200 (21468533829599 / 100000) (134199115939 / 625) := by
  exact
    packedTile16384 214706432 214739200 12 1733 14652 28 _ _ (1918477 / 100000) (23981 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214739200 :
    ThetaLowerSegment 214739200 214771968 (134199115939 / 625) (2684385681723 / 12500) := by
  exact
    packedTile16384 214739200 214771968 12 1682 14653 28 _ _ (479623 / 25000) (383699 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214771968 :
    ThetaLowerSegment 214771968 214804736 (2684385681723 / 12500) (21478394878359 / 100000) := by
  exact
    packedTile16384 214771968 214804736 12 1725 14655 28 _ _ (1918507 / 100000) (191851 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214804736 :
    ThetaLowerSegment 214804736 214837504 (21478394878359 / 100000) (4296334342787 / 20000) := by
  exact
    packedTile16384 214804736 214837504 12 1708 14656 28 _ _ (959261 / 50000) (76741 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214837504 :
    ThetaLowerSegment 214837504 214870272 (4296334342787 / 20000) (4297005831087 / 20000) := by
  exact
    packedTile16384 214837504 214870272 12 1750 14657 28 _ _ (959269 / 50000) (1918541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214870272 :
    ThetaLowerSegment 214870272 214903040 (4297005831087 / 20000) (5372090420499 / 25000) := by
  exact
    packedTile16384 214870272 214903040 12 1737 14658 28 _ _ (1918553 / 100000) (479639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214903040 :
    ThetaLowerSegment 214903040 214935808 (5372090420499 / 25000) (5372897178343 / 25000) := by
  exact
    packedTile16384 214903040 214935808 12 1682 14659 28 _ _ (239821 / 12500) (1918571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214935808 :
    ThetaLowerSegment 214935808 214968576 (5372897178343 / 25000) (2149490018763 / 10000) := by
  exact
    packedTile16384 214935808 214968576 12 1726 14660 28 _ _ (1918583 / 100000) (959293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell214968576 :
    ThetaLowerSegment 214968576 215001344 (2149490018763 / 10000) (21498186747717 / 100000) := by
  exact
    packedTile16384 214968576 215001344 12 1713 14661 28 _ _ (1918599 / 100000) (959301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215001344 :
    ThetaLowerSegment 215001344 215034112 (21498186747717 / 100000) (21501502112709 / 100000) := by
  exact
    packedTile16384 215001344 215034112 12 1728 14662 28 _ _ (959307 / 50000) (1918617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215034112 :
    ThetaLowerSegment 215034112 215066880 (21501502112709 / 100000) (21504832852653 / 100000) := by
  exact
    packedTile16384 215034112 215066880 12 1736 14664 28 _ _ (1918629 / 100000) (239829 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215066880 :
    ThetaLowerSegment 215066880 215099648 (21504832852653 / 100000) (21508056174573 / 100000) := by
  exact
    packedTile16384 215066880 215099648 12 1680 14665 28 _ _ (479661 / 25000) (1918647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215099648 :
    ThetaLowerSegment 215099648 215132416 (21508056174573 / 100000) (21511363944413 / 100000) := by
  exact
    packedTile16384 215099648 215132416 12 1724 14666 28 _ _ (95933 / 5000) (1918663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215132416 :
    ThetaLowerSegment 215132416 215165184 (21511363944413 / 100000) (10757323398669 / 50000) := by
  exact
    packedTile16384 215132416 215165184 12 1711 14667 28 _ _ (76747 / 4000) (959339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215165184 :
    ThetaLowerSegment 215165184 215197952 (10757323398669 / 50000) (10758965797309 / 50000) := by
  exact
    packedTile16384 215165184 215197952 12 1712 14668 28 _ _ (191869 / 10000) (1918693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215197952 :
    ThetaLowerSegment 215197952 215230720 (10758965797309 / 50000) (2690151572521 / 12500) := by
  exact
    packedTile16384 215197952 215230720 12 1710 14669 28 _ _ (383741 / 20000) (479677 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215230720 :
    ThetaLowerSegment 215230720 215263488 (2690151572521 / 12500) (21524522373893 / 100000) := by
  exact
    packedTile16384 215230720 215263488 12 1725 14670 28 _ _ (1918721 / 100000) (479681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215263488 :
    ThetaLowerSegment 215263488 215296256 (21524522373893 / 100000) (21527811087397 / 100000) := by
  exact
    packedTile16384 215263488 215296256 12 1714 14671 28 _ _ (119921 / 6250) (1918739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215296256 :
    ThetaLowerSegment 215296256 215329024 (21527811087397 / 100000) (21531161226643 / 100000) := by
  exact
    packedTile16384 215296256 215329024 12 1746 14672 28 _ _ (1918751 / 100000) (959377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215329024 :
    ThetaLowerSegment 215329024 215361792 (21531161226643 / 100000) (21534402022417 / 100000) := by
  exact
    packedTile16384 215329024 215361792 12 1689 14674 28 _ _ (959383 / 50000) (1918769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215361792 :
    ThetaLowerSegment 215361792 215394560 (21534402022417 / 100000) (673051458784 / 3125) := by
  exact
    packedTile16384 215361792 215394560 12 1691 14675 28 _ _ (1918781 / 100000) (59962 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215394560 :
    ThetaLowerSegment 215394560 215427328 (673051458784 / 3125) (21540868341251 / 100000) := by
  exact
    packedTile16384 215394560 215427328 12 1679 14676 28 _ _ (1918797 / 100000) (4797 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215427328 :
    ThetaLowerSegment 215427328 215460096 (21540868341251 / 100000) (4308840263539 / 20000) := by
  exact
    packedTile16384 215427328 215460096 12 1737 14677 28 _ _ (479703 / 25000) (383763 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215460096 :
    ThetaLowerSegment 215460096 215492864 (4308840263539 / 20000) (21547432622363 / 100000) := by
  exact
    packedTile16384 215460096 215492864 12 1684 14678 28 _ _ (1918827 / 100000) (191883 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215492864 :
    ThetaLowerSegment 215492864 215525632 (21547432622363 / 100000) (21550669708817 / 100000) := by
  exact
    packedTile16384 215492864 215525632 12 1687 14679 28 _ _ (959421 / 50000) (383769 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215525632 :
    ThetaLowerSegment 215525632 215558400 (21550669708817 / 100000) (21554018116027 / 100000) := by
  exact
    packedTile16384 215525632 215558400 12 1745 14680 28 _ _ (959429 / 50000) (1918861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215558400 :
    ThetaLowerSegment 215558400 215591168 (21554018116027 / 100000) (2155722455281 / 10000) := by
  exact
    packedTile16384 215558400 215591168 12 1671 14681 28 _ _ (1918873 / 100000) (479719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215591168 :
    ThetaLowerSegment 215591168 215623936 (2155722455281 / 10000) (10780247168981 / 50000) := by
  exact
    packedTile16384 215591168 215623936 12 1704 14683 28 _ _ (239861 / 12500) (1918891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215623936 :
    ThetaLowerSegment 215623936 215656704 (10780247168981 / 50000) (4312747840587 / 20000) := by
  exact
    packedTile16384 215623936 215656704 12 1691 14684 28 _ _ (1918903 / 100000) (959453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215656704 :
    ThetaLowerSegment 215656704 215689472 (4312747840587 / 20000) (21567018633797 / 100000) := by
  exact
    packedTile16384 215656704 215689472 12 1709 14685 28 _ _ (959459 / 50000) (1918921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215689472 :
    ThetaLowerSegment 215689472 215722240 (21567018633797 / 100000) (4314070364431 / 20000) := by
  exact
    packedTile16384 215689472 215722240 12 1737 14686 28 _ _ (959467 / 50000) (1918937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215722240 :
    ThetaLowerSegment 215722240 215755008 (4314070364431 / 20000) (21573598683863 / 100000) := by
  exact
    packedTile16384 215722240 215755008 12 1692 14687 28 _ _ (1918949 / 100000) (239869 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215755008 :
    ThetaLowerSegment 215755008 215787776 (21573598683863 / 100000) (21576814867527 / 100000) := by
  exact
    packedTile16384 215755008 215787776 12 1676 14688 28 _ _ (479741 / 25000) (1918967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215787776 :
    ThetaLowerSegment 215787776 215820544 (21576814867527 / 100000) (2158007137489 / 10000) := by
  exact
    packedTile16384 215787776 215820544 12 1697 14689 28 _ _ (1918979 / 100000) (959491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215820544 :
    ThetaLowerSegment 215820544 215853312 (2158007137489 / 10000) (2158333366469 / 10000) := by
  exact
    packedTile16384 215820544 215853312 12 1700 14690 28 _ _ (959497 / 50000) (1918997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215853312 :
    ThetaLowerSegment 215853312 215886080 (2158333366469 / 10000) (21586670821341 / 100000) := by
  exact
    packedTile16384 215853312 215886080 12 1739 14691 28 _ _ (1919009 / 100000) (479753 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215886080 :
    ThetaLowerSegment 215886080 215918848 (21586670821341 / 100000) (21589898621391 / 100000) := by
  exact
    packedTile16384 215886080 215918848 12 1682 14693 28 _ _ (76761 / 4000) (479757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215918848 :
    ThetaLowerSegment 215918848 215951616 (21589898621391 / 100000) (21593149475151 / 100000) := by
  exact
    packedTile16384 215918848 215951616 12 1694 14694 28 _ _ (11994 / 625) (1919043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215951616 :
    ThetaLowerSegment 215951616 215984384 (21593149475151 / 100000) (21596473278411 / 100000) := by
  exact
    packedTile16384 215951616 215984384 12 1732 14695 28 _ _ (383811 / 20000) (959529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell215984384 :
    ThetaLowerSegment 215984384 216017152 (21596473278411 / 100000) (21599810541141 / 100000) := by
  exact
    packedTile16384 215984384 216017152 12 1739 14696 28 _ _ (191907 / 10000) (1919073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216017152 :
    ThetaLowerSegment 216017152 216049920 (21599810541141 / 100000) (21603130558191 / 100000) := by
  exact
    packedTile16384 216017152 216049920 12 1730 14697 28 _ _ (383817 / 20000) (119943 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216049920 :
    ThetaLowerSegment 216049920 216082688 (21603130558191 / 100000) (4321276303057 / 20000) := by
  exact
    packedTile16384 216049920 216082688 12 1694 14698 28 _ _ (1919101 / 100000) (59972 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216082688 :
    ThetaLowerSegment 216082688 216115456 (4321276303057 / 20000) (21609690071269 / 100000) := by
  exact
    packedTile16384 216082688 216115456 12 1724 14699 28 _ _ (479779 / 25000) (1919119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216115456 :
    ThetaLowerSegment 216115456 216148224 (21609690071269 / 100000) (21612948755707 / 100000) := by
  exact
    packedTile16384 216115456 216148224 12 1698 14700 28 _ _ (1919131 / 100000) (959567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216148224 :
    ThetaLowerSegment 216148224 216180992 (21612948755707 / 100000) (4323237654831 / 20000) := by
  exact
    packedTile16384 216148224 216180992 12 1688 14701 28 _ _ (959573 / 50000) (1919149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216180992 :
    ThetaLowerSegment 216180992 216213760 (4323237654831 / 20000) (21619531452617 / 100000) := by
  exact
    packedTile16384 216180992 216213760 12 1742 14703 28 _ _ (1919161 / 100000) (479791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216213760 :
    ThetaLowerSegment 216213760 216246528 (21619531452617 / 100000) (21622805566873 / 100000) := by
  exact
    packedTile16384 216213760 216246528 12 1706 14704 28 _ _ (239897 / 12500) (1919179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216246528 :
    ThetaLowerSegment 216246528 216279296 (21622805566873 / 100000) (10813067681629 / 50000) := by
  exact
    packedTile16384 216246528 216279296 12 1735 14705 28 _ _ (1919191 / 100000) (959597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216279296 :
    ThetaLowerSegment 216279296 216312064 (10813067681629 / 50000) (21629353873397 / 100000) := by
  exact
    packedTile16384 216279296 216312064 12 1677 14706 28 _ _ (1919207 / 100000) (191921 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216312064 :
    ThetaLowerSegment 216312064 216344832 (21629353873397 / 100000) (21632603116243 / 100000) := by
  exact
    packedTile16384 216312064 216344832 12 1693 14707 28 _ _ (959611 / 50000) (76769 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216344832 :
    ThetaLowerSegment 216344832 216377600 (21632603116243 / 100000) (10817916596057 / 50000) := by
  exact
    packedTile16384 216344832 216377600 12 1683 14708 28 _ _ (1919237 / 100000) (47981 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216377600 :
    ThetaLowerSegment 216377600 216410368 (10817916596057 / 50000) (10819604578191 / 50000) := by
  exact
    packedTile16384 216377600 216410368 12 1759 14709 28 _ _ (479813 / 25000) (383851 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216410368 :
    ThetaLowerSegment 216410368 216443136 (10819604578191 / 50000) (21642512214889 / 100000) := by
  exact
    packedTile16384 216410368 216443136 12 1721 14710 28 _ _ (1919267 / 100000) (191927 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216443136 :
    ThetaLowerSegment 216443136 216475904 (21642512214889 / 100000) (4329156150427 / 20000) := by
  exact
    packedTile16384 216443136 216475904 12 1703 14712 28 _ _ (959641 / 50000) (383857 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216475904 :
    ThetaLowerSegment 216475904 216508672 (4329156150427 / 20000) (21648978300937 / 100000) := by
  exact
    packedTile16384 216475904 216508672 12 1666 14713 28 _ _ (1919297 / 100000) (19193 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216508672 :
    ThetaLowerSegment 216508672 216541440 (21648978300937 / 100000) (21652283357923 / 100000) := by
  exact
    packedTile16384 216508672 216541440 12 1722 14714 28 _ _ (1919313 / 100000) (479829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216541440 :
    ThetaLowerSegment 216541440 216574208 (21652283357923 / 100000) (21655559650819 / 100000) := by
  exact
    packedTile16384 216541440 216574208 12 1707 14715 28 _ _ (59979 / 3125) (1919331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216574208 :
    ThetaLowerSegment 216574208 216606976 (21655559650819 / 100000) (21658814856547 / 100000) := by
  exact
    packedTile16384 216574208 216606976 12 1696 14716 28 _ _ (1919343 / 100000) (959673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216606976 :
    ThetaLowerSegment 216606976 216639744 (21658814856547 / 100000) (21661976039173 / 100000) := by
  exact
    packedTile16384 216606976 216639744 12 1647 14717 28 _ _ (959679 / 50000) (1919361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216639744 :
    ThetaLowerSegment 216639744 216672512 (21661976039173 / 100000) (5416313102221 / 25000) := by
  exact
    packedTile16384 216639744 216672512 12 1707 14718 28 _ _ (1919373 / 100000) (119961 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216672512 :
    ThetaLowerSegment 216672512 216705280 (5416313102221 / 25000) (135427945141 / 625) := by
  exact
    packedTile16384 216672512 216705280 12 1677 14719 28 _ _ (479847 / 25000) (1919391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216705280 :
    ThetaLowerSegment 216705280 216738048 (135427945141 / 625) (21671778353929 / 100000) := by
  exact
    packedTile16384 216705280 216738048 12 1723 14720 28 _ _ (1919403 / 100000) (959703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216738048 :
    ThetaLowerSegment 216738048 216770816 (21671778353929 / 100000) (4335009808781 / 20000) := by
  exact
    packedTile16384 216738048 216770816 12 1704 14722 28 _ _ (1919419 / 100000) (959711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216770816 :
    ThetaLowerSegment 216770816 216803584 (4335009808781 / 20000) (4335643222001 / 20000) := by
  exact
    packedTile16384 216770816 216803584 12 1650 14723 28 _ _ (959717 / 50000) (1919437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216803584 :
    ThetaLowerSegment 216803584 216836352 (4335643222001 / 20000) (21681521401183 / 100000) := by
  exact
    packedTile16384 216803584 216836352 12 1722 14724 28 _ _ (1919449 / 100000) (479863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216836352 :
    ThetaLowerSegment 216836352 216869120 (21681521401183 / 100000) (21684826718191 / 100000) := by
  exact
    packedTile16384 216836352 216869120 12 1722 14725 28 _ _ (239933 / 12500) (1919467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216869120 :
    ThetaLowerSegment 216869120 216901888 (21684826718191 / 100000) (10844088104523 / 50000) := by
  exact
    packedTile16384 216869120 216901888 12 1745 14726 28 _ _ (1919479 / 100000) (959741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216901888 :
    ThetaLowerSegment 216901888 216934656 (10844088104523 / 50000) (2711431598163 / 12500) := by
  exact
    packedTile16384 216901888 216934656 12 1707 14727 28 _ _ (959747 / 50000) (1919497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216934656 :
    ThetaLowerSegment 216934656 216967424 (2711431598163 / 12500) (677958193886 / 3125) := by
  exact
    packedTile16384 216934656 216967424 12 1672 14728 28 _ _ (1919509 / 100000) (239939 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell216967424 :
    ThetaLowerSegment 216967424 217000192 (677958193886 / 3125) (1356120337197 / 6250) := by
  exact
    packedTile16384 216967424 217000192 12 1700 14729 28 _ _ (479881 / 25000) (1919527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217000192 :
    ThetaLowerSegment 217000192 217032960 (1356120337197 / 6250) (21701179013757 / 100000) := by
  exact
    packedTile16384 217000192 217032960 12 1695 14730 28 _ _ (1919539 / 100000) (959771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217032960 :
    ThetaLowerSegment 217032960 217065728 (21701179013757 / 100000) (21704453772881 / 100000) := by
  exact
    packedTile16384 217032960 217065728 12 1706 14732 28 _ _ (959777 / 50000) (1919557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217065728 :
    ThetaLowerSegment 217065728 217098496 (21704453772881 / 100000) (21707713202741 / 100000) := by
  exact
    packedTile16384 217065728 217098496 12 1698 14733 28 _ _ (191957 / 10000) (1919573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217098496 :
    ThetaLowerSegment 217098496 217131264 (21707713202741 / 100000) (10855489208413 / 50000) := by
  exact
    packedTile16384 217098496 217131264 12 1701 14734 28 _ _ (383917 / 20000) (479897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217131264 :
    ThetaLowerSegment 217131264 217164032 (10855489208413 / 50000) (10857149662413 / 50000) := by
  exact
    packedTile16384 217131264 217164032 12 1730 14735 28 _ _ (4799 / 250) (1919603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217164032 :
    ThetaLowerSegment 217164032 217196800 (10857149662413 / 50000) (21717583786091 / 100000) := by
  exact
    packedTile16384 217164032 217196800 12 1711 14736 28 _ _ (383923 / 20000) (959809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217196800 :
    ThetaLowerSegment 217196800 217229568 (21717583786091 / 100000) (21720900906731 / 100000) := by
  exact
    packedTile16384 217196800 217229568 12 1728 14737 28 _ _ (191963 / 10000) (1919633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217229568 :
    ThetaLowerSegment 217229568 217262336 (21720900906731 / 100000) (10862081191793 / 50000) := by
  exact
    packedTile16384 217229568 217262336 12 1699 14738 28 _ _ (383929 / 20000) (59989 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217262336 :
    ThetaLowerSegment 217262336 217295104 (10862081191793 / 50000) (10863728260073 / 50000) := by
  exact
    packedTile16384 217262336 217295104 12 1716 14739 28 _ _ (95983 / 5000) (1919663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217295104 :
    ThetaLowerSegment 217295104 217327872 (10863728260073 / 50000) (1358172637531 / 6250) := by
  exact
    packedTile16384 217295104 217327872 12 1722 14740 28 _ _ (76787 / 4000) (959839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217327872 :
    ThetaLowerSegment 217327872 217360640 (1358172637531 / 6250) (5433528494809 / 25000) := by
  exact
    packedTile16384 217327872 217360640 12 1746 14742 28 _ _ (191969 / 10000) (1919693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217360640 :
    ThetaLowerSegment 217360640 217393408 (5433528494809 / 25000) (21737429309771 / 100000) := by
  exact
    packedTile16384 217360640 217393408 12 1727 14743 28 _ _ (383941 / 20000) (479927 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217393408 :
    ThetaLowerSegment 217393408 217426176 (21737429309771 / 100000) (21740715870411 / 100000) := by
  exact
    packedTile16384 217393408 217426176 12 1712 14744 28 _ _ (47993 / 2500) (1919723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217426176 :
    ThetaLowerSegment 217426176 217458944 (21740715870411 / 100000) (21743987098851 / 100000) := by
  exact
    packedTile16384 217426176 217458944 12 1704 14745 28 _ _ (383947 / 20000) (959869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217458944 :
    ThetaLowerSegment 217458944 217491712 (21743987098851 / 100000) (5436798750693 / 25000) := by
  exact
    packedTile16384 217458944 217491712 12 1671 14746 28 _ _ (1919751 / 100000) (959877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217491712 :
    ThetaLowerSegment 217491712 217524480 (5436798750693 / 25000) (2718798206733 / 12500) := by
  exact
    packedTile16384 217491712 217524480 12 1662 14747 28 _ _ (959883 / 50000) (1919769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217524480 :
    ThetaLowerSegment 217524480 217557248 (2718798206733 / 12500) (21753681917841 / 100000) := by
  exact
    packedTile16384 217524480 217557248 12 1717 14748 28 _ _ (1919781 / 100000) (239973 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217557248 :
    ThetaLowerSegment 217557248 217590016 (21753681917841 / 100000) (21756947490837 / 100000) := by
  exact
    packedTile16384 217557248 217590016 12 1701 14749 28 _ _ (479949 / 25000) (1919799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217590016 :
    ThetaLowerSegment 217590016 217622784 (21756947490837 / 100000) (21760199650671 / 100000) := by
  exact
    packedTile16384 217590016 217622784 12 1694 14750 28 _ _ (1919811 / 100000) (959907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217622784 :
    ThetaLowerSegment 217622784 217655552 (21760199650671 / 100000) (21763392321309 / 100000) := by
  exact
    packedTile16384 217622784 217655552 12 1663 14752 28 _ _ (959913 / 50000) (1919829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217655552 :
    ThetaLowerSegment 217655552 217688320 (21763392321309 / 100000) (1088333858463 / 5000) := by
  exact
    packedTile16384 217655552 217688320 12 1711 14753 28 _ _ (1919841 / 100000) (479961 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217688320 :
    ThetaLowerSegment 217688320 217721088 (1088333858463 / 5000) (5442507789423 / 25000) := by
  exact
    packedTile16384 217688320 217721088 12 1747 14754 28 _ _ (119991 / 6250) (1919859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217721088 :
    ThetaLowerSegment 217721088 217753856 (5442507789423 / 25000) (10886641709583 / 50000) := by
  exact
    packedTile16384 217721088 217753856 12 1694 14755 28 _ _ (1919871 / 100000) (959937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217753856 :
    ThetaLowerSegment 217753856 217786624 (10886641709583 / 50000) (2722072002957 / 12500) := by
  exact
    packedTile16384 217753856 217786624 12 1715 14756 28 _ _ (959943 / 50000) (1919889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217786624 :
    ThetaLowerSegment 217786624 217819392 (2722072002957 / 12500) (21779715061791 / 100000) := by
  exact
    packedTile16384 217786624 217819392 12 1635 14757 28 _ _ (1919901 / 100000) (59997 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217819392 :
    ThetaLowerSegment 217819392 217852160 (21779715061791 / 100000) (21782934760923 / 100000) := by
  exact
    packedTile16384 217819392 217852160 12 1677 14758 28 _ _ (479979 / 25000) (1919919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217852160 :
    ThetaLowerSegment 217852160 217884928 (21782934760923 / 100000) (435724625649 / 2000) := by
  exact
    packedTile16384 217852160 217884928 12 1717 14759 28 _ _ (1919931 / 100000) (959967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217884928 :
    ThetaLowerSegment 217884928 217917696 (435724625649 / 2000) (5447393477109 / 25000) := by
  exact
    packedTile16384 217884928 217917696 12 1741 14760 28 _ _ (959973 / 50000) (1919949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217917696 :
    ThetaLowerSegment 217917696 217950464 (5447393477109 / 25000) (21792839762097 / 100000) := by
  exact
    packedTile16384 217917696 217950464 12 1701 14762 28 _ _ (1919961 / 100000) (479991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217950464 :
    ThetaLowerSegment 217950464 217983232 (21792839762097 / 100000) (21796180520337 / 100000) := by
  exact
    packedTile16384 217950464 217983232 12 1740 14763 28 _ _ (239997 / 12500) (1919979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell217983232 :
    ThetaLowerSegment 217983232 218016000 (21796180520337 / 100000) (1362463961571 / 6250) := by
  exact
    packedTile16384 217983232 218016000 12 1689 14764 28 _ _ (1919991 / 100000) (959997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218016000 :
    ThetaLowerSegment 218016000 218048768 (1362463961571 / 6250) (10901317777587 / 50000) := by
  exact
    packedTile16384 218016000 218048768 12 1673 14765 28 _ _ (960003 / 50000) (1920009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218048768 :
    ThetaLowerSegment 218048768 218081536 (10901317777587 / 50000) (4361199502389 / 20000) := by
  exact
    packedTile16384 218048768 218081536 12 1751 14766 28 _ _ (1920021 / 100000) (240003 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218081536 :
    ThetaLowerSegment 218081536 218114304 (4361199502389 / 20000) (21809371015197 / 100000) := by
  exact
    packedTile16384 218081536 218114304 12 1757 14767 28 _ _ (480009 / 25000) (1920039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218114304 :
    ThetaLowerSegment 218114304 218147072 (21809371015197 / 100000) (10906324271127 / 50000) := by
  exact
    packedTile16384 218114304 218147072 12 1707 14768 28 _ _ (1920051 / 100000) (960027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218147072 :
    ThetaLowerSegment 218147072 218179840 (10906324271127 / 50000) (10907975528747 / 50000) := by
  exact
    packedTile16384 218147072 218179840 12 1720 14769 28 _ _ (1920067 / 100000) (192007 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218179840 :
    ThetaLowerSegment 218179840 218212608 (10907975528747 / 50000) (10909630639431 / 50000) := by
  exact
    packedTile16384 218179840 218212608 12 1724 14770 28 _ _ (960041 / 50000) (384017 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218212608 :
    ThetaLowerSegment 218212608 218245376 (10909630639431 / 50000) (21822558085411 / 100000) := by
  exact
    packedTile16384 218212608 218245376 12 1717 14772 28 _ _ (1920097 / 100000) (19201 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218245376 :
    ThetaLowerSegment 218245376 218278144 (21822558085411 / 100000) (21825824195923 / 100000) := by
  exact
    packedTile16384 218245376 218278144 12 1701 14773 28 _ _ (120007 / 6250) (384023 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218278144 :
    ThetaLowerSegment 218278144 218310912 (21825824195923 / 100000) (4365819986517 / 20000) := by
  exact
    packedTile16384 218278144 218310912 12 1706 14774 28 _ _ (1920127 / 100000) (192013 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218310912 :
    ThetaLowerSegment 218310912 218343680 (4365819986517 / 20000) (4366457473661 / 20000) := by
  exact
    packedTile16384 218310912 218343680 12 1660 14775 28 _ _ (960071 / 50000) (384029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218343680 :
    ThetaLowerSegment 218343680 218376448 (4366457473661 / 20000) (5458889348919 / 25000) := by
  exact
    packedTile16384 218343680 218376448 12 1703 14776 28 _ _ (1920157 / 100000) (12001 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218376448 :
    ThetaLowerSegment 218376448 218409216 (5458889348919 / 25000) (5459704461933 / 25000) := by
  exact
    packedTile16384 218376448 218409216 12 1698 14777 28 _ _ (480043 / 25000) (76807 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218409216 :
    ThetaLowerSegment 218409216 218441984 (5459704461933 / 25000) (21842030320583 / 100000) := by
  exact
    packedTile16384 218409216 218441984 12 1673 14778 28 _ _ (1920187 / 100000) (192019 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218441984 :
    ThetaLowerSegment 218441984 218474752 (21842030320583 / 100000) (21845310025599 / 100000) := by
  exact
    packedTile16384 218441984 218474752 12 1708 14779 28 _ _ (960101 / 50000) (384041 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218474752 :
    ThetaLowerSegment 218474752 218507520 (21845310025599 / 100000) (21848593596669 / 100000) := by
  exact
    packedTile16384 218474752 218507520 12 1710 14780 28 _ _ (1920217 / 100000) (96011 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218507520 :
    ThetaLowerSegment 218507520 218540288 (21848593596669 / 100000) (21851779261557 / 100000) := by
  exact
    packedTile16384 218507520 218540288 12 1659 14781 28 _ _ (240029 / 12500) (384047 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218540288 :
    ThetaLowerSegment 218540288 218573056 (21851779261557 / 100000) (10927528561593 / 50000) := by
  exact
    packedTile16384 218540288 218573056 12 1707 14783 28 _ _ (1920247 / 100000) (7681 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218573056 :
    ThetaLowerSegment 218573056 218605824 (10927528561593 / 50000) (10929185747699 / 50000) := by
  exact
    packedTile16384 218573056 218605824 12 1726 14784 28 _ _ (960131 / 50000) (384053 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218605824 :
    ThetaLowerSegment 218605824 218638592 (10929185747699 / 50000) (21861641727129 / 100000) := by
  exact
    packedTile16384 218605824 218638592 12 1703 14785 28 _ _ (1920277 / 100000) (48007 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218638592 :
    ThetaLowerSegment 218638592 218671360 (21861641727129 / 100000) (21864919665573 / 100000) := by
  exact
    packedTile16384 218638592 218671360 12 1707 14786 28 _ _ (480073 / 25000) (384059 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218671360 :
    ThetaLowerSegment 218671360 218704128 (21864919665573 / 100000) (21868172665631 / 100000) := by
  exact
    packedTile16384 218671360 218704128 12 1694 14787 28 _ _ (1920307 / 100000) (192031 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218704128 :
    ThetaLowerSegment 218704128 218736896 (21868172665631 / 100000) (21871435292709 / 100000) := by
  exact
    packedTile16384 218704128 218736896 12 1699 14788 28 _ _ (960161 / 50000) (76813 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218736896 :
    ThetaLowerSegment 218736896 218769664 (21871435292709 / 100000) (874989377267 / 4000) := by
  exact
    packedTile16384 218736896 218769664 12 1718 14789 28 _ _ (1920337 / 100000) (96017 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218769664 :
    ThetaLowerSegment 218769664 218802432 (874989377267 / 4000) (21878079683117 / 100000) := by
  exact
    packedTile16384 218769664 218802432 12 1742 14790 28 _ _ (1920351 / 100000) (960177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218802432 :
    ThetaLowerSegment 218802432 218835200 (21878079683117 / 100000) (21881371190441 / 100000) := by
  exact
    packedTile16384 218802432 218835200 12 1714 14791 28 _ _ (960183 / 50000) (1920369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218835200 :
    ThetaLowerSegment 218835200 218867968 (21881371190441 / 100000) (10942299675451 / 50000) := by
  exact
    packedTile16384 218835200 218867968 12 1681 14793 28 _ _ (1920381 / 100000) (60012 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218867968 :
    ThetaLowerSegment 218867968 218900736 (10942299675451 / 50000) (10943950255813 / 50000) := by
  exact
    packedTile16384 218867968 218900736 12 1719 14794 28 _ _ (480099 / 25000) (1920399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218900736 :
    ThetaLowerSegment 218900736 218933504 (10943950255813 / 50000) (684100713208 / 3125) := by
  exact
    packedTile16384 218900736 218933504 12 1730 14795 28 _ _ (1920411 / 100000) (960207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218933504 :
    ThetaLowerSegment 218933504 218966272 (684100713208 / 3125) (5473632449057 / 25000) := by
  exact
    packedTile16384 218933504 218966272 12 1722 14796 28 _ _ (960213 / 50000) (1920429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218966272 :
    ThetaLowerSegment 218966272 218999040 (5473632449057 / 25000) (1094887038679 / 5000) := by
  exact
    packedTile16384 218966272 218999040 12 1672 14797 28 _ _ (1920441 / 100000) (480111 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell218999040 :
    ThetaLowerSegment 218999040 219031808 (1094887038679 / 5000) (5475246105941 / 25000) := by
  exact
    packedTile16384 218999040 219031808 12 1689 14798 28 _ _ (240057 / 12500) (1920459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219031808 :
    ThetaLowerSegment 219031808 219064576 (5475246105941 / 25000) (10952153419297 / 50000) := by
  exact
    packedTile16384 219031808 219064576 12 1730 14799 28 _ _ (1920471 / 100000) (960237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219064576 :
    ThetaLowerSegment 219064576 219097344 (10952153419297 / 50000) (10953806957743 / 50000) := by
  exact
    packedTile16384 219064576 219097344 12 1722 14800 28 _ _ (960243 / 50000) (1920489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219097344 :
    ThetaLowerSegment 219097344 219130112 (10953806957743 / 50000) (4382179210339 / 20000) := by
  exact
    packedTile16384 219097344 219130112 12 1709 14801 28 _ _ (1920501 / 100000) (240063 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219130112 :
    ThetaLowerSegment 219130112 219162880 (4382179210339 / 20000) (21914134041671 / 100000) := by
  exact
    packedTile16384 219130112 219162880 12 1686 14803 28 _ _ (480129 / 25000) (1920519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219162880 :
    ThetaLowerSegment 219162880 219195648 (21914134041671 / 100000) (21917364374813 / 100000) := by
  exact
    packedTile16384 219162880 219195648 12 1682 14804 28 _ _ (1920531 / 100000) (960267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219195648 :
    ThetaLowerSegment 219195648 219228416 (21917364374813 / 100000) (4384149675373 / 20000) := by
  exact
    packedTile16384 219195648 219228416 12 1762 14805 28 _ _ (960273 / 50000) (1920549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219228416 :
    ThetaLowerSegment 219228416 219261184 (4384149675373 / 20000) (21923971078223 / 100000) := by
  exact
    packedTile16384 219228416 219261184 12 1678 14806 28 _ _ (1920561 / 100000) (480141 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219261184 :
    ThetaLowerSegment 219261184 219293952 (21923971078223 / 100000) (21927320562767 / 100000) := by
  exact
    packedTile16384 219261184 219293952 12 1744 14807 28 _ _ (60018 / 3125) (1920579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219293952 :
    ThetaLowerSegment 219293952 219326720 (21927320562767 / 100000) (1370662918373 / 6250) := by
  exact
    packedTile16384 219293952 219326720 12 1711 14808 28 _ _ (1920591 / 100000) (960297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219326720 :
    ThetaLowerSegment 219326720 219359488 (1370662918373 / 6250) (5483457367709 / 25000) := by
  exact
    packedTile16384 219326720 219359488 12 1678 14809 28 _ _ (960303 / 50000) (1920609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219359488 :
    ThetaLowerSegment 219359488 219392256 (5483457367709 / 25000) (21937065717221 / 100000) := by
  exact
    packedTile16384 219359488 219392256 12 1685 14810 28 _ _ (1920621 / 100000) (120039 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219392256 :
    ThetaLowerSegment 219392256 219425024 (21937065717221 / 100000) (4388050410469 / 20000) := by
  exact
    packedTile16384 219392256 219425024 12 1659 14811 28 _ _ (480159 / 25000) (1920639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219425024 :
    ThetaLowerSegment 219425024 219457792 (4388050410469 / 20000) (10971784508311 / 50000) := by
  exact
    packedTile16384 219425024 219457792 12 1727 14813 28 _ _ (1920651 / 100000) (960327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219457792 :
    ThetaLowerSegment 219457792 219490560 (10971784508311 / 50000) (10973455487731 / 50000) := by
  exact
    packedTile16384 219457792 219490560 12 1740 14814 28 _ _ (960333 / 50000) (1920669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219490560 :
    ThetaLowerSegment 219490560 219523328 (10973455487731 / 50000) (10975070779611 / 50000) := by
  exact
    packedTile16384 219490560 219523328 12 1682 14815 28 _ _ (48017 / 2500) (1920683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219523328 :
    ThetaLowerSegment 219523328 219556096 (10975070779611 / 50000) (21953416344197 / 100000) := by
  exact
    packedTile16384 219523328 219556096 12 1705 14816 28 _ _ (384139 / 20000) (960349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219556096 :
    ThetaLowerSegment 219556096 219588864 (21953416344197 / 100000) (21956673868357 / 100000) := by
  exact
    packedTile16384 219556096 219588864 12 1696 14817 28 _ _ (192071 / 10000) (1920713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219588864 :
    ThetaLowerSegment 219588864 219621632 (21956673868357 / 100000) (10979955144991 / 50000) := by
  exact
    packedTile16384 219588864 219621632 12 1685 14818 28 _ _ (76829 / 4000) (240091 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219621632 :
    ThetaLowerSegment 219621632 219654400 (10979955144991 / 50000) (10981599298431 / 50000) := by
  exact
    packedTile16384 219621632 219654400 12 1712 14819 28 _ _ (96037 / 5000) (1920743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219654400 :
    ThetaLowerSegment 219654400 219687168 (10981599298431 / 50000) (21966511899237 / 100000) := by
  exact
    packedTile16384 219654400 219687168 12 1725 14820 28 _ _ (384151 / 20000) (960379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219687168 :
    ThetaLowerSegment 219687168 219719936 (21966511899237 / 100000) (21969817544407 / 100000) := by
  exact
    packedTile16384 219687168 219719936 12 1721 14821 28 _ _ (192077 / 10000) (1920773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219719936 :
    ThetaLowerSegment 219719936 219752704 (21969817544407 / 100000) (21973113611467 / 100000) := by
  exact
    packedTile16384 219719936 219752704 12 1716 14822 28 _ _ (384157 / 20000) (480197 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219752704 :
    ThetaLowerSegment 219752704 219785472 (21973113611467 / 100000) (21976338634667 / 100000) := by
  exact
    packedTile16384 219752704 219785472 12 1679 14824 28 _ _ (2401 / 125) (1920803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219785472 :
    ThetaLowerSegment 219785472 219818240 (21976338634667 / 100000) (5494887079133 / 25000) := by
  exact
    packedTile16384 219785472 219818240 12 1671 14825 28 _ _ (384163 / 20000) (960409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219818240 :
    ThetaLowerSegment 219818240 219851008 (5494887079133 / 25000) (5495691906903 / 25000) := by
  exact
    packedTile16384 219818240 219851008 12 1676 14826 28 _ _ (192083 / 10000) (1920833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219851008 :
    ThetaLowerSegment 219851008 219883776 (5495691906903 / 25000) (21986054193407 / 100000) := by
  exact
    packedTile16384 219851008 219883776 12 1711 14827 28 _ _ (384169 / 20000) (120053 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219883776 :
    ThetaLowerSegment 219883776 219916544 (21986054193407 / 100000) (21989331178861 / 100000) := by
  exact
    packedTile16384 219883776 219916544 12 1706 14828 28 _ _ (1920859 / 100000) (960431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219916544 :
    ThetaLowerSegment 219916544 219949312 (21989331178861 / 100000) (21992615873401 / 100000) := by
  exact
    packedTile16384 219916544 219949312 12 1710 14829 28 _ _ (960437 / 50000) (1920877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219949312 :
    ThetaLowerSegment 219949312 219982080 (21992615873401 / 100000) (10997930127461 / 50000) := by
  exact
    packedTile16384 219949312 219982080 12 1689 14830 28 _ _ (1920889 / 100000) (480223 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell219982080 :
    ThetaLowerSegment 219982080 220014848 (10997930127461 / 50000) (10999610918461 / 50000) := by
  exact
    packedTile16384 219982080 220014848 12 1750 14831 28 _ _ (240113 / 12500) (1920907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220014848 :
    ThetaLowerSegment 220014848 220047616 (10999610918461 / 50000) (880098497091 / 4000) := by
  exact
    packedTile16384 220014848 220047616 12 1687 14832 28 _ _ (1920919 / 100000) (960461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220047616 :
    ThetaLowerSegment 220047616 220080384 (880098497091 / 4000) (22005666545187 / 100000) := by
  exact
    packedTile16384 220047616 220080384 12 1668 14834 28 _ _ (960467 / 50000) (1920937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220080384 :
    ThetaLowerSegment 220080384 220113152 (22005666545187 / 100000) (22008909107099 / 100000) := by
  exact
    packedTile16384 220080384 220113152 12 1688 14835 28 _ _ (1920949 / 100000) (240119 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220113152 :
    ThetaLowerSegment 220113152 220145920 (22008909107099 / 100000) (22012286161811 / 100000) := by
  exact
    packedTile16384 220113152 220145920 12 1758 14836 28 _ _ (480241 / 25000) (1920967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220145920 :
    ThetaLowerSegment 220145920 220178688 (22012286161811 / 100000) (22015559510027 / 100000) := by
  exact
    packedTile16384 220145920 220178688 12 1704 14837 28 _ _ (1920979 / 100000) (960491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220178688 :
    ThetaLowerSegment 220178688 220211456 (22015559510027 / 100000) (22018848250043 / 100000) := by
  exact
    packedTile16384 220178688 220211456 12 1712 14838 28 _ _ (1920993 / 100000) (480249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220211456 :
    ThetaLowerSegment 220211456 220244224 (22018848250043 / 100000) (4404399356431 / 20000) := by
  exact
    packedTile16384 220211456 220244224 12 1639 14839 28 _ _ (120063 / 6250) (1921011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220244224 :
    ThetaLowerSegment 220244224 220276992 (4404399356431 / 20000) (1376581669049 / 6250) := by
  exact
    packedTile16384 220244224 220276992 12 1723 14840 28 _ _ (1921023 / 100000) (960513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220276992 :
    ThetaLowerSegment 220276992 220309760 (1376581669049 / 6250) (2753563874521 / 12500) := by
  exact
    packedTile16384 220276992 220309760 12 1668 14841 28 _ _ (960519 / 50000) (1921041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220309760 :
    ThetaLowerSegment 220309760 220342528 (2753563874521 / 12500) (22031820970487 / 100000) := by
  exact
    packedTile16384 220309760 220342528 12 1723 14842 28 _ _ (1921053 / 100000) (60033 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220342528 :
    ThetaLowerSegment 220342528 220375296 (22031820970487 / 100000) (22035159786671 / 100000) := by
  exact
    packedTile16384 220342528 220375296 12 1738 14843 28 _ _ (480267 / 25000) (1921071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220375296 :
    ThetaLowerSegment 220375296 220408064 (22035159786671 / 100000) (2754797200087 / 12500) := by
  exact
    packedTile16384 220375296 220408064 12 1675 14845 28 _ _ (1921083 / 100000) (960543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220408064 :
    ThetaLowerSegment 220408064 220440832 (2754797200087 / 12500) (11020832299687 / 50000) := by
  exact
    packedTile16384 220408064 220440832 12 1711 14846 28 _ _ (960549 / 50000) (1921101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220440832 :
    ThetaLowerSegment 220440832 220473600 (11020832299687 / 50000) (11022451797103 / 50000) := by
  exact
    packedTile16384 220440832 220473600 12 1686 14847 28 _ _ (240139 / 12500) (384223 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220473600 :
    ThetaLowerSegment 220473600 220506368 (11022451797103 / 50000) (22048206011519 / 100000) := by
  exact
    packedTile16384 220473600 220506368 12 1719 14848 28 _ _ (1921127 / 100000) (192113 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220506368 :
    ThetaLowerSegment 220506368 220539136 (22048206011519 / 100000) (882058340197 / 4000) := by
  exact
    packedTile16384 220506368 220539136 12 1693 14849 28 _ _ (960571 / 50000) (384229 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220539136 :
    ThetaLowerSegment 220539136 220571904 (882058340197 / 4000) (4410948736679 / 20000) := by
  exact
    packedTile16384 220539136 220571904 12 1710 14850 28 _ _ (1921157 / 100000) (48029 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220571904 :
    ThetaLowerSegment 220571904 220604672 (4410948736679 / 20000) (4411609619847 / 20000) := by
  exact
    packedTile16384 220571904 220604672 12 1720 14851 28 _ _ (480293 / 25000) (76847 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220604672 :
    ThetaLowerSegment 220604672 220637440 (4411609619847 / 20000) (22061302590013 / 100000) := by
  exact
    packedTile16384 220604672 220637440 12 1694 14852 28 _ _ (1921187 / 100000) (192119 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220637440 :
    ThetaLowerSegment 220637440 220670208 (22061302590013 / 100000) (4412927559337 / 20000) := by
  exact
    packedTile16384 220637440 220670208 12 1736 14853 28 _ _ (960601 / 50000) (384241 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220670208 :
    ThetaLowerSegment 220670208 220702976 (4412927559337 / 20000) (22067880809293 / 100000) := by
  exact
    packedTile16384 220670208 220702976 12 1688 14854 28 _ _ (60038 / 3125) (1921219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220702976 :
    ThetaLowerSegment 220702976 220735744 (22067880809293 / 100000) (22071108477373 / 100000) := by
  exact
    packedTile16384 220702976 220735744 12 1680 14856 28 _ _ (1921231 / 100000) (960617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220735744 :
    ThetaLowerSegment 220735744 220768512 (22071108477373 / 100000) (22074355383113 / 100000) := by
  exact
    packedTile16384 220735744 220768512 12 1690 14857 28 _ _ (960623 / 50000) (1921249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220768512 :
    ThetaLowerSegment 220768512 220801280 (22074355383113 / 100000) (22077613841769 / 100000) := by
  exact
    packedTile16384 220768512 220801280 12 1696 14858 28 _ _ (1921261 / 100000) (120079 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220801280 :
    ThetaLowerSegment 220801280 220834048 (22077613841769 / 100000) (22080906908833 / 100000) := by
  exact
    packedTile16384 220801280 220834048 12 1714 14859 28 _ _ (480319 / 25000) (1921279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220834048 :
    ThetaLowerSegment 220834048 220866816 (22080906908833 / 100000) (11042104804031 / 50000) := by
  exact
    packedTile16384 220834048 220866816 12 1719 14860 28 _ _ (1921291 / 100000) (960647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220866816 :
    ThetaLowerSegment 220866816 220899584 (11042104804031 / 50000) (11043739835437 / 50000) := by
  exact
    packedTile16384 220866816 220899584 12 1702 14861 28 _ _ (960653 / 50000) (1921309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220899584 :
    ThetaLowerSegment 220899584 220932352 (11043739835437 / 50000) (11045359508197 / 50000) := by
  exact
    packedTile16384 220899584 220932352 12 1686 14862 28 _ _ (48033 / 2500) (1921323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220932352 :
    ThetaLowerSegment 220932352 220965120 (11045359508197 / 50000) (1380878643539 / 6250) := by
  exact
    packedTile16384 220932352 220965120 12 1738 14863 28 _ _ (384267 / 20000) (960669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220965120 :
    ThetaLowerSegment 220965120 220997888 (1380878643539 / 6250) (11048624829487 / 50000) := by
  exact
    packedTile16384 220965120 220997888 12 1661 14864 28 _ _ (38427 / 2000) (1921353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell220997888 :
    ThetaLowerSegment 220997888 221030656 (11048624829487 / 50000) (22100656239119 / 100000) := by
  exact
    packedTile16384 220997888 221030656 12 1773 14865 28 _ _ (384273 / 20000) (240171 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221030656 :
    ThetaLowerSegment 221030656 221063424 (22100656239119 / 100000) (22104014811359 / 100000) := by
  exact
    packedTile16384 221030656 221063424 12 1748 14867 28 _ _ (96069 / 5000) (1921383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221063424 :
    ThetaLowerSegment 221063424 221096192 (22104014811359 / 100000) (22107173584739 / 100000) := by
  exact
    packedTile16384 221063424 221096192 12 1644 14868 28 _ _ (384279 / 20000) (960699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221096192 :
    ThetaLowerSegment 221096192 221128960 (22107173584739 / 100000) (22110436137221 / 100000) := by
  exact
    packedTile16384 221096192 221128960 12 1698 14869 28 _ _ (1921409 / 100000) (480353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221128960 :
    ThetaLowerSegment 221128960 221161728 (22110436137221 / 100000) (22113756357893 / 100000) := by
  exact
    packedTile16384 221128960 221161728 12 1728 14870 28 _ _ (120089 / 6250) (1921427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221161728 :
    ThetaLowerSegment 221161728 221194496 (22113756357893 / 100000) (691155101237 / 3125) := by
  exact
    packedTile16384 221161728 221194496 12 1669 14871 28 _ _ (1921439 / 100000) (960721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221194496 :
    ThetaLowerSegment 221194496 221227264 (691155101237 / 3125) (691258859753 / 3125) := by
  exact
    packedTile16384 221194496 221227264 12 1728 14872 28 _ _ (960727 / 50000) (1921457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221227264 :
    ThetaLowerSegment 221227264 221260032 (691258859753 / 3125) (22123663376067 / 100000) := by
  exact
    packedTile16384 221227264 221260032 12 1759 14873 28 _ _ (1921469 / 100000) (60046 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221260032 :
    ThetaLowerSegment 221260032 221292800 (22123663376067 / 100000) (5531739679853 / 25000) := by
  exact
    packedTile16384 221260032 221292800 12 1715 14874 28 _ _ (1921483 / 100000) (960743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221292800 :
    ThetaLowerSegment 221292800 221325568 (5531739679853 / 25000) (11065121279747 / 50000) := by
  exact
    packedTile16384 221292800 221325568 12 1709 14875 28 _ _ (960749 / 50000) (1921501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221325568 :
    ThetaLowerSegment 221325568 221358336 (11065121279747 / 50000) (22133530268237 / 100000) := by
  exact
    packedTile16384 221325568 221358336 12 1711 14877 28 _ _ (1921513 / 100000) (480379 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221358336 :
    ThetaLowerSegment 221358336 221391104 (22133530268237 / 100000) (885469645661 / 4000) := by
  exact
    packedTile16384 221358336 221391104 12 1671 14878 28 _ _ (240191 / 12500) (1921531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221391104 :
    ThetaLowerSegment 221391104 221423872 (885469645661 / 4000) (11070041352401 / 50000) := by
  exact
    packedTile16384 221391104 221423872 12 1739 14879 28 _ _ (1921543 / 100000) (960773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221423872 :
    ThetaLowerSegment 221423872 221456640 (11070041352401 / 50000) (2767909541567 / 12500) := by
  exact
    packedTile16384 221423872 221456640 12 1662 14880 28 _ _ (1921557 / 100000) (48039 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221456640 :
    ThetaLowerSegment 221456640 221489408 (2767909541567 / 12500) (2768314993259 / 12500) := by
  exact
    packedTile16384 221456640 221489408 12 1688 14881 28 _ _ (480393 / 25000) (76863 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221489408 :
    ThetaLowerSegment 221489408 221522176 (2768314993259 / 12500) (11074891400399 / 50000) := by
  exact
    packedTile16384 221489408 221522176 12 1698 14882 28 _ _ (1921587 / 100000) (192159 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221522176 :
    ThetaLowerSegment 221522176 221554944 (11074891400399 / 50000) (5538261900649 / 25000) := by
  exact
    packedTile16384 221522176 221554944 12 1699 14883 28 _ _ (960801 / 50000) (384321 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221554944 :
    ThetaLowerSegment 221554944 221587712 (5538261900649 / 25000) (22156339332517 / 100000) := by
  exact
    packedTile16384 221554944 221587712 12 1713 14884 28 _ _ (1921617 / 100000) (96081 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221587712 :
    ThetaLowerSegment 221587712 221620480 (22156339332517 / 100000) (2769956768249 / 12500) := by
  exact
    packedTile16384 221587712 221620480 12 1725 14885 28 _ _ (1921631 / 100000) (960817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221620480 :
    ThetaLowerSegment 221620480 221653248 (2769956768249 / 12500) (2216288827621 / 10000) := by
  exact
    packedTile16384 221620480 221653248 12 1683 14886 28 _ _ (960823 / 50000) (1921649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221653248 :
    ThetaLowerSegment 221653248 221686016 (2216288827621 / 10000) (11083085236599 / 50000) := by
  exact
    packedTile16384 221653248 221686016 12 1708 14888 28 _ _ (1921661 / 100000) (60052 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221686016 :
    ThetaLowerSegment 221686016 221718784 (11083085236599 / 50000) (11084732112931 / 50000) := by
  exact
    packedTile16384 221686016 221718784 12 1714 14889 28 _ _ (480419 / 25000) (1921679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221718784 :
    ThetaLowerSegment 221718784 221751552 (11084732112931 / 50000) (11086338646607 / 50000) := by
  exact
    packedTile16384 221718784 221751552 12 1672 14890 28 _ _ (1921691 / 100000) (960847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221751552 :
    ThetaLowerSegment 221751552 221784320 (11086338646607 / 50000) (11087995156317 / 50000) := by
  exact
    packedTile16384 221751552 221784320 12 1724 14891 28 _ _ (384341 / 20000) (480427 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221784320 :
    ThetaLowerSegment 221784320 221817088 (11087995156317 / 50000) (11089615166277 / 50000) := by
  exact
    packedTile16384 221784320 221817088 12 1686 14892 28 _ _ (48043 / 2500) (1921723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221817088 :
    ThetaLowerSegment 221817088 221849856 (11089615166277 / 50000) (11091275545317 / 50000) := by
  exact
    packedTile16384 221817088 221849856 12 1728 14893 28 _ _ (384347 / 20000) (960869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221849856 :
    ThetaLowerSegment 221849856 221882624 (11091275545317 / 50000) (11092920563317 / 50000) := by
  exact
    packedTile16384 221849856 221882624 12 1712 14894 28 _ _ (7687 / 400) (1921753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221882624 :
    ThetaLowerSegment 221882624 221915392 (11092920563317 / 50000) (11094564632419 / 50000) := by
  exact
    packedTile16384 221882624 221915392 12 1711 14895 28 _ _ (480441 / 25000) (1921767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221915392 :
    ThetaLowerSegment 221915392 221948160 (11094564632419 / 50000) (4438491941569 / 20000) := by
  exact
    packedTile16384 221915392 221948160 12 1733 14896 28 _ _ (1921779 / 100000) (960891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221948160 :
    ThetaLowerSegment 221948160 221980928 (4438491941569 / 20000) (22195642198709 / 100000) := by
  exact
    packedTile16384 221948160 221980928 12 1656 14897 28 _ _ (960897 / 50000) (1921797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell221980928 :
    ThetaLowerSegment 221980928 222013696 (22195642198709 / 100000) (11099490190471 / 50000) := by
  exact
    packedTile16384 221980928 222013696 12 1737 14899 28 _ _ (1921809 / 100000) (480453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222013696 :
    ThetaLowerSegment 222013696 222046464 (11099490190471 / 50000) (22202299369263 / 100000) := by
  exact
    packedTile16384 222013696 222046464 12 1727 14900 28 _ _ (1921823 / 100000) (960913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222046464 :
    ThetaLowerSegment 222046464 222079232 (22202299369263 / 100000) (4441128289109 / 20000) := by
  exact
    packedTile16384 222046464 222079232 12 1739 14901 28 _ _ (960919 / 50000) (1921841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222079232 :
    ThetaLowerSegment 222079232 222112000 (4441128289109 / 20000) (11104436040219 / 50000) := by
  exact
    packedTile16384 222079232 222112000 12 1681 14902 28 _ _ (1921853 / 100000) (60058 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222112000 :
    ThetaLowerSegment 222112000 222144768 (11104436040219 / 50000) (11106115752851 / 50000) := by
  exact
    packedTile16384 222112000 222144768 12 1748 14903 28 _ _ (480467 / 25000) (1921871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222144768 :
    ThetaLowerSegment 222144768 222177536 (11106115752851 / 50000) (11107764727607 / 50000) := by
  exact
    packedTile16384 222144768 222177536 12 1716 14904 28 _ _ (960941 / 50000) (384377 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222177536 :
    ThetaLowerSegment 222177536 222210304 (11107764727607 / 50000) (111094348561 / 500) := by
  exact
    packedTile16384 222177536 222210304 12 1738 14905 28 _ _ (1921897 / 100000) (19219 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222210304 :
    ThetaLowerSegment 222210304 222243072 (111094348561 / 500) (138888416076 / 625) := by
  exact
    packedTile16384 222210304 222243072 12 1705 14906 28 _ _ (240239 / 12500) (384383 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222243072 :
    ThetaLowerSegment 222243072 222275840 (138888416076 / 625) (11112712689811 / 50000) := by
  exact
    packedTile16384 222243072 222275840 12 1706 14907 28 _ _ (1921927 / 100000) (192193 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222275840 :
    ThetaLowerSegment 222275840 222308608 (11112712689811 / 50000) (22228625411387 / 100000) := by
  exact
    packedTile16384 222275840 222308608 12 1665 14908 28 _ _ (1921941 / 100000) (240243 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222308608 :
    ThetaLowerSegment 222308608 222341376 (22228625411387 / 100000) (22231875438983 / 100000) := by
  exact
    packedTile16384 222308608 222341376 12 1691 14910 28 _ _ (480489 / 25000) (1921959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222341376 :
    ThetaLowerSegment 222341376 222374144 (22231875438983 / 100000) (22235115882089 / 100000) := by
  exact
    packedTile16384 222341376 222374144 12 1686 14911 28 _ _ (1921971 / 100000) (960987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222374144 :
    ThetaLowerSegment 222374144 222406912 (22235115882089 / 100000) (4447663582153 / 20000) := by
  exact
    packedTile16384 222374144 222406912 12 1666 14912 28 _ _ (960993 / 50000) (1921989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222406912 :
    ThetaLowerSegment 222406912 222439680 (4447663582153 / 20000) (4448320521753 / 20000) := by
  exact
    packedTile16384 222406912 222439680 12 1709 14913 28 _ _ (961 / 50) (1922003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222439680 :
    ThetaLowerSegment 222439680 222472448 (4448320521753 / 20000) (2224489886449 / 10000) := by
  exact
    packedTile16384 222439680 222472448 12 1715 14914 28 _ _ (384403 / 20000) (961009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222472448 :
    ThetaLowerSegment 222472448 222505216 (2224489886449 / 10000) (278102102969 / 1250) := by
  exact
    packedTile16384 222472448 222505216 12 1701 14915 28 _ _ (192203 / 10000) (1922033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222505216 :
    ThetaLowerSegment 222505216 222537984 (278102102969 / 1250) (890059658133 / 4000) := by
  exact
    packedTile16384 222505216 222537984 12 1729 14916 28 _ _ (384409 / 20000) (60064 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222537984 :
    ThetaLowerSegment 222537984 222570752 (890059658133 / 4000) (1390926879363 / 6250) := by
  exact
    packedTile16384 222537984 222570752 12 1737 14917 28 _ _ (1922059 / 100000) (961031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222570752 :
    ThetaLowerSegment 222570752 222603520 (1390926879363 / 6250) (5564531126161 / 25000) := by
  exact
    packedTile16384 222570752 222603520 12 1714 14918 28 _ _ (961037 / 50000) (1922077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222603520 :
    ThetaLowerSegment 222603520 222636288 (5564531126161 / 25000) (22261397822211 / 100000) := by
  exact
    packedTile16384 222603520 222636288 12 1703 14919 28 _ _ (1922089 / 100000) (480523 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222636288 :
    ThetaLowerSegment 222636288 222669056 (22261397822211 / 100000) (22264765348419 / 100000) := by
  exact
    packedTile16384 222636288 222669056 12 1752 14921 28 _ _ (240263 / 12500) (1922107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222669056 :
    ThetaLowerSegment 222669056 222701824 (22264765348419 / 100000) (4453609280769 / 20000) := by
  exact
    packedTile16384 222669056 222701824 12 1707 14922 28 _ _ (961059 / 50000) (1922121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222701824 :
    ThetaLowerSegment 222701824 222734592 (4453609280769 / 20000) (4454255117457 / 20000) := by
  exact
    packedTile16384 222701824 222734592 12 1680 14923 28 _ _ (1922133 / 100000) (240267 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222734592 :
    ThetaLowerSegment 222734592 222767360 (4454255117457 / 20000) (22274549005329 / 100000) := by
  exact
    packedTile16384 222734592 222767360 12 1703 14924 28 _ _ (480537 / 25000) (1922151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222767360 :
    ThetaLowerSegment 222767360 222800128 (22274549005329 / 100000) (22277808992081 / 100000) := by
  exact
    packedTile16384 222767360 222800128 12 1696 14925 28 _ _ (961081 / 50000) (384433 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222800128 :
    ThetaLowerSegment 222800128 222832896 (22277808992081 / 100000) (11140500864039 / 50000) := by
  exact
    packedTile16384 222800128 222832896 12 1661 14926 28 _ _ (1922177 / 100000) (96109 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222832896 :
    ThetaLowerSegment 222832896 222865664 (11140500864039 / 50000) (11142162599023 / 50000) := by
  exact
    packedTile16384 222832896 222865664 12 1729 14927 28 _ _ (120137 / 6250) (384439 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222865664 :
    ThetaLowerSegment 222865664 222898432 (11142162599023 / 50000) (2785935422813 / 12500) := by
  exact
    packedTile16384 222865664 222898432 12 1643 14928 28 _ _ (961103 / 50000) (1922209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222898432 :
    ThetaLowerSegment 222898432 222931200 (2785935422813 / 12500) (22290833813707 / 100000) := by
  exact
    packedTile16384 222898432 222931200 12 1743 14929 28 _ _ (1922221 / 100000) (120139 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222931200 :
    ThetaLowerSegment 222931200 222963968 (22290833813707 / 100000) (22294128526211 / 100000) := by
  exact
    packedTile16384 222931200 222963968 12 1714 14930 28 _ _ (480559 / 25000) (1922239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222963968 :
    ThetaLowerSegment 222963968 222996736 (22294128526211 / 100000) (11148733738099 / 50000) := by
  exact
    packedTile16384 222963968 222996736 12 1737 14931 28 _ _ (1922251 / 100000) (961127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell222996736 :
    ThetaLowerSegment 222996736 223029504 (11148733738099 / 50000) (11150375352409 / 50000) := by
  exact
    packedTile16384 222996736 223029504 12 1708 14933 28 _ _ (384453 / 20000) (480567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223029504 :
    ThetaLowerSegment 223029504 223062272 (11150375352409 / 50000) (11152025629789 / 50000) := by
  exact
    packedTile16384 223029504 223062272 12 1717 14934 28 _ _ (48057 / 2500) (1922283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223062272 :
    ThetaLowerSegment 223062272 223095040 (11152025629789 / 50000) (22307278792883 / 100000) := by
  exact
    packedTile16384 223062272 223095040 12 1679 14935 28 _ _ (384459 / 20000) (961149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223095040 :
    ThetaLowerSegment 223095040 223127808 (22307278792883 / 100000) (11155280087173 / 50000) := by
  exact
    packedTile16384 223095040 223127808 12 1707 14936 28 _ _ (1922309 / 100000) (240289 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223127808 :
    ThetaLowerSegment 223127808 223160576 (11155280087173 / 50000) (2231390694043 / 10000) := by
  exact
    packedTile16384 223127808 223160576 12 1741 14937 28 _ _ (480581 / 25000) (1922327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223160576 :
    ThetaLowerSegment 223160576 223193344 (2231390694043 / 10000) (1394825594927 / 6250) := by
  exact
    packedTile16384 223160576 223193344 12 1718 14938 28 _ _ (1922339 / 100000) (961171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223193344 :
    ThetaLowerSegment 223193344 223226112 (1394825594927 / 6250) (5580138603263 / 25000) := by
  exact
    packedTile16384 223193344 223226112 12 1740 14939 28 _ _ (1922353 / 100000) (480589 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223226112 :
    ThetaLowerSegment 223226112 223258880 (5580138603263 / 25000) (5580975794527 / 25000) := by
  exact
    packedTile16384 223226112 223258880 12 1742 14940 28 _ _ (60074 / 3125) (1922371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223258880 :
    ThetaLowerSegment 223258880 223291648 (5580975794527 / 25000) (22327142393463 / 100000) := by
  exact
    packedTile16384 223258880 223291648 12 1685 14941 28 _ _ (1922383 / 100000) (961193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223291648 :
    ThetaLowerSegment 223291648 223324416 (22327142393463 / 100000) (11165269634481 / 50000) := by
  exact
    packedTile16384 223291648 223324416 12 1767 14942 28 _ _ (1922397 / 100000) (2403 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223324416 :
    ThetaLowerSegment 223324416 223357184 (11165269634481 / 50000) (11166841206291 / 50000) := by
  exact
    packedTile16384 223324416 223357184 12 1635 14944 28 _ _ (480603 / 25000) (384483 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223357184 :
    ThetaLowerSegment 223357184 223389952 (11166841206291 / 50000) (5584240518261 / 25000) := by
  exact
    packedTile16384 223357184 223389952 12 1706 14945 28 _ _ (1922427 / 100000) (192243 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223389952 :
    ThetaLowerSegment 223389952 223422720 (5584240518261 / 25000) (22340282128651 / 100000) := by
  exact
    packedTile16384 223389952 223422720 12 1727 14946 28 _ _ (1922441 / 100000) (480611 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223422720 :
    ThetaLowerSegment 223422720 223455488 (22340282128651 / 100000) (22343581063147 / 100000) := by
  exact
    packedTile16384 223422720 223455488 12 1716 14947 28 _ _ (240307 / 12500) (1922459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223455488 :
    ThetaLowerSegment 223455488 223488256 (22343581063147 / 100000) (22346918472803 / 100000) := by
  exact
    packedTile16384 223455488 223488256 12 1736 14948 28 _ _ (1922471 / 100000) (961237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223488256 :
    ThetaLowerSegment 223488256 223521024 (22346918472803 / 100000) (2793787996111 / 12500) := by
  exact
    packedTile16384 223488256 223521024 12 1761 14949 28 _ _ (384497 / 20000) (240311 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223521024 :
    ThetaLowerSegment 223521024 223553792 (2793787996111 / 12500) (5588404109097 / 25000) := by
  exact
    packedTile16384 223521024 223553792 12 1723 14950 28 _ _ (769 / 40) (1922503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223553792 :
    ThetaLowerSegment 223553792 223586560 (5588404109097 / 25000) (5589219255457 / 25000) := by
  exact
    packedTile16384 223553792 223586560 12 1696 14951 28 _ _ (384503 / 20000) (961259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223586560 :
    ThetaLowerSegment 223586560 223619328 (5589219255457 / 25000) (4472030217743 / 20000) := by
  exact
    packedTile16384 223586560 223619328 12 1703 14952 28 _ _ (1922529 / 100000) (480633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223619328 :
    ThetaLowerSegment 223619328 223652096 (4472030217743 / 20000) (22363488625099 / 100000) := by
  exact
    packedTile16384 223619328 223652096 12 1736 14953 28 _ _ (120159 / 6250) (1922547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223652096 :
    ThetaLowerSegment 223652096 223684864 (22363488625099 / 100000) (22366776200989 / 100000) := by
  exact
    packedTile16384 223652096 223684864 12 1710 14955 28 _ _ (1922559 / 100000) (961281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223684864 :
    ThetaLowerSegment 223684864 223717632 (22366776200989 / 100000) (22370013813921 / 100000) := by
  exact
    packedTile16384 223684864 223717632 12 1684 14956 28 _ _ (1922573 / 100000) (120161 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223717632 :
    ThetaLowerSegment 223717632 223750400 (22370013813921 / 100000) (22373284136109 / 100000) := by
  exact
    packedTile16384 223717632 223750400 12 1701 14957 28 _ _ (480647 / 25000) (1922591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223750400 :
    ThetaLowerSegment 223750400 223783168 (22373284136109 / 100000) (139852936808 / 625) := by
  exact
    packedTile16384 223750400 223783168 12 1657 14958 28 _ _ (1922603 / 100000) (961303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223783168 :
    ThetaLowerSegment 223783168 223815936 (139852936808 / 625) (11189874936941 / 50000) := by
  exact
    packedTile16384 223783168 223815936 12 1706 14959 28 _ _ (1922617 / 100000) (96131 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223815936 :
    ThetaLowerSegment 223815936 223848704 (11189874936941 / 50000) (11191494754401 / 50000) := by
  exact
    packedTile16384 223815936 223848704 12 1685 14960 28 _ _ (240329 / 12500) (384527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223848704 :
    ThetaLowerSegment 223848704 223881472 (11191494754401 / 50000) (11193121313763 / 50000) := by
  exact
    packedTile16384 223848704 223881472 12 1692 14961 28 _ _ (1922647 / 100000) (38453 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223881472 :
    ThetaLowerSegment 223881472 223914240 (11193121313763 / 50000) (22389524609853 / 100000) := by
  exact
    packedTile16384 223881472 223914240 12 1707 14962 28 _ _ (1922661 / 100000) (240333 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223914240 :
    ThetaLowerSegment 223914240 223947008 (22389524609853 / 100000) (22392697025253 / 100000) := by
  exact
    packedTile16384 223914240 223947008 12 1650 14963 28 _ _ (480669 / 25000) (1922679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223947008 :
    ThetaLowerSegment 223947008 223979776 (22392697025253 / 100000) (5598968808369 / 25000) := by
  exact
    packedTile16384 223947008 223979776 12 1653 14964 28 _ _ (1922691 / 100000) (961347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell223979776 :
    ThetaLowerSegment 223979776 224012544 (5598968808369 / 25000) (11199600756563 / 50000) := by
  exact
    packedTile16384 223979776 224012544 12 1730 14965 28 _ _ (384541 / 20000) (480677 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224012544 :
    ThetaLowerSegment 224012544 224045312 (11199600756563 / 50000) (11201257179843 / 50000) := by
  exact
    packedTile16384 224012544 224045312 12 1723 14967 28 _ _ (12017 / 625) (1922723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224045312 :
    ThetaLowerSegment 224045312 224078080 (11201257179843 / 50000) (5601452000757 / 25000) := by
  exact
    packedTile16384 224045312 224078080 12 1713 14968 28 _ _ (961367 / 50000) (1922737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224078080 :
    ThetaLowerSegment 224078080 224110848 (5601452000757 / 25000) (11204540260913 / 50000) := by
  exact
    packedTile16384 224078080 224110848 12 1702 14969 28 _ _ (1922749 / 100000) (60086 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224110848 :
    ThetaLowerSegment 224110848 224143616 (11204540260913 / 50000) (11206187108279 / 50000) := by
  exact
    packedTile16384 224110848 224143616 12 1713 14970 28 _ _ (480691 / 25000) (1922767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224143616 :
    ThetaLowerSegment 224143616 224176384 (11206187108279 / 50000) (11207817624023 / 50000) := by
  exact
    packedTile16384 224143616 224176384 12 1696 14971 28 _ _ (961389 / 50000) (1922781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224176384 :
    ThetaLowerSegment 224176384 224209152 (11207817624023 / 50000) (2802364441613 / 12500) := by
  exact
    packedTile16384 224176384 224209152 12 1706 14972 28 _ _ (1922793 / 100000) (480699 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224209152 :
    ThetaLowerSegment 224209152 224241920 (2802364441613 / 12500) (22422332360943 / 100000) := by
  exact
    packedTile16384 224209152 224241920 12 1777 14973 28 _ _ (1922807 / 100000) (192281 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224241920 :
    ThetaLowerSegment 224241920 224274688 (22422332360943 / 100000) (22425581930123 / 100000) := by
  exact
    packedTile16384 224241920 224274688 12 1690 14974 28 _ _ (961411 / 50000) (76913 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224274688 :
    ThetaLowerSegment 224274688 224307456 (22425581930123 / 100000) (11214439797789 / 50000) := by
  exact
    packedTile16384 224274688 224307456 12 1715 14975 28 _ _ (1922837 / 100000) (48071 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224307456 :
    ThetaLowerSegment 224307456 224340224 (11214439797789 / 50000) (22432196513553 / 100000) := by
  exact
    packedTile16384 224307456 224340224 12 1725 14976 28 _ _ (1922851 / 100000) (961427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224340224 :
    ThetaLowerSegment 224340224 224372992 (22432196513553 / 100000) (22435484614413 / 100000) := by
  exact
    packedTile16384 224340224 224372992 12 1710 14977 28 _ _ (961433 / 50000) (1922869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224372992 :
    ThetaLowerSegment 224372992 224405760 (22435484614413 / 100000) (224388054299 / 1000) := by
  exact
    packedTile16384 224372992 224405760 12 1727 14979 28 _ _ (1922881 / 100000) (480721 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224405760 :
    ThetaLowerSegment 224405760 224438528 (224388054299 / 1000) (4488400640857 / 20000) := by
  exact
    packedTile16384 224405760 224438528 12 1663 14980 28 _ _ (384579 / 20000) (961449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224438528 :
    ThetaLowerSegment 224438528 224471296 (4488400640857 / 20000) (4489057506913 / 20000) := by
  exact
    packedTile16384 224438528 224471296 12 1708 14981 28 _ _ (192291 / 10000) (1922913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224471296 :
    ThetaLowerSegment 224471296 224504064 (4489057506913 / 20000) (22448562274137 / 100000) := by
  exact
    packedTile16384 224471296 224504064 12 1703 14982 28 _ _ (480731 / 25000) (1922927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224504064 :
    ThetaLowerSegment 224504064 224536832 (22448562274137 / 100000) (4490370869141 / 20000) := by
  exact
    packedTile16384 224504064 224536832 12 1712 14983 28 _ _ (1922939 / 100000) (961471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224536832 :
    ThetaLowerSegment 224536832 224569600 (4490370869141 / 20000) (22455138751137 / 100000) := by
  exact
    packedTile16384 224536832 224569600 12 1708 14984 28 _ _ (961477 / 50000) (1922957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224569600 :
    ThetaLowerSegment 224569600 224602368 (22455138751137 / 100000) (22458430872353 / 100000) := by
  exact
    packedTile16384 224569600 224602368 12 1712 14985 28 _ _ (240371 / 12500) (1922971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224602368 :
    ThetaLowerSegment 224602368 224635136 (22458430872353 / 100000) (4492329989179 / 20000) := by
  exact
    packedTile16384 224602368 224635136 12 1674 14986 28 _ _ (1922983 / 100000) (961493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224635136 :
    ThetaLowerSegment 224635136 224667904 (4492329989179 / 20000) (1404057560237 / 6250) := by
  exact
    packedTile16384 224635136 224667904 12 1701 14987 28 _ _ (1922997 / 100000) (1923 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224667904 :
    ThetaLowerSegment 224667904 224700672 (1404057560237 / 6250) (5617041271259 / 25000) := by
  exact
    packedTile16384 224667904 224700672 12 1687 14988 28 _ _ (480753 / 25000) (384603 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224700672 :
    ThetaLowerSegment 224700672 224733440 (5617041271259 / 25000) (11235718076131 / 50000) := by
  exact
    packedTile16384 224700672 224733440 12 1701 14990 28 _ _ (961513 / 50000) (1923029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224733440 :
    ThetaLowerSegment 224733440 224766208 (11235718076131 / 50000) (449492875693 / 2000) := by
  exact
    packedTile16384 224733440 224766208 12 1668 14991 28 _ _ (1923041 / 100000) (480761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224766208 :
    ThetaLowerSegment 224766208 224798976 (449492875693 / 2000) (11238934374781 / 50000) := by
  exact
    packedTile16384 224766208 224798976 12 1677 14992 28 _ _ (120191 / 6250) (1923059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224798976 :
    ThetaLowerSegment 224798976 224831744 (11238934374781 / 50000) (11240553599721 / 50000) := by
  exact
    packedTile16384 224798976 224831744 12 1684 14993 28 _ _ (192307 / 10000) (1923073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224831744 :
    ThetaLowerSegment 224831744 224864512 (11240553599721 / 50000) (11242188221971 / 50000) := by
  exact
    packedTile16384 224831744 224864512 12 1700 14994 28 _ _ (384617 / 20000) (120193 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224864512 :
    ThetaLowerSegment 224864512 224897280 (11242188221971 / 50000) (4497547219579 / 20000) := by
  exact
    packedTile16384 224864512 224897280 12 1747 14995 28 _ _ (1923099 / 100000) (961551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224897280 :
    ThetaLowerSegment 224897280 224930048 (4497547219579 / 20000) (22491020776607 / 100000) := by
  exact
    packedTile16384 224897280 224930048 12 1708 14996 28 _ _ (961557 / 50000) (1923117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224930048 :
    ThetaLowerSegment 224930048 224962816 (22491020776607 / 100000) (11247167163937 / 50000) := by
  exact
    packedTile16384 224930048 224962816 12 1723 14997 28 _ _ (1923129 / 100000) (480783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224962816 :
    ThetaLowerSegment 224962816 224995584 (11247167163937 / 50000) (11248824913203 / 50000) := by
  exact
    packedTile16384 224962816 224995584 12 1724 14998 28 _ _ (1923143 / 100000) (961573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell224995584 :
    ThetaLowerSegment 224995584 225028352 (11248824913203 / 50000) (5625237972173 / 25000) := by
  exact
    packedTile16384 224995584 225028352 12 1717 14999 28 _ _ (961579 / 50000) (1923161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225028352 :
    ThetaLowerSegment 225028352 225061120 (5625237972173 / 25000) (1406513229077 / 6250) := by
  exact
    packedTile16384 225028352 225061120 12 1695 15000 28 _ _ (480793 / 25000) (76927 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225061120 :
    ThetaLowerSegment 225061120 225093888 (1406513229077 / 6250) (4501499678363 / 20000) := by
  exact
    packedTile16384 225061120 225093888 12 1709 15002 28 _ _ (1923187 / 100000) (192319 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225093888 :
    ThetaLowerSegment 225093888 225126656 (4501499678363 / 20000) (11255375262353 / 50000) := by
  exact
    packedTile16384 225093888 225126656 12 1691 15003 28 _ _ (1923201 / 100000) (480801 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225126656 :
    ThetaLowerSegment 225126656 225159424 (11255375262353 / 50000) (11256991725401 / 50000) := by
  exact
    packedTile16384 225126656 225159424 12 1681 15004 28 _ _ (120201 / 6250) (1923219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225159424 :
    ThetaLowerSegment 225159424 225192192 (11256991725401 / 50000) (703664454936 / 3125) := by
  exact
    packedTile16384 225159424 225192192 12 1705 15005 28 _ _ (192323 / 10000) (1923233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225192192 :
    ThetaLowerSegment 225192192 225224960 (703664454936 / 3125) (1407530850597 / 6250) := by
  exact
    packedTile16384 225192192 225224960 12 1680 15006 28 _ _ (384649 / 20000) (120203 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225224960 :
    ThetaLowerSegment 225224960 225257728 (1407530850597 / 6250) (5630930690773 / 25000) := by
  exact
    packedTile16384 225224960 225257728 12 1679 15007 28 _ _ (96163 / 5000) (1923263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225257728 :
    ThetaLowerSegment 225257728 225290496 (5630930690773 / 25000) (11263487509713 / 50000) := by
  exact
    packedTile16384 225257728 225290496 12 1691 15008 28 _ _ (961637 / 50000) (1923277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225290496 :
    ThetaLowerSegment 225290496 225323264 (11263487509713 / 50000) (11265122305363 / 50000) := by
  exact
    packedTile16384 225290496 225323264 12 1700 15009 28 _ _ (1923289 / 100000) (480823 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225323264 :
    ThetaLowerSegment 225323264 225356032 (11265122305363 / 50000) (5633373748199 / 25000) := by
  exact
    packedTile16384 225323264 225356032 12 1690 15010 28 _ _ (1923303 / 100000) (961653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225356032 :
    ThetaLowerSegment 225356032 225388800 (5633373748199 / 25000) (11268389048311 / 50000) := by
  exact
    packedTile16384 225356032 225388800 12 1707 15011 28 _ _ (961659 / 50000) (1923321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225388800 :
    ThetaLowerSegment 225388800 225421568 (11268389048311 / 50000) (11270021957179 / 50000) := by
  exact
    packedTile16384 225388800 225421568 12 1698 15012 28 _ _ (480833 / 25000) (384667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225421568 :
    ThetaLowerSegment 225421568 225454336 (11270021957179 / 50000) (704477227832 / 3125) := by
  exact
    packedTile16384 225421568 225454336 12 1678 15014 28 _ _ (1923347 / 100000) (38467 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225454336 :
    ThetaLowerSegment 225454336 225487104 (704477227832 / 3125) (22546519847353 / 100000) := by
  exact
    packedTile16384 225454336 225487104 12 1689 15015 28 _ _ (1923361 / 100000) (480841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225487104 :
    ThetaLowerSegment 225487104 225519872 (22546519847353 / 100000) (22549751119033 / 100000) := by
  exact
    packedTile16384 225487104 225519872 12 1680 15016 28 _ _ (120211 / 6250) (1923379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225519872 :
    ThetaLowerSegment 225519872 225552640 (22549751119033 / 100000) (22553049732883 / 100000) := by
  exact
    packedTile16384 225519872 225552640 12 1715 15017 28 _ _ (192339 / 10000) (1923393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225552640 :
    ThetaLowerSegment 225552640 225585408 (22553049732883 / 100000) (22556369529913 / 100000) := by
  exact
    packedTile16384 225552640 225585408 12 1726 15018 28 _ _ (384681 / 20000) (120213 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225585408 :
    ThetaLowerSegment 225585408 225618176 (22556369529913 / 100000) (22559639342213 / 100000) := by
  exact
    packedTile16384 225585408 225618176 12 1700 15019 28 _ _ (1923419 / 100000) (961711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225618176 :
    ThetaLowerSegment 225618176 225650944 (22559639342213 / 100000) (4512567602591 / 20000) := by
  exact
    packedTile16384 225618176 225650944 12 1663 15020 28 _ _ (961717 / 50000) (1923437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225650944 :
    ThetaLowerSegment 225650944 225683712 (4512567602591 / 20000) (4513213881119 / 20000) := by
  exact
    packedTile16384 225650944 225683712 12 1680 15021 28 _ _ (240431 / 12500) (1923451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225683712 :
    ThetaLowerSegment 225683712 225716480 (4513213881119 / 20000) (4513879399317 / 20000) := by
  exact
    packedTile16384 225683712 225716480 12 1730 15022 28 _ _ (1923463 / 100000) (961733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225716480 :
    ThetaLowerSegment 225716480 225749248 (4513879399317 / 20000) (4514537228793 / 20000) := by
  exact
    packedTile16384 225716480 225749248 12 1710 15023 28 _ _ (961739 / 50000) (1923481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225749248 :
    ThetaLowerSegment 225749248 225782016 (4514537228793 / 20000) (22575909916557 / 100000) := by
  exact
    packedTile16384 225749248 225782016 12 1676 15024 28 _ _ (480873 / 25000) (384699 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225782016 :
    ThetaLowerSegment 225782016 225814784 (22575909916557 / 100000) (22579252971723 / 100000) := by
  exact
    packedTile16384 225782016 225814784 12 1738 15026 28 _ _ (1923507 / 100000) (192351 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225814784 :
    ThetaLowerSegment 225814784 225847552 (22579252971723 / 100000) (22582557580801 / 100000) := by
  exact
    packedTile16384 225814784 225847552 12 1718 15027 28 _ _ (1923521 / 100000) (480881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225847552 :
    ThetaLowerSegment 225847552 225880320 (22582557580801 / 100000) (22585842980289 / 100000) := by
  exact
    packedTile16384 225847552 225880320 12 1708 15028 28 _ _ (120221 / 6250) (1923539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225880320 :
    ThetaLowerSegment 225880320 225913088 (22585842980289 / 100000) (22589166874689 / 100000) := by
  exact
    packedTile16384 225880320 225913088 12 1728 15029 28 _ _ (38471 / 2000) (1923553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225913088 :
    ThetaLowerSegment 225913088 225945856 (22589166874689 / 100000) (22592448476579 / 100000) := by
  exact
    packedTile16384 225913088 225945856 12 1706 15030 28 _ _ (384713 / 20000) (120223 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225945856 :
    ThetaLowerSegment 225945856 225978624 (22592448476579 / 100000) (4519145251039 / 20000) := by
  exact
    packedTile16384 225945856 225978624 12 1704 15031 28 _ _ (1923579 / 100000) (961791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell225978624 :
    ThetaLowerSegment 225978624 226011392 (4519145251039 / 20000) (4519793502217 / 20000) := by
  exact
    packedTile16384 225978624 226011392 12 1685 15032 28 _ _ (961797 / 50000) (1923597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226011392 :
    ThetaLowerSegment 226011392 226044160 (4519793502217 / 20000) (22602272269629 / 100000) := by
  exact
    packedTile16384 226011392 226044160 12 1718 15033 28 _ _ (240451 / 12500) (1923611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226044160 :
    ThetaLowerSegment 226044160 226076928 (22602272269629 / 100000) (22605573206697 / 100000) := by
  exact
    packedTile16384 226044160 226076928 12 1716 15034 28 _ _ (1923623 / 100000) (961813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226076928 :
    ThetaLowerSegment 226076928 226109696 (22605573206697 / 100000) (706527738539 / 3125) := by
  exact
    packedTile16384 226076928 226109696 12 1723 15035 28 _ _ (1923637 / 100000) (48091 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226109696 :
    ThetaLowerSegment 226109696 226142464 (706527738539 / 3125) (5653053406889 / 25000) := by
  exact
    packedTile16384 226109696 226142464 12 1729 15036 28 _ _ (480913 / 25000) (384731 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226142464 :
    ThetaLowerSegment 226142464 226175232 (5653053406889 / 25000) (11307737120713 / 50000) := by
  exact
    packedTile16384 226142464 226175232 12 1695 15038 28 _ _ (961833 / 50000) (1923669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226175232 :
    ThetaLowerSegment 226175232 226208000 (11307737120713 / 50000) (11309360707477 / 50000) := by
  exact
    packedTile16384 226175232 226208000 12 1688 15039 28 _ _ (1923681 / 100000) (480921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226208000 :
    ThetaLowerSegment 226208000 226240768 (11309360707477 / 50000) (22622001314929 / 100000) := by
  exact
    packedTile16384 226208000 226240768 12 1705 15040 28 _ _ (384739 / 20000) (961849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226240768 :
    ThetaLowerSegment 226240768 226273536 (22622001314929 / 100000) (22625217758049 / 100000) := by
  exact
    packedTile16384 226240768 226273536 12 1672 15041 28 _ _ (192371 / 10000) (1923713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226273536 :
    ThetaLowerSegment 226273536 226306304 (22625217758049 / 100000) (22628530410777 / 100000) := by
  exact
    packedTile16384 226273536 226306304 12 1722 15042 28 _ _ (480931 / 25000) (1923727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226306304 :
    ThetaLowerSegment 226306304 226339072 (22628530410777 / 100000) (4526370156513 / 20000) := by
  exact
    packedTile16384 226306304 226339072 12 1726 15043 28 _ _ (961869 / 50000) (1923741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226339072 :
    ThetaLowerSegment 226339072 226371840 (4526370156513 / 20000) (22635086535111 / 100000) := by
  exact
    packedTile16384 226339072 226371840 12 1682 15044 28 _ _ (1923753 / 100000) (480939 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226371840 :
    ThetaLowerSegment 226371840 226404608 (22635086535111 / 100000) (11319167888787 / 50000) := by
  exact
    packedTile16384 226371840 226404608 12 1689 15045 28 _ _ (1923767 / 100000) (192377 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226404608 :
    ThetaLowerSegment 226404608 226437376 (11319167888787 / 50000) (1415102672427 / 6250) := by
  exact
    packedTile16384 226404608 226437376 12 1719 15046 28 _ _ (961891 / 50000) (384757 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226437376 :
    ThetaLowerSegment 226437376 226470144 (1415102672427 / 6250) (5661228783957 / 25000) := by
  exact
    packedTile16384 226437376 226470144 12 1701 15047 28 _ _ (480949 / 25000) (1923799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226470144 :
    ThetaLowerSegment 226470144 226502912 (5661228783957 / 25000) (22648149062119 / 100000) := by
  exact
    packedTile16384 226470144 226502912 12 1681 15048 28 _ _ (1923811 / 100000) (961907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226502912 :
    ThetaLowerSegment 226502912 226535680 (22648149062119 / 100000) (1415716247809 / 6250) := by
  exact
    packedTile16384 226502912 226535680 12 1721 15050 28 _ _ (76953 / 4000) (480957 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226535680 :
    ThetaLowerSegment 226535680 226568448 (1415716247809 / 6250) (1415920174849 / 6250) := by
  exact
    packedTile16384 226535680 226568448 12 1696 15051 28 _ _ (12024 / 625) (1923843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226568448 :
    ThetaLowerSegment 226568448 226601216 (1415920174849 / 6250) (11328972626517 / 50000) := by
  exact
    packedTile16384 226568448 226601216 12 1675 15052 28 _ _ (961927 / 50000) (1923857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226601216 :
    ThetaLowerSegment 226601216 226633984 (11328972626517 / 50000) (2266126200319 / 10000) := by
  exact
    packedTile16384 226601216 226633984 12 1724 15053 28 _ _ (1923869 / 100000) (60121 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226633984 :
    ThetaLowerSegment 226633984 226666752 (2266126200319 / 10000) (283306898039 / 1250) := by
  exact
    packedTile16384 226633984 226666752 12 1710 15054 28 _ _ (1923883 / 100000) (961943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226666752 :
    ThetaLowerSegment 226666752 226699520 (283306898039 / 1250) (11333917968503 / 50000) := by
  exact
    packedTile16384 226666752 226699520 12 1707 15055 28 _ _ (961949 / 50000) (1923901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226699520 :
    ThetaLowerSegment 226699520 226732288 (11333917968503 / 50000) (11335583114339 / 50000) := by
  exact
    packedTile16384 226699520 226732288 12 1731 15056 28 _ _ (240489 / 12500) (384783 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226732288 :
    ThetaLowerSegment 226732288 226765056 (11335583114339 / 50000) (22674450372067 / 100000) := by
  exact
    packedTile16384 226732288 226765056 12 1707 15057 28 _ _ (1923927 / 100000) (192393 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226765056 :
    ThetaLowerSegment 226765056 226797824 (22674450372067 / 100000) (5669434596809 / 25000) := by
  exact
    packedTile16384 226765056 226797824 12 1709 15058 28 _ _ (1923941 / 100000) (240493 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226797824 :
    ThetaLowerSegment 226797824 226830592 (5669434596809 / 25000) (11340479543953 / 50000) := by
  exact
    packedTile16384 226797824 226830592 12 1674 15059 28 _ _ (384791 / 20000) (961979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226830592 :
    ThetaLowerSegment 226830592 226863360 (11340479543953 / 50000) (1417766649521 / 6250) := by
  exact
    packedTile16384 226830592 226863360 12 1719 15060 28 _ _ (192397 / 10000) (1923973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226863360 :
    ThetaLowerSegment 226863360 226896128 (1417766649521 / 6250) (708987761017 / 3125) := by
  exact
    packedTile16384 226863360 226896128 12 1737 15061 28 _ _ (120249 / 6250) (1923987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226896128 :
    ThetaLowerSegment 226896128 226928896 (708987761017 / 3125) (11345422259431 / 50000) := by
  exact
    packedTile16384 226896128 226928896 12 1682 15063 28 _ _ (1923999 / 100000) (962001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226928896 :
    ThetaLowerSegment 226928896 226961664 (11345422259431 / 50000) (22694086480767 / 100000) := by
  exact
    packedTile16384 226928896 226961664 12 1685 15064 28 _ _ (1924013 / 100000) (120251 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226961664 :
    ThetaLowerSegment 226961664 226994432 (22694086480767 / 100000) (22697353480311 / 100000) := by
  exact
    packedTile16384 226961664 226994432 12 1698 15065 28 _ _ (481007 / 25000) (1924031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell226994432 :
    ThetaLowerSegment 226994432 227027200 (22697353480311 / 100000) (22700674376803 / 100000) := by
  exact
    packedTile16384 226994432 227027200 12 1726 15066 28 _ _ (962021 / 50000) (384809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227027200 :
    ThetaLowerSegment 227027200 227059968 (22700674376803 / 100000) (22704006843527 / 100000) := by
  exact
    packedTile16384 227027200 227059968 12 1732 15067 28 _ _ (1924057 / 100000) (96203 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227059968 :
    ThetaLowerSegment 227059968 227092736 (22704006843527 / 100000) (5676815111897 / 25000) := by
  exact
    packedTile16384 227059968 227092736 12 1691 15068 28 _ _ (1924071 / 100000) (962037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227092736 :
    ThetaLowerSegment 227092736 227125504 (5676815111897 / 25000) (22710483289963 / 100000) := by
  exact
    packedTile16384 227092736 227125504 12 1675 15069 28 _ _ (384817 / 20000) (240511 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227125504 :
    ThetaLowerSegment 227125504 227158272 (22710483289963 / 100000) (22713808134763 / 100000) := by
  exact
    packedTile16384 227125504 227158272 12 1728 15070 28 _ _ (19241 / 1000) (1924103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227158272 :
    ThetaLowerSegment 227158272 227191040 (22713808134763 / 100000) (22717090673247 / 100000) := by
  exact
    packedTile16384 227158272 227191040 12 1706 15071 28 _ _ (962057 / 50000) (1924117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227191040 :
    ThetaLowerSegment 227191040 227223808 (22717090673247 / 100000) (11360179884209 / 50000) := by
  exact
    packedTile16384 227191040 227223808 12 1699 15072 28 _ _ (1924129 / 100000) (481033 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227223808 :
    ThetaLowerSegment 227223808 227256576 (11360179884209 / 50000) (11361823102331 / 50000) := by
  exact
    packedTile16384 227223808 227256576 12 1708 15073 28 _ _ (1924143 / 100000) (962073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227256576 :
    ThetaLowerSegment 227256576 227289344 (11361823102331 / 50000) (11363443243367 / 50000) := by
  exact
    packedTile16384 227256576 227289344 12 1684 15075 28 _ _ (962079 / 50000) (1924161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227289344 :
    ThetaLowerSegment 227289344 227322112 (11363443243367 / 50000) (11365098031287 / 50000) := by
  exact
    packedTile16384 227289344 227322112 12 1720 15076 28 _ _ (481043 / 25000) (76967 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227322112 :
    ThetaLowerSegment 227322112 227354880 (11365098031287 / 50000) (5683377858763 / 25000) := by
  exact
    packedTile16384 227322112 227354880 12 1723 15077 28 _ _ (962093 / 50000) (1924189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227354880 :
    ThetaLowerSegment 227354880 227387648 (5683377858763 / 25000) (5684193719987 / 25000) := by
  exact
    packedTile16384 227354880 227387648 12 1696 15078 28 _ _ (1924201 / 100000) (481051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227387648 :
    ThetaLowerSegment 227387648 227420416 (5684193719987 / 25000) (5685013435577 / 25000) := by
  exact
    packedTile16384 227387648 227420416 12 1704 15079 28 _ _ (384843 / 20000) (962109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227420416 :
    ThetaLowerSegment 227420416 227453184 (5685013435577 / 25000) (5685840854477 / 25000) := by
  exact
    packedTile16384 227420416 227453184 12 1720 15080 28 _ _ (192423 / 10000) (1924233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227453184 :
    ThetaLowerSegment 227453184 227485952 (5685840854477 / 25000) (5686665393031 / 25000) := by
  exact
    packedTile16384 227453184 227485952 12 1714 15081 28 _ _ (481061 / 25000) (1924247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227485952 :
    ThetaLowerSegment 227485952 227518720 (5686665393031 / 25000) (11374936579363 / 50000) := by
  exact
    packedTile16384 227485952 227518720 12 1669 15082 28 _ _ (962129 / 50000) (1924261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227518720 :
    ThetaLowerSegment 227518720 227551488 (11374936579363 / 50000) (11376529877407 / 50000) := by
  exact
    packedTile16384 227518720 227551488 12 1656 15083 28 _ _ (1924273 / 100000) (481069 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227551488 :
    ThetaLowerSegment 227551488 227584256 (11376529877407 / 50000) (22756282935539 / 100000) := by
  exact
    packedTile16384 227551488 227584256 12 1675 15084 28 _ _ (1924287 / 100000) (192429 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227584256 :
    ThetaLowerSegment 227584256 227617024 (22756282935539 / 100000) (22759629296717 / 100000) := by
  exact
    packedTile16384 227584256 227617024 12 1739 15085 28 _ _ (962151 / 50000) (384861 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227617024 :
    ThetaLowerSegment 227617024 227649792 (22759629296717 / 100000) (4552562038213 / 20000) := by
  exact
    packedTile16384 227617024 227649792 12 1653 15086 28 _ _ (481079 / 25000) (1924319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227649792 :
    ThetaLowerSegment 227649792 227682560 (4552562038213 / 20000) (182127990447 / 800) := by
  exact
    packedTile16384 227649792 227682560 12 1657 15088 28 _ _ (192433 / 10000) (1924333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227682560 :
    ThetaLowerSegment 227682560 227715328 (182127990447 / 800) (4553844031881 / 20000) := by
  exact
    packedTile16384 227682560 227715328 12 1674 15089 28 _ _ (384869 / 20000) (481087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227715328 :
    ThetaLowerSegment 227715328 227748096 (4553844031881 / 20000) (22772499267141 / 100000) := by
  exact
    packedTile16384 227715328 227748096 12 1704 15090 28 _ _ (1924359 / 100000) (962181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227748096 :
    ThetaLowerSegment 227748096 227780864 (22772499267141 / 100000) (22775770702941 / 100000) := by
  exact
    packedTile16384 227748096 227780864 12 1700 15091 28 _ _ (962187 / 50000) (1924377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227780864 :
    ThetaLowerSegment 227780864 227813632 (22775770702941 / 100000) (22779094121017 / 100000) := by
  exact
    packedTile16384 227780864 227813632 12 1727 15092 28 _ _ (481097 / 25000) (1924391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227813632 :
    ThetaLowerSegment 227813632 227846400 (22779094121017 / 100000) (4556468887199 / 20000) := by
  exact
    packedTile16384 227813632 227846400 12 1689 15093 28 _ _ (962201 / 50000) (384881 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227846400 :
    ThetaLowerSegment 227846400 227879168 (4556468887199 / 20000) (911423868029 / 4000) := by
  exact
    packedTile16384 227846400 227879168 12 1690 15094 28 _ _ (1924417 / 100000) (96221 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227879168 :
    ThetaLowerSegment 227879168 227911936 (911423868029 / 4000) (11394425456773 / 50000) := by
  exact
    packedTile16384 227879168 227911936 12 1691 15095 28 _ _ (1924431 / 100000) (962217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227911936 :
    ThetaLowerSegment 227911936 227944704 (11394425456773 / 50000) (2849008092087 / 12500) := by
  exact
    packedTile16384 227911936 227944704 12 1670 15096 28 _ _ (384889 / 20000) (60139 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227944704 :
    ThetaLowerSegment 227944704 227977472 (2849008092087 / 12500) (2849418964297 / 12500) := by
  exact
    packedTile16384 227944704 227977472 12 1708 15097 28 _ _ (96223 / 5000) (1924463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell227977472 :
    ThetaLowerSegment 227977472 228010240 (2849418964297 / 12500) (5699637547541 / 25000) := by
  exact
    packedTile16384 227977472 228010240 12 1662 15098 28 _ _ (962237 / 50000) (1924477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228010240 :
    ThetaLowerSegment 228010240 228043008 (5699637547541 / 25000) (5700441983943 / 25000) := by
  exact
    packedTile16384 228010240 228043008 12 1672 15100 28 _ _ (1924489 / 100000) (481123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228043008 :
    ThetaLowerSegment 228043008 228075776 (5700441983943 / 25000) (11402537115963 / 50000) := by
  exact
    packedTile16384 228043008 228075776 12 1718 15101 28 _ _ (1924503 / 100000) (962253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228075776 :
    ThetaLowerSegment 228075776 228108544 (11402537115963 / 50000) (11404219143821 / 50000) := by
  exact
    packedTile16384 228075776 228108544 12 1748 15102 28 _ _ (1924517 / 100000) (48113 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228108544 :
    ThetaLowerSegment 228108544 228141312 (11404219143821 / 50000) (11405904071587 / 50000) := by
  exact
    packedTile16384 228108544 228141312 12 1751 15103 28 _ _ (481133 / 25000) (384907 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228141312 :
    ThetaLowerSegment 228141312 228174080 (11405904071587 / 50000) (11407570728423 / 50000) := by
  exact
    packedTile16384 228141312 228174080 12 1732 15104 28 _ _ (962273 / 50000) (1924549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228174080 :
    ThetaLowerSegment 228174080 228206848 (11407570728423 / 50000) (11409215264943 / 50000) := by
  exact
    packedTile16384 228174080 228206848 12 1709 15105 28 _ _ (24057 / 1250) (1924563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228206848 :
    ThetaLowerSegment 228206848 228239616 (11409215264943 / 50000) (11410855002843 / 50000) := by
  exact
    packedTile16384 228206848 228239616 12 1704 15106 28 _ _ (76983 / 4000) (962289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228239616 :
    ThetaLowerSegment 228239616 228272384 (11410855002843 / 50000) (11412471657603 / 50000) := by
  exact
    packedTile16384 228239616 228272384 12 1680 15107 28 _ _ (1924589 / 100000) (120287 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228272384 :
    ThetaLowerSegment 228272384 228305152 (11412471657603 / 50000) (11414106608701 / 50000) := by
  exact
    packedTile16384 228272384 228305152 12 1699 15108 28 _ _ (481151 / 25000) (1924607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228305152 :
    ThetaLowerSegment 228305152 228337920 (11414106608701 / 50000) (11415750232473 / 50000) := by
  exact
    packedTile16384 228305152 228337920 12 1708 15109 28 _ _ (962309 / 50000) (1924621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228337920 :
    ThetaLowerSegment 228337920 228370688 (11415750232473 / 50000) (2283469920333 / 10000) := by
  exact
    packedTile16384 228337920 228370688 12 1662 15110 28 _ _ (240579 / 12500) (384927 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228370688 :
    ThetaLowerSegment 228370688 228403456 (2283469920333 / 10000) (11419020195261 / 50000) := by
  exact
    packedTile16384 228370688 228403456 12 1736 15111 28 _ _ (1924647 / 100000) (38493 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228403456 :
    ThetaLowerSegment 228403456 228436224 (11419020195261 / 50000) (4568263617641 / 20000) := by
  exact
    packedTile16384 228403456 228436224 12 1703 15113 28 _ _ (1924661 / 100000) (240583 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228436224 :
    ThetaLowerSegment 228436224 228468992 (4568263617641 / 20000) (142778844103 / 625) := by
  exact
    packedTile16384 228436224 228468992 12 1713 15114 28 _ _ (76987 / 4000) (962339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228468992 :
    ThetaLowerSegment 228468992 228501760 (142778844103 / 625) (2284784661099 / 10000) := by
  exact
    packedTile16384 228468992 228501760 12 1679 15115 28 _ _ (192469 / 10000) (1924693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228501760 :
    ThetaLowerSegment 228501760 228534528 (2284784661099 / 10000) (2285113785483 / 10000) := by
  exact
    packedTile16384 228501760 228534528 12 1710 15116 28 _ _ (60147 / 3125) (1924707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228534528 :
    ThetaLowerSegment 228534528 228567296 (2285113785483 / 10000) (5713608724191 / 25000) := by
  exact
    packedTile16384 228534528 228567296 12 1713 15117 28 _ _ (962359 / 50000) (1924721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228567296 :
    ThetaLowerSegment 228567296 228600064 (5713608724191 / 25000) (4571538309 / 20) := by
  exact
    packedTile16384 228567296 228600064 12 1692 15118 28 _ _ (1924733 / 100000) (60148 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228600064 :
    ThetaLowerSegment 228600064 228632832 (4571538309 / 20) (22861004034587 / 100000) := by
  exact
    packedTile16384 228600064 228632832 12 1721 15119 28 _ _ (1924747 / 100000) (7699 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228632832 :
    ThetaLowerSegment 228632832 228665600 (22861004034587 / 100000) (11432148650329 / 50000) := by
  exact
    packedTile16384 228632832 228665600 12 1711 15120 28 _ _ (1924761 / 100000) (481191 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228665600 :
    ThetaLowerSegment 228665600 228698368 (11432148650329 / 50000) (11433854964253 / 50000) := by
  exact
    packedTile16384 228665600 228698368 12 1773 15121 28 _ _ (240597 / 12500) (1924779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228698368 :
    ThetaLowerSegment 228698368 228731136 (11433854964253 / 50000) (1429434093781 / 6250) := by
  exact
    packedTile16384 228698368 228731136 12 1681 15122 28 _ _ (192479 / 10000) (1924793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228731136 :
    ThetaLowerSegment 228731136 228763904 (1429434093781 / 6250) (5718563559643 / 25000) := by
  exact
    packedTile16384 228731136 228763904 12 1719 15123 28 _ _ (481201 / 25000) (1924807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228763904 :
    ThetaLowerSegment 228763904 228796672 (5718563559643 / 25000) (22877493708949 / 100000) := by
  exact
    packedTile16384 228763904 228796672 12 1683 15124 28 _ _ (1924819 / 100000) (962411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228796672 :
    ThetaLowerSegment 228796672 228829440 (22877493708949 / 100000) (1430046787597 / 6250) := by
  exact
    packedTile16384 228796672 228829440 12 1691 15126 28 _ _ (1924833 / 100000) (481209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228829440 :
    ThetaLowerSegment 228829440 228862208 (1430046787597 / 6250) (22883953471807 / 100000) := by
  exact
    packedTile16384 228829440 228862208 12 1665 15127 28 _ _ (1924847 / 100000) (38497 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228862208 :
    ThetaLowerSegment 228862208 228894976 (22883953471807 / 100000) (22887183390243 / 100000) := by
  exact
    packedTile16384 228862208 228894976 12 1678 15128 28 _ _ (962431 / 50000) (384973 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228894976 :
    ThetaLowerSegment 228894976 228927744 (22887183390243 / 100000) (22890549998367 / 100000) := by
  exact
    packedTile16384 228894976 228927744 12 1749 15129 28 _ _ (481219 / 25000) (1924879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228927744 :
    ThetaLowerSegment 228927744 228960512 (22890549998367 / 100000) (22893797287797 / 100000) := by
  exact
    packedTile16384 228927744 228960512 12 1687 15130 28 _ _ (192489 / 10000) (1924893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228960512 :
    ThetaLowerSegment 228960512 228993280 (22893797287797 / 100000) (22897219768887 / 100000) := by
  exact
    packedTile16384 228960512 228993280 12 1778 15131 28 _ _ (384981 / 20000) (481227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell228993280 :
    ThetaLowerSegment 228993280 229026048 (22897219768887 / 100000) (11450266277243 / 50000) := by
  exact
    packedTile16384 228993280 229026048 12 1721 15132 28 _ _ (1924919 / 100000) (962461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229026048 :
    ThetaLowerSegment 229026048 229058816 (11450266277243 / 50000) (22903814565251 / 100000) := by
  exact
    packedTile16384 229026048 229058816 12 1705 15133 28 _ _ (1924933 / 100000) (240617 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229058816 :
    ThetaLowerSegment 229058816 229091584 (22903814565251 / 100000) (11453505951109 / 50000) := by
  exact
    packedTile16384 229058816 229091584 12 1661 15134 28 _ _ (1924947 / 100000) (38499 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229091584 :
    ThetaLowerSegment 229091584 229124352 (11453505951109 / 50000) (5727577340531 / 25000) := by
  exact
    packedTile16384 229091584 229124352 12 1713 15135 28 _ _ (962481 / 50000) (384993 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229124352 :
    ThetaLowerSegment 229124352 229157120 (5727577340531 / 25000) (5728380536767 / 25000) := by
  exact
    packedTile16384 229124352 229157120 12 1669 15136 28 _ _ (120311 / 6250) (1924979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229157120 :
    ThetaLowerSegment 229157120 229189888 (5728380536767 / 25000) (11458421377409 / 50000) := by
  exact
    packedTile16384 229157120 229189888 12 1725 15137 28 _ _ (192499 / 10000) (1924993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229189888 :
    ThetaLowerSegment 229189888 229222656 (11458421377409 / 50000) (22920074838213 / 100000) := by
  exact
    packedTile16384 229189888 229222656 12 1679 15139 28 _ _ (385001 / 20000) (120313 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229222656 :
    ThetaLowerSegment 229222656 229255424 (22920074838213 / 100000) (22923262669677 / 100000) := by
  exact
    packedTile16384 229222656 229255424 12 1656 15140 28 _ _ (1925019 / 100000) (962511 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229255424 :
    ThetaLowerSegment 229255424 229288192 (22923262669677 / 100000) (22926462074523 / 100000) := by
  exact
    packedTile16384 229255424 229288192 12 1662 15141 28 _ _ (1925033 / 100000) (481259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229288192 :
    ThetaLowerSegment 229288192 229320960 (22926462074523 / 100000) (4585944621167 / 20000) := by
  exact
    packedTile16384 229288192 229320960 12 1694 15142 28 _ _ (240631 / 12500) (1925051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229320960 :
    ThetaLowerSegment 229320960 229353728 (4585944621167 / 20000) (22933041912723 / 100000) := by
  exact
    packedTile16384 229320960 229353728 12 1724 15143 28 _ _ (962531 / 50000) (385013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229353728 :
    ThetaLowerSegment 229353728 229386496 (22933041912723 / 100000) (22936310691771 / 100000) := by
  exact
    packedTile16384 229353728 229386496 12 1698 15144 28 _ _ (481269 / 25000) (1925079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229386496 :
    ThetaLowerSegment 229386496 229419264 (22936310691771 / 100000) (22939585269861 / 100000) := by
  exact
    packedTile16384 229386496 229419264 12 1701 15145 28 _ _ (192509 / 10000) (1925093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229419264 :
    ThetaLowerSegment 229419264 229452032 (22939585269861 / 100000) (11471433786943 / 50000) := by
  exact
    packedTile16384 229419264 229452032 12 1705 15146 28 _ _ (385021 / 20000) (481277 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229452032 :
    ThetaLowerSegment 229452032 229484800 (11471433786943 / 50000) (22946119099877 / 100000) := by
  exact
    packedTile16384 229452032 229484800 12 1689 15147 28 _ _ (1925119 / 100000) (962561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229484800 :
    ThetaLowerSegment 229484800 229517568 (22946119099877 / 100000) (4589888375887 / 20000) := by
  exact
    packedTile16384 229484800 229517568 12 1726 15148 28 _ _ (1925133 / 100000) (120321 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229517568 :
    ThetaLowerSegment 229517568 229550336 (4589888375887 / 20000) (22952614523339 / 100000) := by
  exact
    packedTile16384 229517568 229550336 12 1648 15149 28 _ _ (481287 / 25000) (1925151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229550336 :
    ThetaLowerSegment 229550336 229583104 (22952614523339 / 100000) (22956006658783 / 100000) := by
  exact
    packedTile16384 229550336 229583104 12 1762 15150 28 _ _ (962581 / 50000) (385033 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229583104 :
    ThetaLowerSegment 229583104 229615872 (22956006658783 / 100000) (22959185124359 / 100000) := by
  exact
    packedTile16384 229583104 229615872 12 1651 15152 28 _ _ (240647 / 12500) (1925179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229615872 :
    ThetaLowerSegment 229615872 229648640 (22959185124359 / 100000) (22962477199259 / 100000) := by
  exact
    packedTile16384 229615872 229648640 12 1710 15153 28 _ _ (192519 / 10000) (1925193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229648640 :
    ThetaLowerSegment 229648640 229681408 (22962477199259 / 100000) (11482893313327 / 50000) := by
  exact
    packedTile16384 229648640 229681408 12 1719 15154 28 _ _ (385041 / 20000) (240651 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229681408 :
    ThetaLowerSegment 229681408 229714176 (11482893313327 / 50000) (2871138694331 / 12500) := by
  exact
    packedTile16384 229681408 229714176 12 1726 15155 28 _ _ (1925219 / 100000) (962611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229714176 :
    ThetaLowerSegment 229714176 229746944 (2871138694331 / 12500) (11486162346879 / 50000) := by
  exact
    packedTile16384 229714176 229746944 12 1670 15156 28 _ _ (1925233 / 100000) (481309 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229746944 :
    ThetaLowerSegment 229746944 229779712 (11486162346879 / 50000) (11487841162263 / 50000) := by
  exact
    packedTile16384 229746944 229779712 12 1744 15157 28 _ _ (1925247 / 100000) (7701 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229779712 :
    ThetaLowerSegment 229779712 229812480 (11487841162263 / 50000) (2872376869131 / 12500) := by
  exact
    packedTile16384 229779712 229812480 12 1731 15158 28 _ _ (962631 / 50000) (385053 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229812480 :
    ThetaLowerSegment 229812480 229845248 (2872376869131 / 12500) (5745549358569 / 25000) := by
  exact
    packedTile16384 229812480 229845248 12 1653 15159 28 _ _ (481319 / 25000) (1925279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229845248 :
    ThetaLowerSegment 229845248 229878016 (5745549358569 / 25000) (5746363756239 / 25000) := by
  exact
    packedTile16384 229845248 229878016 12 1692 15160 28 _ _ (192529 / 10000) (1925293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229878016 :
    ThetaLowerSegment 229878016 229910784 (5746363756239 / 25000) (5747181047787 / 25000) := by
  exact
    packedTile16384 229878016 229910784 12 1698 15161 28 _ _ (240663 / 12500) (1925307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229910784 :
    ThetaLowerSegment 229910784 229943552 (5747181047787 / 25000) (22992076171527 / 100000) := by
  exact
    packedTile16384 229910784 229943552 12 1741 15162 28 _ _ (1925319 / 100000) (962661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229943552 :
    ThetaLowerSegment 229943552 229976320 (22992076171527 / 100000) (22995410848283 / 100000) := by
  exact
    packedTile16384 229943552 229976320 12 1732 15163 28 _ _ (1925333 / 100000) (240667 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell229976320 :
    ThetaLowerSegment 229976320 230009088 (22995410848283 / 100000) (11499369886623 / 50000) := by
  exact
    packedTile16384 229976320 230009088 12 1729 15164 28 _ _ (1925347 / 100000) (38507 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230009088 :
    ThetaLowerSegment 230009088 230041856 (11499369886623 / 50000) (2300205909561 / 10000) := by
  exact
    packedTile16384 230009088 230041856 12 1724 15166 28 _ _ (1925361 / 100000) (481341 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230041856 :
    ThetaLowerSegment 230041856 230074624 (2300205909561 / 10000) (11502618945693 / 50000) := by
  exact
    packedTile16384 230041856 230074624 12 1651 15167 28 _ _ (60168 / 3125) (1925379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230074624 :
    ThetaLowerSegment 230074624 230107392 (11502618945693 / 50000) (1438038800101 / 6250) := by
  exact
    packedTile16384 230074624 230107392 12 1757 15168 28 _ _ (192539 / 10000) (1925393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230107392 :
    ThetaLowerSegment 230107392 230140160 (1438038800101 / 6250) (2876479528287 / 12500) := by
  exact
    packedTile16384 230107392 230140160 12 1670 15169 28 _ _ (481351 / 25000) (1925407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230140160 :
    ThetaLowerSegment 230140160 230172928 (2876479528287 / 12500) (719221207194 / 3125) := by
  exact
    packedTile16384 230140160 230172928 12 1684 15170 28 _ _ (962709 / 50000) (1925421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230172928 :
    ThetaLowerSegment 230172928 230205696 (719221207194 / 3125) (11509200963783 / 50000) := by
  exact
    packedTile16384 230172928 230205696 12 1726 15171 28 _ _ (1925433 / 100000) (481359 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230205696 :
    ThetaLowerSegment 230205696 230238464 (11509200963783 / 50000) (23021627051291 / 100000) := by
  exact
    packedTile16384 230205696 230238464 12 1675 15172 28 _ _ (1925447 / 100000) (38509 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230238464 :
    ThetaLowerSegment 230238464 230271232 (23021627051291 / 100000) (11512441502921 / 50000) := by
  exact
    packedTile16384 230238464 230271232 12 1691 15173 28 _ _ (1925461 / 100000) (240683 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230271232 :
    ThetaLowerSegment 230271232 230304000 (11512441502921 / 50000) (23028169791667 / 100000) := by
  exact
    packedTile16384 230271232 230304000 12 1707 15174 28 _ _ (77019 / 4000) (962739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230304000 :
    ThetaLowerSegment 230304000 230336768 (23028169791667 / 100000) (23031402689377 / 100000) := by
  exact
    packedTile16384 230304000 230336768 12 1679 15175 28 _ _ (192549 / 10000) (1925493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230336768 :
    ThetaLowerSegment 230336768 230369536 (23031402689377 / 100000) (23034629834081 / 100000) := by
  exact
    packedTile16384 230336768 230369536 12 1676 15176 28 _ _ (60172 / 3125) (1925507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230369536 :
    ThetaLowerSegment 230369536 230402304 (23034629834081 / 100000) (23037920544343 / 100000) := by
  exact
    packedTile16384 230369536 230402304 12 1709 15177 28 _ _ (962759 / 50000) (1925521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230402304 :
    ThetaLowerSegment 230402304 230435072 (23037920544343 / 100000) (4608246876983 / 20000) := by
  exact
    packedTile16384 230402304 230435072 12 1721 15179 28 _ _ (481383 / 25000) (385107 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230435072 :
    ThetaLowerSegment 230435072 230467840 (4608246876983 / 20000) (23044580983863 / 100000) := by
  exact
    packedTile16384 230435072 230467840 12 1738 15180 28 _ _ (962773 / 50000) (1925549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230467840 :
    ThetaLowerSegment 230467840 230500608 (23044580983863 / 100000) (460955817881 / 2000) := by
  exact
    packedTile16384 230467840 230500608 12 1667 15181 28 _ _ (1925561 / 100000) (481391 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230500608 :
    ThetaLowerSegment 230500608 230533376 (460955817881 / 2000) (36881798503 / 160) := by
  exact
    packedTile16384 230500608 230533376 12 1731 15182 28 _ _ (77023 / 4000) (962789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230533376 :
    ThetaLowerSegment 230533376 230566144 (36881798503 / 160) (23054447630989 / 100000) := by
  exact
    packedTile16384 230533376 230566144 12 1726 15183 28 _ _ (1925589 / 100000) (240699 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230566144 :
    ThetaLowerSegment 230566144 230598912 (23054447630989 / 100000) (11528875020067 / 50000) := by
  exact
    packedTile16384 230566144 230598912 12 1715 15184 28 _ _ (1925603 / 100000) (962803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230598912 :
    ThetaLowerSegment 230598912 230631680 (11528875020067 / 50000) (11530534902783 / 50000) := by
  exact
    packedTile16384 230598912 230631680 12 1724 15185 28 _ _ (962809 / 50000) (1925621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230631680 :
    ThetaLowerSegment 230631680 230664448 (11530534902783 / 50000) (11532194797567 / 50000) := by
  exact
    packedTile16384 230631680 230664448 12 1724 15186 28 _ _ (60176 / 3125) (385127 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230664448 :
    ThetaLowerSegment 230664448 230697216 (11532194797567 / 50000) (2883459584107 / 12500) := by
  exact
    packedTile16384 230664448 230697216 12 1707 15187 28 _ _ (962823 / 50000) (1925649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230697216 :
    ThetaLowerSegment 230697216 230729984 (2883459584107 / 12500) (5767723612679 / 25000) := by
  exact
    packedTile16384 230697216 230729984 12 1671 15188 28 _ _ (96283 / 5000) (1925663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230729984 :
    ThetaLowerSegment 230729984 230762752 (5767723612679 / 25000) (5768553578173 / 25000) := by
  exact
    packedTile16384 230729984 230762752 12 1724 15189 28 _ _ (962837 / 50000) (1925677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230762752 :
    ThetaLowerSegment 230762752 230795520 (5768553578173 / 25000) (11538792134221 / 50000) := by
  exact
    packedTile16384 230762752 230795520 12 1750 15190 28 _ _ (1925689 / 100000) (481423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230795520 :
    ThetaLowerSegment 230795520 230828288 (11538792134221 / 50000) (11540394319117 / 50000) := by
  exact
    packedTile16384 230795520 230828288 12 1664 15191 28 _ _ (1925703 / 100000) (962853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230828288 :
    ThetaLowerSegment 230828288 230861056 (11540394319117 / 50000) (2308411627721 / 10000) := by
  exact
    packedTile16384 230828288 230861056 12 1728 15193 28 _ _ (1925717 / 100000) (48143 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230861056 :
    ThetaLowerSegment 230861056 230893824 (2308411627721 / 10000) (11543652643873 / 50000) := by
  exact
    packedTile16384 230861056 230893824 12 1656 15194 28 _ _ (1925731 / 100000) (962867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230893824 :
    ThetaLowerSegment 230893824 230926592 (11543652643873 / 50000) (11545320339043 / 50000) := by
  exact
    packedTile16384 230893824 230926592 12 1732 15195 28 _ _ (385149 / 20000) (481437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230926592 :
    ThetaLowerSegment 230926592 230959360 (11545320339043 / 50000) (11546960123683 / 50000) := by
  exact
    packedTile16384 230926592 230959360 12 1703 15196 28 _ _ (12036 / 625) (1925763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230959360 :
    ThetaLowerSegment 230959360 230992128 (11546960123683 / 50000) (5774302848783 / 25000) := by
  exact
    packedTile16384 230959360 230992128 12 1709 15197 28 _ _ (962887 / 50000) (1925777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell230992128 :
    ThetaLowerSegment 230992128 231024896 (5774302848783 / 25000) (1155024839473 / 5000) := by
  exact
    packedTile16384 230992128 231024896 12 1706 15198 28 _ _ (481447 / 25000) (1925791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231024896 :
    ThetaLowerSegment 231024896 231057664 (1155024839473 / 5000) (5775934960007 / 25000) := by
  exact
    packedTile16384 231024896 231057664 12 1684 15199 28 _ _ (962901 / 50000) (385161 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231057664 :
    ThetaLowerSegment 231057664 231090432 (5775934960007 / 25000) (5776751024537 / 25000) := by
  exact
    packedTile16384 231057664 231090432 12 1695 15200 28 _ _ (240727 / 12500) (1925819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231090432 :
    ThetaLowerSegment 231090432 231123200 (5776751024537 / 25000) (11555130338339 / 50000) := by
  exact
    packedTile16384 231090432 231123200 12 1691 15201 28 _ _ (192583 / 10000) (1925833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231123200 :
    ThetaLowerSegment 231123200 231155968 (11555130338339 / 50000) (23113582759303 / 100000) := by
  exact
    packedTile16384 231123200 231155968 12 1725 15202 28 _ _ (385169 / 20000) (240731 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231155968 :
    ThetaLowerSegment 231155968 231188736 (23113582759303 / 100000) (4623362870141 / 20000) := by
  exact
    packedTile16384 231155968 231188736 12 1678 15203 28 _ _ (1925859 / 100000) (962931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231188736 :
    ThetaLowerSegment 231188736 231221504 (4623362870141 / 20000) (23120130704011 / 100000) := by
  exact
    packedTile16384 231188736 231221504 12 1722 15204 28 _ _ (1925873 / 100000) (481469 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231221504 :
    ThetaLowerSegment 231221504 231254272 (23120130704011 / 100000) (11561714874221 / 50000) := by
  exact
    packedTile16384 231221504 231254272 12 1713 15205 28 _ _ (1925887 / 100000) (192589 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231254272 :
    ThetaLowerSegment 231254272 231287040 (11561714874221 / 50000) (23126655632617 / 100000) := by
  exact
    packedTile16384 231254272 231287040 12 1675 15207 28 _ _ (1925901 / 100000) (120369 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231287040 :
    ThetaLowerSegment 231287040 231319808 (23126655632617 / 100000) (23130000948709 / 100000) := by
  exact
    packedTile16384 231287040 231319808 12 1737 15208 28 _ _ (481479 / 25000) (1925919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231319808 :
    ThetaLowerSegment 231319808 231352576 (23130000948709 / 100000) (23133321252029 / 100000) := by
  exact
    packedTile16384 231319808 231352576 12 1724 15209 28 _ _ (192593 / 10000) (1925933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231352576 :
    ThetaLowerSegment 231352576 231385344 (23133321252029 / 100000) (4627320612121 / 20000) := by
  exact
    packedTile16384 231352576 231385344 12 1704 15210 28 _ _ (240743 / 12500) (1925947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231385344 :
    ThetaLowerSegment 231385344 231418112 (4627320612121 / 20000) (4627992771463 / 20000) := by
  exact
    packedTile16384 231385344 231418112 12 1745 15211 28 _ _ (962979 / 50000) (1925961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231418112 :
    ThetaLowerSegment 231418112 231450880 (4627992771463 / 20000) (23143197564303 / 100000) := by
  exact
    packedTile16384 231418112 231450880 12 1679 15212 28 _ _ (481493 / 25000) (77039 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231450880 :
    ThetaLowerSegment 231450880 231483648 (23143197564303 / 100000) (23146450554657 / 100000) := by
  exact
    packedTile16384 231450880 231483648 12 1689 15213 28 _ _ (962993 / 50000) (1925989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231483648 :
    ThetaLowerSegment 231483648 231516416 (23146450554657 / 100000) (23149778682657 / 100000) := by
  exact
    packedTile16384 231483648 231516416 12 1728 15214 28 _ _ (963 / 50) (1926003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231516416 :
    ThetaLowerSegment 231516416 231549184 (23149778682657 / 100000) (23152945051317 / 100000) := by
  exact
    packedTile16384 231516416 231549184 12 1644 15215 28 _ _ (385203 / 20000) (963009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231549184 :
    ThetaLowerSegment 231549184 231581952 (23152945051317 / 100000) (23156227004733 / 100000) := by
  exact
    packedTile16384 231549184 231581952 12 1704 15216 28 _ _ (1926029 / 100000) (120377 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231581952 :
    ThetaLowerSegment 231581952 231614720 (23156227004733 / 100000) (11579738119637 / 50000) := by
  exact
    packedTile16384 231581952 231614720 12 1687 15217 28 _ _ (1926043 / 100000) (963023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231614720 :
    ThetaLowerSegment 231614720 231647488 (11579738119637 / 50000) (11581452310367 / 50000) := by
  exact
    packedTile16384 231614720 231647488 12 1780 15218 28 _ _ (1926057 / 100000) (96303 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231647488 :
    ThetaLowerSegment 231647488 231680256 (11581452310367 / 50000) (1447881609421 / 6250) := by
  exact
    packedTile16384 231647488 231680256 12 1662 15219 28 _ _ (1926071 / 100000) (963037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231680256 :
    ThetaLowerSegment 231680256 231713024 (1447881609421 / 6250) (5792333467299 / 25000) := by
  exact
    packedTile16384 231680256 231713024 12 1676 15221 28 _ _ (385217 / 20000) (240761 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231713024 :
    ThetaLowerSegment 231713024 231745792 (5792333467299 / 25000) (5793163616399 / 25000) := by
  exact
    packedTile16384 231713024 231745792 12 1724 15222 28 _ _ (19261 / 1000) (1926103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231745792 :
    ThetaLowerSegment 231745792 231778560 (5793163616399 / 25000) (11587938427159 / 50000) := by
  exact
    packedTile16384 231745792 231778560 12 1673 15223 28 _ _ (963057 / 50000) (1926117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231778560 :
    ThetaLowerSegment 231778560 231811328 (11587938427159 / 50000) (11589558300807 / 50000) := by
  exact
    packedTile16384 231778560 231811328 12 1682 15224 28 _ _ (120383 / 6250) (1926131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231811328 :
    ThetaLowerSegment 231811328 231844096 (11589558300807 / 50000) (1448896912127 / 6250) := by
  exact
    packedTile16384 231811328 231844096 12 1679 15225 28 _ _ (963071 / 50000) (385229 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231844096 :
    ThetaLowerSegment 231844096 231876864 (1448896912127 / 6250) (2898211318567 / 12500) := by
  exact
    packedTile16384 231844096 231876864 12 1734 15226 28 _ _ (481539 / 25000) (1926159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231876864 :
    ThetaLowerSegment 231876864 231909632 (2898211318567 / 12500) (5797246074809 / 25000) := by
  exact
    packedTile16384 231876864 231909632 12 1710 15227 28 _ _ (192617 / 10000) (1926173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231909632 :
    ThetaLowerSegment 231909632 231942400 (5797246074809 / 25000) (5798075778567 / 25000) := by
  exact
    packedTile16384 231909632 231942400 12 1723 15228 28 _ _ (240773 / 12500) (1926187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231942400 :
    ThetaLowerSegment 231942400 231975168 (5798075778567 / 25000) (5798894412717 / 25000) := by
  exact
    packedTile16384 231942400 231975168 12 1700 15229 28 _ _ (963099 / 50000) (1926201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell231975168 :
    ThetaLowerSegment 231975168 232007936 (5798894412717 / 25000) (11599412622993 / 50000) := by
  exact
    packedTile16384 231975168 232007936 12 1686 15230 28 _ _ (1926213 / 100000) (240777 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232007936 :
    ThetaLowerSegment 232007936 232040704 (11599412622993 / 50000) (23202105610567 / 100000) := by
  exact
    packedTile16384 232007936 232040704 12 1703 15231 28 _ _ (1926227 / 100000) (192623 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232040704 :
    ThetaLowerSegment 232040704 232073472 (23202105610567 / 100000) (5801333979181 / 25000) := by
  exact
    packedTile16384 232040704 232073472 12 1677 15232 28 _ _ (1926241 / 100000) (481561 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232073472 :
    ThetaLowerSegment 232073472 232106240 (5801333979181 / 25000) (23208624034009 / 100000) := by
  exact
    packedTile16384 232073472 232106240 12 1707 15233 28 _ _ (385251 / 20000) (963129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232106240 :
    ThetaLowerSegment 232106240 232139008 (23208624034009 / 100000) (23211917953999 / 100000) := by
  exact
    packedTile16384 232106240 232139008 12 1710 15235 28 _ _ (1926269 / 100000) (60196 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232139008 :
    ThetaLowerSegment 232139008 232171776 (23211917953999 / 100000) (2901896912319 / 12500) := by
  exact
    packedTile16384 232139008 232171776 12 1691 15236 28 _ _ (1926283 / 100000) (963143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232171776 :
    ThetaLowerSegment 232171776 232204544 (2901896912319 / 12500) (23218444224561 / 100000) := by
  exact
    packedTile16384 232171776 232204544 12 1697 15237 28 _ _ (1926297 / 100000) (19263 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232204544 :
    ThetaLowerSegment 232204544 232237312 (23218444224561 / 100000) (5805445630381 / 25000) := by
  exact
    packedTile16384 232204544 232237312 12 1733 15238 28 _ _ (1926311 / 100000) (963157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232237312 :
    ThetaLowerSegment 232237312 232270080 (5805445630381 / 25000) (11612493000831 / 50000) := by
  exact
    packedTile16384 232237312 232270080 12 1663 15239 28 _ _ (963163 / 50000) (1926329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232270080 :
    ThetaLowerSegment 232270080 232302848 (11612493000831 / 50000) (11614105347411 / 50000) := by
  exact
    packedTile16384 232270080 232302848 12 1674 15240 28 _ _ (96317 / 5000) (1926343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232302848 :
    ThetaLowerSegment 232302848 232335616 (11614105347411 / 50000) (11615750453727 / 50000) := by
  exact
    packedTile16384 232302848 232335616 12 1708 15241 28 _ _ (963177 / 50000) (1926357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232335616 :
    ThetaLowerSegment 232335616 232368384 (11615750453727 / 50000) (11617377271503 / 50000) := by
  exact
    packedTile16384 232335616 232368384 12 1689 15242 28 _ _ (60199 / 3125) (1926371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232368384 :
    ThetaLowerSegment 232368384 232401152 (11617377271503 / 50000) (580951071927 / 2500) := by
  exact
    packedTile16384 232368384 232401152 12 1707 15243 28 _ _ (963191 / 50000) (385277 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232401152 :
    ThetaLowerSegment 232401152 232433920 (580951071927 / 2500) (1162063479519 / 5000) := by
  exact
    packedTile16384 232401152 232433920 12 1675 15244 28 _ _ (481599 / 25000) (1926399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232433920 :
    ThetaLowerSegment 232433920 232466688 (1162063479519 / 5000) (2324460805891 / 10000) := by
  exact
    packedTile16384 232433920 232466688 12 1733 15245 28 _ _ (192641 / 10000) (1926413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232466688 :
    ThetaLowerSegment 232466688 232499456 (2324460805891 / 10000) (2324781555487 / 10000) := by
  exact
    packedTile16384 232466688 232499456 12 1665 15246 28 _ _ (240803 / 12500) (1926427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232499456 :
    ThetaLowerSegment 232499456 232532224 (2324781555487 / 10000) (5812767327163 / 25000) := by
  exact
    packedTile16384 232499456 232532224 12 1689 15247 28 _ _ (963219 / 50000) (1926441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232532224 :
    ThetaLowerSegment 232532224 232564992 (5812767327163 / 25000) (5813599554427 / 25000) := by
  exact
    packedTile16384 232532224 232564992 12 1728 15249 28 _ _ (481613 / 25000) (385291 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232564992 :
    ThetaLowerSegment 232564992 232597760 (5813599554427 / 25000) (4651519615879 / 20000) := by
  exact
    packedTile16384 232564992 232597760 12 1661 15250 28 _ _ (1926467 / 100000) (192647 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232597760 :
    ThetaLowerSegment 232597760 232630528 (4651519615879 / 20000) (23260896214867 / 100000) := by
  exact
    packedTile16384 232597760 232630528 12 1712 15251 28 _ _ (1926481 / 100000) (481621 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232630528 :
    ThetaLowerSegment 232630528 232663296 (23260896214867 / 100000) (11632075032461 / 50000) := by
  exact
    packedTile16384 232630528 232663296 12 1689 15252 28 _ _ (385299 / 20000) (963249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232663296 :
    ThetaLowerSegment 232663296 232696064 (11632075032461 / 50000) (23267369261461 / 100000) := by
  exact
    packedTile16384 232663296 232696064 12 1671 15253 28 _ _ (1926509 / 100000) (120407 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232696064 :
    ThetaLowerSegment 232696064 232728832 (23267369261461 / 100000) (4654147364733 / 20000) := by
  exact
    packedTile16384 232696064 232728832 12 1748 15254 28 _ _ (1926523 / 100000) (963263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232728832 :
    ThetaLowerSegment 232728832 232761600 (4654147364733 / 20000) (23274019642713 / 100000) := by
  exact
    packedTile16384 232728832 232761600 12 1704 15255 28 _ _ (1926537 / 100000) (96327 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232761600 :
    ThetaLowerSegment 232761600 232794368 (23274019642713 / 100000) (4655467432707 / 20000) := by
  exact
    packedTile16384 232761600 232794368 12 1722 15256 28 _ _ (1926551 / 100000) (963277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232794368 :
    ThetaLowerSegment 232794368 232827136 (4655467432707 / 20000) (1164031097843 / 5000) := by
  exact
    packedTile16384 232794368 232827136 12 1705 15257 28 _ _ (385313 / 20000) (240821 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232827136 :
    ThetaLowerSegment 232827136 232859904 (1164031097843 / 5000) (23283879801949 / 100000) := by
  exact
    packedTile16384 232827136 232859904 12 1691 15258 28 _ _ (1926579 / 100000) (963291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232859904 :
    ThetaLowerSegment 232859904 232892672 (23283879801949 / 100000) (23287251339699 / 100000) := by
  exact
    packedTile16384 232859904 232892672 12 1750 15259 28 _ _ (1926593 / 100000) (481649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232892672 :
    ThetaLowerSegment 232892672 232925440 (23287251339699 / 100000) (11645260395889 / 50000) := by
  exact
    packedTile16384 232892672 232925440 12 1697 15260 28 _ _ (1926607 / 100000) (192661 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232925440 :
    ThetaLowerSegment 232925440 232958208 (11645260395889 / 50000) (23293855772729 / 100000) := by
  exact
    packedTile16384 232925440 232958208 12 1731 15261 28 _ _ (1926621 / 100000) (60207 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232958208 :
    ThetaLowerSegment 232958208 232990976 (23293855772729 / 100000) (5824281318081 / 25000) := by
  exact
    packedTile16384 232958208 232990976 12 1697 15262 28 _ _ (385327 / 20000) (963319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell232990976 :
    ThetaLowerSegment 232990976 233023744 (5824281318081 / 25000) (5825069317931 / 25000) := by
  exact
    packedTile16384 232990976 233023744 12 1636 15264 28 _ _ (38533 / 2000) (1926653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233023744 :
    ThetaLowerSegment 233023744 233056512 (5825069317931 / 25000) (5825872255153 / 25000) := by
  exact
    packedTile16384 233023744 233056512 12 1667 15265 28 _ _ (240833 / 12500) (1926667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233056512 :
    ThetaLowerSegment 233056512 233089280 (5825872255153 / 25000) (11653394710013 / 50000) := by
  exact
    packedTile16384 233056512 233089280 12 1713 15266 28 _ _ (963339 / 50000) (1926681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233089280 :
    ThetaLowerSegment 233089280 233122048 (11653394710013 / 50000) (11655012167947 / 50000) := by
  exact
    packedTile16384 233089280 233122048 12 1679 15267 28 _ _ (481673 / 25000) (385339 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233122048 :
    ThetaLowerSegment 233122048 233154816 (11655012167947 / 50000) (2331331129633 / 10000) := by
  exact
    packedTile16384 233122048 233154816 12 1706 15268 28 _ _ (963353 / 50000) (1926709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233154816 :
    ThetaLowerSegment 233154816 233187584 (2331331129633 / 10000) (2331656745313 / 10000) := by
  exact
    packedTile16384 233154816 233187584 12 1690 15269 28 _ _ (12042 / 625) (1926723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233187584 :
    ThetaLowerSegment 233187584 233220352 (2331656745313 / 10000) (5829954463347 / 25000) := by
  exact
    packedTile16384 233187584 233220352 12 1687 15270 28 _ _ (963367 / 50000) (1926737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233220352 :
    ThetaLowerSegment 233220352 233253120 (5829954463347 / 25000) (5830772367873 / 25000) := by
  exact
    packedTile16384 233220352 233253120 12 1698 15271 28 _ _ (481687 / 25000) (1926751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233253120 :
    ThetaLowerSegment 233253120 233285888 (5830772367873 / 25000) (11663168032731 / 50000) := by
  exact
    packedTile16384 233253120 233285888 12 1685 15272 28 _ _ (963381 / 50000) (385353 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233285888 :
    ThetaLowerSegment 233285888 233318656 (11663168032731 / 50000) (466590805879 / 2000) := by
  exact
    packedTile16384 233285888 233318656 12 1663 15273 28 _ _ (240847 / 12500) (1926779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233318656 :
    ThetaLowerSegment 233318656 233351424 (466590805879 / 2000) (1166641658903 / 5000) := by
  exact
    packedTile16384 233318656 233351424 12 1709 15274 28 _ _ (192679 / 10000) (1926793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233351424 :
    ThetaLowerSegment 233351424 233384192 (1166641658903 / 5000) (1458504026773 / 6250) := by
  exact
    packedTile16384 233351424 233384192 12 1677 15275 28 _ _ (481701 / 25000) (1926807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233384192 :
    ThetaLowerSegment 233384192 233416960 (1458504026773 / 6250) (2333931882397 / 10000) := by
  exact
    packedTile16384 233384192 233416960 12 1689 15276 28 _ _ (963409 / 50000) (1926821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233416960 :
    ThetaLowerSegment 233416960 233449728 (2333931882397 / 10000) (11671290475273 / 50000) := by
  exact
    packedTile16384 233416960 233449728 12 1693 15277 28 _ _ (120427 / 6250) (385367 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233449728 :
    ThetaLowerSegment 233449728 233482496 (11671290475273 / 50000) (2918230387603 / 12500) := by
  exact
    packedTile16384 233449728 233482496 12 1693 15279 28 _ _ (963423 / 50000) (1926849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233482496 :
    ThetaLowerSegment 233482496 233515264 (2918230387603 / 12500) (5837279208991 / 25000) := by
  exact
    packedTile16384 233482496 233515264 12 1699 15280 28 _ _ (96343 / 5000) (1926863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233515264 :
    ThetaLowerSegment 233515264 233548032 (5837279208991 / 25000) (5838103911063 / 25000) := by
  exact
    packedTile16384 233515264 233548032 12 1712 15281 28 _ _ (963437 / 50000) (1926877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233548032 :
    ThetaLowerSegment 233548032 233580800 (5838103911063 / 25000) (5838941625621 / 25000) := by
  exact
    packedTile16384 233548032 233580800 12 1739 15282 28 _ _ (240861 / 12500) (1926891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233580800 :
    ThetaLowerSegment 233580800 233613568 (5838941625621 / 25000) (1459942789233 / 6250) := by
  exact
    packedTile16384 233580800 233613568 12 1722 15283 28 _ _ (963451 / 50000) (385381 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233613568 :
    ThetaLowerSegment 233613568 233646336 (1459942789233 / 6250) (2920294566387 / 12500) := by
  exact
    packedTile16384 233613568 233646336 12 1698 15284 28 _ _ (481729 / 25000) (1926919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233646336 :
    ThetaLowerSegment 233646336 233679104 (2920294566387 / 12500) (11682792069423 / 50000) := by
  exact
    packedTile16384 233646336 233679104 12 1675 15285 28 _ _ (192693 / 10000) (1926933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233679104 :
    ThetaLowerSegment 233679104 233711872 (11682792069423 / 50000) (2336878479283 / 10000) := by
  exact
    packedTile16384 233679104 233711872 12 1661 15286 28 _ _ (60217 / 3125) (1926947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233711872 :
    ThetaLowerSegment 233711872 233744640 (2336878479283 / 10000) (2921505409851 / 12500) := by
  exact
    packedTile16384 233711872 233744640 12 1691 15287 28 _ _ (963479 / 50000) (1926961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233744640 :
    ThetaLowerSegment 233744640 233777408 (2921505409851 / 12500) (5843834118489 / 25000) := by
  exact
    packedTile16384 233744640 233777408 12 1709 15288 28 _ _ (481743 / 25000) (77079 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233777408 :
    ThetaLowerSegment 233777408 233810176 (5843834118489 / 25000) (2337851407387 / 10000) := by
  exact
    packedTile16384 233777408 233810176 12 1649 15289 28 _ _ (963493 / 50000) (1926989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233810176 :
    ThetaLowerSegment 233810176 233842944 (2337851407387 / 10000) (23381745654547 / 100000) := by
  exact
    packedTile16384 233810176 233842944 12 1677 15290 28 _ _ (1927001 / 100000) (481751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233842944 :
    ThetaLowerSegment 233842944 233875712 (23381745654547 / 100000) (23385006163927 / 100000) := by
  exact
    packedTile16384 233842944 233875712 12 1692 15291 28 _ _ (385403 / 20000) (963509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233875712 :
    ThetaLowerSegment 233875712 233908480 (23385006163927 / 100000) (23388158783371 / 100000) := by
  exact
    packedTile16384 233875712 233908480 12 1636 15292 28 _ _ (1927029 / 100000) (240879 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233908480 :
    ThetaLowerSegment 233908480 233941248 (23388158783371 / 100000) (23391484859589 / 100000) := by
  exact
    packedTile16384 233908480 233941248 12 1726 15294 28 _ _ (1927043 / 100000) (963523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233941248 :
    ThetaLowerSegment 233941248 233974016 (23391484859589 / 100000) (11697365975317 / 50000) := by
  exact
    packedTile16384 233941248 233974016 12 1685 15295 28 _ _ (1927057 / 100000) (96353 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell233974016 :
    ThetaLowerSegment 233974016 234006784 (11697365975317 / 50000) (935921937593 / 4000) := by
  exact
    packedTile16384 233974016 234006784 12 1721 15296 28 _ _ (1927071 / 100000) (963537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234006784 :
    ThetaLowerSegment 234006784 234010880 (935921937593 / 4000) (1169923908989 / 5000) := by
  exact
    packedTile16384 234006784 234010880 9 223 15297 28 _ _ (385417 / 20000) (120443 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234010880 :
    ThetaLowerSegment 234010880 234012928 (1169923908989 / 5000) (5849673503353 / 25000) := by
  exact
    packedTile16384 234010880 234012928 8 112 15297 28 _ _ (963543 / 50000) (1927089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_204712192_234012928 :
    ThetaLowerSegment 204712192 234012928 (20469224769031 / 100000) (5849673503353 / 25000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell204712192 cell204744960)
                      (ThetaLowerSegment.join cell204777728 cell204810496))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell204843264 cell204876032)
                      (ThetaLowerSegment.join cell204908800 cell204941568)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell204974336 cell205007104)
                      (ThetaLowerSegment.join cell205039872 cell205072640))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell205105408 cell205138176)
                      (ThetaLowerSegment.join cell205170944 cell205203712))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell205236480 cell205269248)
                      (ThetaLowerSegment.join cell205302016 cell205334784))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell205367552 cell205400320)
                      (ThetaLowerSegment.join cell205433088 cell205465856)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell205498624 cell205531392)
                      (ThetaLowerSegment.join cell205564160 cell205596928))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell205629696 cell205662464)
                      (ThetaLowerSegment.join cell205695232 cell205728000)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell205760768 cell205793536)
                      (ThetaLowerSegment.join cell205826304 cell205859072))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell205891840 cell205924608)
                      (ThetaLowerSegment.join cell205957376 cell205990144)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell206022912 cell206055680)
                      (ThetaLowerSegment.join cell206088448 cell206121216))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell206153984 cell206186752)
                      (ThetaLowerSegment.join cell206219520 cell206252288))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell206285056 cell206317824)
                      (ThetaLowerSegment.join cell206350592 cell206383360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell206416128 cell206448896)
                      (ThetaLowerSegment.join cell206481664 cell206514432)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell206547200 cell206579968)
                      (ThetaLowerSegment.join cell206612736 cell206645504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell206678272 cell206711040)
                      (ThetaLowerSegment.join cell206743808 cell206776576))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell206809344 cell206842112)
                      (ThetaLowerSegment.join cell206874880 cell206907648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell206940416 cell206973184)
                      (ThetaLowerSegment.join cell207005952 cell207038720)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell207071488 cell207104256)
                      (ThetaLowerSegment.join cell207137024 cell207169792))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell207202560 cell207235328)
                      (ThetaLowerSegment.join cell207268096 cell207300864))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell207333632 cell207366400)
                      (ThetaLowerSegment.join cell207399168 cell207431936))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell207464704 cell207497472)
                      (ThetaLowerSegment.join cell207530240 cell207563008)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell207595776 cell207628544)
                      (ThetaLowerSegment.join cell207661312 cell207694080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell207726848 cell207759616)
                      (ThetaLowerSegment.join cell207792384 cell207825152)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell207857920 cell207890688)
                      (ThetaLowerSegment.join cell207923456 cell207956224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell207988992 cell208021760)
                      (ThetaLowerSegment.join cell208054528 cell208087296)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell208120064 cell208152832)
                      (ThetaLowerSegment.join cell208185600 cell208218368))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell208251136 cell208283904)
                      (ThetaLowerSegment.join cell208316672 cell208349440))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell208382208 cell208414976)
                      (ThetaLowerSegment.join cell208447744 cell208480512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell208513280 cell208546048)
                      (ThetaLowerSegment.join cell208578816 cell208611584)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell208644352 cell208677120)
                      (ThetaLowerSegment.join cell208709888 cell208742656))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell208775424 cell208808192)
                      (ThetaLowerSegment.join cell208840960 cell208873728)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell208906496 cell208939264)
                      (ThetaLowerSegment.join cell208972032 cell209004800))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell209037568 cell209070336)
                      (ThetaLowerSegment.join cell209103104 cell209135872)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell209168640 cell209201408)
                      (ThetaLowerSegment.join cell209234176 cell209266944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell209299712 cell209332480)
                      (ThetaLowerSegment.join cell209365248 cell209398016))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell209430784 cell209463552)
                      (ThetaLowerSegment.join cell209496320 cell209529088))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell209561856 cell209594624)
                      (ThetaLowerSegment.join cell209627392 cell209660160)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell209692928 cell209725696)
                      (ThetaLowerSegment.join cell209758464 cell209791232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell209824000 cell209856768)
                      (ThetaLowerSegment.join cell209889536 cell209922304)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell209955072 cell209987840)
                      (ThetaLowerSegment.join cell210020608 cell210053376))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell210086144 cell210118912)
                      (ThetaLowerSegment.join cell210151680 cell210184448)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell210217216 cell210249984)
                      (ThetaLowerSegment.join cell210282752 cell210315520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell210348288 cell210381056)
                      (ThetaLowerSegment.join cell210413824 cell210446592))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell210479360 cell210512128)
                      (ThetaLowerSegment.join cell210544896 cell210577664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell210610432 cell210643200)
                      (ThetaLowerSegment.join cell210675968 cell210708736)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell210741504 cell210774272)
                      (ThetaLowerSegment.join cell210807040 cell210839808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell210872576 cell210905344)
                      (ThetaLowerSegment.join cell210938112 cell210970880))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell211003648 cell211036416)
                      (ThetaLowerSegment.join cell211069184 cell211101952))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell211134720 cell211167488)
                      (ThetaLowerSegment.join cell211200256 cell211233024)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell211265792 cell211298560)
                      (ThetaLowerSegment.join cell211331328 cell211364096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell211396864 cell211429632)
                      (ThetaLowerSegment.join cell211462400 cell211495168))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell211527936 cell211560704)
                      (ThetaLowerSegment.join cell211593472 cell211626240))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell211659008 cell211691776)
                      (ThetaLowerSegment.join cell211724544 cell211757312)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell211790080 cell211822848)
                      (ThetaLowerSegment.join cell211855616 cell211888384))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell211921152 cell211953920)
                      (ThetaLowerSegment.join cell211986688 cell212019456)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell212052224 cell212084992)
                      (ThetaLowerSegment.join cell212117760 cell212150528))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell212183296 cell212216064)
                      (ThetaLowerSegment.join cell212248832 cell212281600)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell212314368 cell212347136)
                      (ThetaLowerSegment.join cell212379904 cell212412672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell212445440 cell212478208)
                      (ThetaLowerSegment.join cell212510976 cell212543744))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell212576512 cell212609280)
                      (ThetaLowerSegment.join cell212642048 cell212674816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell212707584 cell212740352)
                      (ThetaLowerSegment.join cell212773120 cell212805888)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell212838656 cell212871424)
                      (ThetaLowerSegment.join cell212904192 cell212936960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell212969728 cell213002496)
                      (ThetaLowerSegment.join cell213035264 cell213068032))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell213100800 cell213133568)
                      (ThetaLowerSegment.join cell213166336 cell213199104))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell213231872 cell213264640)
                      (ThetaLowerSegment.join cell213297408 cell213330176)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell213362944 cell213395712)
                      (ThetaLowerSegment.join cell213428480 cell213461248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell213494016 cell213526784)
                      (ThetaLowerSegment.join cell213559552 cell213592320))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell213625088 cell213657856)
                      (ThetaLowerSegment.join cell213690624 cell213723392))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell213756160 cell213788928)
                      (ThetaLowerSegment.join cell213821696 cell213854464)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell213887232 cell213920000)
                      (ThetaLowerSegment.join cell213952768 cell213985536))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell214018304 cell214051072)
                      (ThetaLowerSegment.join cell214083840 cell214116608)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell214149376 cell214182144)
                      (ThetaLowerSegment.join cell214214912 cell214247680))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell214280448 cell214313216)
                      (ThetaLowerSegment.join cell214345984 cell214378752)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell214411520 cell214444288)
                      (ThetaLowerSegment.join cell214477056 cell214509824))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell214542592 cell214575360)
                      (ThetaLowerSegment.join cell214608128 cell214640896))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell214673664 cell214706432)
                      (ThetaLowerSegment.join cell214739200 cell214771968))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell214804736 cell214837504)
                      (ThetaLowerSegment.join cell214870272 cell214903040)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell214935808 cell214968576)
                      (ThetaLowerSegment.join cell215001344 cell215034112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell215066880 cell215099648)
                      (ThetaLowerSegment.join cell215132416 cell215165184))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell215197952 cell215230720)
                      (ThetaLowerSegment.join cell215263488 cell215296256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell215329024 cell215361792)
                      (ThetaLowerSegment.join cell215394560 cell215427328)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell215460096 cell215492864)
                      (ThetaLowerSegment.join cell215525632 cell215558400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell215591168 cell215623936)
                      (ThetaLowerSegment.join cell215656704 cell215689472))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell215722240 cell215755008)
                      (ThetaLowerSegment.join cell215787776 cell215820544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell215853312 cell215886080)
                      (ThetaLowerSegment.join cell215918848 cell215951616)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell215984384 cell216017152)
                      (ThetaLowerSegment.join cell216049920 cell216082688))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell216115456 cell216148224)
                      (ThetaLowerSegment.join cell216180992 cell216213760)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell216246528 cell216279296)
                      (ThetaLowerSegment.join cell216312064 cell216344832))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell216377600 cell216410368)
                      (ThetaLowerSegment.join cell216443136 cell216475904)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell216508672 cell216541440)
                      (ThetaLowerSegment.join cell216574208 cell216606976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell216639744 cell216672512)
                      (ThetaLowerSegment.join cell216705280 cell216738048))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell216770816 cell216803584)
                      (ThetaLowerSegment.join cell216836352 cell216869120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell216901888 cell216934656)
                      (ThetaLowerSegment.join cell216967424 cell217000192)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell217032960 cell217065728)
                      (ThetaLowerSegment.join cell217098496 cell217131264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell217164032 cell217196800)
                      (ThetaLowerSegment.join cell217229568 cell217262336)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell217295104 cell217327872)
                      (ThetaLowerSegment.join cell217360640 cell217393408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell217426176 cell217458944)
                      (ThetaLowerSegment.join cell217491712 cell217524480)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell217557248 cell217590016)
                      (ThetaLowerSegment.join cell217622784 cell217655552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell217688320 cell217721088)
                      (ThetaLowerSegment.join cell217753856 cell217786624))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell217819392 cell217852160)
                      (ThetaLowerSegment.join cell217884928 cell217917696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell217950464 cell217983232)
                      (ThetaLowerSegment.join cell218016000 cell218048768)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell218081536 cell218114304)
                      (ThetaLowerSegment.join cell218147072 cell218179840))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell218212608 cell218245376)
                      (ThetaLowerSegment.join cell218278144 cell218310912)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell218343680 cell218376448)
                      (ThetaLowerSegment.join cell218409216 cell218441984))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell218474752 cell218507520)
                      (ThetaLowerSegment.join cell218540288 cell218573056)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell218605824 cell218638592)
                      (ThetaLowerSegment.join cell218671360 cell218704128))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell218736896 cell218769664)
                      (ThetaLowerSegment.join cell218802432 cell218835200))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell218867968 cell218900736)
                      (ThetaLowerSegment.join cell218933504 cell218966272))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell218999040 cell219031808)
                      (ThetaLowerSegment.join cell219064576 cell219097344)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell219130112 cell219162880)
                      (ThetaLowerSegment.join cell219195648 cell219228416))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell219261184 cell219293952)
                      (ThetaLowerSegment.join cell219326720 cell219359488))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell219392256 cell219425024)
                      (ThetaLowerSegment.join cell219457792 cell219490560))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell219523328 cell219556096)
                      (ThetaLowerSegment.join cell219588864 cell219621632)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell219654400 cell219687168)
                      (ThetaLowerSegment.join cell219719936 cell219752704))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell219785472 cell219818240)
                      (ThetaLowerSegment.join cell219851008 cell219883776))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell219916544 cell219949312)
                      (ThetaLowerSegment.join cell219982080 cell220014848))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell220047616 cell220080384)
                      (ThetaLowerSegment.join cell220113152 cell220145920)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell220178688 cell220211456)
                      (ThetaLowerSegment.join cell220244224 cell220276992))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell220309760 cell220342528)
                      (ThetaLowerSegment.join cell220375296 cell220408064)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell220440832 cell220473600)
                      (ThetaLowerSegment.join cell220506368 cell220539136))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell220571904 cell220604672)
                      (ThetaLowerSegment.join cell220637440 cell220670208)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell220702976 cell220735744)
                      (ThetaLowerSegment.join cell220768512 cell220801280))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell220834048 cell220866816)
                      (ThetaLowerSegment.join cell220899584 cell220932352))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell220965120 cell220997888)
                      (ThetaLowerSegment.join cell221030656 cell221063424))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell221096192 cell221128960)
                      (ThetaLowerSegment.join cell221161728 cell221194496)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell221227264 cell221260032)
                      (ThetaLowerSegment.join cell221292800 cell221325568))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell221358336 cell221391104)
                      (ThetaLowerSegment.join cell221423872 cell221456640)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell221489408 cell221522176)
                      (ThetaLowerSegment.join cell221554944 cell221587712))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell221620480 cell221653248)
                      (ThetaLowerSegment.join cell221686016 cell221718784)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell221751552 cell221784320)
                      (ThetaLowerSegment.join cell221817088 cell221849856))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell221882624 cell221915392)
                      (ThetaLowerSegment.join cell221948160 cell221980928))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell222013696 cell222046464)
                      (ThetaLowerSegment.join cell222079232 cell222112000))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell222144768 cell222177536)
                      (ThetaLowerSegment.join cell222210304 cell222243072)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell222275840 cell222308608)
                      (ThetaLowerSegment.join cell222341376 cell222374144))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell222406912 cell222439680)
                      (ThetaLowerSegment.join cell222472448 cell222505216)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell222537984 cell222570752)
                      (ThetaLowerSegment.join cell222603520 cell222636288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell222669056 cell222701824)
                      (ThetaLowerSegment.join cell222734592 cell222767360)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell222800128 cell222832896)
                      (ThetaLowerSegment.join cell222865664 cell222898432))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell222931200 cell222963968)
                      (ThetaLowerSegment.join cell222996736 cell223029504))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell223062272 cell223095040)
                      (ThetaLowerSegment.join cell223127808 cell223160576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell223193344 cell223226112)
                      (ThetaLowerSegment.join cell223258880 cell223291648)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell223324416 cell223357184)
                      (ThetaLowerSegment.join cell223389952 cell223422720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell223455488 cell223488256)
                      (ThetaLowerSegment.join cell223521024 cell223553792))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell223586560 cell223619328)
                      (ThetaLowerSegment.join cell223652096 cell223684864))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell223717632 cell223750400)
                      (ThetaLowerSegment.join cell223783168 cell223815936)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell223848704 cell223881472)
                      (ThetaLowerSegment.join cell223914240 cell223947008))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell223979776 cell224012544)
                      (ThetaLowerSegment.join cell224045312 cell224078080))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell224110848 cell224143616)
                      (ThetaLowerSegment.join cell224176384 cell224209152))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell224241920 cell224274688)
                      (ThetaLowerSegment.join cell224307456 cell224340224)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell224372992 cell224405760)
                      (ThetaLowerSegment.join cell224438528 cell224471296))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell224504064 cell224536832)
                      (ThetaLowerSegment.join cell224569600 cell224602368)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell224635136 cell224667904)
                      (ThetaLowerSegment.join cell224700672 cell224733440))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell224766208 cell224798976)
                      (ThetaLowerSegment.join cell224831744 cell224864512)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell224897280 cell224930048)
                      (ThetaLowerSegment.join cell224962816 cell224995584))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell225028352 cell225061120)
                      (ThetaLowerSegment.join cell225093888 cell225126656))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell225159424 cell225192192)
                      (ThetaLowerSegment.join cell225224960 cell225257728))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell225290496 cell225323264)
                      (ThetaLowerSegment.join cell225356032 cell225388800)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell225421568 cell225454336)
                      (ThetaLowerSegment.join cell225487104 cell225519872))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell225552640 cell225585408)
                      (ThetaLowerSegment.join cell225618176 cell225650944)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell225683712 cell225716480)
                      (ThetaLowerSegment.join cell225749248 cell225782016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell225814784 cell225847552)
                      (ThetaLowerSegment.join cell225880320 cell225913088)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell225945856 cell225978624)
                      (ThetaLowerSegment.join cell226011392 cell226044160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell226076928 cell226109696)
                      (ThetaLowerSegment.join cell226142464 cell226175232))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell226208000 cell226240768)
                      (ThetaLowerSegment.join cell226273536 cell226306304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell226339072 cell226371840)
                      (ThetaLowerSegment.join cell226404608 cell226437376)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell226470144 cell226502912)
                      (ThetaLowerSegment.join cell226535680 cell226568448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell226601216 cell226633984)
                      (ThetaLowerSegment.join cell226666752 cell226699520)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell226732288 cell226765056)
                      (ThetaLowerSegment.join cell226797824 cell226830592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell226863360 cell226896128)
                      (ThetaLowerSegment.join cell226928896 cell226961664)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell226994432 cell227027200)
                      (ThetaLowerSegment.join cell227059968 cell227092736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell227125504 cell227158272)
                      (ThetaLowerSegment.join cell227191040 cell227223808))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell227256576 cell227289344)
                      (ThetaLowerSegment.join cell227322112 cell227354880))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell227387648 cell227420416)
                      (ThetaLowerSegment.join cell227453184 cell227485952)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell227518720 cell227551488)
                      (ThetaLowerSegment.join cell227584256 cell227617024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell227649792 cell227682560)
                      (ThetaLowerSegment.join cell227715328 cell227748096))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell227780864 cell227813632)
                      (ThetaLowerSegment.join cell227846400 cell227879168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell227911936 cell227944704)
                      (ThetaLowerSegment.join cell227977472 cell228010240)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell228043008 cell228075776)
                      (ThetaLowerSegment.join cell228108544 cell228141312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell228174080 cell228206848)
                      (ThetaLowerSegment.join cell228239616 cell228272384))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell228305152 cell228337920)
                      (ThetaLowerSegment.join cell228370688 cell228403456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell228436224 cell228468992)
                      (ThetaLowerSegment.join cell228501760 cell228534528)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell228567296 cell228600064)
                      (ThetaLowerSegment.join cell228632832 cell228665600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell228698368 cell228731136)
                      (ThetaLowerSegment.join cell228763904 cell228796672)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell228829440 cell228862208)
                      (ThetaLowerSegment.join cell228894976 cell228927744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell228960512 cell228993280)
                      (ThetaLowerSegment.join cell229026048 cell229058816)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell229091584 cell229124352)
                      (ThetaLowerSegment.join cell229157120 cell229189888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell229222656 cell229255424)
                      (ThetaLowerSegment.join cell229288192 cell229320960))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell229353728 cell229386496)
                      (ThetaLowerSegment.join cell229419264 cell229452032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell229484800 cell229517568)
                      (ThetaLowerSegment.join cell229550336 cell229583104)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell229615872 cell229648640)
                      (ThetaLowerSegment.join cell229681408 cell229714176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell229746944 cell229779712)
                      (ThetaLowerSegment.join cell229812480 cell229845248))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell229878016 cell229910784)
                    (ThetaLowerSegment.join cell229943552 cell229976320))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell230009088 cell230041856)
                    (ThetaLowerSegment.join cell230074624 cell230107392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell230140160 cell230172928)
                    (ThetaLowerSegment.join cell230205696 cell230238464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell230271232 cell230304000)
                    (ThetaLowerSegment.join cell230336768 cell230369536))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell230402304 cell230435072)
                    (ThetaLowerSegment.join cell230467840 cell230500608))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell230533376 cell230566144)
                    (ThetaLowerSegment.join cell230598912 cell230631680)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell230664448 cell230697216)
                    (ThetaLowerSegment.join cell230729984 cell230762752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell230795520 cell230828288)
                    (ThetaLowerSegment.join cell230861056 cell230893824)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell230926592 cell230959360)
                    (ThetaLowerSegment.join cell230992128 cell231024896))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell231057664 cell231090432)
                    (ThetaLowerSegment.join cell231123200 cell231155968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell231188736 cell231221504)
                    (ThetaLowerSegment.join cell231254272 cell231287040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell231319808 cell231352576)
                    (ThetaLowerSegment.join cell231385344 cell231418112))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell231450880 cell231483648)
                    (ThetaLowerSegment.join cell231516416 cell231549184))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell231581952 cell231614720)
                    (ThetaLowerSegment.join cell231647488 cell231680256)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell231713024 cell231745792)
                    (ThetaLowerSegment.join cell231778560 cell231811328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell231844096 cell231876864)
                    (ThetaLowerSegment.join cell231909632 cell231942400))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell231975168 cell232007936)
                    (ThetaLowerSegment.join cell232040704 cell232073472))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell232106240 cell232139008)
                    (ThetaLowerSegment.join cell232171776 cell232204544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell232237312 cell232270080)
                    (ThetaLowerSegment.join cell232302848 cell232335616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell232368384 cell232401152)
                    (ThetaLowerSegment.join cell232433920 cell232466688))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell232499456 cell232532224)
                    (ThetaLowerSegment.join cell232564992 cell232597760))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell232630528 cell232663296)
                    (ThetaLowerSegment.join cell232696064 cell232728832)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell232761600 cell232794368)
                    (ThetaLowerSegment.join cell232827136 cell232859904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell232892672 cell232925440)
                    (ThetaLowerSegment.join cell232958208 cell232990976)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell233023744 cell233056512)
                    (ThetaLowerSegment.join cell233089280 cell233122048))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell233154816 cell233187584)
                    (ThetaLowerSegment.join cell233220352 cell233253120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell233285888 cell233318656)
                    (ThetaLowerSegment.join cell233351424 cell233384192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell233416960 cell233449728)
                    (ThetaLowerSegment.join cell233482496 cell233515264))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell233548032 cell233580800)
                    (ThetaLowerSegment.join cell233613568 cell233646336))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell233679104 cell233711872)
                    (ThetaLowerSegment.join cell233744640 cell233777408)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell233810176 cell233842944)
                    (ThetaLowerSegment.join cell233875712 cell233908480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell233941248 cell233974016)
                    (ThetaLowerSegment.join cell234006784 cell234010880)))))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
