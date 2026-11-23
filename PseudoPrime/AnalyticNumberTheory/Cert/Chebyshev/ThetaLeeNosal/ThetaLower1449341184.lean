/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1449341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1417341184 :
    ThetaLowerSegment 1417341184 1417406720 (141728394035641 / 100000)
      (141734934793753 / 100000) := by
  exact
    packedTile65536 1417341184 1417406720 13 3104 37647 30 _ _ (2107203 / 100000) (1053603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1417406720 :
    ThetaLowerSegment 1417406720 1417472256 (141734934793753 / 100000)
      (141741540890833 / 100000) := by
  exact
    packedTile65536 1417406720 1417472256 13 3135 37648 30 _ _ (263401 / 12500) (2107211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1417472256 :
    ThetaLowerSegment 1417472256 1417603328 (141741540890833 / 100000)
      (141754710972083 / 100000) := by
  exact
    packedTile65536 1417472256 1417603328 14 6250 37649 30 _ _ (2107213 / 100000) (131701 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1417603328 :
    ThetaLowerSegment 1417603328 1417734400 (141754710972083 / 100000)
      (28353566107251 / 20000) := by
  exact
    packedTile65536 1417603328 1417734400 14 6226 37651 30 _ _ (1053611 / 50000) (84289 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1417734400 :
    ThetaLowerSegment 1417734400 1417865472 (28353566107251 / 20000)
      (141780929084151 / 100000) := by
  exact
    packedTile65536 1417734400 1417865472 14 6216 37652 30 _ _ (2107231 / 100000) (1053617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1417865472 :
    ThetaLowerSegment 1417865472 1417996544 (141780929084151 / 100000)
      (141794307950911 / 100000) := by
  exact
    packedTile65536 1417865472 1417996544 14 6349 37654 30 _ _ (52681 / 2500) (2107243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1417996544 :
    ThetaLowerSegment 1417996544 1418127616 (141794307950911 / 100000)
      (141807440332911 / 100000) := by
  exact
    packedTile65536 1417996544 1418127616 14 6232 37656 30 _ _ (8429 / 400) (2107253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1418127616 :
    ThetaLowerSegment 1418127616 1418258688 (141807440332911 / 100000)
      (141820458979013 / 100000) := by
  exact
    packedTile65536 1418127616 1418258688 14 6178 37658 30 _ _ (2107259 / 100000) (1053631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1418258688 :
    ThetaLowerSegment 1418258688 1418389760 (141820458979013 / 100000) (1134669608409 / 800) := by
  exact
    packedTile65536 1418258688 1418389760 14 6284 37659 30 _ _ (526817 / 25000) (2107271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1418389760 :
    ThetaLowerSegment 1418389760 1418520832 (1134669608409 / 800) (70923422068887 / 50000) := by
  exact
    packedTile65536 1418389760 1418520832 14 6237 37661 30 _ _ (2107277 / 100000) (26341 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1418520832 :
    ThetaLowerSegment 1418520832 1418651904 (70923422068887 / 50000)
      (141860080007421 / 100000) := by
  exact
    packedTile65536 1418520832 1418651904 14 6281 37663 30 _ _ (2107287 / 100000) (210729 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1418651904 :
    ThetaLowerSegment 1418651904 1418782976 (141860080007421 / 100000)
      (141873075701853 / 100000) := by
  exact
    packedTile65536 1418651904 1418782976 14 6167 37664 30 _ _ (65853 / 3125) (2107299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1418782976 :
    ThetaLowerSegment 1418782976 1418914048 (141873075701853 / 100000)
      (70943054691639 / 50000) := by
  exact
    packedTile65536 1418782976 1418914048 14 6185 37666 30 _ _ (421461 / 20000) (526827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1418914048 :
    ThetaLowerSegment 1418914048 1419045120 (70943054691639 / 50000) (70949667442971 / 50000) := by
  exact
    packedTile65536 1418914048 1419045120 14 6276 37668 30 _ _ (1053657 / 50000) (2107317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1419045120 :
    ThetaLowerSegment 1419045120 1419176192 (70949667442971 / 50000) (70956245454837 / 50000) := by
  exact
    packedTile65536 1419045120 1419176192 14 6243 37670 30 _ _ (526831 / 25000) (2107327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1419176192 :
    ThetaLowerSegment 1419176192 1419307264 (70956245454837 / 50000) (70962828763129 / 50000) := by
  exact
    packedTile65536 1419176192 1419307264 14 6248 37671 30 _ _ (2107333 / 100000) (263417 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1419307264 :
    ThetaLowerSegment 1419307264 1419438336 (70962828763129 / 50000) (4435583580556 / 3125) := by
  exact
    packedTile65536 1419307264 1419438336 14 6177 37673 30 _ _ (1053671 / 50000) (421469 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1419438336 :
    ThetaLowerSegment 1419438336 1419569408 (4435583580556 / 3125) (1135615320513 / 800) := by
  exact
    packedTile65536 1419438336 1419569408 14 6283 37675 30 _ _ (2107351 / 100000) (1053677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1419569408 :
    ThetaLowerSegment 1419569408 1419700480 (1135615320513 / 800) (28393010469273 / 20000) := by
  exact
    packedTile65536 1419569408 1419700480 14 6234 37677 30 _ _ (13171 / 625) (2107363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1419700480 :
    ThetaLowerSegment 1419700480 1419831552 (28393010469273 / 20000) (28395637938189 / 20000) := by
  exact
    packedTile65536 1419700480 1419831552 14 6234 37678 30 _ _ (210737 / 10000) (2107373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1419831552 :
    ThetaLowerSegment 1419831552 1419962624 (28395637938189 / 20000) (70995639310957 / 50000) := by
  exact
    packedTile65536 1419831552 1419962624 14 6211 37680 30 _ _ (2107379 / 100000) (1053691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1419962624 :
    ThetaLowerSegment 1419962624 1420093696 (70995639310957 / 50000) (71002178535921 / 50000) := by
  exact
    packedTile65536 1419962624 1420093696 14 6206 37682 30 _ _ (526847 / 25000) (2107391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1420093696 :
    ThetaLowerSegment 1420093696 1420224768 (71002178535921 / 50000) (28403463091199 / 20000) := by
  exact
    packedTile65536 1420093696 1420224768 14 6149 37684 30 _ _ (2107397 / 100000) (10537 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1420224768 :
    ThetaLowerSegment 1420224768 1420355840 (28403463091199 / 20000)
      (142030448816419 / 100000) := by
  exact
    packedTile65536 1420224768 1420355840 14 6232 37685 30 _ _ (2107407 / 100000) (210741 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1420355840 :
    ThetaLowerSegment 1420355840 1420486912 (142030448816419 / 100000)
      (142043531654947 / 100000) := by
  exact
    packedTile65536 1420355840 1420486912 14 6208 37687 30 _ _ (263427 / 12500) (2107419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1420486912 :
    ThetaLowerSegment 1420486912 1420617984 (142043531654947 / 100000)
      (142056736779997 / 100000) := by
  exact
    packedTile65536 1420486912 1420617984 14 6266 37689 30 _ _ (84297 / 4000) (526857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1420617984 :
    ThetaLowerSegment 1420617984 1420749056 (142056736779997 / 100000)
      (142069916672233 / 100000) := by
  exact
    packedTile65536 1420617984 1420749056 14 6254 37691 30 _ _ (1053717 / 50000) (2107437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1420749056 :
    ThetaLowerSegment 1420749056 1420880128 (142069916672233 / 100000)
      (28416621011357 / 20000) := by
  exact
    packedTile65536 1420749056 1420880128 14 6258 37692 30 _ _ (526861 / 25000) (2107447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1420880128 :
    ThetaLowerSegment 1420880128 1421011200 (28416621011357 / 20000) (14209635039889 / 10000) := by
  exact
    packedTile65536 1420880128 1421011200 14 6285 37694 30 _ _ (2107453 / 100000) (65858 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1421011200 :
    ThetaLowerSegment 1421011200 1421142272 (14209635039889 / 10000) (14210933236481 / 10000) := by
  exact
    packedTile65536 1421011200 1421142272 14 6160 37696 30 _ _ (1053731 / 50000) (421493 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1421142272 :
    ThetaLowerSegment 1421142272 1421273344 (14210933236481 / 10000) (5684897211883 / 4000) := by
  exact
    packedTile65536 1421142272 1421273344 14 6215 37698 30 _ _ (2107471 / 100000) (1053737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1421273344 :
    ThetaLowerSegment 1421273344 1421404416 (5684897211883 / 4000) (5685419866923 / 4000) := by
  exact
    packedTile65536 1421273344 1421404416 14 6200 37699 30 _ _ (52687 / 2500) (2107483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1421404416 :
    ThetaLowerSegment 1421404416 1421535488 (5685419866923 / 4000) (28429711357721 / 20000) := by
  exact
    packedTile65536 1421404416 1421535488 14 6197 37701 30 _ _ (210749 / 10000) (2107493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1421535488 :
    ThetaLowerSegment 1421535488 1421666560 (28429711357721 / 20000)
      (142161488402469 / 100000) := by
  exact
    packedTile65536 1421535488 1421666560 14 6136 37703 30 _ _ (2107499 / 100000) (1053751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1421666560 :
    ThetaLowerSegment 1421666560 1421797632 (142161488402469 / 100000)
      (28434951876069 / 20000) := by
  exact
    packedTile65536 1421666560 1421797632 14 6297 37704 30 _ _ (526877 / 25000) (2107511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1421797632 :
    ThetaLowerSegment 1421797632 1421928704 (28434951876069 / 20000)
      (142187821770711 / 100000) := by
  exact
    packedTile65536 1421797632 1421928704 14 6198 37706 30 _ _ (2107517 / 100000) (13172 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1421928704 :
    ThetaLowerSegment 1421928704 1422059776 (142187821770711 / 100000)
      (142200880008003 / 100000) := by
  exact
    packedTile65536 1421928704 1422059776 14 6196 37708 30 _ _ (2107527 / 100000) (210753 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1422059776 :
    ThetaLowerSegment 1422059776 1422190848 (142200880008003 / 100000)
      (142214068968291 / 100000) := by
  exact
    packedTile65536 1422059776 1422190848 14 6258 37710 30 _ _ (131721 / 6250) (2107539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1422190848 :
    ThetaLowerSegment 1422190848 1422321920 (142214068968291 / 100000)
      (142227131532201 / 100000) := by
  exact
    packedTile65536 1422190848 1422321920 14 6198 37711 30 _ _ (421509 / 20000) (526887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1422321920 :
    ThetaLowerSegment 1422321920 1422452992 (142227131532201 / 100000)
      (142240213119879 / 100000) := by
  exact
    packedTile65536 1422321920 1422452992 14 6207 37713 30 _ _ (1053777 / 50000) (2107557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1422452992 :
    ThetaLowerSegment 1422452992 1422584064 (142240213119879 / 100000)
      (142253187277707 / 100000) := by
  exact
    packedTile65536 1422452992 1422584064 14 6156 37715 30 _ _ (2107563 / 100000) (1053783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1422584064 :
    ThetaLowerSegment 1422584064 1422715136 (142253187277707 / 100000) (7113314924467 / 5000) := by
  exact
    packedTile65536 1422584064 1422715136 14 6221 37717 30 _ _ (2107573 / 100000) (263447 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1422715136 :
    ThetaLowerSegment 1422715136 1422846208 (7113314924467 / 5000) (35569879310911 / 25000) := by
  exact
    packedTile65536 1422715136 1422846208 14 6272 37718 30 _ _ (1053791 / 50000) (421517 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1422846208 :
    ThetaLowerSegment 1422846208 1422977280 (35569879310911 / 25000) (7114626686283 / 5000) := by
  exact
    packedTile65536 1422846208 1422977280 14 6176 37720 30 _ _ (2107591 / 100000) (1053797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1422977280 :
    ThetaLowerSegment 1422977280 1423108352 (7114626686283 / 5000) (7115287313503 / 5000) := by
  exact
    packedTile65536 1422977280 1423108352 14 6269 37722 30 _ _ (5269 / 250) (2107603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1423108352 :
    ThetaLowerSegment 1423108352 1423239424 (7115287313503 / 5000) (35579707576683 / 25000) := by
  exact
    packedTile65536 1423108352 1423239424 14 6208 37724 30 _ _ (2107609 / 100000) (526903 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1423239424 :
    ThetaLowerSegment 1423239424 1423370496 (35579707576683 / 25000) (4447874169338 / 3125) := by
  exact
    packedTile65536 1423239424 1423370496 14 6236 37725 30 _ _ (2107619 / 100000) (1053811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1423370496 :
    ThetaLowerSegment 1423370496 1423501568 (4447874169338 / 3125) (4448286210612 / 3125) := by
  exact
    packedTile65536 1423370496 1423501568 14 6256 37727 30 _ _ (526907 / 25000) (2107631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1423501568 :
    ThetaLowerSegment 1423501568 1423632640 (4448286210612 / 3125) (142358291425731 / 100000) := by
  exact
    packedTile65536 1423501568 1423632640 14 6231 37729 30 _ _ (2107637 / 100000) (52691 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1423632640 :
    ThetaLowerSegment 1423632640 1423763712 (142358291425731 / 100000)
      (142371491612629 / 100000) := by
  exact
    packedTile65536 1423632640 1423763712 14 6263 37731 30 _ _ (1053823 / 50000) (2107649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1423763712 :
    ThetaLowerSegment 1423763712 1423894784 (142371491612629 / 100000)
      (35596127649391 / 25000) := by
  exact
    packedTile65536 1423763712 1423894784 14 6177 37732 30 _ _ (421531 / 20000) (1053829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1423894784 :
    ThetaLowerSegment 1423894784 1424025856 (35596127649391 / 25000)
      (142397538074929 / 100000) := by
  exact
    packedTile65536 1423894784 1424025856 14 6181 37734 30 _ _ (421533 / 20000) (526917 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1424025856 :
    ThetaLowerSegment 1424025856 1424156928 (142397538074929 / 100000)
      (142410696283711 / 100000) := by
  exact
    packedTile65536 1424025856 1424156928 14 6243 37736 30 _ _ (1053837 / 50000) (2107677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1424156928 :
    ThetaLowerSegment 1424156928 1424288000 (142410696283711 / 100000)
      (71211967320317 / 50000) := by
  exact
    packedTile65536 1424156928 1424288000 14 6281 37738 30 _ _ (2107683 / 100000) (1053843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1424288000 :
    ThetaLowerSegment 1424288000 1424419072 (71211967320317 / 50000) (71218445311679 / 50000) := by
  exact
    packedTile65536 1424288000 1424419072 14 6147 37739 30 _ _ (526923 / 25000) (421539 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1424419072 :
    ThetaLowerSegment 1424419072 1424550144 (71218445311679 / 50000) (28489973547683 / 20000) := by
  exact
    packedTile65536 1424419072 1424550144 14 6157 37741 30 _ _ (2107701 / 100000) (263463 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1424550144 :
    ThetaLowerSegment 1424550144 1424681216 (28489973547683 / 20000)
      (142463011424211 / 100000) := by
  exact
    packedTile65536 1424550144 1424681216 14 6236 37743 30 _ _ (2107711 / 100000) (1053857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1424681216 :
    ThetaLowerSegment 1424681216 1424812288 (142463011424211 / 100000)
      (142475925424651 / 100000) := by
  exact
    packedTile65536 1424681216 1424812288 14 6127 37744 30 _ _ (52693 / 2500) (2107723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1424812288 :
    ThetaLowerSegment 1424812288 1424943360 (142475925424651 / 100000)
      (142489073438153 / 100000) := by
  exact
    packedTile65536 1424812288 1424943360 14 6238 37746 30 _ _ (2107729 / 100000) (526933 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1424943360 :
    ThetaLowerSegment 1424943360 1425074432 (142489073438153 / 100000)
      (142502229938749 / 100000) := by
  exact
    packedTile65536 1424943360 1425074432 14 6242 37748 30 _ _ (1053869 / 50000) (2107741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1425074432 :
    ThetaLowerSegment 1425074432 1425205504 (142502229938749 / 100000) (7125770484037 / 5000) := by
  exact
    packedTile65536 1425074432 1425205504 14 6253 37750 30 _ _ (2107747 / 100000) (8431 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1425205504 :
    ThetaLowerSegment 1425205504 1425336576 (7125770484037 / 5000) (71264274718939 / 50000) := by
  exact
    packedTile65536 1425205504 1425336576 14 6234 37751 30 _ _ (2107757 / 100000) (26347 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1425336576 :
    ThetaLowerSegment 1425336576 1425467648 (71264274718939 / 50000) (35635404923711 / 25000) := by
  exact
    packedTile65536 1425336576 1425467648 14 6201 37753 30 _ _ (1053883 / 50000) (2107769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1425467648 :
    ThetaLowerSegment 1425467648 1425598720 (35635404923711 / 25000)
      (142554757456419 / 100000) := by
  exact
    packedTile65536 1425467648 1425598720 14 6233 37755 30 _ _ (84311 / 4000) (1053889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1425598720 :
    ThetaLowerSegment 1425598720 1425729792 (142554757456419 / 100000)
      (142568000663291 / 100000) := by
  exact
    packedTile65536 1425598720 1425729792 14 6283 37757 30 _ _ (263473 / 12500) (2107787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1425729792 :
    ThetaLowerSegment 1425729792 1425860864 (142568000663291 / 100000)
      (142581081626649 / 100000) := by
  exact
    packedTile65536 1425729792 1425860864 14 6206 37758 30 _ _ (2107793 / 100000) (526949 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1425860864 :
    ThetaLowerSegment 1425860864 1425991936 (142581081626649 / 100000)
      (142594099417977 / 100000) := by
  exact
    packedTile65536 1425860864 1425991936 14 6176 37760 30 _ _ (2107803 / 100000) (1053903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1425991936 :
    ThetaLowerSegment 1425991936 1426123008 (142594099417977 / 100000)
      (142607448191373 / 100000) := by
  exact
    packedTile65536 1425991936 1426123008 14 6333 37762 30 _ _ (526953 / 25000) (421563 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1426123008 :
    ThetaLowerSegment 1426123008 1426254080 (142607448191373 / 100000)
      (142620440800017 / 100000) := by
  exact
    packedTile65536 1426123008 1426254080 14 6164 37764 30 _ _ (2107821 / 100000) (131739 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1426254080 :
    ThetaLowerSegment 1426254080 1426385152 (142620440800017 / 100000)
      (142633408170177 / 100000) := by
  exact
    packedTile65536 1426254080 1426385152 14 6152 37765 30 _ _ (210783 / 10000) (2107833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1426385152 :
    ThetaLowerSegment 1426385152 1426516224 (142633408170177 / 100000)
      (28529283550497 / 20000) := by
  exact
    packedTile65536 1426385152 1426516224 14 6172 37767 30 _ _ (2107839 / 100000) (1053921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1426516224 :
    ThetaLowerSegment 1426516224 1426647296 (28529283550497 / 20000) (14265949695553 / 10000) := by
  exact
    packedTile65536 1426516224 1426647296 14 6205 37769 30 _ _ (2107849 / 100000) (526963 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1426647296 :
    ThetaLowerSegment 1426647296 1426778368 (14265949695553 / 10000) (8917033642061 / 6250) := by
  exact
    packedTile65536 1426647296 1426778368 14 6187 37770 30 _ _ (1053929 / 50000) (2107861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1426778368 :
    ThetaLowerSegment 1426778368 1426909440 (8917033642061 / 6250) (142685377290873 / 100000) := by
  exact
    packedTile65536 1426778368 1426909440 14 6091 37772 30 _ _ (2107867 / 100000) (210787 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1426909440 :
    ThetaLowerSegment 1426909440 1427040512 (142685377290873 / 100000)
      (28539717469953 / 20000) := by
  exact
    packedTile65536 1426909440 1427040512 14 6267 37774 30 _ _ (526969 / 25000) (2107879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1427040512 :
    ThetaLowerSegment 1427040512 1427171584 (28539717469953 / 20000) (14271179324929 / 10000) := by
  exact
    packedTile65536 1427040512 1427171584 14 6265 37776 30 _ _ (421577 / 20000) (131743 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1427171584 :
    ThetaLowerSegment 1427171584 1427302656 (14271179324929 / 10000) (2854498424387 / 2000) := by
  exact
    packedTile65536 1427171584 1427302656 14 6228 37777 30 _ _ (421579 / 20000) (1053949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1427302656 :
    ThetaLowerSegment 1427302656 1427433728 (2854498424387 / 2000) (14273792698703 / 10000) := by
  exact
    packedTile65536 1427302656 1427433728 14 6170 37779 30 _ _ (65872 / 3125) (2107907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1427433728 :
    ThetaLowerSegment 1427433728 1427564800 (14273792698703 / 10000)
      (142750913839023 / 100000) := by
  exact
    packedTile65536 1427433728 1427564800 14 6161 37781 30 _ _ (2107913 / 100000) (526979 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1427564800 :
    ThetaLowerSegment 1427564800 1427695872 (142750913839023 / 100000)
      (142764096783211 / 100000) := by
  exact
    packedTile65536 1427564800 1427695872 14 6254 37783 30 _ _ (1053961 / 50000) (84317 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1427695872 :
    ThetaLowerSegment 1427695872 1427826944 (142764096783211 / 100000)
      (142777187034721 / 100000) := by
  exact
    packedTile65536 1427695872 1427826944 14 6210 37784 30 _ _ (2107931 / 100000) (1053967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1427826944 :
    ThetaLowerSegment 1427826944 1427958016 (142777187034721 / 100000)
      (142790416466161 / 100000) := by
  exact
    packedTile65536 1427826944 1427958016 14 6276 37786 30 _ _ (105397 / 5000) (2107943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1427958016 :
    ThetaLowerSegment 1427958016 1428089088 (142790416466161 / 100000)
      (142803645960361 / 100000) := by
  exact
    packedTile65536 1427958016 1428089088 14 6276 37788 30 _ _ (42159 / 2000) (2107953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1428089088 :
    ThetaLowerSegment 1428089088 1428220160 (142803645960361 / 100000) (7140833762747 / 5000) := by
  exact
    packedTile65536 1428089088 1428220160 14 6181 37790 30 _ _ (2107959 / 100000) (1053981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1428220160 :
    ThetaLowerSegment 1428220160 1428351232 (7140833762747 / 5000) (35707437745111 / 25000) := by
  exact
    packedTile65536 1428220160 1428351232 14 6203 37791 30 _ _ (65874 / 3125) (2107971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1428351232 :
    ThetaLowerSegment 1428351232 1428482304 (35707437745111 / 25000) (71421391247129 / 50000) := by
  exact
    packedTile65536 1428351232 1428482304 14 6182 37793 30 _ _ (2107977 / 100000) (105399 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1428482304 :
    ThetaLowerSegment 1428482304 1428613376 (71421391247129 / 50000) (71427961839491 / 50000) := by
  exact
    packedTile65536 1428482304 1428613376 14 6234 37795 30 _ _ (1053993 / 50000) (2107989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1428613376 :
    ThetaLowerSegment 1428613376 1428744448 (71427961839491 / 50000) (71434507167071 / 50000) := by
  exact
    packedTile65536 1428613376 1428744448 14 6210 37797 30 _ _ (526999 / 25000) (2107999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1428744448 :
    ThetaLowerSegment 1428744448 1428875520 (71434507167071 / 50000) (8930128403317 / 6250) := by
  exact
    packedTile65536 1428744448 1428875520 14 6186 37798 30 _ _ (421601 / 20000) (263501 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1428875520 :
    ThetaLowerSegment 1428875520 1429006592 (8930128403317 / 6250) (71447670632657 / 50000) := by
  exact
    packedTile65536 1428875520 1429006592 14 6303 37800 30 _ _ (1054007 / 50000) (2108017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1429006592 :
    ThetaLowerSegment 1429006592 1429137664 (71447670632657 / 50000) (71454201287911 / 50000) := by
  exact
    packedTile65536 1429006592 1429137664 14 6196 37802 30 _ _ (2108023 / 100000) (1054013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1429137664 :
    ThetaLowerSegment 1429137664 1429268736 (71454201287911 / 50000) (14292147026619 / 10000) := by
  exact
    packedTile65536 1429137664 1429268736 14 6199 37803 30 _ _ (65876 / 3125) (421607 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1429268736 :
    ThetaLowerSegment 1429268736 1429399808 (14292147026619 / 10000) (28586935428611 / 20000) := by
  exact
    packedTile65536 1429268736 1429399808 14 6265 37805 30 _ _ (2108041 / 100000) (527011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1429399808 :
    ThetaLowerSegment 1429399808 1429530880 (28586935428611 / 20000)
      (142947759707561 / 100000) := by
  exact
    packedTile65536 1429399808 1429530880 14 6206 37807 30 _ _ (2108051 / 100000) (1054027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1429530880 :
    ThetaLowerSegment 1429530880 1429661952 (142947759707561 / 100000)
      (142961061566161 / 100000) := by
  exact
    packedTile65536 1429530880 1429661952 14 6310 37809 30 _ _ (105403 / 5000) (2108063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1429661952 :
    ThetaLowerSegment 1429661952 1429793024 (142961061566161 / 100000)
      (142974258078101 / 100000) := by
  exact
    packedTile65536 1429661952 1429793024 14 6260 37810 30 _ _ (2108069 / 100000) (263509 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1429793024 :
    ThetaLowerSegment 1429793024 1429924096 (142974258078101 / 100000) (228779667719 / 160) := by
  exact
    packedTile65536 1429793024 1429924096 14 6183 37812 30 _ _ (1054039 / 50000) (2108081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1429924096 :
    ThetaLowerSegment 1429924096 1430055168 (228779667719 / 160) (143000459435777 / 100000) := by
  exact
    packedTile65536 1429924096 1430055168 14 6246 37814 30 _ _ (2108087 / 100000) (210809 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1430055168 :
    ThetaLowerSegment 1430055168 1430186240 (143000459435777 / 100000)
      (143013611846721 / 100000) := by
  exact
    packedTile65536 1430055168 1430186240 14 6239 37816 30 _ _ (65878 / 3125) (2108099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1430186240 :
    ThetaLowerSegment 1430186240 1430317312 (143013611846721 / 100000)
      (28605342323481 / 20000) := by
  exact
    packedTile65536 1430186240 1430317312 14 6214 37817 30 _ _ (1054053 / 50000) (2108109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1430317312 :
    ThetaLowerSegment 1430317312 1430448384 (28605342323481 / 20000) (5721594481551 / 4000) := by
  exact
    packedTile65536 1430317312 1430448384 14 6238 37819 30 _ _ (421623 / 20000) (1054059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1430448384 :
    ThetaLowerSegment 1430448384 1430579456 (5721594481551 / 4000) (28610569616523 / 20000) := by
  exact
    packedTile65536 1430448384 1430579456 14 6160 37821 30 _ _ (527031 / 25000) (2108127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1430579456 :
    ThetaLowerSegment 1430579456 1430710528 (28610569616523 / 20000)
      (143066007048801 / 100000) := by
  exact
    packedTile65536 1430579456 1430710528 14 6242 37823 30 _ _ (2108133 / 100000) (263517 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1430710528 :
    ThetaLowerSegment 1430710528 1430841600 (143066007048801 / 100000)
      (28615841646801 / 20000) := by
  exact
    packedTile65536 1430710528 1430841600 14 6262 37824 30 _ _ (1054071 / 50000) (421629 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1430841600 :
    ThetaLowerSegment 1430841600 1430972672 (28615841646801 / 20000) (35773078652193 / 25000) := by
  exact
    packedTile65536 1430841600 1430972672 14 6217 37826 30 _ _ (2108151 / 100000) (1054077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1430972672 :
    ThetaLowerSegment 1430972672 1431103744 (35773078652193 / 25000) (17888176313113 / 12500) := by
  exact
    packedTile65536 1430972672 1431103744 14 6212 37828 30 _ _ (2108161 / 100000) (527041 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1431103744 :
    ThetaLowerSegment 1431103744 1431234816 (17888176313113 / 12500) (8944898220879 / 6250) := by
  exact
    packedTile65536 1431103744 1431234816 14 6148 37829 30 _ _ (210817 / 10000) (2108173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1431234816 :
    ThetaLowerSegment 1431234816 1431365888 (8944898220879 / 6250) (7156568317471 / 5000) := by
  exact
    packedTile65536 1431234816 1431365888 14 6164 37831 30 _ _ (2108179 / 100000) (1054091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1431365888 :
    ThetaLowerSegment 1431365888 1431496960 (7156568317471 / 5000) (35786141955669 / 25000) := by
  exact
    packedTile65536 1431365888 1431496960 14 6262 37833 30 _ _ (527047 / 25000) (2108191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1431496960 :
    ThetaLowerSegment 1431496960 1431628032 (35786141955669 / 25000)
      (143157788326063 / 100000) := by
  exact
    packedTile65536 1431496960 1431628032 14 6271 37835 30 _ _ (2108197 / 100000) (10541 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1431628032 :
    ThetaLowerSegment 1431628032 1431759104 (143157788326063 / 100000)
      (143170992020241 / 100000) := by
  exact
    packedTile65536 1431628032 1431759104 14 6263 37836 30 _ _ (1054103 / 50000) (2108209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1431759104 :
    ThetaLowerSegment 1431759104 1431890176 (143170992020241 / 100000)
      (71592047288233 / 50000) := by
  exact
    packedTile65536 1431759104 1431890176 14 6215 37838 30 _ _ (421643 / 20000) (1054109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1431890176 :
    ThetaLowerSegment 1431890176 1432021248 (71592047288233 / 50000) (71598591218633 / 50000) := by
  exact
    packedTile65536 1431890176 1432021248 14 6208 37840 30 _ _ (84329 / 4000) (527057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1432021248 :
    ThetaLowerSegment 1432021248 1432152320 (71598591218633 / 50000) (71605093012289 / 50000) := by
  exact
    packedTile65536 1432021248 1432152320 14 6168 37842 30 _ _ (1054117 / 50000) (2108237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1432152320 :
    ThetaLowerSegment 1432152320 1432283392 (71605093012289 / 50000) (1790291610143 / 1250) := by
  exact
    packedTile65536 1432152320 1432283392 14 6234 37843 30 _ _ (2108243 / 100000) (1054123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1432283392 :
    ThetaLowerSegment 1432283392 1432414464 (1790291610143 / 1250) (17904561065053 / 12500) := by
  exact
    packedTile65536 1432283392 1432414464 14 6242 37845 30 _ _ (527063 / 25000) (421651 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1432414464 :
    ThetaLowerSegment 1432414464 1432545536 (17904561065053 / 12500) (71624824142793 / 50000) := by
  exact
    packedTile65536 1432414464 1432545536 14 6242 37847 30 _ _ (2108261 / 100000) (263533 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1432545536 :
    ThetaLowerSegment 1432545536 1432676608 (71624824142793 / 50000) (17907830721267 / 12500) := by
  exact
    packedTile65536 1432545536 1432676608 14 6165 37848 30 _ _ (210827 / 10000) (2108273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1432676608 :
    ThetaLowerSegment 1432676608 1432807680 (17907830721267 / 12500) (8954736140391 / 6250) := by
  exact
    packedTile65536 1432676608 1432807680 14 6229 37850 30 _ _ (52707 / 2500) (2108283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1432807680 :
    ThetaLowerSegment 1432807680 1432938752 (8954736140391 / 6250) (143289033059199 / 100000) := by
  exact
    packedTile65536 1432807680 1432938752 14 6287 37852 30 _ _ (2108289 / 100000) (527073 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1432938752 :
    ThetaLowerSegment 1432938752 1433069824 (143289033059199 / 100000)
      (143301969575727 / 100000) := by
  exact
    packedTile65536 1432938752 1433069824 14 6136 37854 30 _ _ (1054149 / 50000) (2108301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1433069824 :
    ThetaLowerSegment 1433069824 1433200896 (143301969575727 / 100000)
      (143314939880391 / 100000) := by
  exact
    packedTile65536 1433069824 1433200896 14 6152 37855 30 _ _ (2108307 / 100000) (210831 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1433200896 :
    ThetaLowerSegment 1433200896 1433331968 (143314939880391 / 100000)
      (143327834341047 / 100000) := by
  exact
    packedTile65536 1433200896 1433331968 14 6116 37857 30 _ _ (527079 / 25000) (2108319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1433331968 :
    ThetaLowerSegment 1433331968 1433463040 (143327834341047 / 100000)
      (17917618778859 / 12500) := by
  exact
    packedTile65536 1433331968 1433463040 14 6221 37859 30 _ _ (84333 / 4000) (263541 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1433463040 :
    ThetaLowerSegment 1433463040 1433594112 (17917618778859 / 12500) (35838578212941 / 25000) := by
  exact
    packedTile65536 1433463040 1433594112 14 6338 37861 30 _ _ (1054167 / 50000) (2108337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1433594112 :
    ThetaLowerSegment 1433594112 1433725184 (35838578212941 / 25000) (35841832968991 / 25000) := by
  exact
    packedTile65536 1433594112 1433725184 14 6175 37862 30 _ _ (263543 / 12500) (2108347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1433725184 :
    ThetaLowerSegment 1433725184 1433856256 (35841832968991 / 25000)
      (143380342522327 / 100000) := by
  exact
    packedTile65536 1433725184 1433856256 14 6171 37864 30 _ _ (2108353 / 100000) (527089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1433856256 :
    ThetaLowerSegment 1433856256 1433987328 (143380342522327 / 100000)
      (143393414366727 / 100000) := by
  exact
    packedTile65536 1433856256 1433987328 14 6200 37866 30 _ _ (1054181 / 50000) (421673 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1433987328 :
    ThetaLowerSegment 1433987328 1434118400 (143393414366727 / 100000)
      (143406380848377 / 100000) := by
  exact
    packedTile65536 1433987328 1434118400 14 6150 37868 30 _ _ (2108371 / 100000) (1054187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1434118400 :
    ThetaLowerSegment 1434118400 1434249472 (143406380848377 / 100000)
      (143419575090417 / 100000) := by
  exact
    packedTile65536 1434118400 1434249472 14 6258 37869 30 _ _ (105419 / 5000) (2108383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1434249472 :
    ThetaLowerSegment 1434249472 1434380544 (143419575090417 / 100000)
      (35858135947789 / 25000) := by
  exact
    packedTile65536 1434249472 1434380544 14 6151 37871 30 _ _ (2108389 / 100000) (263549 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1434380544 :
    ThetaLowerSegment 1434380544 1434511616 (35858135947789 / 25000) (71722868018721 / 50000) := by
  exact
    packedTile65536 1434380544 1434511616 14 6257 37873 30 _ _ (1054199 / 50000) (2108401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1434511616 :
    ThetaLowerSegment 1434511616 1434642688 (71722868018721 / 50000) (71729476823597 / 50000) := by
  exact
    packedTile65536 1434511616 1434642688 14 6269 37874 30 _ _ (263551 / 12500) (2108411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1434642688 :
    ThetaLowerSegment 1434642688 1434773760 (71729476823597 / 50000) (71736122553981 / 50000) := by
  exact
    packedTile65536 1434642688 1434773760 14 6304 37876 30 _ _ (2108417 / 100000) (105421 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1434773760 :
    ThetaLowerSegment 1434773760 1434904832 (71736122553981 / 50000) (17935661242453 / 12500) := by
  exact
    packedTile65536 1434773760 1434904832 14 6187 37878 30 _ _ (1054213 / 50000) (2108429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1434904832 :
    ThetaLowerSegment 1434904832 1435035904 (17935661242453 / 12500) (35874601101331 / 25000) := by
  exact
    packedTile65536 1434904832 1435035904 14 6220 37880 30 _ _ (421687 / 20000) (1054219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1435035904 :
    ThetaLowerSegment 1435035904 1435166976 (35874601101331 / 25000) (3587789501797 / 2500) := by
  exact
    packedTile65536 1435035904 1435166976 14 6249 37881 30 _ _ (527111 / 25000) (2108447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1435166976 :
    ThetaLowerSegment 1435166976 1435298048 (3587789501797 / 2500) (71762387385377 / 50000) := by
  exact
    packedTile65536 1435166976 1435298048 14 6258 37883 30 _ _ (2108453 / 100000) (263557 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1435298048 :
    ThetaLowerSegment 1435298048 1435429120 (71762387385377 / 50000) (71768839279097 / 50000) := by
  exact
    packedTile65536 1435298048 1435429120 14 6120 37885 30 _ _ (1054231 / 50000) (421693 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1435429120 :
    ThetaLowerSegment 1435429120 1435560192 (71768839279097 / 50000)
      (143550833308763 / 100000) := by
  exact
    packedTile65536 1435429120 1435560192 14 6239 37887 30 _ _ (2108471 / 100000) (1054237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1435560192 :
    ThetaLowerSegment 1435560192 1435691264 (143550833308763 / 100000)
      (71781956108203 / 50000) := by
  exact
    packedTile65536 1435560192 1435691264 14 6203 37888 30 _ _ (2108481 / 100000) (527121 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1435691264 :
    ThetaLowerSegment 1435691264 1435822336 (71781956108203 / 50000) (71788460799853 / 50000) := by
  exact
    packedTile65536 1435691264 1435822336 14 6170 37890 30 _ _ (210849 / 10000) (2108493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1435822336 :
    ThetaLowerSegment 1435822336 1435953408 (71788460799853 / 50000)
      (143590013269997 / 100000) := by
  exact
    packedTile65536 1435822336 1435953408 14 6209 37892 30 _ _ (2108499 / 100000) (1054251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1435953408 :
    ThetaLowerSegment 1435953408 1436084480 (143590013269997 / 100000)
      (143603324281001 / 100000) := by
  exact
    packedTile65536 1435953408 1436084480 14 6313 37893 30 _ _ (527127 / 25000) (2108511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1436084480 :
    ThetaLowerSegment 1436084480 1436215552 (143603324281001 / 100000)
      (143616287443517 / 100000) := by
  exact
    packedTile65536 1436084480 1436215552 14 6148 37895 30 _ _ (2108517 / 100000) (52713 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1436215552 :
    ThetaLowerSegment 1436215552 1436346624 (143616287443517 / 100000)
      (143629499467433 / 100000) := by
  exact
    packedTile65536 1436215552 1436346624 14 6266 37897 30 _ _ (1054263 / 50000) (2108529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1436346624 :
    ThetaLowerSegment 1436346624 1436477696 (143629499467433 / 100000)
      (71821306223299 / 50000) := by
  exact
    packedTile65536 1436346624 1436477696 14 6219 37899 30 _ _ (421707 / 20000) (1054269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1436477696 :
    ThetaLowerSegment 1436477696 1436608768 (71821306223299 / 50000) (71827852198147 / 50000) := by
  exact
    packedTile65536 1436477696 1436608768 14 6209 37900 30 _ _ (65892 / 3125) (2108547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1436608768 :
    ThetaLowerSegment 1436608768 1436739840 (71827852198147 / 50000) (35917210699067 / 25000) := by
  exact
    packedTile65536 1436608768 1436739840 14 6231 37902 30 _ _ (1054277 / 50000) (2108557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1436739840 :
    ThetaLowerSegment 1436739840 1436870912 (35917210699067 / 25000) (898012027007 / 625) := by
  exact
    packedTile65536 1436739840 1436870912 14 6204 37904 30 _ _ (2108563 / 100000) (1054283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1436870912 :
    ThetaLowerSegment 1436870912 1437001984 (898012027007 / 625) (35923776251173 / 25000) := by
  exact
    packedTile65536 1436870912 1437001984 14 6251 37906 30 _ _ (527143 / 25000) (84343 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1437001984 :
    ThetaLowerSegment 1437001984 1437133056 (35923776251173 / 25000)
      (143708252007227 / 100000) := by
  exact
    packedTile65536 1437001984 1437133056 14 6235 37907 30 _ _ (2108581 / 100000) (263573 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1437133056 :
    ThetaLowerSegment 1437133056 1437264128 (143708252007227 / 100000)
      (143721219835727 / 100000) := by
  exact
    packedTile65536 1437133056 1437264128 14 6150 37909 30 _ _ (210859 / 10000) (2108593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1437264128 :
    ThetaLowerSegment 1437264128 1437395200 (143721219835727 / 100000)
      (17966784271517 / 12500) := by
  exact
    packedTile65536 1437264128 1437395200 14 6191 37911 30 _ _ (2108599 / 100000) (1054301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1437395200 :
    ThetaLowerSegment 1437395200 1437526272 (17966784271517 / 12500) (17968419497021 / 12500) := by
  exact
    packedTile65536 1437395200 1437526272 14 6204 37912 30 _ _ (65894 / 3125) (2108611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1437526272 :
    ThetaLowerSegment 1437526272 1437657344 (17968419497021 / 12500)
      (143760465248057 / 100000) := by
  exact
    packedTile65536 1437526272 1437657344 14 6217 37914 30 _ _ (2108617 / 100000) (105431 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1437657344 :
    ThetaLowerSegment 1437657344 1437788416 (143760465248057 / 100000)
      (143773429086853 / 100000) := by
  exact
    packedTile65536 1437657344 1437788416 14 6148 37916 30 _ _ (2108627 / 100000) (210863 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1437788416 :
    ThetaLowerSegment 1437788416 1437919488 (143773429086853 / 100000)
      (143786468891877 / 100000) := by
  exact
    packedTile65536 1437788416 1437919488 14 6184 37918 30 _ _ (527159 / 25000) (2108639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1437919488 :
    ThetaLowerSegment 1437919488 1438050560 (143786468891877 / 100000)
      (71899814472661 / 50000) := by
  exact
    packedTile65536 1437919488 1438050560 14 6241 37919 30 _ _ (421729 / 20000) (263581 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1438050560 :
    ThetaLowerSegment 1438050560 1438181632 (71899814472661 / 50000) (17976583871289 / 12500) := by
  exact
    packedTile65536 1438050560 1438181632 14 6185 37921 30 _ _ (1054327 / 50000) (2108657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1438181632 :
    ThetaLowerSegment 1438181632 1438312704 (17976583871289 / 12500)
      (143825666660381 / 100000) := by
  exact
    packedTile65536 1438181632 1438312704 14 6163 37923 30 _ _ (2108663 / 100000) (1054333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1438312704 :
    ThetaLowerSegment 1438312704 1438443776 (143825666660381 / 100000)
      (28767753146169 / 20000) := by
  exact
    packedTile65536 1438312704 1438443776 14 6212 37925 30 _ _ (65896 / 3125) (84347 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1438443776 :
    ThetaLowerSegment 1438443776 1438574848 (28767753146169 / 20000) (28770363693247 / 20000) := by
  exact
    packedTile65536 1438443776 1438574848 14 6190 37926 30 _ _ (2108681 / 100000) (527171 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1438574848 :
    ThetaLowerSegment 1438574848 1438705920 (28770363693247 / 20000) (28772984373179 / 20000) := by
  exact
    packedTile65536 1438574848 1438705920 14 6214 37928 30 _ _ (210869 / 10000) (2108693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1438705920 :
    ThetaLowerSegment 1438705920 1438836992 (28772984373179 / 20000) (14387796416921 / 10000) := by
  exact
    packedTile65536 1438705920 1438836992 14 6185 37930 30 _ _ (2108699 / 100000) (1054351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1438836992 :
    ThetaLowerSegment 1438836992 1438968064 (14387796416921 / 10000) (71945599213447 / 50000) := by
  exact
    packedTile65536 1438836992 1438968064 14 6276 37932 30 _ _ (2108709 / 100000) (263589 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1438968064 :
    ThetaLowerSegment 1438968064 1439099136 (71945599213447 / 50000) (359760507227 / 250) := by
  exact
    packedTile65536 1438968064 1439099136 14 6167 37933 30 _ _ (1054359 / 50000) (2108721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1439099136 :
    ThetaLowerSegment 1439099136 1439230208 (359760507227 / 250) (14391729808547 / 10000) := by
  exact
    packedTile65536 1439099136 1439230208 14 6210 37935 30 _ _ (2108727 / 100000) (210873 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1439230208 :
    ThetaLowerSegment 1439230208 1439361280 (14391729808547 / 10000) (71965166091343 / 50000) := by
  exact
    packedTile65536 1439230208 1439361280 14 6181 37937 30 _ _ (65898 / 3125) (2108739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1439361280 :
    ThetaLowerSegment 1439361280 1439492352 (71965166091343 / 50000)
      (143943539252621 / 100000) := by
  exact
    packedTile65536 1439361280 1439492352 14 6263 37938 30 _ _ (421749 / 20000) (527187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1439492352 :
    ThetaLowerSegment 1439492352 1439623424 (143943539252621 / 100000)
      (143956799097773 / 100000) := by
  exact
    packedTile65536 1439492352 1439623424 14 6288 37940 30 _ _ (1054377 / 50000) (2108757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1439623424 :
    ThetaLowerSegment 1439623424 1439754496 (143956799097773 / 100000)
      (71984876614441 / 50000) := by
  exact
    packedTile65536 1439623424 1439754496 14 6143 37942 30 _ _ (2108763 / 100000) (1054383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1439754496 :
    ThetaLowerSegment 1439754496 1439885568 (71984876614441 / 50000) (71991384284833 / 50000) := by
  exact
    packedTile65536 1439754496 1439885568 14 6172 37944 30 _ _ (527193 / 25000) (84351 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1439885568 :
    ThetaLowerSegment 1439885568 1440016640 (71991384284833 / 50000) (71997951028867 / 50000) := by
  exact
    packedTile65536 1439885568 1440016640 14 6228 37945 30 _ _ (2108781 / 100000) (131799 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1440016640 :
    ThetaLowerSegment 1440016640 1440147712 (71997951028867 / 50000) (5760359146829 / 4000) := by
  exact
    packedTile65536 1440016640 1440147712 14 6201 37947 30 _ _ (2108791 / 100000) (1054397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1440147712 :
    ThetaLowerSegment 1440147712 1440278784 (5760359146829 / 4000) (5760890480077 / 4000) := by
  exact
    packedTile65536 1440147712 1440278784 14 6299 37949 30 _ _ (2636 / 125) (2108803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1440278784 :
    ThetaLowerSegment 1440278784 1440409856 (5760890480077 / 4000) (18004430520873 / 12500) := by
  exact
    packedTile65536 1440278784 1440409856 14 6251 37951 30 _ _ (2108809 / 100000) (527203 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1440409856 :
    ThetaLowerSegment 1440409856 1440540928 (18004430520873 / 12500) (36012156069871 / 25000) := by
  exact
    packedTile65536 1440409856 1440540928 14 6250 37952 30 _ _ (1054409 / 50000) (2108821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1440540928 :
    ThetaLowerSegment 1440540928 1440672000 (36012156069871 / 25000) (72030813653383 / 50000) := by
  exact
    packedTile65536 1440540928 1440672000 14 6166 37954 30 _ _ (2108827 / 100000) (210883 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1440672000 :
    ThetaLowerSegment 1440672000 1440803072 (72030813653383 / 50000) (72037420636571 / 50000) := by
  exact
    packedTile65536 1440672000 1440803072 14 6266 37956 30 _ _ (527209 / 25000) (2108839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1440803072 :
    ThetaLowerSegment 1440803072 1440934144 (72037420636571 / 50000)
      (144088002574787 / 100000) := by
  exact
    packedTile65536 1440803072 1440934144 14 6241 37957 30 _ _ (421769 / 20000) (131803 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1440934144 :
    ThetaLowerSegment 1440934144 1441065216 (144088002574787 / 100000)
      (144101338967483 / 100000) := by
  exact
    packedTile65536 1440934144 1441065216 14 6324 37959 30 _ _ (1054427 / 50000) (2108857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1441065216 :
    ThetaLowerSegment 1441065216 1441196288 (144101338967483 / 100000)
      (36028607170031 / 25000) := by
  exact
    packedTile65536 1441065216 1441196288 14 6207 37961 30 _ _ (2108863 / 100000) (1054433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1441196288 :
    ThetaLowerSegment 1441196288 1441327360 (36028607170031 / 25000) (36031912826891 / 25000) := by
  exact
    packedTile65536 1441196288 1441327360 14 6270 37963 30 _ _ (263609 / 12500) (16871 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1441327360 :
    ThetaLowerSegment 1441327360 1441458432 (36031912826891 / 25000) (14414071161379 / 10000) := by
  exact
    packedTile65536 1441327360 1441458432 14 6193 37964 30 _ _ (1054441 / 50000) (421777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1441458432 :
    ThetaLowerSegment 1441458432 1441589504 (14414071161379 / 10000)
      (144153464077667 / 100000) := by
  exact
    packedTile65536 1441458432 1441589504 14 6047 37966 30 _ _ (2108891 / 100000) (1054447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1441589504 :
    ThetaLowerSegment 1441589504 1441720576 (144153464077667 / 100000)
      (144166710078567 / 100000) := by
  exact
    packedTile65536 1441589504 1441720576 14 6281 37968 30 _ _ (21089 / 1000) (2108903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1441720576 :
    ThetaLowerSegment 1441720576 1441851648 (144166710078567 / 100000)
      (144179532245287 / 100000) := by
  exact
    packedTile65536 1441720576 1441851648 14 6080 37969 30 _ _ (2108909 / 100000) (131807 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1441851648 :
    ThetaLowerSegment 1441851648 1441982720 (144179532245287 / 100000)
      (144192596992297 / 100000) := by
  exact
    packedTile65536 1441851648 1441982720 14 6195 37971 30 _ _ (1054459 / 50000) (2108921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1441982720 :
    ThetaLowerSegment 1441982720 1442113792 (144192596992297 / 100000)
      (36051429156791 / 25000) := by
  exact
    packedTile65536 1441982720 1442113792 14 6221 37973 30 _ _ (2108927 / 100000) (210893 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1442113792 :
    ThetaLowerSegment 1442113792 1442244864 (36051429156791 / 25000) (36054692208017 / 25000) := by
  exact
    packedTile65536 1442113792 1442244864 14 6189 37975 30 _ _ (263617 / 12500) (2108939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1442244864 :
    ThetaLowerSegment 1442244864 1442375936 (36054692208017 / 25000)
      (144231694555973 / 100000) := by
  exact
    packedTile65536 1442244864 1442375936 14 6129 37976 30 _ _ (421789 / 20000) (527237 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1442375936 :
    ThetaLowerSegment 1442375936 1442441472 (144231694555973 / 100000)
      (144238232313373 / 100000) := by
  exact
    packedTile65536 1442375936 1442441472 13 3100 37978 30 _ _ (1054477 / 50000) (2108957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1442441472 :
    ThetaLowerSegment 1442441472 1442507008 (144238232313373 / 100000) (2884895528263 / 2000) := by
  exact
    packedTile65536 1442441472 1442507008 13 3103 37979 30 _ _ (2108959 / 100000) (1054481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1442507008 :
    ThetaLowerSegment 1442507008 1442572544 (2884895528263 / 2000) (18031419019973 / 12500) := by
  exact
    packedTile65536 1442507008 1442572544 13 3118 37980 30 _ _ (2108963 / 100000) (1054483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1442572544 :
    ThetaLowerSegment 1442572544 1442638080 (18031419019973 / 12500) (9016118254347 / 6250) := by
  exact
    packedTile65536 1442572544 1442638080 13 3101 37981 30 _ _ (263621 / 12500) (2108971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1442638080 :
    ThetaLowerSegment 1442638080 1442703616 (9016118254347 / 6250) (36066137523539 / 25000) := by
  exact
    packedTile65536 1442638080 1442703616 13 3157 37982 30 _ _ (527243 / 25000) (84359 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1442703616 :
    ThetaLowerSegment 1442703616 1442834688 (36066137523539 / 25000)
      (144277686911889 / 100000) := by
  exact
    packedTile65536 1442703616 1442834688 14 6229 37982 30 _ _ (2108977 / 100000) (105449 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1442834688 :
    ThetaLowerSegment 1442834688 1442965760 (144277686911889 / 100000)
      (144290948215857 / 100000) := by
  exact
    packedTile65536 1442834688 1442965760 14 6288 37984 30 _ _ (1054493 / 50000) (2108989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1442965760 :
    ThetaLowerSegment 1442965760 1443096832 (144290948215857 / 100000)
      (72151968758031 / 50000) := by
  exact
    packedTile65536 1442965760 1443096832 14 6159 37986 30 _ _ (421799 / 20000) (1054499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1443096832 :
    ThetaLowerSegment 1443096832 1443227904 (72151968758031 / 50000) (72158467653857 / 50000) := by
  exact
    packedTile65536 1443096832 1443227904 14 6163 37988 30 _ _ (527251 / 25000) (2109007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1443227904 :
    ThetaLowerSegment 1443227904 1443358976 (72158467653857 / 50000)
      (144330312777173 / 100000) := by
  exact
    packedTile65536 1443227904 1443358976 14 6343 37989 30 _ _ (2109013 / 100000) (263627 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1443358976 :
    ThetaLowerSegment 1443358976 1443490048 (144330312777173 / 100000) (5773739007339 / 4000) := by
  exact
    packedTile65536 1443358976 1443490048 14 6241 37991 30 _ _ (1054511 / 50000) (84361 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1443490048 :
    ThetaLowerSegment 1443490048 1443621120 (5773739007339 / 4000) (36089200537591 / 25000) := by
  exact
    packedTile65536 1443490048 1443621120 14 6319 37993 30 _ _ (2109031 / 100000) (1054517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1443621120 :
    ThetaLowerSegment 1443621120 1443752192 (36089200537591 / 25000)
      (144369762207309 / 100000) := by
  exact
    packedTile65536 1443621120 1443752192 14 6145 37995 30 _ _ (2109041 / 100000) (527261 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1443752192 :
    ThetaLowerSegment 1443752192 1443883264 (144369762207309 / 100000)
      (144382802463459 / 100000) := by
  exact
    packedTile65536 1443752192 1443883264 14 6183 37996 30 _ _ (42181 / 2000) (2109053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1443883264 :
    ThetaLowerSegment 1443883264 1444014336 (144382802463459 / 100000)
      (144395853320551 / 100000) := by
  exact
    packedTile65536 1443883264 1444014336 14 6188 37998 30 _ _ (2109059 / 100000) (1054531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1444014336 :
    ThetaLowerSegment 1444014336 1444145408 (144395853320551 / 100000)
      (144409056086231 / 100000) := by
  exact
    packedTile65536 1444014336 1444145408 14 6260 38000 30 _ _ (527267 / 25000) (2109071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1444145408 :
    ThetaLowerSegment 1444145408 1444276480 (144409056086231 / 100000)
      (144422022691627 / 100000) := by
  exact
    packedTile65536 1444145408 1444276480 14 6148 38001 30 _ _ (2109077 / 100000) (52727 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1444276480 :
    ThetaLowerSegment 1444276480 1444407552 (144422022691627 / 100000)
      (144435113788429 / 100000) := by
  exact
    packedTile65536 1444276480 1444407552 14 6207 38003 30 _ _ (1054543 / 50000) (2109089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1444407552 :
    ThetaLowerSegment 1444407552 1444538624 (144435113788429 / 100000)
      (72224072943217 / 50000) := by
  exact
    packedTile65536 1444407552 1444538624 14 6179 38005 30 _ _ (421819 / 20000) (1054549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1444538624 :
    ThetaLowerSegment 1444538624 1444669696 (72224072943217 / 50000) (72230596401889 / 50000) := by
  exact
    packedTile65536 1444538624 1444669696 14 6186 38007 30 _ _ (131819 / 6250) (2109107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1444669696 :
    ThetaLowerSegment 1444669696 1444800768 (72230596401889 / 50000)
      (144474419051401 / 100000) := by
  exact
    packedTile65536 1444669696 1444800768 14 6271 38008 30 _ _ (2109113 / 100000) (527279 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1444800768 :
    ThetaLowerSegment 1444800768 1444931840 (144474419051401 / 100000)
      (144487358514871 / 100000) := by
  exact
    packedTile65536 1444800768 1444931840 14 6135 38010 30 _ _ (1054561 / 50000) (16873 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1444931840 :
    ThetaLowerSegment 1444931840 1445062912 (144487358514871 / 100000)
      (144500473091429 / 100000) := by
  exact
    packedTile65536 1444931840 1445062912 14 6218 38012 30 _ _ (2109131 / 100000) (1054567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1445062912 :
    ThetaLowerSegment 1445062912 1445193984 (144500473091429 / 100000)
      (144513629906749 / 100000) := by
  exact
    packedTile65536 1445062912 1445193984 14 6238 38013 30 _ _ (105457 / 5000) (2109143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1445193984 :
    ThetaLowerSegment 1445193984 1445325056 (144513629906749 / 100000)
      (72263371243041 / 50000) := by
  exact
    packedTile65536 1445193984 1445325056 14 6217 38015 30 _ _ (2109149 / 100000) (65911 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1445325056 :
    ThetaLowerSegment 1445325056 1445456128 (72263371243041 / 50000) (28907979462153 / 20000) := by
  exact
    packedTile65536 1445325056 1445456128 14 6237 38017 30 _ _ (2109159 / 100000) (1054581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1445456128 :
    ThetaLowerSegment 1445456128 1445587200 (28907979462153 / 20000)
      (144553107029949 / 100000) := by
  exact
    packedTile65536 1445456128 1445587200 14 6263 38019 30 _ _ (131823 / 6250) (2109171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1445587200 :
    ThetaLowerSegment 1445587200 1445718272 (144553107029949 / 100000)
      (72283130983449 / 50000) := by
  exact
    packedTile65536 1445587200 1445718272 14 6237 38020 30 _ _ (2109177 / 100000) (105459 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1445718272 :
    ThetaLowerSegment 1445718272 1445849344 (72283130983449 / 50000) (36144869004297 / 25000) := by
  exact
    packedTile65536 1445718272 1445849344 14 6265 38022 30 _ _ (1054593 / 50000) (2109189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1445849344 :
    ThetaLowerSegment 1445849344 1445980416 (36144869004297 / 25000)
      (144592660595133 / 100000) := by
  exact
    packedTile65536 1445849344 1445980416 14 6251 38024 30 _ _ (421839 / 20000) (1054599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1445980416 :
    ThetaLowerSegment 1445980416 1446111488 (144592660595133 / 100000)
      (144605741878341 / 100000) := by
  exact
    packedTile65536 1445980416 1446111488 14 6202 38026 30 _ _ (527301 / 25000) (2109207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1446111488 :
    ThetaLowerSegment 1446111488 1446242560 (144605741878341 / 100000)
      (18077362657281 / 12500) := by
  exact
    packedTile65536 1446111488 1446242560 14 6239 38027 30 _ _ (2109213 / 100000) (65913 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1446242560 :
    ThetaLowerSegment 1446242560 1446373632 (18077362657281 / 12500) (72316059876261 / 50000) := by
  exact
    packedTile65536 1446242560 1446373632 14 6267 38029 30 _ _ (1054611 / 50000) (84369 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1446373632 :
    ThetaLowerSegment 1446373632 1446504704 (72316059876261 / 50000)
      (144645043010859 / 100000) := by
  exact
    packedTile65536 1446373632 1446504704 14 6127 38031 30 _ _ (2109231 / 100000) (1054617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1446504704 :
    ThetaLowerSegment 1446504704 1446635776 (144645043010859 / 100000)
      (144658248962499 / 100000) := by
  exact
    packedTile65536 1446504704 1446635776 14 6261 38032 30 _ _ (52731 / 2500) (2109243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1446635776 :
    ThetaLowerSegment 1446635776 1446766848 (144658248962499 / 100000)
      (18083936089809 / 12500) := by
  exact
    packedTile65536 1446635776 1446766848 14 6277 38034 30 _ _ (2109249 / 100000) (527313 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1446766848 :
    ThetaLowerSegment 1446766848 1446897920 (18083936089809 / 12500) (14468463150507 / 10000) := by
  exact
    packedTile65536 1446766848 1446897920 14 6231 38036 30 _ _ (1054629 / 50000) (2109261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1446897920 :
    ThetaLowerSegment 1446897920 1447028992 (14468463150507 / 10000) (72348808076361 / 50000) := by
  exact
    packedTile65536 1446897920 1447028992 14 6156 38038 30 _ _ (2109267 / 100000) (210927 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1447028992 :
    ThetaLowerSegment 1447028992 1447160064 (72348808076361 / 50000) (72355261406283 / 50000) := by
  exact
    packedTile65536 1447028992 1447160064 14 6119 38039 30 _ _ (527319 / 25000) (2109279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1447160064 :
    ThetaLowerSegment 1447160064 1447291136 (72355261406283 / 50000)
      (144723640455981 / 100000) := by
  exact
    packedTile65536 1447160064 1447291136 14 6219 38041 30 _ _ (421857 / 20000) (263661 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1447291136 :
    ThetaLowerSegment 1447291136 1447422208 (144723640455981 / 100000)
      (144736958538297 / 100000) := by
  exact
    packedTile65536 1447291136 1447422208 14 6314 38043 30 _ _ (1054647 / 50000) (2109297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1447422208 :
    ThetaLowerSegment 1447422208 1447553280 (144736958538297 / 100000)
      (144749926539289 / 100000) := by
  exact
    packedTile65536 1447422208 1447553280 14 6148 38045 30 _ _ (263663 / 12500) (2109307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1447553280 :
    ThetaLowerSegment 1447553280 1447684352 (144749926539289 / 100000)
      (144763046466149 / 100000) := by
  exact
    packedTile65536 1447553280 1447684352 14 6220 38046 30 _ _ (2109313 / 100000) (527329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1447684352 :
    ThetaLowerSegment 1447684352 1447815424 (144763046466149 / 100000)
      (144776155902379 / 100000) := by
  exact
    packedTile65536 1447684352 1447815424 14 6215 38048 30 _ _ (1054661 / 50000) (84373 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1447815424 :
    ThetaLowerSegment 1447815424 1447946496 (144776155902379 / 100000)
      (36197284708671 / 25000) := by
  exact
    packedTile65536 1447815424 1447946496 14 6155 38050 30 _ _ (2109331 / 100000) (1054667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1447946496 :
    ThetaLowerSegment 1447946496 1448077568 (36197284708671 / 25000) (9050152652629 / 6250) := by
  exact
    packedTile65536 1447946496 1448077568 14 6307 38051 30 _ _ (105467 / 5000) (2109343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1448077568 :
    ThetaLowerSegment 1448077568 1448208640 (9050152652629 / 6250) (144815535171307 / 100000) := by
  exact
    packedTile65536 1448077568 1448208640 14 6207 38053 30 _ _ (2109349 / 100000) (263669 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1448208640 :
    ThetaLowerSegment 1448208640 1448339712 (144815535171307 / 100000)
      (144828619518981 / 100000) := by
  exact
    packedTile65536 1448208640 1448339712 14 6203 38055 30 _ _ (1054679 / 50000) (2109361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1448339712 :
    ThetaLowerSegment 1448339712 1448470784 (144828619518981 / 100000)
      (72420911023517 / 50000) := by
  exact
    packedTile65536 1448339712 1448470784 14 6259 38057 30 _ _ (2109367 / 100000) (210937 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1448470784 :
    ThetaLowerSegment 1448470784 1448601856 (72420911023517 / 50000) (72427427940669 / 50000) := by
  exact
    packedTile65536 1448470784 1448601856 14 6179 38058 30 _ _ (65918 / 3125) (2109379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1448601856 :
    ThetaLowerSegment 1448601856 1448732928 (72427427940669 / 50000) (72434059847109 / 50000) := by
  exact
    packedTile65536 1448601856 1448732928 14 6288 38060 30 _ _ (421877 / 20000) (527347 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1448732928 :
    ThetaLowerSegment 1448732928 1448864000 (72434059847109 / 50000) (72440662250329 / 50000) := by
  exact
    packedTile65536 1448732928 1448864000 14 6260 38062 30 _ _ (1054697 / 50000) (2109397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1448864000 :
    ThetaLowerSegment 1448864000 1448995072 (72440662250329 / 50000)
      (144894396471049 / 100000) := by
  exact
    packedTile65536 1448864000 1448995072 14 6197 38063 30 _ _ (2109403 / 100000) (1054703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1448995072 :
    ThetaLowerSegment 1448995072 1449126144 (144894396471049 / 100000) (1159259764853 / 800) := by
  exact
    packedTile65536 1448995072 1449126144 14 6198 38065 30 _ _ (527353 / 25000) (421883 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1449126144 :
    ThetaLowerSegment 1449126144 1449257216 (1159259764853 / 800) (7246033251749 / 5000) := by
  exact
    packedTile65536 1449126144 1449257216 14 6255 38067 30 _ _ (2109421 / 100000) (131839 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1449257216 :
    ThetaLowerSegment 1449257216 1449322752 (7246033251749 / 5000) (14492715575109 / 10000) := by
  exact
    packedTile65536 1449257216 1449322752 13 3077 38069 30 _ _ (210943 / 10000) (2109433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1449322752 :
    ThetaLowerSegment 1449322752 1449339136 (14492715575109 / 10000) (28985759800191 / 20000) := by
  exact
    packedTile65536 1449322752 1449339136 11 779 38069 30 _ _ (421887 / 20000) (1054719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1449339136 :
    ThetaLowerSegment 1449339136 1449341184 (28985759800191 / 20000)
      (144929050023839 / 100000) := by
  exact
    packedTile65536 1449339136 1449341184 8 119 38070 30 _ _ (527359 / 25000) (2109439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1417341184_1449341184 :
    ThetaLowerSegment 1417341184 1449341184 (141728394035641 / 100000)
      (144929050023839 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1417341184 cell1417406720)
                  (ThetaLowerSegment.join cell1417472256 cell1417603328))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1417734400 cell1417865472)
                  (ThetaLowerSegment.join cell1417996544 cell1418127616)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1418258688 cell1418389760)
                  (ThetaLowerSegment.join cell1418520832 cell1418651904))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1418782976 cell1418914048)
                  (ThetaLowerSegment.join cell1419045120 cell1419176192))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1419307264 cell1419438336)
                  (ThetaLowerSegment.join cell1419569408 cell1419700480))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1419831552 cell1419962624)
                  (ThetaLowerSegment.join cell1420093696 cell1420224768)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1420355840 cell1420486912)
                  (ThetaLowerSegment.join cell1420617984 cell1420749056))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1420880128 cell1421011200)
                  (ThetaLowerSegment.join cell1421142272 cell1421273344)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1421404416 cell1421535488)
                  (ThetaLowerSegment.join cell1421666560 cell1421797632))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1421928704 cell1422059776)
                  (ThetaLowerSegment.join cell1422190848 cell1422321920)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1422452992 cell1422584064)
                  (ThetaLowerSegment.join cell1422715136 cell1422846208))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1422977280 cell1423108352)
                  (ThetaLowerSegment.join cell1423239424 cell1423370496))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1423501568 cell1423632640)
                  (ThetaLowerSegment.join cell1423763712 cell1423894784))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1424025856 cell1424156928)
                  (ThetaLowerSegment.join cell1424288000 cell1424419072)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1424550144 cell1424681216)
                  (ThetaLowerSegment.join cell1424812288 cell1424943360))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1425074432 cell1425205504)
                  (ThetaLowerSegment.join cell1425336576 cell1425467648))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1425598720 cell1425729792)
                  (ThetaLowerSegment.join cell1425860864 cell1425991936))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1426123008 cell1426254080)
                  (ThetaLowerSegment.join cell1426385152 cell1426516224)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1426647296 cell1426778368)
                  (ThetaLowerSegment.join cell1426909440 cell1427040512))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1427171584 cell1427302656)
                  (ThetaLowerSegment.join cell1427433728 cell1427564800))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1427695872 cell1427826944)
                  (ThetaLowerSegment.join cell1427958016 cell1428089088))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1428220160 cell1428351232)
                  (ThetaLowerSegment.join cell1428482304 cell1428613376)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1428744448 cell1428875520)
                  (ThetaLowerSegment.join cell1429006592 cell1429137664))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1429268736 cell1429399808)
                  (ThetaLowerSegment.join cell1429530880 cell1429661952)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1429793024 cell1429924096)
                  (ThetaLowerSegment.join cell1430055168 cell1430186240))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1430317312 cell1430448384)
                  (ThetaLowerSegment.join cell1430579456 cell1430710528)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1430841600 cell1430972672)
                  (ThetaLowerSegment.join cell1431103744 cell1431234816))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1431365888 cell1431496960)
                  (ThetaLowerSegment.join cell1431628032 cell1431759104))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1431890176 cell1432021248)
                  (ThetaLowerSegment.join cell1432152320 cell1432283392))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1432414464 cell1432545536)
                  (ThetaLowerSegment.join cell1432676608 cell1432807680)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1432938752 cell1433069824)
                  (ThetaLowerSegment.join cell1433200896 cell1433331968))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1433463040 cell1433594112)
                  (ThetaLowerSegment.join cell1433725184 cell1433856256)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1433987328 cell1434118400)
                  (ThetaLowerSegment.join cell1434249472 cell1434380544))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1434511616 cell1434642688)
                  (ThetaLowerSegment.join cell1434773760 cell1434904832)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1435035904 cell1435166976)
                  (ThetaLowerSegment.join cell1435298048 cell1435429120))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1435560192 cell1435691264)
                  (ThetaLowerSegment.join cell1435822336 cell1435953408))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1436084480 cell1436215552)
                  (ThetaLowerSegment.join cell1436346624 cell1436477696))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1436608768 cell1436739840)
                  (ThetaLowerSegment.join cell1436870912 cell1437001984)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1437133056 cell1437264128)
                  (ThetaLowerSegment.join cell1437395200 cell1437526272))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1437657344 cell1437788416)
                  (ThetaLowerSegment.join cell1437919488 cell1438050560)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1438181632 cell1438312704)
                  (ThetaLowerSegment.join cell1438443776 cell1438574848))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1438705920 cell1438836992)
                  (ThetaLowerSegment.join cell1438968064 cell1439099136)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1439230208 cell1439361280)
                  (ThetaLowerSegment.join cell1439492352 cell1439623424))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1439754496 cell1439885568)
                  (ThetaLowerSegment.join cell1440016640 cell1440147712))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1440278784 cell1440409856)
                  (ThetaLowerSegment.join cell1440540928 cell1440672000))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1440803072 cell1440934144)
                  (ThetaLowerSegment.join cell1441065216 cell1441196288)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1441327360 cell1441458432)
                  (ThetaLowerSegment.join cell1441589504 cell1441720576))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1441851648 cell1441982720)
                  (ThetaLowerSegment.join cell1442113792 cell1442244864))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1442375936 cell1442441472)
                  (ThetaLowerSegment.join cell1442507008 cell1442572544))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1442638080 cell1442703616)
                  (ThetaLowerSegment.join cell1442834688 cell1442965760)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1443096832 cell1443227904)
                  (ThetaLowerSegment.join cell1443358976 cell1443490048))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1443621120 cell1443752192)
                  (ThetaLowerSegment.join cell1443883264 cell1444014336))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1444145408 cell1444276480)
                  (ThetaLowerSegment.join cell1444407552 cell1444538624))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1444669696 cell1444800768)
                  (ThetaLowerSegment.join cell1444931840 cell1445062912)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1445193984 cell1445325056)
                  (ThetaLowerSegment.join cell1445456128 cell1445587200))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1445718272 cell1445849344)
                  (ThetaLowerSegment.join cell1445980416 cell1446111488)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1446242560 cell1446373632)
                  (ThetaLowerSegment.join cell1446504704 cell1446635776))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1446766848 cell1446897920)
                  (ThetaLowerSegment.join cell1447028992 cell1447160064)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1447291136 cell1447422208)
                  (ThetaLowerSegment.join cell1447553280 cell1447684352))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1447815424 cell1447946496)
                  (ThetaLowerSegment.join cell1448077568 cell1448208640))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1448339712 cell1448470784)
                  (ThetaLowerSegment.join cell1448601856 cell1448732928))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1448864000 cell1448995072)
                  (ThetaLowerSegment.join cell1449126144 cell1449257216)))
              (ThetaLowerSegment.join cell1449322752 cell1449339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
