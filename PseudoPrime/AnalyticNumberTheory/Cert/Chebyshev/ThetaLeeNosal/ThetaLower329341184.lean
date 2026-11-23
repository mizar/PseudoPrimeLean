/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 329341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell297341184 :
    ThetaLowerSegment 297341184 297406720 (7433021829089 / 25000) (3717327911707 / 12500) := by
  exact
    packedTile32768 297341184 297406720 13 3350 17243 28 _ _ (975519 / 50000) (1951041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297406720 :
    ThetaLowerSegment 297406720 297472256 (3717327911707 / 12500) (7436274715449 / 25000) := by
  exact
    packedTile32768 297406720 297472256 13 3319 17245 28 _ _ (97553 / 5000) (1951063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297472256 :
    ThetaLowerSegment 297472256 297505024 (7436274715449 / 25000) (14874150293679 / 50000) := by
  exact
    packedTile32768 297472256 297505024 12 1641 17247 28 _ _ (975541 / 50000) (390217 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297505024 :
    ThetaLowerSegment 297505024 297537792 (14874150293679 / 50000) (14875789211799 / 50000) := by
  exact
    packedTile32768 297505024 297537792 12 1680 17248 28 _ _ (1951093 / 100000) (243887 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297537792 :
    ThetaLowerSegment 297537792 297570560 (14875789211799 / 50000) (14877433992471 / 50000) := by
  exact
    packedTile32768 297537792 297570560 12 1686 17249 28 _ _ (60972 / 3125) (1951107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297570560 :
    ThetaLowerSegment 297570560 297603328 (14877433992471 / 50000) (1859882896687 / 6250) := by
  exact
    packedTile32768 297570560 297603328 12 1670 17250 28 _ _ (390223 / 20000) (975559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297603328 :
    ThetaLowerSegment 297603328 297636096 (1859882896687 / 6250) (595228201841 / 2000) := by
  exact
    packedTile32768 297603328 297636096 12 1683 17251 28 _ _ (975563 / 50000) (1951129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297636096 :
    ThetaLowerSegment 297636096 297668864 (595228201841 / 2000) (29764654832881 / 100000) := by
  exact
    packedTile32768 297636096 297668864 12 1663 17252 28 _ _ (1951137 / 100000) (97557 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297668864 :
    ThetaLowerSegment 297668864 297701632 (29764654832881 / 100000) (29767944468409 / 100000) := by
  exact
    packedTile32768 297668864 297701632 12 1686 17253 28 _ _ (487787 / 25000) (1951151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297701632 :
    ThetaLowerSegment 297701632 297734400 (29767944468409 / 100000) (29771222415529 / 100000) := by
  exact
    packedTile32768 297701632 297734400 12 1680 17254 28 _ _ (1951159 / 100000) (975581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297734400 :
    ThetaLowerSegment 297734400 297767168 (29771222415529 / 100000) (29774588183779 / 100000) := by
  exact
    packedTile32768 297734400 297767168 12 1725 17254 28 _ _ (195117 / 10000) (1951173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297767168 :
    ThetaLowerSegment 297767168 297799936 (29774588183779 / 100000) (14888912596529 / 50000) := by
  exact
    packedTile32768 297767168 297799936 12 1659 17255 28 _ _ (1951181 / 100000) (121949 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297799936 :
    ThetaLowerSegment 297799936 297832704 (14888912596529 / 50000) (14890565256153 / 50000) := by
  exact
    packedTile32768 297799936 297832704 12 1694 17256 28 _ _ (243899 / 12500) (390239 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297832704 :
    ThetaLowerSegment 297832704 297865472 (14890565256153 / 50000) (29784363655677 / 100000) := by
  exact
    packedTile32768 297832704 297865472 12 1657 17257 28 _ _ (1951203 / 100000) (975603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297865472 :
    ThetaLowerSegment 297865472 297898240 (29784363655677 / 100000) (29787641695197 / 100000) := by
  exact
    packedTile32768 297865472 297898240 12 1680 17258 28 _ _ (975607 / 50000) (1951217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297898240 :
    ThetaLowerSegment 297898240 297931008 (29787641695197 / 100000) (29791032924247 / 100000) := by
  exact
    packedTile32768 297898240 297931008 12 1738 17259 28 _ _ (78049 / 4000) (487807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297931008 :
    ThetaLowerSegment 297931008 297996544 (29791032924247 / 100000) (29797674931591 / 100000) := by
  exact
    packedTile32768 297931008 297996544 13 3404 17260 28 _ _ (487809 / 25000) (1951239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297996544 :
    ThetaLowerSegment 297996544 298062080 (29797674931591 / 100000) (29804196035827 / 100000) := by
  exact
    packedTile32768 297996544 298062080 13 3342 17262 28 _ _ (975629 / 50000) (1951261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298062080 :
    ThetaLowerSegment 298062080 298127616 (29804196035827 / 100000) (29810684041827 / 100000) := by
  exact
    packedTile32768 298062080 298127616 13 3325 17264 28 _ _ (24391 / 1250) (1951283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298127616 :
    ThetaLowerSegment 298127616 298193152 (29810684041827 / 100000) (29817207244413 / 100000) := by
  exact
    packedTile32768 298127616 298193152 13 3343 17266 28 _ _ (975651 / 50000) (390261 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298193152 :
    ThetaLowerSegment 298193152 298225920 (29817207244413 / 100000) (29820426929013 / 100000) := by
  exact
    packedTile32768 298193152 298225920 12 1650 17268 28 _ _ (487831 / 25000) (1951327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298225920 :
    ThetaLowerSegment 298225920 298258688 (29820426929013 / 100000) (14911816486209 / 50000) := by
  exact
    packedTile32768 298225920 298258688 12 1643 17269 28 _ _ (390267 / 20000) (975669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298258688 :
    ThetaLowerSegment 298258688 298291456 (14911816486209 / 50000) (372837536837 / 1250) := by
  exact
    packedTile32768 298258688 298291456 12 1727 17270 28 _ _ (975673 / 50000) (1951349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298291456 :
    ThetaLowerSegment 298291456 298324224 (372837536837 / 1250) (7457576160751 / 25000) := by
  exact
    packedTile32768 298291456 298324224 12 1692 17271 28 _ _ (1951357 / 100000) (12196 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298324224 :
    ThetaLowerSegment 298324224 298356992 (7457576160751 / 25000) (7458404516467 / 25000) := by
  exact
    packedTile32768 298324224 298356992 12 1698 17272 28 _ _ (243921 / 12500) (1951371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298356992 :
    ThetaLowerSegment 298356992 298422528 (7458404516467 / 25000) (29840231289299 / 100000) := by
  exact
    packedTile32768 298356992 298422528 13 3389 17273 28 _ _ (1951379 / 100000) (975691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298422528 :
    ThetaLowerSegment 298422528 298488064 (29840231289299 / 100000) (29846787996659 / 100000) := by
  exact
    packedTile32768 298422528 298488064 13 3360 17274 28 _ _ (1951401 / 100000) (487851 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298488064 :
    ThetaLowerSegment 298488064 298553600 (29846787996659 / 100000) (1194136288939 / 4000) := by
  exact
    packedTile32768 298488064 298553600 13 3392 17276 28 _ _ (1951423 / 100000) (975713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298553600 :
    ThetaLowerSegment 298553600 298619136 (1194136288939 / 4000) (5971963934349 / 20000) := by
  exact
    packedTile32768 298553600 298619136 13 3286 17278 28 _ _ (390289 / 20000) (243931 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298619136 :
    ThetaLowerSegment 298619136 298651904 (5971963934349 / 20000) (29863103989023 / 100000) := by
  exact
    packedTile32768 298619136 298651904 12 1683 17280 28 _ _ (975733 / 50000) (1951469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298651904 :
    ThetaLowerSegment 298651904 298717440 (29863103989023 / 100000) (5973911114397 / 20000) := by
  exact
    packedTile32768 298651904 298717440 13 3306 17281 28 _ _ (1951477 / 100000) (48787 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298717440 :
    ThetaLowerSegment 298717440 298750208 (5973911114397 / 20000) (597454925457 / 2000) := by
  exact
    packedTile32768 298717440 298750208 12 1635 17283 28 _ _ (1951499 / 100000) (975751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298750208 :
    ThetaLowerSegment 298750208 298782976 (597454925457 / 2000) (2987609506401 / 10000) := by
  exact
    packedTile32768 298750208 298782976 12 1716 17284 28 _ _ (195151 / 10000) (1951513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298782976 :
    ThetaLowerSegment 298782976 298815744 (2987609506401 / 10000) (1195173773859 / 4000) := by
  exact
    packedTile32768 298782976 298815744 12 1665 17285 28 _ _ (1951521 / 100000) (487881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298815744 :
    ThetaLowerSegment 298815744 298848512 (1195173773859 / 4000) (29882572180403 / 100000) := by
  exact
    packedTile32768 298815744 298848512 12 1654 17286 28 _ _ (487883 / 25000) (390307 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298848512 :
    ThetaLowerSegment 298848512 298881280 (29882572180403 / 100000) (7471454399103 / 25000) := by
  exact
    packedTile32768 298848512 298881280 12 1663 17287 28 _ _ (1951543 / 100000) (975773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298881280 :
    ThetaLowerSegment 298881280 298914048 (7471454399103 / 25000) (14944547127789 / 50000) := by
  exact
    packedTile32768 298881280 298914048 12 1679 17288 28 _ _ (975777 / 50000) (1951557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298914048 :
    ThetaLowerSegment 298914048 298946816 (14944547127789 / 50000) (7473066875067 / 25000) := by
  exact
    packedTile32768 298914048 298946816 12 1626 17289 28 _ _ (390313 / 20000) (121973 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298946816 :
    ThetaLowerSegment 298946816 298979584 (7473066875067 / 25000) (7473883121729 / 25000) := by
  exact
    packedTile32768 298946816 298979584 12 1673 17290 28 _ _ (243947 / 12500) (1951579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell298979584 :
    ThetaLowerSegment 298979584 299012352 (7473883121729 / 25000) (29898840426881 / 100000) := by
  exact
    packedTile32768 298979584 299012352 12 1695 17291 28 _ _ (1951587 / 100000) (195159 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299012352 :
    ThetaLowerSegment 299012352 299045120 (29898840426881 / 100000) (5980430848057 / 20000) := by
  exact
    packedTile32768 299012352 299045120 12 1698 17291 28 _ _ (975799 / 50000) (1951601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299045120 :
    ThetaLowerSegment 299045120 299077888 (5980430848057 / 20000) (7476357747949 / 25000) := by
  exact
    packedTile32768 299045120 299077888 12 1679 17292 28 _ _ (1951609 / 100000) (487903 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299077888 :
    ThetaLowerSegment 299077888 299110656 (7476357747949 / 25000) (1869297162541 / 6250) := by
  exact
    packedTile32768 299077888 299110656 12 1703 17293 28 _ _ (97581 / 5000) (1951623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299110656 :
    ThetaLowerSegment 299110656 299143424 (1869297162541 / 6250) (7478018093339 / 25000) := by
  exact
    packedTile32768 299110656 299143424 12 1700 17294 28 _ _ (1951631 / 100000) (975817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299143424 :
    ThetaLowerSegment 299143424 299176192 (7478018093339 / 25000) (14957635557297 / 50000) := by
  exact
    packedTile32768 299143424 299176192 12 1639 17295 28 _ _ (975821 / 50000) (390329 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299176192 :
    ThetaLowerSegment 299176192 299208960 (14957635557297 / 50000) (7479634545429 / 25000) := by
  exact
    packedTile32768 299176192 299208960 12 1674 17296 28 _ _ (1951653 / 100000) (243957 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299208960 :
    ThetaLowerSegment 299208960 299241728 (7479634545429 / 25000) (7480460099301 / 25000) := by
  exact
    packedTile32768 299208960 299241728 12 1692 17297 28 _ _ (121979 / 6250) (1951667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299241728 :
    ThetaLowerSegment 299241728 299274496 (7480460099301 / 25000) (7481275899451 / 25000) := by
  exact
    packedTile32768 299241728 299274496 12 1672 17298 28 _ _ (78067 / 4000) (975839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299274496 :
    ThetaLowerSegment 299274496 299307264 (7481275899451 / 25000) (14964159012323 / 50000) := by
  exact
    packedTile32768 299274496 299307264 12 1647 17299 28 _ _ (975843 / 50000) (1951689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299307264 :
    ThetaLowerSegment 299307264 299340032 (14964159012323 / 50000) (14965798437803 / 50000) := by
  exact
    packedTile32768 299307264 299340032 12 1680 17300 28 _ _ (1951697 / 100000) (19517 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299340032 :
    ThetaLowerSegment 299340032 299372800 (14965798437803 / 50000) (2993493039287 / 10000) := by
  exact
    packedTile32768 299340032 299372800 12 1708 17301 28 _ _ (487927 / 25000) (1951711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299372800 :
    ThetaLowerSegment 299372800 299405568 (2993493039287 / 10000) (3742275672169 / 12500) := by
  exact
    packedTile32768 299372800 299405568 12 1678 17302 28 _ _ (1951719 / 100000) (975861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299405568 :
    ThetaLowerSegment 299405568 299438336 (3742275672169 / 12500) (1197659917767 / 4000) := by
  exact
    packedTile32768 299405568 299438336 12 1687 17303 28 _ _ (1951729 / 100000) (487933 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299438336 :
    ThetaLowerSegment 299438336 299471104 (1197659917767 / 4000) (5988965522523 / 20000) := by
  exact
    packedTile32768 299438336 299471104 12 1706 17304 28 _ _ (97587 / 5000) (1951743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299471104 :
    ThetaLowerSegment 299471104 299503872 (5988965522523 / 20000) (29948149492817 / 100000) := by
  exact
    packedTile32768 299471104 299503872 12 1702 17305 28 _ _ (1951751 / 100000) (975877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299503872 :
    ThetaLowerSegment 299503872 299536640 (29948149492817 / 100000) (5990275541433 / 20000) := by
  exact
    packedTile32768 299503872 299536640 12 1654 17306 28 _ _ (975881 / 50000) (390353 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299536640 :
    ThetaLowerSegment 299536640 299569408 (5990275541433 / 20000) (5990939144253 / 20000) := by
  exact
    packedTile32768 299536640 299569408 12 1700 17307 28 _ _ (1951773 / 100000) (60993 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299569408 :
    ThetaLowerSegment 299569408 299602176 (5990939144253 / 20000) (29957941538057 / 100000) := by
  exact
    packedTile32768 299569408 299602176 12 1663 17308 28 _ _ (243973 / 12500) (1951787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299602176 :
    ThetaLowerSegment 299602176 299634944 (29957941538057 / 100000) (7490297819183 / 25000) := by
  exact
    packedTile32768 299602176 299634944 12 1665 17309 28 _ _ (390359 / 20000) (975899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299634944 :
    ThetaLowerSegment 299634944 299667712 (7490297819183 / 25000) (2996443713011 / 10000) := by
  exact
    packedTile32768 299634944 299667712 12 1663 17309 28 _ _ (975903 / 50000) (1951809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299667712 :
    ThetaLowerSegment 299667712 299700480 (2996443713011 / 10000) (29967718134487 / 100000) := by
  exact
    packedTile32768 299667712 299700480 12 1681 17310 28 _ _ (1951817 / 100000) (97591 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299700480 :
    ThetaLowerSegment 299700480 299733248 (29967718134487 / 100000) (29971020627463 / 100000) := by
  exact
    packedTile32768 299700480 299733248 12 1692 17311 28 _ _ (487957 / 25000) (1951831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299733248 :
    ThetaLowerSegment 299733248 299766016 (29971020627463 / 100000) (29974327042729 / 100000) := by
  exact
    packedTile32768 299733248 299766016 12 1694 17312 28 _ _ (1951839 / 100000) (975921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299766016 :
    ThetaLowerSegment 299766016 299798784 (29974327042729 / 100000) (29977721309879 / 100000) := by
  exact
    packedTile32768 299766016 299798784 12 1739 17313 28 _ _ (39037 / 2000) (1951853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299798784 :
    ThetaLowerSegment 299798784 299831552 (29977721309879 / 100000) (14990495338527 / 50000) := by
  exact
    packedTile32768 299798784 299831552 12 1675 17314 28 _ _ (1951861 / 100000) (243983 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299831552 :
    ThetaLowerSegment 299831552 299864320 (14990495338527 / 50000) (14992127103519 / 50000) := by
  exact
    packedTile32768 299831552 299864320 12 1672 17315 28 _ _ (60996 / 3125) (3123 / 160) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299864320 :
    ThetaLowerSegment 299864320 299897088 (14992127103519 / 50000) (14993762781473 / 50000) := by
  exact
    packedTile32768 299864320 299897088 12 1676 17316 28 _ _ (1951883 / 100000) (975943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299897088 :
    ThetaLowerSegment 299897088 299929856 (14993762781473 / 50000) (29990775464791 / 100000) := by
  exact
    packedTile32768 299897088 299929856 12 1665 17317 28 _ _ (1951893 / 100000) (243987 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299929856 :
    ThetaLowerSegment 299929856 299962624 (29990775464791 / 100000) (29994162018231 / 100000) := by
  exact
    packedTile32768 299929856 299962624 12 1735 17318 28 _ _ (60997 / 3125) (1951907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell299962624 :
    ThetaLowerSegment 299962624 300028160 (29994162018231 / 100000) (15000333875463 / 50000) := by
  exact
    packedTile32768 299962624 300028160 13 3333 17319 28 _ _ (390383 / 20000) (975959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300028160 :
    ThetaLowerSegment 300028160 300060928 (15000333875463 / 50000) (15001989118039 / 50000) := by
  exact
    packedTile32768 300028160 300060928 12 1696 17321 28 _ _ (1951937 / 100000) (97597 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300060928 :
    ThetaLowerSegment 300060928 300093696 (15001989118039 / 50000) (15003641442021 / 50000) := by
  exact
    packedTile32768 300060928 300093696 12 1693 17322 28 _ _ (487987 / 25000) (1951951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300093696 :
    ThetaLowerSegment 300093696 300159232 (15003641442021 / 50000) (750342230337 / 2500) := by
  exact
    packedTile32768 300093696 300159232 13 3282 17323 28 _ _ (1951959 / 100000) (975981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300159232 :
    ThetaLowerSegment 300159232 300192000 (750342230337 / 2500) (15008501838609 / 50000) := by
  exact
    packedTile32768 300159232 300192000 12 1698 17325 28 _ _ (1951981 / 100000) (121999 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300192000 :
    ThetaLowerSegment 300192000 300224768 (15008501838609 / 50000) (15010180551729 / 50000) := by
  exact
    packedTile32768 300192000 300224768 12 1720 17326 28 _ _ (243999 / 12500) (390399 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300224768 :
    ThetaLowerSegment 300224768 300257536 (15010180551729 / 50000) (6004727703299 / 20000) := by
  exact
    packedTile32768 300224768 300257536 12 1679 17326 28 _ _ (1952003 / 100000) (976003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300257536 :
    ThetaLowerSegment 300257536 300290304 (6004727703299 / 20000) (30026921804043 / 100000) := by
  exact
    packedTile32768 300257536 300290304 12 1682 17327 28 _ _ (976007 / 50000) (1952017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300290304 :
    ThetaLowerSegment 300290304 300355840 (30026921804043 / 100000) (15016684671309 / 50000) := by
  exact
    packedTile32768 300290304 300355840 13 3303 17328 28 _ _ (78081 / 4000) (488007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300355840 :
    ThetaLowerSegment 300355840 300388608 (15016684671309 / 50000) (3003669172491 / 10000) := by
  exact
    packedTile32768 300355840 300388608 12 1702 17330 28 _ _ (976023 / 50000) (1952049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300388608 :
    ThetaLowerSegment 300388608 300421376 (3003669172491 / 10000) (30040027790323 / 100000) := by
  exact
    packedTile32768 300388608 300421376 12 1709 17331 28 _ _ (1952057 / 100000) (97603 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300421376 :
    ThetaLowerSegment 300421376 300486912 (30040027790323 / 100000) (30046576978463 / 100000) := by
  exact
    packedTile32768 300421376 300486912 13 3355 17332 28 _ _ (488017 / 25000) (1952071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300486912 :
    ThetaLowerSegment 300486912 300519680 (30046576978463 / 100000) (30049772549793 / 100000) := by
  exact
    packedTile32768 300486912 300519680 12 1637 17334 28 _ _ (195209 / 10000) (1952093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300519680 :
    ThetaLowerSegment 300519680 300552448 (30049772549793 / 100000) (7513278148651 / 25000) := by
  exact
    packedTile32768 300519680 300552448 12 1711 17335 28 _ _ (1952101 / 100000) (244013 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300552448 :
    ThetaLowerSegment 300552448 300585216 (7513278148651 / 25000) (7514105356111 / 25000) := by
  exact
    packedTile32768 300552448 300585216 12 1695 17336 28 _ _ (122007 / 6250) (390423 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300585216 :
    ThetaLowerSegment 300585216 300650752 (7514105356111 / 25000) (240503641441 / 800) := by
  exact
    packedTile32768 300585216 300650752 13 3347 17337 28 _ _ (1952123 / 100000) (976063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300650752 :
    ThetaLowerSegment 300650752 300683520 (240503641441 / 800) (6013239147833 / 20000) := by
  exact
    packedTile32768 300650752 300683520 12 1660 17339 28 _ _ (122009 / 6250) (1952147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300683520 :
    ThetaLowerSegment 300683520 300716288 (6013239147833 / 20000) (1503472694293 / 5000) := by
  exact
    packedTile32768 300683520 300716288 12 1669 17340 28 _ _ (390431 / 20000) (976079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300716288 :
    ThetaLowerSegment 300716288 300749056 (1503472694293 / 5000) (7518179476853 / 25000) := by
  exact
    packedTile32768 300716288 300749056 12 1672 17341 28 _ _ (976083 / 50000) (1952169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300749056 :
    ThetaLowerSegment 300749056 300781824 (7518179476853 / 25000) (3007606393879 / 10000) := by
  exact
    packedTile32768 300749056 300781824 12 1714 17342 28 _ _ (1952177 / 100000) (97609 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300781824 :
    ThetaLowerSegment 300781824 300814592 (3007606393879 / 10000) (15039678639973 / 50000) := by
  exact
    packedTile32768 300781824 300814592 12 1687 17343 28 _ _ (488047 / 25000) (1952191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300814592 :
    ThetaLowerSegment 300814592 300880128 (15039678639973 / 50000) (6017195437351 / 20000) := by
  exact
    packedTile32768 300814592 300880128 13 3391 17344 28 _ _ (1952199 / 100000) (976101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300880128 :
    ThetaLowerSegment 300880128 300945664 (6017195437351 / 20000) (7523144411489 / 25000) := by
  exact
    packedTile32768 300880128 300945664 13 3381 17345 28 _ _ (1952221 / 100000) (61007 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell300945664 :
    ThetaLowerSegment 300945664 301011200 (7523144411489 / 25000) (30099119612249 / 100000) := by
  exact
    packedTile32768 300945664 301011200 13 3351 17347 28 _ _ (1952243 / 100000) (976123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301011200 :
    ThetaLowerSegment 301011200 301076736 (30099119612249 / 100000) (30105591367409 / 100000) := by
  exact
    packedTile32768 301011200 301076736 13 3315 17349 28 _ _ (244033 / 12500) (1952267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301076736 :
    ThetaLowerSegment 301076736 301142272 (30105591367409 / 100000) (30112149096083 / 100000) := by
  exact
    packedTile32768 301076736 301142272 13 3359 17351 28 _ _ (976143 / 50000) (1952289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301142272 :
    ThetaLowerSegment 301142272 301207808 (30112149096083 / 100000) (6023733570499 / 20000) := by
  exact
    packedTile32768 301142272 301207808 13 3339 17353 28 _ _ (488077 / 25000) (1952311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301207808 :
    ThetaLowerSegment 301207808 301273344 (6023733570499 / 20000) (1205012699539 / 4000) := by
  exact
    packedTile32768 301207808 301273344 13 3406 17355 28 _ _ (195233 / 10000) (1952333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301273344 :
    ThetaLowerSegment 301273344 301338880 (1205012699539 / 4000) (6026387191673 / 20000) := by
  exact
    packedTile32768 301273344 301338880 13 3390 17357 28 _ _ (1952351 / 100000) (976177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301338880 :
    ThetaLowerSegment 301338880 301404416 (6026387191673 / 20000) (6027699186329 / 20000) := by
  exact
    packedTile32768 301338880 301404416 13 3360 17359 28 _ _ (1952373 / 100000) (244047 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301404416 :
    ThetaLowerSegment 301404416 301469952 (6027699186329 / 20000) (3014506964561 / 10000) := by
  exact
    packedTile32768 301404416 301469952 13 3367 17361 28 _ _ (390479 / 20000) (976199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301469952 :
    ThetaLowerSegment 301469952 301535488 (3014506964561 / 10000) (7537900608223 / 25000) := by
  exact
    packedTile32768 301469952 301535488 13 3346 17362 28 _ _ (1952417 / 100000) (97621 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301535488 :
    ThetaLowerSegment 301535488 301601024 (7537900608223 / 25000) (1884886872419 / 6250) := by
  exact
    packedTile32768 301535488 301601024 13 3374 17364 28 _ _ (976219 / 50000) (1952441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301601024 :
    ThetaLowerSegment 301601024 301666560 (1884886872419 / 6250) (942644783647 / 3125) := by
  exact
    packedTile32768 301601024 301666560 13 3300 17366 28 _ _ (97623 / 5000) (1952463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301666560 :
    ThetaLowerSegment 301666560 301732096 (942644783647 / 3125) (15085650401367 / 50000) := by
  exact
    packedTile32768 301666560 301732096 13 3415 17368 28 _ _ (976241 / 50000) (390497 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301732096 :
    ThetaLowerSegment 301732096 301797632 (15085650401367 / 50000) (15088868127959 / 50000) := by
  exact
    packedTile32768 301732096 301797632 13 3296 17370 28 _ _ (244063 / 12500) (1952507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301797632 :
    ThetaLowerSegment 301797632 301863168 (15088868127959 / 50000) (3773029770521 / 12500) := by
  exact
    packedTile32768 301797632 301863168 13 3330 17372 28 _ _ (78101 / 4000) (122033 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301863168 :
    ThetaLowerSegment 301863168 301928704 (3773029770521 / 12500) (30190843630669 / 100000) := by
  exact
    packedTile32768 301863168 301928704 13 3383 17374 28 _ _ (1952547 / 100000) (39051 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301928704 :
    ThetaLowerSegment 301928704 301994240 (30190843630669 / 100000) (15098726538367 / 50000) := by
  exact
    packedTile32768 301928704 301994240 13 3385 17376 28 _ _ (1952569 / 100000) (488143 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell301994240 :
    ThetaLowerSegment 301994240 302059776 (15098726538367 / 50000) (7550982454441 / 25000) := by
  exact
    packedTile32768 301994240 302059776 13 3317 17377 28 _ _ (195259 / 10000) (1952593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302059776 :
    ThetaLowerSegment 302059776 302125312 (7550982454441 / 25000) (944081187117 / 3125) := by
  exact
    packedTile32768 302059776 302125312 13 3415 17379 28 _ _ (488153 / 25000) (390523 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302125312 :
    ThetaLowerSegment 302125312 302190848 (944081187117 / 3125) (7554273112107 / 25000) := by
  exact
    packedTile32768 302125312 302190848 13 3326 17381 28 _ _ (976317 / 50000) (1952637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302190848 :
    ThetaLowerSegment 302190848 302256384 (7554273112107 / 25000) (30223596742233 / 100000) := by
  exact
    packedTile32768 302190848 302256384 13 3331 17383 28 _ _ (390531 / 20000) (976329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302256384 :
    ThetaLowerSegment 302256384 302321920 (30223596742233 / 100000) (7557531135361 / 25000) := by
  exact
    packedTile32768 302256384 302321920 13 3343 17385 28 _ _ (1952677 / 100000) (48817 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302321920 :
    ThetaLowerSegment 302321920 302387456 (7557531135361 / 25000) (6047344542273 / 20000) := by
  exact
    packedTile32768 302321920 302387456 13 3379 17387 28 _ _ (1952699 / 100000) (976351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302387456 :
    ThetaLowerSegment 302387456 302452992 (6047344542273 / 20000) (6048657160657 / 20000) := by
  exact
    packedTile32768 302387456 302452992 13 3361 17389 28 _ _ (24409 / 1250) (1952723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302452992 :
    ThetaLowerSegment 302452992 302518528 (6048657160657 / 20000) (30249802103339 / 100000) := by
  exact
    packedTile32768 302452992 302518528 13 3337 17391 28 _ _ (976371 / 50000) (390549 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302518528 :
    ThetaLowerSegment 302518528 302584064 (30249802103339 / 100000) (30256343862739 / 100000) := by
  exact
    packedTile32768 302518528 302584064 13 3350 17393 28 _ _ (488191 / 25000) (1952767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302584064 :
    ThetaLowerSegment 302584064 302649600 (30256343862739 / 100000) (15131471161627 / 50000) := by
  exact
    packedTile32768 302584064 302649600 13 3379 17394 28 _ _ (390557 / 20000) (488197 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302649600 :
    ThetaLowerSegment 302649600 302715136 (15131471161627 / 50000) (6053905828253 / 20000) := by
  exact
    packedTile32768 302649600 302715136 13 3373 17396 28 _ _ (1952807 / 100000) (195281 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302715136 :
    ThetaLowerSegment 302715136 302780672 (6053905828253 / 20000) (15138015054503 / 50000) := by
  exact
    packedTile32768 302715136 302780672 13 3329 17398 28 _ _ (1952829 / 100000) (61026 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302780672 :
    ThetaLowerSegment 302780672 302846208 (15138015054503 / 50000) (7570623998839 / 25000) := by
  exact
    packedTile32768 302780672 302846208 13 3311 17400 28 _ _ (39057 / 2000) (1952853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302846208 :
    ThetaLowerSegment 302846208 302911744 (7570623998839 / 25000) (7572244394381 / 25000) := by
  exact
    packedTile32768 302846208 302911744 13 3319 17402 28 _ _ (244109 / 12500) (15623 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302911744 :
    ThetaLowerSegment 302911744 302944512 (7572244394381 / 25000) (946634662959 / 3125) := by
  exact
    packedTile32768 302911744 302944512 12 1706 17404 28 _ _ (976447 / 50000) (1952897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell302944512 :
    ThetaLowerSegment 302944512 303010048 (946634662959 / 3125) (30298892457443 / 100000) := by
  exact
    packedTile32768 302944512 303010048 13 3371 17405 28 _ _ (390581 / 20000) (488227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303010048 :
    ThetaLowerSegment 303010048 303075584 (30298892457443 / 100000) (6061072109671 / 20000) := by
  exact
    packedTile32768 303010048 303075584 13 3312 17407 28 _ _ (976463 / 50000) (1952929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303075584 :
    ThetaLowerSegment 303075584 303108352 (6061072109671 / 20000) (30308682512903 / 100000) := by
  exact
    packedTile32768 303075584 303108352 12 1701 17409 28 _ _ (488237 / 25000) (1952951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303108352 :
    ThetaLowerSegment 303108352 303141120 (30308682512903 / 100000) (15155982718491 / 50000) := by
  exact
    packedTile32768 303108352 303141120 12 1681 17410 28 _ _ (1952959 / 100000) (976481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303141120 :
    ThetaLowerSegment 303141120 303206656 (15155982718491 / 50000) (30318494212349 / 100000) := by
  exact
    packedTile32768 303141120 303206656 13 3343 17410 28 _ _ (1952969 / 100000) (488243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303206656 :
    ThetaLowerSegment 303206656 303239424 (30318494212349 / 100000) (30321755707319 / 100000) := by
  exact
    packedTile32768 303206656 303239424 12 1670 17412 28 _ _ (1952991 / 100000) (976497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303239424 :
    ThetaLowerSegment 303239424 303272192 (30321755707319 / 100000) (30325134400779 / 100000) := by
  exact
    packedTile32768 303239424 303272192 12 1730 17413 28 _ _ (976501 / 50000) (390601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303272192 :
    ThetaLowerSegment 303272192 303337728 (30325134400779 / 100000) (1213266454809 / 4000) := by
  exact
    packedTile32768 303272192 303337728 13 3342 17414 28 _ _ (1953013 / 100000) (244127 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303337728 :
    ThetaLowerSegment 303337728 303403264 (1213266454809 / 4000) (30338211846261 / 100000) := by
  exact
    packedTile32768 303337728 303403264 13 3354 17416 28 _ _ (976517 / 50000) (1953037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303403264 :
    ThetaLowerSegment 303403264 303468800 (30338211846261 / 100000) (6068932948657 / 20000) := by
  exact
    packedTile32768 303403264 303468800 13 3304 17418 28 _ _ (61033 / 3125) (1953059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303468800 :
    ThetaLowerSegment 303468800 303501568 (6068932948657 / 20000) (30347910757259 / 100000) := by
  exact
    packedTile32768 303468800 303501568 12 1662 17420 28 _ _ (1953077 / 100000) (48827 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303501568 :
    ThetaLowerSegment 303501568 303534336 (30347910757259 / 100000) (30351266162443 / 100000) := by
  exact
    packedTile32768 303501568 303534336 12 1718 17421 28 _ _ (61034 / 3125) (1953091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303534336 :
    ThetaLowerSegment 303534336 303567104 (30351266162443 / 100000) (3794320130057 / 12500) := by
  exact
    packedTile32768 303534336 303567104 12 1687 17422 28 _ _ (1953099 / 100000) (976551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303567104 :
    ThetaLowerSegment 303567104 303632640 (3794320130057 / 12500) (7590260364859 / 25000) := by
  exact
    packedTile32768 303567104 303632640 13 3318 17423 28 _ _ (195311 / 10000) (1953113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303632640 :
    ThetaLowerSegment 303632640 303665408 (7590260364859 / 25000) (15182163312889 / 50000) := by
  exact
    packedTile32768 303632640 303665408 12 1682 17425 28 _ _ (1953131 / 100000) (976567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303665408 :
    ThetaLowerSegment 303665408 303698176 (15182163312889 / 50000) (1897977080949 / 6250) := by
  exact
    packedTile32768 303665408 303698176 12 1693 17425 28 _ _ (976571 / 50000) (390629 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303698176 :
    ThetaLowerSegment 303698176 303730944 (1897977080949 / 6250) (30370768105749 / 100000) := by
  exact
    packedTile32768 303698176 303730944 12 1605 17426 28 _ _ (1953153 / 100000) (488289 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303730944 :
    ThetaLowerSegment 303730944 303763712 (30370768105749 / 100000) (30374000592169 / 100000) := by
  exact
    packedTile32768 303730944 303763712 12 1655 17427 28 _ _ (488291 / 25000) (1953167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303763712 :
    ThetaLowerSegment 303763712 303796480 (30374000592169 / 100000) (30377242862669 / 100000) := by
  exact
    packedTile32768 303763712 303796480 12 1660 17428 28 _ _ (78127 / 4000) (976589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303796480 :
    ThetaLowerSegment 303796480 303829248 (30377242862669 / 100000) (7595118845961 / 25000) := by
  exact
    packedTile32768 303796480 303829248 12 1655 17429 28 _ _ (390637 / 20000) (488297 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303829248 :
    ThetaLowerSegment 303829248 303862016 (7595118845961 / 25000) (759593479359 / 2500) := by
  exact
    packedTile32768 303829248 303862016 12 1671 17430 28 _ _ (488299 / 25000) (1953199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303862016 :
    ThetaLowerSegment 303862016 303894784 (759593479359 / 2500) (30387077205123 / 100000) := by
  exact
    packedTile32768 303862016 303894784 12 1709 17431 28 _ _ (1953207 / 100000) (195321 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303894784 :
    ThetaLowerSegment 303894784 303927552 (30387077205123 / 100000) (30390341032401 / 100000) := by
  exact
    packedTile32768 303894784 303927552 12 1671 17432 28 _ _ (976609 / 50000) (1953221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303927552 :
    ThetaLowerSegment 303927552 303960320 (30390341032401 / 100000) (6078713943657 / 20000) := by
  exact
    packedTile32768 303927552 303960320 12 1653 17433 28 _ _ (488307 / 25000) (1953231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303960320 :
    ThetaLowerSegment 303960320 303993088 (6078713943657 / 20000) (15198416790327 / 50000) := by
  exact
    packedTile32768 303960320 303993088 12 1671 17434 28 _ _ (1953239 / 100000) (976621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell303993088 :
    ThetaLowerSegment 303993088 304025856 (15198416790327 / 50000) (15200045800827 / 50000) := by
  exact
    packedTile32768 303993088 304025856 12 1668 17435 28 _ _ (7813 / 400) (1953253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304025856 :
    ThetaLowerSegment 304025856 304058624 (15200045800827 / 50000) (15201651381369 / 50000) := by
  exact
    packedTile32768 304025856 304058624 12 1644 17436 28 _ _ (1953261 / 100000) (122079 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304058624 :
    ThetaLowerSegment 304058624 304091392 (15201651381369 / 50000) (15203296036393 / 50000) := by
  exact
    packedTile32768 304058624 304091392 12 1684 17437 28 _ _ (244159 / 12500) (78131 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304091392 :
    ThetaLowerSegment 304091392 304124160 (15203296036393 / 50000) (7602482557931 / 25000) := by
  exact
    packedTile32768 304091392 304124160 12 1709 17438 28 _ _ (976641 / 50000) (390657 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304124160 :
    ThetaLowerSegment 304124160 304156928 (7602482557931 / 25000) (30413252783117 / 100000) := by
  exact
    packedTile32768 304124160 304156928 12 1701 17439 28 _ _ (1953293 / 100000) (122081 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304156928 :
    ThetaLowerSegment 304156928 304189696 (30413252783117 / 100000) (30416428855421 / 100000) := by
  exact
    packedTile32768 304156928 304189696 12 1626 17440 28 _ _ (244163 / 12500) (1953307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304189696 :
    ThetaLowerSegment 304189696 304222464 (30416428855421 / 100000) (15209854235653 / 50000) := by
  exact
    packedTile32768 304189696 304222464 12 1679 17441 28 _ _ (390663 / 20000) (976659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304222464 :
    ThetaLowerSegment 304222464 304255232 (15209854235653 / 50000) (7605748490989 / 25000) := by
  exact
    packedTile32768 304222464 304255232 12 1682 17441 28 _ _ (78133 / 4000) (122083 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304255232 :
    ThetaLowerSegment 304255232 304288000 (7605748490989 / 25000) (7606577682121 / 25000) := by
  exact
    packedTile32768 304255232 304288000 12 1698 17442 28 _ _ (244167 / 12500) (1953339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304288000 :
    ThetaLowerSegment 304288000 304320768 (7606577682121 / 25000) (6085919642297 / 20000) := by
  exact
    packedTile32768 304288000 304320768 12 1683 17443 28 _ _ (1953347 / 100000) (39067 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304320768 :
    ThetaLowerSegment 304320768 304353536 (6085919642297 / 20000) (30432897433147 / 100000) := by
  exact
    packedTile32768 304320768 304353536 12 1689 17444 28 _ _ (976679 / 50000) (1953361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304353536 :
    ThetaLowerSegment 304353536 304386304 (30432897433147 / 100000) (30436272854779 / 100000) := by
  exact
    packedTile32768 304353536 304386304 12 1728 17445 28 _ _ (1953369 / 100000) (488343 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304386304 :
    ThetaLowerSegment 304386304 304419072 (30436272854779 / 100000) (3804947979023 / 12500) := by
  exact
    packedTile32768 304386304 304419072 12 1695 17446 28 _ _ (1953379 / 100000) (976691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304419072 :
    ThetaLowerSegment 304419072 304451840 (3804947979023 / 12500) (951339303557 / 3125) := by
  exact
    packedTile32768 304419072 304451840 12 1676 17447 28 _ _ (195339 / 10000) (1953393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304451840 :
    ThetaLowerSegment 304451840 304484608 (951339303557 / 3125) (15223063853549 / 50000) := by
  exact
    packedTile32768 304451840 304484608 12 1674 17448 28 _ _ (1953401 / 100000) (488351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304484608 :
    ThetaLowerSegment 304484608 304517376 (15223063853549 / 50000) (15224717416807 / 50000) := by
  exact
    packedTile32768 304484608 304517376 12 1693 17449 28 _ _ (488353 / 25000) (390683 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304517376 :
    ThetaLowerSegment 304517376 304550144 (15224717416807 / 50000) (15226354384443 / 50000) := by
  exact
    packedTile32768 304517376 304550144 12 1676 17450 28 _ _ (976711 / 50000) (78137 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304550144 :
    ThetaLowerSegment 304550144 304582912 (15226354384443 / 50000) (30455988582893 / 100000) := by
  exact
    packedTile32768 304550144 304582912 12 1679 17451 28 _ _ (1953433 / 100000) (488359 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304582912 :
    ThetaLowerSegment 304582912 304615680 (30455988582893 / 100000) (30459311391137 / 100000) := by
  exact
    packedTile32768 304582912 304615680 12 1701 17452 28 _ _ (488361 / 25000) (1953447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304615680 :
    ThetaLowerSegment 304615680 304648448 (30459311391137 / 100000) (15231315155591 / 50000) := by
  exact
    packedTile32768 304615680 304648448 12 1699 17453 28 _ _ (390691 / 20000) (976729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304648448 :
    ThetaLowerSegment 304648448 304681216 (15231315155591 / 50000) (15232963880051 / 50000) := by
  exact
    packedTile32768 304648448 304681216 12 1688 17454 28 _ _ (390693 / 20000) (488367 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304681216 :
    ThetaLowerSegment 304681216 304713984 (15232963880051 / 50000) (15234564753633 / 50000) := by
  exact
    packedTile32768 304681216 304713984 12 1639 17455 28 _ _ (488369 / 25000) (1953479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304713984 :
    ThetaLowerSegment 304713984 304746752 (15234564753633 / 50000) (30472499272341 / 100000) := by
  exact
    packedTile32768 304713984 304746752 12 1725 17456 28 _ _ (1953487 / 100000) (195349 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304746752 :
    ThetaLowerSegment 304746752 304779520 (30472499272341 / 100000) (30475820218941 / 100000) := by
  exact
    packedTile32768 304746752 304779520 12 1700 17456 28 _ _ (976749 / 50000) (1953501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304779520 :
    ThetaLowerSegment 304779520 304845056 (30475820218941 / 100000) (6096460391697 / 20000) := by
  exact
    packedTile32768 304779520 304845056 13 3318 17457 28 _ _ (488377 / 25000) (1953511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304845056 :
    ThetaLowerSegment 304845056 304877824 (6096460391697 / 20000) (1219423589979 / 4000) := by
  exact
    packedTile32768 304845056 304877824 12 1683 17459 28 _ _ (195353 / 10000) (1953533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304877824 :
    ThetaLowerSegment 304877824 304910592 (1219423589979 / 4000) (30488922490421 / 100000) := by
  exact
    packedTile32768 304877824 304910592 12 1706 17460 28 _ _ (1953541 / 100000) (244193 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304910592 :
    ThetaLowerSegment 304910592 304976128 (30488922490421 / 100000) (3049544539721 / 10000) := by
  exact
    packedTile32768 304910592 304976128 13 3339 17461 28 _ _ (1953551 / 100000) (976777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell304976128 :
    ThetaLowerSegment 304976128 305041664 (3049544539721 / 10000) (30502109034713 / 100000) := by
  exact
    packedTile32768 304976128 305041664 13 3411 17463 28 _ _ (1953573 / 100000) (244197 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305041664 :
    ThetaLowerSegment 305041664 305107200 (30502109034713 / 100000) (30508690692899 / 100000) := by
  exact
    packedTile32768 305041664 305107200 13 3369 17465 28 _ _ (976797 / 50000) (1953597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305107200 :
    ThetaLowerSegment 305107200 305172736 (30508690692899 / 100000) (30515204048643 / 100000) := by
  exact
    packedTile32768 305107200 305172736 13 3334 17467 28 _ _ (122101 / 6250) (1953619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305172736 :
    ThetaLowerSegment 305172736 305238272 (30515204048643 / 100000) (30521647143469 / 100000) := by
  exact
    packedTile32768 305172736 305238272 13 3298 17469 28 _ _ (1953637 / 100000) (48841 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305238272 :
    ThetaLowerSegment 305238272 305303808 (30521647143469 / 100000) (7632012321003 / 25000) := by
  exact
    packedTile32768 305238272 305303808 13 3277 17471 28 _ _ (1953659 / 100000) (976831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305303808 :
    ThetaLowerSegment 305303808 305336576 (7632012321003 / 25000) (7632847519203 / 25000) := by
  exact
    packedTile32768 305303808 305336576 12 1710 17472 28 _ _ (24421 / 1250) (1953683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305336576 :
    ThetaLowerSegment 305336576 305369344 (7632847519203 / 25000) (30534670324001 / 100000) := by
  exact
    packedTile32768 305336576 305369344 12 1679 17473 28 _ _ (1953691 / 100000) (976847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305369344 :
    ThetaLowerSegment 305369344 305402112 (30534670324001 / 100000) (6107595197557 / 20000) := by
  exact
    packedTile32768 305369344 305402112 12 1692 17474 28 _ _ (976851 / 50000) (390741 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305402112 :
    ThetaLowerSegment 305402112 305434880 (6107595197557 / 20000) (6108251644789 / 20000) := by
  exact
    packedTile32768 305402112 305434880 12 1680 17475 28 _ _ (122107 / 6250) (390743 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305434880 :
    ThetaLowerSegment 305434880 305467648 (6108251644789 / 20000) (38180687809 / 125) := by
  exact
    packedTile32768 305434880 305467648 12 1685 17476 28 _ _ (1953723 / 100000) (976863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305467648 :
    ThetaLowerSegment 305467648 305500416 (38180687809 / 125) (15273897699687 / 50000) := by
  exact
    packedTile32768 305467648 305500416 12 1661 17477 28 _ _ (976867 / 50000) (1953737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305500416 :
    ThetaLowerSegment 305500416 305533184 (15273897699687 / 50000) (30551099182169 / 100000) := by
  exact
    packedTile32768 305500416 305533184 12 1691 17478 28 _ _ (390749 / 20000) (488437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305533184 :
    ThetaLowerSegment 305533184 305565952 (30551099182169 / 100000) (7638603676101 / 25000) := by
  exact
    packedTile32768 305533184 305565952 12 1697 17479 28 _ _ (390751 / 20000) (976879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305565952 :
    ThetaLowerSegment 305565952 305631488 (7638603676101 / 25000) (305609715431 / 1000) := by
  exact
    packedTile32768 305565952 305631488 13 3356 17480 28 _ _ (976883 / 50000) (1953769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305631488 :
    ThetaLowerSegment 305631488 305697024 (305609715431 / 1000) (7641892859741 / 25000) := by
  exact
    packedTile32768 305631488 305697024 13 3378 17482 28 _ _ (488447 / 25000) (1953791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305697024 :
    ThetaLowerSegment 305697024 305762560 (7641892859741 / 25000) (6114822949061 / 20000) := by
  exact
    packedTile32768 305697024 305762560 13 3349 17484 28 _ _ (1953809 / 100000) (488453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305762560 :
    ThetaLowerSegment 305762560 305828096 (6114822949061 / 20000) (6116159368781 / 20000) := by
  exact
    packedTile32768 305762560 305828096 13 3420 17486 28 _ _ (195383 / 10000) (1953833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305828096 :
    ThetaLowerSegment 305828096 305893632 (6116159368781 / 20000) (30587211340021 / 100000) := by
  exact
    packedTile32768 305828096 305893632 13 3283 17487 28 _ _ (488463 / 25000) (390771 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305893632 :
    ThetaLowerSegment 305893632 305959168 (30587211340021 / 100000) (15296869614857 / 50000) := by
  exact
    packedTile32768 305893632 305959168 13 3341 17489 28 _ _ (1953873 / 100000) (488469 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell305959168 :
    ThetaLowerSegment 305959168 306024704 (15296869614857 / 50000) (15300199051937 / 50000) := by
  exact
    packedTile32768 305959168 306024704 13 3408 17491 28 _ _ (390779 / 20000) (976949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306024704 :
    ThetaLowerSegment 306024704 306090240 (15300199051937 / 50000) (15303559787457 / 50000) := by
  exact
    packedTile32768 306024704 306090240 13 3440 17493 28 _ _ (488479 / 25000) (1953919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306090240 :
    ThetaLowerSegment 306090240 306155776 (15303559787457 / 50000) (612270257201 / 2000) := by
  exact
    packedTile32768 306090240 306155776 13 3272 17495 28 _ _ (976969 / 50000) (1953941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306155776 :
    ThetaLowerSegment 306155776 306221312 (612270257201 / 2000) (30620041037069 / 100000) := by
  exact
    packedTile32768 306155776 306221312 13 3341 17497 28 _ _ (1953959 / 100000) (976981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306221312 :
    ThetaLowerSegment 306221312 306286848 (30620041037069 / 100000) (30626606409869 / 100000) := by
  exact
    packedTile32768 306221312 306286848 13 3360 17499 28 _ _ (97699 / 5000) (1953983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306286848 :
    ThetaLowerSegment 306286848 306352384 (30626606409869 / 100000) (30633316452737 / 100000) := by
  exact
    packedTile32768 306286848 306352384 13 3434 17501 28 _ _ (977001 / 50000) (390801 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306352384 :
    ThetaLowerSegment 306352384 306417920 (30633316452737 / 100000) (30639827257373 / 100000) := by
  exact
    packedTile32768 306352384 306417920 13 3332 17502 28 _ _ (1954023 / 100000) (977013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306417920 :
    ThetaLowerSegment 306417920 306483456 (30639827257373 / 100000) (7661591861497 / 25000) := by
  exact
    packedTile32768 306417920 306483456 13 3347 17504 28 _ _ (390809 / 20000) (61064 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306483456 :
    ThetaLowerSegment 306483456 306548992 (7661591861497 / 25000) (3065286862357 / 10000) := by
  exact
    packedTile32768 306483456 306548992 13 3327 17506 28 _ _ (977033 / 50000) (1954069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306548992 :
    ThetaLowerSegment 306548992 306614528 (3065286862357 / 10000) (3832420012573 / 12500) := by
  exact
    packedTile32768 306548992 306614528 13 3322 17508 28 _ _ (1954087 / 100000) (195409 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306614528 :
    ThetaLowerSegment 306614528 306680064 (3832420012573 / 12500) (30665841880137 / 100000) := by
  exact
    packedTile32768 306614528 306680064 13 3317 17510 28 _ _ (1954109 / 100000) (61066 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306680064 :
    ThetaLowerSegment 306680064 306745600 (30665841880137 / 100000) (30672435114757 / 100000) := by
  exact
    packedTile32768 306680064 306745600 13 3374 17512 28 _ _ (195413 / 10000) (1954133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306745600 :
    ThetaLowerSegment 306745600 306811136 (30672435114757 / 100000) (766973707501 / 2500) := by
  exact
    packedTile32768 306745600 306811136 13 3333 17514 28 _ _ (1954151 / 100000) (977077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306811136 :
    ThetaLowerSegment 306811136 306876672 (766973707501 / 2500) (15342802106639 / 50000) := by
  exact
    packedTile32768 306811136 306876672 13 3406 17516 28 _ _ (1954173 / 100000) (61068 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306876672 :
    ThetaLowerSegment 306876672 306942208 (15342802106639 / 50000) (3836512738541 / 12500) := by
  exact
    packedTile32768 306876672 306942208 13 3325 17517 28 _ _ (977097 / 50000) (1954197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell306942208 :
    ThetaLowerSegment 306942208 307007744 (3836512738541 / 12500) (959334293354 / 3125) := by
  exact
    packedTile32768 306942208 307007744 13 3375 17519 28 _ _ (244277 / 12500) (1954219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307007744 :
    ThetaLowerSegment 307007744 307073280 (959334293354 / 3125) (7676310043201 / 25000) := by
  exact
    packedTile32768 307007744 307073280 13 3348 17521 28 _ _ (1954237 / 100000) (12214 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307073280 :
    ThetaLowerSegment 307073280 307138816 (7676310043201 / 25000) (7677955528437 / 25000) := by
  exact
    packedTile32768 307073280 307138816 13 3368 17523 28 _ _ (977129 / 50000) (1954261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307138816 :
    ThetaLowerSegment 307138816 307204352 (7677955528437 / 25000) (7679619109287 / 25000) := by
  exact
    packedTile32768 307138816 307204352 13 3405 17525 28 _ _ (48857 / 2500) (1954283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307204352 :
    ThetaLowerSegment 307204352 307269888 (7679619109287 / 25000) (30724982305177 / 100000) := by
  exact
    packedTile32768 307204352 307269888 13 3329 17527 28 _ _ (1954301 / 100000) (61072 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307269888 :
    ThetaLowerSegment 307269888 307335424 (30724982305177 / 100000) (30731578141927 / 100000) := by
  exact
    packedTile32768 307269888 307335424 13 3375 17529 28 _ _ (977161 / 50000) (78173 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307335424 :
    ThetaLowerSegment 307335424 307400960 (30731578141927 / 100000) (6147627774947 / 20000) := by
  exact
    packedTile32768 307335424 307400960 13 3357 17530 28 _ _ (244293 / 12500) (1954347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307400960 :
    ThetaLowerSegment 307400960 307466496 (6147627774947 / 20000) (3074469576931 / 10000) := by
  exact
    packedTile32768 307400960 307466496 13 3355 17532 28 _ _ (390873 / 20000) (61074 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307466496 :
    ThetaLowerSegment 307466496 307532032 (3074469576931 / 10000) (15375648842609 / 50000) := by
  exact
    packedTile32768 307466496 307532032 13 3378 17534 28 _ _ (977193 / 50000) (1954389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307532032 :
    ThetaLowerSegment 307532032 307597568 (15375648842609 / 50000) (15378885340601 / 50000) := by
  exact
    packedTile32768 307532032 307597568 13 3312 17536 28 _ _ (1954407 / 100000) (195441 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307597568 :
    ThetaLowerSegment 307597568 307663104 (15378885340601 / 50000) (6152846795581 / 20000) := by
  exact
    packedTile32768 307597568 307663104 13 3307 17538 28 _ _ (1954429 / 100000) (61076 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307663104 :
    ThetaLowerSegment 307663104 307728640 (6152846795581 / 20000) (6154163313101 / 20000) := by
  exact
    packedTile32768 307663104 307728640 13 3368 17540 28 _ _ (39089 / 2000) (1954453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307728640 :
    ThetaLowerSegment 307728640 307794176 (6154163313101 / 20000) (30777352316529 / 100000) := by
  exact
    packedTile32768 307728640 307794176 13 3344 17542 28 _ _ (1954471 / 100000) (977237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307794176 :
    ThetaLowerSegment 307794176 307859712 (30777352316529 / 100000) (3078387445967 / 10000) := by
  exact
    packedTile32768 307794176 307859712 13 3337 17544 28 _ _ (1954493 / 100000) (61078 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307859712 :
    ThetaLowerSegment 307859712 307925248 (3078387445967 / 10000) (615807268923 / 2000) := by
  exact
    packedTile32768 307859712 307925248 13 3320 17545 28 _ _ (977257 / 50000) (1954517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307925248 :
    ThetaLowerSegment 307925248 307990784 (615807268923 / 2000) (6159399036681 / 20000) := by
  exact
    packedTile32768 307925248 307990784 13 3393 17547 28 _ _ (390907 / 20000) (977269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell307990784 :
    ThetaLowerSegment 307990784 308056320 (6159399036681 / 20000) (30803754041511 / 100000) := by
  exact
    packedTile32768 307990784 308056320 13 3458 17549 28 _ _ (1954557 / 100000) (12216 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308056320 :
    ThetaLowerSegment 308056320 308121856 (30803754041511 / 100000) (30810315559857 / 100000) := by
  exact
    packedTile32768 308056320 308121856 13 3357 17551 28 _ _ (977289 / 50000) (1954581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308121856 :
    ThetaLowerSegment 308121856 308187392 (30810315559857 / 100000) (30816894740091 / 100000) := by
  exact
    packedTile32768 308121856 308187392 13 3366 17553 28 _ _ (1954599 / 100000) (977301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308187392 :
    ThetaLowerSegment 308187392 308252928 (30816894740091 / 100000) (30823550221191 / 100000) := by
  exact
    packedTile32768 308187392 308252928 13 3405 17555 28 _ _ (97731 / 5000) (1954623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308252928 :
    ThetaLowerSegment 308252928 308318464 (30823550221191 / 100000) (30830119772953 / 100000) := by
  exact
    packedTile32768 308252928 308318464 13 3361 17557 28 _ _ (977321 / 50000) (390929 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308318464 :
    ThetaLowerSegment 308318464 308384000 (30830119772953 / 100000) (30836644438047 / 100000) := by
  exact
    packedTile32768 308318464 308384000 13 3338 17558 28 _ _ (1954663 / 100000) (977333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308384000 :
    ThetaLowerSegment 308384000 308449536 (30836644438047 / 100000) (30843259088703 / 100000) := by
  exact
    packedTile32768 308384000 308449536 13 3384 17560 28 _ _ (488671 / 25000) (1954687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308449536 :
    ThetaLowerSegment 308449536 308515072 (30843259088703 / 100000) (30849815169273 / 100000) := by
  exact
    packedTile32768 308449536 308515072 13 3354 17562 28 _ _ (390941 / 20000) (488677 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308515072 :
    ThetaLowerSegment 308515072 308580608 (30849815169273 / 100000) (30856422146533 / 100000) := by
  exact
    packedTile32768 308515072 308580608 13 3380 17564 28 _ _ (1954727 / 100000) (195473 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308580608 :
    ThetaLowerSegment 308580608 308646144 (30856422146533 / 100000) (30862999873553 / 100000) := by
  exact
    packedTile32768 308580608 308646144 13 3365 17566 28 _ _ (488687 / 25000) (1954751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308646144 :
    ThetaLowerSegment 308646144 308711680 (30862999873553 / 100000) (385869183329 / 1250) := by
  exact
    packedTile32768 308646144 308711680 13 3343 17568 28 _ _ (1954769 / 100000) (488693 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308711680 :
    ThetaLowerSegment 308711680 308777216 (385869183329 / 1250) (3087617117837 / 10000) := by
  exact
    packedTile32768 308711680 308777216 13 3395 17570 28 _ _ (195479 / 10000) (1954793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308777216 :
    ThetaLowerSegment 308777216 308842752 (3087617117837 / 10000) (3088264160609 / 10000) := by
  exact
    packedTile32768 308777216 308842752 13 3310 17572 28 _ _ (488703 / 25000) (390963 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308842752 :
    ThetaLowerSegment 308842752 308908288 (3088264160609 / 10000) (15444632290147 / 50000) := by
  exact
    packedTile32768 308842752 308908288 13 3388 17573 28 _ _ (1954833 / 100000) (488709 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308908288 :
    ThetaLowerSegment 308908288 308973824 (15444632290147 / 50000) (15447887122057 / 50000) := by
  exact
    packedTile32768 308908288 308973824 13 3330 17575 28 _ _ (977427 / 50000) (1954857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell308973824 :
    ThetaLowerSegment 308973824 309039360 (15447887122057 / 50000) (15451179131557 / 50000) := by
  exact
    packedTile32768 308973824 309039360 13 3368 17577 28 _ _ (15639 / 800) (977439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309039360 :
    ThetaLowerSegment 309039360 309104896 (15451179131557 / 50000) (15454463356837 / 50000) := by
  exact
    packedTile32768 309039360 309104896 13 3360 17579 28 _ _ (122181 / 6250) (1954899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309104896 :
    ThetaLowerSegment 309104896 309170432 (15454463356837 / 50000) (15457726114979 / 50000) := by
  exact
    packedTile32768 309104896 309170432 13 3338 17581 28 _ _ (977459 / 50000) (1954921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309170432 :
    ThetaLowerSegment 309170432 309235968 (15457726114979 / 50000) (6184389698451 / 20000) := by
  exact
    packedTile32768 309170432 309235968 13 3323 17583 28 _ _ (1954939 / 100000) (977471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309235968 :
    ThetaLowerSegment 309235968 309301504 (6184389698451 / 20000) (6185705777523 / 20000) := by
  exact
    packedTile32768 309235968 309301504 13 3366 17585 28 _ _ (24437 / 1250) (1954963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309301504 :
    ThetaLowerSegment 309301504 309367040 (6185705777523 / 20000) (15467547834397 / 50000) := by
  exact
    packedTile32768 309301504 309367040 13 3359 17586 28 _ _ (1954981 / 100000) (244373 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309367040 :
    ThetaLowerSegment 309367040 309432576 (15467547834397 / 50000) (15470832237757 / 50000) := by
  exact
    packedTile32768 309367040 309432576 13 3360 17588 28 _ _ (977501 / 50000) (391001 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309432576 :
    ThetaLowerSegment 309432576 309498112 (15470832237757 / 50000) (15474119610613 / 50000) := by
  exact
    packedTile32768 309432576 309498112 13 3363 17590 28 _ _ (122189 / 6250) (1955027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309498112 :
    ThetaLowerSegment 309498112 309563648 (15474119610613 / 50000) (15477392355943 / 50000) := by
  exact
    packedTile32768 309498112 309563648 13 3348 17592 28 _ _ (391009 / 20000) (244381 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309563648 :
    ThetaLowerSegment 309563648 309629184 (15477392355943 / 50000) (7740316438919 / 25000) := by
  exact
    packedTile32768 309563648 309629184 13 3315 17594 28 _ _ (977533 / 50000) (1955069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309629184 :
    ThetaLowerSegment 309629184 309694720 (7740316438919 / 25000) (30967891545519 / 100000) := by
  exact
    packedTile32768 309629184 309694720 13 3389 17596 28 _ _ (1955087 / 100000) (195509 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309694720 :
    ThetaLowerSegment 309694720 309760256 (30967891545519 / 100000) (30974388369403 / 100000) := by
  exact
    packedTile32768 309694720 309760256 13 3323 17598 28 _ _ (488777 / 25000) (1955111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309760256 :
    ThetaLowerSegment 309760256 309825792 (30974388369403 / 100000) (30981039718261 / 100000) := by
  exact
    packedTile32768 309760256 309825792 13 3402 17600 28 _ _ (1955129 / 100000) (488783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309825792 :
    ThetaLowerSegment 309825792 309891328 (30981039718261 / 100000) (30987593384413 / 100000) := by
  exact
    packedTile32768 309825792 309891328 13 3352 17601 28 _ _ (1955151 / 100000) (977577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309891328 :
    ThetaLowerSegment 309891328 309956864 (30987593384413 / 100000) (30994072824421 / 100000) := by
  exact
    packedTile32768 309891328 309956864 13 3314 17603 28 _ _ (488793 / 25000) (78207 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell309956864 :
    ThetaLowerSegment 309956864 310022400 (30994072824421 / 100000) (15500329934819 / 50000) := by
  exact
    packedTile32768 309956864 310022400 13 3369 17605 28 _ _ (1955193 / 100000) (488799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310022400 :
    ThetaLowerSegment 310022400 310087936 (15500329934819 / 50000) (968977568108 / 3125) := by
  exact
    packedTile32768 310022400 310087936 13 3387 17607 28 _ _ (977607 / 50000) (1955217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310087936 :
    ThetaLowerSegment 310087936 310153472 (968977568108 / 3125) (15506877003653 / 50000) := by
  exact
    packedTile32768 310087936 310153472 13 3310 17609 28 _ _ (391047 / 20000) (977619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310153472 :
    ThetaLowerSegment 310153472 310219008 (15506877003653 / 50000) (15510147169313 / 50000) := by
  exact
    packedTile32768 310153472 310219008 13 3345 17611 28 _ _ (244407 / 12500) (1955259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310219008 :
    ThetaLowerSegment 310219008 310284544 (15510147169313 / 50000) (15513447676889 / 50000) := by
  exact
    packedTile32768 310219008 310284544 13 3376 17613 28 _ _ (1955277 / 100000) (24441 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310284544 :
    ThetaLowerSegment 310284544 310350080 (15513447676889 / 50000) (31033463203119 / 100000) := by
  exact
    packedTile32768 310284544 310350080 13 3359 17614 28 _ _ (1955299 / 100000) (977651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310350080 :
    ThetaLowerSegment 310350080 310415616 (31033463203119 / 100000) (31039982239999 / 100000) := by
  exact
    packedTile32768 310350080 310415616 13 3334 17616 28 _ _ (48883 / 2500) (1955323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310415616 :
    ThetaLowerSegment 310415616 310481152 (31039982239999 / 100000) (31046501346893 / 100000) := by
  exact
    packedTile32768 310415616 310481152 13 3334 17618 28 _ _ (1955341 / 100000) (122209 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310481152 :
    ThetaLowerSegment 310481152 310546688 (31046501346893 / 100000) (31052893425271 / 100000) := by
  exact
    packedTile32768 310481152 310546688 13 3269 17620 28 _ _ (977681 / 50000) (391073 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310546688 :
    ThetaLowerSegment 310546688 310612224 (31052893425271 / 100000) (15529732733767 / 50000) := by
  exact
    packedTile32768 310546688 310612224 13 3361 17622 28 _ _ (1955383 / 100000) (977693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310612224 :
    ThetaLowerSegment 310612224 310677760 (15529732733767 / 50000) (15533005102361 / 50000) := by
  exact
    packedTile32768 310612224 310677760 13 3347 17624 28 _ _ (488851 / 25000) (1955407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310677760 :
    ThetaLowerSegment 310677760 310743296 (15533005102361 / 50000) (31072547190497 / 100000) := by
  exact
    packedTile32768 310677760 310743296 13 3343 17626 28 _ _ (78217 / 4000) (488857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310743296 :
    ThetaLowerSegment 310743296 310808832 (31072547190497 / 100000) (31079109667273 / 100000) := by
  exact
    packedTile32768 310743296 310808832 13 3356 17627 28 _ _ (977723 / 50000) (1955449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310808832 :
    ThetaLowerSegment 310808832 310874368 (31079109667273 / 100000) (31085723056667 / 100000) := by
  exact
    packedTile32768 310808832 310874368 13 3382 17629 28 _ _ (1955467 / 100000) (195547 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310874368 :
    ThetaLowerSegment 310874368 310939904 (31085723056667 / 100000) (6218455179391 / 20000) := by
  exact
    packedTile32768 310874368 310939904 13 3351 17631 28 _ _ (61109 / 3125) (1955491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell310939904 :
    ThetaLowerSegment 310939904 311005440 (6218455179391 / 20000) (49758254379 / 160) := by
  exact
    packedTile32768 310939904 311005440 13 3392 17633 28 _ _ (195551 / 10000) (1955513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311005440 :
    ThetaLowerSegment 311005440 311070976 (49758254379 / 160) (31105467837849 / 100000) := by
  exact
    packedTile32768 311005440 311070976 13 3354 17635 28 _ _ (1955531 / 100000) (977767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311070976 :
    ThetaLowerSegment 311070976 311136512 (31105467837849 / 100000) (31111997425977 / 100000) := by
  exact
    packedTile32768 311070976 311136512 13 3339 17637 28 _ _ (61111 / 3125) (391111 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311136512 :
    ThetaLowerSegment 311136512 311202048 (31111997425977 / 100000) (1944905987191 / 6250) := by
  exact
    packedTile32768 311136512 311202048 13 3323 17639 28 _ _ (1955573 / 100000) (244447 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311202048 :
    ThetaLowerSegment 311202048 311267584 (1944905987191 / 6250) (1945306883961 / 6250) := by
  exact
    packedTile32768 311202048 311267584 13 3280 17640 28 _ _ (977797 / 50000) (1955597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311267584 :
    ThetaLowerSegment 311267584 311333120 (1945306883961 / 6250) (15565722904353 / 50000) := by
  exact
    packedTile32768 311267584 311333120 13 3342 17642 28 _ _ (391123 / 20000) (977809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311333120 :
    ThetaLowerSegment 311333120 311398656 (15565722904353 / 50000) (15568988816473 / 50000) := by
  exact
    packedTile32768 311333120 311398656 13 3340 17644 28 _ _ (488909 / 25000) (1955639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311398656 :
    ThetaLowerSegment 311398656 311464192 (15568988816473 / 50000) (31144617088461 / 100000) := by
  exact
    packedTile32768 311398656 311464192 13 3395 17646 28 _ _ (1955657 / 100000) (97783 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311464192 :
    ThetaLowerSegment 311464192 311529728 (31144617088461 / 100000) (31151129496201 / 100000) := by
  exact
    packedTile32768 311464192 311529728 13 3330 17648 28 _ _ (977839 / 50000) (1955681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311529728 :
    ThetaLowerSegment 311529728 311595264 (31151129496201 / 100000) (31157591125697 / 100000) := by
  exact
    packedTile32768 311529728 311595264 13 3304 17650 28 _ _ (1955699 / 100000) (977851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311595264 :
    ThetaLowerSegment 311595264 311660800 (31157591125697 / 100000) (31164089983257 / 100000) := by
  exact
    packedTile32768 311595264 311660800 13 3323 17652 28 _ _ (48893 / 2500) (1955723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311660800 :
    ThetaLowerSegment 311660800 311726336 (31164089983257 / 100000) (389633339253 / 1250) := by
  exact
    packedTile32768 311660800 311726336 13 3363 17653 28 _ _ (1955741 / 100000) (61117 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311726336 :
    ThetaLowerSegment 311726336 311791872 (389633339253 / 1250) (3897153834689 / 12500) := by
  exact
    packedTile32768 311726336 311791872 13 3356 17655 28 _ _ (977881 / 50000) (391153 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311791872 :
    ThetaLowerSegment 311791872 311857408 (3897153834689 / 12500) (15591875629017 / 50000) := by
  exact
    packedTile32768 311791872 311857408 13 3334 17657 28 _ _ (1955783 / 100000) (977893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311857408 :
    ThetaLowerSegment 311857408 311922944 (15591875629017 / 50000) (15595178004071 / 50000) := by
  exact
    packedTile32768 311857408 311922944 13 3377 17659 28 _ _ (488951 / 25000) (1955807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311922944 :
    ThetaLowerSegment 311922944 311988480 (15595178004071 / 50000) (15598475525021 / 50000) := by
  exact
    packedTile32768 311922944 311988480 13 3372 17661 28 _ _ (78233 / 4000) (488957 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell311988480 :
    ThetaLowerSegment 311988480 312054016 (15598475525021 / 50000) (15601771125531 / 50000) := by
  exact
    packedTile32768 311988480 312054016 13 3370 17663 28 _ _ (977923 / 50000) (1955849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312054016 :
    ThetaLowerSegment 312054016 312119552 (15601771125531 / 50000) (1248402915639 / 4000) := by
  exact
    packedTile32768 312054016 312119552 13 3339 17665 28 _ _ (1955867 / 100000) (195587 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312119552 :
    ThetaLowerSegment 312119552 312185088 (1248402915639 / 4000) (31216699439519 / 100000) := by
  exact
    packedTile32768 312119552 312185088 13 3388 17666 28 _ _ (122243 / 6250) (1955891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312185088 :
    ThetaLowerSegment 312185088 312250624 (31216699439519 / 100000) (15611626845289 / 50000) := by
  exact
    packedTile32768 312185088 312250624 13 3351 17668 28 _ _ (1955909 / 100000) (244489 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312250624 :
    ThetaLowerSegment 312250624 312316160 (15611626845289 / 50000) (3903718177781 / 12500) := by
  exact
    packedTile32768 312250624 312316160 13 3319 17670 28 _ _ (195593 / 10000) (1955933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312316160 :
    ThetaLowerSegment 312316160 312381696 (3903718177781 / 12500) (6247281869461 / 20000) := by
  exact
    packedTile32768 312316160 312381696 13 3407 17672 28 _ _ (1955951 / 100000) (977977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312381696 :
    ThetaLowerSegment 312381696 312447232 (6247281869461 / 20000) (31243063564049 / 100000) := by
  exact
    packedTile32768 312381696 312447232 13 3402 17674 28 _ _ (488993 / 25000) (78239 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312447232 :
    ThetaLowerSegment 312447232 312512768 (31243063564049 / 100000) (6249904450587 / 20000) := by
  exact
    packedTile32768 312447232 312512768 13 3302 17676 28 _ _ (1955993 / 100000) (488999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312512768 :
    ThetaLowerSegment 312512768 312578304 (6249904450587 / 20000) (31256092503961 / 100000) := by
  exact
    packedTile32768 312512768 312578304 13 3359 17678 28 _ _ (978007 / 50000) (1956017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312578304 :
    ThetaLowerSegment 312578304 312643840 (31256092503961 / 100000) (1953916182091 / 6250) := by
  exact
    packedTile32768 312578304 312643840 13 3357 17679 28 _ _ (391207 / 20000) (978019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312643840 :
    ThetaLowerSegment 312643840 312709376 (1953916182091 / 6250) (3908659531363 / 12500) := by
  exact
    packedTile32768 312643840 312709376 13 3383 17681 28 _ _ (244507 / 12500) (1956059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312709376 :
    ThetaLowerSegment 312709376 312774912 (3908659531363 / 12500) (31275780206929 / 100000) := by
  exact
    packedTile32768 312709376 312774912 13 3325 17683 28 _ _ (1956077 / 100000) (24451 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312774912 :
    ThetaLowerSegment 312774912 312840448 (31275780206929 / 100000) (31282299881563 / 100000) := by
  exact
    packedTile32768 312774912 312840448 13 3333 17685 28 _ _ (978049 / 50000) (1956101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312840448 :
    ThetaLowerSegment 312840448 312905984 (31282299881563 / 100000) (7822205884607 / 25000) := by
  exact
    packedTile32768 312840448 312905984 13 3335 17687 28 _ _ (1956119 / 100000) (978061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312905984 :
    ThetaLowerSegment 312905984 312971520 (7822205884607 / 25000) (7823869581677 / 25000) := by
  exact
    packedTile32768 312905984 312971520 13 3402 17689 28 _ _ (97807 / 5000) (1956143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell312971520 :
    ThetaLowerSegment 312971520 313037056 (7823869581677 / 25000) (15651050943927 / 50000) := by
  exact
    packedTile32768 312971520 313037056 13 3386 17691 28 _ _ (1956161 / 100000) (489041 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313037056 :
    ThetaLowerSegment 313037056 313102592 (15651050943927 / 50000) (626172241231 / 2000) := by
  exact
    packedTile32768 313037056 313102592 13 3328 17692 28 _ _ (978091 / 50000) (391237 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313102592 :
    ThetaLowerSegment 313102592 313168128 (626172241231 / 2000) (1957199790053 / 6250) := by
  exact
    packedTile32768 313102592 313168128 13 3366 17694 28 _ _ (1956203 / 100000) (978103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313168128 :
    ThetaLowerSegment 313168128 313233664 (1957199790053 / 6250) (391522315041 / 1250) := by
  exact
    packedTile32768 313168128 313233664 13 3368 17696 28 _ _ (61132 / 3125) (1956227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313233664 :
    ThetaLowerSegment 313233664 313299200 (391522315041 / 1250) (1253130493219 / 4000) := by
  exact
    packedTile32768 313233664 313299200 13 3311 17698 28 _ _ (391249 / 20000) (244531 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313299200 :
    ThetaLowerSegment 313299200 313364736 (1253130493219 / 4000) (6266965511163 / 20000) := by
  exact
    packedTile32768 313299200 313364736 13 3356 17700 28 _ _ (391253 / 20000) (489067 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313364736 :
    ThetaLowerSegment 313364736 313430272 (6266965511163 / 20000) (31341402633061 / 100000) := by
  exact
    packedTile32768 313364736 313430272 13 3361 17702 28 _ _ (978143 / 50000) (1956289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313430272 :
    ThetaLowerSegment 313430272 313495808 (31341402633061 / 100000) (3134779388803 / 10000) := by
  exact
    packedTile32768 313430272 313495808 13 3267 17703 28 _ _ (1956307 / 100000) (195631 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313495808 :
    ThetaLowerSegment 313495808 313561344 (3134779388803 / 10000) (627086560471 / 2000) := by
  exact
    packedTile32768 313495808 313561344 13 3340 17705 28 _ _ (244541 / 12500) (1956331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313561344 :
    ThetaLowerSegment 313561344 313626880 (627086560471 / 2000) (15680466328887 / 50000) := by
  exact
    packedTile32768 313561344 313626880 13 3376 17707 28 _ _ (1956349 / 100000) (61136 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313626880 :
    ThetaLowerSegment 313626880 313692416 (15680466328887 / 50000) (15683764768707 / 50000) := by
  exact
    packedTile32768 313626880 313692416 13 3372 17709 28 _ _ (195637 / 10000) (1956373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313692416 :
    ThetaLowerSegment 313692416 313757952 (15683764768707 / 50000) (3921766300081 / 12500) := by
  exact
    packedTile32768 313692416 313757952 13 3374 17711 28 _ _ (1956391 / 100000) (978197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313757952 :
    ThetaLowerSegment 313757952 313823488 (3921766300081 / 12500) (1569030404039 / 5000) := by
  exact
    packedTile32768 313757952 313823488 13 3311 17713 28 _ _ (489103 / 25000) (391283 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313823488 :
    ThetaLowerSegment 313823488 313889024 (1569030404039 / 5000) (31387183652093 / 100000) := by
  exact
    packedTile32768 313823488 313889024 13 3361 17715 28 _ _ (1956433 / 100000) (489109 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313889024 :
    ThetaLowerSegment 313889024 313954560 (31387183652093 / 100000) (6278742859109 / 20000) := by
  exact
    packedTile32768 313889024 313954560 13 3338 17716 28 _ _ (978227 / 50000) (1956457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell313954560 :
    ThetaLowerSegment 313954560 314020096 (6278742859109 / 20000) (31400325221191 / 100000) := by
  exact
    packedTile32768 313954560 314020096 13 3379 17718 28 _ _ (978237 / 50000) (1956477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314020096 :
    ThetaLowerSegment 314020096 314085632 (31400325221191 / 100000) (15703442674463 / 50000) := by
  exact
    packedTile32768 314020096 314085632 13 3353 17720 28 _ _ (391299 / 20000) (978249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314085632 :
    ThetaLowerSegment 314085632 314151168 (15703442674463 / 50000) (15706722773537 / 50000) := by
  exact
    packedTile32768 314085632 314151168 13 3353 17722 28 _ _ (489129 / 25000) (1956519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314151168 :
    ThetaLowerSegment 314151168 314216704 (15706722773537 / 50000) (15709962798809 / 50000) := by
  exact
    packedTile32768 314151168 314216704 13 3312 17724 28 _ _ (1956537 / 100000) (97827 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314216704 :
    ThetaLowerSegment 314216704 314282240 (15709962798809 / 50000) (7856608766521 / 25000) := by
  exact
    packedTile32768 314216704 314282240 13 3327 17726 28 _ _ (978279 / 50000) (1956561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314282240 :
    ThetaLowerSegment 314282240 314347776 (7856608766521 / 25000) (7858275771829 / 25000) := by
  exact
    packedTile32768 314282240 314347776 13 3408 17728 28 _ _ (1956579 / 100000) (978291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314347776 :
    ThetaLowerSegment 314347776 314413312 (7858275771829 / 25000) (7859937414379 / 25000) := by
  exact
    packedTile32768 314347776 314413312 13 3397 17729 28 _ _ (9783 / 500) (1956603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314413312 :
    ThetaLowerSegment 314413312 314478848 (7859937414379 / 25000) (982695114978 / 3125) := by
  exact
    packedTile32768 314413312 314478848 13 3319 17731 28 _ _ (97831 / 5000) (1956623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314478848 :
    ThetaLowerSegment 314478848 314544384 (982695114978 / 3125) (31452769077031 / 100000) := by
  exact
    packedTile32768 314478848 314544384 13 3335 17733 28 _ _ (1956641 / 100000) (489161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314544384 :
    ThetaLowerSegment 314544384 314609920 (31452769077031 / 100000) (31459294544801 / 100000) := by
  exact
    packedTile32768 314544384 314609920 13 3335 17735 28 _ _ (978331 / 50000) (391333 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314609920 :
    ThetaLowerSegment 314609920 314675456 (31459294544801 / 100000) (31465872913047 / 100000) := by
  exact
    packedTile32768 314609920 314675456 13 3362 17737 28 _ _ (1956683 / 100000) (978343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314675456 :
    ThetaLowerSegment 314675456 314740992 (31465872913047 / 100000) (31472414174519 / 100000) := by
  exact
    packedTile32768 314675456 314740992 13 3343 17739 28 _ _ (61147 / 3125) (1956707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314740992 :
    ThetaLowerSegment 314740992 314806528 (31472414174519 / 100000) (1967431539459 / 6250) := by
  exact
    packedTile32768 314740992 314806528 13 3317 17740 28 _ _ (78269 / 4000) (244591 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314806528 :
    ThetaLowerSegment 314806528 314872064 (1967431539459 / 6250) (31485500818739 / 100000) := by
  exact
    packedTile32768 314806528 314872064 13 3371 17742 28 _ _ (391349 / 20000) (489187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314872064 :
    ThetaLowerSegment 314872064 314937600 (31485500818739 / 100000) (6298397890959 / 20000) := by
  exact
    packedTile32768 314872064 314937600 13 3316 17744 28 _ _ (978383 / 50000) (1956769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell314937600 :
    ThetaLowerSegment 314937600 315003136 (6298397890959 / 20000) (3937316374217 / 12500) := by
  exact
    packedTile32768 314937600 315003136 13 3343 17746 28 _ _ (1956787 / 100000) (195679 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315003136 :
    ThetaLowerSegment 315003136 315068672 (3937316374217 / 12500) (3938128938739 / 12500) := by
  exact
    packedTile32768 315003136 315068672 13 3322 17748 28 _ _ (244601 / 12500) (1956811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315068672 :
    ThetaLowerSegment 315068672 315134208 (3938128938739 / 12500) (15755789529873 / 50000) := by
  exact
    packedTile32768 315068672 315134208 13 3346 17750 28 _ _ (1956829 / 100000) (61151 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315134208 :
    ThetaLowerSegment 315134208 315199744 (15755789529873 / 50000) (31518089496369 / 100000) := by
  exact
    packedTile32768 315134208 315199744 13 3327 17752 28 _ _ (1956849 / 100000) (489213 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315199744 :
    ThetaLowerSegment 315199744 315265280 (31518089496369 / 100000) (31524611744079 / 100000) := by
  exact
    packedTile32768 315199744 315265280 13 3333 17753 28 _ _ (195687 / 10000) (1956873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315265280 :
    ThetaLowerSegment 315265280 315330816 (31524611744079 / 100000) (31531210380531 / 100000) := by
  exact
    packedTile32768 315265280 315330816 13 3372 17755 28 _ _ (1956891 / 100000) (978447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315330816 :
    ThetaLowerSegment 315330816 315396352 (31531210380531 / 100000) (31537650577923 / 100000) := by
  exact
    packedTile32768 315330816 315396352 13 3291 17757 28 _ _ (122307 / 6250) (391383 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315396352 :
    ThetaLowerSegment 315396352 315461888 (31537650577923 / 100000) (6308854567839 / 20000) := by
  exact
    packedTile32768 315396352 315461888 13 3384 17759 28 _ _ (1956933 / 100000) (244617 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315461888 :
    ThetaLowerSegment 315461888 315527424 (6308854567839 / 20000) (15775415294349 / 50000) := by
  exact
    packedTile32768 315461888 315527424 13 3351 17761 28 _ _ (1956953 / 100000) (489239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315527424 :
    ThetaLowerSegment 315527424 315592960 (15775415294349 / 50000) (15778751935019 / 50000) := by
  exact
    packedTile32768 315527424 315592960 13 3410 17763 28 _ _ (978487 / 50000) (1956977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315592960 :
    ThetaLowerSegment 315592960 315658496 (15778751935019 / 50000) (15782039686619 / 50000) := by
  exact
    packedTile32768 315592960 315658496 13 3360 17764 28 _ _ (391399 / 20000) (978499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315658496 :
    ThetaLowerSegment 315658496 315724032 (15782039686619 / 50000) (15785343129627 / 50000) := by
  exact
    packedTile32768 315658496 315724032 13 3376 17766 28 _ _ (244627 / 12500) (1957019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315724032 :
    ThetaLowerSegment 315724032 315789568 (15785343129627 / 50000) (15788614315301 / 50000) := by
  exact
    packedTile32768 315724032 315789568 13 3343 17768 28 _ _ (489259 / 25000) (1957039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315789568 :
    ThetaLowerSegment 315789568 315855104 (15788614315301 / 50000) (15791878686377 / 50000) := by
  exact
    packedTile32768 315789568 315855104 13 3336 17770 28 _ _ (1957057 / 100000) (97853 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315855104 :
    ThetaLowerSegment 315855104 315920640 (15791878686377 / 50000) (3948791888989 / 12500) := by
  exact
    packedTile32768 315855104 315920640 13 3361 17772 28 _ _ (978539 / 50000) (1957081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315920640 :
    ThetaLowerSegment 315920640 315986176 (3948791888989 / 12500) (7899217955643 / 25000) := by
  exact
    packedTile32768 315920640 315986176 13 3340 17774 28 _ _ (1957099 / 100000) (978551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell315986176 :
    ThetaLowerSegment 315986176 316051712 (7899217955643 / 25000) (15801682771707 / 50000) := by
  exact
    packedTile32768 315986176 316051712 13 3318 17776 28 _ _ (1957119 / 100000) (978561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316051712 :
    ThetaLowerSegment 316051712 316117248 (15801682771707 / 50000) (15804958045497 / 50000) := by
  exact
    packedTile32768 316051712 316117248 13 3347 17777 28 _ _ (97857 / 5000) (1957143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316117248 :
    ThetaLowerSegment 316117248 316182784 (15804958045497 / 50000) (7904084873349 / 25000) := by
  exact
    packedTile32768 316117248 316182784 13 3282 17779 28 _ _ (1957161 / 100000) (489291 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316182784 :
    ThetaLowerSegment 316182784 316248320 (7904084873349 / 25000) (15811409861499 / 50000) := by
  exact
    packedTile32768 316182784 316248320 13 3311 17781 28 _ _ (978591 / 50000) (391437 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316248320 :
    ThetaLowerSegment 316248320 316313856 (15811409861499 / 50000) (1976833942329 / 6250) := by
  exact
    packedTile32768 316248320 316313856 13 3333 17783 28 _ _ (978601 / 50000) (391441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316313856 :
    ThetaLowerSegment 316313856 316379392 (1976833942329 / 6250) (15817996860509 / 50000) := by
  exact
    packedTile32768 316313856 316379392 13 3398 17785 28 _ _ (1957223 / 100000) (978613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316379392 :
    ThetaLowerSegment 316379392 316444928 (15817996860509 / 50000) (15821308517357 / 50000) := by
  exact
    packedTile32768 316379392 316444928 13 3384 17787 28 _ _ (489311 / 25000) (1957247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316444928 :
    ThetaLowerSegment 316444928 316510464 (15821308517357 / 50000) (632985395501 / 2000) := by
  exact
    packedTile32768 316444928 316510464 13 3399 17788 28 _ _ (122329 / 6250) (1957267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316510464 :
    ThetaLowerSegment 316510464 316576000 (632985395501 / 2000) (6331176688213 / 20000) := by
  exact
    packedTile32768 316510464 316576000 13 3379 17790 28 _ _ (391457 / 20000) (244661 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316576000 :
    ThetaLowerSegment 316576000 316641536 (6331176688213 / 20000) (31662272087849 / 100000) := by
  exact
    packedTile32768 316576000 316641536 13 3264 17792 28 _ _ (978653 / 50000) (1957309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316641536 :
    ThetaLowerSegment 316641536 316707072 (31662272087849 / 100000) (15834403801351 / 50000) := by
  exact
    packedTile32768 316641536 316707072 13 3339 17794 28 _ _ (1957327 / 100000) (195733 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316707072 :
    ThetaLowerSegment 316707072 316772608 (15834403801351 / 50000) (31675515430871 / 100000) := by
  exact
    packedTile32768 316707072 316772608 13 3427 17796 28 _ _ (1957347 / 100000) (39147 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316772608 :
    ThetaLowerSegment 316772608 316838144 (31675515430871 / 100000) (31682051082623 / 100000) := by
  exact
    packedTile32768 316772608 316838144 13 3339 17798 28 _ _ (244671 / 12500) (1957371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316838144 :
    ThetaLowerSegment 316838144 316903680 (31682051082623 / 100000) (15844328635249 / 50000) := by
  exact
    packedTile32768 316838144 316903680 13 3375 17799 28 _ _ (1957389 / 100000) (122337 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316903680 :
    ThetaLowerSegment 316903680 316969216 (15844328635249 / 50000) (3961886164559 / 12500) := by
  exact
    packedTile32768 316903680 316969216 13 3286 17801 28 _ _ (1957409 / 100000) (489353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell316969216 :
    ThetaLowerSegment 316969216 317034752 (3961886164559 / 12500) (1981356589367 / 6250) := by
  exact
    packedTile32768 316969216 317034752 13 3380 17803 28 _ _ (195743 / 10000) (1957433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317034752 :
    ThetaLowerSegment 317034752 317100288 (1981356589367 / 6250) (31708096507387 / 100000) := by
  exact
    packedTile32768 317034752 317100288 13 3265 17805 28 _ _ (1957451 / 100000) (978727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317100288 :
    ThetaLowerSegment 317100288 317165824 (31708096507387 / 100000) (792866987059 / 2500) := by
  exact
    packedTile32768 317100288 317165824 13 3363 17807 28 _ _ (1957471 / 100000) (978737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317165824 :
    ThetaLowerSegment 317165824 317231360 (792866987059 / 2500) (3965151209459 / 12500) := by
  exact
    packedTile32768 317165824 317231360 13 3336 17809 28 _ _ (489373 / 25000) (391499 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317231360 :
    ThetaLowerSegment 317231360 317296896 (3965151209459 / 12500) (31727737981527 / 100000) := by
  exact
    packedTile32768 317231360 317296896 13 3335 17810 28 _ _ (1957513 / 100000) (489379 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317296896 :
    ThetaLowerSegment 317296896 317362432 (31727737981527 / 100000) (15867141007173 / 50000) := by
  exact
    packedTile32768 317296896 317362432 13 3343 17812 28 _ _ (1957533 / 100000) (61173 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317362432 :
    ThetaLowerSegment 317362432 317427968 (15867141007173 / 50000) (15870421867677 / 50000) := by
  exact
    packedTile32768 317362432 317427968 13 3352 17814 28 _ _ (978777 / 50000) (1957557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317427968 :
    ThetaLowerSegment 317427968 317493504 (15870421867677 / 50000) (1984209174969 / 6250) := by
  exact
    packedTile32768 317427968 317493504 13 3322 17816 28 _ _ (78303 / 4000) (978789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317493504 :
    ThetaLowerSegment 317493504 317559040 (1984209174969 / 6250) (1984616354729 / 6250) := by
  exact
    packedTile32768 317493504 317559040 13 3328 17818 28 _ _ (391519 / 20000) (978799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317559040 :
    ThetaLowerSegment 317559040 317624576 (1984616354729 / 6250) (1985040667997 / 6250) := by
  exact
    packedTile32768 317559040 317624576 13 3468 17820 28 _ _ (122351 / 6250) (1957619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317624576 :
    ThetaLowerSegment 317624576 317690112 (1985040667997 / 6250) (15883584809581 / 50000) := by
  exact
    packedTile32768 317624576 317690112 13 3330 17822 28 _ _ (1957637 / 100000) (48941 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317690112 :
    ThetaLowerSegment 317690112 317755648 (15883584809581 / 50000) (6354717755293 / 20000) := by
  exact
    packedTile32768 317690112 317755648 13 3279 17823 28 _ _ (1957657 / 100000) (97883 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317755648 :
    ThetaLowerSegment 317755648 317821184 (6354717755293 / 20000) (31780199855071 / 100000) := by
  exact
    packedTile32768 317755648 317821184 13 3377 17825 28 _ _ (978839 / 50000) (1957681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317821184 :
    ThetaLowerSegment 317821184 317886720 (31780199855071 / 100000) (31786717031713 / 100000) := by
  exact
    packedTile32768 317821184 317886720 13 3329 17827 28 _ _ (978849 / 50000) (1957701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317886720 :
    ThetaLowerSegment 317886720 317952256 (31786717031713 / 100000) (31793345868247 / 100000) := by
  exact
    packedTile32768 317886720 317952256 13 3386 17829 28 _ _ (1957719 / 100000) (978861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell317952256 :
    ThetaLowerSegment 317952256 318017792 (31793345868247 / 100000) (31799918001427 / 100000) := by
  exact
    packedTile32768 317952256 318017792 13 3357 17831 28 _ _ (97887 / 5000) (1957743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318017792 :
    ThetaLowerSegment 318017792 318083328 (31799918001427 / 100000) (31806445173267 / 100000) := by
  exact
    packedTile32768 318017792 318083328 13 3334 17833 28 _ _ (12236 / 625) (1957763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318083328 :
    ThetaLowerSegment 318083328 318148864 (31806445173267 / 100000) (15906506764261 / 50000) := by
  exact
    packedTile32768 318083328 318148864 13 3355 17834 28 _ _ (1957781 / 100000) (244723 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318148864 :
    ThetaLowerSegment 318148864 318214400 (15906506764261 / 50000) (31819660262917 / 100000) := by
  exact
    packedTile32768 318148864 318214400 13 3395 17836 28 _ _ (1957801 / 100000) (489451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318214400 :
    ThetaLowerSegment 318214400 318279936 (31819660262917 / 100000) (1273047897223 / 4000) := by
  exact
    packedTile32768 318214400 318279936 13 3339 17838 28 _ _ (978911 / 50000) (78313 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318279936 :
    ThetaLowerSegment 318279936 318345472 (1273047897223 / 4000) (15916306641043 / 50000) := by
  exact
    packedTile32768 318279936 318345472 13 3277 17840 28 _ _ (1957843 / 100000) (978923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318345472 :
    ThetaLowerSegment 318345472 318411008 (15916306641043 / 50000) (15919576272253 / 50000) := by
  exact
    packedTile32768 318345472 318411008 13 3340 17842 28 _ _ (1957863 / 100000) (978933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318411008 :
    ThetaLowerSegment 318411008 318476544 (15919576272253 / 50000) (3184567425611 / 10000) := by
  exact
    packedTile32768 318411008 318476544 13 3331 17844 28 _ _ (489471 / 25000) (1957887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318476544 :
    ThetaLowerSegment 318476544 318542080 (3184567425611 / 10000) (15926079417079 / 50000) := by
  exact
    packedTile32768 318476544 318542080 13 3312 17845 28 _ _ (122369 / 6250) (1957907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318542080 :
    ThetaLowerSegment 318542080 318607616 (15926079417079 / 50000) (31858727672533 / 100000) := by
  exact
    packedTile32768 318542080 318607616 13 3355 17847 28 _ _ (78317 / 4000) (244741 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318607616 :
    ThetaLowerSegment 318607616 318673152 (31858727672533 / 100000) (31865216305577 / 100000) := by
  exact
    packedTile32768 318607616 318673152 13 3314 17849 28 _ _ (978973 / 50000) (1957949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318673152 :
    ThetaLowerSegment 318673152 318738688 (31865216305577 / 100000) (31871759827949 / 100000) := by
  exact
    packedTile32768 318673152 318738688 13 3342 17851 28 _ _ (978983 / 50000) (1957969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318738688 :
    ThetaLowerSegment 318738688 318804224 (31871759827949 / 100000) (31878385655957 / 100000) := by
  exact
    packedTile32768 318738688 318804224 13 3384 17853 28 _ _ (1957987 / 100000) (195799 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318804224 :
    ThetaLowerSegment 318804224 318869760 (31878385655957 / 100000) (15942449972623 / 50000) := by
  exact
    packedTile32768 318804224 318869760 13 3327 17855 28 _ _ (1958007 / 100000) (195801 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318869760 :
    ThetaLowerSegment 318869760 318935296 (15942449972623 / 50000) (3189145542299 / 10000) := by
  exact
    packedTile32768 318869760 318935296 13 3348 17856 28 _ _ (489507 / 25000) (1958031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell318935296 :
    ThetaLowerSegment 318935296 319000832 (3189145542299 / 10000) (15948961427767 / 50000) := by
  exact
    packedTile32768 318935296 319000832 13 3303 17858 28 _ _ (61189 / 3125) (1958051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319000832 :
    ThetaLowerSegment 319000832 319066368 (15948961427767 / 50000) (31904425602683 / 100000) := by
  exact
    packedTile32768 319000832 319066368 13 3321 17860 28 _ _ (1958069 / 100000) (244759 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319066368 :
    ThetaLowerSegment 319066368 319131904 (31904425602683 / 100000) (31910879464027 / 100000) := by
  exact
    packedTile32768 319066368 319131904 13 3296 17862 28 _ _ (1958089 / 100000) (489523 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319131904 :
    ThetaLowerSegment 319131904 319197440 (31910879464027 / 100000) (31917417593317 / 100000) := by
  exact
    packedTile32768 319131904 319197440 13 3339 17864 28 _ _ (195811 / 10000) (1958113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319197440 :
    ThetaLowerSegment 319197440 319262976 (31917417593317 / 100000) (7981009508557 / 25000) := by
  exact
    packedTile32768 319197440 319262976 13 3381 17866 28 _ _ (1958131 / 100000) (979067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319262976 :
    ThetaLowerSegment 319262976 319328512 (7981009508557 / 25000) (3991318366019 / 12500) := by
  exact
    packedTile32768 319262976 319328512 13 3324 17867 28 _ _ (1958151 / 100000) (979077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319328512 :
    ThetaLowerSegment 319328512 319394048 (3991318366019 / 12500) (3992150589119 / 12500) := by
  exact
    packedTile32768 319328512 319394048 13 3400 17869 28 _ _ (489543 / 25000) (78327 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319394048 :
    ThetaLowerSegment 319394048 319459584 (3992150589119 / 12500) (3992970582019 / 12500) := by
  exact
    packedTile32768 319394048 319459584 13 3350 17871 28 _ _ (122387 / 6250) (391639 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319459584 :
    ThetaLowerSegment 319459584 319525120 (3992970582019 / 12500) (31950213051561 / 100000) := by
  exact
    packedTile32768 319459584 319525120 13 3293 17873 28 _ _ (1958213 / 100000) (244777 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319525120 :
    ThetaLowerSegment 319525120 319590656 (31950213051561 / 100000) (998650690248 / 3125) := by
  exact
    packedTile32768 319525120 319590656 13 3375 17875 28 _ _ (1958233 / 100000) (489559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319590656 :
    ThetaLowerSegment 319590656 319656192 (998650690248 / 3125) (7990847517963 / 25000) := by
  exact
    packedTile32768 319590656 319656192 13 3354 17877 28 _ _ (979127 / 50000) (1958257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319656192 :
    ThetaLowerSegment 319656192 319721728 (7990847517963 / 25000) (7992494426397 / 25000) := by
  exact
    packedTile32768 319656192 319721728 13 3364 17878 28 _ _ (979137 / 50000) (1958277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319721728 :
    ThetaLowerSegment 319721728 319787264 (7992494426397 / 25000) (31976489036463 / 100000) := by
  exact
    packedTile32768 319721728 319787264 13 3325 17880 28 _ _ (391659 / 20000) (979149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319787264 :
    ThetaLowerSegment 319787264 319852800 (31976489036463 / 100000) (7995755004247 / 25000) := by
  exact
    packedTile32768 319787264 319852800 13 3335 17882 28 _ _ (391663 / 20000) (979159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319852800 :
    ThetaLowerSegment 319852800 319918336 (7995755004247 / 25000) (7997394131479 / 25000) := by
  exact
    packedTile32768 319852800 319918336 13 3348 17884 28 _ _ (61198 / 3125) (1958339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319918336 :
    ThetaLowerSegment 319918336 319983872 (7997394131479 / 25000) (7999038171341 / 25000) := by
  exact
    packedTile32768 319918336 319983872 13 3358 17886 28 _ _ (489589 / 25000) (1958359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell319983872 :
    ThetaLowerSegment 319983872 320049408 (7999038171341 / 25000) (6400532074427 / 20000) := by
  exact
    packedTile32768 319983872 320049408 13 3323 17888 28 _ _ (1958377 / 100000) (97919 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320049408 :
    ThetaLowerSegment 320049408 320114944 (6400532074427 / 20000) (32009213168497 / 100000) := by
  exact
    packedTile32768 320049408 320114944 13 3346 17889 28 _ _ (1958397 / 100000) (2448 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320114944 :
    ThetaLowerSegment 320114944 320180480 (32009213168497 / 100000) (6403151248607 / 20000) := by
  exact
    packedTile32768 320114944 320180480 13 3341 17891 28 _ _ (979209 / 50000) (1958421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320180480 :
    ThetaLowerSegment 320180480 320246016 (6403151248607 / 20000) (32022320927211 / 100000) := by
  exact
    packedTile32768 320180480 320246016 13 3352 17893 28 _ _ (979219 / 50000) (1958441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320246016 :
    ThetaLowerSegment 320246016 320311552 (32022320927211 / 100000) (16014439903201 / 50000) := by
  exact
    packedTile32768 320246016 320311552 13 3349 17895 28 _ _ (1958459 / 100000) (979231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320311552 :
    ThetaLowerSegment 320311552 320377088 (16014439903201 / 50000) (2002210637863 / 6250) := by
  exact
    packedTile32768 320311552 320377088 13 3314 17897 28 _ _ (1958479 / 100000) (979241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320377088 :
    ThetaLowerSegment 320377088 320442624 (2002210637863 / 6250) (4005241886807 / 12500) := by
  exact
    packedTile32768 320377088 320442624 13 3352 17899 28 _ _ (1958499 / 100000) (979251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320442624 :
    ThetaLowerSegment 320442624 320508160 (4005241886807 / 12500) (4006064465207 / 12500) := by
  exact
    packedTile32768 320442624 320508160 13 3360 17900 28 _ _ (48963 / 2500) (1958523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320508160 :
    ThetaLowerSegment 320508160 320573696 (4006064465207 / 12500) (2003439853741 / 6250) := by
  exact
    packedTile32768 320508160 320573696 13 3330 17902 28 _ _ (97927 / 5000) (1958543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320573696 :
    ThetaLowerSegment 320573696 320639232 (2003439853741 / 6250) (8015394813399 / 25000) := by
  exact
    packedTile32768 320573696 320639232 13 3340 17904 28 _ _ (1958561 / 100000) (489641 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320639232 :
    ThetaLowerSegment 320639232 320704768 (8015394813399 / 25000) (16034148593213 / 50000) := by
  exact
    packedTile32768 320639232 320704768 13 3430 17906 28 _ _ (1958581 / 100000) (244823 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320704768 :
    ThetaLowerSegment 320704768 320770304 (16034148593213 / 50000) (1002341348031 / 3125) := by
  exact
    packedTile32768 320704768 320770304 13 3383 17908 28 _ _ (979301 / 50000) (391721 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320770304 :
    ThetaLowerSegment 320770304 320835840 (1002341348031 / 3125) (16040727570681 / 50000) := by
  exact
    packedTile32768 320770304 320835840 13 3335 17910 28 _ _ (979311 / 50000) (15669 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320835840 :
    ThetaLowerSegment 320835840 320901376 (16040727570681 / 50000) (16044006339063 / 50000) := by
  exact
    packedTile32768 320835840 320901376 13 3348 17911 28 _ _ (1958643 / 100000) (979323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320901376 :
    ThetaLowerSegment 320901376 320966912 (16044006339063 / 50000) (32094536984579 / 100000) := by
  exact
    packedTile32768 320901376 320966912 13 3331 17913 28 _ _ (1958663 / 100000) (979333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell320966912 :
    ThetaLowerSegment 320966912 321032448 (32094536984579 / 100000) (16050532637509 / 50000) := by
  exact
    packedTile32768 320966912 321032448 13 3333 17915 28 _ _ (1958683 / 100000) (979343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321032448 :
    ThetaLowerSegment 321032448 321097984 (16050532637509 / 50000) (3210766219009 / 10000) := by
  exact
    packedTile32768 321032448 321097984 13 3368 17917 28 _ _ (122419 / 6250) (1958707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321097984 :
    ThetaLowerSegment 321097984 321163520 (3210766219009 / 10000) (16057078659437 / 50000) := by
  exact
    packedTile32768 321097984 321163520 13 3316 17919 28 _ _ (489681 / 25000) (1958727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321163520 :
    ThetaLowerSegment 321163520 321229056 (16057078659437 / 50000) (16060353681077 / 50000) := by
  exact
    packedTile32768 321163520 321229056 13 3344 17921 28 _ _ (391749 / 20000) (489687 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321229056 :
    ThetaLowerSegment 321229056 321294592 (16060353681077 / 50000) (1003976673587 / 3125) := by
  exact
    packedTile32768 321229056 321294592 13 3342 17922 28 _ _ (391753 / 20000) (122423 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321294592 :
    ThetaLowerSegment 321294592 321360128 (1003976673587 / 3125) (16066899907127 / 50000) := by
  exact
    packedTile32768 321294592 321360128 13 3342 17924 28 _ _ (391757 / 20000) (489697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321360128 :
    ThetaLowerSegment 321360128 321425664 (16066899907127 / 50000) (16070165236729 / 50000) := by
  exact
    packedTile32768 321360128 321425664 13 3334 17926 28 _ _ (979403 / 50000) (1958809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321425664 :
    ThetaLowerSegment 321425664 321491200 (16070165236729 / 50000) (8036691304217 / 25000) := by
  exact
    packedTile32768 321425664 321491200 13 3285 17928 28 _ _ (979413 / 50000) (1958829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321491200 :
    ThetaLowerSegment 321491200 321556736 (8036691304217 / 25000) (32153376325493 / 100000) := by
  exact
    packedTile32768 321491200 321556736 13 3375 17930 28 _ _ (1958847 / 100000) (39177 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321556736 :
    ThetaLowerSegment 321556736 321622272 (32153376325493 / 100000) (32159907188071 / 100000) := by
  exact
    packedTile32768 321556736 321622272 13 3334 17932 28 _ _ (1958867 / 100000) (195887 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321622272 :
    ThetaLowerSegment 321622272 321687808 (32159907188071 / 100000) (32166442035103 / 100000) := by
  exact
    packedTile32768 321622272 321687808 13 3336 17933 28 _ _ (1958887 / 100000) (195889 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321687808 :
    ThetaLowerSegment 321687808 321753344 (32166442035103 / 100000) (32172955404203 / 100000) := by
  exact
    packedTile32768 321687808 321753344 13 3325 17935 28 _ _ (489727 / 25000) (1958911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321753344 :
    ThetaLowerSegment 321753344 321818880 (32172955404203 / 100000) (32179470798731 / 100000) := by
  exact
    packedTile32768 321753344 321818880 13 3326 17937 28 _ _ (122433 / 6250) (1958931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321818880 :
    ThetaLowerSegment 321818880 321851648 (32179470798731 / 100000) (32182710898723 / 100000) := by
  exact
    packedTile32768 321818880 321851648 12 1654 17939 28 _ _ (489737 / 25000) (1958951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321851648 :
    ThetaLowerSegment 321851648 321884416 (32182710898723 / 100000) (32185966688581 / 100000) := by
  exact
    packedTile32768 321851648 321884416 12 1662 17940 28 _ _ (1958959 / 100000) (979481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321884416 :
    ThetaLowerSegment 321884416 321917184 (32185966688581 / 100000) (16094633775673 / 50000) := by
  exact
    packedTile32768 321884416 321917184 12 1685 17941 28 _ _ (1958969 / 100000) (489743 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321917184 :
    ThetaLowerSegment 321917184 321949952 (16094633775673 / 50000) (16096251892327 / 50000) := by
  exact
    packedTile32768 321917184 321949952 12 1652 17942 28 _ _ (1958979 / 100000) (979491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321949952 :
    ThetaLowerSegment 321949952 321982720 (16096251892327 / 50000) (32195781173251 / 100000) := by
  exact
    packedTile32768 321949952 321982720 12 1673 17942 28 _ _ (1958989 / 100000) (122437 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell321982720 :
    ThetaLowerSegment 321982720 322015488 (32195781173251 / 100000) (16099525371291 / 50000) := by
  exact
    packedTile32768 321982720 322015488 12 1669 17943 28 _ _ (1958999 / 100000) (979501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322015488 :
    ThetaLowerSegment 322015488 322048256 (16099525371291 / 50000) (16101168980681 / 50000) := by
  exact
    packedTile32768 322015488 322048256 12 1678 17944 28 _ _ (195901 / 10000) (1959013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322048256 :
    ThetaLowerSegment 322048256 322081024 (16101168980681 / 50000) (16102819455031 / 50000) := by
  exact
    packedTile32768 322048256 322081024 12 1685 17945 28 _ _ (97951 / 5000) (1959023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322081024 :
    ThetaLowerSegment 322081024 322113792 (16102819455031 / 50000) (8052229091813 / 25000) := by
  exact
    packedTile32768 322081024 322113792 12 1673 17946 28 _ _ (195903 / 10000) (1959033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322113792 :
    ThetaLowerSegment 322113792 322146560 (8052229091813 / 25000) (8053059724773 / 25000) := by
  exact
    packedTile32768 322113792 322146560 12 1696 17947 28 _ _ (12244 / 625) (1959043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322146560 :
    ThetaLowerSegment 322146560 322212096 (8053059724773 / 25000) (16109350902521 / 50000) := by
  exact
    packedTile32768 322146560 322212096 13 3299 17948 28 _ _ (39181 / 2000) (1959053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322212096 :
    ThetaLowerSegment 322212096 322244864 (16109350902521 / 50000) (6444403702449 / 20000) := by
  exact
    packedTile32768 322212096 322244864 12 1693 17950 28 _ _ (1959071 / 100000) (979537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322244864 :
    ThetaLowerSegment 322244864 322277632 (6444403702449 / 20000) (4028166414777 / 12500) := by
  exact
    packedTile32768 322244864 322277632 12 1691 17951 28 _ _ (1959081 / 100000) (489771 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322277632 :
    ThetaLowerSegment 322277632 322310400 (4028166414777 / 12500) (32228585368367 / 100000) := by
  exact
    packedTile32768 322277632 322310400 12 1661 17952 28 _ _ (1959091 / 100000) (979547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322310400 :
    ThetaLowerSegment 322310400 322343168 (32228585368367 / 100000) (32231790457603 / 100000) := by
  exact
    packedTile32768 322310400 322343168 12 1636 17953 28 _ _ (1959101 / 100000) (61222 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322343168 :
    ThetaLowerSegment 322343168 322375936 (32231790457603 / 100000) (32235117028081 / 100000) := by
  exact
    packedTile32768 322343168 322375936 12 1698 17953 28 _ _ (1959111 / 100000) (979557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322375936 :
    ThetaLowerSegment 322375936 322408704 (32235117028081 / 100000) (16119189482273 / 50000) := by
  exact
    packedTile32768 322375936 322408704 12 1665 17954 28 _ _ (1959121 / 100000) (489781 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322408704 :
    ThetaLowerSegment 322408704 322441472 (16119189482273 / 50000) (16120854744473 / 50000) := by
  exact
    packedTile32768 322408704 322441472 12 1700 17955 28 _ _ (489783 / 25000) (391827 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322441472 :
    ThetaLowerSegment 322441472 322474240 (16120854744473 / 50000) (16122500423753 / 50000) := by
  exact
    packedTile32768 322441472 322474240 12 1680 17956 28 _ _ (979571 / 50000) (391829 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322474240 :
    ThetaLowerSegment 322474240 322539776 (16122500423753 / 50000) (16125810411057 / 50000) := by
  exact
    packedTile32768 322474240 322539776 13 3379 17957 28 _ _ (122447 / 6250) (391831 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322539776 :
    ThetaLowerSegment 322539776 322605312 (16125810411057 / 50000) (16129112595463 / 50000) := by
  exact
    packedTile32768 322539776 322605312 13 3371 17959 28 _ _ (489793 / 25000) (78367 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322605312 :
    ThetaLowerSegment 322605312 322670848 (16129112595463 / 50000) (2016540953897 / 6250) := by
  exact
    packedTile32768 322605312 322670848 13 3282 17961 28 _ _ (1959193 / 100000) (489799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322670848 :
    ThetaLowerSegment 322670848 322703616 (2016540953897 / 6250) (16133971410883 / 50000) := by
  exact
    packedTile32768 322670848 322703616 12 1678 17963 28 _ _ (1959213 / 100000) (122451 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322703616 :
    ThetaLowerSegment 322703616 322769152 (16133971410883 / 50000) (16137282497753 / 50000) := by
  exact
    packedTile32768 322703616 322769152 13 3380 17963 28 _ _ (1959223 / 100000) (979613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322769152 :
    ThetaLowerSegment 322769152 322834688 (16137282497753 / 50000) (32281048130593 / 100000) := by
  exact
    packedTile32768 322769152 322834688 13 3309 17965 28 _ _ (1959243 / 100000) (979623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322834688 :
    ThetaLowerSegment 322834688 322900224 (32281048130593 / 100000) (32287554846337 / 100000) := by
  exact
    packedTile32768 322834688 322900224 13 3321 17967 28 _ _ (61227 / 3125) (1959267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322900224 :
    ThetaLowerSegment 322900224 322932992 (32287554846337 / 100000) (32290813135629 / 100000) := by
  exact
    packedTile32768 322900224 322932992 12 1663 17969 28 _ _ (489821 / 25000) (1959287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322932992 :
    ThetaLowerSegment 322932992 322965760 (32290813135629 / 100000) (32294179202721 / 100000) := by
  exact
    packedTile32768 322932992 322965760 12 1718 17970 28 _ _ (979647 / 50000) (1959297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell322965760 :
    ThetaLowerSegment 322965760 323031296 (32294179202721 / 100000) (6460154843997 / 20000) := by
  exact
    packedTile32768 322965760 323031296 13 3366 17971 28 _ _ (244913 / 12500) (1959307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323031296 :
    ThetaLowerSegment 323031296 323096832 (6460154843997 / 20000) (32307304646877 / 100000) := by
  exact
    packedTile32768 323031296 323096832 13 3333 17973 28 _ _ (489831 / 25000) (1959327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323096832 :
    ThetaLowerSegment 323096832 323162368 (32307304646877 / 100000) (8078451928233 / 25000) := by
  exact
    packedTile32768 323096832 323162368 13 3319 17974 28 _ _ (391869 / 20000) (489837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323162368 :
    ThetaLowerSegment 323162368 323227904 (8078451928233 / 25000) (32320291251717 / 100000) := by
  exact
    packedTile32768 323162368 323227904 13 3309 17976 28 _ _ (391873 / 20000) (244921 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323227904 :
    ThetaLowerSegment 323227904 323260672 (32320291251717 / 100000) (8080891346013 / 25000) := by
  exact
    packedTile32768 323227904 323260672 12 1671 17978 28 _ _ (391877 / 20000) (489847 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323260672 :
    ThetaLowerSegment 323260672 323293440 (8080891346013 / 25000) (32326913990107 / 100000) := by
  exact
    packedTile32768 323260672 323293440 12 1709 17979 28 _ _ (391879 / 20000) (979699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323293440 :
    ThetaLowerSegment 323293440 323358976 (32326913990107 / 100000) (32333509350703 / 100000) := by
  exact
    packedTile32768 323293440 323358976 13 3366 17980 28 _ _ (979703 / 50000) (1959409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323358976 :
    ThetaLowerSegment 323358976 323424512 (32333509350703 / 100000) (32339902957741 / 100000) := by
  exact
    packedTile32768 323358976 323424512 13 3263 17982 28 _ _ (979713 / 50000) (1959429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323424512 :
    ThetaLowerSegment 323424512 323457280 (32339902957741 / 100000) (32343194827021 / 100000) := by
  exact
    packedTile32768 323424512 323457280 12 1680 17984 28 _ _ (979723 / 50000) (1959449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323457280 :
    ThetaLowerSegment 323457280 323490048 (32343194827021 / 100000) (32346476915821 / 100000) := by
  exact
    packedTile32768 323457280 323490048 12 1675 17984 28 _ _ (61233 / 3125) (1959459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323490048 :
    ThetaLowerSegment 323490048 323522816 (32346476915821 / 100000) (32349784494429 / 100000) := by
  exact
    packedTile32768 323490048 323522816 12 1688 17985 28 _ _ (979733 / 50000) (1959469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323522816 :
    ThetaLowerSegment 323522816 323555584 (32349784494429 / 100000) (32353048983111 / 100000) := by
  exact
    packedTile32768 323522816 323555584 12 1666 17986 28 _ _ (1959477 / 100000) (48987 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323555584 :
    ThetaLowerSegment 323555584 323588352 (32353048983111 / 100000) (16178151845509 / 50000) := by
  exact
    packedTile32768 323555584 323588352 12 1661 17987 28 _ _ (1959487 / 100000) (195949 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323588352 :
    ThetaLowerSegment 323588352 323621120 (16178151845509 / 50000) (16179840931923 / 50000) := by
  exact
    packedTile32768 323588352 323621120 12 1724 17988 28 _ _ (1959497 / 100000) (3919 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323621120 :
    ThetaLowerSegment 323621120 323686656 (16179840931923 / 50000) (8091571350609 / 25000) := by
  exact
    packedTile32768 323621120 323686656 13 3370 17989 28 _ _ (1959507 / 100000) (195951 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323686656 :
    ThetaLowerSegment 323686656 323752192 (8091571350609 / 25000) (8093229110451 / 25000) := by
  exact
    packedTile32768 323686656 323752192 13 3384 17991 28 _ _ (1959527 / 100000) (195953 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323752192 :
    ThetaLowerSegment 323752192 323817728 (8093229110451 / 25000) (32379502479271 / 100000) := by
  exact
    packedTile32768 323752192 323817728 13 3361 17993 28 _ _ (1959547 / 100000) (39191 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323817728 :
    ThetaLowerSegment 323817728 323883264 (32379502479271 / 100000) (32386027840711 / 100000) := by
  exact
    packedTile32768 323817728 323883264 13 3330 17994 28 _ _ (122473 / 6250) (1959571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323883264 :
    ThetaLowerSegment 323883264 323948800 (32386027840711 / 100000) (32392680641971 / 100000) := by
  exact
    packedTile32768 323883264 323948800 13 3395 17996 28 _ _ (489897 / 25000) (1959591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell323948800 :
    ThetaLowerSegment 323948800 324014336 (32392680641971 / 100000) (6479852201127 / 20000) := by
  exact
    packedTile32768 323948800 324014336 13 3358 17998 28 _ _ (244951 / 12500) (1959611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324014336 :
    ThetaLowerSegment 324014336 324079872 (6479852201127 / 20000) (32405768930223 / 100000) := by
  exact
    packedTile32768 324014336 324079872 13 3321 18000 28 _ _ (489907 / 25000) (1959631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324079872 :
    ThetaLowerSegment 324079872 324145408 (32405768930223 / 100000) (32412243610519 / 100000) := by
  exact
    packedTile32768 324079872 324145408 13 3304 18002 28 _ _ (1959649 / 100000) (489913 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324145408 :
    ThetaLowerSegment 324145408 324210944 (32412243610519 / 100000) (16209389553317 / 50000) := by
  exact
    packedTile32768 324145408 324210944 13 3335 18004 28 _ _ (1959669 / 100000) (244959 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324210944 :
    ThetaLowerSegment 324210944 324276480 (16209389553317 / 50000) (16212658314569 / 50000) := by
  exact
    packedTile32768 324210944 324276480 13 3336 18005 28 _ _ (1959689 / 100000) (489923 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324276480 :
    ThetaLowerSegment 324276480 324342016 (16212658314569 / 50000) (16215876156747 / 50000) := by
  exact
    packedTile32768 324276480 324342016 13 3284 18007 28 _ _ (1959709 / 100000) (61241 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324342016 :
    ThetaLowerSegment 324342016 324407552 (16215876156747 / 50000) (32438150828679 / 100000) := by
  exact
    packedTile32768 324342016 324407552 13 3265 18009 28 _ _ (1959729 / 100000) (489933 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324407552 :
    ThetaLowerSegment 324407552 324440320 (32438150828679 / 100000) (32441474564679 / 100000) := by
  exact
    packedTile32768 324407552 324440320 12 1696 18011 28 _ _ (7839 / 400) (1959753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324440320 :
    ThetaLowerSegment 324440320 324473088 (32441474564679 / 100000) (32444749323639 / 100000) := by
  exact
    packedTile32768 324440320 324473088 12 1671 18012 28 _ _ (24497 / 1250) (1959763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324473088 :
    ThetaLowerSegment 324473088 324505856 (32444749323639 / 100000) (32448061334939 / 100000) := by
  exact
    packedTile32768 324473088 324505856 12 1690 18013 28 _ _ (195977 / 10000) (1959773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324505856 :
    ThetaLowerSegment 324505856 324538624 (32448061334939 / 100000) (32451314569739 / 100000) := by
  exact
    packedTile32768 324505856 324538624 12 1660 18014 28 _ _ (97989 / 5000) (1959783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324538624 :
    ThetaLowerSegment 324538624 324571392 (32451314569739 / 100000) (32454671690009 / 100000) := by
  exact
    packedTile32768 324538624 324571392 12 1713 18014 28 _ _ (195979 / 10000) (1959793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324571392 :
    ThetaLowerSegment 324571392 324604160 (32454671690009 / 100000) (32457960234409 / 100000) := by
  exact
    packedTile32768 324571392 324604160 12 1678 18015 28 _ _ (9799 / 500) (1959803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324604160 :
    ThetaLowerSegment 324604160 324636928 (32457960234409 / 100000) (32461215478819 / 100000) := by
  exact
    packedTile32768 324604160 324636928 12 1661 18016 28 _ _ (195981 / 10000) (1959813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324636928 :
    ThetaLowerSegment 324636928 324669696 (32461215478819 / 100000) (32464537373719 / 100000) := by
  exact
    packedTile32768 324636928 324669696 12 1695 18017 28 _ _ (97991 / 5000) (1959823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324669696 :
    ThetaLowerSegment 324669696 324735232 (32464537373719 / 100000) (32471034210169 / 100000) := by
  exact
    packedTile32768 324669696 324735232 13 3315 18018 28 _ _ (195983 / 10000) (1959833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324735232 :
    ThetaLowerSegment 324735232 324768000 (32471034210169 / 100000) (3247426992417 / 10000) := by
  exact
    packedTile32768 324735232 324768000 12 1651 18020 28 _ _ (1959851 / 100000) (979927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324768000 :
    ThetaLowerSegment 324768000 324800768 (3247426992417 / 10000) (8119379843427 / 25000) := by
  exact
    packedTile32768 324768000 324800768 12 1658 18021 28 _ _ (1959861 / 100000) (244983 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324800768 :
    ThetaLowerSegment 324800768 324833536 (8119379843427 / 25000) (4060110314043 / 12500) := by
  exact
    packedTile32768 324800768 324833536 12 1716 18022 28 _ _ (1959871 / 100000) (979937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324833536 :
    ThetaLowerSegment 324833536 324866304 (4060110314043 / 12500) (8121033978701 / 25000) := by
  exact
    packedTile32768 324833536 324866304 12 1660 18023 28 _ _ (1959881 / 100000) (489971 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324866304 :
    ThetaLowerSegment 324866304 324899072 (8121033978701 / 25000) (16243708386169 / 50000) := by
  exact
    packedTile32768 324866304 324899072 12 1674 18024 28 _ _ (1959891 / 100000) (979947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324899072 :
    ThetaLowerSegment 324899072 324931840 (16243708386169 / 50000) (4061342105579 / 12500) := by
  exact
    packedTile32768 324899072 324931840 12 1694 18024 28 _ _ (1959901 / 100000) (61247 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324931840 :
    ThetaLowerSegment 324931840 324997376 (4061342105579 / 12500) (16248655193063 / 50000) := by
  exact
    packedTile32768 324931840 324997376 13 3354 18025 28 _ _ (1959911 / 100000) (979957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell324997376 :
    ThetaLowerSegment 324997376 325062912 (16248655193063 / 50000) (3250394279263 / 10000) := by
  exact
    packedTile32768 324997376 325062912 13 3384 18027 28 _ _ (1959931 / 100000) (979967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325062912 :
    ThetaLowerSegment 325062912 325128448 (3250394279263 / 10000) (8127629117071 / 25000) := by
  exact
    packedTile32768 325062912 325128448 13 3354 18029 28 _ _ (1959951 / 100000) (979977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325128448 :
    ThetaLowerSegment 325128448 325193984 (8127629117071 / 25000) (4064635541807 / 12500) := by
  exact
    packedTile32768 325128448 325193984 13 3351 18031 28 _ _ (489993 / 25000) (78399 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325193984 :
    ThetaLowerSegment 325193984 325259520 (4064635541807 / 12500) (4065458248449 / 12500) := by
  exact
    packedTile32768 325193984 325259520 13 3358 18033 28 _ _ (244999 / 12500) (391999 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325259520 :
    ThetaLowerSegment 325259520 325325056 (4065458248449 / 12500) (1626509543377 / 5000) := by
  exact
    packedTile32768 325259520 325325056 13 3329 18034 28 _ _ (490003 / 25000) (392003 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325325056 :
    ThetaLowerSegment 325325056 325390592 (1626509543377 / 5000) (8134204433933 / 25000) := by
  exact
    packedTile32768 325325056 325390592 13 3381 18036 28 _ _ (61251 / 3125) (392007 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325390592 :
    ThetaLowerSegment 325390592 325456128 (8134204433933 / 25000) (1627168607481 / 5000) := by
  exact
    packedTile32768 325390592 325456128 13 3344 18038 28 _ _ (490013 / 25000) (392011 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325456128 :
    ThetaLowerSegment 325456128 325521664 (1627168607481 / 5000) (8137462056877 / 25000) := by
  exact
    packedTile32768 325456128 325521664 13 3304 18040 28 _ _ (245009 / 12500) (78403 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325521664 :
    ThetaLowerSegment 325521664 325587200 (8137462056877 / 25000) (8139103633927 / 25000) := by
  exact
    packedTile32768 325521664 325587200 13 3350 18042 28 _ _ (490023 / 25000) (392019 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325587200 :
    ThetaLowerSegment 325587200 325652736 (8139103633927 / 25000) (32562951512563 / 100000) := by
  exact
    packedTile32768 325587200 325652736 13 3335 18044 28 _ _ (1960113 / 100000) (490029 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325652736 :
    ThetaLowerSegment 325652736 325718272 (32562951512563 / 100000) (6513893398931 / 20000) := by
  exact
    packedTile32768 325652736 325718272 13 3324 18045 28 _ _ (1960133 / 100000) (245017 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325718272 :
    ThetaLowerSegment 325718272 325783808 (6513893398931 / 20000) (16288005972761 / 50000) := by
  exact
    packedTile32768 325718272 325783808 13 3339 18047 28 _ _ (1960153 / 100000) (490039 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325783808 :
    ThetaLowerSegment 325783808 325849344 (16288005972761 / 50000) (16291220656481 / 50000) := by
  exact
    packedTile32768 325783808 325849344 13 3280 18049 28 _ _ (1960173 / 100000) (122511 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325849344 :
    ThetaLowerSegment 325849344 325882112 (16291220656481 / 50000) (32585889292449 / 100000) := by
  exact
    packedTile32768 325849344 325882112 12 1759 18051 28 _ _ (1960193 / 100000) (490049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325882112 :
    ThetaLowerSegment 325882112 325947648 (32585889292449 / 100000) (32592463813311 / 100000) := by
  exact
    packedTile32768 325882112 325947648 13 3354 18052 28 _ _ (1960203 / 100000) (980103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell325947648 :
    ThetaLowerSegment 325947648 326013184 (32592463813311 / 100000) (8149740488139 / 25000) := by
  exact
    packedTile32768 325947648 326013184 13 3315 18054 28 _ _ (1960223 / 100000) (980113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326013184 :
    ThetaLowerSegment 326013184 326078720 (8149740488139 / 25000) (32605562090737 / 100000) := by
  exact
    packedTile32768 326013184 326078720 13 3367 18055 28 _ _ (1960243 / 100000) (980123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326078720 :
    ThetaLowerSegment 326078720 326144256 (32605562090737 / 100000) (6522439908251 / 20000) := by
  exact
    packedTile32768 326078720 326144256 13 3386 18057 28 _ _ (1960263 / 100000) (980133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326144256 :
    ThetaLowerSegment 326144256 326209792 (6522439908251 / 20000) (32618889990547 / 100000) := by
  exact
    packedTile32768 326144256 326209792 13 3413 18059 28 _ _ (490071 / 25000) (1960287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326209792 :
    ThetaLowerSegment 326209792 326275328 (32618889990547 / 100000) (1305016868939 / 4000) := by
  exact
    packedTile32768 326209792 326275328 13 3332 18061 28 _ _ (122519 / 6250) (1960307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326275328 :
    ThetaLowerSegment 326275328 326340864 (1305016868939 / 4000) (6526389920479 / 20000) := by
  exact
    packedTile32768 326275328 326340864 13 3330 18063 28 _ _ (490081 / 25000) (1960327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326340864 :
    ThetaLowerSegment 326340864 326406400 (6526389920479 / 20000) (6527683747519 / 20000) := by
  exact
    packedTile32768 326340864 326406400 13 3300 18064 28 _ _ (245043 / 12500) (1960347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326406400 :
    ThetaLowerSegment 326406400 326471936 (6527683747519 / 20000) (32644964392991 / 100000) := by
  exact
    packedTile32768 326406400 326471936 13 3339 18066 28 _ _ (490091 / 25000) (1960367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326471936 :
    ThetaLowerSegment 326471936 326537472 (32644964392991 / 100000) (32651561085151 / 100000) := by
  exact
    packedTile32768 326471936 326537472 13 3365 18068 28 _ _ (61262 / 3125) (1960387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326537472 :
    ThetaLowerSegment 326537472 326603008 (32651561085151 / 100000) (1306325608039 / 4000) := by
  exact
    packedTile32768 326537472 326603008 13 3356 18070 28 _ _ (490101 / 25000) (1960407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326603008 :
    ThetaLowerSegment 326603008 326668544 (1306325608039 / 4000) (6532929761731 / 20000) := by
  exact
    packedTile32768 326603008 326668544 13 3320 18072 28 _ _ (245053 / 12500) (1960427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326668544 :
    ThetaLowerSegment 326668544 326734080 (6532929761731 / 20000) (32671182968507 / 100000) := by
  exact
    packedTile32768 326668544 326734080 13 3333 18073 28 _ _ (490111 / 25000) (1960447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326734080 :
    ThetaLowerSegment 326734080 326799616 (32671182968507 / 100000) (32677621132283 / 100000) := by
  exact
    packedTile32768 326734080 326799616 13 3284 18075 28 _ _ (122529 / 6250) (1960467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326799616 :
    ThetaLowerSegment 326799616 326865152 (32677621132283 / 100000) (32684163267391 / 100000) := by
  exact
    packedTile32768 326799616 326865152 13 3337 18077 28 _ _ (490121 / 25000) (1960487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326865152 :
    ThetaLowerSegment 326865152 326930688 (32684163267391 / 100000) (32690774086879 / 100000) := by
  exact
    packedTile32768 326865152 326930688 13 3372 18079 28 _ _ (245063 / 12500) (1960507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326930688 :
    ThetaLowerSegment 326930688 326996224 (32690774086879 / 100000) (32697334000183 / 100000) := by
  exact
    packedTile32768 326930688 326996224 13 3346 18081 28 _ _ (490131 / 25000) (1960527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell326996224 :
    ThetaLowerSegment 326996224 327061760 (32697334000183 / 100000) (6540775659211 / 20000) := by
  exact
    packedTile32768 326996224 327061760 13 3338 18083 28 _ _ (61267 / 3125) (1960547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327061760 :
    ThetaLowerSegment 327061760 327127296 (6540775659211 / 20000) (32710471672787 / 100000) := by
  exact
    packedTile32768 327061760 327127296 13 3363 18084 28 _ _ (490141 / 25000) (1960567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327127296 :
    ThetaLowerSegment 327127296 327192832 (32710471672787 / 100000) (32716996496339 / 100000) := by
  exact
    packedTile32768 327127296 327192832 13 3328 18086 28 _ _ (245073 / 12500) (1960587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327192832 :
    ThetaLowerSegment 327192832 327258368 (32716996496339 / 100000) (16361759714587 / 50000) := by
  exact
    packedTile32768 327192832 327258368 13 3327 18088 28 _ _ (392121 / 20000) (61269 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327258368 :
    ThetaLowerSegment 327258368 327323904 (16361759714587 / 50000) (2045630960339 / 6250) := by
  exact
    packedTile32768 327258368 327323904 13 3354 18090 28 _ _ (3137 / 160) (490157 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327323904 :
    ThetaLowerSegment 327323904 327389440 (2045630960339 / 6250) (32736598824889 / 100000) := by
  exact
    packedTile32768 327323904 327389440 13 3317 18092 28 _ _ (392129 / 20000) (245081 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327389440 :
    ThetaLowerSegment 327389440 327454976 (32736598824889 / 100000) (16371539411357 / 50000) := by
  exact
    packedTile32768 327389440 327454976 13 3305 18093 28 _ _ (392133 / 20000) (490167 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327454976 :
    ThetaLowerSegment 327454976 327520512 (16371539411357 / 50000) (16374845126267 / 50000) := by
  exact
    packedTile32768 327454976 327520512 13 3372 18095 28 _ _ (392137 / 20000) (122543 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327520512 :
    ThetaLowerSegment 327520512 327586048 (16374845126267 / 50000) (16378131267847 / 50000) := by
  exact
    packedTile32768 327520512 327586048 13 3352 18097 28 _ _ (392141 / 20000) (490177 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327586048 :
    ThetaLowerSegment 327586048 327651584 (16378131267847 / 50000) (32762821160819 / 100000) := by
  exact
    packedTile32768 327586048 327651584 13 3345 18099 28 _ _ (78429 / 4000) (245091 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327651584 :
    ThetaLowerSegment 327651584 327717120 (32762821160819 / 100000) (16384742866537 / 50000) := by
  exact
    packedTile32768 327651584 327717120 13 3399 18101 28 _ _ (392149 / 20000) (490187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327717120 :
    ThetaLowerSegment 327717120 327782656 (16384742866537 / 50000) (32776068021179 / 100000) := by
  exact
    packedTile32768 327717120 327782656 13 3357 18102 28 _ _ (392153 / 20000) (61274 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327782656 :
    ThetaLowerSegment 327782656 327848192 (32776068021179 / 100000) (2048908785779 / 6250) := by
  exact
    packedTile32768 327782656 327848192 13 3301 18104 28 _ _ (392157 / 20000) (490197 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327848192 :
    ThetaLowerSegment 327848192 327913728 (2048908785779 / 6250) (32789232799929 / 100000) := by
  exact
    packedTile32768 327848192 327913728 13 3413 18106 28 _ _ (392161 / 20000) (245101 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327913728 :
    ThetaLowerSegment 327913728 327979264 (32789232799929 / 100000) (8198964606901 / 25000) := by
  exact
    packedTile32768 327913728 327979264 13 3379 18108 28 _ _ (78433 / 4000) (490207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell327979264 :
    ThetaLowerSegment 327979264 328044800 (8198964606901 / 25000) (32802335098639 / 100000) := by
  exact
    packedTile32768 327979264 328044800 13 3303 18110 28 _ _ (392169 / 20000) (122553 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328044800 :
    ThetaLowerSegment 328044800 328110336 (32802335098639 / 100000) (8202209821961 / 25000) := by
  exact
    packedTile32768 328044800 328110336 13 3317 18112 28 _ _ (392173 / 20000) (490217 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328110336 :
    ThetaLowerSegment 328110336 328175872 (8202209821961 / 25000) (16407692360987 / 50000) := by
  exact
    packedTile32768 328110336 328175872 13 3338 18113 28 _ _ (392177 / 20000) (245111 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328175872 :
    ThetaLowerSegment 328175872 328241408 (16407692360987 / 50000) (8205515891101 / 25000) := by
  exact
    packedTile32768 328175872 328241408 13 3406 18115 28 _ _ (392181 / 20000) (490227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328241408 :
    ThetaLowerSegment 328241408 328306944 (8205515891101 / 25000) (4103582268977 / 12500) := by
  exact
    packedTile32768 328241408 328306944 13 3363 18117 28 _ _ (490231 / 25000) (1960927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328306944 :
    ThetaLowerSegment 328306944 328372480 (4103582268977 / 12500) (4104379392713 / 12500) := by
  exact
    packedTile32768 328306944 328372480 13 3252 18119 28 _ _ (122559 / 6250) (1960947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328372480 :
    ThetaLowerSegment 328372480 328438016 (4104379392713 / 12500) (4105201036629 / 12500) := by
  exact
    packedTile32768 328372480 328438016 13 3352 18121 28 _ _ (490241 / 25000) (1960967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328438016 :
    ThetaLowerSegment 328438016 328503552 (4105201036629 / 12500) (4106016805973 / 12500) := by
  exact
    packedTile32768 328438016 328503552 13 3328 18122 28 _ _ (245123 / 12500) (1960987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328503552 :
    ThetaLowerSegment 328503552 328569088 (4106016805973 / 12500) (6570922721 / 20) := by
  exact
    packedTile32768 328503552 328569088 13 3304 18124 28 _ _ (490251 / 25000) (1961007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328569088 :
    ThetaLowerSegment 328569088 328634624 (6570922721 / 20) (4107641996353 / 12500) := by
  exact
    packedTile32768 328569088 328634624 13 3326 18126 28 _ _ (61282 / 3125) (1961027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328634624 :
    ThetaLowerSegment 328634624 328700160 (4107641996353 / 12500) (2054226198893 / 6250) := by
  exact
    packedTile32768 328634624 328700160 13 3306 18128 28 _ _ (490261 / 25000) (1961047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328700160 :
    ThetaLowerSegment 328700160 328765696 (2054226198893 / 6250) (4109254227829 / 12500) := by
  exact
    packedTile32768 328700160 328765696 13 3271 18130 28 _ _ (245133 / 12500) (1961067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328765696 :
    ThetaLowerSegment 328765696 328798464 (4109254227829 / 12500) (1643867108567 / 5000) := by
  exact
    packedTile32768 328765696 328798464 12 1687 18131 28 _ _ (490271 / 25000) (1961087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328798464 :
    ThetaLowerSegment 328798464 328864000 (1643867108567 / 5000) (8220978939607 / 25000) := by
  exact
    packedTile32768 328798464 328864000 13 3352 18132 28 _ _ (980547 / 50000) (1961097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328864000 :
    ThetaLowerSegment 328864000 328929536 (8220978939607 / 25000) (8222614508683 / 25000) := by
  exact
    packedTile32768 328864000 328929536 13 3336 18134 28 _ _ (980557 / 50000) (1961117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328929536 :
    ThetaLowerSegment 328929536 328995072 (8222614508683 / 25000) (3289710039559 / 10000) := by
  exact
    packedTile32768 328929536 328995072 13 3387 18136 28 _ _ (980567 / 50000) (1961137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell328995072 :
    ThetaLowerSegment 328995072 329060608 (3289710039559 / 10000) (16451841014207 / 50000) := by
  exact
    packedTile32768 328995072 329060608 13 3356 18138 28 _ _ (980577 / 50000) (1961157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329060608 :
    ThetaLowerSegment 329060608 329126144 (16451841014207 / 50000) (131641117671 / 400) := by
  exact
    packedTile32768 329060608 329126144 13 3364 18140 28 _ _ (980587 / 50000) (1961177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329126144 :
    ThetaLowerSegment 329126144 329191680 (131641117671 / 400) (16458352144647 / 50000) := by
  exact
    packedTile32768 329126144 329191680 13 3276 18141 28 _ _ (980597 / 50000) (1961197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329191680 :
    ThetaLowerSegment 329191680 329257216 (16458352144647 / 50000) (2057703789231 / 6250) := by
  exact
    packedTile32768 329191680 329257216 13 3343 18143 28 _ _ (980607 / 50000) (1961217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329257216 :
    ThetaLowerSegment 329257216 329322752 (2057703789231 / 6250) (32929773882489 / 100000) := by
  exact
    packedTile32768 329257216 329322752 13 3321 18145 28 _ _ (1961233 / 100000) (490309 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329322752 :
    ThetaLowerSegment 329322752 329339136 (32929773882489 / 100000) (4116426441093 / 12500) := by
  exact
    packedTile32768 329322752 329339136 11 835 18147 28 _ _ (1961253 / 100000) (245157 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329339136 :
    ThetaLowerSegment 329339136 329341184 (4116426441093 / 12500) (2058225478409 / 6250) := by
  exact
    packedTile32768 329339136 329341184 8 100 18147 28 _ _ (980629 / 50000) (1961261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_297341184_329341184 :
    ThetaLowerSegment 297341184 329341184 (7433021829089 / 25000) (2058225478409 / 6250) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell297341184 cell297406720)
                      (ThetaLowerSegment.join cell297472256 cell297505024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell297537792 cell297570560)
                      (ThetaLowerSegment.join cell297603328 cell297636096)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell297668864 cell297701632)
                      (ThetaLowerSegment.join cell297734400 cell297767168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell297799936 cell297832704)
                      (ThetaLowerSegment.join cell297865472 cell297898240))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell297931008 cell297996544)
                      (ThetaLowerSegment.join cell298062080 cell298127616))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell298193152 cell298225920)
                      (ThetaLowerSegment.join cell298258688 cell298291456)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell298324224 cell298356992)
                      (ThetaLowerSegment.join cell298422528 cell298488064))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell298553600 cell298619136)
                      (ThetaLowerSegment.join cell298651904 cell298717440)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell298750208 cell298782976)
                      (ThetaLowerSegment.join cell298815744 cell298848512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell298881280 cell298914048)
                      (ThetaLowerSegment.join cell298946816 cell298979584)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell299012352 cell299045120)
                      (ThetaLowerSegment.join cell299077888 cell299110656))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell299143424 cell299176192)
                      (ThetaLowerSegment.join cell299208960 cell299241728))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell299274496 cell299307264)
                      (ThetaLowerSegment.join cell299340032 cell299372800))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell299405568 cell299438336)
                      (ThetaLowerSegment.join cell299471104 cell299503872)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell299536640 cell299569408)
                      (ThetaLowerSegment.join cell299602176 cell299634944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell299667712 cell299700480)
                      (ThetaLowerSegment.join cell299733248 cell299766016))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell299798784 cell299831552)
                      (ThetaLowerSegment.join cell299864320 cell299897088))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell299929856 cell299962624)
                      (ThetaLowerSegment.join cell300028160 cell300060928)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell300093696 cell300159232)
                      (ThetaLowerSegment.join cell300192000 cell300224768))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell300257536 cell300290304)
                      (ThetaLowerSegment.join cell300355840 cell300388608))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell300421376 cell300486912)
                      (ThetaLowerSegment.join cell300519680 cell300552448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell300585216 cell300650752)
                      (ThetaLowerSegment.join cell300683520 cell300716288)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell300749056 cell300781824)
                      (ThetaLowerSegment.join cell300814592 cell300880128))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell300945664 cell301011200)
                      (ThetaLowerSegment.join cell301076736 cell301142272)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell301207808 cell301273344)
                      (ThetaLowerSegment.join cell301338880 cell301404416))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell301469952 cell301535488)
                      (ThetaLowerSegment.join cell301601024 cell301666560)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell301732096 cell301797632)
                      (ThetaLowerSegment.join cell301863168 cell301928704))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell301994240 cell302059776)
                      (ThetaLowerSegment.join cell302125312 cell302190848))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell302256384 cell302321920)
                      (ThetaLowerSegment.join cell302387456 cell302452992))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell302518528 cell302584064)
                      (ThetaLowerSegment.join cell302649600 cell302715136)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell302780672 cell302846208)
                      (ThetaLowerSegment.join cell302911744 cell302944512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell303010048 cell303075584)
                      (ThetaLowerSegment.join cell303108352 cell303141120)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell303206656 cell303239424)
                      (ThetaLowerSegment.join cell303272192 cell303337728))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell303403264 cell303468800)
                      (ThetaLowerSegment.join cell303501568 cell303534336)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell303567104 cell303632640)
                      (ThetaLowerSegment.join cell303665408 cell303698176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell303730944 cell303763712)
                      (ThetaLowerSegment.join cell303796480 cell303829248))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell303862016 cell303894784)
                      (ThetaLowerSegment.join cell303927552 cell303960320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell303993088 cell304025856)
                      (ThetaLowerSegment.join cell304058624 cell304091392)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell304124160 cell304156928)
                      (ThetaLowerSegment.join cell304189696 cell304222464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell304255232 cell304288000)
                      (ThetaLowerSegment.join cell304320768 cell304353536)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell304386304 cell304419072)
                      (ThetaLowerSegment.join cell304451840 cell304484608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell304517376 cell304550144)
                      (ThetaLowerSegment.join cell304582912 cell304615680)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell304648448 cell304681216)
                      (ThetaLowerSegment.join cell304713984 cell304746752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell304779520 cell304845056)
                      (ThetaLowerSegment.join cell304877824 cell304910592))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell304976128 cell305041664)
                      (ThetaLowerSegment.join cell305107200 cell305172736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell305238272 cell305303808)
                      (ThetaLowerSegment.join cell305336576 cell305369344)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell305402112 cell305434880)
                      (ThetaLowerSegment.join cell305467648 cell305500416))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell305533184 cell305565952)
                      (ThetaLowerSegment.join cell305631488 cell305697024))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell305762560 cell305828096)
                      (ThetaLowerSegment.join cell305893632 cell305959168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell306024704 cell306090240)
                      (ThetaLowerSegment.join cell306155776 cell306221312)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell306286848 cell306352384)
                      (ThetaLowerSegment.join cell306417920 cell306483456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell306548992 cell306614528)
                      (ThetaLowerSegment.join cell306680064 cell306745600))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell306811136 cell306876672)
                      (ThetaLowerSegment.join cell306942208 cell307007744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell307073280 cell307138816)
                      (ThetaLowerSegment.join cell307204352 cell307269888)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell307335424 cell307400960)
                      (ThetaLowerSegment.join cell307466496 cell307532032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell307597568 cell307663104)
                      (ThetaLowerSegment.join cell307728640 cell307794176)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell307859712 cell307925248)
                      (ThetaLowerSegment.join cell307990784 cell308056320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell308121856 cell308187392)
                      (ThetaLowerSegment.join cell308252928 cell308318464)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell308384000 cell308449536)
                      (ThetaLowerSegment.join cell308515072 cell308580608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell308646144 cell308711680)
                      (ThetaLowerSegment.join cell308777216 cell308842752))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell308908288 cell308973824)
                      (ThetaLowerSegment.join cell309039360 cell309104896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell309170432 cell309235968)
                      (ThetaLowerSegment.join cell309301504 cell309367040)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell309432576 cell309498112)
                      (ThetaLowerSegment.join cell309563648 cell309629184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell309694720 cell309760256)
                      (ThetaLowerSegment.join cell309825792 cell309891328))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell309956864 cell310022400)
                      (ThetaLowerSegment.join cell310087936 cell310153472))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell310219008 cell310284544)
                      (ThetaLowerSegment.join cell310350080 cell310415616)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell310481152 cell310546688)
                      (ThetaLowerSegment.join cell310612224 cell310677760))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell310743296 cell310808832)
                      (ThetaLowerSegment.join cell310874368 cell310939904))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell311005440 cell311070976)
                      (ThetaLowerSegment.join cell311136512 cell311202048))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell311267584 cell311333120)
                      (ThetaLowerSegment.join cell311398656 cell311464192)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell311529728 cell311595264)
                      (ThetaLowerSegment.join cell311660800 cell311726336))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell311791872 cell311857408)
                      (ThetaLowerSegment.join cell311922944 cell311988480)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell312054016 cell312119552)
                      (ThetaLowerSegment.join cell312185088 cell312250624))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell312316160 cell312381696)
                      (ThetaLowerSegment.join cell312447232 cell312512768)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell312578304 cell312643840)
                      (ThetaLowerSegment.join cell312709376 cell312774912))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell312840448 cell312905984)
                      (ThetaLowerSegment.join cell312971520 cell313037056))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell313102592 cell313168128)
                      (ThetaLowerSegment.join cell313233664 cell313299200))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell313364736 cell313430272)
                      (ThetaLowerSegment.join cell313495808 cell313561344)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell313626880 cell313692416)
                      (ThetaLowerSegment.join cell313757952 cell313823488))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell313889024 cell313954560)
                      (ThetaLowerSegment.join cell314020096 cell314085632))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell314151168 cell314216704)
                      (ThetaLowerSegment.join cell314282240 cell314347776))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell314413312 cell314478848)
                      (ThetaLowerSegment.join cell314544384 cell314609920)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell314675456 cell314740992)
                      (ThetaLowerSegment.join cell314806528 cell314872064))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell314937600 cell315003136)
                      (ThetaLowerSegment.join cell315068672 cell315134208))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell315199744 cell315265280)
                      (ThetaLowerSegment.join cell315330816 cell315396352))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell315461888 cell315527424)
                      (ThetaLowerSegment.join cell315592960 cell315658496)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell315724032 cell315789568)
                      (ThetaLowerSegment.join cell315855104 cell315920640))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell315986176 cell316051712)
                      (ThetaLowerSegment.join cell316117248 cell316182784)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell316248320 cell316313856)
                      (ThetaLowerSegment.join cell316379392 cell316444928))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell316510464 cell316576000)
                      (ThetaLowerSegment.join cell316641536 cell316707072)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell316772608 cell316838144)
                      (ThetaLowerSegment.join cell316903680 cell316969216))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell317034752 cell317100288)
                      (ThetaLowerSegment.join cell317165824 cell317231360))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell317296896 cell317362432)
                      (ThetaLowerSegment.join cell317427968 cell317493504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell317559040 cell317624576)
                      (ThetaLowerSegment.join cell317690112 cell317755648)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell317821184 cell317886720)
                      (ThetaLowerSegment.join cell317952256 cell318017792))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell318083328 cell318148864)
                      (ThetaLowerSegment.join cell318214400 cell318279936)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell318345472 cell318411008)
                      (ThetaLowerSegment.join cell318476544 cell318542080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell318607616 cell318673152)
                      (ThetaLowerSegment.join cell318738688 cell318804224)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell318869760 cell318935296)
                      (ThetaLowerSegment.join cell319000832 cell319066368))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell319131904 cell319197440)
                      (ThetaLowerSegment.join cell319262976 cell319328512))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell319394048 cell319459584)
                      (ThetaLowerSegment.join cell319525120 cell319590656))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell319656192 cell319721728)
                      (ThetaLowerSegment.join cell319787264 cell319852800)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell319918336 cell319983872)
                      (ThetaLowerSegment.join cell320049408 cell320114944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell320180480 cell320246016)
                      (ThetaLowerSegment.join cell320311552 cell320377088)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell320442624 cell320508160)
                      (ThetaLowerSegment.join cell320573696 cell320639232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell320704768 cell320770304)
                      (ThetaLowerSegment.join cell320835840 cell320901376)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell320966912 cell321032448)
                      (ThetaLowerSegment.join cell321097984 cell321163520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell321229056 cell321294592)
                      (ThetaLowerSegment.join cell321360128 cell321425664))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell321491200 cell321556736)
                      (ThetaLowerSegment.join cell321622272 cell321687808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell321753344 cell321818880)
                      (ThetaLowerSegment.join cell321851648 cell321884416)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell321917184 cell321949952)
                      (ThetaLowerSegment.join cell321982720 cell322015488))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell322048256 cell322081024)
                      (ThetaLowerSegment.join cell322113792 cell322146560))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell322212096 cell322244864)
                      (ThetaLowerSegment.join cell322277632 cell322310400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell322343168 cell322375936)
                      (ThetaLowerSegment.join cell322408704 cell322441472)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell322474240 cell322539776)
                      (ThetaLowerSegment.join cell322605312 cell322670848))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell322703616 cell322769152)
                      (ThetaLowerSegment.join cell322834688 cell322900224))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell322932992 cell322965760)
                      (ThetaLowerSegment.join cell323031296 cell323096832))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell323162368 cell323227904)
                      (ThetaLowerSegment.join cell323260672 cell323293440)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell323358976 cell323424512)
                      (ThetaLowerSegment.join cell323457280 cell323490048))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell323522816 cell323555584)
                      (ThetaLowerSegment.join cell323588352 cell323621120)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell323686656 cell323752192)
                      (ThetaLowerSegment.join cell323817728 cell323883264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell323948800 cell324014336)
                      (ThetaLowerSegment.join cell324079872 cell324145408)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell324210944 cell324276480)
                      (ThetaLowerSegment.join cell324342016 cell324407552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell324440320 cell324473088)
                      (ThetaLowerSegment.join cell324505856 cell324538624))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell324571392 cell324604160)
                      (ThetaLowerSegment.join cell324636928 cell324669696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell324735232 cell324768000)
                      (ThetaLowerSegment.join cell324800768 cell324833536)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell324866304 cell324899072)
                      (ThetaLowerSegment.join cell324931840 cell324997376))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell325062912 cell325128448)
                      (ThetaLowerSegment.join cell325193984 cell325259520)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell325325056 cell325390592)
                (ThetaLowerSegment.join cell325456128 cell325521664))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell325587200 cell325652736)
                (ThetaLowerSegment.join cell325718272 cell325783808)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell325849344 cell325882112)
                (ThetaLowerSegment.join cell325947648 cell326013184))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell326078720 cell326144256)
                (ThetaLowerSegment.join cell326209792 cell326275328))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell326340864 cell326406400)
                (ThetaLowerSegment.join cell326471936 cell326537472))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell326603008 cell326668544)
                (ThetaLowerSegment.join cell326734080 cell326799616)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell326865152 cell326930688)
                (ThetaLowerSegment.join cell326996224 cell327061760))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell327127296 cell327192832)
                (ThetaLowerSegment.join cell327258368 cell327323904)))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell327389440 cell327454976)
                (ThetaLowerSegment.join cell327520512 cell327586048))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell327651584 cell327717120)
                (ThetaLowerSegment.join cell327782656 cell327848192)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell327913728 cell327979264)
                (ThetaLowerSegment.join cell328044800 cell328110336))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell328175872 cell328241408)
                (ThetaLowerSegment.join cell328306944 cell328372480))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell328438016 cell328503552)
                (ThetaLowerSegment.join cell328569088 cell328634624))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell328700160 cell328765696)
                (ThetaLowerSegment.join cell328798464 cell328864000)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell328929536 cell328995072)
                (ThetaLowerSegment.join cell329060608 cell329126144))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell329191680 cell329257216)
                (ThetaLowerSegment.join cell329322752 cell329339136)))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
