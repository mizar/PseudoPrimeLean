/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis16384

/-! # Direct theta estimate up to 152170752 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell128917760 :
    ThetaLowerSegment 128917760 128950528 (1611321991643 / 12500) (6446933204999 / 50000) := by
  exact
    packedTile16384 128917760 128950528 12 1762 11354 27 _ _ (1867467 / 100000) (186747 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128950528 :
    ThetaLowerSegment 128950528 128983296 (6446933204999 / 50000) (6448599007863 / 50000) := by
  exact
    packedTile16384 128950528 128983296 12 1784 11355 27 _ _ (466873 / 25000) (373499 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128983296 :
    ThetaLowerSegment 128983296 129016064 (6448599007863 / 50000) (6450229351077 / 50000) := by
  exact
    packedTile16384 128983296 129016064 12 1746 11357 27 _ _ (933759 / 50000) (1867521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129016064 :
    ThetaLowerSegment 129016064 129048832 (6450229351077 / 50000) (2580736789783 / 20000) := by
  exact
    packedTile16384 129016064 129048832 12 1727 11358 27 _ _ (1867543 / 100000) (933773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129048832 :
    ThetaLowerSegment 129048832 129081600 (2580736789783 / 20000) (6453491971669 / 50000) := by
  exact
    packedTile16384 129048832 129081600 12 1767 11359 27 _ _ (1867569 / 100000) (466893 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129081600 :
    ThetaLowerSegment 129081600 129114368 (6453491971669 / 50000) (403441238552 / 3125) := by
  exact
    packedTile16384 129081600 129114368 12 1679 11361 27 _ _ (933797 / 50000) (1867597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129114368 :
    ThetaLowerSegment 129114368 129147136 (403441238552 / 3125) (6456723865361 / 50000) := by
  exact
    packedTile16384 129114368 129147136 12 1782 11362 27 _ _ (1867619 / 100000) (933811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129147136 :
    ThetaLowerSegment 129147136 129179904 (6456723865361 / 50000) (6458378598831 / 50000) := by
  exact
    packedTile16384 129147136 129179904 12 1772 11364 27 _ _ (373529 / 20000) (58364 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129179904 :
    ThetaLowerSegment 129179904 129212672 (6458378598831 / 50000) (6460044560471 / 50000) := by
  exact
    packedTile16384 129179904 129212672 12 1784 11365 27 _ _ (186767 / 10000) (1867673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129212672 :
    ThetaLowerSegment 129212672 129245440 (6460044560471 / 50000) (6461675992927 / 50000) := by
  exact
    packedTile16384 129212672 129245440 12 1747 11367 27 _ _ (116731 / 6250) (1867699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129245440 :
    ThetaLowerSegment 129245440 129278208 (6461675992927 / 50000) (12926618629883 / 100000) := by
  exact
    packedTile16384 129245440 129278208 12 1749 11368 27 _ _ (1867721 / 100000) (466931 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129278208 :
    ThetaLowerSegment 129278208 129310976 (12926618629883 / 100000) (12929913333827 / 100000) := by
  exact
    packedTile16384 129278208 129310976 12 1764 11370 27 _ _ (933873 / 50000) (1867749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129310976 :
    ThetaLowerSegment 129310976 129343744 (12929913333827 / 100000) (12933168860423 / 100000) := by
  exact
    packedTile16384 129310976 129343744 12 1743 11371 27 _ _ (466943 / 25000) (74711 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129343744 :
    ThetaLowerSegment 129343744 129376512 (12933168860423 / 100000) (12936478596707 / 100000) := by
  exact
    packedTile16384 129343744 129376512 12 1772 11372 27 _ _ (1867797 / 100000) (9339 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129376512 :
    ThetaLowerSegment 129376512 129409280 (12936478596707 / 100000) (12939788377291 / 100000) := by
  exact
    packedTile16384 129376512 129409280 12 1772 11374 27 _ _ (933911 / 50000) (74713 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129409280 :
    ThetaLowerSegment 129409280 129442048 (12939788377291 / 100000) (12943088864707 / 100000) := by
  exact
    packedTile16384 129409280 129442048 12 1767 11375 27 _ _ (233481 / 12500) (1867851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129442048 :
    ThetaLowerSegment 129442048 129474816 (12943088864707 / 100000) (12946421150139 / 100000) := by
  exact
    packedTile16384 129442048 129474816 12 1784 11377 27 _ _ (1867873 / 100000) (466969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129474816 :
    ThetaLowerSegment 129474816 129507584 (12946421150139 / 100000) (12949706782721 / 100000) := by
  exact
    packedTile16384 129474816 129507584 12 1759 11378 27 _ _ (933949 / 50000) (1867901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129507584 :
    ThetaLowerSegment 129507584 129540352 (12949706782721 / 100000) (12952927083697 / 100000) := by
  exact
    packedTile16384 129507584 129540352 12 1724 11380 27 _ _ (466981 / 25000) (1867927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129540352 :
    ThetaLowerSegment 129540352 129573120 (12952927083697 / 100000) (6478112006841 / 50000) := by
  exact
    packedTile16384 129540352 129573120 12 1765 11381 27 _ _ (1867949 / 100000) (116747 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129573120 :
    ThetaLowerSegment 129573120 129605888 (6478112006841 / 50000) (809968193763 / 6250) := by
  exact
    packedTile16384 129573120 129605888 12 1749 11383 27 _ _ (933987 / 50000) (1867977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129605888 :
    ThetaLowerSegment 129605888 129638656 (809968193763 / 6250) (12962758230459 / 100000) := by
  exact
    packedTile16384 129605888 129638656 12 1749 11384 27 _ _ (1867999 / 100000) (934001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129638656 :
    ThetaLowerSegment 129638656 129671424 (12962758230459 / 100000) (6483010835067 / 50000) := by
  exact
    packedTile16384 129638656 129671424 12 1747 11385 27 _ _ (74721 / 4000) (467007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129671424 :
    ThetaLowerSegment 129671424 129704192 (6483010835067 / 50000) (1621162045223 / 12500) := by
  exact
    packedTile16384 129671424 129704192 12 1753 11387 27 _ _ (37361 / 2000) (1868053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129704192 :
    ThetaLowerSegment 129704192 129736960 (1621162045223 / 12500) (12972619667209 / 100000) := by
  exact
    packedTile16384 129704192 129736960 12 1779 11388 27 _ _ (74723 / 4000) (934039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129736960 :
    ThetaLowerSegment 129736960 129769728 (12972619667209 / 100000) (12975982247209 / 100000) := by
  exact
    packedTile16384 129736960 129769728 12 1800 11390 27 _ _ (18681 / 1000) (1868103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129769728 :
    ThetaLowerSegment 129769728 129802496 (12975982247209 / 100000) (2595839458411 / 20000) := by
  exact
    packedTile16384 129769728 129802496 12 1721 11391 27 _ _ (934063 / 50000) (1868129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129802496 :
    ThetaLowerSegment 129802496 129835264 (2595839458411 / 20000) (3245622710567 / 25000) := by
  exact
    packedTile16384 129802496 129835264 12 1763 11393 27 _ _ (1868151 / 100000) (934077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129835264 :
    ThetaLowerSegment 129835264 129868032 (3245622710567 / 25000) (3246433031907 / 25000) := by
  exact
    packedTile16384 129835264 129868032 12 1735 11394 27 _ _ (116761 / 6250) (1868179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129868032 :
    ThetaLowerSegment 129868032 129900800 (3246433031907 / 25000) (2597784229347 / 20000) := by
  exact
    packedTile16384 129868032 129900800 12 1707 11395 27 _ _ (1868201 / 100000) (467051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129900800 :
    ThetaLowerSegment 129900800 129933568 (2597784229347 / 20000) (649608126029 / 5000) := by
  exact
    packedTile16384 129900800 129933568 12 1735 11397 27 _ _ (1868227 / 100000) (186823 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129933568 :
    ThetaLowerSegment 129933568 129966336 (649608126029 / 5000) (3248852385639 / 25000) := by
  exact
    packedTile16384 129933568 129966336 12 1738 11398 27 _ _ (467063 / 25000) (373651 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129966336 :
    ThetaLowerSegment 129966336 129999104 (3248852385639 / 25000) (12998658476259 / 100000) := by
  exact
    packedTile16384 129966336 129999104 12 1739 11400 27 _ _ (1868277 / 100000) (46707 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell129999104 :
    ThetaLowerSegment 129999104 130031872 (12998658476259 / 100000) (2600386721933 / 20000) := by
  exact
    packedTile16384 129999104 130031872 12 1753 11401 27 _ _ (934151 / 50000) (373661 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130031872 :
    ThetaLowerSegment 130031872 130064640 (2600386721933 / 20000) (13005190105369 / 100000) := by
  exact
    packedTile16384 130031872 130064640 12 1743 11403 27 _ _ (233541 / 12500) (1868331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130064640 :
    ThetaLowerSegment 130064640 130097408 (13005190105369 / 100000) (13008396199117 / 100000) := by
  exact
    packedTile16384 130064640 130097408 12 1716 11404 27 _ _ (1868353 / 100000) (467089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130097408 :
    ThetaLowerSegment 130097408 130130176 (13008396199117 / 100000) (13011678939263 / 100000) := by
  exact
    packedTile16384 130097408 130130176 12 1757 11406 27 _ _ (934189 / 50000) (1868381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130130176 :
    ThetaLowerSegment 130130176 130162944 (13011678939263 / 100000) (13014948644513 / 100000) := by
  exact
    packedTile16384 130130176 130162944 12 1750 11407 27 _ _ (1868403 / 100000) (934203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130162944 :
    ThetaLowerSegment 130162944 130195712 (13014948644513 / 100000) (2603639568161 / 20000) := by
  exact
    packedTile16384 130162944 130195712 12 1739 11408 27 _ _ (467107 / 25000) (1868431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130195712 :
    ThetaLowerSegment 130195712 130228480 (2603639568161 / 20000) (13021475107367 / 100000) := by
  exact
    packedTile16384 130195712 130228480 12 1754 11410 27 _ _ (1868453 / 100000) (233557 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130228480 :
    ThetaLowerSegment 130228480 130261248 (13021475107367 / 100000) (6512349116821 / 50000) := by
  exact
    packedTile16384 130228480 130261248 12 1725 11411 27 _ _ (1868479 / 100000) (934241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130261248 :
    ThetaLowerSegment 130261248 130294016 (6512349116821 / 50000) (6514001808609 / 50000) := by
  exact
    packedTile16384 130261248 130294016 12 1769 11413 27 _ _ (233563 / 12500) (1868507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130294016 :
    ThetaLowerSegment 130294016 130326784 (6514001808609 / 50000) (814453662171 / 6250) := by
  exact
    packedTile16384 130294016 130326784 12 1742 11414 27 _ _ (1868529 / 100000) (467133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130326784 :
    ThetaLowerSegment 130326784 130359552 (814453662171 / 6250) (6517270822057 / 50000) := by
  exact
    packedTile16384 130326784 130359552 12 1757 11416 27 _ _ (934277 / 50000) (1868557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130359552 :
    ThetaLowerSegment 130359552 130392320 (6517270822057 / 50000) (13037824737417 / 100000) := by
  exact
    packedTile16384 130359552 130392320 12 1757 11417 27 _ _ (1868579 / 100000) (934291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130392320 :
    ThetaLowerSegment 130392320 130425088 (13037824737417 / 100000) (13041158326953 / 100000) := by
  exact
    packedTile16384 130392320 130425088 12 1784 11418 27 _ _ (467151 / 25000) (1868607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130425088 :
    ThetaLowerSegment 130425088 130457856 (13041158326953 / 100000) (13044361157059 / 100000) := by
  exact
    packedTile16384 130425088 130457856 12 1714 11420 27 _ _ (1868629 / 100000) (233579 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130457856 :
    ThetaLowerSegment 130457856 130490624 (13044361157059 / 100000) (6523822191947 / 50000) := by
  exact
    packedTile16384 130457856 130490624 12 1757 11421 27 _ _ (373731 / 20000) (934329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130490624 :
    ThetaLowerSegment 130490624 130523392 (6523822191947 / 50000) (6525467564687 / 50000) := by
  exact
    packedTile16384 130490624 130523392 12 1761 11423 27 _ _ (46717 / 2500) (1868683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130523392 :
    ThetaLowerSegment 130523392 130556160 (6525467564687 / 50000) (13054128746219 / 100000) := by
  exact
    packedTile16384 130523392 130556160 12 1709 11424 27 _ _ (373741 / 20000) (467177 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130556160 :
    ThetaLowerSegment 130556160 130588928 (13054128746219 / 100000) (13057445741969 / 100000) := by
  exact
    packedTile16384 130556160 130588928 12 1775 11426 27 _ _ (186873 / 10000) (1868733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130588928 :
    ThetaLowerSegment 130588928 130621696 (13057445741969 / 100000) (13060731013259 / 100000) := by
  exact
    packedTile16384 130588928 130621696 12 1758 11427 27 _ _ (373751 / 20000) (934379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130621696 :
    ThetaLowerSegment 130621696 130654464 (13060731013259 / 100000) (13064001378259 / 100000) := by
  exact
    packedTile16384 130621696 130654464 12 1750 11428 27 _ _ (93439 / 5000) (1868783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130654464 :
    ThetaLowerSegment 130654464 130687232 (13064001378259 / 100000) (13067301687889 / 100000) := by
  exact
    packedTile16384 130654464 130687232 12 1766 11430 27 _ _ (373761 / 20000) (233601 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130687232 :
    ThetaLowerSegment 130687232 130720000 (13067301687889 / 100000) (13070665581889 / 100000) := by
  exact
    packedTile16384 130687232 130720000 12 1800 11431 27 _ _ (186883 / 10000) (1868833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130720000 :
    ThetaLowerSegment 130720000 130752768 (13070665581889 / 100000) (6536972711207 / 50000) := by
  exact
    packedTile16384 130720000 130752768 12 1755 11433 27 _ _ (373771 / 20000) (934429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130752768 :
    ThetaLowerSegment 130752768 130785536 (6536972711207 / 50000) (6538615456727 / 50000) := by
  exact
    packedTile16384 130752768 130785536 12 1758 11434 27 _ _ (23361 / 1250) (1868883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130785536 :
    ThetaLowerSegment 130785536 130818304 (6538615456727 / 50000) (1635056145983 / 12500) := by
  exact
    packedTile16384 130785536 130818304 12 1722 11436 27 _ _ (373781 / 20000) (467227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130818304 :
    ThetaLowerSegment 130818304 130851072 (1635056145983 / 12500) (6541870176797 / 50000) := by
  exact
    packedTile16384 130818304 130851072 12 1761 11437 27 _ _ (186893 / 10000) (1868933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130851072 :
    ThetaLowerSegment 130851072 130883840 (6541870176797 / 50000) (6543546630329 / 50000) := by
  exact
    packedTile16384 130851072 130883840 12 1794 11439 27 _ _ (467239 / 25000) (1868959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130883840 :
    ThetaLowerSegment 130883840 130916608 (6543546630329 / 50000) (3272592863333 / 25000) := by
  exact
    packedTile16384 130883840 130916608 12 1754 11440 27 _ _ (1868981 / 100000) (233623 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130916608 :
    ThetaLowerSegment 130916608 130949376 (3272592863333 / 25000) (130936010957 / 1000) := by
  exact
    packedTile16384 130916608 130949376 12 1728 11441 27 _ _ (934503 / 50000) (1869009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130949376 :
    ThetaLowerSegment 130949376 130982144 (130936010957 / 1000) (6548495758967 / 50000) := by
  exact
    packedTile16384 130949376 130982144 12 1814 11443 27 _ _ (1869031 / 100000) (934517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell130982144 :
    ThetaLowerSegment 130982144 131014912 (6548495758967 / 50000) (6550110623351 / 50000) := by
  exact
    packedTile16384 130982144 131014912 12 1728 11444 27 _ _ (58408 / 3125) (1869059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131014912 :
    ThetaLowerSegment 131014912 131047680 (6550110623351 / 50000) (409484830232 / 3125) := by
  exact
    packedTile16384 131014912 131047680 12 1762 11446 27 _ _ (1869081 / 100000) (467271 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131047680 :
    ThetaLowerSegment 131047680 131080448 (409484830232 / 3125) (6553432937241 / 50000) := by
  exact
    packedTile16384 131047680 131080448 12 1793 11447 27 _ _ (934553 / 50000) (1869109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131080448 :
    ThetaLowerSegment 131080448 131113216 (6553432937241 / 50000) (2622024753963 / 20000) := by
  exact
    packedTile16384 131080448 131113216 12 1743 11449 27 _ _ (1869131 / 100000) (934567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131113216 :
    ThetaLowerSegment 131113216 131145984 (2622024753963 / 20000) (13113434045091 / 100000) := by
  exact
    packedTile16384 131113216 131145984 12 1771 11450 27 _ _ (467289 / 25000) (1869159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131145984 :
    ThetaLowerSegment 131145984 131178752 (13113434045091 / 100000) (1639581363199 / 12500) := by
  exact
    packedTile16384 131145984 131178752 12 1721 11451 27 _ _ (1869181 / 100000) (58412 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131178752 :
    ThetaLowerSegment 131178752 131211520 (1639581363199 / 12500) (6559976896297 / 50000) := by
  exact
    packedTile16384 131178752 131211520 12 1767 11453 27 _ _ (934603 / 50000) (1869209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131211520 :
    ThetaLowerSegment 131211520 131244288 (6559976896297 / 50000) (6561588173419 / 50000) := by
  exact
    packedTile16384 131211520 131244288 12 1724 11454 27 _ _ (1869231 / 100000) (934617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131244288 :
    ThetaLowerSegment 131244288 131277056 (6561588173419 / 50000) (6563228445559 / 50000) := by
  exact
    packedTile16384 131244288 131277056 12 1755 11456 27 _ _ (233657 / 12500) (1869259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131277056 :
    ThetaLowerSegment 131277056 131309824 (6563228445559 / 50000) (13129700093653 / 100000) := by
  exact
    packedTile16384 131277056 131309824 12 1735 11457 27 _ _ (1869281 / 100000) (467321 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131309824 :
    ThetaLowerSegment 131309824 131342592 (13129700093653 / 100000) (13133014373191 / 100000) := by
  exact
    packedTile16384 131309824 131342592 12 1773 11459 27 _ _ (934653 / 50000) (1869309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131342592 :
    ThetaLowerSegment 131342592 131375360 (13133014373191 / 100000) (13136379167191 / 100000) := by
  exact
    packedTile16384 131342592 131375360 12 1800 11460 27 _ _ (186933 / 10000) (1869333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131375360 :
    ThetaLowerSegment 131375360 131408128 (13136379167191 / 100000) (13139665493281 / 100000) := by
  exact
    packedTile16384 131375360 131408128 12 1758 11461 27 _ _ (373871 / 20000) (934679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131408128 :
    ThetaLowerSegment 131408128 131440896 (13139665493281 / 100000) (13142925692001 / 100000) := by
  exact
    packedTile16384 131408128 131440896 12 1744 11463 27 _ _ (93469 / 5000) (1869383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131440896 :
    ThetaLowerSegment 131440896 131473664 (13142925692001 / 100000) (3286542277419 / 25000) := by
  exact
    packedTile16384 131440896 131473664 12 1735 11464 27 _ _ (373881 / 20000) (58419 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131473664 :
    ThetaLowerSegment 131473664 131506432 (3286542277419 / 25000) (3287361087759 / 25000) := by
  exact
    packedTile16384 131473664 131506432 12 1752 11466 27 _ _ (186943 / 10000) (1869433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131506432 :
    ThetaLowerSegment 131506432 131539200 (3287361087759 / 25000) (6576320559543 / 50000) := by
  exact
    packedTile16384 131506432 131539200 12 1710 11467 27 _ _ (373891 / 20000) (934729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131539200 :
    ThetaLowerSegment 131539200 131571968 (6576320559543 / 50000) (6577966636683 / 50000) := by
  exact
    packedTile16384 131539200 131571968 12 1761 11469 27 _ _ (46737 / 2500) (1869483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131571968 :
    ThetaLowerSegment 131571968 131604736 (6577966636683 / 50000) (13159221732661 / 100000) := by
  exact
    packedTile16384 131571968 131604736 12 1759 11470 27 _ _ (373901 / 20000) (467377 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131604736 :
    ThetaLowerSegment 131604736 131637504 (13159221732661 / 100000) (13162480323451 / 100000) := by
  exact
    packedTile16384 131604736 131637504 12 1743 11471 27 _ _ (186953 / 10000) (1869533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131637504 :
    ThetaLowerSegment 131637504 131670272 (13162480323451 / 100000) (13165815609571 / 100000) := by
  exact
    packedTile16384 131637504 131670272 12 1784 11473 27 _ _ (373911 / 20000) (934779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131670272 :
    ThetaLowerSegment 131670272 131703040 (13165815609571 / 100000) (13169145331551 / 100000) := by
  exact
    packedTile16384 131670272 131703040 12 1781 11474 27 _ _ (93479 / 5000) (1869583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131703040 :
    ThetaLowerSegment 131703040 131735808 (13169145331551 / 100000) (411641249018 / 3125) := by
  exact
    packedTile16384 131703040 131735808 12 1805 11476 27 _ _ (373921 / 20000) (233701 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131735808 :
    ThetaLowerSegment 131735808 131768576 (411641249018 / 3125) (13175726382311 / 100000) := by
  exact
    packedTile16384 131735808 131768576 12 1715 11477 27 _ _ (1869629 / 100000) (58426 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131768576 :
    ThetaLowerSegment 131768576 131801344 (13175726382311 / 100000) (2635798159639 / 20000) := by
  exact
    packedTile16384 131768576 131801344 12 1746 11479 27 _ _ (934827 / 50000) (1869657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131801344 :
    ThetaLowerSegment 131801344 131834112 (2635798159639 / 20000) (13182202906717 / 100000) := by
  exact
    packedTile16384 131801344 131834112 12 1718 11480 27 _ _ (1869679 / 100000) (934841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131834112 :
    ThetaLowerSegment 131834112 131866880 (13182202906717 / 100000) (13185443103749 / 100000) := by
  exact
    packedTile16384 131834112 131866880 12 1733 11481 27 _ _ (233713 / 12500) (1869707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131866880 :
    ThetaLowerSegment 131866880 131899648 (13185443103749 / 100000) (1648592429497 / 12500) := by
  exact
    packedTile16384 131866880 131899648 12 1763 11483 27 _ _ (1869729 / 100000) (467433 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131899648 :
    ThetaLowerSegment 131899648 131932416 (1648592429497 / 12500) (1319199467769 / 10000) := by
  exact
    packedTile16384 131899648 131932416 12 1741 11484 27 _ _ (934877 / 50000) (1869757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131932416 :
    ThetaLowerSegment 131932416 131965184 (1319199467769 / 10000) (13195253702487 / 100000) := by
  exact
    packedTile16384 131932416 131965184 12 1743 11486 27 _ _ (1869779 / 100000) (934891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131965184 :
    ThetaLowerSegment 131965184 131997952 (13195253702487 / 100000) (1319854642557 / 10000) := by
  exact
    packedTile16384 131965184 131997952 12 1761 11487 27 _ _ (1869803 / 100000) (934903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell131997952 :
    ThetaLowerSegment 131997952 132030720 (1319854642557 / 10000) (264035811543 / 2000) := by
  exact
    packedTile16384 131997952 132030720 12 1735 11489 27 _ _ (467457 / 25000) (1869831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132030720 :
    ThetaLowerSegment 132030720 132063488 (264035811543 / 2000) (13205068429459 / 100000) := by
  exact
    packedTile16384 132030720 132063488 12 1753 11490 27 _ _ (1869853 / 100000) (58433 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132063488 :
    ThetaLowerSegment 132063488 132096256 (13205068429459 / 100000) (13208271530473 / 100000) := by
  exact
    packedTile16384 132063488 132096256 12 1713 11491 27 _ _ (934939 / 50000) (1869881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132096256 :
    ThetaLowerSegment 132096256 132129024 (13208271530473 / 100000) (2642299048649 / 20000) := by
  exact
    packedTile16384 132096256 132129024 12 1724 11493 27 _ _ (1869903 / 100000) (934953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132129024 :
    ThetaLowerSegment 132129024 132161792 (2642299048649 / 20000) (412965169403 / 3125) := by
  exact
    packedTile16384 132129024 132161792 12 1813 11494 27 _ _ (1869927 / 100000) (186993 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132161792 :
    ThetaLowerSegment 132161792 132194560 (412965169403 / 3125) (413067666147 / 3125) := by
  exact
    packedTile16384 132161792 132194560 12 1754 11496 27 _ _ (58436 / 3125) (373991 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132194560 :
    ThetaLowerSegment 132194560 132227328 (413067666147 / 3125) (13221409726799 / 100000) := by
  exact
    packedTile16384 132194560 132227328 12 1735 11497 27 _ _ (1869977 / 100000) (93499 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132227328 :
    ThetaLowerSegment 132227328 132260096 (13221409726799 / 100000) (13224785080409 / 100000) := by
  exact
    packedTile16384 132227328 132260096 12 1805 11499 27 _ _ (935001 / 50000) (374001 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132260096 :
    ThetaLowerSegment 132260096 132292864 (13224785080409 / 100000) (1653505099677 / 12500) := by
  exact
    packedTile16384 132260096 132292864 12 1741 11500 27 _ _ (1870027 / 100000) (187003 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132292864 :
    ThetaLowerSegment 132292864 132325632 (1653505099677 / 12500) (13231251674983 / 100000) := by
  exact
    packedTile16384 132292864 132325632 12 1717 11501 27 _ _ (1870051 / 100000) (935027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132325632 :
    ThetaLowerSegment 132325632 132358400 (13231251674983 / 100000) (13234520567831 / 100000) := by
  exact
    packedTile16384 132325632 132358400 12 1748 11503 27 _ _ (467519 / 25000) (1870079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132358400 :
    ThetaLowerSegment 132358400 132391168 (13234520567831 / 100000) (165472392181 / 1250) := by
  exact
    packedTile16384 132358400 132391168 12 1749 11504 27 _ _ (1870101 / 100000) (233763 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132391168 :
    ThetaLowerSegment 132391168 132423936 (165472392181 / 1250) (3310269763997 / 25000) := by
  exact
    packedTile16384 132391168 132423936 12 1758 11506 27 _ _ (935063 / 50000) (1870129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132423936 :
    ThetaLowerSegment 132423936 132456704 (3310269763997 / 25000) (6622163753269 / 50000) := by
  exact
    packedTile16384 132423936 132456704 12 1737 11507 27 _ _ (37403 / 2000) (1870153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132456704 :
    ThetaLowerSegment 132456704 132489472 (6622163753269 / 50000) (13247613404013 / 100000) := by
  exact
    packedTile16384 132456704 132489472 12 1757 11508 27 _ _ (74807 / 4000) (935089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132489472 :
    ThetaLowerSegment 132489472 132522240 (13247613404013 / 100000) (13250953581213 / 100000) := by
  exact
    packedTile16384 132489472 132522240 12 1786 11510 27 _ _ (9351 / 500) (1870203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132522240 :
    ThetaLowerSegment 132522240 132555008 (13250953581213 / 100000) (3313557086297 / 25000) := by
  exact
    packedTile16384 132522240 132555008 12 1751 11511 27 _ _ (74809 / 4000) (467557 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132555008 :
    ThetaLowerSegment 132555008 132587776 (3313557086297 / 25000) (3314379995857 / 25000) := by
  exact
    packedTile16384 132555008 132587776 12 1760 11513 27 _ _ (1870249 / 100000) (467563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132587776 :
    ThetaLowerSegment 132587776 132620544 (3314379995857 / 25000) (1657590704133 / 12500) := by
  exact
    packedTile16384 132587776 132620544 12 1714 11514 27 _ _ (935137 / 50000) (1870277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132620544 :
    ThetaLowerSegment 132620544 132653312 (1657590704133 / 12500) (2652784394811 / 20000) := by
  exact
    packedTile16384 132620544 132653312 12 1709 11516 27 _ _ (1870299 / 100000) (935151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132653312 :
    ThetaLowerSegment 132653312 132686080 (2652784394811 / 20000) (13267172595429 / 100000) := by
  exact
    packedTile16384 132653312 132686080 12 1738 11517 27 _ _ (1870323 / 100000) (935163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132686080 :
    ThetaLowerSegment 132686080 132718848 (13267172595429 / 100000) (13270520518349 / 100000) := by
  exact
    packedTile16384 132686080 132718848 12 1790 11518 27 _ _ (467587 / 25000) (1870351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132718848 :
    ThetaLowerSegment 132718848 132751616 (13270520518349 / 100000) (13273771226623 / 100000) := by
  exact
    packedTile16384 132718848 132751616 12 1738 11520 27 _ _ (1870373 / 100000) (233797 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132751616 :
    ThetaLowerSegment 132751616 132784384 (13273771226623 / 100000) (13277038811929 / 100000) := by
  exact
    packedTile16384 132751616 132784384 12 1747 11521 27 _ _ (935199 / 50000) (1870401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132784384 :
    ThetaLowerSegment 132784384 132817152 (13277038811929 / 100000) (13280332625071 / 100000) := by
  exact
    packedTile16384 132784384 132817152 12 1761 11523 27 _ _ (935211 / 50000) (74817 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132817152 :
    ThetaLowerSegment 132817152 132849920 (13280332625071 / 100000) (13283594684639 / 100000) := by
  exact
    packedTile16384 132817152 132849920 12 1744 11524 27 _ _ (1870447 / 100000) (37409 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132849920 :
    ThetaLowerSegment 132849920 132882688 (13283594684639 / 100000) (13286918513383 / 100000) := by
  exact
    packedTile16384 132849920 132882688 12 1777 11526 27 _ _ (233809 / 12500) (74819 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132882688 :
    ThetaLowerSegment 132882688 132915456 (13286918513383 / 100000) (13290203104359 / 100000) := by
  exact
    packedTile16384 132882688 132915456 12 1756 11527 27 _ _ (58453 / 3125) (1870499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132915456 :
    ThetaLowerSegment 132915456 132948224 (13290203104359 / 100000) (2658690065763 / 20000) := by
  exact
    packedTile16384 132915456 132948224 12 1736 11528 27 _ _ (1870521 / 100000) (467631 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132948224 :
    ThetaLowerSegment 132948224 132980992 (2658690065763 / 20000) (13296684502849 / 100000) := by
  exact
    packedTile16384 132948224 132980992 12 1729 11530 27 _ _ (935273 / 50000) (1870549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell132980992 :
    ThetaLowerSegment 132980992 133013760 (13296684502849 / 100000) (13300023470299 / 100000) := by
  exact
    packedTile16384 132980992 133013760 12 1785 11531 27 _ _ (187057 / 10000) (1870573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133013760 :
    ThetaLowerSegment 133013760 133046528 (13300023470299 / 100000) (1662906748483 / 12500) := by
  exact
    packedTile16384 133013760 133046528 12 1727 11533 27 _ _ (374119 / 20000) (935299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133046528 :
    ThetaLowerSegment 133046528 133079296 (1662906748483 / 12500) (3326649663659 / 25000) := by
  exact
    packedTile16384 133046528 133079296 12 1788 11534 27 _ _ (1870619 / 100000) (935311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133079296 :
    ThetaLowerSegment 133079296 133112064 (3326649663659 / 25000) (3327488647493 / 25000) := by
  exact
    packedTile16384 133079296 133112064 12 1794 11536 27 _ _ (467661 / 25000) (1870647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133112064 :
    ThetaLowerSegment 133112064 133144832 (3327488647493 / 25000) (6656610389023 / 50000) := by
  exact
    packedTile16384 133112064 133144832 12 1746 11537 27 _ _ (1870669 / 100000) (116917 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133144832 :
    ThetaLowerSegment 133144832 133177600 (6656610389023 / 50000) (13316515068419 / 100000) := by
  exact
    packedTile16384 133144832 133177600 12 1761 11538 27 _ _ (1870693 / 100000) (233837 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133177600 :
    ThetaLowerSegment 133177600 133210368 (13316515068419 / 100000) (2663939806091 / 20000) := by
  exact
    packedTile16384 133177600 133210368 12 1702 11540 27 _ _ (935359 / 50000) (1870721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133210368 :
    ThetaLowerSegment 133210368 133243136 (2663939806091 / 20000) (832677500497 / 6250) := by
  exact
    packedTile16384 133210368 133243136 12 1679 11541 27 _ _ (1870743 / 100000) (935373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133243136 :
    ThetaLowerSegment 133243136 133275904 (832677500497 / 6250) (13326097013299 / 100000) := by
  exact
    packedTile16384 133243136 133275904 12 1741 11543 27 _ _ (1870767 / 100000) (187077 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133275904 :
    ThetaLowerSegment 133275904 133308672 (13326097013299 / 100000) (13329410185931 / 100000) := by
  exact
    packedTile16384 133275904 133308672 12 1771 11544 27 _ _ (233849 / 12500) (374159 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133308672 :
    ThetaLowerSegment 133308672 133341440 (13329410185931 / 100000) (13332684113931 / 100000) := by
  exact
    packedTile16384 133308672 133341440 12 1750 11545 27 _ _ (58463 / 3125) (1870819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133341440 :
    ThetaLowerSegment 133341440 133374208 (13332684113931 / 100000) (13336029177639 / 100000) := by
  exact
    packedTile16384 133341440 133374208 12 1788 11547 27 _ _ (1870841 / 100000) (467711 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133374208 :
    ThetaLowerSegment 133374208 133406976 (13336029177639 / 100000) (13339295707929 / 100000) := by
  exact
    packedTile16384 133374208 133406976 12 1746 11548 27 _ _ (374173 / 20000) (467717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133406976 :
    ThetaLowerSegment 133406976 133439744 (13339295707929 / 100000) (13342599699669 / 100000) := by
  exact
    packedTile16384 133406976 133439744 12 1766 11550 27 _ _ (187089 / 10000) (1870893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133439744 :
    ThetaLowerSegment 133439744 133472512 (13342599699669 / 100000) (6672967770557 / 50000) := by
  exact
    packedTile16384 133439744 133472512 12 1783 11551 27 _ _ (374183 / 20000) (935459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133472512 :
    ThetaLowerSegment 133472512 133505280 (6672967770557 / 50000) (1668640920381 / 12500) := by
  exact
    packedTile16384 133472512 133505280 12 1706 11553 27 _ _ (1870939 / 100000) (935471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133505280 :
    ThetaLowerSegment 133505280 133538048 (1668640920381 / 12500) (417263951662 / 3125) := by
  exact
    packedTile16384 133505280 133538048 12 1774 11554 27 _ _ (467741 / 25000) (1870967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133538048 :
    ThetaLowerSegment 133538048 133570816 (417263951662 / 3125) (3338910992919 / 25000) := by
  exact
    packedTile16384 133538048 133570816 12 1709 11555 27 _ _ (467747 / 25000) (1870991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133570816 :
    ThetaLowerSegment 133570816 133603584 (3338910992919 / 25000) (6679444154109 / 50000) := by
  exact
    packedTile16384 133570816 133603584 12 1734 11557 27 _ _ (1871013 / 100000) (233877 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133603584 :
    ThetaLowerSegment 133603584 133636352 (6679444154109 / 50000) (6681075698373 / 50000) := by
  exact
    packedTile16384 133603584 133636352 12 1744 11558 27 _ _ (1871037 / 100000) (11694 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133636352 :
    ThetaLowerSegment 133636352 133669120 (6681075698373 / 50000) (1336542949737 / 10000) := by
  exact
    packedTile16384 133636352 133669120 12 1752 11560 27 _ _ (935531 / 50000) (374213 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133669120 :
    ThetaLowerSegment 133669120 133701888 (1336542949737 / 10000) (835542941131 / 6250) := by
  exact
    packedTile16384 133669120 133701888 12 1741 11561 27 _ _ (935543 / 50000) (1871089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133701888 :
    ThetaLowerSegment 133701888 133734656 (835542941131 / 6250) (13371877302351 / 100000) := by
  exact
    packedTile16384 133701888 133734656 12 1705 11562 27 _ _ (1871111 / 100000) (935557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133734656 :
    ThetaLowerSegment 133734656 133767424 (13371877302351 / 100000) (6687616123703 / 50000) := by
  exact
    packedTile16384 133734656 133767424 12 1793 11564 27 _ _ (374227 / 20000) (935569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133767424 :
    ThetaLowerSegment 133767424 133800192 (6687616123703 / 50000) (6689236548263 / 50000) := by
  exact
    packedTile16384 133767424 133800192 12 1732 11565 27 _ _ (46779 / 2500) (1871163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133800192 :
    ThetaLowerSegment 133800192 133832960 (6689236548263 / 50000) (6690889739327 / 50000) := by
  exact
    packedTile16384 133800192 133832960 12 1767 11567 27 _ _ (116949 / 6250) (1871187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133832960 :
    ThetaLowerSegment 133832960 133865728 (6690889739327 / 50000) (13385037253523 / 100000) := by
  exact
    packedTile16384 133832960 133865728 12 1741 11568 27 _ _ (1871209 / 100000) (467803 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133865728 :
    ThetaLowerSegment 133865728 133898496 (13385037253523 / 100000) (13388259516749 / 100000) := by
  exact
    packedTile16384 133865728 133898496 12 1722 11570 27 _ _ (1871233 / 100000) (467809 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133898496 :
    ThetaLowerSegment 133898496 133931264 (13388259516749 / 100000) (2678300107121 / 20000) := by
  exact
    packedTile16384 133898496 133931264 12 1732 11571 27 _ _ (935629 / 50000) (1871261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133931264 :
    ThetaLowerSegment 133931264 133964032 (2678300107121 / 20000) (13394771536541 / 100000) := by
  exact
    packedTile16384 133931264 133964032 12 1748 11572 27 _ _ (935641 / 50000) (374257 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133964032 :
    ThetaLowerSegment 133964032 133996800 (13394771536541 / 100000) (2679621241123 / 20000) := by
  exact
    packedTile16384 133964032 133996800 12 1782 11574 27 _ _ (1871307 / 100000) (187131 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell133996800 :
    ThetaLowerSegment 133996800 134029568 (2679621241123 / 20000) (107210449453 / 800) := by
  exact
    packedTile16384 133996800 134029568 12 1710 11575 27 _ _ (1871331 / 100000) (935667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134029568 :
    ThetaLowerSegment 134029568 134062336 (107210449453 / 800) (13404612867677 / 100000) := by
  exact
    packedTile16384 134029568 134062336 12 1767 11577 27 _ _ (467839 / 25000) (1871359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134062336 :
    ThetaLowerSegment 134062336 134095104 (13404612867677 / 100000) (13407973866157 / 100000) := by
  exact
    packedTile16384 134062336 134095104 12 1796 11578 27 _ _ (93569 / 5000) (1871383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134095104 :
    ThetaLowerSegment 134095104 134127872 (13407973866157 / 100000) (13411217009289 / 100000) := by
  exact
    packedTile16384 134095104 134127872 12 1733 11579 27 _ _ (467851 / 25000) (1871407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134127872 :
    ThetaLowerSegment 134127872 134160640 (13411217009289 / 100000) (3353623470367 / 25000) := by
  exact
    packedTile16384 134127872 134160640 12 1751 11581 27 _ _ (1871429 / 100000) (233929 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134160640 :
    ThetaLowerSegment 134160640 134193408 (3353623470367 / 25000) (419303290463 / 3125) := by
  exact
    packedTile16384 134160640 134193408 12 1716 11582 27 _ _ (1871453 / 100000) (58483 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134193408 :
    ThetaLowerSegment 134193408 134226176 (419303290463 / 3125) (134210327827 / 1000) := by
  exact
    packedTile16384 134193408 134226176 12 1778 11584 27 _ _ (935739 / 50000) (1871481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134226176 :
    ThetaLowerSegment 134226176 134258944 (134210327827 / 1000) (10739483759 / 80) := by
  exact
    packedTile16384 134226176 134258944 12 1775 11585 27 _ _ (935751 / 50000) (374301 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134258944 :
    ThetaLowerSegment 134258944 134291712 (10739483759 / 80) (13427624256419 / 100000) := by
  exact
    packedTile16384 134258944 134291712 12 1747 11587 27 _ _ (1871527 / 100000) (187153 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134291712 :
    ThetaLowerSegment 134291712 134324480 (13427624256419 / 100000) (13430918186179 / 100000) := by
  exact
    packedTile16384 134291712 134324480 12 1760 11588 27 _ _ (1871551 / 100000) (935777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134324480 :
    ThetaLowerSegment 134324480 134357248 (13430918186179 / 100000) (6717114501177 / 50000) := by
  exact
    packedTile16384 134324480 134357248 12 1769 11589 27 _ _ (74863 / 4000) (935789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134357248 :
    ThetaLowerSegment 134357248 134390016 (6717114501177 / 50000) (6718750279577 / 50000) := by
  exact
    packedTile16384 134357248 134390016 12 1748 11591 27 _ _ (4679 / 250) (1871603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134390016 :
    ThetaLowerSegment 134390016 134422784 (6718750279577 / 50000) (6720378592457 / 50000) := by
  exact
    packedTile16384 134390016 134422784 12 1740 11592 27 _ _ (233953 / 12500) (1871627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134422784 :
    ThetaLowerSegment 134422784 134455552 (6720378592457 / 50000) (6722040616769 / 50000) := by
  exact
    packedTile16384 134422784 134455552 12 1776 11594 27 _ _ (1871649 / 100000) (467913 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134455552 :
    ThetaLowerSegment 134455552 134488320 (6722040616769 / 50000) (13447399709767 / 100000) := by
  exact
    packedTile16384 134455552 134488320 12 1773 11595 27 _ _ (1871673 / 100000) (467919 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134488320 :
    ThetaLowerSegment 134488320 134521088 (13447399709767 / 100000) (6725331038819 / 50000) := by
  exact
    packedTile16384 134488320 134521088 12 1743 11596 27 _ _ (1871697 / 100000) (18717 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134521088 :
    ThetaLowerSegment 134521088 134553856 (6725331038819 / 50000) (1681732606317 / 12500) := by
  exact
    packedTile16384 134521088 134553856 12 1709 11598 27 _ _ (935861 / 50000) (74869 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134553856 :
    ThetaLowerSegment 134553856 134586624 (1681732606317 / 12500) (1345713453429 / 10000) := by
  exact
    packedTile16384 134553856 134586624 12 1749 11599 27 _ _ (935873 / 50000) (1871749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134586624 :
    ThetaLowerSegment 134586624 134619392 (1345713453429 / 10000) (1346038018347 / 10000) := by
  exact
    packedTile16384 134586624 134619392 12 1734 11601 27 _ _ (187177 / 10000) (1871773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134619392 :
    ThetaLowerSegment 134619392 134652160 (1346038018347 / 10000) (1346365956831 / 10000) := by
  exact
    packedTile16384 134619392 134652160 12 1752 11602 27 _ _ (374359 / 20000) (935899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134652160 :
    ThetaLowerSegment 134652160 134684928 (1346365956831 / 10000) (13466895943361 / 100000) := by
  exact
    packedTile16384 134652160 134684928 12 1729 11603 27 _ _ (1871819 / 100000) (935911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134684928 :
    ThetaLowerSegment 134684928 134717696 (13466895943361 / 100000) (13470197874413 / 100000) := by
  exact
    packedTile16384 134684928 134717696 12 1764 11605 27 _ _ (1871843 / 100000) (935923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134717696 :
    ThetaLowerSegment 134717696 134750464 (13470197874413 / 100000) (13473550390001 / 100000) := by
  exact
    packedTile16384 134717696 134750464 12 1791 11606 27 _ _ (467967 / 25000) (1871871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134750464 :
    ThetaLowerSegment 134750464 134783232 (13473550390001 / 100000) (13476863638841 / 100000) := by
  exact
    packedTile16384 134750464 134783232 12 1770 11608 27 _ _ (467973 / 25000) (374379 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134783232 :
    ThetaLowerSegment 134783232 134816000 (13476863638841 / 100000) (2696025652069 / 20000) := by
  exact
    packedTile16384 134783232 134816000 12 1744 11609 27 _ _ (467979 / 25000) (1871919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134816000 :
    ThetaLowerSegment 134816000 134848768 (2696025652069 / 20000) (1348343223621 / 10000) := by
  exact
    packedTile16384 134816000 134848768 12 1765 11611 27 _ _ (1871941 / 100000) (233993 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134848768 :
    ThetaLowerSegment 134848768 134881536 (1348343223621 / 10000) (53946877627 / 400) := by
  exact
    packedTile16384 134848768 134881536 12 1756 11612 27 _ _ (374393 / 20000) (58499 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134881536 :
    ThetaLowerSegment 134881536 134914304 (53946877627 / 400) (13490034699269 / 100000) := by
  exact
    packedTile16384 134881536 134914304 12 1771 11613 27 _ _ (1871989 / 100000) (233999 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134914304 :
    ThetaLowerSegment 134914304 134947072 (13490034699269 / 100000) (13493357524119 / 100000) := by
  exact
    packedTile16384 134914304 134947072 12 1775 11615 27 _ _ (936007 / 50000) (1872017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134947072 :
    ThetaLowerSegment 134947072 134979840 (13493357524119 / 100000) (13496616742277 / 100000) := by
  exact
    packedTile16384 134947072 134979840 12 1741 11616 27 _ _ (936019 / 50000) (1872041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell134979840 :
    ThetaLowerSegment 134979840 135012608 (13496616742277 / 100000) (13499887234591 / 100000) := by
  exact
    packedTile16384 134979840 135012608 12 1747 11618 27 _ _ (936031 / 50000) (374413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135012608 :
    ThetaLowerSegment 135012608 135045376 (13499887234591 / 100000) (2700634174687 / 20000) := by
  exact
    packedTile16384 135012608 135045376 12 1754 11619 27 _ _ (936043 / 50000) (1872089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135045376 :
    ThetaLowerSegment 135045376 135078144 (2700634174687 / 20000) (13506488254127 / 100000) := by
  exact
    packedTile16384 135045376 135078144 12 1772 11620 27 _ _ (1872111 / 100000) (936057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135078144 :
    ThetaLowerSegment 135078144 135110912 (13506488254127 / 100000) (13509835631507 / 100000) := by
  exact
    packedTile16384 135078144 135110912 12 1788 11622 27 _ _ (374427 / 20000) (936069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135110912 :
    ThetaLowerSegment 135110912 135143680 (13509835631507 / 100000) (13513111909757 / 100000) := by
  exact
    packedTile16384 135110912 135143680 12 1750 11623 27 _ _ (1872159 / 100000) (936081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135143680 :
    ThetaLowerSegment 135143680 135176448 (13513111909757 / 100000) (13516309598321 / 100000) := by
  exact
    packedTile16384 135143680 135176448 12 1708 11625 27 _ _ (1872183 / 100000) (936093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135176448 :
    ThetaLowerSegment 135176448 135209216 (13516309598321 / 100000) (13519614045441 / 100000) := by
  exact
    packedTile16384 135176448 135209216 12 1765 11626 27 _ _ (117013 / 6250) (1872211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135209216 :
    ThetaLowerSegment 135209216 135241984 (13519614045441 / 100000) (13522873601353 / 100000) := by
  exact
    packedTile16384 135209216 135241984 12 1741 11627 27 _ _ (234029 / 12500) (374447 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135241984 :
    ThetaLowerSegment 135241984 135274752 (13522873601353 / 100000) (13526080775881 / 100000) := by
  exact
    packedTile16384 135241984 135274752 12 1713 11629 27 _ _ (58508 / 3125) (1872259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135274752 :
    ThetaLowerSegment 135274752 135307520 (13526080775881 / 100000) (13529375988681 / 100000) := by
  exact
    packedTile16384 135274752 135307520 12 1760 11630 27 _ _ (46807 / 2500) (1872283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135307520 :
    ThetaLowerSegment 135307520 135340288 (13529375988681 / 100000) (845790899671 / 6250) := by
  exact
    packedTile16384 135307520 135340288 12 1751 11632 27 _ _ (374461 / 20000) (468077 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135340288 :
    ThetaLowerSegment 135340288 135373056 (845790899671 / 6250) (13535925353499 / 100000) := by
  exact
    packedTile16384 135340288 135373056 12 1747 11633 27 _ _ (1872329 / 100000) (468083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135373056 :
    ThetaLowerSegment 135373056 135405824 (13535925353499 / 100000) (13539145800659 / 100000) := by
  exact
    packedTile16384 135373056 135405824 12 1720 11634 27 _ _ (1872353 / 100000) (468089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135405824 :
    ThetaLowerSegment 135405824 135438592 (13539145800659 / 100000) (2708491232639 / 20000) := by
  exact
    packedTile16384 135405824 135438592 12 1768 11636 27 _ _ (1872377 / 100000) (93619 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135438592 :
    ThetaLowerSegment 135438592 135471360 (2708491232639 / 20000) (423305965918 / 3125) := by
  exact
    packedTile16384 135438592 135471360 12 1781 11637 27 _ _ (1872401 / 100000) (468101 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135471360 :
    ThetaLowerSegment 135471360 135504128 (423305965918 / 3125) (846816962483 / 6250) := by
  exact
    packedTile16384 135471360 135504128 12 1752 11639 27 _ _ (936213 / 50000) (1872429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135504128 :
    ThetaLowerSegment 135504128 135536896 (846816962483 / 6250) (3388077684557 / 25000) := by
  exact
    packedTile16384 135504128 135536896 12 1730 11640 27 _ _ (37449 / 2000) (1872453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135536896 :
    ThetaLowerSegment 135536896 135569664 (3388077684557 / 25000) (6777757270621 / 50000) := by
  exact
    packedTile16384 135536896 135569664 12 1711 11642 27 _ _ (936237 / 50000) (1872477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135569664 :
    ThetaLowerSegment 135569664 135602432 (6777757270621 / 50000) (3389689895069 / 25000) := by
  exact
    packedTile16384 135569664 135602432 12 1733 11643 27 _ _ (936249 / 50000) (1872501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135602432 :
    ThetaLowerSegment 135602432 135635200 (3389689895069 / 25000) (16952526892 / 125) := by
  exact
    packedTile16384 135602432 135635200 12 1742 11644 27 _ _ (936261 / 50000) (74901 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135635200 :
    ThetaLowerSegment 135635200 135667968 (16952526892 / 125) (423913353511 / 3125) := by
  exact
    packedTile16384 135635200 135667968 12 1712 11646 27 _ _ (936273 / 50000) (1872549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135667968 :
    ThetaLowerSegment 135667968 135700736 (423913353511 / 3125) (6784255900943 / 50000) := by
  exact
    packedTile16384 135667968 135700736 12 1754 11647 27 _ _ (1872571 / 100000) (936287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135700736 :
    ThetaLowerSegment 135700736 135733504 (6784255900943 / 50000) (13571730792691 / 100000) := by
  exact
    packedTile16384 135700736 135733504 12 1719 11649 27 _ _ (374519 / 20000) (936299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135733504 :
    ThetaLowerSegment 135733504 135766272 (13571730792691 / 100000) (13575064054511 / 100000) := by
  exact
    packedTile16384 135733504 135766272 12 1780 11650 27 _ _ (1872619 / 100000) (936311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135766272 :
    ThetaLowerSegment 135766272 135799040 (13575064054511 / 100000) (13578266274041 / 100000) := by
  exact
    packedTile16384 135766272 135799040 12 1710 11651 27 _ _ (1872643 / 100000) (936323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135799040 :
    ThetaLowerSegment 135799040 135831808 (13578266274041 / 100000) (13581569658629 / 100000) := by
  exact
    packedTile16384 135799040 135831808 12 1764 11653 27 _ _ (1872667 / 100000) (187267 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135831808 :
    ThetaLowerSegment 135831808 135864576 (13581569658629 / 100000) (6792420624903 / 50000) := by
  exact
    packedTile16384 135831808 135864576 12 1747 11654 27 _ _ (1872691 / 100000) (936347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135864576 :
    ThetaLowerSegment 135864576 135897344 (6792420624903 / 50000) (13588090410331 / 100000) := by
  exact
    packedTile16384 135864576 135897344 12 1735 11656 27 _ _ (374543 / 20000) (936359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135897344 :
    ThetaLowerSegment 135897344 135930112 (13588090410331 / 100000) (13591375196291 / 100000) := by
  exact
    packedTile16384 135897344 135930112 12 1754 11657 27 _ _ (93637 / 5000) (1872743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135930112 :
    ThetaLowerSegment 135930112 135962880 (13591375196291 / 100000) (13594622569067 / 100000) := by
  exact
    packedTile16384 135930112 135962880 12 1734 11658 27 _ _ (468191 / 25000) (1872767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135962880 :
    ThetaLowerSegment 135962880 135995648 (13594622569067 / 100000) (543917196507 / 4000) := by
  exact
    packedTile16384 135962880 135995648 12 1766 11660 27 _ _ (468197 / 25000) (1872791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell135995648 :
    ThetaLowerSegment 135995648 136028416 (543917196507 / 4000) (13601205460863 / 100000) := by
  exact
    packedTile16384 135995648 136028416 12 1749 11661 27 _ _ (468203 / 25000) (374563 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136028416 :
    ThetaLowerSegment 136028416 136061184 (13601205460863 / 100000) (13604441721471 / 100000) := by
  exact
    packedTile16384 136028416 136061184 12 1728 11663 27 _ _ (468209 / 25000) (1872839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136061184 :
    ThetaLowerSegment 136061184 136093952 (13604441721471 / 100000) (13607767920831 / 100000) := by
  exact
    packedTile16384 136061184 136093952 12 1776 11664 27 _ _ (93643 / 5000) (1872863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136093952 :
    ThetaLowerSegment 136093952 136126720 (13607767920831 / 100000) (13610921857487 / 100000) := by
  exact
    packedTile16384 136093952 136126720 12 1684 11665 27 _ _ (468221 / 25000) (1872887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136126720 :
    ThetaLowerSegment 136126720 136159488 (13610921857487 / 100000) (13614251887911 / 100000) := by
  exact
    packedTile16384 136126720 136159488 12 1778 11667 27 _ _ (468227 / 25000) (1872911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136159488 :
    ThetaLowerSegment 136159488 136192256 (13614251887911 / 100000) (13617610054987 / 100000) := by
  exact
    packedTile16384 136159488 136192256 12 1793 11668 27 _ _ (468233 / 25000) (374587 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136192256 :
    ThetaLowerSegment 136192256 136225024 (13617610054987 / 100000) (13620825920439 / 100000) := by
  exact
    packedTile16384 136192256 136225024 12 1717 11670 27 _ _ (468239 / 25000) (1872959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136225024 :
    ThetaLowerSegment 136225024 136257792 (13620825920439 / 100000) (13624054937959 / 100000) := by
  exact
    packedTile16384 136225024 136257792 12 1724 11671 27 _ _ (93649 / 5000) (1872983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136257792 :
    ThetaLowerSegment 136257792 136290560 (13624054937959 / 100000) (13627323329939 / 100000) := by
  exact
    packedTile16384 136257792 136290560 12 1745 11672 27 _ _ (468251 / 25000) (1873007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136290560 :
    ThetaLowerSegment 136290560 136323328 (13627323329939 / 100000) (2726109736831 / 20000) := by
  exact
    packedTile16384 136290560 136323328 12 1722 11674 27 _ _ (468257 / 25000) (1873031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136323328 :
    ThetaLowerSegment 136323328 136356096 (2726109736831 / 20000) (6816947914933 / 50000) := by
  exact
    packedTile16384 136323328 136356096 12 1787 11675 27 _ _ (1873053 / 100000) (58533 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136356096 :
    ThetaLowerSegment 136356096 136388864 (6816947914933 / 50000) (13637254256927 / 100000) := by
  exact
    packedTile16384 136356096 136388864 12 1793 11677 27 _ _ (1873077 / 100000) (46827 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136388864 :
    ThetaLowerSegment 136388864 136421632 (13637254256927 / 100000) (13640524691273 / 100000) := by
  exact
    packedTile16384 136388864 136421632 12 1746 11678 27 _ _ (1873101 / 100000) (117069 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136421632 :
    ThetaLowerSegment 136421632 136454400 (13640524691273 / 100000) (13643851361273 / 100000) := by
  exact
    packedTile16384 136421632 136454400 12 1776 11679 27 _ _ (2997 / 160) (234141 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136454400 :
    ThetaLowerSegment 136454400 136487168 (13643851361273 / 100000) (545888771327 / 4000) := by
  exact
    packedTile16384 136454400 136487168 12 1798 11681 27 _ _ (1873149 / 100000) (58536 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136487168 :
    ThetaLowerSegment 136487168 136519936 (545888771327 / 4000) (13650467365157 / 100000) := by
  exact
    packedTile16384 136487168 136519936 12 1734 11682 27 _ _ (1873173 / 100000) (234147 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136519936 :
    ThetaLowerSegment 136519936 136552704 (13650467365157 / 100000) (13653775431059 / 100000) := by
  exact
    packedTile16384 136519936 136552704 12 1766 11684 27 _ _ (1873197 / 100000) (4683 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136552704 :
    ThetaLowerSegment 136552704 136585472 (13653775431059 / 100000) (341426854331 / 2500) := by
  exact
    packedTile16384 136552704 136585472 12 1761 11685 27 _ _ (1873221 / 100000) (234153 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136585472 :
    ThetaLowerSegment 136585472 136618240 (341426854331 / 2500) (1366033736603 / 10000) := by
  exact
    packedTile16384 136585472 136618240 12 1742 11686 27 _ _ (374649 / 20000) (58539 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136618240 :
    ThetaLowerSegment 136618240 136651008 (1366033736603 / 10000) (341593199573 / 2500) := by
  exact
    packedTile16384 136618240 136651008 12 1810 11688 27 _ _ (1873269 / 100000) (234159 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136651008 :
    ThetaLowerSegment 136651008 136683776 (341593199573 / 2500) (2733391882669 / 20000) := by
  exact
    packedTile16384 136651008 136683776 12 1725 11689 27 _ _ (1873293 / 100000) (117081 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136683776 :
    ThetaLowerSegment 136683776 136716544 (2733391882669 / 20000) (6835125415657 / 50000) := by
  exact
    packedTile16384 136683776 136716544 12 1757 11691 27 _ _ (1873317 / 100000) (46833 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136716544 :
    ThetaLowerSegment 136716544 136749312 (6835125415657 / 50000) (13673553531497 / 100000) := by
  exact
    packedTile16384 136716544 136749312 12 1763 11692 27 _ _ (1873341 / 100000) (58542 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136749312 :
    ThetaLowerSegment 136749312 136782080 (13673553531497 / 100000) (13676822551677 / 100000) := by
  exact
    packedTile16384 136749312 136782080 12 1745 11693 27 _ _ (468341 / 25000) (1873367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136782080 :
    ThetaLowerSegment 136782080 136814848 (13676822551677 / 100000) (13680110347617 / 100000) := by
  exact
    packedTile16384 136782080 136814848 12 1755 11695 27 _ _ (468347 / 25000) (1873391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136814848 :
    ThetaLowerSegment 136814848 136847616 (13680110347617 / 100000) (2736664275157 / 20000) := by
  exact
    packedTile16384 136814848 136847616 12 1714 11696 27 _ _ (468353 / 25000) (374683 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136847616 :
    ThetaLowerSegment 136847616 136880384 (2736664275157 / 20000) (13686575534117 / 100000) := by
  exact
    packedTile16384 136847616 136880384 12 1737 11698 27 _ _ (468359 / 25000) (1873439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136880384 :
    ThetaLowerSegment 136880384 136913152 (13686575534117 / 100000) (13689887811397 / 100000) := by
  exact
    packedTile16384 136880384 136913152 12 1768 11699 27 _ _ (93673 / 5000) (1873463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136913152 :
    ThetaLowerSegment 136913152 136945920 (13689887811397 / 100000) (13693153294009 / 100000) := by
  exact
    packedTile16384 136913152 136945920 12 1743 11700 27 _ _ (468371 / 25000) (1873487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136945920 :
    ThetaLowerSegment 136945920 136978688 (13693153294009 / 100000) (547855553693 / 4000) := by
  exact
    packedTile16384 136945920 136978688 12 1727 11702 27 _ _ (468377 / 25000) (1873511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell136978688 :
    ThetaLowerSegment 136978688 137011456 (547855553693 / 4000) (13699661902729 / 100000) := by
  exact
    packedTile16384 136978688 137011456 12 1747 11703 27 _ _ (468383 / 25000) (374707 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137011456 :
    ThetaLowerSegment 137011456 137044224 (13699661902729 / 100000) (13702949993509 / 100000) := by
  exact
    packedTile16384 137011456 137044224 12 1755 11705 27 _ _ (468389 / 25000) (1873559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137044224 :
    ThetaLowerSegment 137044224 137076992 (13702949993509 / 100000) (13706168803949 / 100000) := by
  exact
    packedTile16384 137044224 137076992 12 1718 11706 27 _ _ (93679 / 5000) (1873583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137076992 :
    ThetaLowerSegment 137076992 137109760 (13706168803949 / 100000) (13709494451049 / 100000) := by
  exact
    packedTile16384 137076992 137109760 12 1775 11707 27 _ _ (468401 / 25000) (1873607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137109760 :
    ThetaLowerSegment 137109760 137142528 (13709494451049 / 100000) (13712763931909 / 100000) := by
  exact
    packedTile16384 137109760 137142528 12 1745 11709 27 _ _ (468407 / 25000) (1873631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137142528 :
    ThetaLowerSegment 137142528 137175296 (13712763931909 / 100000) (13715941645701 / 100000) := by
  exact
    packedTile16384 137142528 137175296 12 1696 11710 27 _ _ (468413 / 25000) (374731 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137175296 :
    ThetaLowerSegment 137175296 137208064 (13715941645701 / 100000) (2743839993653 / 20000) := by
  exact
    packedTile16384 137175296 137208064 12 1739 11712 27 _ _ (468419 / 25000) (1873679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137208064 :
    ThetaLowerSegment 137208064 137240832 (2743839993653 / 20000) (6861240407607 / 50000) := by
  exact
    packedTile16384 137208064 137240832 12 1751 11713 27 _ _ (1873699 / 100000) (936851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137240832 :
    ThetaLowerSegment 137240832 137273600 (6861240407607 / 50000) (1715725599977 / 12500) := by
  exact
    packedTile16384 137240832 137273600 12 1774 11714 27 _ _ (1873723 / 100000) (936863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137273600 :
    ThetaLowerSegment 137273600 137306368 (1715725599977 / 12500) (3432273774887 / 25000) := by
  exact
    packedTile16384 137273600 137306368 12 1756 11716 27 _ _ (1873747 / 100000) (1499 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137306368 :
    ThetaLowerSegment 137306368 137339136 (3432273774887 / 25000) (429134234388 / 3125) := by
  exact
    packedTile16384 137306368 137339136 12 1708 11717 27 _ _ (1873771 / 100000) (936887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137339136 :
    ThetaLowerSegment 137339136 137371904 (429134234388 / 3125) (13735640224491 / 100000) := by
  exact
    packedTile16384 137339136 137371904 12 1785 11719 27 _ _ (374759 / 20000) (936899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137371904 :
    ThetaLowerSegment 137371904 137404672 (13735640224491 / 100000) (13738926903017 / 100000) := by
  exact
    packedTile16384 137371904 137404672 12 1754 11720 27 _ _ (1873819 / 100000) (936911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137404672 :
    ThetaLowerSegment 137404672 137437440 (13738926903017 / 100000) (3435564180507 / 25000) := by
  exact
    packedTile16384 137404672 137437440 12 1777 11721 27 _ _ (1873843 / 100000) (936923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137437440 :
    ThetaLowerSegment 137437440 137470208 (3435564180507 / 25000) (1718197620039 / 12500) := by
  exact
    packedTile16384 137437440 137470208 12 1774 11723 27 _ _ (936933 / 50000) (1873869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137470208 :
    ThetaLowerSegment 137470208 137502976 (1718197620039 / 12500) (1718617371399 / 12500) := by
  exact
    packedTile16384 137470208 137502976 12 1792 11724 27 _ _ (187389 / 10000) (1873893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137502976 :
    ThetaLowerSegment 137502976 137535744 (1718617371399 / 12500) (6876083862507 / 50000) := by
  exact
    packedTile16384 137502976 137535744 12 1723 11726 27 _ _ (936957 / 50000) (1873917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137535744 :
    ThetaLowerSegment 137535744 137568512 (6876083862507 / 50000) (6877761037017 / 50000) := by
  exact
    packedTile16384 137535744 137568512 12 1790 11727 27 _ _ (936969 / 50000) (1873941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137568512 :
    ThetaLowerSegment 137568512 137601280 (6877761037017 / 50000) (6879382014147 / 50000) := by
  exact
    packedTile16384 137568512 137601280 12 1730 11728 27 _ _ (936981 / 50000) (374793 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137601280 :
    ThetaLowerSegment 137601280 137634048 (6879382014147 / 50000) (3440515092417 / 25000) := by
  exact
    packedTile16384 137601280 137634048 12 1759 11730 27 _ _ (936993 / 50000) (1873989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137634048 :
    ThetaLowerSegment 137634048 137666816 (3440515092417 / 25000) (13765319271319 / 100000) := by
  exact
    packedTile16384 137634048 137666816 12 1739 11731 27 _ _ (1874009 / 100000) (468503 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137666816 :
    ThetaLowerSegment 137666816 137699584 (13765319271319 / 100000) (13768531363881 / 100000) := by
  exact
    packedTile16384 137666816 137699584 12 1714 11733 27 _ _ (1874033 / 100000) (468509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137699584 :
    ThetaLowerSegment 137699584 137732352 (13768531363881 / 100000) (13771762238149 / 100000) := by
  exact
    packedTile16384 137699584 137732352 12 1724 11734 27 _ _ (1874057 / 100000) (93703 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137732352 :
    ThetaLowerSegment 137732352 137765120 (13771762238149 / 100000) (551001375343 / 4000) := by
  exact
    packedTile16384 137732352 137765120 12 1746 11735 27 _ _ (1874081 / 100000) (468521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137765120 :
    ThetaLowerSegment 137765120 137797888 (551001375343 / 4000) (2755671809169 / 20000) := by
  exact
    packedTile16384 137765120 137797888 12 1774 11737 27 _ _ (374821 / 20000) (468527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137797888 :
    ThetaLowerSegment 137797888 137830656 (2755671809169 / 20000) (2756318383329 / 20000) := by
  exact
    packedTile16384 137797888 137830656 12 1725 11738 27 _ _ (117133 / 6250) (1874131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137830656 :
    ThetaLowerSegment 137830656 137863424 (2756318383329 / 20000) (13784807961477 / 100000) := by
  exact
    packedTile16384 137830656 137863424 12 1716 11740 27 _ _ (234269 / 12500) (374831 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137863424 :
    ThetaLowerSegment 137863424 137896192 (13784807961477 / 100000) (13788069027717 / 100000) := by
  exact
    packedTile16384 137863424 137896192 12 1740 11741 27 _ _ (58568 / 3125) (1874179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137896192 :
    ThetaLowerSegment 137896192 137928960 (13788069027717 / 100000) (13791399481117 / 100000) := by
  exact
    packedTile16384 137896192 137928960 12 1777 11742 27 _ _ (9371 / 500) (1874203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137928960 :
    ThetaLowerSegment 137928960 137961728 (13791399481117 / 100000) (13794664377583 / 100000) := by
  exact
    packedTile16384 137928960 137961728 12 1742 11744 27 _ _ (1874223 / 100000) (937113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137961728 :
    ThetaLowerSegment 137961728 137994496 (13794664377583 / 100000) (13797816861037 / 100000) := by
  exact
    packedTile16384 137961728 137994496 12 1682 11745 27 _ _ (1874247 / 100000) (7497 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell137994496 :
    ThetaLowerSegment 137994496 138027264 (13797816861037 / 100000) (6900564348947 / 50000) := by
  exact
    packedTile16384 137994496 138027264 12 1767 11747 27 _ _ (1874271 / 100000) (937137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138027264 :
    ThetaLowerSegment 138027264 138060032 (6900564348947 / 50000) (13804350610999 / 100000) := by
  exact
    packedTile16384 138027264 138060032 12 1719 11748 27 _ _ (374859 / 20000) (937149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138060032 :
    ThetaLowerSegment 138060032 138092800 (13804350610999 / 100000) (13807565066369 / 100000) := by
  exact
    packedTile16384 138060032 138092800 12 1715 11749 27 _ _ (937159 / 50000) (1874321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138092800 :
    ThetaLowerSegment 138092800 138125568 (13807565066369 / 100000) (13810772065531 / 100000) := by
  exact
    packedTile16384 138092800 138125568 12 1711 11751 27 _ _ (937171 / 50000) (374869 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138125568 :
    ThetaLowerSegment 138125568 138158336 (13810772065531 / 100000) (13814192783481 / 100000) := by
  exact
    packedTile16384 138125568 138158336 12 1825 11752 27 _ _ (937183 / 50000) (1874369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138158336 :
    ThetaLowerSegment 138158336 138191104 (13814192783481 / 100000) (13817422357451 / 100000) := by
  exact
    packedTile16384 138158336 138191104 12 1723 11754 27 _ _ (187439 / 10000) (1874393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138191104 :
    ThetaLowerSegment 138191104 138223872 (13817422357451 / 100000) (3455163929969 / 25000) := by
  exact
    packedTile16384 138191104 138223872 12 1725 11755 27 _ _ (1874413 / 100000) (117151 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138223872 :
    ThetaLowerSegment 138223872 138256640 (3455163929969 / 25000) (2764771076767 / 20000) := by
  exact
    packedTile16384 138223872 138256640 12 1707 11756 27 _ _ (1874437 / 100000) (46861 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138256640 :
    ThetaLowerSegment 138256640 138289408 (2764771076767 / 20000) (13827090703521 / 100000) := by
  exact
    packedTile16384 138256640 138289408 12 1726 11758 27 _ _ (1874461 / 100000) (58577 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138289408 :
    ThetaLowerSegment 138289408 138322176 (13827090703521 / 100000) (13830416038137 / 100000) := by
  exact
    packedTile16384 138289408 138322176 12 1774 11759 27 _ _ (468621 / 25000) (1874487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138322176 :
    ThetaLowerSegment 138322176 138354944 (13830416038137 / 100000) (553350556377 / 4000) := by
  exact
    packedTile16384 138322176 138354944 12 1786 11761 27 _ _ (468627 / 25000) (1874511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138354944 :
    ThetaLowerSegment 138354944 138387712 (553350556377 / 4000) (2767405119021 / 20000) := by
  exact
    packedTile16384 138354944 138387712 12 1740 11762 27 _ _ (468633 / 25000) (374907 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138387712 :
    ThetaLowerSegment 138387712 138420480 (2767405119021 / 20000) (2768064212559 / 20000) := by
  exact
    packedTile16384 138387712 138420480 12 1758 11763 27 _ _ (374911 / 20000) (937279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138420480 :
    ThetaLowerSegment 138420480 138453248 (2768064212559 / 20000) (6921811098207 / 50000) := by
  exact
    packedTile16384 138420480 138453248 12 1761 11765 27 _ _ (1874579 / 100000) (937291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138453248 :
    ThetaLowerSegment 138453248 138486016 (6921811098207 / 50000) (3461697568871 / 25000) := by
  exact
    packedTile16384 138453248 138486016 12 1690 11766 27 _ _ (1874603 / 100000) (937303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138486016 :
    ThetaLowerSegment 138486016 138518784 (3461697568871 / 25000) (692504105937 / 5000) := by
  exact
    packedTile16384 138486016 138518784 12 1756 11768 27 _ _ (937313 / 50000) (1874629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138518784 :
    ThetaLowerSegment 138518784 138551552 (692504105937 / 5000) (346335006231 / 2500) := by
  exact
    packedTile16384 138518784 138551552 12 1770 11769 27 _ _ (37493 / 2000) (1874653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138551552 :
    ThetaLowerSegment 138551552 138584320 (346335006231 / 2500) (1732093083457 / 12500) := by
  exact
    packedTile16384 138551552 138584320 12 1784 11770 27 _ _ (937337 / 50000) (1874677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138584320 :
    ThetaLowerSegment 138584320 138617088 (1732093083457 / 12500) (346498853723 / 2500) := by
  exact
    packedTile16384 138584320 138617088 12 1712 11772 27 _ _ (1874697 / 100000) (18747 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138617088 :
    ThetaLowerSegment 138617088 138649856 (346498853723 / 2500) (13863191792087 / 100000) := by
  exact
    packedTile16384 138617088 138649856 12 1727 11773 27 _ _ (1874721 / 100000) (468681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138649856 :
    ThetaLowerSegment 138649856 138682624 (13863191792087 / 100000) (13866491343287 / 100000) := by
  exact
    packedTile16384 138649856 138682624 12 1760 11774 27 _ _ (374949 / 20000) (468687 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138682624 :
    ThetaLowerSegment 138682624 138715392 (13866491343287 / 100000) (2773949188107 / 20000) := by
  exact
    packedTile16384 138682624 138715392 12 1736 11776 27 _ _ (117173 / 6250) (1874771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138715392 :
    ThetaLowerSegment 138715392 138748160 (2773949188107 / 20000) (13873019327367 / 100000) := by
  exact
    packedTile16384 138715392 138748160 12 1746 11777 27 _ _ (234349 / 12500) (374959 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138748160 :
    ThetaLowerSegment 138748160 138780928 (13873019327367 / 100000) (13876320878343 / 100000) := by
  exact
    packedTile16384 138748160 138780928 12 1761 11779 27 _ _ (58588 / 3125) (1874819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138780928 :
    ThetaLowerSegment 138780928 138813696 (13876320878343 / 100000) (6939792486521 / 50000) := by
  exact
    packedTile16384 138780928 138813696 12 1741 11780 27 _ _ (1874839 / 100000) (937421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138813696 :
    ThetaLowerSegment 138813696 138846464 (6939792486521 / 50000) (86767865524 / 625) := by
  exact
    packedTile16384 138813696 138846464 12 1746 11781 27 _ _ (1874863 / 100000) (937433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138846464 :
    ThetaLowerSegment 138846464 138879232 (86767865524 / 625) (867891454801 / 6250) := by
  exact
    packedTile16384 138846464 138879232 12 1816 11783 27 _ _ (937443 / 50000) (1874889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138879232 :
    ThetaLowerSegment 138879232 138912000 (867891454801 / 6250) (6944752498103 / 50000) := by
  exact
    packedTile16384 138879232 138912000 12 1729 11784 27 _ _ (187491 / 10000) (1874913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138912000 :
    ThetaLowerSegment 138912000 138944768 (6944752498103 / 50000) (1389274113229 / 10000) := by
  exact
    packedTile16384 138912000 138944768 12 1726 11786 27 _ _ (937467 / 50000) (1874937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138944768 :
    ThetaLowerSegment 138944768 138977536 (1389274113229 / 10000) (6948035527961 / 50000) := by
  exact
    packedTile16384 138944768 138977536 12 1776 11787 27 _ _ (1874957 / 100000) (23437 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell138977536 :
    ThetaLowerSegment 138977536 139010304 (6948035527961 / 50000) (6949689261203 / 50000) := by
  exact
    packedTile16384 138977536 139010304 12 1764 11788 27 _ _ (1874981 / 100000) (234373 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139010304 :
    ThetaLowerSegment 139010304 139043072 (6949689261203 / 50000) (6951294264627 / 50000) := by
  exact
    packedTile16384 139010304 139043072 12 1712 11790 27 _ _ (468751 / 25000) (1875007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139043072 :
    ThetaLowerSegment 139043072 139075840 (6951294264627 / 50000) (6952938664183 / 50000) := by
  exact
    packedTile16384 139043072 139075840 12 1754 11791 27 _ _ (468757 / 25000) (1875031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139075840 :
    ThetaLowerSegment 139075840 139108608 (6952938664183 / 50000) (13909134291953 / 100000) := by
  exact
    packedTile16384 139075840 139108608 12 1737 11793 27 _ _ (1875051 / 100000) (937527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139108608 :
    ThetaLowerSegment 139108608 139141376 (13909134291953 / 100000) (13912434423953 / 100000) := by
  exact
    packedTile16384 139108608 139141376 12 1760 11794 27 _ _ (75003 / 4000) (937539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139141376 :
    ThetaLowerSegment 139141376 139174144 (13912434423953 / 100000) (278312554351 / 2000) := by
  exact
    packedTile16384 139141376 139174144 12 1703 11795 27 _ _ (1875099 / 100000) (937551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139174144 :
    ThetaLowerSegment 139174144 139206912 (278312554351 / 2000) (86993123784 / 625) := by
  exact
    packedTile16384 139174144 139206912 12 1745 11797 27 _ _ (937561 / 50000) (15001 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139206912 :
    ThetaLowerSegment 139206912 139239680 (86993123784 / 625) (1392213443229 / 10000) := by
  exact
    packedTile16384 139206912 139239680 12 1725 11798 27 _ _ (937573 / 50000) (1875149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139239680 :
    ThetaLowerSegment 139239680 139272448 (1392213443229 / 10000) (6962724865541 / 50000) := by
  exact
    packedTile16384 139239680 139272448 12 1768 11799 27 _ _ (1875169 / 100000) (468793 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139272448 :
    ThetaLowerSegment 139272448 139305216 (6962724865541 / 50000) (13928740694797 / 100000) := by
  exact
    packedTile16384 139272448 139305216 12 1755 11801 27 _ _ (1875193 / 100000) (468799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139305216 :
    ThetaLowerSegment 139305216 139337984 (13928740694797 / 100000) (2786403714473 / 20000) := by
  exact
    packedTile16384 139305216 139337984 12 1748 11802 27 _ _ (117201 / 6250) (1875219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139337984 :
    ThetaLowerSegment 139337984 139370752 (2786403714473 / 20000) (2787067549433 / 20000) := by
  exact
    packedTile16384 139337984 139370752 12 1770 11804 27 _ _ (46881 / 2500) (1875243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139370752 :
    ThetaLowerSegment 139370752 139403520 (2787067549433 / 20000) (1393862883373 / 10000) := by
  exact
    packedTile16384 139370752 139403520 12 1755 11805 27 _ _ (1875263 / 100000) (937633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139403520 :
    ThetaLowerSegment 139403520 139436288 (1393862883373 / 10000) (13941987472747 / 100000) := by
  exact
    packedTile16384 139403520 139436288 12 1791 11806 27 _ _ (1875287 / 100000) (187529 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139436288 :
    ThetaLowerSegment 139436288 139469056 (13941987472747 / 100000) (13945233634357 / 100000) := by
  exact
    packedTile16384 139436288 139469056 12 1731 11808 27 _ _ (187531 / 10000) (1875313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139469056 :
    ThetaLowerSegment 139469056 139501824 (13945233634357 / 100000) (2789701968571 / 20000) := by
  exact
    packedTile16384 139469056 139501824 12 1747 11809 27 _ _ (937667 / 50000) (1875337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139501824 :
    ThetaLowerSegment 139501824 139534592 (2789701968571 / 20000) (13951731706181 / 100000) := by
  exact
    packedTile16384 139501824 139534592 12 1718 11811 27 _ _ (1875357 / 100000) (11721 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139534592 :
    ThetaLowerSegment 139534592 139567360 (13951731706181 / 100000) (6977528378347 / 50000) := by
  exact
    packedTile16384 139534592 139567360 12 1773 11812 27 _ _ (1875381 / 100000) (234423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139567360 :
    ThetaLowerSegment 139567360 139600128 (6977528378347 / 50000) (6979156229019 / 50000) := by
  exact
    packedTile16384 139567360 139600128 12 1736 11813 27 _ _ (468851 / 25000) (1875407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139600128 :
    ThetaLowerSegment 139600128 139632896 (6979156229019 / 50000) (6980828173081 / 50000) := by
  exact
    packedTile16384 139600128 139632896 12 1783 11815 27 _ _ (468857 / 25000) (1875431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139632896 :
    ThetaLowerSegment 139632896 139665664 (6980828173081 / 50000) (13964895250039 / 100000) := by
  exact
    packedTile16384 139632896 139665664 12 1727 11816 27 _ _ (1875451 / 100000) (937727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139665664 :
    ThetaLowerSegment 139665664 139698432 (13964895250039 / 100000) (6984080226007 / 50000) := by
  exact
    packedTile16384 139665664 139698432 12 1741 11818 27 _ _ (75019 / 4000) (937739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139698432 :
    ThetaLowerSegment 139698432 139731200 (6984080226007 / 50000) (3492874240739 / 25000) := by
  exact
    packedTile16384 139698432 139731200 12 1779 11819 27 _ _ (937749 / 50000) (1875501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139731200 :
    ThetaLowerSegment 139731200 139763968 (3492874240739 / 25000) (6987371745769 / 50000) := by
  exact
    packedTile16384 139731200 139763968 12 1731 11820 27 _ _ (937761 / 50000) (75021 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139763968 :
    ThetaLowerSegment 139763968 139796736 (6987371745769 / 50000) (3494512050457 / 25000) := by
  exact
    packedTile16384 139763968 139796736 12 1762 11822 27 _ _ (375109 / 20000) (468887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139796736 :
    ThetaLowerSegment 139796736 139829504 (3494512050457 / 25000) (6990687730617 / 50000) := by
  exact
    packedTile16384 139796736 139829504 12 1774 11823 27 _ _ (1875569 / 100000) (468893 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139829504 :
    ThetaLowerSegment 139829504 139862272 (6990687730617 / 50000) (6992278232633 / 50000) := by
  exact
    packedTile16384 139829504 139862272 12 1696 11824 27 _ _ (234449 / 12500) (375119 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139862272 :
    ThetaLowerSegment 139862272 139895040 (6992278232633 / 50000) (13987803154831 / 100000) := by
  exact
    packedTile16384 139862272 139895040 12 1731 11826 27 _ _ (375123 / 20000) (937809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139895040 :
    ThetaLowerSegment 139895040 139927808 (13987803154831 / 100000) (6995575585223 / 50000) := by
  exact
    packedTile16384 139895040 139927808 12 1785 11827 27 _ _ (1875639 / 100000) (937821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139927808 :
    ThetaLowerSegment 139927808 139960576 (6995575585223 / 50000) (6997259929699 / 50000) := by
  exact
    packedTile16384 139927808 139960576 12 1796 11829 27 _ _ (937831 / 50000) (375133 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139960576 :
    ThetaLowerSegment 139960576 139993344 (6997259929699 / 50000) (6998897403577 / 50000) := by
  exact
    packedTile16384 139960576 139993344 12 1746 11830 27 _ _ (937843 / 50000) (1875689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell139993344 :
    ThetaLowerSegment 139993344 140026112 (6998897403577 / 50000) (7000518016153 / 50000) := by
  exact
    packedTile16384 139993344 140026112 12 1728 11831 27 _ _ (1875709 / 100000) (58616 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140026112 :
    ThetaLowerSegment 140026112 140058880 (7000518016153 / 50000) (280087946881 / 2000) := by
  exact
    packedTile16384 140026112 140058880 12 1792 11833 27 _ _ (468933 / 25000) (375147 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140058880 :
    ThetaLowerSegment 140058880 140091648 (280087946881 / 2000) (7003828703989 / 50000) := by
  exact
    packedTile16384 140058880 140091648 12 1738 11834 27 _ _ (468939 / 25000) (1875759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140091648 :
    ThetaLowerSegment 140091648 140124416 (7003828703989 / 50000) (14010863114289 / 100000) := by
  exact
    packedTile16384 140091648 140124416 12 1709 11836 27 _ _ (1875779 / 100000) (937891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140124416 :
    ThetaLowerSegment 140124416 140157184 (14010863114289 / 100000) (3503545352449 / 25000) := by
  exact
    packedTile16384 140124416 140157184 12 1769 11837 27 _ _ (1875803 / 100000) (937903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140157184 :
    ThetaLowerSegment 140157184 140189952 (3503545352449 / 25000) (1752182075249 / 12500) := by
  exact
    packedTile16384 140157184 140189952 12 1746 11838 27 _ _ (937913 / 50000) (1875829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140189952 :
    ThetaLowerSegment 140189952 140222720 (1752182075249 / 12500) (350516701387 / 2500) := by
  exact
    packedTile16384 140189952 140222720 12 1712 11840 27 _ _ (1875849 / 100000) (468963 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140222720 :
    ThetaLowerSegment 140222720 140255488 (350516701387 / 2500) (7011952906139 / 50000) := by
  exact
    packedTile16384 140222720 140255488 12 1726 11841 27 _ _ (1875873 / 100000) (468969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140255488 :
    ThetaLowerSegment 140255488 140288256 (7011952906139 / 50000) (7013580245919 / 50000) := by
  exact
    packedTile16384 140255488 140288256 12 1735 11842 27 _ _ (234487 / 12500) (1875899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140288256 :
    ThetaLowerSegment 140288256 140321024 (7013580245919 / 50000) (438453699589 / 3125) := by
  exact
    packedTile16384 140288256 140321024 12 1790 11844 27 _ _ (1875919 / 100000) (937961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140321024 :
    ThetaLowerSegment 140321024 140353792 (438453699589 / 3125) (1754218126101 / 12500) := by
  exact
    packedTile16384 140321024 140353792 12 1720 11845 27 _ _ (1875943 / 100000) (937973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140353792 :
    ThetaLowerSegment 140353792 140386560 (1754218126101 / 12500) (7018535548263 / 50000) := by
  exact
    packedTile16384 140353792 140386560 12 1773 11847 27 _ _ (937983 / 50000) (1875969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140386560 :
    ThetaLowerSegment 140386560 140419328 (7018535548263 / 50000) (7020141395703 / 50000) := by
  exact
    packedTile16384 140386560 140419328 12 1712 11848 27 _ _ (187599 / 10000) (1875993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140419328 :
    ThetaLowerSegment 140419328 140452096 (7020141395703 / 50000) (7021754766883 / 50000) := by
  exact
    packedTile16384 140419328 140452096 12 1720 11849 27 _ _ (1876013 / 100000) (117251 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140452096 :
    ThetaLowerSegment 140452096 140484864 (7021754766883 / 50000) (7023415996761 / 50000) := by
  exact
    packedTile16384 140452096 140484864 12 1771 11851 27 _ _ (469009 / 25000) (1876039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140484864 :
    ThetaLowerSegment 140484864 140517632 (7023415996761 / 50000) (7025038788661 / 50000) := by
  exact
    packedTile16384 140484864 140517632 12 1730 11852 27 _ _ (93803 / 5000) (1876063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140517632 :
    ThetaLowerSegment 140517632 140550400 (7025038788661 / 50000) (3513321419813 / 25000) := by
  exact
    packedTile16384 140517632 140550400 12 1710 11854 27 _ _ (1876083 / 100000) (938043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140550400 :
    ThetaLowerSegment 140550400 140583168 (3513321419813 / 25000) (7028270361581 / 50000) := by
  exact
    packedTile16384 140550400 140583168 12 1735 11855 27 _ _ (938053 / 50000) (1876109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140583168 :
    ThetaLowerSegment 140583168 140615936 (7028270361581 / 50000) (14059867099879 / 100000) := by
  exact
    packedTile16384 140583168 140615936 12 1773 11856 27 _ _ (1876129 / 100000) (469033 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140615936 :
    ThetaLowerSegment 140615936 140648704 (14059867099879 / 100000) (14063169129159 / 100000) := by
  exact
    packedTile16384 140615936 140648704 12 1760 11858 27 _ _ (1876153 / 100000) (469039 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140648704 :
    ThetaLowerSegment 140648704 140681472 (14063169129159 / 100000) (14066443056279 / 100000) := by
  exact
    packedTile16384 140648704 140681472 12 1745 11859 27 _ _ (117261 / 6250) (1876179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140681472 :
    ThetaLowerSegment 140681472 140714240 (14066443056279 / 100000) (7034884778553 / 50000) := by
  exact
    packedTile16384 140681472 140714240 12 1773 11860 27 _ _ (1876199 / 100000) (938101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140714240 :
    ThetaLowerSegment 140714240 140747008 (7034884778553 / 50000) (14073051071133 / 100000) := by
  exact
    packedTile16384 140714240 140747008 12 1749 11862 27 _ _ (1876223 / 100000) (938113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140747008 :
    ThetaLowerSegment 140747008 140779776 (14073051071133 / 100000) (14076250070563 / 100000) := by
  exact
    packedTile16384 140747008 140779776 12 1705 11863 27 _ _ (938123 / 50000) (1876249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140779776 :
    ThetaLowerSegment 140779776 140812544 (14076250070563 / 100000) (7039763956253 / 50000) := by
  exact
    packedTile16384 140779776 140812544 12 1747 11865 27 _ _ (1876269 / 100000) (117267 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140812544 :
    ThetaLowerSegment 140812544 140845312 (7039763956253 / 50000) (1760336417813 / 12500) := by
  exact
    packedTile16384 140812544 140845312 12 1686 11866 27 _ _ (1876293 / 100000) (234537 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140845312 :
    ThetaLowerSegment 140845312 140878080 (1760336417813 / 12500) (88037296189 / 625) := by
  exact
    packedTile16384 140845312 140878080 12 1746 11867 27 _ _ (469079 / 25000) (1876319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140878080 :
    ThetaLowerSegment 140878080 140910848 (88037296189 / 625) (14089144032167 / 100000) := by
  exact
    packedTile16384 140878080 140910848 12 1693 11869 27 _ _ (1876339 / 100000) (938171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140910848 :
    ThetaLowerSegment 140910848 140943616 (14089144032167 / 100000) (14092467069269 / 100000) := by
  exact
    packedTile16384 140910848 140943616 12 1771 11870 27 _ _ (938181 / 50000) (375273 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140943616 :
    ThetaLowerSegment 140943616 140976384 (14092467069269 / 100000) (14095750744769 / 100000) := by
  exact
    packedTile16384 140943616 140976384 12 1750 11871 27 _ _ (938193 / 50000) (1876389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell140976384 :
    ThetaLowerSegment 140976384 141009152 (14095750744769 / 100000) (56395830111 / 400) := by
  exact
    packedTile16384 140976384 141009152 12 1709 11873 27 _ _ (1876409 / 100000) (469103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141009152 :
    ThetaLowerSegment 141009152 141041920 (56395830111 / 400) (7051109383283 / 50000) := by
  exact
    packedTile16384 141009152 141041920 12 1738 11874 27 _ _ (117277 / 6250) (375287 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141041920 :
    ThetaLowerSegment 141041920 141074688 (7051109383283 / 50000) (14105470663081 / 100000) := by
  exact
    packedTile16384 141041920 141074688 12 1733 11876 27 _ _ (375291 / 20000) (938229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141074688 :
    ThetaLowerSegment 141074688 141107456 (14105470663081 / 100000) (7054381941863 / 50000) := by
  exact
    packedTile16384 141074688 141107456 12 1755 11877 27 _ _ (1876479 / 100000) (938241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141107456 :
    ThetaLowerSegment 141107456 141140224 (7054381941863 / 50000) (3528011471431 / 25000) := by
  exact
    packedTile16384 141107456 141140224 12 1749 11878 27 _ _ (938251 / 50000) (375301 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141140224 :
    ThetaLowerSegment 141140224 141172992 (3528011471431 / 25000) (3528822130231 / 25000) := by
  exact
    packedTile16384 141140224 141172992 12 1728 11880 27 _ _ (75061 / 4000) (117283 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141172992 :
    ThetaLowerSegment 141172992 141205760 (3528822130231 / 25000) (441205565924 / 3125) := by
  exact
    packedTile16384 141172992 141205760 12 1753 11881 27 _ _ (469137 / 25000) (1876551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141205760 :
    ThetaLowerSegment 141205760 141238528 (441205565924 / 3125) (3530449576351 / 25000) := by
  exact
    packedTile16384 141205760 141238528 12 1716 11883 27 _ _ (1876571 / 100000) (938287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141238528 :
    ThetaLowerSegment 141238528 141271296 (3530449576351 / 25000) (7062567445657 / 50000) := by
  exact
    packedTile16384 141238528 141271296 12 1778 11884 27 _ _ (375319 / 20000) (938299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141271296 :
    ThetaLowerSegment 141271296 141304064 (7062567445657 / 50000) (883029587171 / 6250) := by
  exact
    packedTile16384 141271296 141304064 12 1779 11885 27 _ _ (938309 / 50000) (1876621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141304064 :
    ThetaLowerSegment 141304064 141336832 (883029587171 / 6250) (7065905031217 / 50000) := by
  exact
    packedTile16384 141304064 141336832 12 1778 11887 27 _ _ (1876641 / 100000) (469161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141336832 :
    ThetaLowerSegment 141336832 141369600 (7065905031217 / 50000) (7067551803877 / 50000) := by
  exact
    packedTile16384 141336832 141369600 12 1755 11888 27 _ _ (234583 / 12500) (1876667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141369600 :
    ThetaLowerSegment 141369600 141402368 (7067551803877 / 50000) (565537989627 / 4000) := by
  exact
    packedTile16384 141369600 141402368 12 1783 11889 27 _ _ (1876687 / 100000) (187669 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141402368 :
    ThetaLowerSegment 141402368 141435136 (565537989627 / 4000) (1767704784083 / 12500) := by
  exact
    packedTile16384 141402368 141435136 12 1699 11891 27 _ _ (1876711 / 100000) (938357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141435136 :
    ThetaLowerSegment 141435136 141467904 (1767704784083 / 12500) (141449300641 / 1000) := by
  exact
    packedTile16384 141435136 141467904 12 1754 11892 27 _ _ (938367 / 50000) (1876737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141467904 :
    ThetaLowerSegment 141467904 141500672 (141449300641 / 1000) (14148103660187 / 100000) := by
  exact
    packedTile16384 141467904 141500672 12 1691 11894 27 _ _ (1876757 / 100000) (46919 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141500672 :
    ThetaLowerSegment 141500672 141533440 (14148103660187 / 100000) (14151363627047 / 100000) := by
  exact
    packedTile16384 141500672 141533440 12 1737 11895 27 _ _ (93839 / 5000) (1876783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141533440 :
    ThetaLowerSegment 141533440 141566208 (14151363627047 / 100000) (14154663046721 / 100000) := by
  exact
    packedTile16384 141533440 141566208 12 1758 11896 27 _ _ (1876803 / 100000) (938403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141566208 :
    ThetaLowerSegment 141566208 141598976 (14154663046721 / 100000) (14157970014133 / 100000) := by
  exact
    packedTile16384 141566208 141598976 12 1762 11898 27 _ _ (938413 / 50000) (1876829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141598976 :
    ThetaLowerSegment 141598976 141631744 (14157970014133 / 100000) (1770156108667 / 12500) := by
  exact
    packedTile16384 141598976 141631744 12 1747 11899 27 _ _ (1876849 / 100000) (469213 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141631744 :
    ThetaLowerSegment 141631744 141664512 (1770156108667 / 12500) (14164565303927 / 100000) := by
  exact
    packedTile16384 141631744 141664512 12 1767 11900 27 _ _ (1876873 / 100000) (469219 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141664512 :
    ThetaLowerSegment 141664512 141697280 (14164565303927 / 100000) (14167823595383 / 100000) := by
  exact
    packedTile16384 141664512 141697280 12 1736 11902 27 _ _ (58653 / 3125) (1876899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141697280 :
    ThetaLowerSegment 141697280 141730048 (14167823595383 / 100000) (2834224643797 / 20000) := by
  exact
    packedTile16384 141697280 141730048 12 1758 11903 27 _ _ (1876919 / 100000) (938461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141730048 :
    ThetaLowerSegment 141730048 141762816 (2834224643797 / 20000) (14174357190051 / 100000) := by
  exact
    packedTile16384 141730048 141762816 12 1723 11905 27 _ _ (938471 / 50000) (375389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141762816 :
    ThetaLowerSegment 141762816 141795584 (14174357190051 / 100000) (14177679418101 / 100000) := by
  exact
    packedTile16384 141762816 141795584 12 1770 11906 27 _ _ (375393 / 20000) (234621 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141795584 :
    ThetaLowerSegment 141795584 141828352 (14177679418101 / 100000) (14180851527821 / 100000) := by
  exact
    packedTile16384 141795584 141828352 12 1690 11907 27 _ _ (469247 / 25000) (1876991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141828352 :
    ThetaLowerSegment 141828352 141861120 (14180851527821 / 100000) (2836825007001 / 20000) := by
  exact
    packedTile16384 141828352 141861120 12 1744 11909 27 _ _ (1877011 / 100000) (938507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141861120 :
    ThetaLowerSegment 141861120 141893888 (2836825007001 / 20000) (14187490556967 / 100000) := by
  exact
    packedTile16384 141861120 141893888 12 1793 11910 27 _ _ (938517 / 50000) (1877037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141893888 :
    ThetaLowerSegment 141893888 141926656 (14187490556967 / 100000) (14190773531409 / 100000) := by
  exact
    packedTile16384 141893888 141926656 12 1749 11911 27 _ _ (938529 / 50000) (1877061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141926656 :
    ThetaLowerSegment 141926656 141959424 (14190773531409 / 100000) (7097043289687 / 50000) := by
  exact
    packedTile16384 141926656 141959424 12 1765 11913 27 _ _ (1877081 / 100000) (469271 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141959424 :
    ThetaLowerSegment 141959424 141992192 (7097043289687 / 50000) (7098660414783 / 50000) := by
  exact
    packedTile16384 141959424 141992192 12 1723 11914 27 _ _ (117319 / 6250) (1877107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell141992192 :
    ThetaLowerSegment 141992192 142024960 (7098660414783 / 50000) (443772216279 / 3125) := by
  exact
    packedTile16384 141992192 142024960 12 1806 11916 27 _ _ (1877127 / 100000) (187713 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142024960 :
    ThetaLowerSegment 142024960 142057728 (443772216279 / 3125) (7101982010939 / 50000) := by
  exact
    packedTile16384 142024960 142057728 12 1733 11917 27 _ _ (37543 / 2000) (1877153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142057728 :
    ThetaLowerSegment 142057728 142090496 (7101982010939 / 50000) (3551827286041 / 25000) := by
  exact
    packedTile16384 142057728 142090496 12 1782 11918 27 _ _ (1877173 / 100000) (234647 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142090496 :
    ThetaLowerSegment 142090496 142123264 (3551827286041 / 25000) (1776317944109 / 12500) := by
  exact
    packedTile16384 142090496 142123264 12 1723 11920 27 _ _ (469299 / 25000) (1877199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142123264 :
    ThetaLowerSegment 142123264 142156032 (1776317944109 / 12500) (1421381366837 / 10000) := by
  exact
    packedTile16384 142123264 142156032 12 1742 11921 27 _ _ (1877219 / 100000) (938611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142156032 :
    ThetaLowerSegment 142156032 142188800 (1421381366837 / 10000) (7108579456807 / 50000) := by
  exact
    packedTile16384 142156032 142188800 12 1782 11922 27 _ _ (938621 / 50000) (375449 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142188800 :
    ThetaLowerSegment 142188800 142221568 (7108579456807 / 50000) (14220476040869 / 100000) := by
  exact
    packedTile16384 142188800 142221568 12 1767 11924 27 _ _ (375453 / 20000) (469317 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142221568 :
    ThetaLowerSegment 142221568 142254336 (14220476040869 / 100000) (14223770681309 / 100000) := by
  exact
    packedTile16384 142221568 142254336 12 1755 11925 27 _ _ (234661 / 12500) (1877291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142254336 :
    ThetaLowerSegment 142254336 142287104 (14223770681309 / 100000) (7113521417191 / 50000) := by
  exact
    packedTile16384 142254336 142287104 12 1743 11927 27 _ _ (1877311 / 100000) (938657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142287104 :
    ThetaLowerSegment 142287104 142319872 (7113521417191 / 50000) (7115135924431 / 50000) := by
  exact
    packedTile16384 142287104 142319872 12 1720 11928 27 _ _ (938667 / 50000) (1877337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142319872 :
    ThetaLowerSegment 142319872 142352640 (7115135924431 / 50000) (7116803017447 / 50000) := by
  exact
    packedTile16384 142319872 142352640 12 1776 11929 27 _ _ (1877357 / 100000) (23467 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142352640 :
    ThetaLowerSegment 142352640 142385408 (7116803017447 / 50000) (7118505801107 / 50000) := by
  exact
    packedTile16384 142352640 142385408 12 1814 11931 27 _ _ (93869 / 5000) (1877383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142385408 :
    ThetaLowerSegment 142385408 142418176 (7118505801107 / 50000) (14240276406031 / 100000) := by
  exact
    packedTile16384 142385408 142418176 12 1739 11932 27 _ _ (1877403 / 100000) (938703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142418176 :
    ThetaLowerSegment 142418176 142450944 (14240276406031 / 100000) (14243464275379 / 100000) := by
  exact
    packedTile16384 142418176 142450944 12 1698 11933 27 _ _ (938713 / 50000) (1877429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142450944 :
    ThetaLowerSegment 142450944 142483712 (14243464275379 / 100000) (7123398373677 / 50000) := by
  exact
    packedTile16384 142450944 142483712 12 1775 11935 27 _ _ (1877449 / 100000) (469363 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142483712 :
    ThetaLowerSegment 142483712 142516480 (7123398373677 / 50000) (1425005040633 / 10000) := by
  exact
    packedTile16384 142483712 142516480 12 1733 11936 27 _ _ (58671 / 3125) (75099 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142516480 :
    ThetaLowerSegment 142516480 142549248 (1425005040633 / 10000) (2850651809057 / 20000) := by
  exact
    packedTile16384 142516480 142549248 12 1709 11938 27 _ _ (375499 / 20000) (938749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142549248 :
    ThetaLowerSegment 142549248 142582016 (2850651809057 / 20000) (14256548456821 / 100000) := by
  exact
    packedTile16384 142549248 142582016 12 1752 11939 27 _ _ (938759 / 50000) (1877521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142582016 :
    ThetaLowerSegment 142582016 142614784 (14256548456821 / 100000) (712990675031 / 5000) := by
  exact
    packedTile16384 142582016 142614784 12 1739 11940 27 _ _ (1877541 / 100000) (234693 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142614784 :
    ThetaLowerSegment 142614784 142647552 (712990675031 / 5000) (1782892802699 / 12500) := by
  exact
    packedTile16384 142614784 142647552 12 1773 11942 27 _ _ (469391 / 25000) (1877567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142647552 :
    ThetaLowerSegment 142647552 142680320 (1782892802699 / 12500) (14266366238471 / 100000) := by
  exact
    packedTile16384 142647552 142680320 12 1717 11943 27 _ _ (1877587 / 100000) (187759 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142680320 :
    ThetaLowerSegment 142680320 142713088 (14266366238471 / 100000) (14269668954461 / 100000) := by
  exact
    packedTile16384 142680320 142713088 12 1759 11944 27 _ _ (187761 / 10000) (1877613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142713088 :
    ThetaLowerSegment 142713088 142745856 (14269668954461 / 100000) (1784116769781 / 12500) := by
  exact
    packedTile16384 142713088 142745856 12 1739 11946 27 _ _ (1877633 / 100000) (469409 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142745856 :
    ThetaLowerSegment 142745856 142778624 (1784116769781 / 12500) (1784529384687 / 12500) := by
  exact
    packedTile16384 142745856 142778624 12 1758 11947 27 _ _ (234707 / 12500) (1877659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142778624 :
    ThetaLowerSegment 142778624 142811392 (1784529384687 / 12500) (7139741731083 / 50000) := by
  exact
    packedTile16384 142778624 142811392 12 1730 11949 27 _ _ (1877679 / 100000) (938841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142811392 :
    ThetaLowerSegment 142811392 142844160 (7139741731083 / 50000) (7141384720333 / 50000) := by
  exact
    packedTile16384 142811392 142844160 12 1750 11950 27 _ _ (938851 / 50000) (375541 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142844160 :
    ThetaLowerSegment 142844160 142876928 (7141384720333 / 50000) (3571538275279 / 25000) := by
  exact
    packedTile16384 142844160 142876928 12 1802 11951 27 _ _ (75109 / 4000) (58679 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142876928 :
    ThetaLowerSegment 142876928 142909696 (3571538275279 / 25000) (3572357912281 / 25000) := by
  exact
    packedTile16384 142876928 142909696 12 1746 11953 27 _ _ (469437 / 25000) (1877751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142909696 :
    ThetaLowerSegment 142909696 142942464 (3572357912281 / 25000) (3573176620437 / 25000) := by
  exact
    packedTile16384 142909696 142942464 12 1744 11954 27 _ _ (1877771 / 100000) (938887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142942464 :
    ThetaLowerSegment 142942464 142975232 (3573176620437 / 25000) (7147995371727 / 50000) := by
  exact
    packedTile16384 142942464 142975232 12 1749 11955 27 _ _ (938897 / 50000) (1877797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell142975232 :
    ThetaLowerSegment 142975232 143008000 (7147995371727 / 50000) (14299233733413 / 100000) := by
  exact
    packedTile16384 142975232 143008000 12 1727 11957 27 _ _ (1877817 / 100000) (93891 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143008000 :
    ThetaLowerSegment 143008000 143040768 (14299233733413 / 100000) (14302595067013 / 100000) := by
  exact
    packedTile16384 143008000 143040768 12 1790 11958 27 _ _ (23473 / 1250) (1877843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143040768 :
    ThetaLowerSegment 143040768 143073536 (14302595067013 / 100000) (7152956625467 / 50000) := by
  exact
    packedTile16384 143040768 143073536 12 1767 11959 27 _ _ (1877863 / 100000) (938933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143073536 :
    ThetaLowerSegment 143073536 143106304 (7152956625467 / 50000) (14309193916029 / 100000) := by
  exact
    packedTile16384 143073536 143106304 12 1747 11961 27 _ _ (375577 / 20000) (58684 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143106304 :
    ThetaLowerSegment 143106304 143139072 (14309193916029 / 100000) (14312433307329 / 100000) := by
  exact
    packedTile16384 143106304 143139072 12 1725 11962 27 _ _ (469477 / 25000) (1877911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143139072 :
    ThetaLowerSegment 143139072 143171840 (14312433307329 / 100000) (447364773072 / 3125) := by
  exact
    packedTile16384 143139072 143171840 12 1725 11964 27 _ _ (1877931 / 100000) (938967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143171840 :
    ThetaLowerSegment 143171840 143204608 (447364773072 / 3125) (447466182588 / 3125) := by
  exact
    packedTile16384 143171840 143204608 12 1728 11965 27 _ _ (938977 / 50000) (1877957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143204608 :
    ThetaLowerSegment 143204608 143237376 (447466182588 / 3125) (14322202424589 / 100000) := by
  exact
    packedTile16384 143204608 143237376 12 1749 11966 27 _ _ (1877977 / 100000) (93899 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143237376 :
    ThetaLowerSegment 143237376 143270144 (14322202424589 / 100000) (14325545264589 / 100000) := by
  exact
    packedTile16384 143237376 143270144 12 1780 11968 27 _ _ (939 / 50) (1878003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143270144 :
    ThetaLowerSegment 143270144 143302912 (14325545264589 / 100000) (7164428109569 / 50000) := by
  exact
    packedTile16384 143270144 143302912 12 1763 11969 27 _ _ (1878023 / 100000) (939013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143302912 :
    ThetaLowerSegment 143302912 143335680 (7164428109569 / 50000) (7166058253497 / 50000) := by
  exact
    packedTile16384 143302912 143335680 12 1736 11970 27 _ _ (939023 / 50000) (1878049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143335680 :
    ThetaLowerSegment 143335680 143368448 (7166058253497 / 50000) (7167720343677 / 50000) := by
  exact
    packedTile16384 143335680 143368448 12 1770 11972 27 _ _ (469517 / 25000) (1878071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143368448 :
    ThetaLowerSegment 143368448 143401216 (7167720343677 / 50000) (89616998964 / 625) := by
  exact
    packedTile16384 143368448 143401216 12 1746 11973 27 _ _ (1878091 / 100000) (939047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143401216 :
    ThetaLowerSegment 143401216 143433984 (89616998964 / 625) (7170994815357 / 50000) := by
  exact
    packedTile16384 143401216 143433984 12 1741 11975 27 _ _ (939057 / 50000) (1878117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143433984 :
    ThetaLowerSegment 143433984 143466752 (7170994815357 / 50000) (3586335995849 / 25000) := by
  exact
    packedTile16384 143433984 143466752 12 1786 11976 27 _ _ (1878137 / 100000) (93907 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143466752 :
    ThetaLowerSegment 143466752 143499520 (3586335995849 / 25000) (3587143135109 / 25000) := by
  exact
    packedTile16384 143466752 143499520 12 1719 11977 27 _ _ (23477 / 1250) (1878163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143499520 :
    ThetaLowerSegment 143499520 143532288 (3587143135109 / 25000) (14351910071627 / 100000) := by
  exact
    packedTile16384 143499520 143532288 12 1777 11979 27 _ _ (1878183 / 100000) (939093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143532288 :
    ThetaLowerSegment 143532288 143565056 (14351910071627 / 100000) (14355206323157 / 100000) := by
  exact
    packedTile16384 143532288 143565056 12 1755 11980 27 _ _ (939103 / 50000) (1878209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143565056 :
    ThetaLowerSegment 143565056 143597824 (14355206323157 / 100000) (14358472561649 / 100000) := by
  exact
    packedTile16384 143565056 143597824 12 1739 11981 27 _ _ (469557 / 25000) (1878231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143597824 :
    ThetaLowerSegment 143597824 143630592 (14358472561649 / 100000) (14361725692381 / 100000) := by
  exact
    packedTile16384 143597824 143630592 12 1732 11983 27 _ _ (1878251 / 100000) (939127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143630592 :
    ThetaLowerSegment 143630592 143663360 (14361725692381 / 100000) (2872997275209 / 20000) := by
  exact
    packedTile16384 143630592 143663360 12 1736 11984 27 _ _ (939137 / 50000) (1878277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143663360 :
    ThetaLowerSegment 143663360 143696128 (2872997275209 / 20000) (14368209533697 / 100000) := by
  exact
    packedTile16384 143663360 143696128 12 1716 11985 27 _ _ (1878297 / 100000) (18783 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143696128 :
    ThetaLowerSegment 143696128 143728896 (14368209533697 / 100000) (14371534160097 / 100000) := by
  exact
    packedTile16384 143696128 143728896 12 1770 11987 27 _ _ (23479 / 1250) (1878323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143728896 :
    ThetaLowerSegment 143728896 143761664 (14371534160097 / 100000) (14374804353519 / 100000) := by
  exact
    packedTile16384 143728896 143761664 12 1741 11988 27 _ _ (939171 / 50000) (375669 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143761664 :
    ThetaLowerSegment 143761664 143794432 (14374804353519 / 100000) (14378117789379 / 100000) := by
  exact
    packedTile16384 143761664 143794432 12 1764 11990 27 _ _ (375673 / 20000) (58699 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143794432 :
    ThetaLowerSegment 143794432 143827200 (14378117789379 / 100000) (14381416238707 / 100000) := by
  exact
    packedTile16384 143794432 143827200 12 1756 11991 27 _ _ (469597 / 25000) (1878391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143827200 :
    ThetaLowerSegment 143827200 143859968 (14381416238707 / 100000) (7192294437443 / 50000) := by
  exact
    packedTile16384 143827200 143859968 12 1689 11992 27 _ _ (1878411 / 100000) (939207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143859968 :
    ThetaLowerSegment 143859968 143892736 (7192294437443 / 50000) (3596986409111 / 25000) := by
  exact
    packedTile16384 143859968 143892736 12 1787 11994 27 _ _ (939217 / 50000) (1878437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143892736 :
    ThetaLowerSegment 143892736 143925504 (3596986409111 / 25000) (3597804476699 / 25000) := by
  exact
    packedTile16384 143892736 143925504 12 1742 11995 27 _ _ (234807 / 12500) (1878459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143925504 :
    ThetaLowerSegment 143925504 143958272 (3597804476699 / 25000) (28789108171 / 200) := by
  exact
    packedTile16384 143925504 143958272 12 1776 11996 27 _ _ (1878479 / 100000) (939241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143958272 :
    ThetaLowerSegment 143958272 143991040 (28789108171 / 200) (3599457548247 / 25000) := by
  exact
    packedTile16384 143958272 143991040 12 1744 11998 27 _ _ (939251 / 50000) (375701 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell143991040 :
    ThetaLowerSegment 143991040 144023808 (3599457548247 / 25000) (14401108219113 / 100000) := by
  exact
    packedTile16384 143991040 144023808 12 1745 11999 27 _ _ (75141 / 4000) (58704 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144023808 :
    ThetaLowerSegment 144023808 144056576 (14401108219113 / 100000) (360107590689 / 2500) := by
  exact
    packedTile16384 144023808 144056576 12 1701 12000 27 _ _ (1878547 / 100000) (37571 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144056576 :
    ThetaLowerSegment 144056576 144089344 (360107590689 / 2500) (1440757421793 / 10000) := by
  exact
    packedTile16384 144056576 144089344 12 1741 12002 27 _ _ (187857 / 10000) (1878573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144089344 :
    ThetaLowerSegment 144089344 144122112 (1440757421793 / 10000) (7205447785177 / 50000) := by
  exact
    packedTile16384 144089344 144122112 12 1768 12003 27 _ _ (1878593 / 100000) (469649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144122112 :
    ThetaLowerSegment 144122112 144154880 (7205447785177 / 50000) (7207086877637 / 50000) := by
  exact
    packedTile16384 144122112 144154880 12 1745 12005 27 _ _ (234827 / 12500) (1878619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144154880 :
    ThetaLowerSegment 144154880 144187648 (7207086877637 / 50000) (1441748391543 / 10000) := by
  exact
    packedTile16384 144154880 144187648 12 1762 12006 27 _ _ (939319 / 50000) (1878641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144187648 :
    ThetaLowerSegment 144187648 144220416 (1441748391543 / 10000) (1442082793201 / 10000) := by
  exact
    packedTile16384 144187648 144220416 12 1780 12007 27 _ _ (1878661 / 100000) (234833 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144220416 :
    ThetaLowerSegment 144220416 144253184 (1442082793201 / 10000) (7212055935821 / 50000) := by
  exact
    packedTile16384 144220416 144253184 12 1748 12009 27 _ _ (469671 / 25000) (1878687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144253184 :
    ThetaLowerSegment 144253184 144285952 (7212055935821 / 50000) (1442731318837 / 10000) := by
  exact
    packedTile16384 144253184 144285952 12 1704 12010 27 _ _ (1878707 / 100000) (187871 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144285952 :
    ThetaLowerSegment 144285952 144318720 (1442731318837 / 10000) (14430640417429 / 100000) := by
  exact
    packedTile16384 144285952 144318720 12 1771 12011 27 _ _ (1878729 / 100000) (469683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144318720 :
    ThetaLowerSegment 144318720 144351488 (14430640417429 / 100000) (14433913203413 / 100000) := by
  exact
    packedTile16384 144318720 144351488 12 1742 12013 27 _ _ (58711 / 3125) (375751 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144351488 :
    ThetaLowerSegment 144351488 144384256 (14433913203413 / 100000) (14437193544563 / 100000) := by
  exact
    packedTile16384 144351488 144384256 12 1746 12014 27 _ _ (75151 / 4000) (939389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144384256 :
    ThetaLowerSegment 144384256 144417024 (14437193544563 / 100000) (7220267962213 / 50000) := by
  exact
    packedTile16384 144384256 144417024 12 1779 12016 27 _ _ (1878797 / 100000) (4697 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144417024 :
    ThetaLowerSegment 144417024 144449792 (7220267962213 / 50000) (7221928839093 / 50000) := by
  exact
    packedTile16384 144417024 144449792 12 1768 12017 27 _ _ (93941 / 5000) (1878823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144449792 :
    ThetaLowerSegment 144449792 144482560 (7221928839093 / 50000) (7223548401759 / 50000) := by
  exact
    packedTile16384 144449792 144482560 12 1724 12018 27 _ _ (1878843 / 100000) (939423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144482560 :
    ThetaLowerSegment 144482560 144515328 (7223548401759 / 50000) (3612577415667 / 25000) := by
  exact
    packedTile16384 144482560 144515328 12 1710 12020 27 _ _ (375773 / 20000) (469717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144515328 :
    ThetaLowerSegment 144515328 144548096 (3612577415667 / 25000) (3613398489723 / 25000) := by
  exact
    packedTile16384 144515328 144548096 12 1748 12021 27 _ _ (234861 / 12500) (1878891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144548096 :
    ThetaLowerSegment 144548096 144580864 (3613398489723 / 25000) (7228414721817 / 50000) := by
  exact
    packedTile16384 144548096 144580864 12 1722 12022 27 _ _ (1878911 / 100000) (939457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144580864 :
    ThetaLowerSegment 144580864 144613632 (7228414721817 / 50000) (1446015891291 / 10000) := by
  exact
    packedTile16384 144580864 144613632 12 1772 12024 27 _ _ (1878933 / 100000) (234867 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144613632 :
    ThetaLowerSegment 144613632 144646400 (1446015891291 / 10000) (7231707571829 / 50000) := by
  exact
    packedTile16384 144613632 144646400 12 1733 12025 27 _ _ (469739 / 25000) (1878959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144646400 :
    ThetaLowerSegment 144646400 144679168 (7231707571829 / 50000) (14466712751803 / 100000) := by
  exact
    packedTile16384 144646400 144679168 12 1755 12026 27 _ _ (1878979 / 100000) (939491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144679168 :
    ThetaLowerSegment 144679168 144711936 (14466712751803 / 100000) (7234993925273 / 50000) := by
  exact
    packedTile16384 144679168 144711936 12 1743 12028 27 _ _ (1879001 / 100000) (469751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144711936 :
    ThetaLowerSegment 144711936 144744704 (7234993925273 / 50000) (7236623039081 / 50000) := by
  exact
    packedTile16384 144711936 144744704 12 1734 12029 27 _ _ (117439 / 6250) (1879027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144744704 :
    ThetaLowerSegment 144744704 144777472 (7236623039081 / 50000) (7238231503313 / 50000) := by
  exact
    packedTile16384 144744704 144777472 12 1712 12030 27 _ _ (1879047 / 100000) (37581 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144777472 :
    ThetaLowerSegment 144777472 144810240 (7238231503313 / 50000) (14479741982031 / 100000) := by
  exact
    packedTile16384 144777472 144810240 12 1745 12032 27 _ _ (1879069 / 100000) (58721 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144810240 :
    ThetaLowerSegment 144810240 144843008 (14479741982031 / 100000) (14482994690283 / 100000) := by
  exact
    packedTile16384 144810240 144843008 12 1731 12033 27 _ _ (469773 / 25000) (375819 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144843008 :
    ThetaLowerSegment 144843008 144875776 (14482994690283 / 100000) (14486211735163 / 100000) := by
  exact
    packedTile16384 144843008 144875776 12 1712 12035 27 _ _ (375823 / 20000) (939559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144875776 :
    ThetaLowerSegment 144875776 144908544 (14486211735163 / 100000) (7244728502381 / 50000) := by
  exact
    packedTile16384 144875776 144908544 12 1727 12036 27 _ _ (1879137 / 100000) (93957 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144908544 :
    ThetaLowerSegment 144908544 144941312 (7244728502381 / 50000) (7246396256881 / 50000) := by
  exact
    packedTile16384 144908544 144941312 12 1775 12037 27 _ _ (46979 / 2500) (1879163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144941312 :
    ThetaLowerSegment 144941312 144974080 (7246396256881 / 50000) (1449599463989 / 10000) := by
  exact
    packedTile16384 144941312 144974080 12 1704 12039 27 _ _ (939591 / 50000) (375837 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell144974080 :
    ThetaLowerSegment 144974080 145006848 (1449599463989 / 10000) (2899853267159 / 20000) := by
  exact
    packedTile16384 144974080 145006848 12 1741 12040 27 _ _ (375841 / 20000) (234901 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145006848 :
    ThetaLowerSegment 145006848 145039616 (2899853267159 / 20000) (2900526030783 / 20000) := by
  exact
    packedTile16384 145006848 145039616 12 1790 12041 27 _ _ (469807 / 25000) (1879231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145039616 :
    ThetaLowerSegment 145039616 145072384 (2900526030783 / 20000) (2901167606733 / 20000) := by
  exact
    packedTile16384 145039616 145072384 12 1707 12043 27 _ _ (7517 / 400) (1879253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145072384 :
    ThetaLowerSegment 145072384 145105152 (2901167606733 / 20000) (14509175622513 / 100000) := by
  exact
    packedTile16384 145072384 145105152 12 1776 12044 27 _ _ (1879273 / 100000) (469819 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145105152 :
    ThetaLowerSegment 145105152 145137920 (14509175622513 / 100000) (3628096834417 / 25000) := by
  exact
    packedTile16384 145105152 145137920 12 1709 12045 27 _ _ (375859 / 20000) (939649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145137920 :
    ThetaLowerSegment 145137920 145170688 (3628096834417 / 25000) (7257823977199 / 50000) := by
  exact
    packedTile16384 145137920 145170688 12 1735 12047 27 _ _ (939659 / 50000) (1879321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145170688 :
    ThetaLowerSegment 145170688 145203456 (7257823977199 / 50000) (14518829678711 / 100000) := by
  exact
    packedTile16384 145170688 145203456 12 1693 12048 27 _ _ (1879341 / 100000) (117459 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145203456 :
    ThetaLowerSegment 145203456 145236224 (14518829678711 / 100000) (7261058342299 / 50000) := by
  exact
    packedTile16384 145203456 145236224 12 1749 12050 27 _ _ (1879363 / 100000) (939683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145236224 :
    ThetaLowerSegment 145236224 145268992 (7261058342299 / 50000) (7262691528733 / 50000) := by
  exact
    packedTile16384 145236224 145268992 12 1738 12051 27 _ _ (939693 / 50000) (1879389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145268992 :
    ThetaLowerSegment 145268992 145301760 (7262691528733 / 50000) (7264349166589 / 50000) := by
  exact
    packedTile16384 145268992 145301760 12 1764 12052 27 _ _ (117463 / 6250) (1879411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145301760 :
    ThetaLowerSegment 145301760 145334528 (7264349166589 / 50000) (14531940351653 / 100000) := by
  exact
    packedTile16384 145301760 145334528 12 1725 12054 27 _ _ (1879431 / 100000) (939717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145334528 :
    ThetaLowerSegment 145334528 145367296 (14531940351653 / 100000) (2907047382443 / 20000) := by
  exact
    packedTile16384 145334528 145367296 12 1754 12055 27 _ _ (1879453 / 100000) (58733 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145367296 :
    ThetaLowerSegment 145367296 145400064 (2907047382443 / 20000) (14538471490411 / 100000) := by
  exact
    packedTile16384 145367296 145400064 12 1721 12056 27 _ _ (469869 / 25000) (1879479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145400064 :
    ThetaLowerSegment 145400064 145432832 (14538471490411 / 100000) (14541790683879 / 100000) := by
  exact
    packedTile16384 145400064 145432832 12 1766 12058 27 _ _ (939749 / 50000) (1879501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145432832 :
    ThetaLowerSegment 145432832 145465600 (14541790683879 / 100000) (14545038496167 / 100000) := by
  exact
    packedTile16384 145432832 145465600 12 1728 12059 27 _ _ (1879521 / 100000) (469881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145465600 :
    ThetaLowerSegment 145465600 145498368 (14545038496167 / 100000) (14548288227743 / 100000) := by
  exact
    packedTile16384 145465600 145498368 12 1729 12060 27 _ _ (234943 / 12500) (1879547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145498368 :
    ThetaLowerSegment 145498368 145531136 (14548288227743 / 100000) (14551568070413 / 100000) := by
  exact
    packedTile16384 145498368 145531136 12 1745 12062 27 _ _ (939783 / 50000) (1879569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145531136 :
    ThetaLowerSegment 145531136 145563904 (14551568070413 / 100000) (909676822333 / 6250) := by
  exact
    packedTile16384 145531136 145563904 12 1735 12063 27 _ _ (1879589 / 100000) (234949 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145563904 :
    ThetaLowerSegment 145563904 145596672 (909676822333 / 6250) (7279062997511 / 50000) := by
  exact
    packedTile16384 145563904 145596672 12 1754 12064 27 _ _ (1879611 / 100000) (939807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145596672 :
    ThetaLowerSegment 145596672 145629440 (7279062997511 / 50000) (7280707677261 / 50000) := by
  exact
    packedTile16384 145596672 145629440 12 1750 12066 27 _ _ (939817 / 50000) (1879637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145629440 :
    ThetaLowerSegment 145629440 145662208 (7280707677261 / 50000) (7282338278841 / 50000) := by
  exact
    packedTile16384 145629440 145662208 12 1735 12067 27 _ _ (234957 / 12500) (1879659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145662208 :
    ThetaLowerSegment 145662208 145694976 (7282338278841 / 50000) (7284026230583 / 50000) := by
  exact
    packedTile16384 145662208 145694976 12 1796 12069 27 _ _ (1879679 / 100000) (939841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145694976 :
    ThetaLowerSegment 145694976 145727744 (7284026230583 / 50000) (14571328780009 / 100000) := by
  exact
    packedTile16384 145694976 145727744 12 1743 12070 27 _ _ (1879701 / 100000) (234963 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145727744 :
    ThetaLowerSegment 145727744 145760512 (14571328780009 / 100000) (14574608898389 / 100000) := by
  exact
    packedTile16384 145727744 145760512 12 1745 12071 27 _ _ (469931 / 25000) (1879727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145760512 :
    ThetaLowerSegment 145760512 145793280 (14574608898389 / 100000) (14577832662779 / 100000) := by
  exact
    packedTile16384 145760512 145793280 12 1715 12073 27 _ _ (939873 / 50000) (1879749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145793280 :
    ThetaLowerSegment 145793280 145826048 (14577832662779 / 100000) (2916229715059 / 20000) := by
  exact
    packedTile16384 145793280 145826048 12 1764 12074 27 _ _ (1879769 / 100000) (469943 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145826048 :
    ThetaLowerSegment 145826048 145858816 (2916229715059 / 20000) (14584351739159 / 100000) := by
  exact
    packedTile16384 145826048 145858816 12 1704 12075 27 _ _ (1879791 / 100000) (939897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145858816 :
    ThetaLowerSegment 145858816 145891584 (14584351739159 / 100000) (14587641411909 / 100000) := by
  exact
    packedTile16384 145858816 145891584 12 1750 12077 27 _ _ (1879813 / 100000) (234977 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145891584 :
    ThetaLowerSegment 145891584 145924352 (14587641411909 / 100000) (2918182841277 / 20000) := by
  exact
    packedTile16384 145891584 145924352 12 1741 12078 27 _ _ (469959 / 25000) (1879839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145924352 :
    ThetaLowerSegment 145924352 145957120 (2918182841277 / 20000) (14594205837743 / 100000) := by
  exact
    packedTile16384 145924352 145957120 12 1751 12079 27 _ _ (939929 / 50000) (1879861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145957120 :
    ThetaLowerSegment 145957120 145989888 (14594205837743 / 100000) (14597521947827 / 100000) := by
  exact
    packedTile16384 145957120 145989888 12 1764 12081 27 _ _ (1879881 / 100000) (469971 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell145989888 :
    ThetaLowerSegment 145989888 146022656 (14597521947827 / 100000) (2920175890917 / 20000) := by
  exact
    packedTile16384 145989888 146022656 12 1786 12082 27 _ _ (1879903 / 100000) (939953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146022656 :
    ThetaLowerSegment 146022656 146055424 (2920175890917 / 20000) (14604152405751 / 100000) := by
  exact
    packedTile16384 146022656 146055424 12 1741 12083 27 _ _ (939963 / 50000) (1879929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146055424 :
    ThetaLowerSegment 146055424 146088192 (14604152405751 / 100000) (14607449834543 / 100000) := by
  exact
    packedTile16384 146055424 146088192 12 1754 12085 27 _ _ (469987 / 25000) (1879951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146088192 :
    ThetaLowerSegment 146088192 146120960 (14607449834543 / 100000) (1826345527927 / 12500) := by
  exact
    packedTile16384 146088192 146120960 12 1763 12086 27 _ _ (1879971 / 100000) (939987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146120960 :
    ThetaLowerSegment 146120960 146153728 (1826345527927 / 12500) (7307004545667 / 50000) := by
  exact
    packedTile16384 146120960 146153728 12 1726 12088 27 _ _ (1879993 / 100000) (469999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146153728 :
    ThetaLowerSegment 146153728 146186496 (7307004545667 / 50000) (14617342357929 / 100000) := by
  exact
    packedTile16384 146153728 146186496 12 1773 12089 27 _ _ (376003 / 20000) (940009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146186496 :
    ThetaLowerSegment 146186496 146219264 (14617342357929 / 100000) (14620577903327 / 100000) := by
  exact
    packedTile16384 146186496 146219264 12 1721 12090 27 _ _ (940019 / 50000) (1880041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146219264 :
    ThetaLowerSegment 146219264 146252032 (14620577903327 / 100000) (14623898089287 / 100000) := by
  exact
    packedTile16384 146219264 146252032 12 1766 12092 27 _ _ (94003 / 5000) (1880063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146252032 :
    ThetaLowerSegment 146252032 146284800 (14623898089287 / 100000) (914202672309 / 6250) := by
  exact
    packedTile16384 146252032 146284800 12 1779 12093 27 _ _ (1880083 / 100000) (940043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146284800 :
    ThetaLowerSegment 146284800 146317568 (914202672309 / 6250) (7315228868247 / 50000) := by
  exact
    packedTile16384 146284800 146317568 12 1710 12094 27 _ _ (376021 / 20000) (470027 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146317568 :
    ThetaLowerSegment 146317568 146350336 (7315228868247 / 50000) (914606427231 / 6250) := by
  exact
    packedTile16384 146317568 146350336 12 1726 12096 27 _ _ (1880127 / 100000) (188013 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146350336 :
    ThetaLowerSegment 146350336 146383104 (914606427231 / 6250) (7318480567823 / 50000) := by
  exact
    packedTile16384 146350336 146383104 12 1733 12097 27 _ _ (37603 / 2000) (1880153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146383104 :
    ThetaLowerSegment 146383104 146415872 (7318480567823 / 50000) (7320123838151 / 50000) := by
  exact
    packedTile16384 146383104 146415872 12 1748 12098 27 _ _ (470043 / 25000) (75207 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146415872 :
    ThetaLowerSegment 146415872 146448640 (7320123838151 / 50000) (915213605317 / 6250) := by
  exact
    packedTile16384 146415872 146448640 12 1686 12100 27 _ _ (376039 / 20000) (940099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146448640 :
    ThetaLowerSegment 146448640 146481408 (915213605317 / 6250) (7323354032411 / 50000) := by
  exact
    packedTile16384 146448640 146481408 12 1750 12101 27 _ _ (1880217 / 100000) (94011 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146481408 :
    ThetaLowerSegment 146481408 146514176 (7323354032411 / 50000) (7325016163687 / 50000) := by
  exact
    packedTile16384 146481408 146514176 12 1768 12102 27 _ _ (1880239 / 100000) (940121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146514176 :
    ThetaLowerSegment 146514176 146546944 (7325016163687 / 50000) (732666421333 / 5000) := by
  exact
    packedTile16384 146514176 146546944 12 1753 12104 27 _ _ (940131 / 50000) (376053 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146546944 :
    ThetaLowerSegment 146546944 146579712 (732666421333 / 5000) (3664147209779 / 25000) := by
  exact
    packedTile16384 146546944 146579712 12 1734 12105 27 _ _ (470071 / 25000) (1880287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146579712 :
    ThetaLowerSegment 146579712 146612480 (3664147209779 / 25000) (7329916183483 / 50000) := by
  exact
    packedTile16384 146579712 146612480 12 1725 12107 27 _ _ (940153 / 50000) (1880309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146612480 :
    ThetaLowerSegment 146612480 146645248 (7329916183483 / 50000) (3665776975021 / 25000) := by
  exact
    packedTile16384 146612480 146645248 12 1742 12108 27 _ _ (1880329 / 100000) (470083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146645248 :
    ThetaLowerSegment 146645248 146678016 (3665776975021 / 25000) (14666426719599 / 100000) := by
  exact
    packedTile16384 146645248 146678016 12 1765 12109 27 _ _ (1880351 / 100000) (940177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146678016 :
    ThetaLowerSegment 146678016 146710784 (14666426719599 / 100000) (14669713613351 / 100000) := by
  exact
    packedTile16384 146678016 146710784 12 1748 12111 27 _ _ (940187 / 50000) (1880377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146710784 :
    ThetaLowerSegment 146710784 146743552 (14669713613351 / 100000) (14673051316251 / 100000) := by
  exact
    packedTile16384 146710784 146743552 12 1775 12112 27 _ _ (470099 / 25000) (1880399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146743552 :
    ThetaLowerSegment 146743552 146776320 (14673051316251 / 100000) (14676279993957 / 100000) := by
  exact
    packedTile16384 146743552 146776320 12 1717 12113 27 _ _ (940209 / 50000) (1880421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146776320 :
    ThetaLowerSegment 146776320 146809088 (14676279993957 / 100000) (14679559483061 / 100000) := by
  exact
    packedTile16384 146776320 146809088 12 1744 12115 27 _ _ (1880441 / 100000) (470111 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146809088 :
    ThetaLowerSegment 146809088 146841856 (14679559483061 / 100000) (14682744987383 / 100000) := by
  exact
    packedTile16384 146809088 146841856 12 1694 12116 27 _ _ (1880463 / 100000) (940233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146841856 :
    ThetaLowerSegment 146841856 146874624 (14682744987383 / 100000) (14686073445833 / 100000) := by
  exact
    packedTile16384 146841856 146874624 12 1770 12117 27 _ _ (376097 / 20000) (235061 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146874624 :
    ThetaLowerSegment 146874624 146907392 (14686073445833 / 100000) (1468936621359 / 10000) := by
  exact
    packedTile16384 146874624 146907392 12 1751 12119 27 _ _ (1880507 / 100000) (188051 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146907392 :
    ThetaLowerSegment 146907392 146940160 (1468936621359 / 10000) (1469274364547 / 10000) := by
  exact
    packedTile16384 146907392 146940160 12 1796 12120 27 _ _ (188053 / 10000) (1880533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146940160 :
    ThetaLowerSegment 146940160 146972928 (1469274364547 / 10000) (1469603461147 / 10000) := by
  exact
    packedTile16384 146940160 146972928 12 1750 12121 27 _ _ (235069 / 12500) (376111 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell146972928 :
    ThetaLowerSegment 146972928 147005696 (1469603461147 / 10000) (7349657166263 / 50000) := by
  exact
    packedTile16384 146972928 147005696 12 1744 12123 27 _ _ (940287 / 50000) (1880577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147005696 :
    ThetaLowerSegment 147005696 147038464 (7349657166263 / 50000) (1470264675041 / 10000) := by
  exact
    packedTile16384 147005696 147038464 12 1772 12124 27 _ _ (1880597 / 100000) (9403 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147038464 :
    ThetaLowerSegment 147038464 147071232 (1470264675041 / 10000) (14705950997993 / 100000) := by
  exact
    packedTile16384 147038464 147071232 12 1757 12125 27 _ _ (1880619 / 100000) (940311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147071232 :
    ThetaLowerSegment 147071232 147104000 (14705950997993 / 100000) (14709234597179 / 100000) := by
  exact
    packedTile16384 147071232 147104000 12 1746 12127 27 _ _ (1880641 / 100000) (470161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147104000 :
    ThetaLowerSegment 147104000 147136768 (14709234597179 / 100000) (14712525759179 / 100000) := by
  exact
    packedTile16384 147104000 147136768 12 1750 12128 27 _ _ (235083 / 12500) (1880667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147136768 :
    ThetaLowerSegment 147136768 147169536 (14712525759179 / 100000) (14715741732239 / 100000) := by
  exact
    packedTile16384 147136768 147169536 12 1710 12129 27 _ _ (940343 / 50000) (1880689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147169536 :
    ThetaLowerSegment 147169536 147202304 (14715741732239 / 100000) (2943801704407 / 20000) := by
  exact
    packedTile16384 147169536 147202304 12 1737 12131 27 _ _ (470177 / 25000) (1880711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147202304 :
    ThetaLowerSegment 147202304 147235072 (2943801704407 / 20000) (2944465602097 / 20000) := by
  exact
    packedTile16384 147202304 147235072 12 1765 12132 27 _ _ (188073 / 10000) (1880733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147235072 :
    ThetaLowerSegment 147235072 147267840 (2944465602097 / 20000) (14725574190163 / 100000) := by
  exact
    packedTile16384 147235072 147267840 12 1726 12134 27 _ _ (1880753 / 100000) (470189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147267840 :
    ThetaLowerSegment 147267840 147300608 (14725574190163 / 100000) (14728820407813 / 100000) := by
  exact
    packedTile16384 147267840 147300608 12 1726 12135 27 _ _ (75231 / 4000) (940389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147300608 :
    ThetaLowerSegment 147300608 147333376 (14728820407813 / 100000) (14732130610533 / 100000) := by
  exact
    packedTile16384 147300608 147333376 12 1760 12136 27 _ _ (1880797 / 100000) (2351 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147333376 :
    ThetaLowerSegment 147333376 147366144 (14732130610533 / 100000) (1473544649443 / 10000) := by
  exact
    packedTile16384 147333376 147366144 12 1763 12138 27 _ _ (1880819 / 100000) (940411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147366144 :
    ThetaLowerSegment 147366144 147398912 (1473544649443 / 10000) (36846539283 / 250) := by
  exact
    packedTile16384 147366144 147398912 12 1685 12139 27 _ _ (940421 / 50000) (376169 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147398912 :
    ThetaLowerSegment 147398912 147431680 (36846539283 / 250) (921362971213 / 6250) := by
  exact
    packedTile16384 147398912 147431680 12 1697 12140 27 _ _ (58777 / 3125) (1880867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147431680 :
    ThetaLowerSegment 147431680 147464448 (921362971213 / 6250) (1474511225611 / 10000) := by
  exact
    packedTile16384 147431680 147464448 12 1757 12142 27 _ _ (940443 / 50000) (1880889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147464448 :
    ThetaLowerSegment 147464448 147497216 (1474511225611 / 10000) (1474843205873 / 10000) := by
  exact
    packedTile16384 147464448 147497216 12 1765 12143 27 _ _ (470227 / 25000) (1880911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147497216 :
    ThetaLowerSegment 147497216 147529984 (1474843205873 / 10000) (1475177635227 / 10000) := by
  exact
    packedTile16384 147497216 147529984 12 1778 12144 27 _ _ (188093 / 10000) (1880933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147529984 :
    ThetaLowerSegment 147529984 147562752 (1475177635227 / 10000) (14755092472409 / 100000) := by
  exact
    packedTile16384 147529984 147562752 12 1763 12146 27 _ _ (1880953 / 100000) (470239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147562752 :
    ThetaLowerSegment 147562752 147595520 (14755092472409 / 100000) (7379174220067 / 50000) := by
  exact
    packedTile16384 147562752 147595520 12 1731 12147 27 _ _ (75239 / 4000) (940489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147595520 :
    ThetaLowerSegment 147595520 147628288 (7379174220067 / 50000) (295231976059 / 2000) := by
  exact
    packedTile16384 147595520 147628288 12 1728 12148 27 _ _ (1880997 / 100000) (1881 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147628288 :
    ThetaLowerSegment 147628288 147661056 (295231976059 / 2000) (7382469746347 / 50000) := by
  exact
    packedTile16384 147628288 147661056 12 1776 12150 27 _ _ (1881019 / 100000) (940511 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147661056 :
    ThetaLowerSegment 147661056 147693824 (7382469746347 / 50000) (923008696571 / 6250) := by
  exact
    packedTile16384 147661056 147693824 12 1701 12151 27 _ _ (940521 / 50000) (376209 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147693824 :
    ThetaLowerSegment 147693824 147726592 (923008696571 / 6250) (1846422527301 / 12500) := by
  exact
    packedTile16384 147693824 147726592 12 1723 12152 27 _ _ (235133 / 12500) (1881067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147726592 :
    ThetaLowerSegment 147726592 147759360 (1846422527301 / 12500) (7387344524341 / 50000) := by
  exact
    packedTile16384 147726592 147759360 12 1759 12154 27 _ _ (940543 / 50000) (1881089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147759360 :
    ThetaLowerSegment 147759360 147792128 (7387344524341 / 50000) (7388935941709 / 50000) := by
  exact
    packedTile16384 147759360 147792128 12 1692 12155 27 _ _ (470277 / 25000) (1881111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147792128 :
    ThetaLowerSegment 147792128 147824896 (7388935941709 / 50000) (7390593217239 / 50000) := by
  exact
    packedTile16384 147792128 147824896 12 1762 12156 27 _ _ (188113 / 10000) (1881133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147824896 :
    ThetaLowerSegment 147824896 147857664 (7390593217239 / 50000) (7392239225239 / 50000) := by
  exact
    packedTile16384 147824896 147857664 12 1750 12158 27 _ _ (58786 / 3125) (376231 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147857664 :
    ThetaLowerSegment 147857664 147890432 (7392239225239 / 50000) (14787674566803 / 100000) := by
  exact
    packedTile16384 147857664 147890432 12 1699 12159 27 _ _ (75247 / 4000) (940589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147890432 :
    ThetaLowerSegment 147890432 147923200 (14787674566803 / 100000) (1848886587719 / 12500) := by
  exact
    packedTile16384 147890432 147923200 12 1817 12161 27 _ _ (1881197 / 100000) (4703 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147923200 :
    ThetaLowerSegment 147923200 147955968 (1848886587719 / 12500) (14794334042089 / 100000) := by
  exact
    packedTile16384 147923200 147955968 12 1723 12162 27 _ _ (1881219 / 100000) (940611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147955968 :
    ThetaLowerSegment 147955968 147988736 (14794334042089 / 100000) (14797626213839 / 100000) := by
  exact
    packedTile16384 147955968 147988736 12 1750 12163 27 _ _ (1881241 / 100000) (470311 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell147988736 :
    ThetaLowerSegment 147988736 148021504 (14797626213839 / 100000) (7400424408679 / 50000) := by
  exact
    packedTile16384 147988736 148021504 12 1713 12165 27 _ _ (1881263 / 100000) (940633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148021504 :
    ThetaLowerSegment 148021504 148054272 (7400424408679 / 50000) (14804214436223 / 100000) := by
  exact
    packedTile16384 148021504 148054272 12 1789 12166 27 _ _ (376257 / 20000) (235161 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148054272 :
    ThetaLowerSegment 148054272 148087040 (14804214436223 / 100000) (7403722320171 / 50000) := by
  exact
    packedTile16384 148054272 148087040 12 1717 12167 27 _ _ (1881307 / 100000) (188131 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148087040 :
    ThetaLowerSegment 148087040 148119808 (7403722320171 / 50000) (3702688474953 / 25000) := by
  exact
    packedTile16384 148087040 148119808 12 1759 12169 27 _ _ (188133 / 10000) (1881333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148119808 :
    ThetaLowerSegment 148119808 148152576 (3702688474953 / 25000) (3703496515637 / 25000) := by
  exact
    packedTile16384 148119808 148152576 12 1718 12170 27 _ _ (235169 / 12500) (376271 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148152576 :
    ThetaLowerSegment 148152576 148185344 (3703496515637 / 25000) (3704320557449 / 25000) := by
  exact
    packedTile16384 148152576 148185344 12 1752 12171 27 _ _ (940687 / 50000) (1881377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148185344 :
    ThetaLowerSegment 148185344 148218112 (3704320557449 / 25000) (3705133320521 / 25000) := by
  exact
    packedTile16384 148185344 148218112 12 1728 12173 27 _ _ (470349 / 25000) (1881399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148218112 :
    ThetaLowerSegment 148218112 148250880 (3705133320521 / 25000) (7411889364067 / 50000) := by
  exact
    packedTile16384 148218112 148250880 12 1725 12174 27 _ _ (940709 / 50000) (1881421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148250880 :
    ThetaLowerSegment 148250880 148283648 (7411889364067 / 50000) (7413544090547 / 50000) := by
  exact
    packedTile16384 148250880 148283648 12 1759 12175 27 _ _ (11759 / 625) (1881443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148283648 :
    ThetaLowerSegment 148283648 148316416 (7413544090547 / 50000) (3707592833071 / 25000) := by
  exact
    packedTile16384 148283648 148316416 12 1745 12177 27 _ _ (940731 / 50000) (376293 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148316416 :
    ThetaLowerSegment 148316416 148349184 (3707592833071 / 25000) (3708399989707 / 25000) := by
  exact
    packedTile16384 148316416 148349184 12 1716 12178 27 _ _ (470371 / 25000) (1881487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148349184 :
    ThetaLowerSegment 148349184 148381952 (3708399989707 / 25000) (92730249451 / 625) := by
  exact
    packedTile16384 148349184 148381952 12 1722 12179 27 _ _ (940753 / 50000) (1881509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148381952 :
    ThetaLowerSegment 148381952 148414720 (92730249451 / 625) (1855024569987 / 12500) := by
  exact
    packedTile16384 148381952 148414720 12 1784 12181 27 _ _ (1881529 / 100000) (470383 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148414720 :
    ThetaLowerSegment 148414720 148447488 (1855024569987 / 12500) (7421695716747 / 50000) := by
  exact
    packedTile16384 148414720 148447488 12 1698 12182 27 _ _ (1881551 / 100000) (940777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148447488 :
    ThetaLowerSegment 148447488 148480256 (7421695716747 / 50000) (463957704837 / 3125) := by
  exact
    packedTile16384 148447488 148480256 12 1730 12183 27 _ _ (1881573 / 100000) (235197 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148480256 :
    ThetaLowerSegment 148480256 148513024 (463957704837 / 3125) (14849986385909 / 100000) := by
  exact
    packedTile16384 148480256 148513024 12 1775 12185 27 _ _ (376319 / 20000) (940799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148513024 :
    ThetaLowerSegment 148513024 148545792 (14849986385909 / 100000) (14853282978893 / 100000) := by
  exact
    packedTile16384 148513024 148545792 12 1752 12186 27 _ _ (1881617 / 100000) (94081 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148545792 :
    ThetaLowerSegment 148545792 148578560 (14853282978893 / 100000) (2971303126939 / 20000) := by
  exact
    packedTile16384 148545792 148578560 12 1718 12187 27 _ _ (1881639 / 100000) (940821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148578560 :
    ThetaLowerSegment 148578560 148611328 (2971303126939 / 20000) (928742620389 / 6250) := by
  exact
    packedTile16384 148578560 148611328 12 1789 12189 27 _ _ (1881661 / 100000) (58802 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148611328 :
    ThetaLowerSegment 148611328 148644096 (928742620389 / 6250) (14863146646229 / 100000) := by
  exact
    packedTile16384 148611328 148644096 12 1735 12190 27 _ _ (1881683 / 100000) (940843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148644096 :
    ThetaLowerSegment 148644096 148676864 (14863146646229 / 100000) (14866417049519 / 100000) := by
  exact
    packedTile16384 148644096 148676864 12 1738 12191 27 _ _ (376341 / 20000) (470427 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148676864 :
    ThetaLowerSegment 148676864 148709632 (14866417049519 / 100000) (2973937498209 / 20000) := by
  exact
    packedTile16384 148676864 148709632 12 1738 12193 27 _ _ (1881727 / 100000) (188173 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148709632 :
    ThetaLowerSegment 148709632 148742400 (2973937498209 / 20000) (2974592346861 / 20000) := by
  exact
    packedTile16384 148709632 148742400 12 1740 12194 27 _ _ (1881749 / 100000) (235219 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148742400 :
    ThetaLowerSegment 148742400 148775168 (2974592346861 / 20000) (1487630187783 / 10000) := by
  exact
    packedTile16384 148742400 148775168 12 1775 12195 27 _ _ (1881771 / 100000) (940887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148775168 :
    ThetaLowerSegment 148775168 148807936 (1487630187783 / 10000) (2975890776221 / 20000) := by
  exact
    packedTile16384 148775168 148807936 12 1675 12197 27 _ _ (1881793 / 100000) (470449 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148807936 :
    ThetaLowerSegment 148807936 148840704 (2975890776221 / 20000) (2976562960539 / 20000) := by
  exact
    packedTile16384 148807936 148840704 12 1786 12198 27 _ _ (376363 / 20000) (940909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148840704 :
    ThetaLowerSegment 148840704 148873472 (2976562960539 / 20000) (2977227249 / 20) := by
  exact
    packedTile16384 148840704 148873472 12 1765 12200 27 _ _ (1881837 / 100000) (23523 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148873472 :
    ThetaLowerSegment 148873472 148906240 (2977227249 / 20) (14889356105749 / 100000) := by
  exact
    packedTile16384 148873472 148906240 12 1711 12201 27 _ _ (1881859 / 100000) (940931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148906240 :
    ThetaLowerSegment 148906240 148939008 (14889356105749 / 100000) (14892611759879 / 100000) := by
  exact
    packedTile16384 148906240 148939008 12 1730 12202 27 _ _ (1881881 / 100000) (470471 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148939008 :
    ThetaLowerSegment 148939008 148971776 (14892611759879 / 100000) (1861986489601 / 12500) := by
  exact
    packedTile16384 148939008 148971776 12 1743 12204 27 _ _ (1881903 / 100000) (940953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell148971776 :
    ThetaLowerSegment 148971776 149004544 (1861986489601 / 12500) (3724791616577 / 25000) := by
  exact
    packedTile16384 148971776 149004544 12 1740 12205 27 _ _ (75277 / 4000) (235241 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149004544 :
    ThetaLowerSegment 149004544 149037312 (3724791616577 / 25000) (3725619673257 / 25000) := by
  exact
    packedTile16384 149004544 149037312 12 1760 12206 27 _ _ (1881947 / 100000) (37639 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149037312 :
    ThetaLowerSegment 149037312 149070080 (3725619673257 / 25000) (14905668630483 / 100000) := by
  exact
    packedTile16384 149037312 149070080 12 1695 12208 27 _ _ (1881969 / 100000) (470493 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149070080 :
    ThetaLowerSegment 149070080 149102848 (14905668630483 / 100000) (7454457532479 / 50000) := by
  exact
    packedTile16384 149070080 149102848 12 1725 12209 27 _ _ (1881991 / 100000) (940997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149102848 :
    ThetaLowerSegment 149102848 149135616 (7454457532479 / 50000) (2982441341139 / 20000) := by
  exact
    packedTile16384 149102848 149135616 12 1749 12210 27 _ _ (1882013 / 100000) (58813 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149135616 :
    ThetaLowerSegment 149135616 149168384 (2982441341139 / 20000) (745773601821 / 5000) := by
  exact
    packedTile16384 149135616 149168384 12 1735 12212 27 _ _ (376407 / 20000) (941019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149168384 :
    ThetaLowerSegment 149168384 149201152 (745773601821 / 5000) (14918722348859 / 100000) := by
  exact
    packedTile16384 149168384 149201152 12 1727 12213 27 _ _ (1882057 / 100000) (94103 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149201152 :
    ThetaLowerSegment 149201152 149233920 (14918722348859 / 100000) (14922015987109 / 100000) := by
  exact
    packedTile16384 149201152 149233920 12 1750 12214 27 _ _ (1882079 / 100000) (941041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149233920 :
    ThetaLowerSegment 149233920 149266688 (14922015987109 / 100000) (932832912673 / 6250) := by
  exact
    packedTile16384 149233920 149266688 12 1759 12216 27 _ _ (1882101 / 100000) (235263 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149266688 :
    ThetaLowerSegment 149266688 149299456 (932832912673 / 6250) (14928588321927 / 100000) := by
  exact
    packedTile16384 149266688 149299456 12 1733 12217 27 _ _ (1882123 / 100000) (941063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149299456 :
    ThetaLowerSegment 149299456 149332224 (14928588321927 / 100000) (3732966284093 / 25000) := by
  exact
    packedTile16384 149299456 149332224 12 1741 12218 27 _ _ (376429 / 20000) (470537 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149332224 :
    ThetaLowerSegment 149332224 149364992 (3732966284093 / 25000) (3733798201907 / 25000) := by
  exact
    packedTile16384 149332224 149364992 12 1768 12220 27 _ _ (1882167 / 100000) (188217 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149364992 :
    ThetaLowerSegment 149364992 149397760 (3733798201907 / 25000) (14938405704251 / 100000) := by
  exact
    packedTile16384 149364992 149397760 12 1707 12221 27 _ _ (1882189 / 100000) (117637 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149397760 :
    ThetaLowerSegment 149397760 149430528 (14938405704251 / 100000) (14941665693703 / 100000) := by
  exact
    packedTile16384 149397760 149430528 12 1732 12222 27 _ _ (1882211 / 100000) (941107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149430528 :
    ThetaLowerSegment 149430528 149463296 (14941665693703 / 100000) (14944876783201 / 100000) := by
  exact
    packedTile16384 149430528 149463296 12 1706 12224 27 _ _ (1882233 / 100000) (470559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149463296 :
    ThetaLowerSegment 149463296 149496064 (14944876783201 / 100000) (14948136848861 / 100000) := by
  exact
    packedTile16384 149463296 149496064 12 1732 12225 27 _ _ (376451 / 20000) (941129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149496064 :
    ThetaLowerSegment 149496064 149528832 (14948136848861 / 100000) (2990286919633 / 20000) := by
  exact
    packedTile16384 149496064 149528832 12 1752 12226 27 _ _ (1882277 / 100000) (47057 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149528832 :
    ThetaLowerSegment 149528832 149561600 (2990286919633 / 20000) (14954732384261 / 100000) := by
  exact
    packedTile16384 149528832 149561600 12 1752 12228 27 _ _ (941149 / 50000) (1882301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149561600 :
    ThetaLowerSegment 149561600 149594368 (14954732384261 / 100000) (14958030208901 / 100000) := by
  exact
    packedTile16384 149561600 149594368 12 1752 12229 27 _ _ (23529 / 1250) (1882323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149594368 :
    ThetaLowerSegment 149594368 149627136 (14958030208901 / 100000) (14961367601267 / 100000) := by
  exact
    packedTile16384 149594368 149627136 12 1773 12230 27 _ _ (941171 / 50000) (376469 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149627136 :
    ThetaLowerSegment 149627136 149659904 (14961367601267 / 100000) (14964558208247 / 100000) := by
  exact
    packedTile16384 149627136 149659904 12 1695 12232 27 _ _ (470591 / 25000) (1882367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149659904 :
    ThetaLowerSegment 149659904 149692672 (14964558208247 / 100000) (14967850501361 / 100000) := by
  exact
    packedTile16384 149659904 149692672 12 1749 12233 27 _ _ (941193 / 50000) (1882389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149692672 :
    ThetaLowerSegment 149692672 149725440 (14967850501361 / 100000) (14971180481113 / 100000) := by
  exact
    packedTile16384 149692672 149725440 12 1769 12234 27 _ _ (235301 / 12500) (1882411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149725440 :
    ThetaLowerSegment 149725440 149758208 (14971180481113 / 100000) (14974521794363 / 100000) := by
  exact
    packedTile16384 149725440 149758208 12 1775 12236 27 _ _ (188243 / 10000) (1882433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149758208 :
    ThetaLowerSegment 149758208 149790976 (14974521794363 / 100000) (14977706903147 / 100000) := by
  exact
    packedTile16384 149758208 149790976 12 1692 12237 27 _ _ (470613 / 25000) (376491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149790976 :
    ThetaLowerSegment 149790976 149823744 (14977706903147 / 100000) (14980897696577 / 100000) := by
  exact
    packedTile16384 149790976 149823744 12 1695 12238 27 _ _ (941237 / 50000) (1882477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149823744 :
    ThetaLowerSegment 149823744 149856512 (14980897696577 / 100000) (14984250421953 / 100000) := by
  exact
    packedTile16384 149823744 149856512 12 1781 12240 27 _ _ (58828 / 3125) (1882499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149856512 :
    ThetaLowerSegment 149856512 149889280 (14984250421953 / 100000) (936721198697 / 6250) := by
  exact
    packedTile16384 149856512 149889280 12 1747 12241 27 _ _ (1882517 / 100000) (47063 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149889280 :
    ThetaLowerSegment 149889280 149922048 (936721198697 / 6250) (3747703699253 / 25000) := by
  exact
    packedTile16384 149889280 149922048 12 1740 12242 27 _ _ (1882539 / 100000) (941271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149922048 :
    ThetaLowerSegment 149922048 149954816 (3747703699253 / 25000) (7497050874259 / 50000) := by
  exact
    packedTile16384 149922048 149954816 12 1746 12244 27 _ _ (1882561 / 100000) (470641 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149954816 :
    ThetaLowerSegment 149954816 149987584 (7497050874259 / 50000) (7498662365307 / 50000) := by
  exact
    packedTile16384 149954816 149987584 12 1712 12245 27 _ _ (1882583 / 100000) (941293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell149987584 :
    ThetaLowerSegment 149987584 150020352 (7498662365307 / 50000) (3750147291921 / 25000) := by
  exact
    packedTile16384 149987584 150020352 12 1734 12246 27 _ _ (376521 / 20000) (117663 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150020352 :
    ThetaLowerSegment 150020352 150053120 (3750147291921 / 25000) (1875483117333 / 12500) := by
  exact
    packedTile16384 150020352 150053120 12 1740 12248 27 _ _ (1882627 / 100000) (188263 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150053120 :
    ThetaLowerSegment 150053120 150085888 (1875483117333 / 12500) (1875891651949 / 12500) := by
  exact
    packedTile16384 150053120 150085888 12 1736 12249 27 _ _ (235331 / 12500) (1882651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150085888 :
    ThetaLowerSegment 150085888 150118656 (1875891651949 / 12500) (3752618268043 / 25000) := by
  exact
    packedTile16384 150085888 150118656 12 1774 12250 27 _ _ (188267 / 10000) (1882673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150118656 :
    ThetaLowerSegment 150118656 150151424 (3752618268043 / 25000) (1876724973617 / 12500) := by
  exact
    packedTile16384 150118656 150151424 12 1767 12252 27 _ _ (470673 / 25000) (376539 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150151424 :
    ThetaLowerSegment 150151424 150184192 (1876724973617 / 12500) (1501696463117 / 10000) := by
  exact
    packedTile16384 150151424 150184192 12 1681 12253 27 _ _ (941357 / 50000) (1882717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150184192 :
    ThetaLowerSegment 150184192 150216960 (1501696463117 / 10000) (7510169247041 / 50000) := by
  exact
    packedTile16384 150184192 150216960 12 1792 12254 27 _ _ (117671 / 6250) (1882739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150216960 :
    ThetaLowerSegment 150216960 150249728 (7510169247041 / 50000) (3755888090497 / 25000) := by
  exact
    packedTile16384 150216960 150249728 12 1707 12256 27 _ _ (941379 / 50000) (1882761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150249728 :
    ThetaLowerSegment 150249728 150282496 (3755888090497 / 25000) (7513404784829 / 50000) := by
  exact
    packedTile16384 150249728 150282496 12 1730 12257 27 _ _ (1882779 / 100000) (941391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150282496 :
    ThetaLowerSegment 150282496 150315264 (7513404784829 / 50000) (15030095057403 / 100000) := by
  exact
    packedTile16384 150282496 150315264 12 1745 12258 27 _ _ (1882801 / 100000) (470701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150315264 :
    ThetaLowerSegment 150315264 150348032 (15030095057403 / 100000) (3006668208851 / 20000) := by
  exact
    packedTile16384 150315264 150348032 12 1724 12260 27 _ _ (1882823 / 100000) (941413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150348032 :
    ThetaLowerSegment 150348032 150380800 (3006668208851 / 20000) (751830577301 / 5000) := by
  exact
    packedTile16384 150348032 150380800 12 1737 12261 27 _ _ (376569 / 20000) (58839 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150380800 :
    ThetaLowerSegment 150380800 150413568 (751830577301 / 5000) (7519926921497 / 50000) := by
  exact
    packedTile16384 150380800 150413568 12 1722 12262 27 _ _ (1882867 / 100000) (188287 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150413568 :
    ThetaLowerSegment 150413568 150446336 (7519926921497 / 50000) (1504314324833 / 10000) := by
  exact
    packedTile16384 150413568 150446336 12 1747 12264 27 _ _ (235361 / 12500) (1882891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150446336 :
    ThetaLowerSegment 150446336 150479104 (1504314324833 / 10000) (752322011187 / 5000) := by
  exact
    packedTile16384 150446336 150479104 12 1751 12265 27 _ _ (188291 / 10000) (1882913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150479104 :
    ThetaLowerSegment 150479104 150511872 (752322011187 / 5000) (1881214330311 / 12500) := by
  exact
    packedTile16384 150479104 150511872 12 1739 12266 27 _ _ (470733 / 25000) (376587 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150511872 :
    ThetaLowerSegment 150511872 150544640 (1881214330311 / 12500) (188163517053 / 1250) := by
  exact
    packedTile16384 150511872 150544640 12 1788 12268 27 _ _ (941477 / 50000) (1882957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150544640 :
    ThetaLowerSegment 150544640 150577408 (188163517053 / 1250) (941017769151 / 6250) := by
  exact
    packedTile16384 150544640 150577408 12 1701 12269 27 _ _ (58843 / 3125) (1882979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150577408 :
    ThetaLowerSegment 150577408 150610176 (941017769151 / 6250) (7529755881637 / 50000) := by
  exact
    packedTile16384 150577408 150610176 12 1714 12270 27 _ _ (1882997 / 100000) (1883 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150610176 :
    ThetaLowerSegment 150610176 150642944 (7529755881637 / 50000) (1882840524211 / 12500) := by
  exact
    packedTile16384 150610176 150642944 12 1706 12272 27 _ _ (1883019 / 100000) (941511 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150642944 :
    ThetaLowerSegment 150642944 150675712 (1882840524211 / 12500) (15066036462807 / 100000) := by
  exact
    packedTile16384 150642944 150675712 12 1759 12273 27 _ _ (1883041 / 100000) (470761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150675712 :
    ThetaLowerSegment 150675712 150708480 (15066036462807 / 100000) (15069279097293 / 100000) := by
  exact
    packedTile16384 150675712 150708480 12 1722 12275 27 _ _ (1883063 / 100000) (941533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150708480 :
    ThetaLowerSegment 150708480 150741248 (15069279097293 / 100000) (3014510379457 / 20000) := by
  exact
    packedTile16384 150708480 150741248 12 1738 12276 27 _ _ (470771 / 25000) (1883087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150741248 :
    ThetaLowerSegment 150741248 150774016 (3014510379457 / 20000) (15075858631421 / 100000) := by
  exact
    packedTile16384 150741248 150774016 12 1756 12277 27 _ _ (941553 / 50000) (1883109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150774016 :
    ThetaLowerSegment 150774016 150806784 (15075858631421 / 100000) (3015841366601 / 20000) := by
  exact
    packedTile16384 150774016 150806784 12 1778 12279 27 _ _ (235391 / 12500) (1883131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150806784 :
    ThetaLowerSegment 150806784 150839552 (3015841366601 / 20000) (15082393121113 / 100000) := by
  exact
    packedTile16384 150806784 150839552 12 1692 12280 27 _ _ (1883149 / 100000) (117697 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150839552 :
    ThetaLowerSegment 150839552 150872320 (15082393121113 / 100000) (15085737632809 / 100000) := by
  exact
    packedTile16384 150839552 150872320 12 1776 12281 27 _ _ (1883171 / 100000) (941587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150872320 :
    ThetaLowerSegment 150872320 150905088 (15085737632809 / 100000) (15088935294523 / 100000) := by
  exact
    packedTile16384 150872320 150905088 12 1698 12283 27 _ _ (1883193 / 100000) (470799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150905088 :
    ThetaLowerSegment 150905088 150937856 (15088935294523 / 100000) (7546058022329 / 50000) := by
  exact
    packedTile16384 150905088 150937856 12 1689 12284 27 _ _ (376643 / 20000) (941609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150937856 :
    ThetaLowerSegment 150937856 150970624 (7546058022329 / 50000) (7547729394279 / 50000) := by
  exact
    packedTile16384 150937856 150970624 12 1775 12285 27 _ _ (470809 / 25000) (1883239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell150970624 :
    ThetaLowerSegment 150970624 151003392 (7547729394279 / 50000) (3774666494233 / 25000) := by
  exact
    packedTile16384 150970624 151003392 12 1703 12287 27 _ _ (941629 / 50000) (1883261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151003392 :
    ThetaLowerSegment 151003392 151036160 (3774666494233 / 25000) (3775488075133 / 25000) := by
  exact
    packedTile16384 151003392 151036160 12 1745 12288 27 _ _ (23541 / 1250) (1883283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151036160 :
    ThetaLowerSegment 151036160 151068928 (3775488075133 / 25000) (7552605205631 / 50000) := by
  exact
    packedTile16384 151036160 151068928 12 1730 12289 27 _ _ (1883301 / 100000) (235413 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151068928 :
    ThetaLowerSegment 151068928 151101696 (7552605205631 / 50000) (15108485509959 / 100000) := by
  exact
    packedTile16384 151068928 151101696 12 1739 12291 27 _ _ (1883323 / 100000) (941663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151101696 :
    ThetaLowerSegment 151101696 151134464 (15108485509959 / 100000) (15111728630049 / 100000) := by
  exact
    packedTile16384 151101696 151134464 12 1722 12292 27 _ _ (376669 / 20000) (470837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151134464 :
    ThetaLowerSegment 151134464 151167232 (15111728630049 / 100000) (15115009455363 / 100000) := by
  exact
    packedTile16384 151134464 151167232 12 1742 12293 27 _ _ (1883367 / 100000) (188337 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151167232 :
    ThetaLowerSegment 151167232 151200000 (15115009455363 / 100000) (15118292200647 / 100000) := by
  exact
    packedTile16384 151167232 151200000 12 1743 12295 27 _ _ (470847 / 25000) (1883391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151200000 :
    ThetaLowerSegment 151200000 151232768 (15118292200647 / 100000) (15121674805007 / 100000) := by
  exact
    packedTile16384 151200000 151232768 12 1796 12296 27 _ _ (188341 / 10000) (1883413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151232768 :
    ThetaLowerSegment 151232768 151265536 (15121674805007 / 100000) (15124961393847 / 100000) := by
  exact
    packedTile16384 151232768 151265536 12 1745 12297 27 _ _ (235429 / 12500) (376687 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151265536 :
    ThetaLowerSegment 151265536 151298304 (15124961393847 / 100000) (7564099524777 / 50000) := by
  exact
    packedTile16384 151265536 151298304 12 1719 12299 27 _ _ (1883453 / 100000) (58858 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151298304 :
    ThetaLowerSegment 151298304 151331072 (7564099524777 / 50000) (7565745681927 / 50000) := by
  exact
    packedTile16384 151298304 151331072 12 1748 12300 27 _ _ (75339 / 4000) (941739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151331072 :
    ThetaLowerSegment 151331072 151363840 (7565745681927 / 50000) (1891841843211 / 12500) := by
  exact
    packedTile16384 151331072 151363840 12 1722 12301 27 _ _ (1883497 / 100000) (3767 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151363840 :
    ThetaLowerSegment 151363840 151396608 (1891841843211 / 12500) (3784496424439 / 25000) := by
  exact
    packedTile16384 151363840 151396608 12 1726 12303 27 _ _ (941759 / 50000) (1883521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151396608 :
    ThetaLowerSegment 151396608 151429376 (3784496424439 / 25000) (1892652937877 / 12500) := by
  exact
    packedTile16384 151396608 151429376 12 1719 12304 27 _ _ (94177 / 5000) (1883543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151429376 :
    ThetaLowerSegment 151429376 151462144 (1892652937877 / 12500) (15144570590913 / 100000) := by
  exact
    packedTile16384 151429376 151462144 12 1777 12305 27 _ _ (1883561 / 100000) (470891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151462144 :
    ThetaLowerSegment 151462144 151494912 (15144570590913 / 100000) (15147806586507 / 100000) := by
  exact
    packedTile16384 151462144 151494912 12 1718 12306 27 _ _ (1883583 / 100000) (941793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151494912 :
    ThetaLowerSegment 151494912 151527680 (15147806586507 / 100000) (3787782787333 / 25000) := by
  exact
    packedTile16384 151494912 151527680 12 1765 12308 27 _ _ (376721 / 20000) (235451 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151527680 :
    ThetaLowerSegment 151527680 151560448 (3787782787333 / 25000) (7577184551213 / 50000) := by
  exact
    packedTile16384 151527680 151560448 12 1719 12309 27 _ _ (941813 / 50000) (1883629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151560448 :
    ThetaLowerSegment 151560448 151593216 (7577184551213 / 50000) (7578832743213 / 50000) := by
  exact
    packedTile16384 151560448 151593216 12 1750 12310 27 _ _ (58864 / 3125) (1883651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151593216 :
    ThetaLowerSegment 151593216 151625984 (7578832743213 / 50000) (1895116235817 / 12500) := by
  exact
    packedTile16384 151593216 151625984 12 1733 12312 27 _ _ (188367 / 10000) (1883673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151625984 :
    ThetaLowerSegment 151625984 151658752 (1895116235817 / 12500) (7582105638129 / 50000) := by
  exact
    packedTile16384 151625984 151658752 12 1742 12313 27 _ _ (1883691 / 100000) (941847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151658752 :
    ThetaLowerSegment 151658752 151691520 (7582105638129 / 50000) (3791867524937 / 25000) := by
  exact
    packedTile16384 151658752 151691520 12 1730 12314 27 _ _ (1883713 / 100000) (470929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151691520 :
    ThetaLowerSegment 151691520 151724288 (3791867524937 / 25000) (7585342816843 / 50000) := by
  exact
    packedTile16384 151691520 151724288 12 1707 12316 27 _ _ (941867 / 50000) (1883737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151724288 :
    ThetaLowerSegment 151724288 151757056 (7585342816843 / 50000) (7586983568319 / 50000) := by
  exact
    packedTile16384 151724288 151757056 12 1742 12317 27 _ _ (470939 / 25000) (1883759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151757056 :
    ThetaLowerSegment 151757056 151789824 (7586983568319 / 50000) (7588611152511 / 50000) := by
  exact
    packedTile16384 151757056 151789824 12 1728 12318 27 _ _ (941889 / 50000) (1883781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151789824 :
    ThetaLowerSegment 151789824 151822592 (7588611152511 / 50000) (15180562280649 / 100000) := by
  exact
    packedTile16384 151789824 151822592 12 1773 12320 27 _ _ (1883799 / 100000) (941901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151822592 :
    ThetaLowerSegment 151822592 151855360 (15180562280649 / 100000) (474495416123 / 3125) := by
  exact
    packedTile16384 151822592 151855360 12 1747 12321 27 _ _ (1883821 / 100000) (117739 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151855360 :
    ThetaLowerSegment 151855360 151888128 (474495416123 / 3125) (7593545820167 / 50000) := by
  exact
    packedTile16384 151855360 151888128 12 1719 12322 27 _ _ (941921 / 50000) (376769 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151888128 :
    ThetaLowerSegment 151888128 151920896 (7593545820167 / 50000) (1519032058323 / 10000) := by
  exact
    packedTile16384 151888128 151920896 12 1714 12324 27 _ _ (235483 / 12500) (1883867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151920896 :
    ThetaLowerSegment 151920896 151953664 (1519032058323 / 10000) (3798396339417 / 25000) := by
  exact
    packedTile16384 151920896 151953664 12 1733 12325 27 _ _ (941943 / 50000) (1883889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151953664 :
    ThetaLowerSegment 151953664 151986432 (3798396339417 / 25000) (15196933060407 / 100000) := by
  exact
    packedTile16384 151953664 151986432 12 1777 12326 27 _ _ (1883907 / 100000) (188391 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell151986432 :
    ThetaLowerSegment 151986432 152019200 (15196933060407 / 100000) (15200180954003 / 100000) := by
  exact
    packedTile16384 151986432 152019200 12 1724 12328 27 _ _ (1883929 / 100000) (470983 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152019200 :
    ThetaLowerSegment 152019200 152051968 (15200180954003 / 100000) (15203410044303 / 100000) := by
  exact
    packedTile16384 152019200 152051968 12 1714 12329 27 _ _ (37679 / 2000) (1883953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152051968 :
    ThetaLowerSegment 152051968 152084736 (15203410044303 / 100000) (15206609028759 / 100000) := by
  exact
    packedTile16384 152051968 152084736 12 1698 12330 27 _ _ (470993 / 25000) (75359 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152084736 :
    ThetaLowerSegment 152084736 152117504 (15206609028759 / 100000) (15209879640607 / 100000) := by
  exact
    packedTile16384 152084736 152117504 12 1736 12332 27 _ _ (1883993 / 100000) (470999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152117504 :
    ThetaLowerSegment 152117504 152150272 (15209879640607 / 100000) (15213116378377 / 100000) := by
  exact
    packedTile16384 152117504 152150272 12 1718 12333 27 _ _ (376803 / 20000) (942009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152150272 :
    ThetaLowerSegment 152150272 152166656 (15213116378377 / 100000) (3042965416613 / 20000) := by
  exact
    packedTile16384 152150272 152166656 11 908 12334 27 _ _ (471009 / 25000) (1884039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152166656 :
    ThetaLowerSegment 152166656 152170752 (3042965416613 / 20000) (15215211428653 / 100000) := by
  exact
    packedTile16384 152166656 152170752 9 204 12335 27 _ _ (1884047 / 100000) (37681 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_128917760_152170752 :
    ThetaLowerSegment 128917760 152170752 (1611321991643 / 12500) (15215211428653 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell128917760 cell128950528)
                      (ThetaLowerSegment.join cell128983296 cell129016064))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell129048832 cell129081600)
                      (ThetaLowerSegment.join cell129114368 cell129147136)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell129179904 cell129212672)
                      (ThetaLowerSegment.join cell129245440 cell129278208))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell129310976 cell129343744)
                      (ThetaLowerSegment.join cell129376512 cell129409280))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell129442048 cell129474816)
                      (ThetaLowerSegment.join cell129507584 cell129540352))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell129573120 cell129605888)
                      (ThetaLowerSegment.join cell129638656 cell129671424)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell129704192 cell129736960)
                      (ThetaLowerSegment.join cell129769728 cell129802496))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell129835264 cell129868032)
                      (ThetaLowerSegment.join cell129900800 cell129933568)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell129966336 cell129999104)
                      (ThetaLowerSegment.join cell130031872 cell130064640))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell130097408 cell130130176)
                      (ThetaLowerSegment.join cell130162944 cell130195712)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell130228480 cell130261248)
                      (ThetaLowerSegment.join cell130294016 cell130326784))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell130359552 cell130392320)
                      (ThetaLowerSegment.join cell130425088 cell130457856))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell130490624 cell130523392)
                      (ThetaLowerSegment.join cell130556160 cell130588928))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell130621696 cell130654464)
                      (ThetaLowerSegment.join cell130687232 cell130720000)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell130752768 cell130785536)
                      (ThetaLowerSegment.join cell130818304 cell130851072))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell130883840 cell130916608)
                      (ThetaLowerSegment.join cell130949376 cell130982144))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell131014912 cell131047680)
                      (ThetaLowerSegment.join cell131080448 cell131113216))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell131145984 cell131178752)
                      (ThetaLowerSegment.join cell131211520 cell131244288)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell131277056 cell131309824)
                      (ThetaLowerSegment.join cell131342592 cell131375360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell131408128 cell131440896)
                      (ThetaLowerSegment.join cell131473664 cell131506432))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell131539200 cell131571968)
                      (ThetaLowerSegment.join cell131604736 cell131637504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell131670272 cell131703040)
                      (ThetaLowerSegment.join cell131735808 cell131768576)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell131801344 cell131834112)
                      (ThetaLowerSegment.join cell131866880 cell131899648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell131932416 cell131965184)
                      (ThetaLowerSegment.join cell131997952 cell132030720)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell132063488 cell132096256)
                      (ThetaLowerSegment.join cell132129024 cell132161792))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell132194560 cell132227328)
                      (ThetaLowerSegment.join cell132260096 cell132292864)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell132325632 cell132358400)
                      (ThetaLowerSegment.join cell132391168 cell132423936))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell132456704 cell132489472)
                      (ThetaLowerSegment.join cell132522240 cell132555008))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell132587776 cell132620544)
                      (ThetaLowerSegment.join cell132653312 cell132686080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell132718848 cell132751616)
                      (ThetaLowerSegment.join cell132784384 cell132817152)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell132849920 cell132882688)
                      (ThetaLowerSegment.join cell132915456 cell132948224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell132980992 cell133013760)
                      (ThetaLowerSegment.join cell133046528 cell133079296)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell133112064 cell133144832)
                      (ThetaLowerSegment.join cell133177600 cell133210368))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell133243136 cell133275904)
                      (ThetaLowerSegment.join cell133308672 cell133341440)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell133374208 cell133406976)
                      (ThetaLowerSegment.join cell133439744 cell133472512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell133505280 cell133538048)
                      (ThetaLowerSegment.join cell133570816 cell133603584))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell133636352 cell133669120)
                      (ThetaLowerSegment.join cell133701888 cell133734656))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell133767424 cell133800192)
                      (ThetaLowerSegment.join cell133832960 cell133865728)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell133898496 cell133931264)
                      (ThetaLowerSegment.join cell133964032 cell133996800))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell134029568 cell134062336)
                      (ThetaLowerSegment.join cell134095104 cell134127872)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell134160640 cell134193408)
                      (ThetaLowerSegment.join cell134226176 cell134258944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell134291712 cell134324480)
                      (ThetaLowerSegment.join cell134357248 cell134390016)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell134422784 cell134455552)
                      (ThetaLowerSegment.join cell134488320 cell134521088))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell134553856 cell134586624)
                      (ThetaLowerSegment.join cell134619392 cell134652160))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell134684928 cell134717696)
                      (ThetaLowerSegment.join cell134750464 cell134783232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell134816000 cell134848768)
                      (ThetaLowerSegment.join cell134881536 cell134914304)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell134947072 cell134979840)
                      (ThetaLowerSegment.join cell135012608 cell135045376))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell135078144 cell135110912)
                      (ThetaLowerSegment.join cell135143680 cell135176448))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell135209216 cell135241984)
                      (ThetaLowerSegment.join cell135274752 cell135307520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell135340288 cell135373056)
                      (ThetaLowerSegment.join cell135405824 cell135438592)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell135471360 cell135504128)
                      (ThetaLowerSegment.join cell135536896 cell135569664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell135602432 cell135635200)
                      (ThetaLowerSegment.join cell135667968 cell135700736))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell135733504 cell135766272)
                      (ThetaLowerSegment.join cell135799040 cell135831808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell135864576 cell135897344)
                      (ThetaLowerSegment.join cell135930112 cell135962880)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell135995648 cell136028416)
                      (ThetaLowerSegment.join cell136061184 cell136093952))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell136126720 cell136159488)
                      (ThetaLowerSegment.join cell136192256 cell136225024)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell136257792 cell136290560)
                      (ThetaLowerSegment.join cell136323328 cell136356096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell136388864 cell136421632)
                      (ThetaLowerSegment.join cell136454400 cell136487168)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell136519936 cell136552704)
                      (ThetaLowerSegment.join cell136585472 cell136618240))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell136651008 cell136683776)
                      (ThetaLowerSegment.join cell136716544 cell136749312))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell136782080 cell136814848)
                      (ThetaLowerSegment.join cell136847616 cell136880384))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell136913152 cell136945920)
                      (ThetaLowerSegment.join cell136978688 cell137011456)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell137044224 cell137076992)
                      (ThetaLowerSegment.join cell137109760 cell137142528))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell137175296 cell137208064)
                      (ThetaLowerSegment.join cell137240832 cell137273600))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell137306368 cell137339136)
                      (ThetaLowerSegment.join cell137371904 cell137404672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell137437440 cell137470208)
                      (ThetaLowerSegment.join cell137502976 cell137535744)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell137568512 cell137601280)
                      (ThetaLowerSegment.join cell137634048 cell137666816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell137699584 cell137732352)
                      (ThetaLowerSegment.join cell137765120 cell137797888))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell137830656 cell137863424)
                      (ThetaLowerSegment.join cell137896192 cell137928960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell137961728 cell137994496)
                      (ThetaLowerSegment.join cell138027264 cell138060032)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell138092800 cell138125568)
                      (ThetaLowerSegment.join cell138158336 cell138191104))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell138223872 cell138256640)
                      (ThetaLowerSegment.join cell138289408 cell138322176)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell138354944 cell138387712)
                      (ThetaLowerSegment.join cell138420480 cell138453248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell138486016 cell138518784)
                      (ThetaLowerSegment.join cell138551552 cell138584320)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell138617088 cell138649856)
                      (ThetaLowerSegment.join cell138682624 cell138715392))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell138748160 cell138780928)
                      (ThetaLowerSegment.join cell138813696 cell138846464))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell138879232 cell138912000)
                      (ThetaLowerSegment.join cell138944768 cell138977536))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell139010304 cell139043072)
                      (ThetaLowerSegment.join cell139075840 cell139108608)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell139141376 cell139174144)
                      (ThetaLowerSegment.join cell139206912 cell139239680))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell139272448 cell139305216)
                      (ThetaLowerSegment.join cell139337984 cell139370752))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell139403520 cell139436288)
                      (ThetaLowerSegment.join cell139469056 cell139501824))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell139534592 cell139567360)
                      (ThetaLowerSegment.join cell139600128 cell139632896)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell139665664 cell139698432)
                      (ThetaLowerSegment.join cell139731200 cell139763968))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell139796736 cell139829504)
                      (ThetaLowerSegment.join cell139862272 cell139895040))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell139927808 cell139960576)
                      (ThetaLowerSegment.join cell139993344 cell140026112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell140058880 cell140091648)
                      (ThetaLowerSegment.join cell140124416 cell140157184)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell140189952 cell140222720)
                      (ThetaLowerSegment.join cell140255488 cell140288256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell140321024 cell140353792)
                      (ThetaLowerSegment.join cell140386560 cell140419328)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell140452096 cell140484864)
                      (ThetaLowerSegment.join cell140517632 cell140550400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell140583168 cell140615936)
                      (ThetaLowerSegment.join cell140648704 cell140681472)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell140714240 cell140747008)
                      (ThetaLowerSegment.join cell140779776 cell140812544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell140845312 cell140878080)
                      (ThetaLowerSegment.join cell140910848 cell140943616))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell140976384 cell141009152)
                      (ThetaLowerSegment.join cell141041920 cell141074688))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell141107456 cell141140224)
                      (ThetaLowerSegment.join cell141172992 cell141205760)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell141238528 cell141271296)
                      (ThetaLowerSegment.join cell141304064 cell141336832))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell141369600 cell141402368)
                      (ThetaLowerSegment.join cell141435136 cell141467904)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell141500672 cell141533440)
                      (ThetaLowerSegment.join cell141566208 cell141598976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell141631744 cell141664512)
                      (ThetaLowerSegment.join cell141697280 cell141730048)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell141762816 cell141795584)
                      (ThetaLowerSegment.join cell141828352 cell141861120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell141893888 cell141926656)
                      (ThetaLowerSegment.join cell141959424 cell141992192))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell142024960 cell142057728)
                      (ThetaLowerSegment.join cell142090496 cell142123264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell142156032 cell142188800)
                      (ThetaLowerSegment.join cell142221568 cell142254336)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell142287104 cell142319872)
                      (ThetaLowerSegment.join cell142352640 cell142385408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell142418176 cell142450944)
                      (ThetaLowerSegment.join cell142483712 cell142516480)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell142549248 cell142582016)
                      (ThetaLowerSegment.join cell142614784 cell142647552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell142680320 cell142713088)
                      (ThetaLowerSegment.join cell142745856 cell142778624)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell142811392 cell142844160)
                      (ThetaLowerSegment.join cell142876928 cell142909696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell142942464 cell142975232)
                      (ThetaLowerSegment.join cell143008000 cell143040768))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell143073536 cell143106304)
                      (ThetaLowerSegment.join cell143139072 cell143171840))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell143204608 cell143237376)
                      (ThetaLowerSegment.join cell143270144 cell143302912)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell143335680 cell143368448)
                      (ThetaLowerSegment.join cell143401216 cell143433984))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell143466752 cell143499520)
                      (ThetaLowerSegment.join cell143532288 cell143565056))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell143597824 cell143630592)
                      (ThetaLowerSegment.join cell143663360 cell143696128))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell143728896 cell143761664)
                      (ThetaLowerSegment.join cell143794432 cell143827200)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell143859968 cell143892736)
                      (ThetaLowerSegment.join cell143925504 cell143958272))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell143991040 cell144023808)
                      (ThetaLowerSegment.join cell144056576 cell144089344))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell144122112 cell144154880)
                      (ThetaLowerSegment.join cell144187648 cell144220416))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell144253184 cell144285952)
                      (ThetaLowerSegment.join cell144318720 cell144351488)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell144384256 cell144417024)
                      (ThetaLowerSegment.join cell144449792 cell144482560))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell144515328 cell144548096)
                      (ThetaLowerSegment.join cell144580864 cell144613632)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell144646400 cell144679168)
                      (ThetaLowerSegment.join cell144711936 cell144744704))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell144777472 cell144810240)
                      (ThetaLowerSegment.join cell144843008 cell144875776)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell144908544 cell144941312)
                      (ThetaLowerSegment.join cell144974080 cell145006848))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell145039616 cell145072384)
                      (ThetaLowerSegment.join cell145105152 cell145137920))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell145170688 cell145203456)
                      (ThetaLowerSegment.join cell145236224 cell145268992))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell145301760 cell145334528)
                      (ThetaLowerSegment.join cell145367296 cell145400064)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell145432832 cell145465600)
                      (ThetaLowerSegment.join cell145498368 cell145531136))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell145563904 cell145596672)
                      (ThetaLowerSegment.join cell145629440 cell145662208)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell145694976 cell145727744)
                    (ThetaLowerSegment.join cell145760512 cell145793280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell145826048 cell145858816)
                    (ThetaLowerSegment.join cell145891584 cell145924352)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell145957120 cell145989888)
                    (ThetaLowerSegment.join cell146022656 cell146055424))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell146088192 cell146120960)
                    (ThetaLowerSegment.join cell146153728 cell146186496))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell146219264 cell146252032)
                    (ThetaLowerSegment.join cell146284800 cell146317568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell146350336 cell146383104)
                    (ThetaLowerSegment.join cell146415872 cell146448640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell146481408 cell146514176)
                    (ThetaLowerSegment.join cell146546944 cell146579712))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell146612480 cell146645248)
                    (ThetaLowerSegment.join cell146678016 cell146710784)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell146743552 cell146776320)
                    (ThetaLowerSegment.join cell146809088 cell146841856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell146874624 cell146907392)
                    (ThetaLowerSegment.join cell146940160 cell146972928)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell147005696 cell147038464)
                    (ThetaLowerSegment.join cell147071232 cell147104000))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell147136768 cell147169536)
                    (ThetaLowerSegment.join cell147202304 cell147235072))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell147267840 cell147300608)
                    (ThetaLowerSegment.join cell147333376 cell147366144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell147398912 cell147431680)
                    (ThetaLowerSegment.join cell147464448 cell147497216)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell147529984 cell147562752)
                    (ThetaLowerSegment.join cell147595520 cell147628288))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell147661056 cell147693824)
                    (ThetaLowerSegment.join cell147726592 cell147759360))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell147792128 cell147824896)
                    (ThetaLowerSegment.join cell147857664 cell147890432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell147923200 cell147955968)
                    (ThetaLowerSegment.join cell147988736 cell148021504)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell148054272 cell148087040)
                    (ThetaLowerSegment.join cell148119808 cell148152576))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell148185344 cell148218112)
                    (ThetaLowerSegment.join cell148250880 cell148283648))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell148316416 cell148349184)
                    (ThetaLowerSegment.join cell148381952 cell148414720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell148447488 cell148480256)
                    (ThetaLowerSegment.join cell148513024 cell148545792)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell148578560 cell148611328)
                    (ThetaLowerSegment.join cell148644096 cell148676864))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell148709632 cell148742400)
                    (ThetaLowerSegment.join cell148775168 cell148807936)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell148840704 cell148873472)
                    (ThetaLowerSegment.join cell148906240 cell148939008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell148971776 cell149004544)
                    (ThetaLowerSegment.join cell149037312 cell149070080)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell149102848 cell149135616)
                    (ThetaLowerSegment.join cell149168384 cell149201152))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell149233920 cell149266688)
                    (ThetaLowerSegment.join cell149299456 cell149332224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell149364992 cell149397760)
                    (ThetaLowerSegment.join cell149430528 cell149463296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell149496064 cell149528832)
                    (ThetaLowerSegment.join cell149561600 cell149594368)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell149627136 cell149659904)
                    (ThetaLowerSegment.join cell149692672 cell149725440))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell149758208 cell149790976)
                    (ThetaLowerSegment.join cell149823744 cell149856512)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell149889280 cell149922048)
                    (ThetaLowerSegment.join cell149954816 cell149987584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell150020352 cell150053120)
                    (ThetaLowerSegment.join cell150085888 cell150118656)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell150151424 cell150184192)
                    (ThetaLowerSegment.join cell150216960 cell150249728))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell150282496 cell150315264)
                    (ThetaLowerSegment.join cell150348032 cell150380800))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell150413568 cell150446336)
                    (ThetaLowerSegment.join cell150479104 cell150511872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell150544640 cell150577408)
                    (ThetaLowerSegment.join cell150610176 cell150642944)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell150675712 cell150708480)
                    (ThetaLowerSegment.join cell150741248 cell150774016))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell150806784 cell150839552)
                    (ThetaLowerSegment.join cell150872320 cell150905088)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell150937856 cell150970624)
                    (ThetaLowerSegment.join cell151003392 cell151036160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell151068928 cell151101696)
                    (ThetaLowerSegment.join cell151134464 cell151167232)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell151200000 cell151232768)
                    (ThetaLowerSegment.join cell151265536 cell151298304))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell151331072 cell151363840)
                    (ThetaLowerSegment.join cell151396608 cell151429376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell151462144 cell151494912)
                    (ThetaLowerSegment.join cell151527680 cell151560448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell151593216 cell151625984)
                    (ThetaLowerSegment.join cell151658752 cell151691520)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell151724288 cell151757056)
                    (ThetaLowerSegment.join cell151789824 cell151822592))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell151855360 cell151888128)
                    (ThetaLowerSegment.join cell151920896 cell151953664))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell151986432 cell152019200)
              (ThetaLowerSegment.join cell152051968 cell152084736))
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell152117504 cell152150272)
              cell152166656)))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
