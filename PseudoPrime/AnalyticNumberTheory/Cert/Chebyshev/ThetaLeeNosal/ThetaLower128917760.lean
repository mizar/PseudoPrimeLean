/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis16384

/-! # Direct theta estimate up to 128917760 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell107667712 :
    ThetaLowerSegment 107667712 107700480 (10765696272917 / 100000) (5384496925591 / 50000) := by
  exact
    packedTile16384 107667712 107700480 12 1783 10376 27 _ _ (369891 / 20000) (924729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107700480 :
    ThetaLowerSegment 107700480 107733248 (5384496925591 / 50000) (673266714977 / 6250) := by
  exact
    packedTile16384 107700480 107733248 12 1770 10377 27 _ _ (369897 / 20000) (115593 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107733248 :
    ThetaLowerSegment 107733248 107766016 (673266714977 / 6250) (10775557726817 / 100000) := by
  exact
    packedTile16384 107733248 107766016 12 1779 10379 27 _ _ (369903 / 20000) (924759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107766016 :
    ThetaLowerSegment 107766016 107798784 (10775557726817 / 100000) (10778831423237 / 100000) := by
  exact
    packedTile16384 107766016 107798784 12 1770 10381 27 _ _ (924773 / 50000) (1849549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107798784 :
    ThetaLowerSegment 107798784 107831552 (10778831423237 / 100000) (10782132916397 / 100000) := by
  exact
    packedTile16384 107798784 107831552 12 1785 10382 27 _ _ (231197 / 12500) (1849579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107831552 :
    ThetaLowerSegment 107831552 107864320 (10782132916397 / 100000) (10785391923931 / 100000) := by
  exact
    packedTile16384 107831552 107864320 12 1762 10384 27 _ _ (1849607 / 100000) (184961 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107864320 :
    ThetaLowerSegment 107864320 107897088 (10785391923931 / 100000) (10788662082147 / 100000) := by
  exact
    packedTile16384 107864320 107897088 12 1768 10385 27 _ _ (1849637 / 100000) (46241 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107897088 :
    ThetaLowerSegment 107897088 107929856 (10788662082147 / 100000) (10791858306723 / 100000) := by
  exact
    packedTile16384 107897088 107929856 12 1728 10387 27 _ _ (1849667 / 100000) (184967 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107929856 :
    ThetaLowerSegment 107929856 107962624 (10791858306723 / 100000) (10795071232149 / 100000) := by
  exact
    packedTile16384 107929856 107962624 12 1737 10388 27 _ _ (924849 / 50000) (1849701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107962624 :
    ThetaLowerSegment 107962624 107995392 (10795071232149 / 100000) (10798334152341 / 100000) := by
  exact
    packedTile16384 107962624 107995392 12 1764 10390 27 _ _ (57804 / 3125) (1849731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell107995392 :
    ThetaLowerSegment 107995392 108028160 (10798334152341 / 100000) (2160307956591 / 20000) := by
  exact
    packedTile16384 107995392 108028160 12 1733 10392 27 _ _ (924879 / 50000) (1849761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108028160 :
    ThetaLowerSegment 108028160 108060928 (2160307956591 / 20000) (5402437476261 / 50000) := by
  exact
    packedTile16384 108028160 108060928 12 1803 10393 27 _ _ (1849789 / 100000) (57806 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108060928 :
    ThetaLowerSegment 108060928 108093696 (5402437476261 / 50000) (1351022341157 / 12500) := by
  exact
    packedTile16384 108060928 108093696 12 1786 10395 27 _ _ (1849819 / 100000) (924911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108093696 :
    ThetaLowerSegment 108093696 108126464 (1351022341157 / 12500) (10811425214251 / 100000) := by
  exact
    packedTile16384 108093696 108126464 12 1755 10396 27 _ _ (1849849 / 100000) (462463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108126464 :
    ThetaLowerSegment 108126464 108159232 (10811425214251 / 100000) (10814714300891 / 100000) := by
  exact
    packedTile16384 108126464 108159232 12 1778 10398 27 _ _ (46247 / 2500) (1849883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108159232 :
    ThetaLowerSegment 108159232 108192000 (10814714300891 / 100000) (10817981241951 / 100000) := by
  exact
    packedTile16384 108159232 108192000 12 1766 10399 27 _ _ (184991 / 10000) (1849913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108192000 :
    ThetaLowerSegment 108192000 108224768 (10817981241951 / 100000) (10821272285211 / 100000) := by
  exact
    packedTile16384 108192000 108224768 12 1779 10401 27 _ _ (92497 / 5000) (1849943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108224768 :
    ThetaLowerSegment 108224768 108257536 (10821272285211 / 100000) (10824642932373 / 100000) := by
  exact
    packedTile16384 108224768 108257536 12 1822 10403 27 _ _ (1849971 / 100000) (924987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108257536 :
    ThetaLowerSegment 108257536 108290304 (10824642932373 / 100000) (10827961834167 / 100000) := by
  exact
    packedTile16384 108257536 108290304 12 1794 10404 27 _ _ (1850001 / 100000) (462501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108290304 :
    ThetaLowerSegment 108290304 108323072 (10827961834167 / 100000) (2707816959891 / 25000) := by
  exact
    packedTile16384 108290304 108323072 12 1787 10406 27 _ _ (1850031 / 100000) (925017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108323072 :
    ThetaLowerSegment 108323072 108355840 (2707816959891 / 25000) (677160059259 / 6250) := by
  exact
    packedTile16384 108323072 108355840 12 1780 10407 27 _ _ (1850061 / 100000) (115629 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108355840 :
    ThetaLowerSegment 108355840 108388608 (677160059259 / 6250) (108378781631 / 1000) := by
  exact
    packedTile16384 108355840 108388608 12 1793 10409 27 _ _ (462523 / 25000) (370019 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108388608 :
    ThetaLowerSegment 108388608 108421376 (108378781631 / 1000) (338786952531 / 3125) := by
  exact
    packedTile16384 108388608 108421376 12 1786 10410 27 _ _ (925061 / 50000) (14801 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108421376 :
    ThetaLowerSegment 108421376 108454144 (338786952531 / 3125) (271112772611 / 2500) := by
  exact
    packedTile16384 108421376 108454144 12 1799 10412 27 _ _ (231269 / 12500) (370031 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108454144 :
    ThetaLowerSegment 108454144 108486912 (271112772611 / 2500) (5423901189109 / 50000) := by
  exact
    packedTile16384 108454144 108486912 12 1779 10414 27 _ _ (925091 / 50000) (370037 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108486912 :
    ThetaLowerSegment 108486912 108519680 (5423901189109 / 50000) (5425573781661 / 50000) := by
  exact
    packedTile16384 108486912 108519680 12 1808 10415 27 _ _ (1850213 / 100000) (231277 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108519680 :
    ThetaLowerSegment 108519680 108552448 (5425573781661 / 50000) (2170888569221 / 20000) := by
  exact
    packedTile16384 108519680 108552448 12 1781 10417 27 _ _ (1850243 / 100000) (925123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108552448 :
    ThetaLowerSegment 108552448 108585216 (2170888569221 / 20000) (10857728930953 / 100000) := by
  exact
    packedTile16384 108552448 108585216 12 1776 10418 27 _ _ (1850273 / 100000) (462569 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108585216 :
    ThetaLowerSegment 108585216 108617984 (10857728930953 / 100000) (1357619713711 / 12500) := by
  exact
    packedTile16384 108585216 108617984 12 1745 10420 27 _ _ (1850303 / 100000) (925153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108617984 :
    ThetaLowerSegment 108617984 108650752 (1357619713711 / 12500) (10864275356757 / 100000) := by
  exact
    packedTile16384 108617984 108650752 12 1793 10421 27 _ _ (1850333 / 100000) (57823 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108650752 :
    ThetaLowerSegment 108650752 108683520 (10864275356757 / 100000) (339609507506 / 3125) := by
  exact
    packedTile16384 108650752 108683520 12 1745 10423 27 _ _ (1850363 / 100000) (925183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108683520 :
    ThetaLowerSegment 108683520 108716288 (339609507506 / 3125) (1358836789931 / 12500) := by
  exact
    packedTile16384 108683520 108716288 12 1724 10425 27 _ _ (925197 / 50000) (1850397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108716288 :
    ThetaLowerSegment 108716288 108749056 (1358836789931 / 12500) (1359253597937 / 12500) := by
  exact
    packedTile16384 108716288 108749056 12 1802 10426 27 _ _ (231303 / 12500) (1850427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108749056 :
    ThetaLowerSegment 108749056 108781824 (1359253597937 / 12500) (5438649267857 / 50000) := by
  exact
    packedTile16384 108749056 108781824 12 1767 10428 27 _ _ (925227 / 50000) (1850457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108781824 :
    ThetaLowerSegment 108781824 108814592 (5438649267857 / 50000) (5440326731603 / 50000) := by
  exact
    packedTile16384 108781824 108814592 12 1813 10429 27 _ _ (462621 / 25000) (1850487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108814592 :
    ThetaLowerSegment 108814592 108847360 (5440326731603 / 50000) (680247752047 / 6250) := by
  exact
    packedTile16384 108814592 108847360 12 1789 10431 27 _ _ (925257 / 50000) (1850517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108847360 :
    ThetaLowerSegment 108847360 108880128 (680247752047 / 6250) (680446685527 / 6250) := by
  exact
    packedTile16384 108847360 108880128 12 1720 10432 27 _ _ (115659 / 6250) (1850547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108880128 :
    ThetaLowerSegment 108880128 108912896 (680446685527 / 6250) (5445184408883 / 50000) := by
  exact
    packedTile16384 108880128 108912896 12 1741 10434 27 _ _ (925287 / 50000) (1850577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108912896 :
    ThetaLowerSegment 108912896 108945664 (5445184408883 / 50000) (5446843475369 / 50000) := by
  exact
    packedTile16384 108912896 108945664 12 1793 10436 27 _ _ (462651 / 25000) (1850607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108945664 :
    ThetaLowerSegment 108945664 108978432 (5446843475369 / 50000) (5448472033289 / 50000) := by
  exact
    packedTile16384 108945664 108978432 12 1760 10437 27 _ _ (925317 / 50000) (1850637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell108978432 :
    ThetaLowerSegment 108978432 109011200 (5448472033289 / 50000) (10900166074343 / 100000) := by
  exact
    packedTile16384 108978432 109011200 12 1741 10439 27 _ _ (370133 / 20000) (462667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109011200 :
    ThetaLowerSegment 109011200 109043968 (10900166074343 / 100000) (5451723678289 / 50000) := by
  exact
    packedTile16384 109011200 109043968 12 1773 10440 27 _ _ (370139 / 20000) (925349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109043968 :
    ThetaLowerSegment 109043968 109076736 (5451723678289 / 50000) (2726691889307 / 25000) := by
  exact
    packedTile16384 109043968 109076736 12 1794 10442 27 _ _ (74029 / 4000) (231341 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109076736 :
    ThetaLowerSegment 109076736 109109504 (2726691889307 / 25000) (1363750334621 / 12500) := by
  exact
    packedTile16384 109076736 109109504 12 1748 10443 27 _ _ (370151 / 20000) (925379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109109504 :
    ThetaLowerSegment 109109504 109142272 (1363750334621 / 12500) (10913306328193 / 100000) := by
  exact
    packedTile16384 109109504 109142272 12 1785 10445 27 _ _ (370157 / 20000) (462697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109142272 :
    ThetaLowerSegment 109142272 109175040 (10913306328193 / 100000) (2729150657427 / 25000) := by
  exact
    packedTile16384 109142272 109175040 12 1781 10447 27 _ _ (370163 / 20000) (925409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109175040 :
    ThetaLowerSegment 109175040 109207808 (2729150657427 / 25000) (5459943014369 / 50000) := by
  exact
    packedTile16384 109175040 109207808 12 1774 10448 27 _ _ (370169 / 20000) (57839 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109207808 :
    ThetaLowerSegment 109207808 109240576 (5459943014369 / 50000) (5461590293119 / 50000) := by
  exact
    packedTile16384 109207808 109240576 12 1780 10450 27 _ _ (14807 / 800) (925439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109240576 :
    ThetaLowerSegment 109240576 109273344 (5461590293119 / 50000) (10926465942613 / 100000) := by
  exact
    packedTile16384 109240576 109273344 12 1775 10451 27 _ _ (370181 / 20000) (462727 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109273344 :
    ThetaLowerSegment 109273344 109306112 (10926465942613 / 100000) (5464875676119 / 50000) := by
  exact
    packedTile16384 109273344 109306112 12 1775 10453 27 _ _ (370187 / 20000) (925469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109306112 :
    ThetaLowerSegment 109306112 109338880 (5464875676119 / 50000) (10932955372653 / 100000) := by
  exact
    packedTile16384 109306112 109338880 12 1731 10454 27 _ _ (370193 / 20000) (231371 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109338880 :
    ThetaLowerSegment 109338880 109371648 (10932955372653 / 100000) (10936179805943 / 100000) := by
  exact
    packedTile16384 109338880 109371648 12 1742 10456 27 _ _ (370199 / 20000) (925499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109371648 :
    ThetaLowerSegment 109371648 109404416 (10936179805943 / 100000) (5469766006109 / 50000) := by
  exact
    packedTile16384 109371648 109404416 12 1811 10458 27 _ _ (74041 / 4000) (462757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109404416 :
    ThetaLowerSegment 109404416 109437184 (5469766006109 / 50000) (10942902783373 / 100000) := by
  exact
    packedTile16384 109404416 109437184 12 1821 10459 27 _ _ (370211 / 20000) (925529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109437184 :
    ThetaLowerSegment 109437184 109469952 (10942902783373 / 100000) (2736548965897 / 25000) := by
  exact
    packedTile16384 109437184 109469952 12 1779 10461 27 _ _ (370217 / 20000) (115693 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109469952 :
    ThetaLowerSegment 109469952 109502720 (2736548965897 / 25000) (2737359754267 / 25000) := by
  exact
    packedTile16384 109469952 109502720 12 1752 10462 27 _ _ (370223 / 20000) (925559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109502720 :
    ThetaLowerSegment 109502720 109535488 (2737359754267 / 25000) (547639294271 / 5000) := by
  exact
    packedTile16384 109502720 109535488 12 1808 10464 27 _ _ (231393 / 12500) (1851147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109535488 :
    ThetaLowerSegment 109535488 109568256 (547639294271 / 5000) (5478015496721 / 50000) := by
  exact
    packedTile16384 109535488 109568256 12 1753 10465 27 _ _ (925587 / 50000) (1851177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109568256 :
    ThetaLowerSegment 109568256 109601024 (5478015496721 / 50000) (5479635300221 / 50000) := by
  exact
    packedTile16384 109568256 109601024 12 1750 10467 27 _ _ (462801 / 25000) (1851207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109601024 :
    ThetaLowerSegment 109601024 109633792 (5479635300221 / 50000) (342580123304 / 3125) := by
  exact
    packedTile16384 109601024 109633792 12 1779 10469 27 _ _ (925617 / 50000) (1851237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109633792 :
    ThetaLowerSegment 109633792 109666560 (342580123304 / 3125) (342684256904 / 3125) := by
  exact
    packedTile16384 109633792 109666560 12 1800 10470 27 _ _ (57852 / 3125) (1851267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109666560 :
    ThetaLowerSegment 109666560 109699328 (342684256904 / 3125) (1371139684061 / 12500) := by
  exact
    packedTile16384 109666560 109699328 12 1740 10472 27 _ _ (925647 / 50000) (1851297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109699328 :
    ThetaLowerSegment 109699328 109732096 (1371139684061 / 12500) (2743097190499 / 25000) := by
  exact
    packedTile16384 109699328 109732096 12 1767 10473 27 _ _ (462831 / 25000) (1851327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109732096 :
    ThetaLowerSegment 109732096 109764864 (2743097190499 / 25000) (1371959132999 / 12500) := by
  exact
    packedTile16384 109732096 109764864 12 1774 10475 27 _ _ (925677 / 50000) (1851357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109764864 :
    ThetaLowerSegment 109764864 109797632 (1371959132999 / 12500) (343094560013 / 3125) := by
  exact
    packedTile16384 109764864 109797632 12 1811 10476 27 _ _ (231423 / 12500) (1851387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109797632 :
    ThetaLowerSegment 109797632 109830400 (343094560013 / 3125) (5491132946583 / 50000) := by
  exact
    packedTile16384 109797632 109830400 12 1750 10478 27 _ _ (1851413 / 100000) (231427 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109830400 :
    ThetaLowerSegment 109830400 109863168 (5491132946583 / 50000) (5492762216423 / 50000) := by
  exact
    packedTile16384 109830400 109863168 12 1760 10480 27 _ _ (1851443 / 100000) (925723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109863168 :
    ThetaLowerSegment 109863168 109895936 (5492762216423 / 50000) (1373607598399 / 12500) := by
  exact
    packedTile16384 109863168 109895936 12 1802 10481 27 _ _ (1851473 / 100000) (462869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109895936 :
    ThetaLowerSegment 109895936 109928704 (1373607598399 / 12500) (2198435365813 / 20000) := by
  exact
    packedTile16384 109895936 109928704 12 1791 10483 27 _ _ (1851503 / 100000) (925753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109928704 :
    ThetaLowerSegment 109928704 109961472 (2198435365813 / 20000) (2748858418903 / 25000) := by
  exact
    packedTile16384 109928704 109961472 12 1759 10484 27 _ _ (1851533 / 100000) (115721 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109961472 :
    ThetaLowerSegment 109961472 109994240 (2748858418903 / 25000) (1099874056713 / 10000) := by
  exact
    packedTile16384 109961472 109994240 12 1786 10486 27 _ _ (1851563 / 100000) (925783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell109994240 :
    ThetaLowerSegment 109994240 110027008 (1099874056713 / 10000) (5501028384201 / 50000) := by
  exact
    packedTile16384 109994240 110027008 12 1791 10487 27 _ _ (231449 / 12500) (370319 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110027008 :
    ThetaLowerSegment 110027008 110059776 (5501028384201 / 50000) (22010627543 / 200) := by
  exact
    packedTile16384 110027008 110059776 12 1759 10489 27 _ _ (925811 / 50000) (14813 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110059776 :
    ThetaLowerSegment 110059776 110092544 (22010627543 / 200) (2752188535229 / 25000) := by
  exact
    packedTile16384 110059776 110092544 12 1858 10490 27 _ _ (462913 / 25000) (370331 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110092544 :
    ThetaLowerSegment 110092544 110125312 (2752188535229 / 25000) (1376498397211 / 12500) := by
  exact
    packedTile16384 110092544 110125312 12 1746 10492 27 _ _ (925841 / 50000) (370337 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110125312 :
    ThetaLowerSegment 110125312 110158080 (1376498397211 / 12500) (1376905773631 / 12500) := by
  exact
    packedTile16384 110125312 110158080 12 1760 10494 27 _ _ (1851711 / 100000) (925857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110158080 :
    ThetaLowerSegment 110158080 110190848 (1376905773631 / 12500) (11018414517899 / 100000) := by
  exact
    packedTile16384 110158080 110190848 12 1711 10495 27 _ _ (1851741 / 100000) (57867 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110190848 :
    ThetaLowerSegment 110190848 110223616 (11018414517899 / 100000) (11021655117149 / 100000) := by
  exact
    packedTile16384 110190848 110223616 12 1750 10497 27 _ _ (1851771 / 100000) (925887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110223616 :
    ThetaLowerSegment 110223616 110256384 (11021655117149 / 100000) (5512450662151 / 50000) := by
  exact
    packedTile16384 110223616 110256384 12 1753 10498 27 _ _ (1851801 / 100000) (462951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110256384 :
    ThetaLowerSegment 110256384 110289152 (5512450662151 / 50000) (1378523540319 / 12500) := by
  exact
    packedTile16384 110256384 110289152 12 1775 10500 27 _ _ (185183 / 10000) (1851833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110289152 :
    ThetaLowerSegment 110289152 110321920 (1378523540319 / 12500) (2757843843403 / 25000) := by
  exact
    packedTile16384 110289152 110321920 12 1721 10501 27 _ _ (92593 / 5000) (1851863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110321920 :
    ThetaLowerSegment 110321920 110354688 (2757843843403 / 25000) (5517275682481 / 50000) := by
  exact
    packedTile16384 110321920 110354688 12 1715 10503 27 _ _ (185189 / 10000) (1851893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110354688 :
    ThetaLowerSegment 110354688 110387456 (5517275682481 / 50000) (5518882223081 / 50000) := by
  exact
    packedTile16384 110354688 110387456 12 1735 10504 27 _ _ (23149 / 1250) (1851923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110387456 :
    ThetaLowerSegment 110387456 110420224 (5518882223081 / 50000) (11041081286821 / 100000) := by
  exact
    packedTile16384 110387456 110420224 12 1791 10506 27 _ _ (1851949 / 100000) (115747 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110420224 :
    ThetaLowerSegment 110420224 110452992 (11041081286821 / 100000) (345138484901 / 3125) := by
  exact
    packedTile16384 110420224 110452992 12 1809 10508 27 _ _ (1851979 / 100000) (925991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110452992 :
    ThetaLowerSegment 110452992 110485760 (345138484901 / 3125) (11047737352897 / 100000) := by
  exact
    packedTile16384 110452992 110485760 12 1785 10509 27 _ _ (1852009 / 100000) (463003 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110485760 :
    ThetaLowerSegment 110485760 110518528 (11047737352897 / 100000) (11050946934751 / 100000) := by
  exact
    packedTile16384 110485760 110518528 12 1733 10511 27 _ _ (926019 / 50000) (1852041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110518528 :
    ThetaLowerSegment 110518528 110551296 (11050946934751 / 100000) (11054215834771 / 100000) := by
  exact
    packedTile16384 110518528 110551296 12 1765 10512 27 _ _ (463017 / 25000) (1852071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110551296 :
    ThetaLowerSegment 110551296 110584064 (11054215834771 / 100000) (88459255997 / 800) := by
  exact
    packedTile16384 110551296 110584064 12 1723 10514 27 _ _ (926049 / 50000) (1852101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110584064 :
    ThetaLowerSegment 110584064 110616832 (88459255997 / 800) (2765191226469 / 25000) := by
  exact
    packedTile16384 110584064 110616832 12 1813 10515 27 _ _ (1852127 / 100000) (185213 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110616832 :
    ThetaLowerSegment 110616832 110649600 (2765191226469 / 25000) (138300586601 / 1250) := by
  exact
    packedTile16384 110616832 110649600 12 1772 10517 27 _ _ (1852157 / 100000) (11576 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110649600 :
    ThetaLowerSegment 110649600 110682368 (138300586601 / 1250) (1383419829581 / 12500) := by
  exact
    packedTile16384 110649600 110682368 12 1788 10519 27 _ _ (926093 / 50000) (1852189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110682368 :
    ThetaLowerSegment 110682368 110715136 (1383419829581 / 12500) (1383822223507 / 12500) := by
  exact
    packedTile16384 110682368 110715136 12 1738 10520 27 _ _ (231527 / 12500) (1852219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110715136 :
    ThetaLowerSegment 110715136 110747904 (1383822223507 / 12500) (5536956841551 / 50000) := by
  exact
    packedTile16384 110715136 110747904 12 1801 10522 27 _ _ (926123 / 50000) (1852249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110747904 :
    ThetaLowerSegment 110747904 110780672 (5536956841551 / 50000) (11077149607527 / 100000) := by
  exact
    packedTile16384 110747904 110780672 12 1747 10523 27 _ _ (74091 / 4000) (926139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110780672 :
    ThetaLowerSegment 110780672 110813440 (11077149607527 / 100000) (11080383732057 / 100000) := by
  exact
    packedTile16384 110780672 110813440 12 1746 10525 27 _ _ (370461 / 20000) (463077 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110813440 :
    ThetaLowerSegment 110813440 110846208 (11080383732057 / 100000) (11083686443579 / 100000) := by
  exact
    packedTile16384 110813440 110846208 12 1783 10526 27 _ _ (926167 / 50000) (1852337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110846208 :
    ThetaLowerSegment 110846208 110878976 (11083686443579 / 100000) (11086976242043 / 100000) := by
  exact
    packedTile16384 110846208 110878976 12 1776 10528 27 _ _ (463091 / 25000) (1852367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110878976 :
    ThetaLowerSegment 110878976 110911744 (11086976242043 / 100000) (2772574395673 / 25000) := by
  exact
    packedTile16384 110878976 110911744 12 1793 10529 27 _ _ (1852393 / 100000) (463099 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110911744 :
    ThetaLowerSegment 110911744 110944512 (2772574395673 / 25000) (1109356896171 / 10000) := by
  exact
    packedTile16384 110911744 110944512 12 1766 10531 27 _ _ (1852423 / 100000) (926213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110944512 :
    ThetaLowerSegment 110944512 110977280 (1109356896171 / 10000) (693554840173 / 6250) := by
  exact
    packedTile16384 110944512 110977280 12 1786 10533 27 _ _ (1852453 / 100000) (231557 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell110977280 :
    ThetaLowerSegment 110977280 111010048 (693554840173 / 6250) (5550077241713 / 50000) := by
  exact
    packedTile16384 110977280 111010048 12 1769 10534 27 _ _ (926241 / 50000) (370497 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111010048 :
    ThetaLowerSegment 111010048 111042816 (5550077241713 / 50000) (5551708378529 / 50000) := by
  exact
    packedTile16384 111010048 111042816 12 1761 10536 27 _ _ (57891 / 3125) (370503 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111042816 :
    ThetaLowerSegment 111042816 111075584 (5551708378529 / 50000) (5553346024773 / 50000) := by
  exact
    packedTile16384 111042816 111075584 12 1768 10537 27 _ _ (1852541 / 100000) (57892 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111075584 :
    ThetaLowerSegment 111075584 111108352 (5553346024773 / 50000) (11109921080799 / 100000) := by
  exact
    packedTile16384 111075584 111108352 12 1743 10539 27 _ _ (1852571 / 100000) (926287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111108352 :
    ThetaLowerSegment 111108352 111141120 (11109921080799 / 100000) (11113239087399 / 100000) := by
  exact
    packedTile16384 111108352 111141120 12 1791 10540 27 _ _ (9263 / 500) (1852603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111141120 :
    ThetaLowerSegment 111141120 111173888 (11113239087399 / 100000) (11116525653019 / 100000) := by
  exact
    packedTile16384 111141120 111173888 12 1774 10542 27 _ _ (185263 / 10000) (1852633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111173888 :
    ThetaLowerSegment 111173888 111206656 (11116525653019 / 100000) (11119771511587 / 100000) := by
  exact
    packedTile16384 111173888 111206656 12 1752 10543 27 _ _ (1852659 / 100000) (926331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111206656 :
    ThetaLowerSegment 111206656 111239424 (11119771511587 / 100000) (11123084119519 / 100000) := by
  exact
    packedTile16384 111206656 111239424 12 1788 10545 27 _ _ (1852689 / 100000) (463173 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111239424 :
    ThetaLowerSegment 111239424 111272192 (11123084119519 / 100000) (11126231887401 / 100000) := by
  exact
    packedTile16384 111239424 111272192 12 1699 10547 27 _ _ (926359 / 50000) (1852721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111272192 :
    ThetaLowerSegment 111272192 111304960 (11126231887401 / 100000) (5564726907217 / 50000) := by
  exact
    packedTile16384 111272192 111304960 12 1739 10548 27 _ _ (1852747 / 100000) (7411 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111304960 :
    ThetaLowerSegment 111304960 111337728 (5564726907217 / 50000) (44531214541 / 400) := by
  exact
    packedTile16384 111304960 111337728 12 1808 10550 27 _ _ (1852777 / 100000) (92639 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111337728 :
    ThetaLowerSegment 111337728 111370496 (44531214541 / 400) (2784037913923 / 25000) := by
  exact
    packedTile16384 111337728 111370496 12 1807 10551 27 _ _ (926403 / 50000) (1852809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111370496 :
    ThetaLowerSegment 111370496 111403264 (2784037913923 / 25000) (2784857793853 / 25000) := by
  exact
    packedTile16384 111370496 111403264 12 1770 10553 27 _ _ (463209 / 25000) (1852839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111403264 :
    ThetaLowerSegment 111403264 111436032 (2784857793853 / 25000) (11142623661807 / 100000) := by
  exact
    packedTile16384 111403264 111436032 12 1723 10554 27 _ _ (370573 / 20000) (463217 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111436032 :
    ThetaLowerSegment 111436032 111468800 (11142623661807 / 100000) (11145818052787 / 100000) := by
  exact
    packedTile16384 111436032 111468800 12 1724 10556 27 _ _ (370579 / 20000) (926449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111468800 :
    ThetaLowerSegment 111468800 111501568 (11145818052787 / 100000) (445965169119 / 4000) := by
  exact
    packedTile16384 111468800 111501568 12 1787 10557 27 _ _ (463231 / 25000) (1852927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111501568 :
    ThetaLowerSegment 111501568 111534336 (445965169119 / 4000) (5576205403869 / 50000) := by
  exact
    packedTile16384 111501568 111534336 12 1771 10559 27 _ _ (1852953 / 100000) (463239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111534336 :
    ThetaLowerSegment 111534336 111567104 (5576205403869 / 50000) (5577798969249 / 50000) := by
  exact
    packedTile16384 111534336 111567104 12 1720 10560 27 _ _ (1852983 / 100000) (926493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111567104 :
    ThetaLowerSegment 111567104 111599872 (5577798969249 / 50000) (5579417575231 / 50000) := by
  exact
    packedTile16384 111567104 111599872 12 1747 10562 27 _ _ (463253 / 25000) (370603 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111599872 :
    ThetaLowerSegment 111599872 111632640 (5579417575231 / 50000) (5581074194779 / 50000) := by
  exact
    packedTile16384 111599872 111632640 12 1788 10564 27 _ _ (926521 / 50000) (370609 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111632640 :
    ThetaLowerSegment 111632640 111665408 (5581074194779 / 50000) (11165378292311 / 100000) := by
  exact
    packedTile16384 111632640 111665408 12 1743 10565 27 _ _ (1853071 / 100000) (926537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111665408 :
    ThetaLowerSegment 111665408 111698176 (11165378292311 / 100000) (11168671251011 / 100000) := by
  exact
    packedTile16384 111665408 111698176 12 1777 10567 27 _ _ (18531 / 1000) (1853103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111698176 :
    ThetaLowerSegment 111698176 111730944 (11168671251011 / 100000) (11171995766231 / 100000) := by
  exact
    packedTile16384 111698176 111730944 12 1794 10568 27 _ _ (185313 / 10000) (1853133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111730944 :
    ThetaLowerSegment 111730944 111763712 (11171995766231 / 100000) (5587637002251 / 50000) := by
  exact
    packedTile16384 111730944 111763712 12 1769 10570 27 _ _ (1853159 / 100000) (926581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111763712 :
    ThetaLowerSegment 111763712 111796480 (5587637002251 / 50000) (5589284486383 / 50000) := by
  exact
    packedTile16384 111763712 111796480 12 1778 10571 27 _ _ (463297 / 25000) (1853191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111796480 :
    ThetaLowerSegment 111796480 111829248 (5589284486383 / 50000) (2795479434423 / 25000) := by
  exact
    packedTile16384 111796480 111829248 12 1807 10573 27 _ _ (926609 / 50000) (1853221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111829248 :
    ThetaLowerSegment 111829248 111862016 (2795479434423 / 25000) (5592580459971 / 50000) := by
  exact
    packedTile16384 111829248 111862016 12 1750 10574 27 _ _ (1853247 / 100000) (7413 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111862016 :
    ThetaLowerSegment 111862016 111894784 (5592580459971 / 50000) (5594254894837 / 50000) := by
  exact
    packedTile16384 111862016 111894784 12 1807 10576 27 _ _ (463319 / 25000) (1853279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111894784 :
    ThetaLowerSegment 111894784 111927552 (5594254894837 / 50000) (11191628901989 / 100000) := by
  exact
    packedTile16384 111894784 111927552 12 1683 10578 27 _ _ (370661 / 20000) (463327 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111927552 :
    ThetaLowerSegment 111927552 111960320 (11191628901989 / 100000) (1399369918123 / 12500) := by
  exact
    packedTile16384 111927552 111960320 12 1797 10579 27 _ _ (370667 / 20000) (926669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111960320 :
    ThetaLowerSegment 111960320 111993088 (1399369918123 / 12500) (1399779511567 / 12500) := by
  exact
    packedTile16384 111960320 111993088 12 1768 10581 27 _ _ (463341 / 25000) (1853367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell111993088 :
    ThetaLowerSegment 111993088 112025856 (1399779511567 / 12500) (11201529571897 / 100000) := by
  exact
    packedTile16384 111993088 112025856 12 1777 10582 27 _ _ (1853393 / 100000) (463349 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112025856 :
    ThetaLowerSegment 112025856 112058624 (11201529571897 / 100000) (2801196509027 / 25000) := by
  exact
    packedTile16384 112025856 112058624 12 1757 10584 27 _ _ (1853423 / 100000) (926713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112058624 :
    ThetaLowerSegment 112058624 112091392 (2801196509027 / 25000) (350254689109 / 3125) := by
  exact
    packedTile16384 112058624 112091392 12 1815 10585 27 _ _ (463363 / 25000) (370691 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112091392 :
    ThetaLowerSegment 112091392 112124160 (350254689109 / 3125) (11211473342921 / 100000) := by
  exact
    packedTile16384 112091392 112124160 12 1793 10587 27 _ _ (1853481 / 100000) (463371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112124160 :
    ThetaLowerSegment 112124160 112156928 (11211473342921 / 100000) (11214728106481 / 100000) := by
  exact
    packedTile16384 112124160 112156928 12 1756 10588 27 _ _ (185351 / 10000) (1853513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112156928 :
    ThetaLowerSegment 112156928 112189696 (11214728106481 / 100000) (350564341127 / 3125) := by
  exact
    packedTile16384 112156928 112189696 12 1797 10590 27 _ _ (1853539 / 100000) (926771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112189696 :
    ThetaLowerSegment 112189696 112222464 (350564341127 / 3125) (1402674417533 / 12500) := by
  exact
    packedTile16384 112189696 112222464 12 1800 10591 27 _ _ (1853569 / 100000) (463393 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112222464 :
    ThetaLowerSegment 112222464 112255232 (1402674417533 / 12500) (1122461503999 / 10000) := by
  exact
    packedTile16384 112222464 112255232 12 1737 10593 27 _ _ (926799 / 50000) (1853601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112255232 :
    ThetaLowerSegment 112255232 112288000 (1122461503999 / 10000) (11227819961073 / 100000) := by
  exact
    packedTile16384 112255232 112288000 12 1729 10595 27 _ _ (1853627 / 100000) (185363 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112288000 :
    ThetaLowerSegment 112288000 112320768 (11227819961073 / 100000) (11231176932089 / 100000) := by
  exact
    packedTile16384 112288000 112320768 12 1811 10596 27 _ _ (231707 / 12500) (1853659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112320768 :
    ThetaLowerSegment 112320768 112353536 (11231176932089 / 100000) (2808620513111 / 25000) := by
  exact
    packedTile16384 112320768 112353536 12 1783 10598 27 _ _ (370737 / 20000) (231711 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112353536 :
    ThetaLowerSegment 112353536 112386304 (2808620513111 / 25000) (2809436147711 / 25000) := by
  exact
    packedTile16384 112353536 112386304 12 1760 10599 27 _ _ (370743 / 20000) (926859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112386304 :
    ThetaLowerSegment 112386304 112419072 (2809436147711 / 25000) (562048412583 / 5000) := by
  exact
    packedTile16384 112386304 112419072 12 1739 10601 27 _ _ (115859 / 6250) (1853747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112419072 :
    ThetaLowerSegment 112419072 112451840 (562048412583 / 5000) (11244232745913 / 100000) := by
  exact
    packedTile16384 112419072 112451840 12 1761 10602 27 _ _ (1853773 / 100000) (115861 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112451840 :
    ThetaLowerSegment 112451840 112484608 (11244232745913 / 100000) (11247465776601 / 100000) := by
  exact
    packedTile16384 112451840 112484608 12 1744 10604 27 _ _ (926901 / 50000) (370761 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112484608 :
    ThetaLowerSegment 112484608 112517376 (11247465776601 / 100000) (1125072666533 / 10000) := by
  exact
    packedTile16384 112484608 112517376 12 1759 10605 27 _ _ (1853831 / 100000) (926917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112517376 :
    ThetaLowerSegment 112517376 112550144 (1125072666533 / 10000) (1125398204349 / 10000) := by
  exact
    packedTile16384 112517376 112550144 12 1756 10607 27 _ _ (92693 / 5000) (1853863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112550144 :
    ThetaLowerSegment 112550144 112582912 (1125398204349 / 10000) (5628633567399 / 50000) := by
  exact
    packedTile16384 112550144 112582912 12 1772 10608 27 _ _ (1853889 / 100000) (463473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112582912 :
    ThetaLowerSegment 112582912 112615680 (5628633567399 / 50000) (5630246476929 / 50000) := by
  exact
    packedTile16384 112582912 112615680 12 1740 10610 27 _ _ (1853919 / 100000) (926961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112615680 :
    ThetaLowerSegment 112615680 112648448 (5630246476929 / 50000) (5631910395259 / 50000) := by
  exact
    packedTile16384 112615680 112648448 12 1795 10612 27 _ _ (463487 / 25000) (1853951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112648448 :
    ThetaLowerSegment 112648448 112681216 (5631910395259 / 50000) (11267107891739 / 100000) := by
  exact
    packedTile16384 112648448 112681216 12 1773 10613 27 _ _ (1853977 / 100000) (92699 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112681216 :
    ThetaLowerSegment 112681216 112713984 (11267107891739 / 100000) (11270383920341 / 100000) := by
  exact
    packedTile16384 112681216 112713984 12 1767 10615 27 _ _ (927003 / 50000) (1854009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112713984 :
    ThetaLowerSegment 112713984 112746752 (11270383920341 / 100000) (11273672978431 / 100000) := by
  exact
    packedTile16384 112713984 112746752 12 1774 10616 27 _ _ (370807 / 20000) (927019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112746752 :
    ThetaLowerSegment 112746752 112779520 (11273672978431 / 100000) (11277034396463 / 100000) := by
  exact
    packedTile16384 112746752 112779520 12 1813 10618 27 _ _ (115879 / 6250) (1854067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112779520 :
    ThetaLowerSegment 112779520 112812288 (11277034396463 / 100000) (11280253101911 / 100000) := by
  exact
    packedTile16384 112779520 112812288 12 1736 10619 27 _ _ (1854093 / 100000) (115881 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112812288 :
    ThetaLowerSegment 112812288 112845056 (11280253101911 / 100000) (11283601646243 / 100000) := by
  exact
    packedTile16384 112812288 112845056 12 1806 10621 27 _ _ (927061 / 50000) (14833 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112845056 :
    ThetaLowerSegment 112845056 112877824 (11283601646243 / 100000) (11286827868983 / 100000) := by
  exact
    packedTile16384 112845056 112877824 12 1740 10622 27 _ _ (1854151 / 100000) (927077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112877824 :
    ThetaLowerSegment 112877824 112910592 (11286827868983 / 100000) (11290141288643 / 100000) := by
  exact
    packedTile16384 112877824 112910592 12 1787 10624 27 _ _ (92709 / 5000) (1854183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112910592 :
    ThetaLowerSegment 112910592 112943360 (11290141288643 / 100000) (11293367612303 / 100000) := by
  exact
    packedTile16384 112910592 112943360 12 1740 10625 27 _ _ (1854209 / 100000) (463553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112943360 :
    ThetaLowerSegment 112943360 112976128 (11293367612303 / 100000) (11296597694899 / 100000) := by
  exact
    packedTile16384 112943360 112976128 12 1742 10627 27 _ _ (927119 / 50000) (1854241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell112976128 :
    ThetaLowerSegment 112976128 113008896 (11296597694899 / 100000) (11299916832829 / 100000) := by
  exact
    packedTile16384 112976128 113008896 12 1790 10629 27 _ _ (1854267 / 100000) (185427 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113008896 :
    ThetaLowerSegment 113008896 113041664 (11299916832829 / 100000) (11303161850829 / 100000) := by
  exact
    packedTile16384 113008896 113041664 12 1750 10630 27 _ _ (231787 / 12500) (1854299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113041664 :
    ThetaLowerSegment 113041664 113074432 (11303161850829 / 100000) (11306499635829 / 100000) := by
  exact
    packedTile16384 113041664 113074432 12 1800 10632 27 _ _ (74173 / 4000) (231791 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113074432 :
    ThetaLowerSegment 113074432 113107200 (11306499635829 / 100000) (11309848599153 / 100000) := by
  exact
    packedTile16384 113074432 113107200 12 1806 10633 27 _ _ (927177 / 50000) (1854357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113107200 :
    ThetaLowerSegment 113107200 113139968 (11309848599153 / 100000) (11313153109659 / 100000) := by
  exact
    packedTile16384 113107200 113139968 12 1782 10635 27 _ _ (1854383 / 100000) (927193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113139968 :
    ThetaLowerSegment 113139968 113172736 (11313153109659 / 100000) (11316481779199 / 100000) := by
  exact
    packedTile16384 113139968 113172736 12 1795 10636 27 _ _ (463603 / 25000) (370883 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113172736 :
    ThetaLowerSegment 113172736 113205504 (11316481779199 / 100000) (11319723342067 / 100000) := by
  exact
    packedTile16384 113172736 113205504 12 1748 10638 27 _ _ (1854441 / 100000) (463611 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113205504 :
    ThetaLowerSegment 113205504 113238272 (11319723342067 / 100000) (11322948265397 / 100000) := by
  exact
    packedTile16384 113205504 113238272 12 1739 10639 27 _ _ (185447 / 10000) (1854473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113238272 :
    ThetaLowerSegment 113238272 113271040 (11322948265397 / 100000) (1415776754767 / 12500) := by
  exact
    packedTile16384 113238272 113271040 12 1761 10641 27 _ _ (1854499 / 100000) (927251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113271040 :
    ThetaLowerSegment 113271040 113303808 (1415776754767 / 12500) (1416183591847 / 12500) := by
  exact
    packedTile16384 113271040 113303808 12 1755 10642 27 _ _ (57954 / 3125) (1854531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113303808 :
    ThetaLowerSegment 113303808 113336576 (1416183591847 / 12500) (11332771700793 / 100000) := by
  exact
    packedTile16384 113303808 113336576 12 1781 10644 27 _ _ (1854557 / 100000) (11591 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113336576 :
    ThetaLowerSegment 113336576 113369344 (11332771700793 / 100000) (11336089555147 / 100000) := by
  exact
    packedTile16384 113336576 113369344 12 1789 10645 27 _ _ (927293 / 50000) (1854589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113369344 :
    ThetaLowerSegment 113369344 113402112 (11336089555147 / 100000) (2834826828043 / 25000) := by
  exact
    packedTile16384 113369344 113402112 12 1735 10647 27 _ _ (370923 / 20000) (927309 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113402112 :
    ThetaLowerSegment 113402112 113434880 (2834826828043 / 25000) (1417817494583 / 12500) := by
  exact
    packedTile16384 113402112 113434880 12 1743 10649 27 _ _ (463661 / 25000) (1854647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113434880 :
    ThetaLowerSegment 113434880 113467648 (1417817494583 / 12500) (1418227145261 / 12500) := by
  exact
    packedTile16384 113434880 113467648 12 1767 10650 27 _ _ (115917 / 6250) (74187 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113467648 :
    ThetaLowerSegment 113467648 113500416 (1418227145261 / 12500) (11349138931579 / 100000) := by
  exact
    packedTile16384 113467648 113500416 12 1791 10652 27 _ _ (1854701 / 100000) (115919 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113500416 :
    ThetaLowerSegment 113500416 113533184 (11349138931579 / 100000) (11352399546919 / 100000) := by
  exact
    packedTile16384 113500416 113533184 12 1758 10653 27 _ _ (185473 / 10000) (1854733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113533184 :
    ThetaLowerSegment 113533184 113565952 (11352399546919 / 100000) (2271134268359 / 20000) := by
  exact
    packedTile16384 113533184 113565952 12 1764 10655 27 _ _ (1854759 / 100000) (927381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113565952 :
    ThetaLowerSegment 113565952 113598720 (2271134268359 / 20000) (11358856012791 / 100000) := by
  exact
    packedTile16384 113565952 113598720 12 1717 10656 27 _ _ (463697 / 25000) (1854791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113598720 :
    ThetaLowerSegment 113598720 113631488 (11358856012791 / 100000) (454484226087 / 4000) := by
  exact
    packedTile16384 113598720 113631488 12 1752 10658 27 _ _ (1854817 / 100000) (92741 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113631488 :
    ThetaLowerSegment 113631488 113664256 (454484226087 / 4000) (11365383165057 / 100000) := by
  exact
    packedTile16384 113631488 113664256 12 1767 10659 27 _ _ (927423 / 50000) (1854849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113664256 :
    ThetaLowerSegment 113664256 113697024 (11365383165057 / 100000) (2273730290609 / 20000) := by
  exact
    packedTile16384 113664256 113697024 12 1762 10661 27 _ _ (927437 / 50000) (1854877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113697024 :
    ThetaLowerSegment 113697024 113729792 (2273730290609 / 20000) (5685960823517 / 50000) := by
  exact
    packedTile16384 113697024 113729792 12 1763 10662 27 _ _ (1854903 / 100000) (927453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113729792 :
    ThetaLowerSegment 113729792 113762560 (5685960823517 / 50000) (1137516406817 / 10000) := by
  exact
    packedTile16384 113729792 113762560 12 1748 10664 27 _ _ (463733 / 25000) (370987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113762560 :
    ThetaLowerSegment 113762560 113795328 (1137516406817 / 10000) (5689192140233 / 50000) := by
  exact
    packedTile16384 113762560 113795328 12 1736 10665 27 _ _ (1854961 / 100000) (463741 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113795328 :
    ThetaLowerSegment 113795328 113828096 (5689192140233 / 50000) (5690856066263 / 50000) := by
  exact
    packedTile16384 113795328 113828096 12 1794 10667 27 _ _ (185499 / 10000) (1854993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113828096 :
    ThetaLowerSegment 113828096 113860864 (5690856066263 / 50000) (5692490337121 / 50000) := by
  exact
    packedTile16384 113828096 113860864 12 1762 10669 27 _ _ (927509 / 50000) (1855021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113860864 :
    ThetaLowerSegment 113860864 113893632 (5692490337121 / 50000) (2847045621341 / 25000) := by
  exact
    packedTile16384 113860864 113893632 12 1726 10670 27 _ _ (1855047 / 100000) (37101 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113893632 :
    ThetaLowerSegment 113893632 113926400 (2847045621341 / 25000) (2847857217091 / 25000) := by
  exact
    packedTile16384 113893632 113926400 12 1750 10672 27 _ _ (463769 / 25000) (1855079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113926400 :
    ThetaLowerSegment 113926400 113959168 (2847857217091 / 25000) (1424343224513 / 12500) := by
  exact
    packedTile16384 113926400 113959168 12 1788 10673 27 _ _ (371021 / 20000) (463777 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113959168 :
    ThetaLowerSegment 113959168 113991936 (1424343224513 / 12500) (5699006343539 / 50000) := by
  exact
    packedTile16384 113959168 113991936 12 1761 10675 27 _ _ (927567 / 50000) (1855137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell113991936 :
    ThetaLowerSegment 113991936 114024704 (5699006343539 / 50000) (356289060774 / 3125) := by
  exact
    packedTile16384 113991936 114024704 12 1745 10676 27 _ _ (927581 / 50000) (371033 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114024704 :
    ThetaLowerSegment 114024704 114057472 (356289060774 / 3125) (57022501197 / 500) := by
  exact
    packedTile16384 114024704 114057472 12 1752 10678 27 _ _ (1855191 / 100000) (927597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114057472 :
    ThetaLowerSegment 114057472 114090240 (57022501197 / 500) (14259683593 / 125) := by
  exact
    packedTile16384 114057472 114090240 12 1750 10679 27 _ _ (92761 / 5000) (1855223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114090240 :
    ThetaLowerSegment 114090240 114123008 (14259683593 / 125) (11411043651873 / 100000) := by
  exact
    packedTile16384 114090240 114123008 12 1777 10681 27 _ _ (1855249 / 100000) (463813 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114123008 :
    ThetaLowerSegment 114123008 114155776 (11411043651873 / 100000) (11414346044933 / 100000) := by
  exact
    packedTile16384 114123008 114155776 12 1780 10682 27 _ _ (1855277 / 100000) (23191 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114155776 :
    ThetaLowerSegment 114155776 114188544 (11414346044933 / 100000) (11417668897979 / 100000) := by
  exact
    packedTile16384 114155776 114188544 12 1791 10684 27 _ _ (927653 / 50000) (1855309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114188544 :
    ThetaLowerSegment 114188544 114221312 (11417668897979 / 100000) (1427619337033 / 12500) := by
  exact
    packedTile16384 114188544 114221312 12 1771 10685 27 _ _ (371067 / 20000) (927669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114221312 :
    ThetaLowerSegment 114221312 114254080 (1427619337033 / 12500) (571208409249 / 5000) := by
  exact
    packedTile16384 114221312 114254080 12 1732 10687 27 _ _ (1855363 / 100000) (927683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114254080 :
    ThetaLowerSegment 114254080 114286848 (571208409249 / 5000) (2856878828037 / 25000) := by
  exact
    packedTile16384 114254080 114286848 12 1804 10688 27 _ _ (57981 / 3125) (371079 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114286848 :
    ThetaLowerSegment 114286848 114319616 (2856878828037 / 25000) (357213525153 / 3125) := by
  exact
    packedTile16384 114286848 114319616 12 1788 10690 27 _ _ (1855421 / 100000) (57982 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114319616 :
    ThetaLowerSegment 114319616 114352384 (357213525153 / 3125) (2858537586927 / 25000) := by
  exact
    packedTile16384 114319616 114352384 12 1788 10692 27 _ _ (1855449 / 100000) (463863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114352384 :
    ThetaLowerSegment 114352384 114385152 (2858537586927 / 25000) (2859352141769 / 25000) := by
  exact
    packedTile16384 114352384 114385152 12 1756 10693 27 _ _ (927739 / 50000) (1855481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114385152 :
    ThetaLowerSegment 114385152 114417920 (2859352141769 / 25000) (11440679825917 / 100000) := by
  exact
    packedTile16384 114385152 114417920 12 1763 10695 27 _ _ (1855507 / 100000) (185551 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114417920 :
    ThetaLowerSegment 114417920 114450688 (11440679825917 / 100000) (11443867635047 / 100000) := by
  exact
    packedTile16384 114417920 114450688 12 1718 10696 27 _ _ (371107 / 20000) (927769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114450688 :
    ThetaLowerSegment 114450688 114483456 (11443867635047 / 100000) (11447070338511 / 100000) := by
  exact
    packedTile16384 114450688 114483456 12 1726 10698 27 _ _ (463891 / 25000) (1855567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114483456 :
    ThetaLowerSegment 114483456 114516224 (11447070338511 / 100000) (1431288543537 / 12500) := by
  exact
    packedTile16384 114483456 114516224 12 1745 10699 27 _ _ (1855593 / 100000) (463899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114516224 :
    ThetaLowerSegment 114516224 114548992 (1431288543537 / 12500) (458142153177 / 4000) := by
  exact
    packedTile16384 114516224 114548992 12 1749 10701 27 _ _ (1855621 / 100000) (231953 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114548992 :
    ThetaLowerSegment 114548992 114581760 (458142153177 / 4000) (458270712609 / 4000) := by
  exact
    packedTile16384 114548992 114581760 12 1732 10702 27 _ _ (37113 / 2000) (1855653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114581760 :
    ThetaLowerSegment 114581760 114614528 (458270712609 / 4000) (11460056076641 / 100000) := by
  exact
    packedTile16384 114581760 114614528 12 1772 10704 27 _ _ (927839 / 50000) (1855681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114614528 :
    ThetaLowerSegment 114614528 114647296 (11460056076641 / 100000) (11463503980247 / 100000) := by
  exact
    packedTile16384 114614528 114647296 12 1858 10705 27 _ _ (1855707 / 100000) (185571 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114647296 :
    ThetaLowerSegment 114647296 114680064 (11463503980247 / 100000) (11466751518247 / 100000) := by
  exact
    packedTile16384 114647296 114680064 12 1750 10707 27 _ _ (231967 / 12500) (1855739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114680064 :
    ThetaLowerSegment 114680064 114712832 (11466751518247 / 100000) (11469967557259 / 100000) := by
  exact
    packedTile16384 114680064 114712832 12 1733 10708 27 _ _ (463941 / 25000) (1855767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114712832 :
    ThetaLowerSegment 114712832 114745600 (11469967557259 / 100000) (11473196637079 / 100000) := by
  exact
    packedTile16384 114712832 114745600 12 1740 10710 27 _ _ (1855793 / 100000) (463949 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114745600 :
    ThetaLowerSegment 114745600 114778368 (11473196637079 / 100000) (11476507421743 / 100000) := by
  exact
    packedTile16384 114745600 114778368 12 1784 10711 27 _ _ (1855821 / 100000) (115989 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114778368 :
    ThetaLowerSegment 114778368 114811136 (11476507421743 / 100000) (11479766294343 / 100000) := by
  exact
    packedTile16384 114778368 114811136 12 1756 10713 27 _ _ (37117 / 2000) (1855853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114811136 :
    ThetaLowerSegment 114811136 114843904 (11479766294343 / 100000) (11483054910159 / 100000) := by
  exact
    packedTile16384 114811136 114843904 12 1772 10714 27 _ _ (927939 / 50000) (1855881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114843904 :
    ThetaLowerSegment 114843904 114876672 (11483054910159 / 100000) (11486351000991 / 100000) := by
  exact
    packedTile16384 114843904 114876672 12 1776 10716 27 _ _ (1855907 / 100000) (185591 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114876672 :
    ThetaLowerSegment 114876672 114909440 (11486351000991 / 100000) (11489584039761 / 100000) := by
  exact
    packedTile16384 114876672 114909440 12 1742 10718 27 _ _ (371187 / 20000) (927969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114909440 :
    ThetaLowerSegment 114909440 114942208 (11489584039761 / 100000) (11492872807969 / 100000) := by
  exact
    packedTile16384 114909440 114942208 12 1772 10719 27 _ _ (463991 / 25000) (1855967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114942208 :
    ThetaLowerSegment 114942208 114974976 (11492872807969 / 100000) (5748059469863 / 50000) := by
  exact
    packedTile16384 114942208 114974976 12 1749 10721 27 _ _ (1855993 / 100000) (463999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell114974976 :
    ThetaLowerSegment 114974976 115007744 (5748059469863 / 50000) (11499428225169 / 100000) := by
  exact
    packedTile16384 114974976 115007744 12 1783 10722 27 _ _ (1856021 / 100000) (232003 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115007744 :
    ThetaLowerSegment 115007744 115040512 (11499428225169 / 100000) (11502713433669 / 100000) := by
  exact
    packedTile16384 115007744 115040512 12 1770 10724 27 _ _ (37121 / 2000) (1856053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115040512 :
    ThetaLowerSegment 115040512 115073280 (11502713433669 / 100000) (11506093351707 / 100000) := by
  exact
    packedTile16384 115040512 115073280 12 1821 10725 27 _ _ (928039 / 50000) (1856081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115073280 :
    ThetaLowerSegment 115073280 115106048 (11506093351707 / 100000) (11509280285709 / 100000) := by
  exact
    packedTile16384 115073280 115106048 12 1717 10727 27 _ _ (928053 / 50000) (1856109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115106048 :
    ThetaLowerSegment 115106048 115138816 (11509280285709 / 100000) (11512543371039 / 100000) := by
  exact
    packedTile16384 115106048 115138816 12 1758 10728 27 _ _ (371227 / 20000) (928069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115138816 :
    ThetaLowerSegment 115138816 115171584 (11512543371039 / 100000) (11515791656289 / 100000) := by
  exact
    packedTile16384 115138816 115171584 12 1750 10730 27 _ _ (1856163 / 100000) (928083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115171584 :
    ThetaLowerSegment 115171584 115204352 (11515791656289 / 100000) (11519103102817 / 100000) := by
  exact
    packedTile16384 115171584 115204352 12 1784 10731 27 _ _ (58006 / 3125) (371239 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115204352 :
    ThetaLowerSegment 115204352 115237120 (11519103102817 / 100000) (11522420167957 / 100000) := by
  exact
    packedTile16384 115204352 115237120 12 1787 10733 27 _ _ (92811 / 5000) (1856223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115237120 :
    ThetaLowerSegment 115237120 115269888 (11522420167957 / 100000) (2881402764997 / 25000) := by
  exact
    packedTile16384 115237120 115269888 12 1719 10734 27 _ _ (1856249 / 100000) (464063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115269888 :
    ThetaLowerSegment 115269888 115302656 (2881402764997 / 25000) (2305790842973 / 20000) := by
  exact
    packedTile16384 115269888 115302656 12 1801 10736 27 _ _ (1856277 / 100000) (46407 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115302656 :
    ThetaLowerSegment 115302656 115335424 (2305790842973 / 20000) (11532182330999 / 100000) := by
  exact
    packedTile16384 115302656 115335424 12 1739 10737 27 _ _ (928153 / 50000) (1856309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115335424 :
    ThetaLowerSegment 115335424 115368192 (11532182330999 / 100000) (11535455047841 / 100000) := by
  exact
    packedTile16384 115335424 115368192 12 1763 10739 27 _ _ (928167 / 50000) (1856337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115368192 :
    ThetaLowerSegment 115368192 115400960 (11535455047841 / 100000) (11538696255893 / 100000) := by
  exact
    packedTile16384 115368192 115400960 12 1746 10740 27 _ _ (928181 / 50000) (371273 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115400960 :
    ThetaLowerSegment 115400960 115433728 (11538696255893 / 100000) (11541881822849 / 100000) := by
  exact
    packedTile16384 115400960 115433728 12 1716 10742 27 _ _ (1856391 / 100000) (928197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115433728 :
    ThetaLowerSegment 115433728 115466496 (11541881822849 / 100000) (5772599621801 / 50000) := by
  exact
    packedTile16384 115433728 115466496 12 1787 10744 27 _ _ (1856419 / 100000) (928211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115466496 :
    ThetaLowerSegment 115466496 115499264 (5772599621801 / 50000) (5774262999209 / 50000) := by
  exact
    packedTile16384 115466496 115499264 12 1792 10745 27 _ _ (58014 / 3125) (1856451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115499264 :
    ThetaLowerSegment 115499264 115532032 (5774262999209 / 50000) (5775901339279 / 50000) := by
  exact
    packedTile16384 115499264 115532032 12 1765 10747 27 _ _ (464119 / 25000) (1856479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115532032 :
    ThetaLowerSegment 115532032 115564800 (5775901339279 / 50000) (5777502573979 / 50000) := by
  exact
    packedTile16384 115532032 115564800 12 1725 10748 27 _ _ (232063 / 12500) (1856507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115564800 :
    ThetaLowerSegment 115564800 115597568 (5777502573979 / 50000) (2889589511639 / 25000) := by
  exact
    packedTile16384 115564800 115597568 12 1806 10750 27 _ _ (1856533 / 100000) (232067 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115597568 :
    ThetaLowerSegment 115597568 115630336 (2889589511639 / 25000) (5780829506007 / 50000) := by
  exact
    packedTile16384 115597568 115630336 12 1778 10751 27 _ _ (1856561 / 100000) (464141 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115630336 :
    ThetaLowerSegment 115630336 115663104 (5780829506007 / 50000) (722809073409 / 6250) := by
  exact
    packedTile16384 115630336 115663104 12 1770 10753 27 _ _ (1856589 / 100000) (116037 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115663104 :
    ThetaLowerSegment 115663104 115695872 (722809073409 / 6250) (2892042994157 / 25000) := by
  exact
    packedTile16384 115663104 115695872 12 1738 10754 27 _ _ (928309 / 50000) (1856621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115695872 :
    ThetaLowerSegment 115695872 115728640 (2892042994157 / 25000) (5785733761639 / 50000) := by
  exact
    packedTile16384 115695872 115728640 12 1775 10756 27 _ _ (928323 / 50000) (1856649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115728640 :
    ThetaLowerSegment 115728640 115761408 (5785733761639 / 50000) (2893692636581 / 25000) := by
  exact
    packedTile16384 115728640 115761408 12 1779 10757 27 _ _ (928337 / 50000) (1856677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115761408 :
    ThetaLowerSegment 115761408 115794176 (2893692636581 / 25000) (2894502159089 / 25000) := by
  exact
    packedTile16384 115761408 115794176 12 1744 10759 27 _ _ (1856703 / 100000) (928353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115794176 :
    ThetaLowerSegment 115794176 115826944 (2894502159089 / 25000) (11581252345413 / 100000) := by
  exact
    packedTile16384 115794176 115826944 12 1747 10760 27 _ _ (1856731 / 100000) (928367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115826944 :
    ThetaLowerSegment 115826944 115859712 (11581252345413 / 100000) (5792266619283 / 50000) := by
  exact
    packedTile16384 115826944 115859712 12 1767 10762 27 _ _ (1856759 / 100000) (928381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115859712 :
    ThetaLowerSegment 115859712 115892480 (5792266619283 / 50000) (5793886666813 / 50000) := by
  exact
    packedTile16384 115859712 115892480 12 1745 10763 27 _ _ (464197 / 25000) (1856791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115892480 :
    ThetaLowerSegment 115892480 115925248 (5793886666813 / 50000) (5795574512557 / 50000) := by
  exact
    packedTile16384 115892480 115925248 12 1818 10765 27 _ _ (116051 / 6250) (1856819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115925248 :
    ThetaLowerSegment 115925248 115958016 (5795574512557 / 50000) (5797243815313 / 50000) := by
  exact
    packedTile16384 115925248 115958016 12 1798 10766 27 _ _ (464211 / 25000) (1856847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115958016 :
    ThetaLowerSegment 115958016 115990784 (5797243815313 / 50000) (5798901073573 / 50000) := by
  exact
    packedTile16384 115958016 115990784 12 1785 10768 27 _ _ (232109 / 12500) (2971 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell115990784 :
    ThetaLowerSegment 115990784 116023552 (5798901073573 / 50000) (2900275929281 / 25000) := by
  exact
    packedTile16384 115990784 116023552 12 1778 10769 27 _ _ (1856901 / 100000) (232113 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116023552 :
    ThetaLowerSegment 116023552 116056320 (2900275929281 / 25000) (725274637207 / 6250) := by
  exact
    packedTile16384 116023552 116056320 12 1772 10771 27 _ _ (1856929 / 100000) (464233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116056320 :
    ThetaLowerSegment 116056320 116089088 (725274637207 / 6250) (5803859074171 / 50000) := by
  exact
    packedTile16384 116056320 116089088 12 1790 10772 27 _ _ (1856957 / 100000) (11606 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116089088 :
    ThetaLowerSegment 116089088 116121856 (5803859074171 / 50000) (11610984584957 / 100000) := by
  exact
    packedTile16384 116089088 116121856 12 1759 10774 27 _ _ (371397 / 20000) (464247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116121856 :
    ThetaLowerSegment 116121856 116154624 (11610984584957 / 100000) (11614319782101 / 100000) := by
  exact
    packedTile16384 116121856 116154624 12 1796 10775 27 _ _ (928507 / 50000) (1857017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116154624 :
    ThetaLowerSegment 116154624 116187392 (11614319782101 / 100000) (11617588176021 / 100000) := by
  exact
    packedTile16384 116154624 116187392 12 1760 10777 27 _ _ (928521 / 50000) (371409 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116187392 :
    ThetaLowerSegment 116187392 116220160 (11617588176021 / 100000) (11620851048011 / 100000) := by
  exact
    packedTile16384 116187392 116220160 12 1757 10779 27 _ _ (185707 / 10000) (1857073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116220160 :
    ThetaLowerSegment 116220160 116252928 (11620851048011 / 100000) (11624056399159 / 100000) := by
  exact
    packedTile16384 116220160 116252928 12 1726 10780 27 _ _ (928549 / 50000) (1857101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116252928 :
    ThetaLowerSegment 116252928 116285696 (11624056399159 / 100000) (11627371369069 / 100000) := by
  exact
    packedTile16384 116252928 116285696 12 1785 10782 27 _ _ (928563 / 50000) (1857129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116285696 :
    ThetaLowerSegment 116285696 116318464 (11627371369069 / 100000) (5815285623567 / 50000) := by
  exact
    packedTile16384 116285696 116318464 12 1723 10783 27 _ _ (371431 / 20000) (928579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116318464 :
    ThetaLowerSegment 116318464 116351232 (5815285623567 / 50000) (5816957088267 / 50000) := by
  exact
    packedTile16384 116318464 116351232 12 1800 10785 27 _ _ (1857183 / 100000) (928593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116351232 :
    ThetaLowerSegment 116351232 116384000 (5816957088267 / 50000) (1163721258327 / 10000) := by
  exact
    packedTile16384 116351232 116384000 12 1776 10786 27 _ _ (1857211 / 100000) (928607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116384000 :
    ThetaLowerSegment 116384000 116416768 (1163721258327 / 10000) (11640494324583 / 100000) := by
  exact
    packedTile16384 116384000 116416768 12 1767 10788 27 _ _ (1857239 / 100000) (928621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116416768 :
    ThetaLowerSegment 116416768 116449536 (11640494324583 / 100000) (2910958886979 / 25000) := by
  exact
    packedTile16384 116416768 116449536 12 1799 10789 27 _ _ (1857267 / 100000) (185727 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116449536 :
    ThetaLowerSegment 116449536 116482304 (2910958886979 / 25000) (2911761238419 / 25000) := by
  exact
    packedTile16384 116449536 116482304 12 1728 10791 27 _ _ (371459 / 20000) (928649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116482304 :
    ThetaLowerSegment 116482304 116515072 (2911761238419 / 25000) (5825143919817 / 50000) := by
  exact
    packedTile16384 116482304 116515072 12 1746 10792 27 _ _ (1857323 / 100000) (928663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116515072 :
    ThetaLowerSegment 116515072 116547840 (5825143919817 / 50000) (5826819251321 / 50000) := by
  exact
    packedTile16384 116515072 116547840 12 1804 10794 27 _ _ (232169 / 12500) (371471 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116547840 :
    ThetaLowerSegment 116547840 116580608 (5826819251321 / 50000) (5828424956331 / 50000) := by
  exact
    packedTile16384 116547840 116580608 12 1729 10795 27 _ _ (92869 / 5000) (1857383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116580608 :
    ThetaLowerSegment 116580608 116613376 (5828424956331 / 50000) (5830105910571 / 50000) := by
  exact
    packedTile16384 116580608 116613376 12 1810 10797 27 _ _ (58044 / 3125) (1857411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116613376 :
    ThetaLowerSegment 116613376 116646144 (5830105910571 / 50000) (5831734881943 / 50000) := by
  exact
    packedTile16384 116613376 116646144 12 1754 10798 27 _ _ (464359 / 25000) (1857439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116646144 :
    ThetaLowerSegment 116646144 116678912 (5831734881943 / 50000) (5833392668563 / 50000) := by
  exact
    packedTile16384 116646144 116678912 12 1785 10800 27 _ _ (232183 / 12500) (1857467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116678912 :
    ThetaLowerSegment 116678912 116711680 (5833392668563 / 50000) (5835012401587 / 50000) := by
  exact
    packedTile16384 116678912 116711680 12 1744 10801 27 _ _ (464373 / 25000) (371499 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116711680 :
    ThetaLowerSegment 116711680 116744448 (5835012401587 / 50000) (5836638660347 / 50000) := by
  exact
    packedTile16384 116711680 116744448 12 1751 10803 27 _ _ (23219 / 1250) (1857523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116744448 :
    ThetaLowerSegment 116744448 116777216 (5836638660347 / 50000) (5838263086073 / 50000) := by
  exact
    packedTile16384 116744448 116777216 12 1749 10804 27 _ _ (464387 / 25000) (1857551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116777216 :
    ThetaLowerSegment 116777216 116809984 (5838263086073 / 50000) (5839872675677 / 50000) := by
  exact
    packedTile16384 116777216 116809984 12 1733 10806 27 _ _ (232197 / 12500) (1857579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116809984 :
    ThetaLowerSegment 116809984 116842752 (5839872675677 / 50000) (5841498079177 / 50000) := by
  exact
    packedTile16384 116809984 116842752 12 1750 10807 27 _ _ (464401 / 25000) (1857607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116842752 :
    ThetaLowerSegment 116842752 116875520 (5841498079177 / 50000) (5843111432569 / 50000) := by
  exact
    packedTile16384 116842752 116875520 12 1737 10809 27 _ _ (58051 / 3125) (371527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116875520 :
    ThetaLowerSegment 116875520 116908288 (5843111432569 / 50000) (5844788899549 / 50000) := by
  exact
    packedTile16384 116875520 116908288 12 1806 10810 27 _ _ (92883 / 5000) (1857663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116908288 :
    ThetaLowerSegment 116908288 116941056 (5844788899549 / 50000) (11692804604891 / 100000) := by
  exact
    packedTile16384 116908288 116941056 12 1737 10812 27 _ _ (1857689 / 100000) (464423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116941056 :
    ThetaLowerSegment 116941056 116973824 (11692804604891 / 100000) (11696148495491 / 100000) := by
  exact
    packedTile16384 116941056 116973824 12 1800 10813 27 _ _ (1857717 / 100000) (46443 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell116973824 :
    ThetaLowerSegment 116973824 117006592 (11696148495491 / 100000) (11699440419631 / 100000) := by
  exact
    packedTile16384 116973824 117006592 12 1772 10815 27 _ _ (371549 / 20000) (464437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117006592 :
    ThetaLowerSegment 117006592 117039360 (11699440419631 / 100000) (2340541276913 / 20000) := by
  exact
    packedTile16384 117006592 117039360 12 1758 10816 27 _ _ (1857773 / 100000) (116111 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117039360 :
    ThetaLowerSegment 117039360 117072128 (2340541276913 / 20000) (5852996417267 / 50000) := by
  exact
    packedTile16384 117039360 117072128 12 1769 10818 27 _ _ (1857801 / 100000) (464451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117072128 :
    ThetaLowerSegment 117072128 117104896 (5852996417267 / 50000) (585464431159 / 5000) := by
  exact
    packedTile16384 117072128 117104896 12 1774 10819 27 _ _ (1857829 / 100000) (232229 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117104896 :
    ThetaLowerSegment 117104896 117137664 (585464431159 / 5000) (11712500857933 / 100000) := by
  exact
    packedTile16384 117104896 117137664 12 1729 10821 27 _ _ (1857857 / 100000) (92893 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117137664 :
    ThetaLowerSegment 117137664 117170432 (11712500857933 / 100000) (11715793030153 / 100000) := by
  exact
    packedTile16384 117137664 117170432 12 1772 10823 27 _ _ (371577 / 20000) (58059 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117170432 :
    ThetaLowerSegment 117170432 117203200 (11715793030153 / 100000) (11719062957033 / 100000) := by
  exact
    packedTile16384 117170432 117203200 12 1760 10824 27 _ _ (1857913 / 100000) (464479 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117203200 :
    ThetaLowerSegment 117203200 117235968 (11719062957033 / 100000) (11722331073493 / 100000) := by
  exact
    packedTile16384 117203200 117235968 12 1759 10826 27 _ _ (92897 / 5000) (1857943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117235968 :
    ThetaLowerSegment 117235968 117268736 (11722331073493 / 100000) (11725632682629 / 100000) := by
  exact
    packedTile16384 117235968 117268736 12 1777 10827 27 _ _ (116123 / 6250) (1857971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117268736 :
    ThetaLowerSegment 117268736 117301504 (11725632682629 / 100000) (11728936199517 / 100000) := by
  exact
    packedTile16384 117268736 117301504 12 1778 10829 27 _ _ (464499 / 25000) (1857999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117301504 :
    ThetaLowerSegment 117301504 117334272 (11728936199517 / 100000) (11732215611877 / 100000) := by
  exact
    packedTile16384 117301504 117334272 12 1765 10830 27 _ _ (232253 / 12500) (1858027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117334272 :
    ThetaLowerSegment 117334272 117367040 (11732215611877 / 100000) (11735448622357 / 100000) := by
  exact
    packedTile16384 117334272 117367040 12 1740 10832 27 _ _ (464513 / 25000) (371611 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117367040 :
    ThetaLowerSegment 117367040 117399808 (11735448622357 / 100000) (11738722559317 / 100000) := by
  exact
    packedTile16384 117367040 117399808 12 1762 10833 27 _ _ (11613 / 625) (1858083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117399808 :
    ThetaLowerSegment 117399808 117432576 (11738722559317 / 100000) (11741912930753 / 100000) := by
  exact
    packedTile16384 117399808 117432576 12 1717 10835 27 _ _ (464527 / 25000) (1858111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117432576 :
    ThetaLowerSegment 117432576 117465344 (11741912930753 / 100000) (11745237136057 / 100000) := by
  exact
    packedTile16384 117432576 117465344 12 1789 10836 27 _ _ (232267 / 12500) (1858139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117465344 :
    ThetaLowerSegment 117465344 117498112 (11745237136057 / 100000) (2349689237057 / 20000) := by
  exact
    packedTile16384 117465344 117498112 12 1727 10838 27 _ _ (464541 / 25000) (1858167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117498112 :
    ThetaLowerSegment 117498112 117530880 (2349689237057 / 20000) (11751720319589 / 100000) := by
  exact
    packedTile16384 117498112 117530880 12 1762 10839 27 _ _ (116137 / 6250) (371639 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117530880 :
    ThetaLowerSegment 117530880 117563648 (11751720319589 / 100000) (11754990786789 / 100000) := by
  exact
    packedTile16384 117530880 117563648 12 1760 10841 27 _ _ (92911 / 5000) (1858223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117563648 :
    ThetaLowerSegment 117563648 117596416 (11754990786789 / 100000) (11758393238877 / 100000) := by
  exact
    packedTile16384 117563648 117596416 12 1831 10842 27 _ _ (232281 / 12500) (1858251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117596416 :
    ThetaLowerSegment 117596416 117629184 (11758393238877 / 100000) (11761615487727 / 100000) := by
  exact
    packedTile16384 117596416 117629184 12 1734 10844 27 _ _ (74331 / 4000) (929139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117629184 :
    ThetaLowerSegment 117629184 117661952 (11761615487727 / 100000) (11764938133491 / 100000) := by
  exact
    packedTile16384 117629184 117661952 12 1788 10845 27 _ _ (1858303 / 100000) (929153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117661952 :
    ThetaLowerSegment 117661952 117694720 (11764938133491 / 100000) (117681697711 / 1000) := by
  exact
    packedTile16384 117661952 117694720 12 1739 10847 27 _ _ (1858331 / 100000) (929167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117694720 :
    ThetaLowerSegment 117694720 117727488 (117681697711 / 1000) (2942848970581 / 25000) := by
  exact
    packedTile16384 117694720 117727488 12 1736 10848 27 _ _ (1858359 / 100000) (929181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117727488 :
    ThetaLowerSegment 117727488 117760256 (2942848970581 / 25000) (588730358753 / 5000) := by
  exact
    packedTile16384 117727488 117760256 12 1728 10850 27 _ _ (1858387 / 100000) (185839 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117760256 :
    ThetaLowerSegment 117760256 117793024 (588730358753 / 5000) (1177797090621 / 10000) := by
  exact
    packedTile16384 117760256 117793024 12 1810 10851 27 _ _ (371683 / 20000) (929209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117793024 :
    ThetaLowerSegment 117793024 117825792 (1177797090621 / 10000) (2945342499157 / 25000) := by
  exact
    packedTile16384 117793024 117825792 12 1829 10853 27 _ _ (929221 / 50000) (371689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117825792 :
    ThetaLowerSegment 117825792 117858560 (2945342499157 / 25000) (2946156509017 / 25000) := by
  exact
    packedTile16384 117825792 117858560 12 1752 10854 27 _ _ (185847 / 10000) (1858473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117858560 :
    ThetaLowerSegment 117858560 117891328 (2946156509017 / 25000) (5893906680069 / 50000) := by
  exact
    packedTile16384 117858560 117891328 12 1715 10856 27 _ _ (929249 / 50000) (1858501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117891328 :
    ThetaLowerSegment 117891328 117924096 (5893906680069 / 50000) (736947999973 / 6250) := by
  exact
    packedTile16384 117891328 117924096 12 1805 10857 27 _ _ (929263 / 50000) (1858529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117924096 :
    ThetaLowerSegment 117924096 117956864 (736947999973 / 6250) (5897224173689 / 50000) := by
  exact
    packedTile16384 117924096 117956864 12 1765 10859 27 _ _ (929277 / 50000) (1858557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117956864 :
    ThetaLowerSegment 117956864 117989632 (5897224173689 / 50000) (11797684136899 / 100000) := by
  exact
    packedTile16384 117956864 117989632 12 1741 10860 27 _ _ (1858581 / 100000) (232323 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell117989632 :
    ThetaLowerSegment 117989632 118022400 (11797684136899 / 100000) (1180095343013 / 10000) := by
  exact
    packedTile16384 117989632 118022400 12 1759 10862 27 _ _ (1858609 / 100000) (464653 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118022400 :
    ThetaLowerSegment 118022400 118055168 (1180095343013 / 10000) (5902145771091 / 50000) := by
  exact
    packedTile16384 118022400 118055168 12 1796 10863 27 _ _ (1858637 / 100000) (23233 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118055168 :
    ThetaLowerSegment 118055168 118087936 (5902145771091 / 50000) (737971977537 / 6250) := by
  exact
    packedTile16384 118055168 118087936 12 1754 10865 27 _ _ (371733 / 20000) (464667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118087936 :
    ThetaLowerSegment 118087936 118120704 (737971977537 / 6250) (11810743016473 / 100000) := by
  exact
    packedTile16384 118087936 118120704 12 1717 10866 27 _ _ (1858693 / 100000) (232337 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118120704 :
    ThetaLowerSegment 118120704 118153472 (11810743016473 / 100000) (11814040385753 / 100000) := by
  exact
    packedTile16384 118120704 118153472 12 1774 10868 27 _ _ (11617 / 625) (1858723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118153472 :
    ThetaLowerSegment 118153472 118186240 (11814040385753 / 100000) (11817404719633 / 100000) := by
  exact
    packedTile16384 118153472 118186240 12 1810 10869 27 _ _ (464687 / 25000) (1858751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118186240 :
    ThetaLowerSegment 118186240 118219008 (11817404719633 / 100000) (2364132259037 / 20000) := by
  exact
    packedTile16384 118186240 118219008 12 1752 10871 27 _ _ (232347 / 12500) (1858779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118219008 :
    ThetaLowerSegment 118219008 118251776 (2364132259037 / 20000) (5911950594407 / 50000) := by
  exact
    packedTile16384 118219008 118251776 12 1743 10872 27 _ _ (1858803 / 100000) (929403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118251776 :
    ThetaLowerSegment 118251776 118284544 (5911950594407 / 50000) (295679597109 / 2500) := by
  exact
    packedTile16384 118251776 118284544 12 1766 10874 27 _ _ (1858831 / 100000) (929417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118284544 :
    ThetaLowerSegment 118284544 118317312 (295679597109 / 2500) (1183051124197 / 10000) := by
  exact
    packedTile16384 118284544 118317312 12 1790 10875 27 _ _ (1858859 / 100000) (929431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118317312 :
    ThetaLowerSegment 118317312 118350080 (1183051124197 / 10000) (1183367134987 / 10000) := by
  exact
    packedTile16384 118317312 118350080 12 1700 10877 27 _ _ (1858887 / 100000) (185889 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118350080 :
    ThetaLowerSegment 118350080 118382848 (1183367134987 / 10000) (5918488249481 / 50000) := by
  exact
    packedTile16384 118350080 118382848 12 1778 10878 27 _ _ (929457 / 50000) (1858917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118382848 :
    ThetaLowerSegment 118382848 118415616 (5918488249481 / 50000) (592014177839 / 5000) := by
  exact
    packedTile16384 118382848 118415616 12 1779 10880 27 _ _ (929471 / 50000) (371789 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118415616 :
    ThetaLowerSegment 118415616 118448384 (592014177839 / 5000) (1184360925411 / 10000) := by
  exact
    packedTile16384 118415616 118448384 12 1789 10881 27 _ _ (185897 / 10000) (1858973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118448384 :
    ThetaLowerSegment 118448384 118481152 (1184360925411 / 10000) (2961723060703 / 25000) := by
  exact
    packedTile16384 118448384 118481152 12 1766 10883 27 _ _ (1858997 / 100000) (1859 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118481152 :
    ThetaLowerSegment 118481152 118513920 (2961723060703 / 25000) (1481265868289 / 12500) := by
  exact
    packedTile16384 118481152 118513920 12 1740 10884 27 _ _ (74361 / 4000) (464757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118513920 :
    ThetaLowerSegment 118513920 118546688 (1481265868289 / 12500) (11853411892963 / 100000) := by
  exact
    packedTile16384 118513920 118546688 12 1767 10886 27 _ _ (1859053 / 100000) (116191 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118546688 :
    ThetaLowerSegment 118546688 118579456 (11853411892963 / 100000) (11856663423883 / 100000) := by
  exact
    packedTile16384 118546688 118579456 12 1749 10887 27 _ _ (46477 / 2500) (1859083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118579456 :
    ThetaLowerSegment 118579456 118612224 (11856663423883 / 100000) (2371988578079 / 20000) := by
  exact
    packedTile16384 118579456 118612224 12 1764 10889 27 _ _ (464777 / 25000) (1859111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118612224 :
    ThetaLowerSegment 118612224 118644992 (2371988578079 / 20000) (11863244715931 / 100000) := by
  exact
    packedTile16384 118612224 118644992 12 1776 10890 27 _ _ (58098 / 3125) (1859139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118644992 :
    ThetaLowerSegment 118644992 118677760 (11863244715931 / 100000) (5933237041031 / 50000) := by
  exact
    packedTile16384 118644992 118677760 12 1737 10892 27 _ _ (1859163 / 100000) (929583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118677760 :
    ThetaLowerSegment 118677760 118710528 (5933237041031 / 50000) (11869818766671 / 100000) := by
  exact
    packedTile16384 118677760 118710528 12 1799 10893 27 _ _ (1859191 / 100000) (929597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118710528 :
    ThetaLowerSegment 118710528 118743296 (11869818766671 / 100000) (11873100286441 / 100000) := by
  exact
    packedTile16384 118710528 118743296 12 1765 10895 27 _ _ (929609 / 50000) (1859221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118743296 :
    ThetaLowerSegment 118743296 118776064 (11873100286441 / 100000) (11876290752577 / 100000) := by
  exact
    packedTile16384 118743296 118776064 12 1716 10896 27 _ _ (929623 / 50000) (1859249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118776064 :
    ThetaLowerSegment 118776064 118808832 (11876290752577 / 100000) (11879568652639 / 100000) := by
  exact
    packedTile16384 118776064 118808832 12 1763 10898 27 _ _ (929637 / 50000) (1859277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118808832 :
    ThetaLowerSegment 118808832 118841600 (11879568652639 / 100000) (5941408425743 / 50000) := by
  exact
    packedTile16384 118808832 118841600 12 1747 10899 27 _ _ (1859301 / 100000) (232413 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118841600 :
    ThetaLowerSegment 118841600 118874368 (5941408425743 / 50000) (2971517669309 / 25000) := by
  exact
    packedTile16384 118841600 118874368 12 1750 10901 27 _ _ (1859329 / 100000) (464833 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118874368 :
    ThetaLowerSegment 118874368 118907136 (2971517669309 / 25000) (2972331137559 / 25000) := by
  exact
    packedTile16384 118874368 118907136 12 1750 10902 27 _ _ (464839 / 25000) (1859359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118907136 :
    ThetaLowerSegment 118907136 118939904 (2972331137559 / 25000) (2973140899291 / 25000) := by
  exact
    packedTile16384 118907136 118939904 12 1742 10904 27 _ _ (232423 / 12500) (1859387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118939904 :
    ThetaLowerSegment 118939904 118972672 (2973140899291 / 25000) (2973940446021 / 25000) := by
  exact
    packedTile16384 118939904 118972672 12 1720 10905 27 _ _ (1859411 / 100000) (929707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell118972672 :
    ThetaLowerSegment 118972672 119005440 (2973940446021 / 25000) (11899054850553 / 100000) := by
  exact
    packedTile16384 118972672 119005440 12 1771 10907 27 _ _ (1859439 / 100000) (929721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119005440 :
    ThetaLowerSegment 119005440 119038208 (11899054850553 / 100000) (11902334948577 / 100000) := by
  exact
    packedTile16384 119005440 119038208 12 1764 10908 27 _ _ (929733 / 50000) (1859469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119038208 :
    ThetaLowerSegment 119038208 119070976 (11902334948577 / 100000) (11905572327631 / 100000) := by
  exact
    packedTile16384 119038208 119070976 12 1741 10910 27 _ _ (929747 / 50000) (1859497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119070976 :
    ThetaLowerSegment 119070976 119103744 (11905572327631 / 100000) (11908800457823 / 100000) := by
  exact
    packedTile16384 119070976 119103744 12 1736 10911 27 _ _ (929761 / 50000) (74381 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119103744 :
    ThetaLowerSegment 119103744 119136512 (11908800457823 / 100000) (11912043511279 / 100000) := by
  exact
    packedTile16384 119103744 119136512 12 1744 10913 27 _ _ (1859549 / 100000) (58111 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119136512 :
    ThetaLowerSegment 119136512 119169280 (11912043511279 / 100000) (5957657253611 / 50000) := by
  exact
    packedTile16384 119136512 119169280 12 1759 10914 27 _ _ (1859577 / 100000) (92979 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119169280 :
    ThetaLowerSegment 119169280 119202048 (5957657253611 / 50000) (5959280687903 / 50000) := by
  exact
    packedTile16384 119169280 119202048 12 1746 10916 27 _ _ (464901 / 25000) (1859607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119202048 :
    ThetaLowerSegment 119202048 119234816 (5959280687903 / 50000) (1192179155659 / 10000) := by
  exact
    packedTile16384 119202048 119234816 12 1737 10917 27 _ _ (116227 / 6250) (371927 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119234816 :
    ThetaLowerSegment 119234816 119267584 (1192179155659 / 10000) (1490632604639 / 12500) := by
  exact
    packedTile16384 119234816 119267584 12 1758 10919 27 _ _ (1859659 / 100000) (929831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119267584 :
    ThetaLowerSegment 119267584 119300352 (1490632604639 / 12500) (11928410133399 / 100000) := by
  exact
    packedTile16384 119267584 119300352 12 1801 10920 27 _ _ (1859687 / 100000) (185969 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119300352 :
    ThetaLowerSegment 119300352 119333120 (11928410133399 / 100000) (11931668352327 / 100000) := by
  exact
    packedTile16384 119300352 119333120 12 1752 10922 27 _ _ (929857 / 50000) (1859717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119333120 :
    ThetaLowerSegment 119333120 119365888 (11931668352327 / 100000) (11934889423739 / 100000) := by
  exact
    packedTile16384 119333120 119365888 12 1732 10923 27 _ _ (1859741 / 100000) (58117 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119365888 :
    ThetaLowerSegment 119365888 119398656 (11934889423739 / 100000) (5969102695933 / 50000) := by
  exact
    packedTile16384 119365888 119398656 12 1783 10925 27 _ _ (1859769 / 100000) (464943 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119398656 :
    ThetaLowerSegment 119398656 119431424 (5969102695933 / 50000) (238830279379 / 2000) := by
  exact
    packedTile16384 119398656 119431424 12 1779 10926 27 _ _ (464949 / 25000) (1859799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119431424 :
    ThetaLowerSegment 119431424 119464192 (238830279379 / 2000) (5972396419331 / 50000) := by
  exact
    packedTile16384 119431424 119464192 12 1763 10928 27 _ _ (116239 / 6250) (1859827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119464192 :
    ThetaLowerSegment 119464192 119496960 (5972396419331 / 50000) (5974007050297 / 50000) := by
  exact
    packedTile16384 119464192 119496960 12 1732 10929 27 _ _ (1859851 / 100000) (929927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119496960 :
    ThetaLowerSegment 119496960 119529728 (5974007050297 / 50000) (11951356303157 / 100000) := by
  exact
    packedTile16384 119496960 119529728 12 1797 10931 27 _ _ (1859879 / 100000) (929941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119529728 :
    ThetaLowerSegment 119529728 119562496 (11951356303157 / 100000) (2390919623863 / 20000) := by
  exact
    packedTile16384 119529728 119562496 12 1743 10932 27 _ _ (929953 / 50000) (1859909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119562496 :
    ThetaLowerSegment 119562496 119595264 (2390919623863 / 20000) (11957916239787 / 100000) := by
  exact
    packedTile16384 119562496 119595264 12 1784 10934 27 _ _ (1859933 / 100000) (58123 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119595264 :
    ThetaLowerSegment 119595264 119628032 (11957916239787 / 100000) (1495149883869 / 12500) := by
  exact
    packedTile16384 119595264 119628032 12 1765 10935 27 _ _ (1859961 / 100000) (464991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119628032 :
    ThetaLowerSegment 119628032 119660800 (1495149883869 / 12500) (598223725491 / 5000) := by
  exact
    packedTile16384 119628032 119660800 12 1761 10937 27 _ _ (464997 / 25000) (1859991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119660800 :
    ThetaLowerSegment 119660800 119693568 (598223725491 / 5000) (2991917969331 / 25000) := by
  exact
    packedTile16384 119660800 119693568 12 1719 10938 27 _ _ (116251 / 6250) (1860019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119693568 :
    ThetaLowerSegment 119693568 119726336 (2991917969331 / 25000) (5985470916459 / 50000) := by
  exact
    packedTile16384 119693568 119726336 12 1758 10940 27 _ _ (1860043 / 100000) (930023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119726336 :
    ThetaLowerSegment 119726336 119759104 (5985470916459 / 50000) (5987117078409 / 50000) := by
  exact
    packedTile16384 119726336 119759104 12 1770 10941 27 _ _ (186007 / 10000) (1860073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119759104 :
    ThetaLowerSegment 119759104 119791872 (5987117078409 / 50000) (2994379307447 / 25000) := by
  exact
    packedTile16384 119759104 119791872 12 1765 10943 27 _ _ (930049 / 50000) (1860101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119791872 :
    ThetaLowerSegment 119791872 119824640 (2994379307447 / 25000) (374399022759 / 3125) := by
  exact
    packedTile16384 119791872 119824640 12 1748 10944 27 _ _ (14881 / 800) (58129 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119824640 :
    ThetaLowerSegment 119824640 119857408 (374399022759 / 3125) (374503191271 / 3125) := by
  exact
    packedTile16384 119824640 119857408 12 1792 10946 27 _ _ (232519 / 12500) (372031 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119857408 :
    ThetaLowerSegment 119857408 119890176 (374503191271 / 3125) (2996864936393 / 25000) := by
  exact
    packedTile16384 119857408 119890176 12 1805 10947 27 _ _ (93009 / 5000) (1860183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119890176 :
    ThetaLowerSegment 119890176 119922944 (2996864936393 / 25000) (11990679763889 / 100000) := by
  exact
    packedTile16384 119890176 119922944 12 1731 10949 27 _ _ (1860207 / 100000) (186021 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119922944 :
    ThetaLowerSegment 119922944 119955712 (11990679763889 / 100000) (11994039346493 / 100000) := by
  exact
    packedTile16384 119922944 119955712 12 1806 10950 27 _ _ (930117 / 50000) (1860237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119955712 :
    ThetaLowerSegment 119955712 119988480 (11994039346493 / 100000) (11997304106303 / 100000) := by
  exact
    packedTile16384 119955712 119988480 12 1755 10952 27 _ _ (930131 / 50000) (372053 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell119988480 :
    ThetaLowerSegment 119988480 120021248 (11997304106303 / 100000) (12000600538411 / 100000) := by
  exact
    packedTile16384 119988480 120021248 12 1772 10953 27 _ _ (1860289 / 100000) (465073 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120021248 :
    ThetaLowerSegment 120021248 120054016 (12000600538411 / 100000) (12003945386579 / 100000) := by
  exact
    packedTile16384 120021248 120054016 12 1798 10955 27 _ _ (465079 / 25000) (1860319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120054016 :
    ThetaLowerSegment 120054016 120086784 (12003945386579 / 100000) (12007312609219 / 100000) := by
  exact
    packedTile16384 120054016 120086784 12 1810 10956 27 _ _ (232543 / 12500) (1860347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120086784 :
    ThetaLowerSegment 120086784 120119552 (12007312609219 / 100000) (1201055151513 / 10000) := by
  exact
    packedTile16384 120086784 120119552 12 1741 10958 27 _ _ (1860371 / 100000) (930187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120119552 :
    ThetaLowerSegment 120119552 120152320 (1201055151513 / 10000) (3003448547211 / 25000) := by
  exact
    packedTile16384 120119552 120152320 12 1743 10959 27 _ _ (930199 / 50000) (1860401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120152320 :
    ThetaLowerSegment 120152320 120185088 (3003448547211 / 25000) (1502129381367 / 12500) := by
  exact
    packedTile16384 120152320 120185088 12 1742 10961 27 _ _ (930213 / 50000) (1860429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120185088 :
    ThetaLowerSegment 120185088 120217856 (1502129381367 / 12500) (3005082943413 / 25000) := by
  exact
    packedTile16384 120185088 120217856 12 1772 10962 27 _ _ (1860453 / 100000) (232557 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120217856 :
    ThetaLowerSegment 120217856 120250624 (3005082943413 / 25000) (3005928531573 / 25000) := by
  exact
    packedTile16384 120217856 120250624 12 1818 10964 27 _ _ (11628 / 625) (1860483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120250624 :
    ThetaLowerSegment 120250624 120283392 (3005928531573 / 25000) (12026934663909 / 100000) := by
  exact
    packedTile16384 120250624 120283392 12 1731 10965 27 _ _ (1860507 / 100000) (186051 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120283392 :
    ThetaLowerSegment 120283392 120316160 (12026934663909 / 100000) (6015066461787 / 50000) := by
  exact
    packedTile16384 120283392 120316160 12 1719 10967 27 _ _ (372107 / 20000) (930269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120316160 :
    ThetaLowerSegment 120316160 120348928 (6015066461787 / 50000) (3008345831347 / 25000) := by
  exact
    packedTile16384 120316160 120348928 12 1747 10968 27 _ _ (930281 / 50000) (372113 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120348928 :
    ThetaLowerSegment 120348928 120381696 (3008345831347 / 25000) (6018301072179 / 50000) := by
  exact
    packedTile16384 120348928 120381696 12 1730 10970 27 _ _ (1860589 / 100000) (116287 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120381696 :
    ThetaLowerSegment 120381696 120414464 (6018301072179 / 50000) (6019967253807 / 50000) := by
  exact
    packedTile16384 120381696 120414464 12 1791 10971 27 _ _ (232577 / 12500) (1860619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120414464 :
    ThetaLowerSegment 120414464 120447232 (6019967253807 / 50000) (6021579501833 / 50000) := by
  exact
    packedTile16384 120414464 120447232 12 1733 10973 27 _ _ (465161 / 25000) (1860647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120447232 :
    ThetaLowerSegment 120447232 120480000 (6021579501833 / 50000) (12046457973349 / 100000) := by
  exact
    packedTile16384 120447232 120480000 12 1773 10974 27 _ _ (1860671 / 100000) (930337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120480000 :
    ThetaLowerSegment 120480000 120512768 (12046457973349 / 100000) (12049697448567 / 100000) := by
  exact
    packedTile16384 120480000 120512768 12 1741 10976 27 _ _ (930349 / 50000) (1860701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120512768 :
    ThetaLowerSegment 120512768 120545536 (12049697448567 / 100000) (12052998374717 / 100000) := by
  exact
    packedTile16384 120512768 120545536 12 1774 10977 27 _ _ (74429 / 4000) (232591 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120545536 :
    ThetaLowerSegment 120545536 120578304 (12052998374717 / 100000) (2411239401481 / 20000) := by
  exact
    packedTile16384 120545536 120578304 12 1719 10979 27 _ _ (116297 / 6250) (372151 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120578304 :
    ThetaLowerSegment 120578304 120611072 (2411239401481 / 20000) (12059468256887 / 100000) := by
  exact
    packedTile16384 120578304 120611072 12 1758 10980 27 _ _ (1860779 / 100000) (930391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120611072 :
    ThetaLowerSegment 120611072 120643840 (12059468256887 / 100000) (12062784214961 / 100000) := by
  exact
    packedTile16384 120611072 120643840 12 1782 10982 27 _ _ (1860807 / 100000) (186081 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120643840 :
    ThetaLowerSegment 120643840 120676608 (12062784214961 / 100000) (12066022066121 / 100000) := by
  exact
    packedTile16384 120643840 120676608 12 1740 10983 27 _ _ (930417 / 50000) (1860837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120676608 :
    ThetaLowerSegment 120676608 120709376 (12066022066121 / 100000) (6034686738391 / 50000) := by
  exact
    packedTile16384 120676608 120709376 12 1801 10985 27 _ _ (1860861 / 100000) (58152 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120709376 :
    ThetaLowerSegment 120709376 120742144 (6034686738391 / 50000) (6036284310739 / 50000) := by
  exact
    packedTile16384 120709376 120742144 12 1717 10986 27 _ _ (232611 / 12500) (1860891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120742144 :
    ThetaLowerSegment 120742144 120774912 (6036284310739 / 50000) (377368142524 / 3125) := by
  exact
    packedTile16384 120742144 120774912 12 1726 10988 27 _ _ (372183 / 20000) (930459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120774912 :
    ThetaLowerSegment 120774912 120807680 (377368142524 / 3125) (301974348431 / 2500) := by
  exact
    packedTile16384 120774912 120807680 12 1716 10989 27 _ _ (930471 / 50000) (372189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120807680 :
    ThetaLowerSegment 120807680 120840448 (301974348431 / 2500) (120821710837 / 1000) := by
  exact
    packedTile16384 120807680 120840448 12 1718 10991 27 _ _ (186097 / 10000) (1860973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120840448 :
    ThetaLowerSegment 120840448 120873216 (120821710837 / 1000) (1208550226833 / 10000) := by
  exact
    packedTile16384 120840448 120873216 12 1790 10992 27 _ _ (1860997 / 100000) (1861 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120873216 :
    ThetaLowerSegment 120873216 120905984 (1208550226833 / 10000) (6044400001429 / 50000) := by
  exact
    packedTile16384 120873216 120905984 12 1772 10994 27 _ _ (58157 / 3125) (1861027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120905984 :
    ThetaLowerSegment 120905984 120938752 (6044400001429 / 50000) (6046041448411 / 50000) := by
  exact
    packedTile16384 120905984 120938752 12 1764 10995 27 _ _ (1861051 / 100000) (930527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120938752 :
    ThetaLowerSegment 120938752 120971520 (6046041448411 / 50000) (3023834480561 / 25000) := by
  exact
    packedTile16384 120938752 120971520 12 1749 10997 27 _ _ (930539 / 50000) (1861081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell120971520 :
    ThetaLowerSegment 120971520 121004288 (3023834480561 / 25000) (378083299312 / 3125) := by
  exact
    packedTile16384 120971520 121004288 12 1788 10998 27 _ _ (372221 / 20000) (465277 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121004288 :
    ThetaLowerSegment 121004288 121037056 (378083299312 / 3125) (3025515535971 / 25000) := by
  exact
    packedTile16384 121004288 121037056 12 1825 11000 27 _ _ (465283 / 25000) (372227 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121037056 :
    ThetaLowerSegment 121037056 121069824 (3025515535971 / 25000) (2421067184513 / 20000) := by
  exact
    packedTile16384 121037056 121069824 12 1759 11001 27 _ _ (1861159 / 100000) (930581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121069824 :
    ThetaLowerSegment 121069824 121102592 (2421067184513 / 20000) (12108661861947 / 100000) := by
  exact
    packedTile16384 121069824 121102592 12 1787 11003 27 _ _ (930593 / 50000) (1861189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121102592 :
    ThetaLowerSegment 121102592 121135360 (12108661861947 / 100000) (12111952486531 / 100000) := by
  exact
    packedTile16384 121102592 121135360 12 1768 11004 27 _ _ (1861213 / 100000) (58163 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121135360 :
    ThetaLowerSegment 121135360 121168128 (12111952486531 / 100000) (12115191044131 / 100000) := by
  exact
    packedTile16384 121135360 121168128 12 1740 11006 27 _ _ (46531 / 2500) (1861243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121168128 :
    ThetaLowerSegment 121168128 121200896 (12115191044131 / 100000) (3029633004599 / 25000) := by
  exact
    packedTile16384 121168128 121200896 12 1795 11007 27 _ _ (1861267 / 100000) (186127 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121200896 :
    ThetaLowerSegment 121200896 121233664 (3029633004599 / 25000) (3030444529219 / 25000) := by
  exact
    packedTile16384 121200896 121233664 12 1744 11009 27 _ _ (372259 / 20000) (930649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121233664 :
    ThetaLowerSegment 121233664 121266432 (3030444529219 / 25000) (3031246759001 / 25000) := by
  exact
    packedTile16384 121233664 121266432 12 1724 11010 27 _ _ (930661 / 50000) (74453 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121266432 :
    ThetaLowerSegment 121266432 121299200 (3031246759001 / 25000) (6064122198377 / 50000) := by
  exact
    packedTile16384 121266432 121299200 12 1750 11012 27 _ _ (1861349 / 100000) (232669 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121299200 :
    ThetaLowerSegment 121299200 121331968 (6064122198377 / 50000) (1213156881429 / 10000) := by
  exact
    packedTile16384 121299200 121331968 12 1786 11013 27 _ _ (58168 / 3125) (1861379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121331968 :
    ThetaLowerSegment 121331968 121364736 (1213156881429 / 10000) (12134824408137 / 100000) := by
  exact
    packedTile16384 121331968 121364736 12 1749 11015 27 _ _ (1861403 / 100000) (930703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121364736 :
    ThetaLowerSegment 121364736 121397504 (12134824408137 / 100000) (12138085633497 / 100000) := by
  exact
    packedTile16384 121364736 121397504 12 1752 11016 27 _ _ (186143 / 10000) (1861433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121397504 :
    ThetaLowerSegment 121397504 121430272 (12138085633497 / 100000) (242826081853 / 2000) := by
  exact
    packedTile16384 121397504 121430272 12 1729 11018 27 _ _ (1861457 / 100000) (93073 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121430272 :
    ThetaLowerSegment 121430272 121463040 (242826081853 / 2000) (6072339481571 / 50000) := by
  exact
    packedTile16384 121430272 121463040 12 1813 11019 27 _ _ (465371 / 25000) (1861487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121463040 :
    ThetaLowerSegment 121463040 121495808 (6072339481571 / 50000) (303698787487 / 2500) := by
  exact
    packedTile16384 121463040 121495808 12 1758 11021 27 _ _ (1861511 / 100000) (930757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121495808 :
    ThetaLowerSegment 121495808 121528576 (303698787487 / 2500) (6075592495493 / 50000) := by
  exact
    packedTile16384 121495808 121528576 12 1737 11022 27 _ _ (930769 / 50000) (1861541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121528576 :
    ThetaLowerSegment 121528576 121561344 (6075592495493 / 50000) (6077199956007 / 50000) := by
  exact
    packedTile16384 121528576 121561344 12 1727 11024 27 _ _ (465391 / 25000) (1861567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121561344 :
    ThetaLowerSegment 121561344 121594112 (6077199956007 / 50000) (12157812208317 / 100000) := by
  exact
    packedTile16384 121561344 121594112 12 1833 11025 27 _ _ (1861591 / 100000) (930797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121594112 :
    ThetaLowerSegment 121594112 121626880 (12157812208317 / 100000) (12161066316581 / 100000) := by
  exact
    packedTile16384 121594112 121626880 12 1748 11026 27 _ _ (930809 / 50000) (1861621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121626880 :
    ThetaLowerSegment 121626880 121659648 (12161066316581 / 100000) (6082116487363 / 50000) := by
  exact
    packedTile16384 121626880 121659648 12 1701 11028 27 _ _ (372329 / 20000) (116353 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121659648 :
    ThetaLowerSegment 121659648 121692416 (6082116487363 / 50000) (6083732418659 / 50000) := by
  exact
    packedTile16384 121659648 121692416 12 1736 11029 27 _ _ (232709 / 12500) (74467 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121692416 :
    ThetaLowerSegment 121692416 121725184 (6083732418659 / 50000) (6085422841351 / 50000) := by
  exact
    packedTile16384 121692416 121725184 12 1816 11031 27 _ _ (1861699 / 100000) (930851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121725184 :
    ThetaLowerSegment 121725184 121757952 (6085422841351 / 50000) (3043534768999 / 25000) := by
  exact
    packedTile16384 121725184 121757952 12 1769 11032 27 _ _ (930863 / 50000) (1861729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121757952 :
    ThetaLowerSegment 121757952 121790720 (3043534768999 / 25000) (1217737480271 / 10000) := by
  exact
    packedTile16384 121757952 121790720 12 1738 11034 27 _ _ (1861753 / 100000) (465439 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121790720 :
    ThetaLowerSegment 121790720 121823488 (1217737480271 / 10000) (1218064036483 / 10000) := by
  exact
    packedTile16384 121790720 121823488 12 1754 11035 27 _ _ (93089 / 5000) (1861783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121823488 :
    ThetaLowerSegment 121823488 121856256 (1218064036483 / 10000) (3045972769963 / 25000) := by
  exact
    packedTile16384 121823488 121856256 12 1746 11037 27 _ _ (1861807 / 100000) (186181 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121856256 :
    ThetaLowerSegment 121856256 121889024 (3045972769963 / 25000) (1523399246671 / 12500) := by
  exact
    packedTile16384 121856256 121889024 12 1774 11038 27 _ _ (930917 / 50000) (1861837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121889024 :
    ThetaLowerSegment 121889024 121921792 (1523399246671 / 12500) (6095222391337 / 50000) := by
  exact
    packedTile16384 121889024 121921792 12 1746 11040 27 _ _ (1861861 / 100000) (232733 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121921792 :
    ThetaLowerSegment 121921792 121954560 (6095222391337 / 50000) (6096880402601 / 50000) := by
  exact
    packedTile16384 121921792 121954560 12 1781 11041 27 _ _ (58184 / 3125) (1861891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121954560 :
    ThetaLowerSegment 121954560 121987328 (6096880402601 / 50000) (304926270181 / 2500) := by
  exact
    packedTile16384 121954560 121987328 12 1767 11043 27 _ _ (930957 / 50000) (1861917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell121987328 :
    ThetaLowerSegment 121987328 122020096 (304926270181 / 2500) (610018253111 / 5000) := by
  exact
    packedTile16384 121987328 122020096 12 1780 11044 27 _ _ (1861941 / 100000) (232743 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122020096 :
    ThetaLowerSegment 122020096 122052864 (610018253111 / 5000) (3050917048363 / 25000) := by
  exact
    packedTile16384 122020096 122052864 12 1774 11046 27 _ _ (116373 / 6250) (1861971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122052864 :
    ThetaLowerSegment 122052864 122085632 (3050917048363 / 25000) (1525869094079 / 12500) := by
  exact
    packedTile16384 122052864 122085632 12 1764 11047 27 _ _ (372399 / 20000) (930999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122085632 :
    ThetaLowerSegment 122085632 122118400 (1525869094079 / 12500) (1221022804933 / 10000) := by
  exact
    packedTile16384 122085632 122118400 12 1759 11049 27 _ _ (931011 / 50000) (74481 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122118400 :
    ThetaLowerSegment 122118400 122151168 (1221022804933 / 10000) (12213425187463 / 100000) := by
  exact
    packedTile16384 122118400 122151168 12 1717 11050 27 _ _ (1862049 / 100000) (465513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122151168 :
    ThetaLowerSegment 122151168 122183936 (12213425187463 / 100000) (3054175144347 / 25000) := by
  exact
    packedTile16384 122151168 122183936 12 1759 11052 27 _ _ (74483 / 4000) (931039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122183936 :
    ThetaLowerSegment 122183936 122216704 (3054175144347 / 25000) (611000383527 / 5000) := by
  exact
    packedTile16384 122183936 122216704 12 1776 11053 27 _ _ (931051 / 50000) (372421 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122216704 :
    ThetaLowerSegment 122216704 122249472 (611000383527 / 5000) (12223309225257 / 100000) := by
  exact
    packedTile16384 122216704 122249472 12 1773 11055 27 _ _ (1862129 / 100000) (465533 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122249472 :
    ThetaLowerSegment 122249472 122282240 (12223309225257 / 100000) (12226586619817 / 100000) := by
  exact
    packedTile16384 122249472 122282240 12 1760 11056 27 _ _ (465539 / 25000) (1862159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122282240 :
    ThetaLowerSegment 122282240 122315008 (12226586619817 / 100000) (1222981005859 / 10000) := by
  exact
    packedTile16384 122282240 122315008 12 1731 11058 27 _ _ (1862183 / 100000) (931093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122315008 :
    ThetaLowerSegment 122315008 122347776 (1222981005859 / 10000) (1223305030399 / 10000) := by
  exact
    packedTile16384 122315008 122347776 12 1740 11059 27 _ _ (186221 / 10000) (1862213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122347776 :
    ThetaLowerSegment 122347776 122380544 (1223305030399 / 10000) (6118155539613 / 50000) := by
  exact
    packedTile16384 122347776 122380544 12 1751 11061 27 _ _ (465559 / 25000) (1862239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122380544 :
    ThetaLowerSegment 122380544 122413312 (6118155539613 / 50000) (76497173077 / 625) := by
  exact
    packedTile16384 122380544 122413312 12 1738 11062 27 _ _ (1862263 / 100000) (931133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122413312 :
    ThetaLowerSegment 122413312 122446080 (76497173077 / 625) (30607026061 / 250) := by
  exact
    packedTile16384 122413312 122446080 12 1752 11064 27 _ _ (186229 / 10000) (1862293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122446080 :
    ThetaLowerSegment 122446080 122478848 (30607026061 / 250) (765376781761 / 6250) := by
  exact
    packedTile16384 122446080 122478848 12 1728 11065 27 _ _ (1862317 / 100000) (23279 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122478848 :
    ThetaLowerSegment 122478848 122511616 (765376781761 / 6250) (12249203802991 / 100000) := by
  exact
    packedTile16384 122478848 122511616 12 1705 11067 27 _ _ (1862343 / 100000) (931173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122511616 :
    ThetaLowerSegment 122511616 122544384 (12249203802991 / 100000) (12252494610781 / 100000) := by
  exact
    packedTile16384 122511616 122544384 12 1767 11068 27 _ _ (186237 / 10000) (1862373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122544384 :
    ThetaLowerSegment 122544384 122577152 (12252494610781 / 100000) (765983798047 / 6250) := by
  exact
    packedTile16384 122544384 122577152 12 1743 11069 27 _ _ (1862397 / 100000) (2328 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122577152 :
    ThetaLowerSegment 122577152 122609920 (765983798047 / 6250) (306477654223 / 2500) := by
  exact
    packedTile16384 122577152 122609920 12 1807 11071 27 _ _ (232803 / 12500) (1862427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122609920 :
    ThetaLowerSegment 122609920 122642688 (306477654223 / 2500) (613120507761 / 5000) := by
  exact
    packedTile16384 122609920 122642688 12 1774 11072 27 _ _ (37249 / 2000) (1862453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122642688 :
    ThetaLowerSegment 122642688 122675456 (613120507761 / 5000) (12265682527309 / 100000) := by
  exact
    packedTile16384 122642688 122675456 12 1757 11074 27 _ _ (1862477 / 100000) (23281 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122675456 :
    ThetaLowerSegment 122675456 122708224 (12265682527309 / 100000) (12268964259357 / 100000) := by
  exact
    packedTile16384 122675456 122708224 12 1762 11075 27 _ _ (232813 / 12500) (1862507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122708224 :
    ThetaLowerSegment 122708224 122740992 (12268964259357 / 100000) (12272249762277 / 100000) := by
  exact
    packedTile16384 122708224 122740992 12 1764 11077 27 _ _ (186253 / 10000) (1862533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122740992 :
    ThetaLowerSegment 122740992 122773760 (12272249762277 / 100000) (6137779763033 / 50000) := by
  exact
    packedTile16384 122740992 122773760 12 1777 11078 27 _ _ (1862557 / 100000) (11641 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122773760 :
    ThetaLowerSegment 122773760 122806528 (6137779763033 / 50000) (6139442119253 / 50000) := by
  exact
    packedTile16384 122773760 122806528 12 1785 11080 27 _ _ (232823 / 12500) (1862587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122806528 :
    ThetaLowerSegment 122806528 122839296 (6139442119253 / 50000) (1535276357719 / 12500) := by
  exact
    packedTile16384 122806528 122839296 12 1786 11081 27 _ _ (1862611 / 100000) (931307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122839296 :
    ThetaLowerSegment 122839296 122872064 (1535276357719 / 12500) (12285531943523 / 100000) := by
  exact
    packedTile16384 122839296 122872064 12 1783 11083 27 _ _ (1862637 / 100000) (23283 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122872064 :
    ThetaLowerSegment 122872064 122904832 (12285531943523 / 100000) (2457761301367 / 20000) := by
  exact
    packedTile16384 122872064 122904832 12 1758 11084 27 _ _ (232833 / 12500) (1862667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122904832 :
    ThetaLowerSegment 122904832 122937600 (2457761301367 / 20000) (12292017786119 / 100000) := by
  exact
    packedTile16384 122904832 122937600 12 1724 11086 27 _ _ (1862691 / 100000) (931347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122937600 :
    ThetaLowerSegment 122937600 122970368 (12292017786119 / 100000) (12295232835661 / 100000) := by
  exact
    packedTile16384 122937600 122970368 12 1726 11087 27 _ _ (1862717 / 100000) (11642 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell122970368 :
    ThetaLowerSegment 122970368 123003136 (12295232835661 / 100000) (2459708213801 / 20000) := by
  exact
    packedTile16384 122970368 123003136 12 1776 11089 27 _ _ (232843 / 12500) (1862747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123003136 :
    ThetaLowerSegment 123003136 123035904 (2459708213801 / 20000) (12301737584041 / 100000) := by
  exact
    packedTile16384 123003136 123035904 12 1716 11090 27 _ _ (1862771 / 100000) (931387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123035904 :
    ThetaLowerSegment 123035904 123068672 (12301737584041 / 100000) (12304990027603 / 100000) := by
  exact
    packedTile16384 123035904 123068672 12 1746 11092 27 _ _ (1862797 / 100000) (4657 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123068672 :
    ThetaLowerSegment 123068672 123101440 (12304990027603 / 100000) (492332085147 / 4000) := by
  exact
    packedTile16384 123068672 123101440 12 1778 11093 27 _ _ (232853 / 12500) (1862827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123101440 :
    ThetaLowerSegment 123101440 123134208 (492332085147 / 4000) (492465316179 / 4000) := by
  exact
    packedTile16384 123101440 123134208 12 1788 11095 27 _ _ (37257 / 2000) (1862853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123134208 :
    ThetaLowerSegment 123134208 123166976 (492465316179 / 4000) (12314866858947 / 100000) := by
  exact
    packedTile16384 123134208 123166976 12 1736 11096 27 _ _ (1862877 / 100000) (11643 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123166976 :
    ThetaLowerSegment 123166976 123199744 (12314866858947 / 100000) (12318153021603 / 100000) := by
  exact
    packedTile16384 123166976 123199744 12 1764 11098 27 _ _ (232863 / 12500) (1862907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123199744 :
    ThetaLowerSegment 123199744 123232512 (12318153021603 / 100000) (12321444818913 / 100000) := by
  exact
    packedTile16384 123199744 123232512 12 1767 11099 27 _ _ (186293 / 10000) (1862933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123232512 :
    ThetaLowerSegment 123232512 123265280 (12321444818913 / 100000) (12324757156459 / 100000) := by
  exact
    packedTile16384 123232512 123265280 12 1778 11101 27 _ _ (1862957 / 100000) (23287 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123265280 :
    ThetaLowerSegment 123265280 123298048 (12324757156459 / 100000) (493124570073 / 4000) := by
  exact
    packedTile16384 123265280 123298048 12 1802 11102 27 _ _ (1862983 / 100000) (931493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123298048 :
    ThetaLowerSegment 123298048 123330816 (493124570073 / 4000) (2466264098407 / 20000) := by
  exact
    packedTile16384 123298048 123330816 12 1721 11103 27 _ _ (186301 / 10000) (1863013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123330816 :
    ThetaLowerSegment 123330816 123363584 (2466264098407 / 20000) (3083644735937 / 25000) := by
  exact
    packedTile16384 123330816 123363584 12 1749 11105 27 _ _ (1863037 / 100000) (11644 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123363584 :
    ThetaLowerSegment 123363584 123396352 (3083644735937 / 25000) (6168949461007 / 50000) := by
  exact
    packedTile16384 123363584 123396352 12 1782 11106 27 _ _ (1863063 / 100000) (931533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123396352 :
    ThetaLowerSegment 123396352 123429120 (6168949461007 / 50000) (771323738969 / 6250) := by
  exact
    packedTile16384 123396352 123429120 12 1761 11108 27 _ _ (186309 / 10000) (1863093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123429120 :
    ThetaLowerSegment 123429120 123461888 (771323738969 / 6250) (3086126371391 / 25000) := by
  exact
    packedTile16384 123429120 123461888 12 1785 11109 27 _ _ (465779 / 25000) (1863119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123461888 :
    ThetaLowerSegment 123461888 123494656 (3086126371391 / 25000) (12347738038669 / 100000) := by
  exact
    packedTile16384 123461888 123494656 12 1735 11111 27 _ _ (1863143 / 100000) (931573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123494656 :
    ThetaLowerSegment 123494656 123527424 (12347738038669 / 100000) (3087746385559 / 25000) := by
  exact
    packedTile16384 123494656 123527424 12 1743 11112 27 _ _ (1863169 / 100000) (465793 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123527424 :
    ThetaLowerSegment 123527424 123560192 (3087746385559 / 25000) (3088566191799 / 25000) := by
  exact
    packedTile16384 123527424 123560192 12 1760 11114 27 _ _ (465799 / 25000) (1863199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123560192 :
    ThetaLowerSegment 123560192 123592960 (3088566191799 / 25000) (6178763634459 / 50000) := by
  exact
    packedTile16384 123560192 123592960 12 1751 11115 27 _ _ (931611 / 50000) (74529 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123592960 :
    ThetaLowerSegment 123592960 123625728 (6178763634459 / 50000) (2472184794369 / 20000) := by
  exact
    packedTile16384 123592960 123625728 12 1823 11117 27 _ _ (1863249 / 100000) (465813 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123625728 :
    ThetaLowerSegment 123625728 123658496 (2472184794369 / 20000) (2472817562559 / 20000) := by
  exact
    packedTile16384 123625728 123658496 12 1698 11118 27 _ _ (74531 / 4000) (931639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123658496 :
    ThetaLowerSegment 123658496 123691264 (2472817562559 / 20000) (12367438029791 / 100000) := by
  exact
    packedTile16384 123658496 123691264 12 1798 11120 27 _ _ (931651 / 50000) (372661 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123691264 :
    ThetaLowerSegment 123691264 123724032 (12367438029791 / 100000) (2474139025427 / 20000) := by
  exact
    packedTile16384 123691264 123724032 12 1748 11121 27 _ _ (58229 / 3125) (1863331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123724032 :
    ThetaLowerSegment 123724032 123756800 (2474139025427 / 20000) (2474803125149 / 20000) := by
  exact
    packedTile16384 123724032 123756800 12 1782 11123 27 _ _ (372671 / 20000) (931679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123756800 :
    ThetaLowerSegment 123756800 123789568 (2474803125149 / 20000) (12377310083353 / 100000) := by
  exact
    packedTile16384 123756800 123789568 12 1768 11124 27 _ _ (1863381 / 100000) (232923 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123789568 :
    ThetaLowerSegment 123789568 123822336 (12377310083353 / 100000) (12380600861881 / 100000) := by
  exact
    packedTile16384 123789568 123822336 12 1766 11126 27 _ _ (116463 / 6250) (1863411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123822336 :
    ThetaLowerSegment 123822336 123855104 (12380600861881 / 100000) (2476772746963 / 20000) := by
  exact
    packedTile16384 123822336 123855104 12 1751 11127 27 _ _ (931717 / 50000) (1863437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123855104 :
    ThetaLowerSegment 123855104 123887872 (2476772746963 / 20000) (1238717137809 / 10000) := by
  exact
    packedTile16384 123855104 123887872 12 1775 11129 27 _ _ (1863461 / 100000) (232933 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123887872 :
    ThetaLowerSegment 123887872 123920640 (1238717137809 / 10000) (6195233011553 / 50000) := by
  exact
    packedTile16384 123887872 123920640 12 1768 11130 27 _ _ (1863487 / 100000) (186349 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123920640 :
    ThetaLowerSegment 123920640 123953408 (6195233011553 / 50000) (619689247077 / 5000) := by
  exact
    packedTile16384 123920640 123953408 12 1781 11131 27 _ _ (931757 / 50000) (1863517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123953408 :
    ThetaLowerSegment 123953408 123986176 (619689247077 / 5000) (619850070579 / 5000) := by
  exact
    packedTile16384 123953408 123986176 12 1726 11133 27 _ _ (93177 / 5000) (1863543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell123986176 :
    ThetaLowerSegment 123986176 124018944 (619850070579 / 5000) (12400372604283 / 100000) := by
  exact
    packedTile16384 123986176 124018944 12 1809 11134 27 _ _ (1863567 / 100000) (186357 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124018944 :
    ThetaLowerSegment 124018944 124051712 (12400372604283 / 100000) (12403645073591 / 100000) := by
  exact
    packedTile16384 124018944 124051712 12 1756 11136 27 _ _ (1863593 / 100000) (465899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124051712 :
    ThetaLowerSegment 124051712 124084480 (12403645073591 / 100000) (3101712158663 / 25000) := by
  exact
    packedTile16384 124051712 124084480 12 1719 11137 27 _ _ (1863619 / 100000) (931811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124084480 :
    ThetaLowerSegment 124084480 124117248 (3101712158663 / 25000) (387815472062 / 3125) := by
  exact
    packedTile16384 124084480 124117248 12 1742 11139 27 _ _ (931823 / 50000) (1863649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124117248 :
    ThetaLowerSegment 124117248 124150016 (387815472062 / 3125) (1551671197211 / 12500) := by
  exact
    packedTile16384 124117248 124150016 12 1757 11140 27 _ _ (232959 / 12500) (74547 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124150016 :
    ThetaLowerSegment 124150016 124182784 (1551671197211 / 12500) (12416647824229 / 100000) := by
  exact
    packedTile16384 124150016 124182784 12 1759 11142 27 _ _ (1863699 / 100000) (931851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124182784 :
    ThetaLowerSegment 124182784 124215552 (12416647824229 / 100000) (12419991346879 / 100000) := by
  exact
    packedTile16384 124182784 124215552 12 1794 11143 27 _ _ (74549 / 4000) (116483 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124215552 :
    ThetaLowerSegment 124215552 124248320 (12419991346879 / 100000) (12423256638631 / 100000) := by
  exact
    packedTile16384 124215552 124248320 12 1752 11145 27 _ _ (1863751 / 100000) (931877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124248320 :
    ThetaLowerSegment 124248320 124281088 (12423256638631 / 100000) (12426630076811 / 100000) := by
  exact
    packedTile16384 124248320 124281088 12 1810 11146 27 _ _ (931889 / 50000) (1863781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124281088 :
    ThetaLowerSegment 124281088 124313856 (12426630076811 / 100000) (12429929009891 / 100000) := by
  exact
    packedTile16384 124281088 124313856 12 1770 11148 27 _ _ (465951 / 25000) (1863807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124313856 :
    ThetaLowerSegment 124313856 124346624 (12429929009891 / 100000) (12433250356733 / 100000) := by
  exact
    packedTile16384 124313856 124346624 12 1782 11149 27 _ _ (1863831 / 100000) (931917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124346624 :
    ThetaLowerSegment 124346624 124379392 (12433250356733 / 100000) (12436433824489 / 100000) := by
  exact
    packedTile16384 124346624 124379392 12 1708 11151 27 _ _ (1863857 / 100000) (93193 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124379392 :
    ThetaLowerSegment 124379392 124412160 (12436433824489 / 100000) (6219871108407 / 50000) := by
  exact
    packedTile16384 124379392 124412160 12 1775 11152 27 _ _ (1863883 / 100000) (931943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124412160 :
    ThetaLowerSegment 124412160 124444928 (6219871108407 / 50000) (6221513213117 / 50000) := by
  exact
    packedTile16384 124412160 124444928 12 1762 11154 27 _ _ (186391 / 10000) (1863913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124444928 :
    ThetaLowerSegment 124444928 124477696 (6221513213117 / 50000) (6223143225149 / 50000) := by
  exact
    packedTile16384 124444928 124477696 12 1749 11155 27 _ _ (58248 / 3125) (1863939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124477696 :
    ThetaLowerSegment 124477696 124510464 (6223143225149 / 50000) (3112390357883 / 25000) := by
  exact
    packedTile16384 124477696 124510464 12 1757 11156 27 _ _ (931981 / 50000) (372793 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124510464 :
    ThetaLowerSegment 124510464 124543232 (3112390357883 / 25000) (1245280850037 / 10000) := by
  exact
    packedTile16384 124510464 124543232 12 1742 11158 27 _ _ (1863989 / 100000) (232999 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124543232 :
    ThetaLowerSegment 124543232 124576000 (1245280850037 / 10000) (2491199566007 / 20000) := by
  exact
    packedTile16384 124543232 124576000 12 1711 11159 27 _ _ (372803 / 20000) (932009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124576000 :
    ThetaLowerSegment 124576000 124608768 (2491199566007 / 20000) (3114827557723 / 25000) := by
  exact
    packedTile16384 124576000 124608768 12 1777 11161 27 _ _ (1864041 / 100000) (466011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124608768 :
    ThetaLowerSegment 124608768 124641536 (3114827557723 / 25000) (12462630134219 / 100000) := by
  exact
    packedTile16384 124608768 124641536 12 1781 11162 27 _ _ (1864067 / 100000) (186407 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124641536 :
    ThetaLowerSegment 124641536 124674304 (12462630134219 / 100000) (12465827055429 / 100000) := by
  exact
    packedTile16384 124641536 124674304 12 1715 11164 27 _ _ (932047 / 50000) (1864097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124674304 :
    ThetaLowerSegment 124674304 124707072 (12465827055429 / 100000) (12469197384389 / 100000) := by
  exact
    packedTile16384 124674304 124707072 12 1808 11165 27 _ _ (46603 / 2500) (1864123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124707072 :
    ThetaLowerSegment 124707072 124739840 (12469197384389 / 100000) (12472439134283 / 100000) := by
  exact
    packedTile16384 124707072 124739840 12 1739 11167 27 _ _ (932073 / 50000) (1864149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124739840 :
    ThetaLowerSegment 124739840 124772608 (12472439134283 / 100000) (2495152963783 / 20000) := by
  exact
    packedTile16384 124739840 124772608 12 1784 11168 27 _ _ (1864173 / 100000) (116511 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124772608 :
    ThetaLowerSegment 124772608 124805376 (2495152963783 / 20000) (6239512651483 / 50000) := by
  exact
    packedTile16384 124772608 124805376 12 1749 11170 27 _ _ (1864199 / 100000) (932101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124805376 :
    ThetaLowerSegment 124805376 124838144 (6239512651483 / 50000) (12482233634191 / 100000) := by
  exact
    packedTile16384 124805376 124838144 12 1721 11171 27 _ _ (74569 / 4000) (466057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124838144 :
    ThetaLowerSegment 124838144 124870912 (12482233634191 / 100000) (6242762018603 / 50000) := by
  exact
    packedTile16384 124838144 124870912 12 1765 11173 27 _ _ (1864251 / 100000) (932127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124870912 :
    ThetaLowerSegment 124870912 124903680 (6242762018603 / 50000) (6244417497467 / 50000) := by
  exact
    packedTile16384 124870912 124903680 12 1776 11174 27 _ _ (932139 / 50000) (1864281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124903680 :
    ThetaLowerSegment 124903680 124936448 (6244417497467 / 50000) (6246055288531 / 50000) := by
  exact
    packedTile16384 124903680 124936448 12 1757 11176 27 _ _ (116519 / 6250) (1864307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124936448 :
    ThetaLowerSegment 124936448 124969216 (6246055288531 / 50000) (6247701491921 / 50000) := by
  exact
    packedTile16384 124936448 124969216 12 1766 11177 27 _ _ (186433 / 10000) (1864333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell124969216 :
    ThetaLowerSegment 124969216 125001984 (6247701491921 / 50000) (1249868052169 / 10000) := by
  exact
    packedTile16384 124969216 125001984 12 1758 11178 27 _ _ (466089 / 25000) (1864359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125001984 :
    ThetaLowerSegment 125001984 125034752 (1249868052169 / 10000) (3125482069219 / 25000) := by
  exact
    packedTile16384 125001984 125034752 12 1742 11180 27 _ _ (1864383 / 100000) (932193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125034752 :
    ThetaLowerSegment 125034752 125067520 (3125482069219 / 25000) (12505226416397 / 100000) := by
  exact
    packedTile16384 125034752 125067520 12 1769 11181 27 _ _ (1864409 / 100000) (466103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125067520 :
    ThetaLowerSegment 125067520 125100288 (12505226416397 / 100000) (6254241792171 / 50000) := by
  exact
    packedTile16384 125067520 125100288 12 1747 11183 27 _ _ (372887 / 20000) (932219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125100288 :
    ThetaLowerSegment 125100288 125133056 (6254241792171 / 50000) (3127932868851 / 25000) := by
  exact
    packedTile16384 125100288 125133056 12 1742 11184 27 _ _ (1864461 / 100000) (116529 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125133056 :
    ThetaLowerSegment 125133056 125165824 (3127932868851 / 25000) (3128742056209 / 25000) := by
  exact
    packedTile16384 125133056 125165824 12 1736 11186 27 _ _ (1864487 / 100000) (186449 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125165824 :
    ThetaLowerSegment 125165824 125198592 (3128742056209 / 25000) (6259148191163 / 50000) := by
  exact
    packedTile16384 125165824 125198592 12 1785 11187 27 _ _ (932257 / 50000) (1864517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125198592 :
    ThetaLowerSegment 125198592 125231360 (6259148191163 / 50000) (6260816022193 / 50000) := by
  exact
    packedTile16384 125198592 125231360 12 1789 11189 27 _ _ (93227 / 5000) (1864543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125231360 :
    ThetaLowerSegment 125231360 125264128 (6260816022193 / 50000) (6262453111141 / 50000) := by
  exact
    packedTile16384 125231360 125264128 12 1756 11190 27 _ _ (932283 / 50000) (1864569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125264128 :
    ThetaLowerSegment 125264128 125296896 (6262453111141 / 50000) (6264110733429 / 50000) := by
  exact
    packedTile16384 125264128 125296896 12 1778 11192 27 _ _ (116537 / 6250) (372919 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125296896 :
    ThetaLowerSegment 125296896 125329664 (6264110733429 / 50000) (1566434869313 / 12500) := by
  exact
    packedTile16384 125296896 125329664 12 1747 11193 27 _ _ (932309 / 50000) (1864621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125329664 :
    ThetaLowerSegment 125329664 125362432 (1566434869313 / 12500) (313368272341 / 2500) := by
  exact
    packedTile16384 125329664 125362432 12 1744 11195 27 _ _ (466161 / 25000) (1864647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125362432 :
    ThetaLowerSegment 125362432 125395200 (313368272341 / 2500) (626902686779 / 5000) := by
  exact
    packedTile16384 125362432 125395200 12 1782 11196 27 _ _ (186467 / 10000) (1864673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125395200 :
    ThetaLowerSegment 125395200 125427968 (626902686779 / 5000) (12541333737603 / 100000) := by
  exact
    packedTile16384 125395200 125427968 12 1759 11197 27 _ _ (1864697 / 100000) (18647 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125427968 :
    ThetaLowerSegment 125427968 125460736 (12541333737603 / 100000) (12544555978947 / 100000) := by
  exact
    packedTile16384 125427968 125460736 12 1728 11199 27 _ _ (1864723 / 100000) (932363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125460736 :
    ThetaLowerSegment 125460736 125493504 (12544555978947 / 100000) (501914412567 / 4000) := by
  exact
    packedTile16384 125460736 125493504 12 1772 11200 27 _ _ (1864749 / 100000) (116547 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125493504 :
    ThetaLowerSegment 125493504 125526272 (501914412567 / 4000) (251023032841 / 2000) := by
  exact
    packedTile16384 125493504 125526272 12 1765 11202 27 _ _ (74591 / 4000) (932389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125526272 :
    ThetaLowerSegment 125526272 125559040 (251023032841 / 2000) (12554342316561 / 100000) := by
  exact
    packedTile16384 125526272 125559040 12 1711 11203 27 _ _ (1864801 / 100000) (466201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125559040 :
    ThetaLowerSegment 125559040 125591808 (12554342316561 / 100000) (12557549819001 / 100000) := by
  exact
    packedTile16384 125559040 125591808 12 1720 11205 27 _ _ (1864827 / 100000) (186483 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125591808 :
    ThetaLowerSegment 125591808 125624576 (12557549819001 / 100000) (12560854338517 / 100000) := by
  exact
    packedTile16384 125591808 125624576 12 1772 11206 27 _ _ (1864853 / 100000) (233107 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125624576 :
    ThetaLowerSegment 125624576 125657344 (12560854338517 / 100000) (3141030867851 / 25000) := by
  exact
    packedTile16384 125624576 125657344 12 1753 11208 27 _ _ (1864879 / 100000) (932441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125657344 :
    ThetaLowerSegment 125657344 125690112 (3141030867851 / 25000) (12567396379679 / 100000) := by
  exact
    packedTile16384 125657344 125690112 12 1755 11209 27 _ _ (372981 / 20000) (466227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125690112 :
    ThetaLowerSegment 125690112 125722880 (12567396379679 / 100000) (12570729013163 / 100000) := by
  exact
    packedTile16384 125690112 125722880 12 1787 11211 27 _ _ (466233 / 25000) (372987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125722880 :
    ThetaLowerSegment 125722880 125755648 (12570729013163 / 100000) (12573998284537 / 100000) := by
  exact
    packedTile16384 125722880 125755648 12 1753 11212 27 _ _ (932479 / 50000) (1864961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125755648 :
    ThetaLowerSegment 125755648 125788416 (12573998284537 / 100000) (12577308631137 / 100000) := by
  exact
    packedTile16384 125755648 125788416 12 1775 11214 27 _ _ (233123 / 12500) (1864987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125788416 :
    ThetaLowerSegment 125788416 125821184 (12577308631137 / 100000) (12580667514147 / 100000) := by
  exact
    packedTile16384 125788416 125821184 12 1801 11215 27 _ _ (186501 / 10000) (1865013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125821184 :
    ThetaLowerSegment 125821184 125853952 (12580667514147 / 100000) (2516778059271 / 20000) := by
  exact
    packedTile16384 125821184 125853952 12 1728 11217 27 _ _ (466259 / 25000) (1865039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125853952 :
    ThetaLowerSegment 125853952 125886720 (2516778059271 / 20000) (12587169075351 / 100000) := by
  exact
    packedTile16384 125853952 125886720 12 1758 11218 27 _ _ (932531 / 50000) (373013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125886720 :
    ThetaLowerSegment 125886720 125919488 (12587169075351 / 100000) (12590500122519 / 100000) := by
  exact
    packedTile16384 125886720 125919488 12 1786 11219 27 _ _ (58284 / 3125) (1865091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125919488 :
    ThetaLowerSegment 125919488 125952256 (12590500122519 / 100000) (2518748711153 / 20000) := by
  exact
    packedTile16384 125919488 125952256 12 1739 11221 27 _ _ (932557 / 50000) (1865117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125952256 :
    ThetaLowerSegment 125952256 125985024 (2518748711153 / 20000) (2519420907609 / 20000) := by
  exact
    packedTile16384 125952256 125985024 12 1802 11222 27 _ _ (93257 / 5000) (1865143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell125985024 :
    ThetaLowerSegment 125985024 126017792 (2519420907609 / 20000) (12600372308877 / 100000) := by
  exact
    packedTile16384 125985024 126017792 12 1752 11224 27 _ _ (932583 / 50000) (1865169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126017792 :
    ThetaLowerSegment 126017792 126050560 (12600372308877 / 100000) (12603666237949 / 100000) := by
  exact
    packedTile16384 126017792 126050560 12 1766 11225 27 _ _ (233149 / 12500) (373039 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126050560 :
    ThetaLowerSegment 126050560 126083328 (12603666237949 / 100000) (12606928504231 / 100000) := by
  exact
    packedTile16384 126050560 126083328 12 1749 11227 27 _ _ (932609 / 50000) (1865221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126083328 :
    ThetaLowerSegment 126083328 126116096 (12606928504231 / 100000) (12610237447087 / 100000) := by
  exact
    packedTile16384 126083328 126116096 12 1774 11228 27 _ _ (466311 / 25000) (1865247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126116096 :
    ThetaLowerSegment 126116096 126148864 (12610237447087 / 100000) (12613496073777 / 100000) := by
  exact
    packedTile16384 126116096 126148864 12 1747 11230 27 _ _ (186527 / 10000) (1865273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126148864 :
    ThetaLowerSegment 126148864 126181632 (12613496073777 / 100000) (4037371069 / 32) := by
  exact
    packedTile16384 126148864 126181632 12 1763 11231 27 _ _ (116581 / 6250) (1865299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126181632 :
    ThetaLowerSegment 126181632 126214400 (4037371069 / 32) (12620097402497 / 100000) := by
  exact
    packedTile16384 126181632 126214400 12 1776 11233 27 _ _ (932661 / 50000) (74613 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126214400 :
    ThetaLowerSegment 126214400 126247168 (12620097402497 / 100000) (2524670860021 / 20000) := by
  exact
    packedTile16384 126214400 126247168 12 1746 11234 27 _ _ (466337 / 25000) (1865351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126247168 :
    ThetaLowerSegment 126247168 126279936 (2524670860021 / 20000) (12626635492971 / 100000) := by
  exact
    packedTile16384 126247168 126279936 12 1759 11235 27 _ _ (932687 / 50000) (1865377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126279936 :
    ThetaLowerSegment 126279936 126312704 (12626635492971 / 100000) (12629918596971 / 100000) := by
  exact
    packedTile16384 126279936 126312704 12 1760 11237 27 _ _ (9327 / 500) (1865403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126312704 :
    ThetaLowerSegment 126312704 126345472 (12629918596971 / 100000) (12633184957897 / 100000) := by
  exact
    packedTile16384 126312704 126345472 12 1751 11238 27 _ _ (932713 / 50000) (1865429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126345472 :
    ThetaLowerSegment 126345472 126378240 (12633184957897 / 100000) (12636443902541 / 100000) := by
  exact
    packedTile16384 126345472 126378240 12 1747 11240 27 _ _ (466363 / 25000) (373091 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126378240 :
    ThetaLowerSegment 126378240 126411008 (12636443902541 / 100000) (2527949905557 / 20000) := by
  exact
    packedTile16384 126378240 126411008 12 1772 11241 27 _ _ (1865477 / 100000) (46637 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126411008 :
    ThetaLowerSegment 126411008 126443776 (2527949905557 / 20000) (12643025351053 / 100000) := by
  exact
    packedTile16384 126411008 126443776 12 1756 11243 27 _ _ (1865503 / 100000) (932753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126443776 :
    ThetaLowerSegment 126443776 126476544 (12643025351053 / 100000) (316157856967 / 2500) := by
  exact
    packedTile16384 126443776 126476544 12 1763 11244 27 _ _ (1865529 / 100000) (466383 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126476544 :
    ThetaLowerSegment 126476544 126509312 (316157856967 / 2500) (126496051177 / 1000) := by
  exact
    packedTile16384 126476544 126509312 12 1764 11246 27 _ _ (373111 / 20000) (932779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126509312 :
    ThetaLowerSegment 126509312 126542080 (126496051177 / 1000) (12652797126791 / 100000) := by
  exact
    packedTile16384 126509312 126542080 12 1711 11247 27 _ _ (1865581 / 100000) (116599 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126542080 :
    ThetaLowerSegment 126542080 126574848 (12652797126791 / 100000) (12656129100893 / 100000) := by
  exact
    packedTile16384 126542080 126574848 12 1786 11249 27 _ _ (1865607 / 100000) (186561 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126574848 :
    ThetaLowerSegment 126574848 126607616 (12656129100893 / 100000) (12659453658899 / 100000) := by
  exact
    packedTile16384 126574848 126607616 12 1782 11250 27 _ _ (1865633 / 100000) (466409 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126607616 :
    ThetaLowerSegment 126607616 126640384 (12659453658899 / 100000) (12662733487421 / 100000) := by
  exact
    packedTile16384 126607616 126640384 12 1758 11252 27 _ _ (1865659 / 100000) (932831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126640384 :
    ThetaLowerSegment 126640384 126673152 (12662733487421 / 100000) (12665994704801 / 100000) := by
  exact
    packedTile16384 126640384 126673152 12 1748 11253 27 _ _ (373137 / 20000) (233211 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126673152 :
    ThetaLowerSegment 126673152 126705920 (12665994704801 / 100000) (316732378689 / 2500) := by
  exact
    packedTile16384 126673152 126705920 12 1769 11254 27 _ _ (1865711 / 100000) (932857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126705920 :
    ThetaLowerSegment 126705920 126738688 (316732378689 / 2500) (1584061627383 / 12500) := by
  exact
    packedTile16384 126705920 126738688 12 1714 11256 27 _ _ (233217 / 12500) (1865739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126738688 :
    ThetaLowerSegment 126738688 126771456 (1584061627383 / 12500) (6337913567879 / 50000) := by
  exact
    packedTile16384 126738688 126771456 12 1787 11257 27 _ _ (932881 / 50000) (373153 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126771456 :
    ThetaLowerSegment 126771456 126804224 (6337913567879 / 50000) (6339533071863 / 50000) := by
  exact
    packedTile16384 126771456 126804224 12 1736 11259 27 _ _ (466447 / 25000) (1865791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126804224 :
    ThetaLowerSegment 126804224 126836992 (6339533071863 / 50000) (3170582363103 / 25000) := by
  exact
    packedTile16384 126804224 126836992 12 1749 11260 27 _ _ (932907 / 50000) (1865817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126836992 :
    ThetaLowerSegment 126836992 126869760 (3170582363103 / 25000) (3171395869343 / 25000) := by
  exact
    packedTile16384 126836992 126869760 12 1744 11262 27 _ _ (23323 / 1250) (1865843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126869760 :
    ThetaLowerSegment 126869760 126902528 (3171395869343 / 25000) (1586109824591 / 12500) := by
  exact
    packedTile16384 126869760 126902528 12 1766 11263 27 _ _ (932933 / 50000) (1865869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126902528 :
    ThetaLowerSegment 126902528 126935296 (1586109824591 / 12500) (12692056209101 / 100000) := by
  exact
    packedTile16384 126902528 126935296 12 1703 11265 27 _ _ (1865891 / 100000) (932947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126935296 :
    ThetaLowerSegment 126935296 126968064 (12692056209101 / 100000) (12695385005029 / 100000) := by
  exact
    packedTile16384 126935296 126968064 12 1784 11266 27 _ _ (1865917 / 100000) (11662 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell126968064 :
    ThetaLowerSegment 126968064 127000832 (12695385005029 / 100000) (79366646668 / 625) := by
  exact
    packedTile16384 126968064 127000832 12 1757 11268 27 _ _ (1865943 / 100000) (932973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127000832 :
    ThetaLowerSegment 127000832 127033600 (79366646668 / 625) (3175503686801 / 25000) := by
  exact
    packedTile16384 127000832 127033600 12 1796 11269 27 _ _ (1865969 / 100000) (466493 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127033600 :
    ThetaLowerSegment 127033600 127066368 (3175503686801 / 25000) (12705323156339 / 100000) := by
  exact
    packedTile16384 127033600 127066368 12 1773 11270 27 _ _ (373199 / 20000) (932999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127066368 :
    ThetaLowerSegment 127066368 127099136 (12705323156339 / 100000) (6354325135891 / 50000) := by
  exact
    packedTile16384 127066368 127099136 12 1783 11272 27 _ _ (1866021 / 100000) (233253 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127099136 :
    ThetaLowerSegment 127099136 127131904 (6354325135891 / 50000) (6355970988463 / 50000) := by
  exact
    packedTile16384 127099136 127131904 12 1764 11273 27 _ _ (933023 / 50000) (1866049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127131904 :
    ThetaLowerSegment 127131904 127164672 (6355970988463 / 50000) (6357590738959 / 50000) := by
  exact
    packedTile16384 127131904 127164672 12 1736 11275 27 _ _ (233259 / 12500) (74643 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127164672 :
    ThetaLowerSegment 127164672 127197440 (6357590738959 / 50000) (3179612253879 / 25000) := by
  exact
    packedTile16384 127164672 127197440 12 1751 11276 27 _ _ (933049 / 50000) (1866101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127197440 :
    ThetaLowerSegment 127197440 127230208 (3179612253879 / 25000) (1590210376051 / 12500) := by
  exact
    packedTile16384 127197440 127230208 12 1733 11278 27 _ _ (466531 / 25000) (1866127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127230208 :
    ThetaLowerSegment 127230208 127262976 (1590210376051 / 12500) (3181232526917 / 25000) := by
  exact
    packedTile16384 127230208 127262976 12 1740 11279 27 _ _ (1866149 / 100000) (233269 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127262976 :
    ThetaLowerSegment 127262976 127295744 (3181232526917 / 25000) (12728190315393 / 100000) := by
  exact
    packedTile16384 127262976 127295744 12 1747 11281 27 _ _ (74647 / 4000) (933089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127295744 :
    ThetaLowerSegment 127295744 127328512 (12728190315393 / 100000) (12731433772731 / 100000) := by
  exact
    packedTile16384 127295744 127328512 12 1738 11282 27 _ _ (1866201 / 100000) (466551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127328512 :
    ThetaLowerSegment 127328512 127361280 (12731433772731 / 100000) (12734695937527 / 100000) := by
  exact
    packedTile16384 127328512 127361280 12 1748 11283 27 _ _ (1866227 / 100000) (186623 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127361280 :
    ThetaLowerSegment 127361280 127394048 (12734695937527 / 100000) (12737945082259 / 100000) := by
  exact
    packedTile16384 127361280 127394048 12 1741 11285 27 _ _ (466563 / 25000) (373251 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127394048 :
    ThetaLowerSegment 127394048 127426816 (12737945082259 / 100000) (12741239062929 / 100000) := by
  exact
    packedTile16384 127394048 127426816 12 1765 11286 27 _ _ (933139 / 50000) (1866281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127426816 :
    ThetaLowerSegment 127426816 127459584 (12741239062929 / 100000) (12744564816657 / 100000) := by
  exact
    packedTile16384 127426816 127459584 12 1782 11288 27 _ _ (58322 / 3125) (1866307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127459584 :
    ThetaLowerSegment 127459584 127492352 (12744564816657 / 100000) (6373933176329 / 50000) := by
  exact
    packedTile16384 127459584 127492352 12 1769 11289 27 _ _ (1866329 / 100000) (466583 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127492352 :
    ThetaLowerSegment 127492352 127525120 (6373933176329 / 50000) (1593894358771 / 12500) := by
  exact
    packedTile16384 127492352 127525120 12 1762 11291 27 _ _ (373271 / 20000) (933179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127525120 :
    ThetaLowerSegment 127525120 127557888 (1593894358771 / 12500) (159430309621 / 1250) := by
  exact
    packedTile16384 127525120 127557888 12 1752 11292 27 _ _ (1866381 / 100000) (116649 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127557888 :
    ThetaLowerSegment 127557888 127590656 (159430309621 / 1250) (398677493234 / 3125) := by
  exact
    packedTile16384 127557888 127590656 12 1744 11294 27 _ _ (1866407 / 100000) (186641 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127590656 :
    ThetaLowerSegment 127590656 127623424 (398677493234 / 3125) (398778688844 / 3125) := by
  exact
    packedTile16384 127590656 127623424 12 1735 11295 27 _ _ (58326 / 3125) (373287 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127623424 :
    ThetaLowerSegment 127623424 127656192 (398778688844 / 3125) (159551231093 / 1250) := by
  exact
    packedTile16384 127623424 127656192 12 1704 11297 27 _ _ (933229 / 50000) (1866461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127656192 :
    ThetaLowerSegment 127656192 127688960 (159551231093 / 1250) (1595927136999 / 12500) := by
  exact
    packedTile16384 127656192 127688960 12 1778 11298 27 _ _ (466621 / 25000) (1866487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127688960 :
    ThetaLowerSegment 127688960 127721728 (1595927136999 / 12500) (2554146776497 / 20000) := by
  exact
    packedTile16384 127688960 127721728 12 1777 11299 27 _ _ (1866509 / 100000) (116657 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127721728 :
    ThetaLowerSegment 127721728 127754496 (2554146776497 / 20000) (510961804623 / 4000) := by
  exact
    packedTile16384 127721728 127754496 12 1774 11301 27 _ _ (373307 / 20000) (933269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127754496 :
    ThetaLowerSegment 127754496 127787264 (510961804623 / 4000) (12777296664837 / 100000) := by
  exact
    packedTile16384 127754496 127787264 12 1742 11302 27 _ _ (1866561 / 100000) (466641 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127787264 :
    ThetaLowerSegment 127787264 127820032 (12777296664837 / 100000) (12780583722783 / 100000) := by
  exact
    packedTile16384 127787264 127820032 12 1761 11304 27 _ _ (933293 / 50000) (1866589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127820032 :
    ThetaLowerSegment 127820032 127852800 (12780583722783 / 100000) (12783859626843 / 100000) := by
  exact
    packedTile16384 127820032 127852800 12 1755 11305 27 _ _ (466653 / 25000) (373323 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127852800 :
    ThetaLowerSegment 127852800 127885568 (12783859626843 / 100000) (2557423008703 / 20000) := by
  exact
    packedTile16384 127852800 127885568 12 1744 11307 27 _ _ (933319 / 50000) (1866641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127885568 :
    ThetaLowerSegment 127885568 127918336 (2557423008703 / 20000) (12790333170527 / 100000) := by
  exact
    packedTile16384 127885568 127918336 12 1724 11308 27 _ _ (1866663 / 100000) (933333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127918336 :
    ThetaLowerSegment 127918336 127951104 (12790333170527 / 100000) (6396819538373 / 50000) := by
  exact
    packedTile16384 127918336 127951104 12 1771 11310 27 _ _ (1866689 / 100000) (466673 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127951104 :
    ThetaLowerSegment 127951104 127983872 (6396819538373 / 50000) (6398493980831 / 50000) := by
  exact
    packedTile16384 127951104 127983872 12 1794 11311 27 _ _ (933357 / 50000) (1866717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell127983872 :
    ThetaLowerSegment 127983872 128016640 (6398493980831 / 50000) (6400156312801 / 50000) := by
  exact
    packedTile16384 127983872 128016640 12 1781 11312 27 _ _ (93337 / 5000) (1866743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128016640 :
    ThetaLowerSegment 128016640 128049408 (6400156312801 / 50000) (6401800933647 / 50000) := by
  exact
    packedTile16384 128016640 128049408 12 1762 11314 27 _ _ (933383 / 50000) (1866769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128049408 :
    ThetaLowerSegment 128049408 128082176 (6401800933647 / 50000) (12806874351917 / 100000) := by
  exact
    packedTile16384 128049408 128082176 12 1753 11315 27 _ _ (1866791 / 100000) (933397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128082176 :
    ThetaLowerSegment 128082176 128114944 (12806874351917 / 100000) (6405110777399 / 50000) := by
  exact
    packedTile16384 128082176 128114944 12 1793 11317 27 _ _ (1866817 / 100000) (93341 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128114944 :
    ThetaLowerSegment 128114944 128147712 (6405110777399 / 50000) (6406710660993 / 50000) := by
  exact
    packedTile16384 128114944 128147712 12 1714 11318 27 _ _ (933421 / 50000) (373369 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128147712 :
    ThetaLowerSegment 128147712 128180480 (6406710660993 / 50000) (6408338569889 / 50000) := by
  exact
    packedTile16384 128147712 128180480 12 1744 11320 27 _ _ (466717 / 25000) (1866871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128180480 :
    ThetaLowerSegment 128180480 128213248 (6408338569889 / 50000) (12819953536993 / 100000) := by
  exact
    packedTile16384 128180480 128213248 12 1755 11321 27 _ _ (1866893 / 100000) (116681 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128213248 :
    ThetaLowerSegment 128213248 128246016 (12819953536993 / 100000) (400726753647 / 3125) := by
  exact
    packedTile16384 128213248 128246016 12 1769 11323 27 _ _ (1866919 / 100000) (933461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128246016 :
    ThetaLowerSegment 128246016 128278784 (400726753647 / 3125) (12826495266279 / 100000) := by
  exact
    packedTile16384 128246016 128278784 12 1735 11324 27 _ _ (373389 / 20000) (466737 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128278784 :
    ThetaLowerSegment 128278784 128311552 (12826495266279 / 100000) (12829719523469 / 100000) := by
  exact
    packedTile16384 128278784 128311552 12 1727 11326 27 _ _ (186697 / 10000) (1866973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128311552 :
    ThetaLowerSegment 128311552 128344320 (12829719523469 / 100000) (2566595859697 / 20000) := by
  exact
    packedTile16384 128311552 128344320 12 1746 11327 27 _ _ (466749 / 25000) (1866999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128344320 :
    ThetaLowerSegment 128344320 128377088 (2566595859697 / 20000) (3209071448169 / 25000) := by
  exact
    packedTile16384 128344320 128377088 12 1771 11328 27 _ _ (1867021 / 100000) (116689 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128377088 :
    ThetaLowerSegment 128377088 128409856 (3209071448169 / 25000) (802471836927 / 6250) := by
  exact
    packedTile16384 128377088 128409856 12 1748 11330 27 _ _ (1867047 / 100000) (37341 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128409856 :
    ThetaLowerSegment 128409856 128442624 (802471836927 / 6250) (802674297547 / 6250) := by
  exact
    packedTile16384 128409856 128442624 12 1735 11331 27 _ _ (58346 / 3125) (74683 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128442624 :
    ThetaLowerSegment 128442624 128475392 (802674297547 / 6250) (1284602070739 / 10000) := by
  exact
    packedTile16384 128442624 128475392 12 1731 11333 27 _ _ (933549 / 50000) (1867101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128475392 :
    ThetaLowerSegment 128475392 128508160 (1284602070739 / 10000) (12849319913731 / 100000) := by
  exact
    packedTile16384 128475392 128508160 12 1767 11334 27 _ _ (1867123 / 100000) (933563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128508160 :
    ThetaLowerSegment 128508160 128540928 (12849319913731 / 100000) (12852639704653 / 100000) := by
  exact
    packedTile16384 128508160 128540928 12 1778 11336 27 _ _ (1867149 / 100000) (116697 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128540928 :
    ThetaLowerSegment 128540928 128573696 (12852639704653 / 100000) (12855985680461 / 100000) := by
  exact
    packedTile16384 128540928 128573696 12 1792 11337 27 _ _ (933587 / 50000) (1867177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128573696 :
    ThetaLowerSegment 128573696 128606464 (12855985680461 / 100000) (12859255147661 / 100000) := by
  exact
    packedTile16384 128573696 128606464 12 1751 11339 27 _ _ (2334 / 125) (1867203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128606464 :
    ThetaLowerSegment 128606464 128639232 (12859255147661 / 100000) (12862563870361 / 100000) := by
  exact
    packedTile16384 128606464 128639232 12 1772 11340 27 _ _ (74689 / 4000) (466807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128639232 :
    ThetaLowerSegment 128639232 128672000 (12862563870361 / 100000) (6432935385941 / 50000) := by
  exact
    packedTile16384 128639232 128672000 12 1771 11341 27 _ _ (1867251 / 100000) (933627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128672000 :
    ThetaLowerSegment 128672000 128704768 (6432935385941 / 50000) (6434559916061 / 50000) := by
  exact
    packedTile16384 128672000 128704768 12 1740 11343 27 _ _ (466819 / 25000) (1867279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128704768 :
    ThetaLowerSegment 128704768 128737536 (6434559916061 / 50000) (6436229284049 / 50000) := by
  exact
    packedTile16384 128704768 128737536 12 1788 11344 27 _ _ (933651 / 50000) (373461 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128737536 :
    ThetaLowerSegment 128737536 128770304 (6436229284049 / 50000) (257515498817 / 2000) := by
  exact
    packedTile16384 128737536 128770304 12 1776 11346 27 _ _ (1867327 / 100000) (186733 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128770304 :
    ThetaLowerSegment 128770304 128803072 (257515498817 / 2000) (6439553149301 / 50000) := by
  exact
    packedTile16384 128770304 128803072 12 1784 11347 27 _ _ (1867353 / 100000) (466839 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128803072 :
    ThetaLowerSegment 128803072 128835840 (6439553149301 / 50000) (1288236674059 / 10000) := by
  exact
    packedTile16384 128803072 128835840 12 1746 11349 27 _ _ (933689 / 50000) (1867381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128835840 :
    ThetaLowerSegment 128835840 128868608 (1288236674059 / 10000) (2577147480601 / 20000) := by
  exact
    packedTile16384 128835840 128868608 12 1805 11350 27 _ _ (1867403 / 100000) (933703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128868608 :
    ThetaLowerSegment 128868608 128901376 (2577147480601 / 20000) (1611120306611 / 12500) := by
  exact
    packedTile16384 128868608 128901376 12 1727 11352 27 _ _ (1867429 / 100000) (233429 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell128901376 :
    ThetaLowerSegment 128901376 128917760 (1611120306611 / 12500) (1611321991643 / 12500) := by
  exact
    packedTile16384 128901376 128917760 11 864 11353 27 _ _ (933727 / 50000) (1867457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_107667712_128917760 :
    ThetaLowerSegment 107667712 128917760 (10765696272917 / 100000) (1611321991643 / 12500) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell107667712 cell107700480)
                      (ThetaLowerSegment.join cell107733248 cell107766016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell107798784 cell107831552)
                      (ThetaLowerSegment.join cell107864320 cell107897088)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell107929856 cell107962624)
                      (ThetaLowerSegment.join cell107995392 cell108028160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell108060928 cell108093696)
                      (ThetaLowerSegment.join cell108126464 cell108159232))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell108192000 cell108224768)
                      (ThetaLowerSegment.join cell108257536 cell108290304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell108323072 cell108355840)
                      (ThetaLowerSegment.join cell108388608 cell108421376)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell108454144 cell108486912)
                      (ThetaLowerSegment.join cell108519680 cell108552448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell108585216 cell108617984)
                      (ThetaLowerSegment.join cell108650752 cell108683520)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell108716288 cell108749056)
                      (ThetaLowerSegment.join cell108781824 cell108814592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell108847360 cell108880128)
                      (ThetaLowerSegment.join cell108912896 cell108945664)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell108978432 cell109011200)
                      (ThetaLowerSegment.join cell109043968 cell109076736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell109109504 cell109142272)
                      (ThetaLowerSegment.join cell109175040 cell109207808))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell109240576 cell109273344)
                      (ThetaLowerSegment.join cell109306112 cell109338880))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell109371648 cell109404416)
                      (ThetaLowerSegment.join cell109437184 cell109469952)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell109502720 cell109535488)
                      (ThetaLowerSegment.join cell109568256 cell109601024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell109633792 cell109666560)
                      (ThetaLowerSegment.join cell109699328 cell109732096))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell109764864 cell109797632)
                      (ThetaLowerSegment.join cell109830400 cell109863168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell109895936 cell109928704)
                      (ThetaLowerSegment.join cell109961472 cell109994240)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell110027008 cell110059776)
                      (ThetaLowerSegment.join cell110092544 cell110125312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell110158080 cell110190848)
                      (ThetaLowerSegment.join cell110223616 cell110256384))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell110289152 cell110321920)
                      (ThetaLowerSegment.join cell110354688 cell110387456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell110420224 cell110452992)
                      (ThetaLowerSegment.join cell110485760 cell110518528)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell110551296 cell110584064)
                      (ThetaLowerSegment.join cell110616832 cell110649600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell110682368 cell110715136)
                      (ThetaLowerSegment.join cell110747904 cell110780672)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell110813440 cell110846208)
                      (ThetaLowerSegment.join cell110878976 cell110911744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell110944512 cell110977280)
                      (ThetaLowerSegment.join cell111010048 cell111042816)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell111075584 cell111108352)
                      (ThetaLowerSegment.join cell111141120 cell111173888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell111206656 cell111239424)
                      (ThetaLowerSegment.join cell111272192 cell111304960))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell111337728 cell111370496)
                      (ThetaLowerSegment.join cell111403264 cell111436032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell111468800 cell111501568)
                      (ThetaLowerSegment.join cell111534336 cell111567104)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell111599872 cell111632640)
                      (ThetaLowerSegment.join cell111665408 cell111698176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell111730944 cell111763712)
                      (ThetaLowerSegment.join cell111796480 cell111829248)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell111862016 cell111894784)
                      (ThetaLowerSegment.join cell111927552 cell111960320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell111993088 cell112025856)
                      (ThetaLowerSegment.join cell112058624 cell112091392)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell112124160 cell112156928)
                      (ThetaLowerSegment.join cell112189696 cell112222464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell112255232 cell112288000)
                      (ThetaLowerSegment.join cell112320768 cell112353536))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell112386304 cell112419072)
                      (ThetaLowerSegment.join cell112451840 cell112484608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell112517376 cell112550144)
                      (ThetaLowerSegment.join cell112582912 cell112615680)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell112648448 cell112681216)
                      (ThetaLowerSegment.join cell112713984 cell112746752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell112779520 cell112812288)
                      (ThetaLowerSegment.join cell112845056 cell112877824)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell112910592 cell112943360)
                      (ThetaLowerSegment.join cell112976128 cell113008896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell113041664 cell113074432)
                      (ThetaLowerSegment.join cell113107200 cell113139968)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell113172736 cell113205504)
                      (ThetaLowerSegment.join cell113238272 cell113271040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell113303808 cell113336576)
                      (ThetaLowerSegment.join cell113369344 cell113402112))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell113434880 cell113467648)
                      (ThetaLowerSegment.join cell113500416 cell113533184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell113565952 cell113598720)
                      (ThetaLowerSegment.join cell113631488 cell113664256)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell113697024 cell113729792)
                      (ThetaLowerSegment.join cell113762560 cell113795328))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell113828096 cell113860864)
                      (ThetaLowerSegment.join cell113893632 cell113926400))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell113959168 cell113991936)
                      (ThetaLowerSegment.join cell114024704 cell114057472))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell114090240 cell114123008)
                      (ThetaLowerSegment.join cell114155776 cell114188544)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell114221312 cell114254080)
                      (ThetaLowerSegment.join cell114286848 cell114319616))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell114352384 cell114385152)
                      (ThetaLowerSegment.join cell114417920 cell114450688))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell114483456 cell114516224)
                      (ThetaLowerSegment.join cell114548992 cell114581760))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell114614528 cell114647296)
                      (ThetaLowerSegment.join cell114680064 cell114712832)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell114745600 cell114778368)
                      (ThetaLowerSegment.join cell114811136 cell114843904))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell114876672 cell114909440)
                      (ThetaLowerSegment.join cell114942208 cell114974976)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell115007744 cell115040512)
                      (ThetaLowerSegment.join cell115073280 cell115106048))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell115138816 cell115171584)
                      (ThetaLowerSegment.join cell115204352 cell115237120)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell115269888 cell115302656)
                      (ThetaLowerSegment.join cell115335424 cell115368192))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell115400960 cell115433728)
                      (ThetaLowerSegment.join cell115466496 cell115499264))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell115532032 cell115564800)
                      (ThetaLowerSegment.join cell115597568 cell115630336))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell115663104 cell115695872)
                      (ThetaLowerSegment.join cell115728640 cell115761408)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell115794176 cell115826944)
                      (ThetaLowerSegment.join cell115859712 cell115892480))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell115925248 cell115958016)
                      (ThetaLowerSegment.join cell115990784 cell116023552))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell116056320 cell116089088)
                      (ThetaLowerSegment.join cell116121856 cell116154624))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell116187392 cell116220160)
                      (ThetaLowerSegment.join cell116252928 cell116285696)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell116318464 cell116351232)
                      (ThetaLowerSegment.join cell116384000 cell116416768))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell116449536 cell116482304)
                      (ThetaLowerSegment.join cell116515072 cell116547840))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell116580608 cell116613376)
                      (ThetaLowerSegment.join cell116646144 cell116678912))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell116711680 cell116744448)
                      (ThetaLowerSegment.join cell116777216 cell116809984)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell116842752 cell116875520)
                      (ThetaLowerSegment.join cell116908288 cell116941056))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell116973824 cell117006592)
                      (ThetaLowerSegment.join cell117039360 cell117072128)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell117104896 cell117137664)
                      (ThetaLowerSegment.join cell117170432 cell117203200))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell117235968 cell117268736)
                      (ThetaLowerSegment.join cell117301504 cell117334272)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell117367040 cell117399808)
                      (ThetaLowerSegment.join cell117432576 cell117465344))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell117498112 cell117530880)
                      (ThetaLowerSegment.join cell117563648 cell117596416))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell117629184 cell117661952)
                      (ThetaLowerSegment.join cell117694720 cell117727488))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell117760256 cell117793024)
                      (ThetaLowerSegment.join cell117825792 cell117858560)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell117891328 cell117924096)
                      (ThetaLowerSegment.join cell117956864 cell117989632))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell118022400 cell118055168)
                      (ThetaLowerSegment.join cell118087936 cell118120704))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell118153472 cell118186240)
                      (ThetaLowerSegment.join cell118219008 cell118251776))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell118284544 cell118317312)
                      (ThetaLowerSegment.join cell118350080 cell118382848)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell118415616 cell118448384)
                      (ThetaLowerSegment.join cell118481152 cell118513920))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell118546688 cell118579456)
                      (ThetaLowerSegment.join cell118612224 cell118644992))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell118677760 cell118710528)
                      (ThetaLowerSegment.join cell118743296 cell118776064))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell118808832 cell118841600)
                      (ThetaLowerSegment.join cell118874368 cell118907136)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell118939904 cell118972672)
                      (ThetaLowerSegment.join cell119005440 cell119038208))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell119070976 cell119103744)
                      (ThetaLowerSegment.join cell119136512 cell119169280)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell119202048 cell119234816)
                      (ThetaLowerSegment.join cell119267584 cell119300352))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell119333120 cell119365888)
                      (ThetaLowerSegment.join cell119398656 cell119431424)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell119464192 cell119496960)
                      (ThetaLowerSegment.join cell119529728 cell119562496))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell119595264 cell119628032)
                      (ThetaLowerSegment.join cell119660800 cell119693568))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell119726336 cell119759104)
                      (ThetaLowerSegment.join cell119791872 cell119824640))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell119857408 cell119890176)
                      (ThetaLowerSegment.join cell119922944 cell119955712)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell119988480 cell120021248)
                      (ThetaLowerSegment.join cell120054016 cell120086784))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell120119552 cell120152320)
                      (ThetaLowerSegment.join cell120185088 cell120217856)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell120250624 cell120283392)
                      (ThetaLowerSegment.join cell120316160 cell120348928))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell120381696 cell120414464)
                      (ThetaLowerSegment.join cell120447232 cell120480000)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell120512768 cell120545536)
                      (ThetaLowerSegment.join cell120578304 cell120611072))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell120643840 cell120676608)
                      (ThetaLowerSegment.join cell120709376 cell120742144))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell120774912 cell120807680)
                      (ThetaLowerSegment.join cell120840448 cell120873216))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell120905984 cell120938752)
                      (ThetaLowerSegment.join cell120971520 cell121004288)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell121037056 cell121069824)
                      (ThetaLowerSegment.join cell121102592 cell121135360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell121168128 cell121200896)
                      (ThetaLowerSegment.join cell121233664 cell121266432)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell121299200 cell121331968)
                      (ThetaLowerSegment.join cell121364736 cell121397504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell121430272 cell121463040)
                      (ThetaLowerSegment.join cell121495808 cell121528576)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell121561344 cell121594112)
                      (ThetaLowerSegment.join cell121626880 cell121659648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell121692416 cell121725184)
                      (ThetaLowerSegment.join cell121757952 cell121790720))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell121823488 cell121856256)
                      (ThetaLowerSegment.join cell121889024 cell121921792))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell121954560 cell121987328)
                      (ThetaLowerSegment.join cell122020096 cell122052864)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell122085632 cell122118400)
                      (ThetaLowerSegment.join cell122151168 cell122183936))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell122216704 cell122249472)
                      (ThetaLowerSegment.join cell122282240 cell122315008))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell122347776 cell122380544)
                      (ThetaLowerSegment.join cell122413312 cell122446080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell122478848 cell122511616)
                      (ThetaLowerSegment.join cell122544384 cell122577152)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell122609920 cell122642688)
                      (ThetaLowerSegment.join cell122675456 cell122708224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell122740992 cell122773760)
                      (ThetaLowerSegment.join cell122806528 cell122839296))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell122872064 cell122904832)
                      (ThetaLowerSegment.join cell122937600 cell122970368))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell123003136 cell123035904)
                      (ThetaLowerSegment.join cell123068672 cell123101440)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell123134208 cell123166976)
                      (ThetaLowerSegment.join cell123199744 cell123232512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell123265280 cell123298048)
                      (ThetaLowerSegment.join cell123330816 cell123363584)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell123396352 cell123429120)
                      (ThetaLowerSegment.join cell123461888 cell123494656))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell123527424 cell123560192)
                      (ThetaLowerSegment.join cell123592960 cell123625728)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell123658496 cell123691264)
                      (ThetaLowerSegment.join cell123724032 cell123756800))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell123789568 cell123822336)
                      (ThetaLowerSegment.join cell123855104 cell123887872))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell123920640 cell123953408)
                      (ThetaLowerSegment.join cell123986176 cell124018944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell124051712 cell124084480)
                      (ThetaLowerSegment.join cell124117248 cell124150016)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell124182784 cell124215552)
                      (ThetaLowerSegment.join cell124248320 cell124281088))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell124313856 cell124346624)
                      (ThetaLowerSegment.join cell124379392 cell124412160)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell124444928 cell124477696)
                    (ThetaLowerSegment.join cell124510464 cell124543232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell124576000 cell124608768)
                    (ThetaLowerSegment.join cell124641536 cell124674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell124707072 cell124739840)
                    (ThetaLowerSegment.join cell124772608 cell124805376))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell124838144 cell124870912)
                    (ThetaLowerSegment.join cell124903680 cell124936448))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell124969216 cell125001984)
                    (ThetaLowerSegment.join cell125034752 cell125067520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell125100288 cell125133056)
                    (ThetaLowerSegment.join cell125165824 cell125198592)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell125231360 cell125264128)
                    (ThetaLowerSegment.join cell125296896 cell125329664))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell125362432 cell125395200)
                    (ThetaLowerSegment.join cell125427968 cell125460736)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell125493504 cell125526272)
                    (ThetaLowerSegment.join cell125559040 cell125591808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell125624576 cell125657344)
                    (ThetaLowerSegment.join cell125690112 cell125722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell125755648 cell125788416)
                    (ThetaLowerSegment.join cell125821184 cell125853952))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell125886720 cell125919488)
                    (ThetaLowerSegment.join cell125952256 cell125985024))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell126017792 cell126050560)
                    (ThetaLowerSegment.join cell126083328 cell126116096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell126148864 cell126181632)
                    (ThetaLowerSegment.join cell126214400 cell126247168)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell126279936 cell126312704)
                    (ThetaLowerSegment.join cell126345472 cell126378240))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell126411008 cell126443776)
                    (ThetaLowerSegment.join cell126476544 cell126509312))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell126542080 cell126574848)
                    (ThetaLowerSegment.join cell126607616 cell126640384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell126673152 cell126705920)
                    (ThetaLowerSegment.join cell126738688 cell126771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell126804224 cell126836992)
                    (ThetaLowerSegment.join cell126869760 cell126902528))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell126935296 cell126968064)
                    (ThetaLowerSegment.join cell127000832 cell127033600))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell127066368 cell127099136)
                    (ThetaLowerSegment.join cell127131904 cell127164672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell127197440 cell127230208)
                    (ThetaLowerSegment.join cell127262976 cell127295744)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell127328512 cell127361280)
                    (ThetaLowerSegment.join cell127394048 cell127426816))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell127459584 cell127492352)
                    (ThetaLowerSegment.join cell127525120 cell127557888)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell127590656 cell127623424)
                    (ThetaLowerSegment.join cell127656192 cell127688960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell127721728 cell127754496)
                    (ThetaLowerSegment.join cell127787264 cell127820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell127852800 cell127885568)
                    (ThetaLowerSegment.join cell127918336 cell127951104))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell127983872 cell128016640)
                    (ThetaLowerSegment.join cell128049408 cell128082176))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell128114944 cell128147712)
                    (ThetaLowerSegment.join cell128180480 cell128213248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell128246016 cell128278784)
                    (ThetaLowerSegment.join cell128311552 cell128344320)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell128377088 cell128409856)
                    (ThetaLowerSegment.join cell128442624 cell128475392))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell128508160 cell128540928)
                    (ThetaLowerSegment.join cell128573696 cell128606464)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell128639232 cell128672000)
              (ThetaLowerSegment.join cell128704768 cell128737536))
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell128770304 cell128803072)
              (ThetaLowerSegment.join cell128835840 cell128868608)))
          cell128901376)))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
