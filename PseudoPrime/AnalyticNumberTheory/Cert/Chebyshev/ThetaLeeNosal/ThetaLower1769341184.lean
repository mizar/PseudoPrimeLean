/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1769341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1737341184 :
    ThetaLowerSegment 1737341184 1737472256 (43432179839841 / 25000)
      (173742065549517 / 100000) := by
  exact
    packedTile65536 1737341184 1737472256 14 6273 41681 31 _ _ (2127561 / 100000) (531891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1737472256 :
    ThetaLowerSegment 1737472256 1737603328 (173742065549517 / 100000)
      (34751015551081 / 20000) := by
  exact
    packedTile65536 1737472256 1737603328 14 6116 41682 31 _ _ (132973 / 6250) (2127571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1737603328 :
    ThetaLowerSegment 1737603328 1737734400 (34751015551081 / 20000)
      (173768143199621 / 100000) := by
  exact
    packedTile65536 1737603328 1737734400 14 6141 41684 31 _ _ (265947 / 12500) (2127579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1737734400 :
    ThetaLowerSegment 1737734400 1737865472 (173768143199621 / 100000)
      (173781449103703 / 100000) := by
  exact
    packedTile65536 1737734400 1737865472 14 6254 41686 31 _ _ (2127583 / 100000) (1063793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1737865472 :
    ThetaLowerSegment 1737865472 1737996544 (173781449103703 / 100000)
      (173794606126447 / 100000) := by
  exact
    packedTile65536 1737865472 1737996544 14 6184 41687 31 _ _ (2127591 / 100000) (1063797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1737996544 :
    ThetaLowerSegment 1737996544 1738127616 (173794606126447 / 100000)
      (173807752554489 / 100000) := by
  exact
    packedTile65536 1737996544 1738127616 14 6179 41689 31 _ _ (1063799 / 50000) (2127601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1738127616 :
    ThetaLowerSegment 1738127616 1738258688 (173807752554489 / 100000)
      (173820777758421 / 100000) := by
  exact
    packedTile65536 1738127616 1738258688 14 6122 41690 31 _ _ (1063803 / 50000) (2127609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1738258688 :
    ThetaLowerSegment 1738258688 1738389760 (173820777758421 / 100000) (3476676528179 / 2000) := by
  exact
    packedTile65536 1738258688 1738389760 14 6133 41692 31 _ _ (2127613 / 100000) (66488 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1738389760 :
    ThetaLowerSegment 1738389760 1738520832 (3476676528179 / 2000) (34769401404209 / 20000) := by
  exact
    packedTile65536 1738389760 1738520832 14 6195 41694 31 _ _ (2127621 / 100000) (265953 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1738520832 :
    ThetaLowerSegment 1738520832 1738651904 (34769401404209 / 20000) (21732509630749 / 12500) := by
  exact
    packedTile65536 1738520832 1738651904 14 6143 41695 31 _ _ (2127629 / 100000) (132977 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1738651904 :
    ThetaLowerSegment 1738651904 1738782976 (21732509630749 / 12500) (43468282523213 / 25000) := by
  exact
    packedTile65536 1738651904 1738782976 14 6135 41697 31 _ _ (531909 / 25000) (2127639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1738782976 :
    ThetaLowerSegment 1738782976 1738914048 (43468282523213 / 25000) (10867889906721 / 6250) := by
  exact
    packedTile65536 1738782976 1738914048 14 6161 41698 31 _ _ (531911 / 25000) (2127647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1738914048 :
    ThetaLowerSegment 1738914048 1739045120 (10867889906721 / 6250) (173899368241857 / 100000) := by
  exact
    packedTile65536 1738914048 1739045120 14 6171 41700 31 _ _ (2127651 / 100000) (1063827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1739045120 :
    ThetaLowerSegment 1739045120 1739176192 (173899368241857 / 100000)
      (17391248951491 / 10000) := by
  exact
    packedTile65536 1739045120 1739176192 14 6167 41701 31 _ _ (2127659 / 100000) (1063831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1739176192 :
    ThetaLowerSegment 1739176192 1739307264 (17391248951491 / 10000) (86962770309077 / 50000) := by
  exact
    packedTile65536 1739176192 1739307264 14 6134 41703 31 _ _ (1063833 / 50000) (2127669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1739307264 :
    ThetaLowerSegment 1739307264 1739438336 (86962770309077 / 50000) (43484660176743 / 25000) := by
  exact
    packedTile65536 1739307264 1739438336 14 6157 41705 31 _ _ (1063837 / 50000) (2127677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1739438336 :
    ThetaLowerSegment 1739438336 1739569408 (43484660176743 / 25000) (8697592467531 / 5000) := by
  exact
    packedTile65536 1739438336 1739569408 14 6208 41706 31 _ _ (2127681 / 100000) (531921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1739569408 :
    ThetaLowerSegment 1739569408 1739700480 (8697592467531 / 5000) (86982458808229 / 50000) := by
  exact
    packedTile65536 1739569408 1739700480 14 6142 41708 31 _ _ (2127689 / 100000) (531923 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1739700480 :
    ThetaLowerSegment 1739700480 1739831552 (86982458808229 / 50000) (86989027005781 / 50000) := by
  exact
    packedTile65536 1739700480 1739831552 14 6174 41709 31 _ _ (132981 / 6250) (2127699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1739831552 :
    ThetaLowerSegment 1739831552 1739962624 (86989027005781 / 50000) (86995628207441 / 50000) := by
  exact
    packedTile65536 1739831552 1739962624 14 6205 41711 31 _ _ (265963 / 12500) (2127707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1739962624 :
    ThetaLowerSegment 1739962624 1740093696 (86995628207441 / 50000)
      (174004373753197 / 100000) := by
  exact
    packedTile65536 1739962624 1740093696 14 6165 41712 31 _ _ (2127711 / 100000) (1063857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1740093696 :
    ThetaLowerSegment 1740093696 1740224768 (174004373753197 / 100000)
      (43504340869423 / 25000) := by
  exact
    packedTile65536 1740093696 1740224768 14 6105 41714 31 _ _ (2127719 / 100000) (1063861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1740224768 :
    ThetaLowerSegment 1740224768 1740355840 (43504340869423 / 25000) (87015284075727 / 50000) := by
  exact
    packedTile65536 1740224768 1740355840 14 6206 41716 31 _ _ (2127727 / 100000) (212773 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1740355840 :
    ThetaLowerSegment 1740355840 1740486912 (87015284075727 / 50000) (87021839624181 / 50000) := by
  exact
    packedTile65536 1740355840 1740486912 14 6162 41717 31 _ _ (1063867 / 50000) (2127737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1740486912 :
    ThetaLowerSegment 1740486912 1740617984 (87021839624181 / 50000) (10878546606999 / 6250) := by
  exact
    packedTile65536 1740486912 1740617984 14 6141 41719 31 _ _ (1063871 / 50000) (425549 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1740617984 :
    ThetaLowerSegment 1740617984 1740749056 (10878546606999 / 6250) (8703493057841 / 5000) := by
  exact
    packedTile65536 1740617984 1740749056 14 6164 41720 31 _ _ (2127749 / 100000) (265969 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1740749056 :
    ThetaLowerSegment 1740749056 1740880128 (8703493057841 / 5000) (87041447898101 / 50000) := by
  exact
    packedTile65536 1740749056 1740880128 14 6126 41722 31 _ _ (2127757 / 100000) (26597 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1740880128 :
    ThetaLowerSegment 1740880128 1741011200 (87041447898101 / 50000) (87048113118831 / 50000) := by
  exact
    packedTile65536 1740880128 1741011200 14 6265 41723 31 _ _ (531941 / 25000) (2127767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1741011200 :
    ThetaLowerSegment 1741011200 1741142272 (87048113118831 / 50000) (87054694317627 / 50000) := by
  exact
    packedTile65536 1741011200 1741142272 14 6186 41725 31 _ _ (531943 / 25000) (85111 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1741142272 :
    ThetaLowerSegment 1741142272 1741273344 (87054694317627 / 50000)
      (174122489370557 / 100000) := by
  exact
    packedTile65536 1741142272 1741273344 14 6157 41726 31 _ _ (2127779 / 100000) (1063891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1741273344 :
    ThetaLowerSegment 1741273344 1741404416 (174122489370557 / 100000)
      (174135332692889 / 100000) := by
  exact
    packedTile65536 1741273344 1741404416 14 6036 41728 31 _ _ (2127787 / 100000) (212779 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1741404416 :
    ThetaLowerSegment 1741404416 1741535488 (174135332692889 / 100000)
      (174148354792169 / 100000) := by
  exact
    packedTile65536 1741404416 1741535488 14 6120 41730 31 _ _ (1063897 / 50000) (2127797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1741535488 :
    ThetaLowerSegment 1741535488 1741666560 (174148354792169 / 100000)
      (174161434391063 / 100000) := by
  exact
    packedTile65536 1741535488 1741666560 14 6147 41731 31 _ _ (1063901 / 50000) (425561 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1741666560 :
    ThetaLowerSegment 1741666560 1741797632 (174161434391063 / 100000)
      (174174520416413 / 100000) := by
  exact
    packedTile65536 1741666560 1741797632 14 6150 41733 31 _ _ (2127809 / 100000) (531953 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1741797632 :
    ThetaLowerSegment 1741797632 1741928704 (174174520416413 / 100000)
      (87093895805521 / 50000) := by
  exact
    packedTile65536 1741797632 1741928704 14 6237 41734 31 _ _ (2127817 / 100000) (106391 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1741928704 :
    ThetaLowerSegment 1741928704 1742059776 (87093895805521 / 50000) (17420093517989 / 10000) := by
  exact
    packedTile65536 1741928704 1742059776 14 6177 41736 31 _ _ (132989 / 6250) (2127827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1742059776 :
    ThetaLowerSegment 1742059776 1742190848 (17420093517989 / 10000) (87107027696001 / 50000) := by
  exact
    packedTile65536 1742059776 1742190848 14 6166 41737 31 _ _ (265979 / 12500) (425567 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1742190848 :
    ThetaLowerSegment 1742190848 1742321920 (87107027696001 / 50000) (43556832212921 / 25000) := by
  exact
    packedTile65536 1742190848 1742321920 14 6238 41739 31 _ _ (2127839 / 100000) (1063921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1742321920 :
    ThetaLowerSegment 1742321920 1742452992 (43556832212921 / 25000) (696961047623 / 400) := by
  exact
    packedTile65536 1742321920 1742452992 14 6078 41741 31 _ _ (2127847 / 100000) (42557 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1742452992 :
    ThetaLowerSegment 1742452992 1742584064 (696961047623 / 400) (87126720916713 / 50000) := by
  exact
    packedTile65536 1742452992 1742584064 14 6194 41742 31 _ _ (1063927 / 50000) (2127857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1742584064 :
    ThetaLowerSegment 1742584064 1742715136 (87126720916713 / 50000) (87133238558019 / 50000) := by
  exact
    packedTile65536 1742584064 1742715136 14 6126 41744 31 _ _ (1063931 / 50000) (425573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1742715136 :
    ThetaLowerSegment 1742715136 1742846208 (87133238558019 / 50000) (21784937194071 / 12500) := by
  exact
    packedTile65536 1742715136 1742846208 14 6119 41745 31 _ _ (212787 / 10000) (2127873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1742846208 :
    ThetaLowerSegment 1742846208 1742977280 (21784937194071 / 12500) (5446643382871 / 3125) := by
  exact
    packedTile65536 1742846208 1742977280 14 6152 41747 31 _ _ (2127877 / 100000) (53197 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1742977280 :
    ThetaLowerSegment 1742977280 1743108352 (5446643382871 / 3125) (174305910939857 / 100000) := by
  exact
    packedTile65536 1742977280 1743108352 14 6261 41748 31 _ _ (425577 / 20000) (132993 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1743108352 :
    ThetaLowerSegment 1743108352 1743239424 (174305910939857 / 100000)
      (34863794813769 / 20000) := by
  exact
    packedTile65536 1743108352 1743239424 14 6139 41750 31 _ _ (531973 / 25000) (425579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1743239424 :
    ThetaLowerSegment 1743239424 1743370496 (34863794813769 / 20000) (34866416812149 / 20000) := by
  exact
    packedTile65536 1743239424 1743370496 14 6161 41752 31 _ _ (21279 / 1000) (2127903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1743370496 :
    ThetaLowerSegment 1743370496 1743501568 (34866416812149 / 20000) (278952068823 / 160) := by
  exact
    packedTile65536 1743370496 1743501568 14 6090 41753 31 _ _ (2127907 / 100000) (212791 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1743501568 :
    ThetaLowerSegment 1743501568 1743632640 (278952068823 / 160) (34871641259313 / 20000) := by
  exact
    packedTile65536 1743501568 1743632640 14 6186 41755 31 _ _ (425583 / 20000) (1063959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1743632640 :
    ThetaLowerSegment 1743632640 1743763712 (34871641259313 / 20000)
      (174371237690893 / 100000) := by
  exact
    packedTile65536 1743632640 1743763712 14 6124 41756 31 _ _ (1063961 / 50000) (85117 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1743763712 :
    ThetaLowerSegment 1743763712 1743894784 (174371237690893 / 100000)
      (174384522357883 / 100000) := by
  exact
    packedTile65536 1743763712 1743894784 14 6243 41758 31 _ _ (212793 / 10000) (2127933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1743894784 :
    ThetaLowerSegment 1743894784 1744025856 (174384522357883 / 100000)
      (87198831184429 / 50000) := by
  exact
    packedTile65536 1743894784 1744025856 14 6175 41759 31 _ _ (2127937 / 100000) (106397 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1744025856 :
    ThetaLowerSegment 1744025856 1744156928 (87198831184429 / 50000) (87205355463799 / 50000) := by
  exact
    packedTile65536 1744025856 1744156928 14 6132 41761 31 _ _ (425589 / 20000) (531987 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1744156928 :
    ThetaLowerSegment 1744156928 1744288000 (87205355463799 / 50000) (17442392763747 / 10000) := by
  exact
    packedTile65536 1744156928 1744288000 14 6211 41763 31 _ _ (132997 / 6250) (425591 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1744288000 :
    ThetaLowerSegment 1744288000 1744419072 (17442392763747 / 10000) (17443701246351 / 10000) := by
  exact
    packedTile65536 1744288000 1744419072 14 6149 41764 31 _ _ (53199 / 2500) (2127963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1744419072 :
    ThetaLowerSegment 1744419072 1744550144 (17443701246351 / 10000) (43612501457503 / 25000) := by
  exact
    packedTile65536 1744419072 1744550144 14 6106 41766 31 _ _ (2127967 / 100000) (212797 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1744550144 :
    ThetaLowerSegment 1744550144 1744681216 (43612501457503 / 25000) (43615791306853 / 25000) := by
  exact
    packedTile65536 1744550144 1744681216 14 6184 41767 31 _ _ (85119 / 4000) (1063989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1744681216 :
    ThetaLowerSegment 1744681216 1744812288 (43615791306853 / 25000) (87238154886113 / 50000) := by
  exact
    packedTile65536 1744681216 1744812288 14 6177 41769 31 _ _ (1063991 / 50000) (425597 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1744812288 :
    ThetaLowerSegment 1744812288 1744943360 (87238154886113 / 50000) (87244606951793 / 50000) := by
  exact
    packedTile65536 1744812288 1744943360 14 6064 41770 31 _ _ (212799 / 10000) (2127993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1744943360 :
    ThetaLowerSegment 1744943360 1745074432 (87244606951793 / 50000) (87251207998487 / 50000) := by
  exact
    packedTile65536 1744943360 1745074432 14 6204 41772 31 _ _ (2127997 / 100000) (532 / 25)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1745074432 :
    ThetaLowerSegment 1745074432 1745205504 (87251207998487 / 50000) (21814449607493 / 12500) := by
  exact
    packedTile65536 1745074432 1745205504 14 6194 41774 31 _ _ (425601 / 20000) (266001 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1745205504 :
    ThetaLowerSegment 1745205504 1745336576 (21814449607493 / 12500) (10908041694353 / 6250) := by
  exact
    packedTile65536 1745205504 1745336576 14 6142 41775 31 _ _ (532003 / 25000) (425603 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1745336576 :
    ThetaLowerSegment 1745336576 1745467648 (10908041694353 / 6250) (43635483828587 / 25000) := by
  exact
    packedTile65536 1745336576 1745467648 14 6235 41777 31 _ _ (106401 / 5000) (2128023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1745467648 :
    ThetaLowerSegment 1745467648 1745598720 (43635483828587 / 25000) (4363878014241 / 2500) := by
  exact
    packedTile65536 1745467648 1745598720 14 6196 41778 31 _ _ (2128027 / 100000) (212803 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1745598720 :
    ThetaLowerSegment 1745598720 1745729792 (4363878014241 / 2500) (6982732660587 / 4000) := by
  exact
    packedTile65536 1745598720 1745729792 14 6201 41780 31 _ _ (425607 / 20000) (1064019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1745729792 :
    ThetaLowerSegment 1745729792 1745860864 (6982732660587 / 4000) (34916257386133 / 20000) := by
  exact
    packedTile65536 1745729792 1745860864 14 6095 41781 31 _ _ (1064021 / 50000) (425609 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1745860864 :
    ThetaLowerSegment 1745860864 1745991936 (34916257386133 / 20000) (34918865524213 / 20000) := by
  exact
    packedTile65536 1745860864 1745991936 14 6128 41783 31 _ _ (42561 / 2000) (2128053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1745991936 :
    ThetaLowerSegment 1745991936 1746123008 (34918865524213 / 20000) (87303770363489 / 50000) := by
  exact
    packedTile65536 1745991936 1746123008 14 6209 41785 31 _ _ (2128057 / 100000) (106403 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1746123008 :
    ThetaLowerSegment 1746123008 1746254080 (87303770363489 / 50000)
      (174620562356713 / 100000) := by
  exact
    packedTile65536 1746123008 1746254080 14 6119 41786 31 _ _ (425613 / 20000) (532017 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1746254080 :
    ThetaLowerSegment 1746254080 1746385152 (174620562356713 / 100000)
      (174633615950361 / 100000) := by
  exact
    packedTile65536 1746254080 1746385152 14 6134 41788 31 _ _ (266009 / 12500) (85123 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1746385152 :
    ThetaLowerSegment 1746385152 1746516224 (174633615950361 / 100000)
      (174646933475001 / 100000) := by
  exact
    packedTile65536 1746385152 1746516224 14 6258 41789 31 _ _ (26601 / 1250) (2128083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1746516224 :
    ThetaLowerSegment 1746516224 1746647296 (174646933475001 / 100000)
      (43664983489621 / 25000) := by
  exact
    packedTile65536 1746516224 1746647296 14 6109 41791 31 _ _ (2128087 / 100000) (212809 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1746647296 :
    ThetaLowerSegment 1746647296 1746778368 (43664983489621 / 25000)
      (174673113250819 / 100000) := by
  exact
    packedTile65536 1746647296 1746778368 14 6193 41792 31 _ _ (425619 / 20000) (1064049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1746778368 :
    ThetaLowerSegment 1746778368 1746909440 (174673113250819 / 100000) (6987450426599 / 4000) := by
  exact
    packedTile65536 1746778368 1746909440 14 6178 41794 31 _ _ (1064051 / 50000) (425621 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1746909440 :
    ThetaLowerSegment 1746909440 1747040512 (6987450426599 / 4000) (34939848001573 / 20000) := by
  exact
    packedTile65536 1746909440 1747040512 14 6099 41796 31 _ _ (212811 / 10000) (2128113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1747040512 :
    ThetaLowerSegment 1747040512 1747171584 (34939848001573 / 20000) (34942461329249 / 20000) := by
  exact
    packedTile65536 1747040512 1747171584 14 6140 41797 31 _ _ (2128117 / 100000) (53203 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1747171584 :
    ThetaLowerSegment 1747171584 1747302656 (34942461329249 / 20000) (8736271965281 / 5000) := by
  exact
    packedTile65536 1747171584 1747302656 14 6171 41799 31 _ _ (681 / 32) (66504 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1747302656 :
    ThetaLowerSegment 1747302656 1747433728 (8736271965281 / 5000) (43684588202649 / 25000) := by
  exact
    packedTile65536 1747302656 1747433728 14 6068 41800 31 _ _ (532033 / 25000) (425627 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1747433728 :
    ThetaLowerSegment 1747433728 1747564800 (43684588202649 / 25000) (21843928246827 / 12500) := by
  exact
    packedTile65536 1747433728 1747564800 14 6143 41802 31 _ _ (106407 / 5000) (2128143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1747564800 :
    ThetaLowerSegment 1747564800 1747695872 (21843928246827 / 12500) (34952893026257 / 20000) := by
  exact
    packedTile65536 1747564800 1747695872 14 6127 41803 31 _ _ (2128147 / 100000) (42563 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1747695872 :
    ThetaLowerSegment 1747695872 1747826944 (34952893026257 / 20000) (34955521723313 / 20000) := by
  exact
    packedTile65536 1747695872 1747826944 14 6176 41805 31 _ _ (425631 / 20000) (1064079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1747826944 :
    ThetaLowerSegment 1747826944 1747958016 (34955521723313 / 20000)
      (174790769170373 / 100000) := by
  exact
    packedTile65536 1747826944 1747958016 14 6184 41807 31 _ _ (1064081 / 50000) (425633 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1747958016 :
    ThetaLowerSegment 1747958016 1748089088 (174790769170373 / 100000)
      (174803687162273 / 100000) := by
  exact
    packedTile65536 1747958016 1748089088 14 6070 41808 31 _ _ (212817 / 10000) (2128173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1748089088 :
    ThetaLowerSegment 1748089088 1748220160 (174803687162273 / 100000)
      (174816528582291 / 100000) := by
  exact
    packedTile65536 1748089088 1748220160 14 6034 41810 31 _ _ (2128177 / 100000) (106409 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1748220160 :
    ThetaLowerSegment 1748220160 1748351232 (174816528582291 / 100000)
      (87414881882403 / 50000) := by
  exact
    packedTile65536 1748220160 1748351232 14 6219 41811 31 _ _ (425637 / 20000) (532047 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1748351232 :
    ThetaLowerSegment 1748351232 1748482304 (87414881882403 / 50000) (3496857340859 / 2000) := by
  exact
    packedTile65536 1748351232 1748482304 14 6157 41813 31 _ _ (66506 / 3125) (425639 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1748482304 :
    ThetaLowerSegment 1748482304 1748613376 (3496857340859 / 2000) (3497120514071 / 2000) := by
  exact
    packedTile65536 1748482304 1748613376 14 6183 41814 31 _ _ (10641 / 500) (2128203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1748613376 :
    ThetaLowerSegment 1748613376 1748744448 (3497120514071 / 2000) (17486913545867 / 10000) := by
  exact
    packedTile65536 1748613376 1748744448 14 6160 41816 31 _ _ (2128207 / 100000) (212821 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1748744448 :
    ThetaLowerSegment 1748744448 1748875520 (17486913545867 / 10000) (17488219418591 / 10000) := by
  exact
    packedTile65536 1748744448 1748875520 14 6136 41817 31 _ _ (425643 / 20000) (1064109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1748875520 :
    ThetaLowerSegment 1748875520 1749006592 (17488219418591 / 10000) (4372381270697 / 2500) := by
  exact
    packedTile65536 1748875520 1749006592 14 6135 41819 31 _ _ (1064111 / 50000) (85129 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1749006592 :
    ThetaLowerSegment 1749006592 1749137664 (4372381270697 / 2500) (17490857567591 / 10000) := by
  exact
    packedTile65536 1749006592 1749137664 14 6261 41821 31 _ _ (212823 / 10000) (2128233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1749137664 :
    ThetaLowerSegment 1749137664 1749268736 (17490857567591 / 10000) (87460872603233 / 50000) := by
  exact
    packedTile65536 1749137664 1749268736 14 6188 41822 31 _ _ (2128237 / 100000) (26603 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1749268736 :
    ThetaLowerSegment 1749268736 1749399808 (87460872603233 / 50000) (87467350981013 / 50000) := by
  exact
    packedTile65536 1749268736 1749399808 14 6088 41824 31 _ _ (425649 / 20000) (266031 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1749399808 :
    ThetaLowerSegment 1749399808 1749530880 (87467350981013 / 50000) (87473970908859 / 50000) := by
  exact
    packedTile65536 1749399808 1749530880 14 6221 41825 31 _ _ (532063 / 25000) (425651 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1749530880 :
    ThetaLowerSegment 1749530880 1749661952 (87473970908859 / 50000) (87480497218149 / 50000) := by
  exact
    packedTile65536 1749530880 1749661952 14 6133 41827 31 _ _ (106413 / 5000) (2128263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1749661952 :
    ThetaLowerSegment 1749661952 1749793024 (87480497218149 / 50000)
      (174974144998091 / 100000) := by
  exact
    packedTile65536 1749661952 1749793024 14 6179 41828 31 _ _ (2128267 / 100000) (212827 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1749793024 :
    ThetaLowerSegment 1749793024 1749924096 (174974144998091 / 100000)
      (174987344559641 / 100000) := by
  exact
    packedTile65536 1749793024 1749924096 14 6202 41830 31 _ _ (85131 / 4000) (1064139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1749924096 :
    ThetaLowerSegment 1749924096 1750055168 (174987344559641 / 100000)
      (175000412211121 / 100000) := by
  exact
    packedTile65536 1749924096 1750055168 14 6140 41832 31 _ _ (1064141 / 50000) (425657 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1750055168 :
    ThetaLowerSegment 1750055168 1750186240 (175000412211121 / 100000)
      (175013503322911 / 100000) := by
  exact
    packedTile65536 1750055168 1750186240 14 6151 41833 31 _ _ (212829 / 10000) (2128293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1750186240 :
    ThetaLowerSegment 1750186240 1750317312 (175013503322911 / 100000)
      (35005340604181 / 20000) := by
  exact
    packedTile65536 1750186240 1750317312 14 6202 41835 31 _ _ (2128297 / 100000) (21283 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1750317312 :
    ThetaLowerSegment 1750317312 1750448384 (35005340604181 / 20000) (17503979848157 / 10000) := by
  exact
    packedTile65536 1750317312 1750448384 14 6153 41836 31 _ _ (425661 / 20000) (532077 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1750448384 :
    ThetaLowerSegment 1750448384 1750579456 (17503979848157 / 10000) (87526437415249 / 50000) := by
  exact
    packedTile65536 1750448384 1750579456 14 6144 41838 31 _ _ (266039 / 12500) (425663 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1750579456 :
    ThetaLowerSegment 1750579456 1750710528 (87526437415249 / 50000) (87532926662929 / 50000) := by
  exact
    packedTile65536 1750579456 1750710528 14 6098 41839 31 _ _ (13302 / 625) (2128323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1750710528 :
    ThetaLowerSegment 1750710528 1750841600 (87532926662929 / 50000) (35015793189701 / 20000) := by
  exact
    packedTile65536 1750710528 1750841600 14 6161 41841 31 _ _ (2128327 / 100000) (212833 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1750841600 :
    ThetaLowerSegment 1750841600 1750972672 (35015793189701 / 20000) (17509207436377 / 10000) := by
  exact
    packedTile65536 1750841600 1750972672 14 6159 41843 31 _ _ (425667 / 20000) (1064169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1750972672 :
    ThetaLowerSegment 1750972672 1751103744 (17509207436377 / 10000) (87552669095557 / 50000) := by
  exact
    packedTile65536 1750972672 1751103744 14 6232 41844 31 _ _ (1064171 / 50000) (425669 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1751103744 :
    ThetaLowerSegment 1751103744 1751234816 (87552669095557 / 50000) (21889808497783 / 12500) := by
  exact
    packedTile65536 1751103744 1751234816 14 6169 41846 31 _ _ (42567 / 2000) (2128353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1751234816 :
    ThetaLowerSegment 1751234816 1751365888 (21889808497783 / 12500) (87565855309759 / 50000) := by
  exact
    packedTile65536 1751234816 1751365888 14 6222 41847 31 _ _ (2128357 / 100000) (53209 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1751365888 :
    ThetaLowerSegment 1751365888 1751496960 (87565855309759 / 50000)
      (175144793679173 / 100000) := by
  exact
    packedTile65536 1751365888 1751496960 14 6147 41849 31 _ _ (425673 / 20000) (133023 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1751496960 :
    ThetaLowerSegment 1751496960 1751628032 (175144793679173 / 100000) (1401262912093 / 800) := by
  exact
    packedTile65536 1751496960 1751628032 14 6141 41850 31 _ _ (532093 / 25000) (17027 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1751628032 :
    ThetaLowerSegment 1751628032 1751759104 (1401262912093 / 800) (35034191135401 / 20000) := by
  exact
    packedTile65536 1751628032 1751759104 14 6151 41852 31 _ _ (106419 / 5000) (2128383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1751759104 :
    ThetaLowerSegment 1751759104 1751890176 (35034191135401 / 20000)
      (175184032486733 / 100000) := by
  exact
    packedTile65536 1751759104 1751890176 14 6144 41854 31 _ _ (2128387 / 100000) (212839 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1751890176 :
    ThetaLowerSegment 1751890176 1752021248 (175184032486733 / 100000)
      (43799258712947 / 25000) := by
  exact
    packedTile65536 1751890176 1752021248 14 6109 41855 31 _ _ (425679 / 20000) (1064199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1752021248 :
    ThetaLowerSegment 1752021248 1752152320 (43799258712947 / 25000) (17521025435661 / 10000) := by
  exact
    packedTile65536 1752021248 1752152320 14 6211 41857 31 _ _ (1064201 / 50000) (425681 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1752152320 :
    ThetaLowerSegment 1752152320 1752283392 (17521025435661 / 10000) (17522336110539 / 10000) := by
  exact
    packedTile65536 1752152320 1752283392 14 6158 41858 31 _ _ (212841 / 10000) (2128413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1752283392 :
    ThetaLowerSegment 1752283392 1752414464 (17522336110539 / 10000)
      (175236538135037 / 100000) := by
  exact
    packedTile65536 1752283392 1752414464 14 6191 41860 31 _ _ (2128417 / 100000) (106421 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1752414464 :
    ThetaLowerSegment 1752414464 1752545536 (175236538135037 / 100000)
      (87624825680731 / 50000) := by
  exact
    packedTile65536 1752414464 1752545536 14 6161 41861 31 _ _ (85137 / 4000) (532107 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1752545536 :
    ThetaLowerSegment 1752545536 1752676608 (87624825680731 / 50000) (87631319526763 / 50000) := by
  exact
    packedTile65536 1752545536 1752676608 14 6102 41863 31 _ _ (133027 / 6250) (425687 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1752676608 :
    ThetaLowerSegment 1752676608 1752807680 (87631319526763 / 50000) (87637981540833 / 50000) := by
  exact
    packedTile65536 1752676608 1752807680 14 6260 41864 31 _ _ (2128439 / 100000) (1064221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1752807680 :
    ThetaLowerSegment 1752807680 1752938752 (87637981540833 / 50000)
      (175288910424767 / 100000) := by
  exact
    packedTile65536 1752807680 1752938752 14 6083 41866 31 _ _ (2128447 / 100000) (42569 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1752938752 :
    ThetaLowerSegment 1752938752 1753069824 (175288910424767 / 100000)
      (35060377521761 / 20000) := by
  exact
    packedTile65536 1752938752 1753069824 14 6097 41868 31 _ _ (1064227 / 50000) (2128457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1753069824 :
    ThetaLowerSegment 1753069824 1753200896 (35060377521761 / 20000)
      (175315081944743 / 100000) := by
  exact
    packedTile65536 1753069824 1753200896 14 6199 41869 31 _ _ (1064231 / 50000) (425693 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1753200896 :
    ThetaLowerSegment 1753200896 1753331968 (175315081944743 / 100000)
      (175328269938667 / 100000) := by
  exact
    packedTile65536 1753200896 1753331968 14 6196 41871 31 _ _ (2128469 / 100000) (266059 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1753331968 :
    ThetaLowerSegment 1753331968 1753463040 (175328269938667 / 100000)
      (87670664072531 / 50000) := by
  exact
    packedTile65536 1753331968 1753463040 14 6135 41872 31 _ _ (2128477 / 100000) (13303 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1753463040 :
    ThetaLowerSegment 1753463040 1753594112 (87670664072531 / 50000) (87677242152333 / 50000) := by
  exact
    packedTile65536 1753463040 1753594112 14 6181 41874 31 _ _ (532121 / 25000) (2128487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1753594112 :
    ThetaLowerSegment 1753594112 1753725184 (87677242152333 / 50000) (17536755750253 / 10000) := by
  exact
    packedTile65536 1753594112 1753725184 14 6142 41875 31 _ _ (532123 / 25000) (425699 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1753725184 :
    ThetaLowerSegment 1753725184 1753856256 (17536755750253 / 10000) (5480643380419 / 3125) := by
  exact
    packedTile65536 1753725184 1753856256 14 6122 41877 31 _ _ (2128499 / 100000) (1064251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1753856256 :
    ThetaLowerSegment 1753856256 1753987328 (5480643380419 / 3125) (17539366997743 / 10000) := by
  exact
    packedTile65536 1753856256 1753987328 14 6146 41879 31 _ _ (2128507 / 100000) (212851 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1753987328 :
    ThetaLowerSegment 1753987328 1754118400 (17539366997743 / 10000) (43851684231219 / 25000) := by
  exact
    packedTile65536 1753987328 1754118400 14 6139 41880 31 _ _ (1064257 / 50000) (2128517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1754118400 :
    ThetaLowerSegment 1754118400 1754249472 (43851684231219 / 25000) (43854962155099 / 25000) := by
  exact
    packedTile65536 1754118400 1754249472 14 6160 41882 31 _ _ (1064261 / 50000) (85141 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1754249472 :
    ThetaLowerSegment 1754249472 1754380544 (43854962155099 / 25000) (21929101952383 / 12500) := by
  exact
    packedTile65536 1754249472 1754380544 14 6092 41883 31 _ _ (2128529 / 100000) (532133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1754380544 :
    ThetaLowerSegment 1754380544 1754511616 (21929101952383 / 12500)
      (175446116846777 / 100000) := by
  exact
    packedTile65536 1754380544 1754511616 14 6249 41885 31 _ _ (2128537 / 100000) (106427 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1754511616 :
    ThetaLowerSegment 1754511616 1754642688 (175446116846777 / 100000)
      (175459415989689 / 100000) := by
  exact
    packedTile65536 1754511616 1754642688 14 6248 41886 31 _ _ (66517 / 3125) (2128547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1754642688 :
    ThetaLowerSegment 1754642688 1754773760 (175459415989689 / 100000)
      (175472444856481 / 100000) := by
  exact
    packedTile65536 1754642688 1754773760 14 6121 41888 31 _ _ (266069 / 12500) (425711 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1754773760 :
    ThetaLowerSegment 1754773760 1754904832 (175472444856481 / 100000)
      (175485595093983 / 100000) := by
  exact
    packedTile65536 1754773760 1754904832 14 6178 41890 31 _ _ (2128559 / 100000) (1064281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1754904832 :
    ThetaLowerSegment 1754904832 1755035904 (175485595093983 / 100000)
      (175498749638043 / 100000) := by
  exact
    packedTile65536 1754904832 1755035904 14 6180 41891 31 _ _ (2128567 / 100000) (212857 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1755035904 :
    ThetaLowerSegment 1755035904 1755166976 (175498749638043 / 100000)
      (175511838239569 / 100000) := by
  exact
    packedTile65536 1755035904 1755166976 14 6149 41893 31 _ _ (1064287 / 50000) (2128577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1755166976 :
    ThetaLowerSegment 1755166976 1755298048 (175511838239569 / 100000)
      (87762544328147 / 50000) := by
  exact
    packedTile65536 1755166976 1755298048 14 6225 41894 31 _ _ (2128581 / 100000) (266073 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1755298048 :
    ThetaLowerSegment 1755298048 1755429120 (87762544328147 / 50000) (5485569971223 / 3125) := by
  exact
    packedTile65536 1755298048 1755429120 14 6178 41896 31 _ _ (2128589 / 100000) (133037 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1755429120 :
    ThetaLowerSegment 1755429120 1755560192 (5485569971223 / 3125) (43887860690031 / 25000) := by
  exact
    packedTile65536 1755429120 1755560192 14 6203 41897 31 _ _ (532149 / 25000) (2128599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1755560192 :
    ThetaLowerSegment 1755560192 1755691264 (43887860690031 / 25000) (43891122775661 / 25000) := by
  exact
    packedTile65536 1755560192 1755691264 14 6130 41899 31 _ _ (532151 / 25000) (2128607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1755691264 :
    ThetaLowerSegment 1755691264 1755822336 (43891122775661 / 25000) (43894379550491 / 25000) := by
  exact
    packedTile65536 1755691264 1755822336 14 6120 41900 31 _ _ (2128611 / 100000) (1064307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1755822336 :
    ThetaLowerSegment 1755822336 1755953408 (43894379550491 / 25000) (10974422388259 / 6250) := by
  exact
    packedTile65536 1755822336 1755953408 14 6220 41902 31 _ _ (2128619 / 100000) (1064311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1755953408 :
    ThetaLowerSegment 1755953408 1756084480 (10974422388259 / 6250) (43900936771999 / 25000) := by
  exact
    packedTile65536 1755953408 1756084480 14 6102 41904 31 _ _ (1064313 / 50000) (2128629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1756084480 :
    ThetaLowerSegment 1756084480 1756215552 (43900936771999 / 25000) (87808341398407 / 50000) := by
  exact
    packedTile65536 1756084480 1756215552 14 6077 41905 31 _ _ (1064317 / 50000) (2128637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1756215552 :
    ThetaLowerSegment 1756215552 1756346624 (87808341398407 / 50000) (21953722806691 / 12500) := by
  exact
    packedTile65536 1756215552 1756346624 14 6154 41907 31 _ _ (2128641 / 100000) (532161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1756346624 :
    ThetaLowerSegment 1756346624 1756477696 (21953722806691 / 12500) (5488844191741 / 3125) := by
  exact
    packedTile65536 1756346624 1756477696 14 6216 41908 31 _ _ (2128649 / 100000) (532163 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1756477696 :
    ThetaLowerSegment 1756477696 1756608768 (5488844191741 / 3125) (1097850232832 / 625) := by
  exact
    packedTile65536 1756477696 1756608768 14 6118 41910 31 _ _ (133041 / 6250) (2128659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1756608768 :
    ThetaLowerSegment 1756608768 1756739840 (1097850232832 / 625) (21958649315663 / 12500) := by
  exact
    packedTile65536 1756608768 1756739840 14 6181 41911 31 _ _ (266083 / 12500) (2128667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1756739840 :
    ThetaLowerSegment 1756739840 1756870912 (21958649315663 / 12500)
      (175682168775049 / 100000) := by
  exact
    packedTile65536 1756739840 1756870912 14 6095 41913 31 _ _ (2128671 / 100000) (1064337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1756870912 :
    ThetaLowerSegment 1756870912 1757001984 (175682168775049 / 100000)
      (87847609852999 / 50000) := by
  exact
    packedTile65536 1756870912 1757001984 14 6131 41915 31 _ _ (2128679 / 100000) (1064341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1757001984 :
    ThetaLowerSegment 1757001984 1757133056 (87847609852999 / 50000) (87854117246101 / 50000) := by
  exact
    packedTile65536 1757001984 1757133056 14 6114 41916 31 _ _ (1064343 / 50000) (2128689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1757133056 :
    ThetaLowerSegment 1757133056 1757264128 (87854117246101 / 50000)
      (175721345112389 / 100000) := by
  exact
    packedTile65536 1757133056 1757264128 14 6159 41918 31 _ _ (2128693 / 100000) (266087 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1757264128 :
    ThetaLowerSegment 1757264128 1757395200 (175721345112389 / 100000)
      (175734377019911 / 100000) := by
  exact
    packedTile65536 1757264128 1757395200 14 6122 41919 31 _ _ (2128701 / 100000) (66522 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1757395200 :
    ThetaLowerSegment 1757395200 1757526272 (175734377019911 / 100000)
      (175747447287031 / 100000) := by
  exact
    packedTile65536 1757395200 1757526272 14 6140 41921 31 _ _ (532177 / 25000) (2128711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1757526272 :
    ThetaLowerSegment 1757526272 1757657344 (175747447287031 / 100000)
      (175760655969811 / 100000) := by
  exact
    packedTile65536 1757526272 1757657344 14 6205 41922 31 _ _ (532179 / 25000) (2128719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1757657344 :
    ThetaLowerSegment 1757657344 1757788416 (175760655969811 / 100000) (3515476783027 / 2000) := by
  exact
    packedTile65536 1757657344 1757788416 14 6193 41924 31 _ _ (2128723 / 100000) (1064363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1757788416 :
    ThetaLowerSegment 1757788416 1757919488 (3515476783027 / 2000) (8789344413619 / 5000) := by
  exact
    packedTile65536 1757788416 1757919488 14 6130 41925 31 _ _ (2128731 / 100000) (1064367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1757919488 :
    ThetaLowerSegment 1757919488 1758050560 (8789344413619 / 5000) (43950008839567 / 25000) := by
  exact
    packedTile65536 1757919488 1758050560 14 6176 41927 31 _ _ (1064369 / 50000) (2128741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1758050560 :
    ThetaLowerSegment 1758050560 1758181632 (43950008839567 / 25000) (5494161553784 / 3125) := by
  exact
    packedTile65536 1758050560 1758181632 14 6170 41929 31 _ _ (1064373 / 50000) (2128749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1758181632 :
    ThetaLowerSegment 1758181632 1758312704 (5494161553784 / 3125) (175826306255851 / 100000) := by
  exact
    packedTile65536 1758181632 1758312704 14 6171 41930 31 _ _ (2128753 / 100000) (532189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1758312704 :
    ThetaLowerSegment 1758312704 1758443776 (175826306255851 / 100000)
      (175839389620957 / 100000) := by
  exact
    packedTile65536 1758312704 1758443776 14 6146 41932 31 _ _ (2128761 / 100000) (532191 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1758443776 :
    ThetaLowerSegment 1758443776 1758574848 (175839389620957 / 100000) (7034097218149 / 4000) := by
  exact
    packedTile65536 1758443776 1758574848 14 6126 41933 31 _ _ (66524 / 3125) (2128771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1758574848 :
    ThetaLowerSegment 1758574848 1758705920 (7034097218149 / 4000) (219832155817 / 125) := by
  exact
    packedTile65536 1758574848 1758705920 14 6245 41935 31 _ _ (85151 / 4000) (1064389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1758705920 :
    ThetaLowerSegment 1758705920 1758836992 (219832155817 / 125) (175878712358683 / 100000) := by
  exact
    packedTile65536 1758705920 1758836992 14 6101 41936 31 _ _ (2128783 / 100000) (1064393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1758836992 :
    ThetaLowerSegment 1758836992 1758968064 (175878712358683 / 100000)
      (175891974720383 / 100000) := by
  exact
    packedTile65536 1758836992 1758968064 14 6230 41938 31 _ _ (212879 / 10000) (2128793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1758968064 :
    ThetaLowerSegment 1758968064 1759099136 (175891974720383 / 100000)
      (35181000167069 / 20000) := by
  exact
    packedTile65536 1758968064 1759099136 14 6119 41940 31 _ _ (1064399 / 50000) (2128801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1759099136 :
    ThetaLowerSegment 1759099136 1759230208 (35181000167069 / 20000) (35183633073093 / 20000) := by
  exact
    packedTile65536 1759099136 1759230208 14 6184 41941 31 _ _ (425761 / 20000) (266101 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1759230208 :
    ThetaLowerSegment 1759230208 1759361280 (35183633073093 / 20000) (87965674552187 / 50000) := by
  exact
    packedTile65536 1759230208 1759361280 14 6193 41943 31 _ _ (2128813 / 100000) (133051 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1759361280 :
    ThetaLowerSegment 1759361280 1759492352 (87965674552187 / 50000) (87972212158407 / 50000) := by
  exact
    packedTile65536 1759361280 1759492352 14 6142 41944 31 _ _ (106441 / 5000) (2128823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1759492352 :
    ThetaLowerSegment 1759492352 1759623424 (87972212158407 / 50000) (87978836006729 / 50000) := by
  exact
    packedTile65536 1759492352 1759623424 14 6223 41946 31 _ _ (532207 / 25000) (2128831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1759623424 :
    ThetaLowerSegment 1759623424 1759754496 (87978836006729 / 50000)
      (175970728158513 / 100000) := by
  exact
    packedTile65536 1759623424 1759754496 14 6133 41947 31 _ _ (425767 / 20000) (1064419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1759754496 :
    ThetaLowerSegment 1759754496 1759885568 (175970728158513 / 100000)
      (175983986592717 / 100000) := by
  exact
    packedTile65536 1759754496 1759885568 14 6228 41949 31 _ _ (2128843 / 100000) (1064423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1759885568 :
    ThetaLowerSegment 1759885568 1760016640 (175983986592717 / 100000)
      (175997079020217 / 100000) := by
  exact
    packedTile65536 1759885568 1760016640 14 6150 41950 31 _ _ (42577 / 2000) (2128853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1760016640 :
    ThetaLowerSegment 1760016640 1760147712 (175997079020217 / 100000)
      (22001267444739 / 12500) := by
  exact
    packedTile65536 1760016640 1760147712 14 6135 41952 31 _ _ (2128857 / 100000) (106443 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1760147712 :
    ThetaLowerSegment 1760147712 1760278784 (22001267444739 / 12500)
      (176023195886957 / 100000) := by
  exact
    packedTile65536 1760147712 1760278784 14 6133 41954 31 _ _ (425773 / 20000) (532217 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1760278784 :
    ThetaLowerSegment 1760278784 1760409856 (176023195886957 / 100000)
      (176036160717437 / 100000) := by
  exact
    packedTile65536 1760278784 1760409856 14 6090 41955 31 _ _ (266109 / 12500) (17031 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1760409856 :
    ThetaLowerSegment 1760409856 1760540928 (176036160717437 / 100000)
      (176049189463037 / 100000) := by
  exact
    packedTile65536 1760409856 1760540928 14 6120 41957 31 _ _ (26611 / 1250) (2128883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1760540928 :
    ThetaLowerSegment 1760540928 1760672000 (176049189463037 / 100000)
      (176062188447059 / 100000) := by
  exact
    packedTile65536 1760540928 1760672000 14 6106 41958 31 _ _ (2128887 / 100000) (212889 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1760672000 :
    ThetaLowerSegment 1760672000 1760803072 (176062188447059 / 100000)
      (88037699120267 / 50000) := by
  exact
    packedTile65536 1760672000 1760803072 14 6205 41960 31 _ _ (425779 / 20000) (1064449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1760803072 :
    ThetaLowerSegment 1760803072 1760934144 (88037699120267 / 50000) (2201108079971 / 1250) := by
  exact
    packedTile65536 1760803072 1760934144 14 6223 41961 31 _ _ (1064451 / 50000) (425781 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1760934144 :
    ThetaLowerSegment 1760934144 1761065216 (2201108079971 / 1250) (8805087385491 / 5000) := by
  exact
    packedTile65536 1760934144 1761065216 14 6154 41963 31 _ _ (212891 / 10000) (2128913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1761065216 :
    ThetaLowerSegment 1761065216 1761196288 (8805087385491 / 5000) (176114740490271 / 100000) := by
  exact
    packedTile65536 1761065216 1761196288 14 6103 41965 31 _ _ (2128917 / 100000) (53223 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1761196288 :
    ThetaLowerSegment 1761196288 1761327360 (176114740490271 / 100000)
      (176127976010779 / 100000) := by
  exact
    packedTile65536 1761196288 1761327360 14 6217 41966 31 _ _ (532231 / 25000) (2128927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1761327360 :
    ThetaLowerSegment 1761327360 1761458432 (176127976010779 / 100000)
      (176140964624911 / 100000) := by
  exact
    packedTile65536 1761327360 1761458432 14 6101 41968 31 _ _ (532233 / 25000) (425787 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1761458432 :
    ThetaLowerSegment 1761458432 1761589504 (176140964624911 / 100000)
      (35230797043167 / 20000) := by
  exact
    packedTile65536 1761458432 1761589504 14 6116 41969 31 _ _ (2128939 / 100000) (1064471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1761589504 :
    ThetaLowerSegment 1761589504 1761720576 (35230797043167 / 20000) (5505221261526 / 3125) := by
  exact
    packedTile65536 1761589504 1761720576 14 6151 41971 31 _ _ (2128947 / 100000) (42579 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1761720576 :
    ThetaLowerSegment 1761720576 1761851648 (5505221261526 / 3125) (22022523276207 / 12500) := by
  exact
    packedTile65536 1761720576 1761851648 14 6156 41972 31 _ _ (1064477 / 50000) (2128957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1761851648 :
    ThetaLowerSegment 1761851648 1761982720 (22022523276207 / 12500) (88096664146041 / 50000) := by
  exact
    packedTile65536 1761851648 1761982720 14 6173 41974 31 _ _ (1064481 / 50000) (425793 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1761982720 :
    ThetaLowerSegment 1761982720 1762113792 (88096664146041 / 50000)
      (176206334163703 / 100000) := by
  exact
    packedTile65536 1761982720 1762113792 14 6109 41975 31 _ _ (2128969 / 100000) (532243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1762113792 :
    ThetaLowerSegment 1762113792 1762244864 (176206334163703 / 100000)
      (35243869293003 / 20000) := by
  exact
    packedTile65536 1762113792 1762244864 14 6112 41977 31 _ _ (133061 / 6250) (2128979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1762244864 :
    ThetaLowerSegment 1762244864 1762375936 (35243869293003 / 20000)
      (176232548294799 / 100000) := by
  exact
    packedTile65536 1762244864 1762375936 14 6201 41979 31 _ _ (266123 / 12500) (2128987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1762375936 :
    ThetaLowerSegment 1762375936 1762507008 (176232548294799 / 100000)
      (176245667137341 / 100000) := by
  exact
    packedTile65536 1762375936 1762507008 14 6162 41980 31 _ _ (2128991 / 100000) (1064497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1762507008 :
    ThetaLowerSegment 1762507008 1762638080 (176245667137341 / 100000) (5508086198506 / 3125) := by
  exact
    packedTile65536 1762507008 1762638080 14 6149 41982 31 _ _ (2128999 / 100000) (1064501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1762638080 :
    ThetaLowerSegment 1762638080 1762769152 (5508086198506 / 3125) (8813593438557 / 5000) := by
  exact
    packedTile65536 1762638080 1762769152 14 6158 41983 31 _ _ (1064503 / 50000) (2129009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1762769152 :
    ThetaLowerSegment 1762769152 1762900224 (8813593438557 / 5000) (44071262906457 / 25000) := by
  exact
    packedTile65536 1762769152 1762900224 14 6192 41985 31 _ _ (1064507 / 50000) (2129017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1762900224 :
    ThetaLowerSegment 1762900224 1763031296 (44071262906457 / 25000) (88149012939901 / 50000) := by
  exact
    packedTile65536 1762900224 1763031296 14 6094 41986 31 _ _ (2129021 / 100000) (66532 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1763031296 :
    ThetaLowerSegment 1763031296 1763162368 (88149012939901 / 50000) (11019452414611 / 6250) := by
  exact
    packedTile65536 1763031296 1763162368 14 6206 41988 31 _ _ (2129029 / 100000) (266129 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1763162368 :
    ThetaLowerSegment 1763162368 1763293440 (11019452414611 / 6250) (44081136809453 / 25000) := by
  exact
    packedTile65536 1763162368 1763293440 14 6251 41990 31 _ _ (532259 / 25000) (2129039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1763293440 :
    ThetaLowerSegment 1763293440 1763424512 (44081136809453 / 25000) (3526753498339 / 2000) := by
  exact
    packedTile65536 1763293440 1763424512 14 6166 41991 31 _ _ (2129043 / 100000) (1064523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1763424512 :
    ThetaLowerSegment 1763424512 1763555584 (3526753498339 / 2000) (88175326805923 / 50000) := by
  exact
    packedTile65536 1763424512 1763555584 14 6096 41993 31 _ _ (2129051 / 100000) (1064527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1763555584 :
    ThetaLowerSegment 1763555584 1763686656 (88175326805923 / 50000) (22045462826041 / 12500) := by
  exact
    packedTile65536 1763555584 1763686656 14 6129 41994 31 _ _ (1064529 / 50000) (2129061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1763686656 :
    ThetaLowerSegment 1763686656 1763817728 (22045462826041 / 12500) (88188454602363 / 50000) := by
  exact
    packedTile65536 1763686656 1763817728 14 6203 41996 31 _ _ (1064533 / 50000) (2129069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1763817728 :
    ThetaLowerSegment 1763817728 1763948800 (88188454602363 / 50000) (7055596969119 / 4000) := by
  exact
    packedTile65536 1763817728 1763948800 14 6113 41997 31 _ _ (2129073 / 100000) (532269 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1763948800 :
    ThetaLowerSegment 1763948800 1764079872 (7055596969119 / 4000) (176403030850611 / 100000) := by
  exact
    packedTile65536 1763948800 1764079872 14 6156 41999 31 _ _ (2129081 / 100000) (532271 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1764079872 :
    ThetaLowerSegment 1764079872 1764210944 (176403030850611 / 100000)
      (176416007641971 / 100000) := by
  exact
    packedTile65536 1764079872 1764210944 14 6095 42000 31 _ _ (66534 / 3125) (2129091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1764210944 :
    ThetaLowerSegment 1764210944 1764342016 (176416007641971 / 100000)
      (88214519916233 / 50000) := by
  exact
    packedTile65536 1764210944 1764342016 14 6121 42002 31 _ _ (425819 / 20000) (1064549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1764342016 :
    ThetaLowerSegment 1764342016 1764473088 (88214519916233 / 50000) (17644212955771 / 10000) := by
  exact
    packedTile65536 1764342016 1764473088 14 6148 42004 31 _ _ (2129103 / 100000) (1064553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1764473088 :
    ThetaLowerSegment 1764473088 1764604160 (17644212955771 / 10000) (17645534281437 / 10000) := by
  exact
    packedTile65536 1764473088 1764604160 14 6206 42005 31 _ _ (212911 / 10000) (2129113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1764604160 :
    ThetaLowerSegment 1764604160 1764735232 (17645534281437 / 10000) (5514645772053 / 3125) := by
  exact
    packedTile65536 1764604160 1764735232 14 6257 42007 31 _ _ (1064559 / 50000) (2129121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1764735232 :
    ThetaLowerSegment 1764735232 1764866304 (5514645772053 / 3125) (44120468449299 / 25000) := by
  exact
    packedTile65536 1764735232 1764866304 14 6204 42008 31 _ _ (17033 / 800) (266141 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1764866304 :
    ThetaLowerSegment 1764866304 1764997376 (44120468449299 / 25000) (88247441399913 / 50000) := by
  exact
    packedTile65536 1764866304 1764997376 14 6110 42010 31 _ _ (2129133 / 100000) (133071 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1764997376 :
    ThetaLowerSegment 1764997376 1765128448 (88247441399913 / 50000) (88254047056763 / 50000) := by
  exact
    packedTile65536 1764997376 1765128448 14 6205 42011 31 _ _ (106457 / 5000) (2129143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1765128448 :
    ThetaLowerSegment 1765128448 1765259520 (88254047056763 / 50000) (22065144287653 / 12500) := by
  exact
    packedTile65536 1765128448 1765259520 14 6134 42013 31 _ _ (2129147 / 100000) (42583 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1765259520 :
    ThetaLowerSegment 1765259520 1765390592 (22065144287653 / 12500)
      (176534063367989 / 100000) := by
  exact
    packedTile65536 1765259520 1765390592 14 6063 42014 31 _ _ (425831 / 20000) (1064579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1765390592 :
    ThetaLowerSegment 1765390592 1765521664 (176534063367989 / 100000)
      (35309447724489 / 20000) := by
  exact
    packedTile65536 1765390592 1765521664 14 6188 42016 31 _ _ (1064581 / 50000) (425833 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1765521664 :
    ThetaLowerSegment 1765521664 1765652736 (35309447724489 / 20000) (7062419623061 / 4000) := by
  exact
    packedTile65536 1765521664 1765652736 14 6224 42018 31 _ _ (212917 / 10000) (2129173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1765652736 :
    ThetaLowerSegment 1765652736 1765783808 (7062419623061 / 4000) (17657378728689 / 10000) := by
  exact
    packedTile65536 1765652736 1765783808 14 6245 42019 31 _ _ (2129177 / 100000) (106459 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1765783808 :
    ThetaLowerSegment 1765783808 1765914880 (17657378728689 / 10000) (35317370819047 / 20000) := by
  exact
    packedTile65536 1765783808 1765914880 14 6137 42021 31 _ _ (425837 / 20000) (532297 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1765914880 :
    ThetaLowerSegment 1765914880 1766045952 (35317370819047 / 20000)
      (176599976305531 / 100000) := by
  exact
    packedTile65536 1765914880 1766045952 14 6163 42022 31 _ _ (266149 / 12500) (425839 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1766045952 :
    ThetaLowerSegment 1766045952 1766177024 (176599976305531 / 100000)
      (176612972936227 / 100000) := by
  exact
    packedTile65536 1766045952 1766177024 14 6104 42024 31 _ _ (2129199 / 100000) (1064601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1766177024 :
    ThetaLowerSegment 1766177024 1766308096 (176612972936227 / 100000)
      (88313088074417 / 50000) := by
  exact
    packedTile65536 1766177024 1766308096 14 6201 42025 31 _ _ (2129207 / 100000) (212921 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1766308096 :
    ThetaLowerSegment 1766308096 1766439168 (88313088074417 / 50000) (88319601340043 / 50000) := by
  exact
    packedTile65536 1766308096 1766439168 14 6118 42027 31 _ _ (1064607 / 50000) (2129217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1766439168 :
    ThetaLowerSegment 1766439168 1766570240 (88319601340043 / 50000) (22081534246743 / 12500) := by
  exact
    packedTile65536 1766439168 1766570240 14 6139 42029 31 _ _ (1064611 / 50000) (85169 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1766570240 :
    ThetaLowerSegment 1766570240 1766701312 (22081534246743 / 12500) (35333098871361 / 20000) := by
  exact
    packedTile65536 1766570240 1766701312 14 6209 42030 31 _ _ (2129229 / 100000) (133077 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1766701312 :
    ThetaLowerSegment 1766701312 1766832384 (35333098871361 / 20000)
      (176678506118001 / 100000) := by
  exact
    packedTile65536 1766701312 1766832384 14 6111 42032 31 _ _ (532309 / 25000) (2129239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1766832384 :
    ThetaLowerSegment 1766832384 1766963456 (176678506118001 / 100000)
      (176691551995989 / 100000) := by
  exact
    packedTile65536 1766832384 1766963456 14 6127 42033 31 _ _ (532311 / 25000) (2129247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1766963456 :
    ThetaLowerSegment 1766963456 1767094528 (176691551995989 / 100000)
      (176704561719599 / 100000) := by
  exact
    packedTile65536 1766963456 1767094528 14 6110 42035 31 _ _ (2129251 / 100000) (1064627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1767094528 :
    ThetaLowerSegment 1767094528 1767225600 (176704561719599 / 100000)
      (88358818749559 / 50000) := by
  exact
    packedTile65536 1767094528 1767225600 14 6141 42036 31 _ _ (2129259 / 100000) (1064631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1767225600 :
    ThetaLowerSegment 1767225600 1767356672 (88358818749559 / 50000) (88365419474159 / 50000) := by
  exact
    packedTile65536 1767225600 1767356672 14 6200 42038 31 _ _ (1064633 / 50000) (2129269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1767356672 :
    ThetaLowerSegment 1767356672 1767487744 (88365419474159 / 50000) (88372011706463 / 50000) := by
  exact
    packedTile65536 1767356672 1767487744 14 6192 42039 31 _ _ (1064637 / 50000) (2129277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1767487744 :
    ThetaLowerSegment 1767487744 1767618816 (88372011706463 / 50000) (88378603960439 / 50000) := by
  exact
    packedTile65536 1767487744 1767618816 14 6192 42041 31 _ _ (2129281 / 100000) (532321 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1767618816 :
    ThetaLowerSegment 1767618816 1767749888 (88378603960439 / 50000) (88385074866671 / 50000) := by
  exact
    packedTile65536 1767618816 1767749888 14 6078 42043 31 _ _ (266161 / 12500) (2129291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1767749888 :
    ThetaLowerSegment 1767749888 1767880960 (88385074866671 / 50000) (88391592641727 / 50000) := by
  exact
    packedTile65536 1767749888 1767880960 14 6122 42044 31 _ _ (133081 / 6250) (2129299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1767880960 :
    ThetaLowerSegment 1767880960 1768012032 (88391592641727 / 50000) (88398159412179 / 50000) := by
  exact
    packedTile65536 1767880960 1768012032 14 6168 42046 31 _ _ (2129303 / 100000) (1064653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1768012032 :
    ThetaLowerSegment 1768012032 1768143104 (88398159412179 / 50000) (88404717690059 / 50000) := by
  exact
    packedTile65536 1768012032 1768143104 14 6160 42047 31 _ _ (2129311 / 100000) (1064657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1768143104 :
    ThetaLowerSegment 1768143104 1768274176 (88404717690059 / 50000) (88411382455399 / 50000) := by
  exact
    packedTile65536 1768143104 1768274176 14 6260 42049 31 _ _ (1064659 / 50000) (2129321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1768274176 :
    ThetaLowerSegment 1768274176 1768405248 (88411382455399 / 50000)
      (176835824061023 / 100000) := by
  exact
    packedTile65536 1768274176 1768405248 14 6133 42050 31 _ _ (85173 / 4000) (133083 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1768405248 :
    ThetaLowerSegment 1768405248 1768536320 (176835824061023 / 100000)
      (176849081288281 / 100000) := by
  exact
    packedTile65536 1768405248 1768536320 14 6226 42052 31 _ _ (2129333 / 100000) (266167 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1768536320 :
    ThetaLowerSegment 1768536320 1768667392 (176849081288281 / 100000)
      (176862272549581 / 100000) := by
  exact
    packedTile65536 1768536320 1768667392 14 6195 42053 31 _ _ (106467 / 5000) (2129343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1768667392 :
    ThetaLowerSegment 1768667392 1768798464 (176862272549581 / 100000)
      (176875170010417 / 100000) := by
  exact
    packedTile65536 1768667392 1768798464 14 6057 42055 31 _ _ (532337 / 25000) (2129351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1768798464 :
    ThetaLowerSegment 1768798464 1768929536 (176875170010417 / 100000)
      (44222046689383 / 25000) := by
  exact
    packedTile65536 1768798464 1768929536 14 6113 42057 31 _ _ (425871 / 20000) (1064679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1768929536 :
    ThetaLowerSegment 1768929536 1769060608 (44222046689383 / 25000) (88450675239799 / 50000) := by
  exact
    packedTile65536 1768929536 1769060608 14 6182 42058 31 _ _ (2129363 / 100000) (1064683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1769060608 :
    ThetaLowerSegment 1769060608 1769191680 (88450675239799 / 50000) (44228582247437 / 25000) := by
  exact
    packedTile65536 1769060608 1769191680 14 6095 42060 31 _ _ (212937 / 10000) (2129373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1769191680 :
    ThetaLowerSegment 1769191680 1769322752 (44228582247437 / 25000) (88463678259117 / 50000) := by
  exact
    packedTile65536 1769191680 1769322752 14 6118 42061 31 _ _ (2129377 / 100000) (106469 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1769322752 :
    ThetaLowerSegment 1769322752 1769339136 (88463678259117 / 50000)
      (176929049379309 / 100000) := by
  exact
    packedTile65536 1769322752 1769339136 11 795 42063 31 _ _ (425877 / 20000) (532347 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1769339136 :
    ThetaLowerSegment 1769339136 1769341184 (176929049379309 / 100000)
      (176929258059137 / 100000) := by
  exact
    packedTile65536 1769339136 1769341184 8 98 42063 31 _ _ (1064693 / 50000) (2129389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1737341184_1769341184 :
    ThetaLowerSegment 1737341184 1769341184 (43432179839841 / 25000)
      (176929258059137 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1737341184 cell1737472256)
                  (ThetaLowerSegment.join cell1737603328 cell1737734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1737865472 cell1737996544)
                  (ThetaLowerSegment.join cell1738127616 cell1738258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1738389760 cell1738520832)
                  (ThetaLowerSegment.join cell1738651904 cell1738782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1738914048 cell1739045120)
                  (ThetaLowerSegment.join cell1739176192 cell1739307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1739438336 cell1739569408)
                  (ThetaLowerSegment.join cell1739700480 cell1739831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1739962624 cell1740093696)
                  (ThetaLowerSegment.join cell1740224768 cell1740355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1740486912 cell1740617984)
                  (ThetaLowerSegment.join cell1740749056 cell1740880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1741011200 cell1741142272)
                  (ThetaLowerSegment.join cell1741273344 cell1741404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1741535488 cell1741666560)
                  (ThetaLowerSegment.join cell1741797632 cell1741928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1742059776 cell1742190848)
                  (ThetaLowerSegment.join cell1742321920 cell1742452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1742584064 cell1742715136)
                  (ThetaLowerSegment.join cell1742846208 cell1742977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1743108352 cell1743239424)
                  (ThetaLowerSegment.join cell1743370496 cell1743501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1743632640 cell1743763712)
                  (ThetaLowerSegment.join cell1743894784 cell1744025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1744156928 cell1744288000)
                  (ThetaLowerSegment.join cell1744419072 cell1744550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1744681216 cell1744812288)
                  (ThetaLowerSegment.join cell1744943360 cell1745074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1745205504 cell1745336576)
                  (ThetaLowerSegment.join cell1745467648 cell1745598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1745729792 cell1745860864)
                  (ThetaLowerSegment.join cell1745991936 cell1746123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1746254080 cell1746385152)
                  (ThetaLowerSegment.join cell1746516224 cell1746647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1746778368 cell1746909440)
                  (ThetaLowerSegment.join cell1747040512 cell1747171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1747302656 cell1747433728)
                  (ThetaLowerSegment.join cell1747564800 cell1747695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1747826944 cell1747958016)
                  (ThetaLowerSegment.join cell1748089088 cell1748220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1748351232 cell1748482304)
                  (ThetaLowerSegment.join cell1748613376 cell1748744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1748875520 cell1749006592)
                  (ThetaLowerSegment.join cell1749137664 cell1749268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1749399808 cell1749530880)
                  (ThetaLowerSegment.join cell1749661952 cell1749793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1749924096 cell1750055168)
                  (ThetaLowerSegment.join cell1750186240 cell1750317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1750448384 cell1750579456)
                  (ThetaLowerSegment.join cell1750710528 cell1750841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1750972672 cell1751103744)
                  (ThetaLowerSegment.join cell1751234816 cell1751365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1751496960 cell1751628032)
                  (ThetaLowerSegment.join cell1751759104 cell1751890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1752021248 cell1752152320)
                  (ThetaLowerSegment.join cell1752283392 cell1752414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1752545536 cell1752676608)
                  (ThetaLowerSegment.join cell1752807680 cell1752938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1753069824 cell1753200896)
                  (ThetaLowerSegment.join cell1753331968 cell1753463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1753594112 cell1753725184)
                  (ThetaLowerSegment.join cell1753856256 cell1753987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1754118400 cell1754249472)
                  (ThetaLowerSegment.join cell1754380544 cell1754511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1754642688 cell1754773760)
                  (ThetaLowerSegment.join cell1754904832 cell1755035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1755166976 cell1755298048)
                  (ThetaLowerSegment.join cell1755429120 cell1755560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1755691264 cell1755822336)
                  (ThetaLowerSegment.join cell1755953408 cell1756084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1756215552 cell1756346624)
                  (ThetaLowerSegment.join cell1756477696 cell1756608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1756739840 cell1756870912)
                  (ThetaLowerSegment.join cell1757001984 cell1757133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1757264128 cell1757395200)
                  (ThetaLowerSegment.join cell1757526272 cell1757657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1757788416 cell1757919488)
                  (ThetaLowerSegment.join cell1758050560 cell1758181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1758312704 cell1758443776)
                  (ThetaLowerSegment.join cell1758574848 cell1758705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1758836992 cell1758968064)
                  (ThetaLowerSegment.join cell1759099136 cell1759230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1759361280 cell1759492352)
                  (ThetaLowerSegment.join cell1759623424 cell1759754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1759885568 cell1760016640)
                  (ThetaLowerSegment.join cell1760147712 cell1760278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1760409856 cell1760540928)
                  (ThetaLowerSegment.join cell1760672000 cell1760803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1760934144 cell1761065216)
                  (ThetaLowerSegment.join cell1761196288 cell1761327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1761458432 cell1761589504)
                  (ThetaLowerSegment.join cell1761720576 cell1761851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1761982720 cell1762113792)
                  (ThetaLowerSegment.join cell1762244864 cell1762375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1762507008 cell1762638080)
                  (ThetaLowerSegment.join cell1762769152 cell1762900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1763031296 cell1763162368)
                  (ThetaLowerSegment.join cell1763293440 cell1763424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1763555584 cell1763686656)
                  (ThetaLowerSegment.join cell1763817728 cell1763948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1764079872 cell1764210944)
                  (ThetaLowerSegment.join cell1764342016 cell1764473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1764604160 cell1764735232)
                  (ThetaLowerSegment.join cell1764866304 cell1764997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1765128448 cell1765259520)
                  (ThetaLowerSegment.join cell1765390592 cell1765521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1765652736 cell1765783808)
                  (ThetaLowerSegment.join cell1765914880 cell1766045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1766177024 cell1766308096)
                  (ThetaLowerSegment.join cell1766439168 cell1766570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1766701312 cell1766832384)
                  (ThetaLowerSegment.join cell1766963456 cell1767094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1767225600 cell1767356672)
                  (ThetaLowerSegment.join cell1767487744 cell1767618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1767749888 cell1767880960)
                  (ThetaLowerSegment.join cell1768012032 cell1768143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1768274176 cell1768405248)
                  (ThetaLowerSegment.join cell1768536320 cell1768667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1768798464 cell1768929536)
                (ThetaLowerSegment.join cell1769060608 cell1769191680))
              (ThetaLowerSegment.join cell1769322752 cell1769339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
