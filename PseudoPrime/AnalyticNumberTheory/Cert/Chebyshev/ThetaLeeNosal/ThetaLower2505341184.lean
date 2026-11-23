/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2505341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2473341184 :
    ThetaLowerSegment 2473341184 2473472256 (123663746553391 / 50000)
      (123670317388907 / 50000) := by
  exact
    packedTile65536 2473341184 2473472256 14 6076 49732 31 _ _ (1081441 / 50000) (432577 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2473472256 :
    ThetaLowerSegment 2473472256 2473603328 (123670317388907 / 50000) (1545961670753 / 625) := by
  exact
    packedTile65536 2473472256 2473603328 14 6118 49734 31 _ _ (2162887 / 100000) (216289 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2473603328 :
    ThetaLowerSegment 2473603328 2473734400 (1545961670753 / 625) (123683532646783 / 50000) := by
  exact
    packedTile65536 2473603328 2473734400 14 6102 49735 31 _ _ (2162893 / 100000) (135181 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2473734400 :
    ThetaLowerSegment 2473734400 2473865472 (123683532646783 / 50000) (24738021138761 / 10000) := by
  exact
    packedTile65536 2473734400 2473865472 14 6078 49736 31 _ _ (1081449 / 50000) (2162901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2473865472 :
    ThetaLowerSegment 2473865472 2473996544 (24738021138761 / 10000) (123696590076999 / 50000) := by
  exact
    packedTile65536 2473865472 2473996544 14 5996 49737 31 _ _ (2162903 / 100000) (1081453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2473996544 :
    ThetaLowerSegment 2473996544 2474127616 (123696590076999 / 50000)
      (123703212904357 / 50000) := by
  exact
    packedTile65536 2473996544 2474127616 14 6124 49739 31 _ _ (2162909 / 100000) (67591 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2474127616 :
    ThetaLowerSegment 2474127616 2474258688 (123703212904357 / 50000) (15463719600083 / 6250) := by
  exact
    packedTile65536 2474127616 2474258688 14 6051 49740 31 _ _ (1081457 / 50000) (2162917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2474258688 :
    ThetaLowerSegment 2474258688 2474389760 (15463719600083 / 6250) (247432674963443 / 100000) := by
  exact
    packedTile65536 2474258688 2474389760 14 6085 49741 31 _ _ (2162919 / 100000) (1081461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2474389760 :
    ThetaLowerSegment 2474389760 2474520832 (247432674963443 / 100000)
      (247445762816567 / 100000) := by
  exact
    packedTile65536 2474389760 2474520832 14 6051 49743 31 _ _ (540731 / 25000) (2162927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2474520832 :
    ThetaLowerSegment 2474520832 2474651904 (247445762816567 / 100000)
      (247459108094667 / 100000) := by
  exact
    packedTile65536 2474520832 2474651904 14 6170 49744 31 _ _ (216293 / 10000) (2162933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2474651904 :
    ThetaLowerSegment 2474651904 2474782976 (247459108094667 / 100000)
      (123736091518371 / 50000) := by
  exact
    packedTile65536 2474651904 2474782976 14 6045 49745 31 _ _ (432587 / 20000) (1081469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2474782976 :
    ThetaLowerSegment 2474782976 2474914048 (123736091518371 / 50000)
      (123742630085991 / 50000) := by
  exact
    packedTile65536 2474782976 2474914048 14 6046 49747 31 _ _ (108147 / 5000) (2162943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2474914048 :
    ThetaLowerSegment 2474914048 2475045120 (123742630085991 / 50000) (61874526477069 / 25000) := by
  exact
    packedTile65536 2474914048 2475045120 14 5939 49748 31 _ _ (1081473 / 50000) (2162949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2475045120 :
    ThetaLowerSegment 2475045120 2475176192 (61874526477069 / 25000) (7734719470364 / 3125) := by
  exact
    packedTile65536 2475045120 2475176192 14 5972 49749 31 _ _ (2162951 / 100000) (1081477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2475176192 :
    ThetaLowerSegment 2475176192 2475307264 (7734719470364 / 3125) (30940504965107 / 12500) := by
  exact
    packedTile65536 2475176192 2475307264 14 6018 49751 31 _ _ (540739 / 25000) (2162959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2475307264 :
    ThetaLowerSegment 2475307264 2475438336 (30940504965107 / 12500) (61884311691707 / 25000) := by
  exact
    packedTile65536 2475307264 2475438336 14 6106 49752 31 _ _ (1081481 / 50000) (432593 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2475438336 :
    ThetaLowerSegment 2475438336 2475569408 (61884311691707 / 25000)
      (247550456006297 / 100000) := by
  exact
    packedTile65536 2475438336 2475569408 14 6107 49753 31 _ _ (2162967 / 100000) (216297 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2475569408 :
    ThetaLowerSegment 2475569408 2475700480 (247550456006297 / 100000)
      (247563483586653 / 100000) := by
  exact
    packedTile65536 2475569408 2475700480 14 6023 49755 31 _ _ (540743 / 25000) (86519 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2475700480 :
    ThetaLowerSegment 2475700480 2475831552 (247563483586653 / 100000) (12378822099093 / 5000) := by
  exact
    packedTile65536 2475700480 2475831552 14 5991 49756 31 _ _ (2162977 / 100000) (108149 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2475831552 :
    ThetaLowerSegment 2475831552 2475962624 (12378822099093 / 5000) (9903585879723 / 4000) := by
  exact
    packedTile65536 2475831552 2475962624 14 6105 49757 31 _ _ (2162983 / 100000) (1081493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2475962624 :
    ThetaLowerSegment 2475962624 2476093696 (9903585879723 / 4000) (9904109322819 / 4000) := by
  exact
    packedTile65536 2475962624 2476093696 14 6050 49759 31 _ _ (540747 / 25000) (2162991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2476093696 :
    ThetaLowerSegment 2476093696 2476224768 (9904109322819 / 4000) (247615827830097 / 100000) := by
  exact
    packedTile65536 2476093696 2476224768 14 6054 49760 31 _ _ (2162993 / 100000) (540749 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2476224768 :
    ThetaLowerSegment 2476224768 2476355840 (247615827830097 / 100000)
      (247628935604037 / 100000) := by
  exact
    packedTile65536 2476224768 2476355840 14 6060 49761 31 _ _ (2162999 / 100000) (1081501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2476355840 :
    ThetaLowerSegment 2476355840 2476486912 (247628935604037 / 100000)
      (247642235915633 / 100000) := by
  exact
    packedTile65536 2476355840 2476486912 14 6149 49762 31 _ _ (540751 / 25000) (2163007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2476486912 :
    ThetaLowerSegment 2476486912 2476617984 (247642235915633 / 100000)
      (49531072210849 / 20000) := by
  exact
    packedTile65536 2476486912 2476617984 14 6068 49764 31 _ _ (2163009 / 100000) (540753 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2476617984 :
    ThetaLowerSegment 2476617984 2476749056 (49531072210849 / 20000)
      (247668464593057 / 100000) := by
  exact
    packedTile65536 2476617984 2476749056 14 6058 49765 31 _ _ (1081507 / 50000) (2163017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2476749056 :
    ThetaLowerSegment 2476749056 2476880128 (247668464593057 / 100000)
      (247681468669297 / 100000) := by
  exact
    packedTile65536 2476749056 2476880128 14 6012 49766 31 _ _ (108151 / 5000) (2163023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2476880128 :
    ThetaLowerSegment 2476880128 2477011200 (247681468669297 / 100000)
      (61923682543893 / 25000) := by
  exact
    packedTile65536 2476880128 2477011200 14 6131 49768 31 _ _ (86521 / 4000) (540757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2477011200 :
    ThetaLowerSegment 2477011200 2477142272 (61923682543893 / 25000) (123853913661111 / 50000) := by
  exact
    packedTile65536 2477011200 2477142272 14 6055 49769 31 _ _ (216303 / 10000) (2163033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2477142272 :
    ThetaLowerSegment 2477142272 2477273344 (123853913661111 / 50000)
      (123860522817609 / 50000) := by
  exact
    packedTile65536 2477142272 2477273344 14 6111 49770 31 _ _ (540759 / 25000) (2163039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2477273344 :
    ThetaLowerSegment 2477273344 2477404416 (123860522817609 / 50000) (7741690274139 / 3125) := by
  exact
    packedTile65536 2477273344 2477404416 14 6030 49772 31 _ _ (2163041 / 100000) (540761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2477404416 :
    ThetaLowerSegment 2477404416 2477535488 (7741690274139 / 3125) (123873569214483 / 50000) := by
  exact
    packedTile65536 2477404416 2477535488 14 6033 49773 31 _ _ (1081523 / 50000) (2163049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2477535488 :
    ThetaLowerSegment 2477535488 2477666560 (123873569214483 / 50000)
      (123880084327107 / 50000) := by
  exact
    packedTile65536 2477535488 2477666560 14 6024 49774 31 _ _ (540763 / 25000) (432611 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2477666560 :
    ThetaLowerSegment 2477666560 2477797632 (123880084327107 / 50000)
      (247773322203831 / 100000) := by
  exact
    packedTile65536 2477666560 2477797632 14 6081 49776 31 _ _ (2163057 / 100000) (108153 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2477797632 :
    ThetaLowerSegment 2477797632 2477928704 (247773322203831 / 100000)
      (49557256654267 / 20000) := by
  exact
    packedTile65536 2477797632 2477928704 14 5992 49777 31 _ _ (1081531 / 50000) (432613 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2477928704 :
    ThetaLowerSegment 2477928704 2478059776 (49557256654267 / 20000) (7743729833913 / 3125) := by
  exact
    packedTile65536 2477928704 2478059776 14 6043 49778 31 _ _ (2163067 / 100000) (216307 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2478059776 :
    ThetaLowerSegment 2478059776 2478190848 (7743729833913 / 3125) (15488270820201 / 6250) := by
  exact
    packedTile65536 2478059776 2478190848 14 6000 49780 31 _ _ (2163073 / 100000) (540769 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2478190848 :
    ThetaLowerSegment 2478190848 2478321920 (15488270820201 / 6250) (123912739074111 / 50000) := by
  exact
    packedTile65536 2478190848 2478321920 14 6077 49781 31 _ _ (1081539 / 50000) (2163081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2478321920 :
    ThetaLowerSegment 2478321920 2478452992 (123912739074111 / 50000)
      (247838874121241 / 100000) := by
  exact
    packedTile65536 2478321920 2478452992 14 6193 49782 31 _ _ (2163083 / 100000) (1081543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2478452992 :
    ThetaLowerSegment 2478452992 2478584064 (247838874121241 / 100000)
      (247851969462047 / 100000) := by
  exact
    packedTile65536 2478452992 2478584064 14 6054 49784 31 _ _ (2163089 / 100000) (540773 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2478584064 :
    ThetaLowerSegment 2478584064 2478715136 (247851969462047 / 100000) (9914607611703 / 4000) := by
  exact
    packedTile65536 2478584064 2478715136 14 6112 49785 31 _ _ (1081547 / 50000) (2163097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2478715136 :
    ThetaLowerSegment 2478715136 2478846208 (9914607611703 / 4000) (247878311651109 / 100000) := by
  exact
    packedTile65536 2478715136 2478846208 14 6066 49786 31 _ _ (2163099 / 100000) (1081551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2478846208 :
    ThetaLowerSegment 2478846208 2478977280 (247878311651109 / 100000) (9915660609517 / 4000) := by
  exact
    packedTile65536 2478846208 2478977280 14 6104 49788 31 _ _ (67597 / 3125) (2163107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2478977280 :
    ThetaLowerSegment 2478977280 2479108352 (9915660609517 / 4000) (49580948963737 / 20000) := by
  exact
    packedTile65536 2478977280 2479108352 14 6116 49789 31 _ _ (216311 / 10000) (2163113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2479108352 :
    ThetaLowerSegment 2479108352 2479239424 (49580948963737 / 20000) (24791785113247 / 10000) := by
  exact
    packedTile65536 2479108352 2479239424 14 6059 49790 31 _ _ (432623 / 20000) (1081559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2479239424 :
    ThetaLowerSegment 2479239424 2479370496 (24791785113247 / 10000) (4958617202723 / 2000) := by
  exact
    packedTile65536 2479239424 2479370496 14 6014 49791 31 _ _ (27039 / 1250) (2163123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2479370496 :
    ThetaLowerSegment 2479370496 2479501568 (4958617202723 / 2000) (15496490877127 / 6250) := by
  exact
    packedTile65536 2479370496 2479501568 14 6007 49793 31 _ _ (1081563 / 50000) (2163129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2479501568 :
    ThetaLowerSegment 2479501568 2479632640 (15496490877127 / 6250) (49591419777029 / 20000) := by
  exact
    packedTile65536 2479501568 2479632640 14 6123 49794 31 _ _ (2163131 / 100000) (1081567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2479632640 :
    ThetaLowerSegment 2479632640 2479763712 (49591419777029 / 20000)
      (247970136105817 / 100000) := by
  exact
    packedTile65536 2479632640 2479763712 14 6027 49795 31 _ _ (67598 / 3125) (2163139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2479763712 :
    ThetaLowerSegment 2479763712 2479894784 (247970136105817 / 100000) (7749473085824 / 3125) := by
  exact
    packedTile65536 2479763712 2479894784 14 6011 49797 31 _ _ (2163141 / 100000) (270393 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2479894784 :
    ThetaLowerSegment 2479894784 2480025856 (7749473085824 / 3125) (49599189347951 / 20000) := by
  exact
    packedTile65536 2479894784 2480025856 14 5921 49798 31 _ _ (2163147 / 100000) (43263 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2480025856 :
    ThetaLowerSegment 2480025856 2480156928 (49599189347951 / 20000)
      (248009111682827 / 100000) := by
  exact
    packedTile65536 2480025856 2480156928 14 6086 49799 31 _ _ (135197 / 6250) (432631 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2480156928 :
    ThetaLowerSegment 2480156928 2480288000 (248009111682827 / 100000)
      (248022237719503 / 100000) := by
  exact
    packedTile65536 2480156928 2480288000 14 6068 49801 31 _ _ (2163157 / 100000) (54079 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2480288000 :
    ThetaLowerSegment 2480288000 2480419072 (248022237719503 / 100000)
      (124017782483373 / 50000) := by
  exact
    packedTile65536 2480288000 2480419072 14 6161 49802 31 _ _ (2163163 / 100000) (1081583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2480419072 :
    ThetaLowerSegment 2480419072 2480550144 (124017782483373 / 50000) (4960975335621 / 2000) := by
  exact
    packedTile65536 2480419072 2480550144 14 6103 49803 31 _ _ (67599 / 3125) (2163171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2480550144 :
    ThetaLowerSegment 2480550144 2480681216 (4960975335621 / 2000) (31007750134183 / 12500) := by
  exact
    packedTile65536 2480550144 2480681216 14 6118 49805 31 _ _ (2163173 / 100000) (270397 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2480681216 :
    ThetaLowerSegment 2480681216 2480812288 (31007750134183 / 12500) (31009398475819 / 12500) := by
  exact
    packedTile65536 2480681216 2480812288 14 6096 49806 31 _ _ (1081589 / 50000) (2163181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2480812288 :
    ThetaLowerSegment 2480812288 2480943360 (31009398475819 / 12500) (31011023567799 / 12500) := by
  exact
    packedTile65536 2480812288 2480943360 14 6010 49807 31 _ _ (135199 / 6250) (2163187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2480943360 :
    ThetaLowerSegment 2480943360 2481074432 (31011023567799 / 12500) (31012658938683 / 12500) := by
  exact
    packedTile65536 2480943360 2481074432 14 6048 49809 31 _ _ (2163189 / 100000) (270399 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2481074432 :
    ThetaLowerSegment 2481074432 2481205504 (31012658938683 / 12500) (15507153105457 / 6250) := by
  exact
    packedTile65536 2481074432 2481205504 14 6092 49810 31 _ _ (1081597 / 50000) (2163197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2481205504 :
    ThetaLowerSegment 2481205504 2481336576 (15507153105457 / 6250) (15507973634257 / 6250) := by
  exact
    packedTile65536 2481205504 2481336576 14 6069 49811 31 _ _ (2704 / 125) (2163203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2481336576 :
    ThetaLowerSegment 2481336576 2481467648 (15507973634257 / 6250) (248140706639257 / 100000) := by
  exact
    packedTile65536 2481336576 2481467648 14 6069 49813 31 _ _ (432641 / 20000) (270401 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2481467648 :
    ThetaLowerSegment 2481467648 2481598720 (248140706639257 / 100000)
      (248153893567417 / 100000) := by
  exact
    packedTile65536 2481467648 2481598720 14 6096 49814 31 _ _ (216321 / 10000) (2163213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2481598720 :
    ThetaLowerSegment 2481598720 2481729792 (248153893567417 / 100000)
      (124083534854991 / 50000) := by
  exact
    packedTile65536 2481598720 2481729792 14 6091 49815 31 _ _ (432643 / 20000) (1081609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2481729792 :
    ThetaLowerSegment 2481729792 2481860864 (124083534854991 / 50000) (49636037063781 / 20000) := by
  exact
    packedTile65536 2481729792 2481860864 14 6063 49816 31 _ _ (2163221 / 100000) (270403 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2481860864 :
    ThetaLowerSegment 2481860864 2481991936 (49636037063781 / 20000)
      (248193233898137 / 100000) := by
  exact
    packedTile65536 2481860864 2481991936 14 6032 49818 31 _ _ (1081613 / 50000) (2163229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2481991936 :
    ThetaLowerSegment 2481991936 2482123008 (248193233898137 / 100000)
      (248206459892471 / 100000) := by
  exact
    packedTile65536 2481991936 2482123008 14 6114 49819 31 _ _ (2163231 / 100000) (1081617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2482123008 :
    ThetaLowerSegment 2482123008 2482254080 (248206459892471 / 100000)
      (124109831063941 / 50000) := by
  exact
    packedTile65536 2482123008 2482254080 14 6103 49820 31 _ _ (2163237 / 100000) (54081 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2482254080 :
    ThetaLowerSegment 2482254080 2482385152 (124109831063941 / 50000)
      (124116426788799 / 50000) := by
  exact
    packedTile65536 2482254080 2482385152 14 6098 49822 31 _ _ (1081621 / 50000) (432649 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2482385152 :
    ThetaLowerSegment 2482385152 2482516224 (124116426788799 / 50000)
      (248245895793761 / 100000) := by
  exact
    packedTile65536 2482385152 2482516224 14 6029 49823 31 _ _ (2163247 / 100000) (8653 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2482516224 :
    ThetaLowerSegment 2482516224 2482647296 (248245895793761 / 100000)
      (248258873142509 / 100000) := by
  exact
    packedTile65536 2482516224 2482647296 14 5999 49824 31 _ _ (540813 / 25000) (432651 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2482647296 :
    ThetaLowerSegment 2482647296 2482778368 (248258873142509 / 100000)
      (49654354097341 / 20000) := by
  exact
    packedTile65536 2482647296 2482778368 14 5962 49826 31 _ _ (1081629 / 50000) (2163261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2482778368 :
    ThetaLowerSegment 2482778368 2482909440 (49654354097341 / 20000) (15517807830563 / 6250) := by
  exact
    packedTile65536 2482778368 2482909440 14 6081 49827 31 _ _ (2163263 / 100000) (1081633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2482909440 :
    ThetaLowerSegment 2482909440 2483040512 (15517807830563 / 6250) (7759311961708 / 3125) := by
  exact
    packedTile65536 2482909440 2483040512 14 6036 49828 31 _ _ (540817 / 25000) (2163271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2483040512 :
    ThetaLowerSegment 2483040512 2483171584 (7759311961708 / 3125) (4966222622959 / 2000) := by
  exact
    packedTile65536 2483040512 2483171584 14 6078 49830 31 _ _ (2163273 / 100000) (540819 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2483171584 :
    ThetaLowerSegment 2483171584 2483302656 (4966222622959 / 2000) (49664820001111 / 20000) := by
  exact
    packedTile65536 2483171584 2483302656 14 5995 49831 31 _ _ (2163279 / 100000) (1081641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2483302656 :
    ThetaLowerSegment 2483302656 2483433728 (49664820001111 / 20000)
      (248337114322099 / 100000) := by
  exact
    packedTile65536 2483302656 2483433728 14 6016 49832 31 _ _ (540821 / 25000) (2163287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2483433728 :
    ThetaLowerSegment 2483433728 2483564800 (248337114322099 / 100000)
      (248350314711577 / 100000) := by
  exact
    packedTile65536 2483433728 2483564800 14 6102 49834 31 _ _ (2163289 / 100000) (540823 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2483564800 :
    ThetaLowerSegment 2483564800 2483695872 (248350314711577 / 100000)
      (124181728364351 / 50000) := by
  exact
    packedTile65536 2483564800 2483695872 14 6075 49835 31 _ _ (432659 / 20000) (1081649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2483695872 :
    ThetaLowerSegment 2483695872 2483826944 (124181728364351 / 50000)
      (124188352388951 / 50000) := by
  exact
    packedTile65536 2483695872 2483826944 14 6124 49836 31 _ _ (21633 / 1000) (2163303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2483826944 :
    ThetaLowerSegment 2483826944 2483958016 (124188352388951 / 50000)
      (248389955021027 / 100000) := by
  exact
    packedTile65536 2483826944 2483958016 14 6125 49838 31 _ _ (432661 / 20000) (540827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2483958016 :
    ThetaLowerSegment 2483958016 2484089088 (248389955021027 / 100000)
      (248403060353007 / 100000) := by
  exact
    packedTile65536 2483958016 2484089088 14 6058 49839 31 _ _ (216331 / 10000) (2163313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2484089088 :
    ThetaLowerSegment 2484089088 2484220160 (248403060353007 / 100000)
      (248415942899787 / 100000) := by
  exact
    packedTile65536 2484089088 2484220160 14 5955 49840 31 _ _ (540829 / 25000) (2163319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2484220160 :
    ThetaLowerSegment 2484220160 2484351232 (248415942899787 / 100000)
      (31053621031941 / 12500) := by
  exact
    packedTile65536 2484220160 2484351232 14 6021 49841 31 _ _ (2163321 / 100000) (540831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2484351232 :
    ThetaLowerSegment 2484351232 2484482304 (31053621031941 / 12500) (124221076863749 / 50000) := by
  exact
    packedTile65536 2484351232 2484482304 14 6095 49843 31 _ _ (1081663 / 50000) (2163329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2484482304 :
    ThetaLowerSegment 2484482304 2484613376 (124221076863749 / 50000)
      (124227624188047 / 50000) := by
  exact
    packedTile65536 2484482304 2484613376 14 6053 49844 31 _ _ (540833 / 25000) (432667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2484613376 :
    ThetaLowerSegment 2484613376 2484744448 (124227624188047 / 50000)
      (124234196405853 / 50000) := by
  exact
    packedTile65536 2484613376 2484744448 14 6076 49845 31 _ _ (2163337 / 100000) (108167 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2484744448 :
    ThetaLowerSegment 2484744448 2484875520 (124234196405853 / 50000) (62120420555403 / 25000) := by
  exact
    packedTile65536 2484744448 2484875520 14 6143 49847 31 _ _ (1081671 / 50000) (432669 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2484875520 :
    ThetaLowerSegment 2484875520 2485006592 (62120420555403 / 25000) (62123739129701 / 25000) := by
  exact
    packedTile65536 2484875520 2485006592 14 6136 49848 31 _ _ (2163347 / 100000) (43267 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2485006592 :
    ThetaLowerSegment 2485006592 2485137664 (62123739129701 / 25000) (24850802749763 / 10000) := by
  exact
    packedTile65536 2485006592 2485137664 14 6042 49849 31 _ _ (2163353 / 100000) (540839 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2485137664 :
    ThetaLowerSegment 2485137664 2485268736 (24850802749763 / 10000) (62130250288889 / 25000) := by
  exact
    packedTile65536 2485137664 2485268736 14 5997 49851 31 _ _ (1081679 / 50000) (2163361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2485268736 :
    ThetaLowerSegment 2485268736 2485399808 (62130250288889 / 25000) (49706853812167 / 20000) := by
  exact
    packedTile65536 2485268736 2485399808 14 6133 49852 31 _ _ (2163363 / 100000) (1081683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2485399808 :
    ThetaLowerSegment 2485399808 2485530880 (49706853812167 / 20000)
      (248547175714323 / 100000) := by
  exact
    packedTile65536 2485399808 2485530880 14 5966 49853 31 _ _ (270421 / 12500) (2163371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2485530880 :
    ThetaLowerSegment 2485530880 2485661952 (248547175714323 / 100000)
      (49712043306559 / 20000) := by
  exact
    packedTile65536 2485530880 2485661952 14 6028 49855 31 _ _ (1081687 / 50000) (2163377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2485661952 :
    ThetaLowerSegment 2485661952 2485793024 (49712043306559 / 20000) (24857325089127 / 10000) := by
  exact
    packedTile65536 2485661952 2485793024 14 6025 49856 31 _ _ (2163379 / 100000) (1081691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2485793024 :
    ThetaLowerSegment 2485793024 2485924096 (24857325089127 / 10000) (124293129659631 / 50000) := by
  exact
    packedTile65536 2485793024 2485924096 14 6013 49857 31 _ _ (270423 / 12500) (2163387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2485924096 :
    ThetaLowerSegment 2485924096 2486055168 (124293129659631 / 50000)
      (124299667424211 / 50000) := by
  exact
    packedTile65536 2485924096 2486055168 14 6044 49859 31 _ _ (216339 / 10000) (2163393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2486055168 :
    ThetaLowerSegment 2486055168 2486186240 (124299667424211 / 50000) (62153101520253 / 25000) := by
  exact
    packedTile65536 2486055168 2486186240 14 6042 49860 31 _ _ (432679 / 20000) (1081699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2486186240 :
    ThetaLowerSegment 2486186240 2486317312 (62153101520253 / 25000) (62156359059803 / 25000) := by
  exact
    packedTile65536 2486186240 2486317312 14 6023 49861 31 _ _ (10817 / 500) (2163403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2486317312 :
    ThetaLowerSegment 2486317312 2486448384 (62156359059803 / 25000) (124319305687831 / 50000) := by
  exact
    packedTile65536 2486317312 2486448384 14 6090 49862 31 _ _ (432681 / 20000) (135213 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2486448384 :
    ThetaLowerSegment 2486448384 2486579456 (124319305687831 / 50000)
      (124325834862229 / 50000) := by
  exact
    packedTile65536 2486448384 2486579456 14 6036 49864 31 _ _ (2163411 / 100000) (1081707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2486579456 :
    ThetaLowerSegment 2486579456 2486710528 (124325834862229 / 50000) (24866486007181 / 10000) := by
  exact
    packedTile65536 2486579456 2486710528 14 6097 49865 31 _ _ (270427 / 12500) (2163419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2486710528 :
    ThetaLowerSegment 2486710528 2486841600 (24866486007181 / 10000)
      (248678028815437 / 100000) := by
  exact
    packedTile65536 2486710528 2486841600 14 6087 49866 31 _ _ (2163421 / 100000) (67607 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2486841600 :
    ThetaLowerSegment 2486841600 2486972672 (248678028815437 / 100000)
      (248691020188567 / 100000) := by
  exact
    packedTile65536 2486841600 2486972672 14 6005 49868 31 _ _ (1081713 / 50000) (2163429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2486972672 :
    ThetaLowerSegment 2486972672 2487103744 (248691020188567 / 100000)
      (248703979146247 / 100000) := by
  exact
    packedTile65536 2486972672 2487103744 14 5990 49869 31 _ _ (270429 / 12500) (432687 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2487103744 :
    ThetaLowerSegment 2487103744 2487234816 (248703979146247 / 100000)
      (248717046305727 / 100000) := by
  exact
    packedTile65536 2487103744 2487234816 14 6040 49870 31 _ _ (2163437 / 100000) (27043 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2487234816 :
    ThetaLowerSegment 2487234816 2487365888 (248717046305727 / 100000)
      (248730301714861 / 100000) := by
  exact
    packedTile65536 2487234816 2487365888 14 6127 49872 31 _ _ (1081721 / 50000) (432689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2487365888 :
    ThetaLowerSegment 2487365888 2487496960 (248730301714861 / 100000)
      (49748672922777 / 20000) := by
  exact
    packedTile65536 2487365888 2487496960 14 6038 49873 31 _ _ (270431 / 12500) (2163451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2487496960 :
    ThetaLowerSegment 2487496960 2487628032 (49748672922777 / 20000)
      (248756522735031 / 100000) := by
  exact
    packedTile65536 2487496960 2487628032 14 6082 49874 31 _ _ (2163453 / 100000) (67608 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2487628032 :
    ThetaLowerSegment 2487628032 2487759104 (248756522735031 / 100000)
      (248769652761633 / 100000) := by
  exact
    packedTile65536 2487628032 2487759104 14 6069 49876 31 _ _ (1081729 / 50000) (2163461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2487759104 :
    ThetaLowerSegment 2487759104 2487890176 (248769652761633 / 100000)
      (248782611905003 / 100000) := by
  exact
    packedTile65536 2487759104 2487890176 14 5990 49877 31 _ _ (2163463 / 100000) (1081733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2487890176 :
    ThetaLowerSegment 2487890176 2488021248 (248782611905003 / 100000)
      (248795839354469 / 100000) := by
  exact
    packedTile65536 2487890176 2488021248 14 6114 49878 31 _ _ (2163469 / 100000) (135217 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2488021248 :
    ThetaLowerSegment 2488021248 2488152320 (248795839354469 / 100000)
      (49761774424369 / 20000) := by
  exact
    packedTile65536 2488021248 2488152320 14 6024 49880 31 _ _ (1081737 / 50000) (2163477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2488152320 :
    ThetaLowerSegment 2488152320 2488283392 (49761774424369 / 20000) (124410938397057 / 50000) := by
  exact
    packedTile65536 2488152320 2488283392 14 6011 49881 31 _ _ (2163479 / 100000) (1081741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2488283392 :
    ThetaLowerSegment 2488283392 2488414464 (124410938397057 / 50000) (24883482308237 / 10000) := by
  exact
    packedTile65536 2488283392 2488414464 14 5984 49882 31 _ _ (540871 / 25000) (2163487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2488414464 :
    ThetaLowerSegment 2488414464 2488545536 (24883482308237 / 10000) (24884800739043 / 10000) := by
  exact
    packedTile65536 2488414464 2488545536 14 6094 49884 31 _ _ (216349 / 10000) (2163493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2488545536 :
    ThetaLowerSegment 2488545536 2488676608 (24884800739043 / 10000) (9954445678743 / 4000) := by
  exact
    packedTile65536 2488545536 2488676608 14 6071 49885 31 _ _ (432699 / 20000) (1081749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2488676608 :
    ThetaLowerSegment 2488676608 2488807680 (9954445678743 / 4000) (9954978851683 / 4000) := by
  exact
    packedTile65536 2488676608 2488807680 14 6161 49886 31 _ _ (4327 / 200) (2163503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2488807680 :
    ThetaLowerSegment 2488807680 2488938752 (9954978851683 / 4000) (49777491329817 / 20000) := by
  exact
    packedTile65536 2488807680 2488938752 14 6002 49887 31 _ _ (432701 / 20000) (540877 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2488938752 :
    ThetaLowerSegment 2488938752 2489069824 (49777491329817 / 20000)
      (248900714644493 / 100000) := by
  exact
    packedTile65536 2488938752 2489069824 14 6128 49889 31 _ _ (2163511 / 100000) (1081757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2489069824 :
    ThetaLowerSegment 2489069824 2489200896 (248900714644493 / 100000)
      (248913715212137 / 100000) := by
  exact
    packedTile65536 2489069824 2489200896 14 6009 49890 31 _ _ (540879 / 25000) (2163519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2489200896 :
    ThetaLowerSegment 2489200896 2489331968 (248913715212137 / 100000)
      (248926834803481 / 100000) := by
  exact
    packedTile65536 2489200896 2489331968 14 6064 49891 31 _ _ (2163521 / 100000) (540881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2489331968 :
    ThetaLowerSegment 2489331968 2489463040 (248926834803481 / 100000)
      (124469876611599 / 50000) := by
  exact
    packedTile65536 2489331968 2489463040 14 5971 49893 31 _ _ (2163527 / 100000) (216353 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2489463040 :
    ThetaLowerSegment 2489463040 2489594112 (124469876611599 / 50000)
      (124476387761153 / 50000) := by
  exact
    packedTile65536 2489463040 2489594112 14 6019 49894 31 _ _ (540883 / 25000) (432707 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2489594112 :
    ThetaLowerSegment 2489594112 2489725184 (124476387761153 / 50000)
      (124482908661671 / 50000) := by
  exact
    packedTile65536 2489594112 2489725184 14 6028 49895 31 _ _ (2163537 / 100000) (108177 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2489725184 :
    ThetaLowerSegment 2489725184 2489856256 (124482908661671 / 50000) (62244708838889 / 25000) := by
  exact
    packedTile65536 2489725184 2489856256 14 6017 49897 31 _ _ (1081771 / 50000) (432709 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2489856256 :
    ThetaLowerSegment 2489856256 2489987328 (62244708838889 / 25000) (2489919854003 / 1000) := by
  exact
    packedTile65536 2489856256 2489987328 14 6078 49898 31 _ _ (540887 / 25000) (2163551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2489987328 :
    ThetaLowerSegment 2489987328 2490118400 (2489919854003 / 1000) (7781414134603 / 3125) := by
  exact
    packedTile65536 2489987328 2490118400 14 6132 49899 31 _ _ (2163553 / 100000) (540889 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2490118400 :
    ThetaLowerSegment 2490118400 2490249472 (7781414134603 / 3125) (12450909302851 / 5000) := by
  exact
    packedTile65536 2490118400 2490249472 14 5978 49901 31 _ _ (1081779 / 50000) (2163561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2490249472 :
    ThetaLowerSegment 2490249472 2490380544 (12450909302851 / 5000) (249031217196969 / 100000) := by
  exact
    packedTile65536 2490249472 2490380544 14 6023 49902 31 _ _ (2163563 / 100000) (1081783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2490380544 :
    ThetaLowerSegment 2490380544 2490511616 (249031217196969 / 100000)
      (124522199911443 / 50000) := by
  exact
    packedTile65536 2490380544 2490511616 14 6093 49903 31 _ _ (2163569 / 100000) (540893 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2490511616 :
    ThetaLowerSegment 2490511616 2490642688 (124522199911443 / 50000) (1556608511217 / 625) := by
  exact
    packedTile65536 2490511616 2490642688 14 5991 49905 31 _ _ (1081787 / 50000) (2163577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2490642688 :
    ThetaLowerSegment 2490642688 2490773760 (1556608511217 / 625) (249070531500093 / 100000) := by
  exact
    packedTile65536 2490642688 2490773760 14 6087 49906 31 _ _ (2163579 / 100000) (1081791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2490773760 :
    ThetaLowerSegment 2490773760 2490904832 (249070531500093 / 100000)
      (49816708226137 / 20000) := by
  exact
    packedTile65536 2490773760 2490904832 14 6013 49907 31 _ _ (67612 / 3125) (2163587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2490904832 :
    ThetaLowerSegment 2490904832 2491035904 (49816708226137 / 20000) (49819346507783 / 20000) := by
  exact
    packedTile65536 2490904832 2491035904 14 6097 49908 31 _ _ (216359 / 10000) (2163593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2491035904 :
    ThetaLowerSegment 2491035904 2491166976 (49819346507783 / 20000) (12455485164547 / 5000) := by
  exact
    packedTile65536 2491035904 2491166976 14 5995 49910 31 _ _ (432719 / 20000) (1081799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2491166976 :
    ThetaLowerSegment 2491166976 2491298048 (12455485164547 / 5000) (12456139004467 / 5000) := by
  exact
    packedTile65536 2491166976 2491298048 14 6044 49911 31 _ _ (5409 / 250) (2163603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2491298048 :
    ThetaLowerSegment 2491298048 2491429120 (12456139004467 / 5000) (9965438863561 / 4000) := by
  exact
    packedTile65536 2491298048 2491429120 14 6097 49912 31 _ _ (432721 / 20000) (270451 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2491429120 :
    ThetaLowerSegment 2491429120 2491560192 (9965438863561 / 4000) (62287247509103 / 25000) := by
  exact
    packedTile65536 2491429120 2491560192 14 6017 49914 31 _ _ (2163611 / 100000) (1081807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2491560192 :
    ThetaLowerSegment 2491560192 2491691264 (62287247509103 / 25000) (62290550809831 / 25000) := by
  exact
    packedTile65536 2491560192 2491691264 14 6107 49915 31 _ _ (67613 / 3125) (2163619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2491691264 :
    ThetaLowerSegment 2491691264 2491822336 (62290550809831 / 25000) (49835054734757 / 20000) := by
  exact
    packedTile65536 2491691264 2491822336 14 6041 49916 31 _ _ (2163621 / 100000) (270453 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2491822336 :
    ThetaLowerSegment 2491822336 2491953408 (49835054734757 / 20000)
      (249188367944389 / 100000) := by
  exact
    packedTile65536 2491822336 2491953408 14 6052 49918 31 _ _ (2163627 / 100000) (216363 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2491953408 :
    ThetaLowerSegment 2491953408 2492084480 (249188367944389 / 100000)
      (249201481717941 / 100000) := by
  exact
    packedTile65536 2491953408 2492084480 14 6061 49919 31 _ _ (135227 / 6250) (432727 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2492084480 :
    ThetaLowerSegment 2492084480 2492215552 (249201481717941 / 100000)
      (249214420267201 / 100000) := by
  exact
    packedTile65536 2492084480 2492215552 14 5980 49920 31 _ _ (2163637 / 100000) (54091 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2492215552 :
    ThetaLowerSegment 2492215552 2492346624 (249214420267201 / 100000)
      (49845483452939 / 20000) := by
  exact
    packedTile65536 2492215552 2492346624 14 6007 49922 31 _ _ (1081821 / 50000) (432729 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2492346624 :
    ThetaLowerSegment 2492346624 2492477696 (49845483452939 / 20000)
      (249240622008439 / 100000) := by
  exact
    packedTile65536 2492346624 2492477696 14 6103 49923 31 _ _ (67614 / 3125) (2163651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2492477696 :
    ThetaLowerSegment 2492477696 2492608768 (249240622008439 / 100000) (12462686362733 / 5000) := by
  exact
    packedTile65536 2492477696 2492608768 14 6057 49924 31 _ _ (2163653 / 100000) (270457 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2492608768 :
    ThetaLowerSegment 2492608768 2492739840 (12462686362733 / 5000) (124633507139219 / 50000) := by
  exact
    packedTile65536 2492608768 2492739840 14 6141 49926 31 _ _ (1081829 / 50000) (2163661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2492739840 :
    ThetaLowerSegment 2492739840 2492870912 (124633507139219 / 50000) (31160007645791 / 12500) := by
  exact
    packedTile65536 2492739840 2492870912 14 6030 49927 31 _ _ (2163663 / 100000) (1081833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2492870912 :
    ThetaLowerSegment 2492870912 2493001984 (31160007645791 / 12500) (7790407058468 / 3125) := by
  exact
    packedTile65536 2492870912 2493001984 14 5992 49928 31 _ _ (2163669 / 100000) (270459 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2493001984 :
    ThetaLowerSegment 2493001984 2493133056 (7790407058468 / 3125) (124653076440567 / 50000) := by
  exact
    packedTile65536 2493001984 2493133056 14 6067 49929 31 _ _ (1081837 / 50000) (2163677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2493133056 :
    ThetaLowerSegment 2493133056 2493264128 (124653076440567 / 50000)
      (249319301558417 / 100000) := by
  exact
    packedTile65536 2493133056 2493264128 14 6077 49931 31 _ _ (2163679 / 100000) (1081841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2493264128 :
    ThetaLowerSegment 2493264128 2493395200 (249319301558417 / 100000)
      (249332593069229 / 100000) := by
  exact
    packedTile65536 2493264128 2493395200 14 6143 49932 31 _ _ (540921 / 25000) (2163687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2493395200 :
    ThetaLowerSegment 2493395200 2493526272 (249332593069229 / 100000)
      (249345646610999 / 100000) := by
  exact
    packedTile65536 2493395200 2493526272 14 6033 49933 31 _ _ (216369 / 10000) (2163693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2493526272 :
    ThetaLowerSegment 2493526272 2493657344 (249345646610999 / 100000)
      (249358806203989 / 100000) := by
  exact
    packedTile65536 2493526272 2493657344 14 6082 49935 31 _ _ (432739 / 20000) (1081849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2493657344 :
    ThetaLowerSegment 2493657344 2493788416 (249358806203989 / 100000)
      (249371846823889 / 100000) := by
  exact
    packedTile65536 2493657344 2493788416 14 6027 49936 31 _ _ (21637 / 1000) (2163703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2493788416 :
    ThetaLowerSegment 2493788416 2493919488 (249371846823889 / 100000)
      (249384950221369 / 100000) := by
  exact
    packedTile65536 2493788416 2493919488 14 6056 49937 31 _ _ (432741 / 20000) (540927 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2493919488 :
    ThetaLowerSegment 2493919488 2494050560 (249384950221369 / 100000)
      (24939812938507 / 10000) := by
  exact
    packedTile65536 2493919488 2494050560 14 6091 49939 31 _ _ (2163711 / 100000) (1081857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2494050560 :
    ThetaLowerSegment 2494050560 2494181632 (24939812938507 / 10000) (124705527712227 / 50000) := by
  exact
    packedTile65536 2494050560 2494181632 14 5974 49940 31 _ _ (540929 / 25000) (2163719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2494181632 :
    ThetaLowerSegment 2494181632 2494312704 (124705527712227 / 50000) (9976970251451 / 4000) := by
  exact
    packedTile65536 2494181632 2494312704 14 6101 49941 31 _ _ (2163721 / 100000) (540931 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2494312704 :
    ThetaLowerSegment 2494312704 2494443776 (9976970251451 / 4000) (249437385775643 / 100000) := by
  exact
    packedTile65536 2494312704 2494443776 14 6068 49943 31 _ _ (1081863 / 50000) (2163729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2494443776 :
    ThetaLowerSegment 2494443776 2494574848 (249437385775643 / 100000)
      (249450448225727 / 100000) := by
  exact
    packedTile65536 2494443776 2494574848 14 6037 49944 31 _ _ (540933 / 25000) (432747 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2494574848 :
    ThetaLowerSegment 2494574848 2494705920 (249450448225727 / 100000)
      (124731861376111 / 50000) := by
  exact
    packedTile65536 2494574848 2494705920 14 6135 49945 31 _ _ (2163737 / 100000) (108187 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2494705920 :
    ThetaLowerSegment 2494705920 2494836992 (124731861376111 / 50000)
      (124738523537729 / 50000) := by
  exact
    packedTile65536 2494705920 2494836992 14 6158 49947 31 _ _ (1081871 / 50000) (432749 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2494836992 :
    ThetaLowerSegment 2494836992 2494968064 (124738523537729 / 50000)
      (249490170201013 / 100000) := by
  exact
    packedTile65536 2494836992 2494968064 14 6065 49948 31 _ _ (2163747 / 100000) (1731 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2494968064 :
    ThetaLowerSegment 2494968064 2495099136 (249490170201013 / 100000)
      (24950325874291 / 10000) := by
  exact
    packedTile65536 2494968064 2495099136 14 6049 49949 31 _ _ (2163753 / 100000) (540939 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2495099136 :
    ThetaLowerSegment 2495099136 2495230208 (24950325874291 / 10000) (7797379768026 / 3125) := by
  exact
    packedTile65536 2495099136 2495230208 14 5959 49950 31 _ _ (1081879 / 50000) (2163761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2495230208 :
    ThetaLowerSegment 2495230208 2495361280 (7797379768026 / 3125) (62382320572679 / 25000) := by
  exact
    packedTile65536 2495230208 2495361280 14 6068 49952 31 _ _ (2163763 / 100000) (1081883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2495361280 :
    ThetaLowerSegment 2495361280 2495492352 (62382320572679 / 25000) (62385620318879 / 25000) := by
  exact
    packedTile65536 2495361280 2495492352 14 6100 49953 31 _ _ (270471 / 12500) (2163771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2495492352 :
    ThetaLowerSegment 2495492352 2495623424 (62385620318879 / 25000) (124777761170707 / 50000) := by
  exact
    packedTile65536 2495492352 2495623424 14 6027 49954 31 _ _ (1081887 / 50000) (2163777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2495623424 :
    ThetaLowerSegment 2495623424 2495754496 (124777761170707 / 50000)
      (249568411972917 / 100000) := by
  exact
    packedTile65536 2495623424 2495754496 14 5957 49956 31 _ _ (2163779 / 100000) (1081891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2495754496 :
    ThetaLowerSegment 2495754496 2495885568 (249568411972917 / 100000)
      (249581541814229 / 100000) := by
  exact
    packedTile65536 2495754496 2495885568 14 6068 49957 31 _ _ (270473 / 12500) (2163787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2495885568 :
    ThetaLowerSegment 2495885568 2496016640 (249581541814229 / 100000)
      (249594559168853 / 100000) := by
  exact
    packedTile65536 2495885568 2496016640 14 6016 49958 31 _ _ (2163789 / 100000) (135237 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2496016640 :
    ThetaLowerSegment 2496016640 2496147712 (249594559168853 / 100000)
      (249607663111373 / 100000) := by
  exact
    packedTile65536 2496016640 2496147712 14 6056 49960 31 _ _ (432759 / 20000) (1081899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2496147712 :
    ThetaLowerSegment 2496147712 2496278784 (249607663111373 / 100000)
      (249620760592773 / 100000) := by
  exact
    packedTile65536 2496147712 2496278784 14 6053 49961 31 _ _ (10819 / 500) (2163803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2496278784 :
    ThetaLowerSegment 2496278784 2496409856 (249620760592773 / 100000)
      (249633769388433 / 100000) := by
  exact
    packedTile65536 2496278784 2496409856 14 6012 49962 31 _ _ (432761 / 20000) (67619 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2496409856 :
    ThetaLowerSegment 2496409856 2496540928 (249633769388433 / 100000)
      (249646819326543 / 100000) := by
  exact
    packedTile65536 2496409856 2496540928 14 6031 49964 31 _ _ (216381 / 10000) (2163813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2496540928 :
    ThetaLowerSegment 2496540928 2496672000 (249646819326543 / 100000)
      (249659973164007 / 100000) := by
  exact
    packedTile65536 2496540928 2496672000 14 6079 49965 31 _ _ (270477 / 12500) (2163819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2496672000 :
    ThetaLowerSegment 2496672000 2496803072 (249659973164007 / 100000)
      (249673077263983 / 100000) := by
  exact
    packedTile65536 2496672000 2496803072 14 6056 49966 31 _ _ (2163821 / 100000) (135239 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2496803072 :
    ThetaLowerSegment 2496803072 2496934144 (249673077263983 / 100000)
      (249686192213369 / 100000) := by
  exact
    packedTile65536 2496803072 2496934144 14 6061 49968 31 _ _ (1081913 / 50000) (2163829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2496934144 :
    ThetaLowerSegment 2496934144 2497065216 (249686192213369 / 100000)
      (249699322339877 / 100000) := by
  exact
    packedTile65536 2496934144 2497065216 14 6068 49969 31 _ _ (2163831 / 100000) (1081917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2497065216 :
    ThetaLowerSegment 2497065216 2497196288 (249699322339877 / 100000)
      (49942475786467 / 20000) := by
  exact
    packedTile65536 2497065216 2497196288 14 6034 49970 31 _ _ (2163837 / 100000) (13524 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2497196288 :
    ThetaLowerSegment 2497196288 2497327360 (49942475786467 / 20000)
      (249725493978697 / 100000) := by
  exact
    packedTile65536 2497196288 2497327360 14 6061 49971 31 _ _ (1081921 / 50000) (432769 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2497327360 :
    ThetaLowerSegment 2497327360 2497458432 (249725493978697 / 100000)
      (249738663151539 / 100000) := by
  exact
    packedTile65536 2497327360 2497458432 14 6086 49973 31 _ _ (2163847 / 100000) (43277 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2497458432 :
    ThetaLowerSegment 2497458432 2497589504 (249738663151539 / 100000)
      (249751579184127 / 100000) := by
  exact
    packedTile65536 2497458432 2497589504 14 5969 49974 31 _ _ (540963 / 25000) (432771 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2497589504 :
    ThetaLowerSegment 2497589504 2497720576 (249751579184127 / 100000)
      (249764804684223 / 100000) := by
  exact
    packedTile65536 2497589504 2497720576 14 6112 49975 31 _ _ (1081929 / 50000) (2163861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2497720576 :
    ThetaLowerSegment 2497720576 2497851648 (249764804684223 / 100000)
      (62444470227083 / 25000) := by
  exact
    packedTile65536 2497720576 2497851648 14 6043 49977 31 _ _ (2163863 / 100000) (1081933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2497851648 :
    ThetaLowerSegment 2497851648 2497982720 (62444470227083 / 25000) (62447720356819 / 25000) := by
  exact
    packedTile65536 2497851648 2497982720 14 6008 49978 31 _ _ (540967 / 25000) (2163871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2497982720 :
    ThetaLowerSegment 2497982720 2498113792 (62447720356819 / 25000) (49960813181093 / 20000) := by
  exact
    packedTile65536 2497982720 2498113792 14 6093 49979 31 _ _ (2163873 / 100000) (540969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2498113792 :
    ThetaLowerSegment 2498113792 2498244864 (49960813181093 / 20000) (124908549474341 / 50000) := by
  exact
    packedTile65536 2498113792 2498244864 14 6023 49981 31 _ _ (2163879 / 100000) (1081941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2498244864 :
    ThetaLowerSegment 2498244864 2498375936 (124908549474341 / 50000)
      (124915074666543 / 50000) := by
  exact
    packedTile65536 2498244864 2498375936 14 6031 49982 31 _ _ (540971 / 25000) (2163887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2498375936 :
    ThetaLowerSegment 2498375936 2498507008 (124915074666543 / 50000)
      (249843325253207 / 100000) := by
  exact
    packedTile65536 2498375936 2498507008 14 6089 49983 31 _ _ (2163889 / 100000) (540973 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2498507008 :
    ThetaLowerSegment 2498507008 2498638080 (249843325253207 / 100000)
      (249856527170501 / 100000) := by
  exact
    packedTile65536 2498507008 2498638080 14 6101 49985 31 _ _ (1081947 / 50000) (2163897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2498638080 :
    ThetaLowerSegment 2498638080 2498769152 (249856527170501 / 100000)
      (249869590634801 / 100000) := by
  exact
    packedTile65536 2498638080 2498769152 14 6037 49986 31 _ _ (21639 / 1000) (2163903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2498769152 :
    ThetaLowerSegment 2498769152 2498900224 (249869590634801 / 100000)
      (249882548097941 / 100000) := by
  exact
    packedTile65536 2498769152 2498900224 14 5988 49987 31 _ _ (432781 / 20000) (540977 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2498900224 :
    ThetaLowerSegment 2498900224 2499031296 (249882548097941 / 100000)
      (249895667884271 / 100000) := by
  exact
    packedTile65536 2498900224 2499031296 14 6063 49989 31 _ _ (216391 / 10000) (2163913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2499031296 :
    ThetaLowerSegment 2499031296 2499162368 (249895667884271 / 100000)
      (249908997600671 / 100000) := by
  exact
    packedTile65536 2499031296 2499162368 14 6160 49990 31 _ _ (432783 / 20000) (1081959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2499162368 :
    ThetaLowerSegment 2499162368 2499293440 (249908997600671 / 100000)
      (249922089322721 / 100000) := by
  exact
    packedTile65536 2499162368 2499293440 14 6050 49991 31 _ _ (2163921 / 100000) (540981 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2499293440 :
    ThetaLowerSegment 2499293440 2499424512 (249922089322721 / 100000)
      (49987035782219 / 20000) := by
  exact
    packedTile65536 2499293440 2499424512 14 6049 49992 31 _ _ (1081963 / 50000) (2163929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2499424512 :
    ThetaLowerSegment 2499424512 2499555584 (49987035782219 / 20000) (49989649810867 / 20000) := by
  exact
    packedTile65536 2499424512 2499555584 14 6040 49994 31 _ _ (2163931 / 100000) (1081967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2499555584 :
    ThetaLowerSegment 2499555584 2499686656 (49989649810867 / 20000)
      (249961278112991 / 100000) := by
  exact
    packedTile65536 2499555584 2499686656 14 6021 49995 31 _ _ (67623 / 3125) (2163939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2499686656 :
    ThetaLowerSegment 2499686656 2499817728 (249961278112991 / 100000)
      (249974289896237 / 100000) := by
  exact
    packedTile65536 2499686656 2499817728 14 6013 49996 31 _ _ (1081971 / 50000) (432789 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2499817728 :
    ThetaLowerSegment 2499817728 2499948800 (249974289896237 / 100000)
      (249987546235559 / 100000) := by
  exact
    packedTile65536 2499817728 2499948800 14 6126 49998 31 _ _ (2163947 / 100000) (43279 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2499948800 :
    ThetaLowerSegment 2499948800 2500079872 (249987546235559 / 100000)
      (50000122435547 / 20000) := by
  exact
    packedTile65536 2499948800 2500079872 14 6038 49999 31 _ _ (135247 / 6250) (432791 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2500079872 :
    ThetaLowerSegment 2500079872 2500210944 (50000122435547 / 20000) (1250068466489 / 500) := by
  exact
    packedTile65536 2500079872 2500210944 14 6045 50000 31 _ _ (2163957 / 100000) (54099 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2500210944 :
    ThetaLowerSegment 2500210944 2500342016 (1250068466489 / 500) (125013409948679 / 50000) := by
  exact
    packedTile65536 2500210944 2500342016 14 6066 50002 31 _ _ (2163963 / 100000) (1081983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2500342016 :
    ThetaLowerSegment 2500342016 2500473088 (125013409948679 / 50000) (1000159379283 / 400) := by
  exact
    packedTile65536 2500342016 2500473088 14 6019 50003 31 _ _ (67624 / 3125) (2163971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2500473088 :
    ThetaLowerSegment 2500473088 2500604160 (1000159379283 / 400) (250052770231479 / 100000) := by
  exact
    packedTile65536 2500473088 2500604160 14 5973 50004 31 _ _ (2163973 / 100000) (270497 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2500604160 :
    ThetaLowerSegment 2500604160 2500735232 (250052770231479 / 100000)
      (250065987809103 / 100000) := by
  exact
    packedTile65536 2500604160 2500735232 14 6108 50006 31 _ _ (1081989 / 50000) (2163981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2500735232 :
    ThetaLowerSegment 2500735232 2500866304 (250065987809103 / 100000)
      (250079136175887 / 100000) := by
  exact
    packedTile65536 2500735232 2500866304 14 6076 50007 31 _ _ (135249 / 6250) (2163987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2500866304 :
    ThetaLowerSegment 2500866304 2500997376 (250079136175887 / 100000) (10003688439897 / 4000) := by
  exact
    packedTile65536 2500866304 2500997376 14 6042 50008 31 _ _ (2163989 / 100000) (270499 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2500997376 :
    ThetaLowerSegment 2500997376 2501128448 (10003688439897 / 4000) (10004214290439 / 4000) := by
  exact
    packedTile65536 2500997376 2501128448 14 6075 50009 31 _ _ (1081997 / 50000) (2163997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2501128448 :
    ThetaLowerSegment 2501128448 2501259520 (10004214290439 / 4000) (250118561982873 / 100000) := by
  exact
    packedTile65536 2501128448 2501259520 14 6102 50011 31 _ _ (2163999 / 100000) (1082001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2501259520 :
    ThetaLowerSegment 2501259520 2501390592 (250118561982873 / 100000)
      (250131481092723 / 100000) := by
  exact
    packedTile65536 2501259520 2501390592 14 5970 50012 31 _ _ (432801 / 20000) (270501 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2501390592 :
    ThetaLowerSegment 2501390592 2501521664 (250131481092723 / 100000)
      (250144573353223 / 100000) := by
  exact
    packedTile65536 2501390592 2501521664 14 6050 50013 31 _ _ (216401 / 10000) (2164013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2501521664 :
    ThetaLowerSegment 2501521664 2501652736 (250144573353223 / 100000)
      (125078818755889 / 50000) := by
  exact
    packedTile65536 2501521664 2501652736 14 6037 50015 31 _ _ (432803 / 20000) (1082009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2501652736 :
    ThetaLowerSegment 2501652736 2501783808 (125078818755889 / 50000)
      (125085451477189 / 50000) := by
  exact
    packedTile65536 2501652736 2501783808 14 6130 50016 31 _ _ (108201 / 5000) (2164023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2501783808 :
    ThetaLowerSegment 2501783808 2501914880 (125085451477189 / 50000)
      (250183768083003 / 100000) := by
  exact
    packedTile65536 2501783808 2501914880 14 5945 50017 31 _ _ (86561 / 4000) (541007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2501914880 :
    ThetaLowerSegment 2501914880 2502045952 (250183768083003 / 100000) (10007875457557 / 4000) := by
  exact
    packedTile65536 2501914880 2502045952 14 6062 50019 31 _ _ (2164031 / 100000) (1082017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2502045952 :
    ThetaLowerSegment 2502045952 2502177024 (10007875457557 / 4000) (250210071910273 / 100000) := by
  exact
    packedTile65536 2502045952 2502177024 14 6093 50020 31 _ _ (541009 / 25000) (2164039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2502177024 :
    ThetaLowerSegment 2502177024 2502308096 (250210071910273 / 100000)
      (250222978250797 / 100000) := by
  exact
    packedTile65536 2502177024 2502308096 14 5964 50021 31 _ _ (2164041 / 100000) (541011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2502308096 :
    ThetaLowerSegment 2502308096 2502439168 (250222978250797 / 100000)
      (250236124830247 / 100000) := by
  exact
    packedTile65536 2502308096 2502439168 14 6075 50023 31 _ _ (1082023 / 50000) (2164049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2502439168 :
    ThetaLowerSegment 2502439168 2502570240 (250236124830247 / 100000)
      (250249178391911 / 100000) := by
  exact
    packedTile65536 2502439168 2502570240 14 6032 50024 31 _ _ (541013 / 25000) (432811 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2502570240 :
    ThetaLowerSegment 2502570240 2502701312 (250249178391911 / 100000)
      (62565552044777 / 25000) := by
  exact
    packedTile65536 2502570240 2502701312 14 6021 50025 31 _ _ (2164057 / 100000) (108203 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2502701312 :
    ThetaLowerSegment 2502701312 2502832384 (62565552044777 / 25000) (125137580045089 / 50000) := by
  exact
    packedTile65536 2502701312 2502832384 14 5985 50027 31 _ _ (1082031 / 50000) (432813 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2502832384 :
    ThetaLowerSegment 2502832384 2502963456 (125137580045089 / 50000)
      (250288345750409 / 100000) := by
  exact
    packedTile65536 2502832384 2502963456 14 6093 50028 31 _ _ (2164067 / 100000) (216407 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2502963456 :
    ThetaLowerSegment 2502963456 2503094528 (250288345750409 / 100000)
      (250301568236439 / 100000) := by
  exact
    packedTile65536 2502963456 2503094528 14 6110 50029 31 _ _ (2164073 / 100000) (541019 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2503094528 :
    ThetaLowerSegment 2503094528 2503225600 (250301568236439 / 100000)
      (250314617626779 / 100000) := by
  exact
    packedTile65536 2503094528 2503225600 14 6030 50030 31 _ _ (1082039 / 50000) (2164081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2503225600 :
    ThetaLowerSegment 2503225600 2503356672 (250314617626779 / 100000)
      (125163823785261 / 50000) := by
  exact
    packedTile65536 2503225600 2503356672 14 6021 50032 31 _ _ (2164083 / 100000) (1082043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2503356672 :
    ThetaLowerSegment 2503356672 2503487744 (125163823785261 / 50000)
      (125170377725769 / 50000) := by
  exact
    packedTile65536 2503356672 2503487744 14 6057 50033 31 _ _ (270511 / 12500) (2164091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2503487744 :
    ThetaLowerSegment 2503487744 2503618816 (125170377725769 / 50000) (25035371404641 / 10000) := by
  exact
    packedTile65536 2503487744 2503618816 14 5988 50034 31 _ _ (1082047 / 50000) (2164097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2503618816 :
    ThetaLowerSegment 2503618816 2503749888 (25035371404641 / 10000)
      (250366787368469 / 100000) := by
  exact
    packedTile65536 2503618816 2503749888 14 6041 50036 31 _ _ (2164099 / 100000) (1082051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2503749888 :
    ThetaLowerSegment 2503749888 2503880960 (250366787368469 / 100000)
      (250380174515813 / 100000) := by
  exact
    packedTile65536 2503749888 2503880960 14 6186 50037 31 _ _ (270513 / 12500) (2164107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2503880960 :
    ThetaLowerSegment 2503880960 2504012032 (250380174515813 / 100000)
      (250393115887633 / 100000) := by
  exact
    packedTile65536 2503880960 2504012032 14 5980 50038 31 _ _ (2164109 / 100000) (135257 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2504012032 :
    ThetaLowerSegment 2504012032 2504143104 (250393115887633 / 100000)
      (125203200694809 / 50000) := by
  exact
    packedTile65536 2504012032 2504143104 14 6139 50040 31 _ _ (432823 / 20000) (1082059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2504143104 :
    ThetaLowerSegment 2504143104 2504274176 (125203200694809 / 50000)
      (125209790440209 / 50000) := by
  exact
    packedTile65536 2504143104 2504274176 14 6090 50041 31 _ _ (54103 / 2500) (2164123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2504274176 :
    ThetaLowerSegment 2504274176 2504405248 (125209790440209 / 50000)
      (125216378036709 / 50000) := by
  exact
    packedTile65536 2504274176 2504405248 14 6088 50042 31 _ _ (17313 / 800) (67629 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2504405248 :
    ThetaLowerSegment 2504405248 2504536320 (125216378036709 / 50000)
      (125223021915809 / 50000) := by
  exact
    packedTile65536 2504405248 2504536320 14 6140 50044 31 _ _ (216413 / 10000) (2164133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2504536320 :
    ThetaLowerSegment 2504536320 2504667392 (125223021915809 / 50000) (15653687396483 / 6250) := by
  exact
    packedTile65536 2504536320 2504667392 14 5986 50045 31 _ _ (432827 / 20000) (1082069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2504667392 :
    ThetaLowerSegment 2504667392 2504798464 (15653687396483 / 6250) (250472058934663 / 100000) := by
  exact
    packedTile65536 2504667392 2504798464 14 6035 50046 31 _ _ (2164141 / 100000) (135259 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2504798464 :
    ThetaLowerSegment 2504798464 2504929536 (250472058934663 / 100000)
      (250485303508183 / 100000) := by
  exact
    packedTile65536 2504798464 2504929536 14 6120 50047 31 _ _ (1082073 / 50000) (2164149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2504929536 :
    ThetaLowerSegment 2504929536 2505060608 (250485303508183 / 100000)
      (250498439904753 / 100000) := by
  exact
    packedTile65536 2504929536 2505060608 14 6070 50049 31 _ _ (2164151 / 100000) (1082077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2505060608 :
    ThetaLowerSegment 2505060608 2505191680 (250498439904753 / 100000)
      (250511338274513 / 100000) := by
  exact
    packedTile65536 2505060608 2505191680 14 5960 50050 31 _ _ (541039 / 25000) (2164159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2505191680 :
    ThetaLowerSegment 2505191680 2505322752 (250511338274513 / 100000) (10020977344751 / 4000) := by
  exact
    packedTile65536 2505191680 2505322752 14 6051 50051 31 _ _ (1082081 / 50000) (432833 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2505322752 :
    ThetaLowerSegment 2505322752 2505339136 (10020977344751 / 4000) (25052613248987 / 10000) := by
  exact
    packedTile65536 2505322752 2505339136 11 785 50053 31 _ _ (2164167 / 100000) (216417 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2505339136 :
    ThetaLowerSegment 2505339136 2505341184 (25052613248987 / 10000)
      (250526307787397 / 100000) := by
  exact
    packedTile65536 2505339136 2505341184 8 81 50053 31 _ _ (2164167 / 100000) (216417 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2473341184_2505341184 :
    ThetaLowerSegment 2473341184 2505341184 (123663746553391 / 50000)
      (250526307787397 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2473341184 cell2473472256)
                  (ThetaLowerSegment.join cell2473603328 cell2473734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2473865472 cell2473996544)
                  (ThetaLowerSegment.join cell2474127616 cell2474258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2474389760 cell2474520832)
                  (ThetaLowerSegment.join cell2474651904 cell2474782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2474914048 cell2475045120)
                  (ThetaLowerSegment.join cell2475176192 cell2475307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2475438336 cell2475569408)
                  (ThetaLowerSegment.join cell2475700480 cell2475831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2475962624 cell2476093696)
                  (ThetaLowerSegment.join cell2476224768 cell2476355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2476486912 cell2476617984)
                  (ThetaLowerSegment.join cell2476749056 cell2476880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2477011200 cell2477142272)
                  (ThetaLowerSegment.join cell2477273344 cell2477404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2477535488 cell2477666560)
                  (ThetaLowerSegment.join cell2477797632 cell2477928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2478059776 cell2478190848)
                  (ThetaLowerSegment.join cell2478321920 cell2478452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2478584064 cell2478715136)
                  (ThetaLowerSegment.join cell2478846208 cell2478977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2479108352 cell2479239424)
                  (ThetaLowerSegment.join cell2479370496 cell2479501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2479632640 cell2479763712)
                  (ThetaLowerSegment.join cell2479894784 cell2480025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2480156928 cell2480288000)
                  (ThetaLowerSegment.join cell2480419072 cell2480550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2480681216 cell2480812288)
                  (ThetaLowerSegment.join cell2480943360 cell2481074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2481205504 cell2481336576)
                  (ThetaLowerSegment.join cell2481467648 cell2481598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2481729792 cell2481860864)
                  (ThetaLowerSegment.join cell2481991936 cell2482123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2482254080 cell2482385152)
                  (ThetaLowerSegment.join cell2482516224 cell2482647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2482778368 cell2482909440)
                  (ThetaLowerSegment.join cell2483040512 cell2483171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2483302656 cell2483433728)
                  (ThetaLowerSegment.join cell2483564800 cell2483695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2483826944 cell2483958016)
                  (ThetaLowerSegment.join cell2484089088 cell2484220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2484351232 cell2484482304)
                  (ThetaLowerSegment.join cell2484613376 cell2484744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2484875520 cell2485006592)
                  (ThetaLowerSegment.join cell2485137664 cell2485268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2485399808 cell2485530880)
                  (ThetaLowerSegment.join cell2485661952 cell2485793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2485924096 cell2486055168)
                  (ThetaLowerSegment.join cell2486186240 cell2486317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2486448384 cell2486579456)
                  (ThetaLowerSegment.join cell2486710528 cell2486841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2486972672 cell2487103744)
                  (ThetaLowerSegment.join cell2487234816 cell2487365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2487496960 cell2487628032)
                  (ThetaLowerSegment.join cell2487759104 cell2487890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2488021248 cell2488152320)
                  (ThetaLowerSegment.join cell2488283392 cell2488414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2488545536 cell2488676608)
                  (ThetaLowerSegment.join cell2488807680 cell2488938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2489069824 cell2489200896)
                  (ThetaLowerSegment.join cell2489331968 cell2489463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2489594112 cell2489725184)
                  (ThetaLowerSegment.join cell2489856256 cell2489987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2490118400 cell2490249472)
                  (ThetaLowerSegment.join cell2490380544 cell2490511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2490642688 cell2490773760)
                  (ThetaLowerSegment.join cell2490904832 cell2491035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2491166976 cell2491298048)
                  (ThetaLowerSegment.join cell2491429120 cell2491560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2491691264 cell2491822336)
                  (ThetaLowerSegment.join cell2491953408 cell2492084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2492215552 cell2492346624)
                  (ThetaLowerSegment.join cell2492477696 cell2492608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2492739840 cell2492870912)
                  (ThetaLowerSegment.join cell2493001984 cell2493133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2493264128 cell2493395200)
                  (ThetaLowerSegment.join cell2493526272 cell2493657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2493788416 cell2493919488)
                  (ThetaLowerSegment.join cell2494050560 cell2494181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2494312704 cell2494443776)
                  (ThetaLowerSegment.join cell2494574848 cell2494705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2494836992 cell2494968064)
                  (ThetaLowerSegment.join cell2495099136 cell2495230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2495361280 cell2495492352)
                  (ThetaLowerSegment.join cell2495623424 cell2495754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2495885568 cell2496016640)
                  (ThetaLowerSegment.join cell2496147712 cell2496278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2496409856 cell2496540928)
                  (ThetaLowerSegment.join cell2496672000 cell2496803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2496934144 cell2497065216)
                  (ThetaLowerSegment.join cell2497196288 cell2497327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2497458432 cell2497589504)
                  (ThetaLowerSegment.join cell2497720576 cell2497851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2497982720 cell2498113792)
                  (ThetaLowerSegment.join cell2498244864 cell2498375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2498507008 cell2498638080)
                  (ThetaLowerSegment.join cell2498769152 cell2498900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2499031296 cell2499162368)
                  (ThetaLowerSegment.join cell2499293440 cell2499424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2499555584 cell2499686656)
                  (ThetaLowerSegment.join cell2499817728 cell2499948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2500079872 cell2500210944)
                  (ThetaLowerSegment.join cell2500342016 cell2500473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2500604160 cell2500735232)
                  (ThetaLowerSegment.join cell2500866304 cell2500997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2501128448 cell2501259520)
                  (ThetaLowerSegment.join cell2501390592 cell2501521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2501652736 cell2501783808)
                  (ThetaLowerSegment.join cell2501914880 cell2502045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2502177024 cell2502308096)
                  (ThetaLowerSegment.join cell2502439168 cell2502570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2502701312 cell2502832384)
                  (ThetaLowerSegment.join cell2502963456 cell2503094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2503225600 cell2503356672)
                  (ThetaLowerSegment.join cell2503487744 cell2503618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2503749888 cell2503880960)
                  (ThetaLowerSegment.join cell2504012032 cell2504143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2504274176 cell2504405248)
                  (ThetaLowerSegment.join cell2504536320 cell2504667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2504798464 cell2504929536)
                (ThetaLowerSegment.join cell2505060608 cell2505191680))
              (ThetaLowerSegment.join cell2505322752 cell2505339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
