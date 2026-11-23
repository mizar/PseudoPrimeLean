/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2697341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2665341184 :
    ThetaLowerSegment 2665341184 2665472256 (8329016425604 / 3125) (133270738072757 / 50000) := by
  exact
    packedTile65536 2665341184 2665472256 14 5967 51626 31 _ _ (1085179 / 50000) (2170361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2665472256 :
    ThetaLowerSegment 2665472256 2665603328 (133270738072757 / 50000)
      (133277301250469 / 50000) := by
  exact
    packedTile65536 2665472256 2665603328 14 6048 51628 31 _ _ (2170363 / 100000) (1085183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2665603328 :
    ThetaLowerSegment 2665603328 2665734400 (133277301250469 / 50000)
      (133283845995173 / 50000) := by
  exact
    packedTile65536 2665603328 2665734400 14 6031 51629 31 _ _ (67824 / 3125) (2170371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2665734400 :
    ThetaLowerSegment 2665734400 2665865472 (133283845995173 / 50000)
      (133290391840141 / 50000) := by
  exact
    packedTile65536 2665734400 2665865472 14 6032 51630 31 _ _ (2170373 / 100000) (271297 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2665865472 :
    ThetaLowerSegment 2665865472 2665996544 (133290391840141 / 50000) (66648467222311 / 25000) := by
  exact
    packedTile65536 2665865472 2665996544 14 6029 51632 31 _ _ (1085189 / 50000) (2170381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2665996544 :
    ThetaLowerSegment 2665996544 2666127616 (66648467222311 / 25000)
      (266607006217543 / 100000) := by
  exact
    packedTile65536 2665996544 2666127616 14 6053 51633 31 _ _ (2170383 / 100000) (1085193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2666127616 :
    ThetaLowerSegment 2666127616 2666258688 (266607006217543 / 100000)
      (266619985137783 / 100000) := by
  exact
    packedTile65536 2666127616 2666258688 14 5980 51634 31 _ _ (542597 / 25000) (2170391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2666258688 :
    ThetaLowerSegment 2666258688 2666389760 (266619985137783 / 100000)
      (53326624939401 / 20000) := by
  exact
    packedTile65536 2666258688 2666389760 14 6054 51635 31 _ _ (2170393 / 100000) (542599 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2666389760 :
    ThetaLowerSegment 2666389760 2666520832 (53326624939401 / 20000)
      (266646183981771 / 100000) := by
  exact
    packedTile65536 2666389760 2666520832 14 6017 51637 31 _ _ (1085199 / 50000) (2170401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2666520832 :
    ThetaLowerSegment 2666520832 2666651904 (266646183981771 / 100000)
      (266659262830249 / 100000) := by
  exact
    packedTile65536 2666520832 2666651904 14 6026 51638 31 _ _ (2170403 / 100000) (1085203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2666651904 :
    ThetaLowerSegment 2666651904 2666782976 (266659262830249 / 100000)
      (133336250071271 / 50000) := by
  exact
    packedTile65536 2666651904 2666782976 14 6099 51639 31 _ _ (2170407 / 100000) (217041 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2666782976 :
    ThetaLowerSegment 2666782976 2666914048 (133336250071271 / 50000)
      (133342691854087 / 50000) := by
  exact
    packedTile65536 2666782976 2666914048 14 5936 51640 31 _ _ (542603 / 25000) (434083 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2666914048 :
    ThetaLowerSegment 2666914048 2667045120 (133342691854087 / 50000) (66674656898177 / 25000) := by
  exact
    packedTile65536 2666914048 2667045120 14 6102 51642 31 _ _ (2170417 / 100000) (108521 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2667045120 :
    ThetaLowerSegment 2667045120 2667176192 (66674656898177 / 25000) (33338975256781 / 12500) := by
  exact
    packedTile65536 2667045120 2667176192 14 6070 51643 31 _ _ (1085211 / 50000) (86817 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2667176192 :
    ThetaLowerSegment 2667176192 2667307264 (33338975256781 / 12500) (133362479591361 / 50000) := by
  exact
    packedTile65536 2667176192 2667307264 14 6062 51644 31 _ _ (2170427 / 100000) (217043 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2667307264 :
    ThetaLowerSegment 2667307264 2667438336 (133362479591361 / 50000)
      (133368942052641 / 50000) := by
  exact
    packedTile65536 2667307264 2667438336 14 5955 51645 31 _ _ (67826 / 3125) (434087 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2667438336 :
    ThetaLowerSegment 2667438336 2667569408 (133368942052641 / 50000)
      (266751091214427 / 100000) := by
  exact
    packedTile65536 2667438336 2667569408 14 6085 51647 31 _ _ (2170437 / 100000) (54261 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2667569408 :
    ThetaLowerSegment 2667569408 2667700480 (266751091214427 / 100000)
      (53352822339197 / 20000) := by
  exact
    packedTile65536 2667569408 2667700480 14 5999 51648 31 _ _ (1085221 / 50000) (434089 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2667700480 :
    ThetaLowerSegment 2667700480 2667831552 (53352822339197 / 20000) (133388609512709 / 50000) := by
  exact
    packedTile65536 2667700480 2667831552 14 6039 51649 31 _ _ (2170447 / 100000) (43409 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2667831552 :
    ThetaLowerSegment 2667831552 2667962624 (133388609512709 / 50000)
      (133395184897043 / 50000) := by
  exact
    packedTile65536 2667831552 2667962624 14 6059 51651 31 _ _ (542613 / 25000) (434091 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2667962624 :
    ThetaLowerSegment 2667962624 2668093696 (133395184897043 / 50000)
      (266803533615791 / 100000) := by
  exact
    packedTile65536 2667962624 2668093696 14 6065 51652 31 _ _ (2170457 / 100000) (108523 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2668093696 :
    ThetaLowerSegment 2668093696 2668224768 (266803533615791 / 100000)
      (266816671422277 / 100000) := by
  exact
    packedTile65536 2668093696 2668224768 14 6053 51653 31 _ _ (1085231 / 50000) (434093 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2668224768 :
    ThetaLowerSegment 2668224768 2668355840 (266816671422277 / 100000)
      (266829817934839 / 100000) := by
  exact
    packedTile65536 2668224768 2668355840 14 6057 51654 31 _ _ (1085233 / 50000) (2170469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2668355840 :
    ThetaLowerSegment 2668355840 2668486912 (266829817934839 / 100000)
      (133421512625437 / 50000) := by
  exact
    packedTile65536 2668355840 2668486912 14 6085 51656 31 _ _ (2170471 / 100000) (1085237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2668486912 :
    ThetaLowerSegment 2668486912 2668617984 (133421512625437 / 50000)
      (133428124980571 / 50000) := by
  exact
    packedTile65536 2668486912 2668617984 14 6093 51657 31 _ _ (542619 / 25000) (2170479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2668617984 :
    ThetaLowerSegment 2668617984 2668749056 (133428124980571 / 50000)
      (133434640764533 / 50000) := by
  exact
    packedTile65536 2668617984 2668749056 14 6004 51658 31 _ _ (2170481 / 100000) (542621 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2668749056 :
    ThetaLowerSegment 2668749056 2668880128 (133434640764533 / 50000)
      (133441204314197 / 50000) := by
  exact
    packedTile65536 2668749056 2668880128 14 6048 51659 31 _ _ (1085243 / 50000) (2170489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2668880128 :
    ThetaLowerSegment 2668880128 2669011200 (133441204314197 / 50000) (66723852467371 / 25000) := by
  exact
    packedTile65536 2668880128 2669011200 14 5990 51661 31 _ _ (2170491 / 100000) (1085247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2669011200 :
    ThetaLowerSegment 2669011200 2669142272 (66723852467371 / 25000) (66727104413003 / 25000) := by
  exact
    packedTile65536 2669011200 2669142272 14 5993 51662 31 _ _ (67828 / 3125) (2170499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2669142272 :
    ThetaLowerSegment 2669142272 2669273344 (66727104413003 / 25000) (53384298115907 / 20000) := by
  exact
    packedTile65536 2669142272 2669273344 14 6023 51663 31 _ _ (2170501 / 100000) (271313 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2669273344 :
    ThetaLowerSegment 2669273344 2669404416 (53384298115907 / 20000)
      (266934713302087 / 100000) := by
  exact
    packedTile65536 2669273344 2669404416 14 6092 51665 31 _ _ (1085253 / 50000) (2170509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2669404416 :
    ThetaLowerSegment 2669404416 2669535488 (266934713302087 / 100000) (2135581161653 / 800) := by
  exact
    packedTile65536 2669404416 2669535488 14 5958 51666 31 _ _ (2170511 / 100000) (1085257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2669535488 :
    ThetaLowerSegment 2669535488 2669666560 (2135581161653 / 800) (266960757293781 / 100000) := by
  exact
    packedTile65536 2669535488 2669666560 14 6041 51667 31 _ _ (542629 / 25000) (2170519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2669666560 :
    ThetaLowerSegment 2669666560 2669797632 (266960757293781 / 100000)
      (266973973590061 / 100000) := by
  exact
    packedTile65536 2669666560 2669797632 14 6089 51668 31 _ _ (54263 / 2500) (2170523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2669797632 :
    ThetaLowerSegment 2669797632 2669928704 (266973973590061 / 100000)
      (133493529842643 / 50000) := by
  exact
    packedTile65536 2669797632 2669928704 14 6029 51670 31 _ _ (86821 / 4000) (67829 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2669928704 :
    ThetaLowerSegment 2669928704 2670059776 (133493529842643 / 50000)
      (133500104378013 / 50000) := by
  exact
    packedTile65536 2669928704 2670059776 14 6058 51671 31 _ _ (217053 / 10000) (2170533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2670059776 :
    ThetaLowerSegment 2670059776 2670190848 (133500104378013 / 50000) (66753363340149 / 25000) := by
  exact
    packedTile65536 2670059776 2670190848 14 6102 51672 31 _ _ (434107 / 20000) (1085269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2670190848 :
    ThetaLowerSegment 2670190848 2670321920 (66753363340149 / 25000) (33378327753347 / 12500) := by
  exact
    packedTile65536 2670190848 2670321920 14 6067 51673 31 _ _ (108527 / 5000) (2170543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2670321920 :
    ThetaLowerSegment 2670321920 2670452992 (33378327753347 / 12500) (8344990543433 / 3125) := by
  exact
    packedTile65536 2670321920 2670452992 14 6024 51675 31 _ _ (434109 / 20000) (542637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2670452992 :
    ThetaLowerSegment 2670452992 2670584064 (8344990543433 / 3125) (66763189939939 / 25000) := by
  exact
    packedTile65536 2670452992 2670584064 14 6018 51676 31 _ _ (43411 / 2000) (2170553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2670584064 :
    ThetaLowerSegment 2670584064 2670715136 (66763189939939 / 25000)
      (267065924175831 / 100000) := by
  exact
    packedTile65536 2670584064 2670715136 14 6065 51677 31 _ _ (434111 / 20000) (1085279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2670715136 :
    ThetaLowerSegment 2670715136 2670846208 (267065924175831 / 100000)
      (267078832496151 / 100000) := by
  exact
    packedTile65536 2670715136 2670846208 14 5947 51678 31 _ _ (13566 / 625) (2170563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2670846208 :
    ThetaLowerSegment 2670846208 2670977280 (267078832496151 / 100000)
      (267091990461181 / 100000) := by
  exact
    packedTile65536 2670846208 2670977280 14 6062 51680 31 _ _ (434113 / 20000) (271321 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2670977280 :
    ThetaLowerSegment 2670977280 2671108352 (267091990461181 / 100000)
      (267105217914761 / 100000) := by
  exact
    packedTile65536 2670977280 2671108352 14 6094 51681 31 _ _ (217057 / 10000) (2170573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2671108352 :
    ThetaLowerSegment 2671108352 2671239424 (267105217914761 / 100000)
      (267118215311873 / 100000) := by
  exact
    packedTile65536 2671108352 2671239424 14 5988 51682 31 _ _ (1085287 / 50000) (2170577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2671239424 :
    ThetaLowerSegment 2671239424 2671370496 (267118215311873 / 100000)
      (133565726836597 / 50000) := by
  exact
    packedTile65536 2671239424 2671370496 14 6099 51684 31 _ _ (2170579 / 100000) (1085291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2671370496 :
    ThetaLowerSegment 2671370496 2671501568 (133565726836597 / 50000) (5342892104833 / 2000) := by
  exact
    packedTile65536 2671370496 2671501568 14 6059 51685 31 _ _ (271323 / 12500) (2170587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2671501568 :
    ThetaLowerSegment 2671501568 2671632640 (5342892104833 / 2000) (267157622263883 / 100000) := by
  exact
    packedTile65536 2671501568 2671632640 14 5997 51686 31 _ _ (2170589 / 100000) (67831 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2671632640 :
    ThetaLowerSegment 2671632640 2671763712 (267157622263883 / 100000)
      (267170595904221 / 100000) := by
  exact
    packedTile65536 2671632640 2671763712 14 5977 51687 31 _ _ (1085297 / 50000) (2170597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2671763712 :
    ThetaLowerSegment 2671763712 2671894784 (267170595904221 / 100000)
      (267183662910201 / 100000) := by
  exact
    packedTile65536 2671763712 2671894784 14 6020 51689 31 _ _ (2170599 / 100000) (1085301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2671894784 :
    ThetaLowerSegment 2671894784 2672025856 (267183662910201 / 100000)
      (267196693046013 / 100000) := by
  exact
    packedTile65536 2671894784 2672025856 14 6003 51690 31 _ _ (542651 / 25000) (2170607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2672025856 :
    ThetaLowerSegment 2672025856 2672156928 (267196693046013 / 100000)
      (267209833912899 / 100000) := by
  exact
    packedTile65536 2672025856 2672156928 14 6054 51691 31 _ _ (2170609 / 100000) (542653 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2672156928 :
    ThetaLowerSegment 2672156928 2672288000 (267209833912899 / 100000)
      (267222966127599 / 100000) := by
  exact
    packedTile65536 2672156928 2672288000 14 6050 51692 31 _ _ (1085307 / 50000) (2170617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2672288000 :
    ThetaLowerSegment 2672288000 2672419072 (267222966127599 / 100000)
      (66809044671363 / 25000) := by
  exact
    packedTile65536 2672288000 2672419072 14 6087 51694 31 _ _ (2170619 / 100000) (1085311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2672419072 :
    ThetaLowerSegment 2672419072 2672550144 (66809044671363 / 25000)
      (267249252347781 / 100000) := by
  exact
    packedTile65536 2672419072 2672550144 14 6023 51695 31 _ _ (2170623 / 100000) (1085313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2672550144 :
    ThetaLowerSegment 2672550144 2672681216 (267249252347781 / 100000)
      (267262404182833 / 100000) := by
  exact
    packedTile65536 2672550144 2672681216 14 6059 51696 31 _ _ (542657 / 25000) (2170631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2672681216 :
    ThetaLowerSegment 2672681216 2672812288 (267262404182833 / 100000)
      (133637676004339 / 50000) := by
  exact
    packedTile65536 2672681216 2672812288 14 5965 51697 31 _ _ (2170633 / 100000) (542659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2672812288 :
    ThetaLowerSegment 2672812288 2672943360 (133637676004339 / 50000) (33411070585273 / 12500) := by
  exact
    packedTile65536 2672812288 2672943360 14 6087 51699 31 _ _ (1085319 / 50000) (2170641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2672943360 :
    ThetaLowerSegment 2672943360 2673074432 (33411070585273 / 12500) (133650770393019 / 50000) := by
  exact
    packedTile65536 2672943360 2673074432 14 5978 51700 31 _ _ (2170643 / 100000) (1085323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2673074432 :
    ThetaLowerSegment 2673074432 2673205504 (133650770393019 / 50000)
      (133657387613447 / 50000) := by
  exact
    packedTile65536 2673074432 2673205504 14 6097 51701 31 _ _ (271331 / 12500) (2170651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2673205504 :
    ThetaLowerSegment 2673205504 2673336576 (133657387613447 / 50000)
      (267327914189503 / 100000) := by
  exact
    packedTile65536 2673205504 2673336576 14 6053 51703 31 _ _ (2170653 / 100000) (67833 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2673336576 :
    ThetaLowerSegment 2673336576 2673467648 (267327914189503 / 100000)
      (267340907748291 / 100000) := by
  exact
    packedTile65536 2673336576 2673467648 14 5986 51704 31 _ _ (1085329 / 50000) (2170661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2673467648 :
    ThetaLowerSegment 2673467648 2673598720 (267340907748291 / 100000)
      (267353966456899 / 100000) := by
  exact
    packedTile65536 2673467648 2673598720 14 6016 51705 31 _ _ (2170663 / 100000) (1085333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2673598720 :
    ThetaLowerSegment 2673598720 2673729792 (267353966456899 / 100000)
      (267367316065099 / 100000) := by
  exact
    packedTile65536 2673598720 2673729792 14 6150 51706 31 _ _ (542667 / 25000) (2170671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2673729792 :
    ThetaLowerSegment 2673729792 2673860864 (267367316065099 / 100000)
      (66845124640557 / 25000) := by
  exact
    packedTile65536 2673729792 2673860864 14 6073 51708 31 _ _ (2170673 / 100000) (542669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2673860864 :
    ThetaLowerSegment 2673860864 2673991936 (66845124640557 / 25000) (26739362247537 / 10000) := by
  exact
    packedTile65536 2673860864 2673991936 14 6046 51709 31 _ _ (2170677 / 100000) (54267 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2673991936 :
    ThetaLowerSegment 2673991936 2674123008 (26739362247537 / 10000) (33425842488337 / 12500) := by
  exact
    packedTile65536 2673991936 2674123008 14 6043 51710 31 _ _ (1085341 / 50000) (434137 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2674123008 :
    ThetaLowerSegment 2674123008 2674254080 (33425842488337 / 12500) (66854982250227 / 25000) := by
  exact
    packedTile65536 2674123008 2674254080 14 6076 51711 31 _ _ (2170687 / 100000) (217069 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2674254080 :
    ThetaLowerSegment 2674254080 2674385152 (66854982250227 / 25000) (66858255653763 / 25000) := by
  exact
    packedTile65536 2674254080 2674385152 14 6032 51713 31 _ _ (542673 / 25000) (434139 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2674385152 :
    ThetaLowerSegment 2674385152 2674516224 (66858255653763 / 25000) (66861542089021 / 25000) := by
  exact
    packedTile65536 2674385152 2674516224 14 6056 51714 31 _ _ (2170697 / 100000) (21707 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2674516224 :
    ThetaLowerSegment 2674516224 2674647296 (66861542089021 / 25000) (8358104787501 / 3125) := by
  exact
    packedTile65536 2674516224 2674647296 14 6074 51715 31 _ _ (1085351 / 50000) (434141 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2674647296 :
    ThetaLowerSegment 2674647296 2674778368 (8358104787501 / 3125) (267472292784459 / 100000) := by
  exact
    packedTile65536 2674647296 2674778368 14 5961 51716 31 _ _ (2170707 / 100000) (217071 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2674778368 :
    ThetaLowerSegment 2674778368 2674909440 (267472292784459 / 100000)
      (267485490713419 / 100000) := by
  exact
    packedTile65536 2674778368 2674909440 14 6080 51718 31 _ _ (271339 / 12500) (434143 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2674909440 :
    ThetaLowerSegment 2674909440 2675040512 (267485490713419 / 100000)
      (133749299836691 / 50000) := by
  exact
    packedTile65536 2674909440 2675040512 14 6039 51719 31 _ _ (2170717 / 100000) (13567 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2675040512 :
    ThetaLowerSegment 2675040512 2675171584 (133749299836691 / 50000)
      (133755790295471 / 50000) := by
  exact
    packedTile65536 2675040512 2675171584 14 5980 51720 31 _ _ (1085361 / 50000) (86829 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2675171584 :
    ThetaLowerSegment 2675171584 2675302656 (133755790295471 / 50000) (1672028278938 / 625) := by
  exact
    packedTile65536 2675171584 2675302656 14 5963 51722 31 _ _ (1085363 / 50000) (2170729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2675302656 :
    ThetaLowerSegment 2675302656 2675433728 (1672028278938 / 625) (267537781284297 / 100000) := by
  exact
    packedTile65536 2675302656 2675433728 14 6107 51723 31 _ _ (2170731 / 100000) (1085367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2675433728 :
    ThetaLowerSegment 2675433728 2675564800 (267537781284297 / 100000)
      (267550853456489 / 100000) := by
  exact
    packedTile65536 2675433728 2675564800 14 6022 51724 31 _ _ (135671 / 6250) (2170739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2675564800 :
    ThetaLowerSegment 2675564800 2675695872 (267550853456489 / 100000) (8361378442868 / 3125) := by
  exact
    packedTile65536 2675564800 2675695872 14 6107 51725 31 _ _ (2170741 / 100000) (271343 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2675695872 :
    ThetaLowerSegment 2675695872 2675826944 (8361378442868 / 3125) (66894328162237 / 25000) := by
  exact
    packedTile65536 2675695872 2675826944 14 6082 51727 31 _ _ (1085373 / 50000) (2170749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2675826944 :
    ThetaLowerSegment 2675826944 2675958016 (66894328162237 / 25000) (66897632045259 / 25000) := by
  exact
    packedTile65536 2675826944 2675958016 14 6088 51728 31 _ _ (2170751 / 100000) (1085377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2675958016 :
    ThetaLowerSegment 2675958016 2676089088 (66897632045259 / 25000) (16725210241329 / 6250) := by
  exact
    packedTile65536 2675958016 2676089088 14 5913 51729 31 _ _ (542689 / 25000) (2170759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2676089088 :
    ThetaLowerSegment 2676089088 2676220160 (16725210241329 / 6250) (66904120985187 / 25000) := by
  exact
    packedTile65536 2676089088 2676220160 14 6044 51730 31 _ _ (2170761 / 100000) (542691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2676220160 :
    ThetaLowerSegment 2676220160 2676351232 (66904120985187 / 25000) (66907411866443 / 25000) := by
  exact
    packedTile65536 2676220160 2676351232 14 6064 51732 31 _ _ (1085383 / 50000) (2170769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2676351232 :
    ThetaLowerSegment 2676351232 2676482304 (66907411866443 / 25000) (53528605185489 / 20000) := by
  exact
    packedTile65536 2676351232 2676482304 14 6163 51733 31 _ _ (2170771 / 100000) (1085387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2676482304 :
    ThetaLowerSegment 2676482304 2676613376 (53528605185489 / 20000) (1672850709562 / 625) := by
  exact
    packedTile65536 2676482304 2676613376 14 6029 51734 31 _ _ (86831 / 4000) (1085389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2676613376 :
    ThetaLowerSegment 2676613376 2676744448 (1672850709562 / 625) (3345865421553 / 1250) := by
  exact
    packedTile65536 2676613376 2676744448 14 6044 51735 31 _ _ (108539 / 5000) (2170783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2676744448 :
    ThetaLowerSegment 2676744448 2676875520 (3345865421553 / 1250) (10707292160829 / 4000) := by
  exact
    packedTile65536 2676744448 2676875520 14 6021 51737 31 _ _ (434157 / 20000) (542697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2676875520 :
    ThetaLowerSegment 2676875520 2677006592 (10707292160829 / 4000) (10707814887061 / 4000) := by
  exact
    packedTile65536 2676875520 2677006592 14 6020 51738 31 _ _ (217079 / 10000) (2170793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2677006592 :
    ThetaLowerSegment 2677006592 2677137664 (10707814887061 / 4000) (26770843819163 / 10000) := by
  exact
    packedTile65536 2677006592 2677137664 14 6019 51739 31 _ _ (434159 / 20000) (1085399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2677137664 :
    ThetaLowerSegment 2677137664 2677268736 (26770843819163 / 10000) (26772137181803 / 10000) := by
  exact
    packedTile65536 2677137664 2677268736 14 5958 51741 31 _ _ (5427 / 250) (2170803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2677268736 :
    ThetaLowerSegment 2677268736 2677399808 (26772137181803 / 10000) (26773441401447 / 10000) := by
  exact
    packedTile65536 2677268736 2677399808 14 6008 51742 31 _ _ (434161 / 20000) (271351 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2677399808 :
    ThetaLowerSegment 2677399808 2677530880 (26773441401447 / 10000) (26774742150799 / 10000) := by
  exact
    packedTile65536 2677399808 2677530880 14 5992 51743 31 _ _ (217081 / 10000) (2170813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2677530880 :
    ThetaLowerSegment 2677530880 2677661952 (26774742150799 / 10000) (26776070689579 / 10000) := by
  exact
    packedTile65536 2677530880 2677661952 14 6120 51744 31 _ _ (434163 / 20000) (1085409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2677661952 :
    ThetaLowerSegment 2677661952 2677793024 (26776070689579 / 10000)
      (267773777396989 / 100000) := by
  exact
    packedTile65536 2677661952 2677793024 14 6021 51746 31 _ _ (2170819 / 100000) (1085411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2677793024 :
    ThetaLowerSegment 2677793024 2677924096 (267773777396989 / 100000)
      (267786902198893 / 100000) := by
  exact
    packedTile65536 2677793024 2677924096 14 6046 51747 31 _ _ (271353 / 12500) (2170827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2677924096 :
    ThetaLowerSegment 2677924096 2678055168 (267786902198893 / 100000)
      (267800105180871 / 100000) := by
  exact
    packedTile65536 2677924096 2678055168 14 6082 51748 31 _ _ (2170829 / 100000) (135677 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2678055168 :
    ThetaLowerSegment 2678055168 2678186240 (267800105180871 / 100000)
      (267813214847397 / 100000) := by
  exact
    packedTile65536 2678055168 2678186240 14 6039 51749 31 _ _ (1085417 / 50000) (2170837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2678186240 :
    ThetaLowerSegment 2678186240 2678317312 (267813214847397 / 100000)
      (53565279236361 / 20000) := by
  exact
    packedTile65536 2678186240 2678317312 14 6072 51751 31 _ _ (2170839 / 100000) (1085421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2678317312 :
    ThetaLowerSegment 2678317312 2678448384 (53565279236361 / 20000)
      (267839523275473 / 100000) := by
  exact
    packedTile65536 2678317312 2678448384 14 6047 51752 31 _ _ (542711 / 25000) (2170847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2678448384 :
    ThetaLowerSegment 2678448384 2678579456 (267839523275473 / 100000)
      (267852604811547 / 100000) := by
  exact
    packedTile65536 2678448384 2678579456 14 6026 51753 31 _ _ (2170849 / 100000) (542713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2678579456 :
    ThetaLowerSegment 2678579456 2678710528 (267852604811547 / 100000)
      (267865896950589 / 100000) := by
  exact
    packedTile65536 2678579456 2678710528 14 6123 51754 31 _ _ (1085427 / 50000) (2170857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2678710528 :
    ThetaLowerSegment 2678710528 2678841600 (267865896950589 / 100000)
      (267879008938949 / 100000) := by
  exact
    packedTile65536 2678710528 2678841600 14 6040 51756 31 _ _ (2170859 / 100000) (1085431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2678841600 :
    ThetaLowerSegment 2678841600 2678972672 (267879008938949 / 100000)
      (267892179570837 / 100000) := by
  exact
    packedTile65536 2678841600 2678972672 14 6067 51757 31 _ _ (135679 / 6250) (2170867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2678972672 :
    ThetaLowerSegment 2678972672 2679103744 (267892179570837 / 100000)
      (267905041963737 / 100000) := by
  exact
    packedTile65536 2678972672 2679103744 14 5925 51758 31 _ _ (542717 / 25000) (2170871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2679103744 :
    ThetaLowerSegment 2679103744 2679234816 (267905041963737 / 100000)
      (66979579213033 / 25000) := by
  exact
    packedTile65536 2679103744 2679234816 14 6115 51760 31 _ _ (2170873 / 100000) (542719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2679234816 :
    ThetaLowerSegment 2679234816 2679365888 (66979579213033 / 25000) (26793149625247 / 10000) := by
  exact
    packedTile65536 2679234816 2679365888 14 6071 51761 31 _ _ (1085439 / 50000) (2170881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2679365888 :
    ThetaLowerSegment 2679365888 2679496960 (26793149625247 / 10000) (53588902139211 / 20000) := by
  exact
    packedTile65536 2679365888 2679496960 14 5995 51762 31 _ _ (2170883 / 100000) (1085443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2679496960 :
    ThetaLowerSegment 2679496960 2679628032 (53588902139211 / 20000)
      (267957598979807 / 100000) := by
  exact
    packedTile65536 2679496960 2679628032 14 6029 51763 31 _ _ (271361 / 12500) (2170891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2679628032 :
    ThetaLowerSegment 2679628032 2679759104 (267957598979807 / 100000) (5359410359281 / 2000) := by
  exact
    packedTile65536 2679628032 2679759104 14 5951 51765 31 _ _ (2170893 / 100000) (135681 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2679759104 :
    ThetaLowerSegment 2679759104 2679890176 (5359410359281 / 2000) (6699594825133 / 2500) := by
  exact
    packedTile65536 2679759104 2679890176 14 6115 51766 31 _ _ (1085449 / 50000) (2170901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2679890176 :
    ThetaLowerSegment 2679890176 2680021248 (6699594825133 / 2500) (8374900033003 / 3125) := by
  exact
    packedTile65536 2679890176 2680021248 14 5992 51767 31 _ _ (2170903 / 100000) (1085453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2680021248 :
    ThetaLowerSegment 2680021248 2680152320 (8374900033003 / 3125) (33501246223003 / 12500) := by
  exact
    packedTile65536 2680021248 2680152320 14 6066 51768 31 _ _ (542727 / 25000) (2170911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2680152320 :
    ThetaLowerSegment 2680152320 2680283392 (33501246223003 / 12500) (33502914840239 / 12500) := by
  exact
    packedTile65536 2680152320 2680283392 14 6149 51770 31 _ _ (67841 / 3125) (434183 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2680283392 :
    ThetaLowerSegment 2680283392 2680414464 (33502914840239 / 12500) (53607311828939 / 20000) := by
  exact
    packedTile65536 2680283392 2680414464 14 6099 51771 31 _ _ (2170917 / 100000) (54273 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2680414464 :
    ThetaLowerSegment 2680414464 2680545536 (53607311828939 / 20000)
      (268049549941943 / 100000) := by
  exact
    packedTile65536 2680414464 2680545536 14 5984 51772 31 _ _ (1085461 / 50000) (86837 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2680545536 :
    ThetaLowerSegment 2680545536 2680676608 (268049549941943 / 100000)
      (33507817324773 / 12500) := by
  exact
    packedTile65536 2680545536 2680676608 14 5983 51773 31 _ _ (2170927 / 100000) (217093 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2680676608 :
    ThetaLowerSegment 2680676608 2680807680 (33507817324773 / 12500) (33509473745889 / 12500) := by
  exact
    packedTile65536 2680676608 2680807680 14 6104 51775 31 _ _ (542733 / 25000) (434187 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2680807680 :
    ThetaLowerSegment 2680807680 2680938752 (33509473745889 / 12500) (67022240803207 / 25000) := by
  exact
    packedTile65536 2680807680 2680938752 14 6068 51776 31 _ _ (2170937 / 100000) (108547 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2680938752 :
    ThetaLowerSegment 2680938752 2681069824 (67022240803207 / 25000) (134051045449551 / 50000) := by
  exact
    packedTile65536 2680938752 2681069824 14 6047 51777 31 _ _ (1085471 / 50000) (434189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2681069824 :
    ThetaLowerSegment 2681069824 2681200896 (134051045449551 / 50000)
      (268115118752049 / 100000) := by
  exact
    packedTile65536 2681069824 2681200896 14 6001 51779 31 _ _ (2170947 / 100000) (43419 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2681200896 :
    ThetaLowerSegment 2681200896 2681331968 (268115118752049 / 100000)
      (53625619340621 / 20000) := by
  exact
    packedTile65536 2681200896 2681331968 14 5978 51780 31 _ _ (271369 / 12500) (434191 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2681331968 :
    ThetaLowerSegment 2681331968 2681463040 (53625619340621 / 20000)
      (268141304799409 / 100000) := by
  exact
    packedTile65536 2681331968 2681463040 14 6084 51781 31 _ _ (542739 / 25000) (2170959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2681463040 :
    ThetaLowerSegment 2681463040 2681594112 (268141304799409 / 100000)
      (134077205445483 / 50000) := by
  exact
    packedTile65536 2681463040 2681594112 14 6037 51782 31 _ _ (2170961 / 100000) (542741 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2681594112 :
    ThetaLowerSegment 2681594112 2681725184 (134077205445483 / 50000) (67041903133803 / 25000) := by
  exact
    packedTile65536 2681594112 2681725184 14 6081 51784 31 _ _ (1085483 / 50000) (2170969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2681725184 :
    ThetaLowerSegment 2681725184 2681856256 (67041903133803 / 25000) (134090299641867 / 50000) := by
  exact
    packedTile65536 2681725184 2681856256 14 5982 51785 31 _ _ (2170971 / 100000) (1085487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2681856256 :
    ThetaLowerSegment 2681856256 2681987328 (134090299641867 / 50000)
      (134096811484379 / 50000) := by
  exact
    packedTile65536 2681856256 2681987328 14 5999 51786 31 _ _ (67843 / 3125) (2170979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2681987328 :
    ThetaLowerSegment 2681987328 2682118400 (134096811484379 / 50000)
      (268206807336371 / 100000) := by
  exact
    packedTile65536 2681987328 2682118400 14 6073 51787 31 _ _ (2170981 / 100000) (271373 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2682118400 :
    ThetaLowerSegment 2682118400 2682249472 (268206807336371 / 100000)
      (268219789832651 / 100000) := by
  exact
    packedTile65536 2682118400 2682249472 14 5980 51789 31 _ _ (1085493 / 50000) (2170989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2682249472 :
    ThetaLowerSegment 2682249472 2682380544 (268219789832651 / 100000)
      (134116552260227 / 50000) := by
  exact
    packedTile65536 2682249472 2682380544 14 6133 51790 31 _ _ (2170991 / 100000) (1085497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2682380544 :
    ThetaLowerSegment 2682380544 2682511616 (134116552260227 / 50000)
      (134123099984163 / 50000) := by
  exact
    packedTile65536 2682380544 2682511616 14 6032 51791 31 _ _ (542749 / 25000) (2170999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2682511616 :
    ThetaLowerSegment 2682511616 2682642688 (134123099984163 / 50000)
      (134129555452663 / 50000) := by
  exact
    packedTile65536 2682511616 2682642688 14 5947 51792 31 _ _ (2171 / 100) (2171003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2682642688 :
    ThetaLowerSegment 2682642688 2682773760 (134129555452663 / 50000)
      (268271982793971 / 100000) := by
  exact
    packedTile65536 2682642688 2682773760 14 5929 51794 31 _ _ (434201 / 20000) (67844 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2682773760 :
    ThetaLowerSegment 2682773760 2682904832 (268271982793971 / 100000)
      (268285095694371 / 100000) := by
  exact
    packedTile65536 2682773760 2682904832 14 6040 51795 31 _ _ (217101 / 10000) (2171013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2682904832 :
    ThetaLowerSegment 2682904832 2683035904 (268285095694371 / 100000)
      (268298334543841 / 100000) := by
  exact
    packedTile65536 2682904832 2683035904 14 6098 51796 31 _ _ (434203 / 20000) (1085509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2683035904 :
    ThetaLowerSegment 2683035904 2683166976 (268298334543841 / 100000)
      (268311165272041 / 100000) := by
  exact
    packedTile65536 2683035904 2683166976 14 5910 51798 31 _ _ (108551 / 5000) (2171023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2683166976 :
    ThetaLowerSegment 2683166976 2683298048 (268311165272041 / 100000)
      (268324260894841 / 100000) := by
  exact
    packedTile65536 2683166976 2683298048 14 6032 51799 31 _ _ (86841 / 4000) (542757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2683298048 :
    ThetaLowerSegment 2683298048 2683429120 (268324260894841 / 100000)
      (268337334837501 / 100000) := by
  exact
    packedTile65536 2683298048 2683429120 14 6022 51800 31 _ _ (217103 / 10000) (2171033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2683429120 :
    ThetaLowerSegment 2683429120 2683560192 (268337334837501 / 100000)
      (134175214174793 / 50000) := by
  exact
    packedTile65536 2683429120 2683560192 14 6031 51801 31 _ _ (434207 / 20000) (1085519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2683560192 :
    ThetaLowerSegment 2683560192 2683691264 (134175214174793 / 50000)
      (134181696900233 / 50000) := by
  exact
    packedTile65536 2683560192 2683691264 14 5972 51803 31 _ _ (13569 / 625) (2171043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2683691264 :
    ThetaLowerSegment 2683691264 2683822336 (134181696900233 / 50000)
      (134188258880723 / 50000) := by
  exact
    packedTile65536 2683691264 2683822336 14 6045 51804 31 _ _ (542761 / 25000) (2171047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2683822336 :
    ThetaLowerSegment 2683822336 2683953408 (134188258880723 / 50000) (67097428349317 / 25000) := by
  exact
    packedTile65536 2683822336 2683953408 14 6078 51805 31 _ _ (2171049 / 100000) (542763 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2683953408 :
    ThetaLowerSegment 2683953408 2684084480 (67097428349317 / 25000) (134201381801431 / 50000) := by
  exact
    packedTile65536 2683953408 2684084480 14 6011 51806 31 _ _ (1085527 / 50000) (2171057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2684084480 :
    ThetaLowerSegment 2684084480 2684215552 (134201381801431 / 50000) (13420794057067 / 5000) := by
  exact
    packedTile65536 2684084480 2684215552 14 6042 51808 31 _ _ (2171059 / 100000) (1085531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2684215552 :
    ThetaLowerSegment 2684215552 2684346624 (13420794057067 / 5000) (13421451346693 / 5000) := by
  exact
    packedTile65536 2684215552 2684346624 14 6055 51809 31 _ _ (271383 / 12500) (2171067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2684346624 :
    ThetaLowerSegment 2684346624 2684477696 (13421451346693 / 5000) (6711052419231 / 2500) := by
  exact
    packedTile65536 2684346624 2684477696 14 6020 51810 31 _ _ (2171069 / 100000) (67846 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2684477696 :
    ThetaLowerSegment 2684477696 2684608768 (6711052419231 / 2500) (33556886059507 / 12500) := by
  exact
    packedTile65536 2684477696 2684608768 14 5984 51811 31 _ _ (1085537 / 50000) (2171077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2684608768 :
    ThetaLowerSegment 2684608768 2684739840 (33556886059507 / 12500) (134234103067687 / 50000) := by
  exact
    packedTile65536 2684608768 2684739840 14 6042 51813 31 _ _ (2171079 / 100000) (1085541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2684739840 :
    ThetaLowerSegment 2684739840 2684870912 (134234103067687 / 50000)
      (268481330332109 / 100000) := by
  exact
    packedTile65536 2684739840 2684870912 14 6045 51814 31 _ _ (2171083 / 100000) (1085543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2684870912 :
    ThetaLowerSegment 2684870912 2685001984 (268481330332109 / 100000)
      (268494389426429 / 100000) := by
  exact
    packedTile65536 2684870912 2685001984 14 6015 51815 31 _ _ (135693 / 6250) (2171091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2685001984 :
    ThetaLowerSegment 2685001984 2685133056 (268494389426429 / 100000)
      (268507589671869 / 100000) := by
  exact
    packedTile65536 2685001984 2685133056 14 6080 51817 31 _ _ (2171093 / 100000) (271387 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2685133056 :
    ThetaLowerSegment 2685133056 2685264128 (268507589671869 / 100000)
      (268520572837909 / 100000) := by
  exact
    packedTile65536 2685133056 2685264128 14 5980 51818 31 _ _ (1085549 / 50000) (2171101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2685264128 :
    ThetaLowerSegment 2685264128 2685395200 (268520572837909 / 100000)
      (268533543007231 / 100000) := by
  exact
    packedTile65536 2685264128 2685395200 14 5974 51819 31 _ _ (2171103 / 100000) (1085553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2685395200 :
    ThetaLowerSegment 2685395200 2685526272 (268533543007231 / 100000)
      (268546693408387 / 100000) := by
  exact
    packedTile65536 2685395200 2685526272 14 6057 51820 31 _ _ (542777 / 25000) (2171111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2685526272 :
    ThetaLowerSegment 2685526272 2685657344 (268546693408387 / 100000)
      (268559720086387 / 100000) := by
  exact
    packedTile65536 2685526272 2685657344 14 6000 51822 31 _ _ (2171113 / 100000) (542779 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2685657344 :
    ThetaLowerSegment 2685657344 2685788416 (268559720086387 / 100000)
      (268572894430411 / 100000) := by
  exact
    packedTile65536 2685657344 2685788416 14 6068 51823 31 _ _ (1085559 / 50000) (2171121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2685788416 :
    ThetaLowerSegment 2685788416 2685919488 (268572894430411 / 100000) (10743434067699 / 4000) := by
  exact
    packedTile65536 2685788416 2685919488 14 5968 51824 31 _ _ (2171123 / 100000) (1085563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2685919488 :
    ThetaLowerSegment 2685919488 2686050560 (10743434067699 / 4000) (67149736439853 / 25000) := by
  exact
    packedTile65536 2685919488 2686050560 14 6031 51825 31 _ _ (2171127 / 100000) (217113 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2686050560 :
    ThetaLowerSegment 2686050560 2686181632 (67149736439853 / 25000) (2686122634831 / 1000) := by
  exact
    packedTile65536 2686050560 2686181632 14 6134 51827 31 _ _ (542783 / 25000) (434227 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2686181632 :
    ThetaLowerSegment 2686181632 2686312704 (2686122634831 / 1000) (268625305503059 / 100000) := by
  exact
    packedTile65536 2686181632 2686312704 14 6007 51828 31 _ _ (2171137 / 100000) (108557 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2686312704 :
    ThetaLowerSegment 2686312704 2686443776 (268625305503059 / 100000)
      (53727672115981 / 20000) := by
  exact
    packedTile65536 2686312704 2686443776 14 6013 51829 31 _ _ (1085571 / 50000) (434229 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2686443776 :
    ThetaLowerSegment 2686443776 2686574848 (53727672115981 / 20000) (53730294861557 / 20000) := by
  exact
    packedTile65536 2686443776 2686574848 14 6040 51830 31 _ _ (2171147 / 100000) (43423 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2686574848 :
    ThetaLowerSegment 2686574848 2686705920 (53730294861557 / 20000)
      (268664627146601 / 100000) := by
  exact
    packedTile65536 2686574848 2686705920 14 6058 51832 31 _ _ (135697 / 6250) (434231 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2686705920 :
    ThetaLowerSegment 2686705920 2686836992 (268664627146601 / 100000)
      (268677671457857 / 100000) := by
  exact
    packedTile65536 2686705920 2686836992 14 6008 51833 31 _ _ (2171157 / 100000) (54279 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2686836992 :
    ThetaLowerSegment 2686836992 2686968064 (268677671457857 / 100000)
      (268690806987957 / 100000) := by
  exact
    packedTile65536 2686836992 2686968064 14 6050 51834 31 _ _ (1085581 / 50000) (434233 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2686968064 :
    ThetaLowerSegment 2686968064 2687099136 (268690806987957 / 100000)
      (53740802838147 / 20000) := by
  exact
    packedTile65536 2686968064 2687099136 14 6083 51835 31 _ _ (1085583 / 50000) (2171169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2687099136 :
    ThetaLowerSegment 2687099136 2687230208 (53740802838147 / 20000) (134358660648897 / 50000) := by
  exact
    packedTile65536 2687099136 2687230208 14 6129 51837 31 _ _ (2171171 / 100000) (1085587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2687230208 :
    ThetaLowerSegment 2687230208 2687361280 (134358660648897 / 50000)
      (134365319645689 / 50000) := by
  exact
    packedTile65536 2687230208 2687361280 14 6134 51838 31 _ _ (271397 / 12500) (2171179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2687361280 :
    ThetaLowerSegment 2687361280 2687492352 (134365319645689 / 50000)
      (134371920035929 / 50000) := by
  exact
    packedTile65536 2687361280 2687492352 14 6080 51839 31 _ _ (2171181 / 100000) (135699 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2687492352 :
    ThetaLowerSegment 2687492352 2687623424 (134371920035929 / 50000)
      (134378487873579 / 50000) := by
  exact
    packedTile65536 2687492352 2687623424 14 6050 51841 31 _ _ (1085593 / 50000) (2171189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2687623424 :
    ThetaLowerSegment 2687623424 2687754496 (134378487873579 / 50000)
      (268770057172933 / 100000) := by
  exact
    packedTile65536 2687623424 2687754496 14 6025 51842 31 _ _ (2171191 / 100000) (1085597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2687754496 :
    ThetaLowerSegment 2687754496 2687885568 (268770057172933 / 100000)
      (268783203764713 / 100000) := by
  exact
    packedTile65536 2687754496 2687885568 14 6055 51843 31 _ _ (542799 / 25000) (2171199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2687885568 :
    ThetaLowerSegment 2687885568 2688016640 (268783203764713 / 100000) (6719908325429 / 2500) := by
  exact
    packedTile65536 2687885568 2688016640 14 6047 51844 31 _ _ (2171201 / 100000) (542801 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2688016640 :
    ThetaLowerSegment 2688016640 2688147712 (6719908325429 / 2500) (1680059478587 / 625) := by
  exact
    packedTile65536 2688016640 2688147712 14 6072 51846 31 _ _ (434241 / 20000) (271401 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2688147712 :
    ThetaLowerSegment 2688147712 2688278784 (1680059478587 / 625) (13441131751237 / 5000) := by
  exact
    packedTile65536 2688147712 2688278784 14 6042 51847 31 _ _ (217121 / 10000) (2171213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2688278784 :
    ThetaLowerSegment 2688278784 2688409856 (13441131751237 / 5000) (26883596194241 / 10000) := by
  exact
    packedTile65536 2688278784 2688409856 14 6138 51848 31 _ _ (434243 / 20000) (1085609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2688409856 :
    ThetaLowerSegment 2688409856 2688540928 (26883596194241 / 10000) (1075395496751 / 400) := by
  exact
    packedTile65536 2688409856 2688540928 14 5947 51849 31 _ _ (108561 / 5000) (2171223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2688540928 :
    ThetaLowerSegment 2688540928 2688672000 (1075395496751 / 400) (10754487091333 / 4000) := by
  exact
    packedTile65536 2688540928 2688672000 14 6127 51851 31 _ _ (86849 / 4000) (542807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2688672000 :
    ThetaLowerSegment 2688672000 2688803072 (10754487091333 / 4000) (53775057434013 / 20000) := by
  exact
    packedTile65536 2688672000 2688803072 14 6038 51852 31 _ _ (217123 / 10000) (2171233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2688803072 :
    ThetaLowerSegment 2688803072 2688934144 (53775057434013 / 20000) (53777690707821 / 20000) := by
  exact
    packedTile65536 2688803072 2688934144 14 6064 51853 31 _ _ (434247 / 20000) (1085619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2688934144 :
    ThetaLowerSegment 2688934144 2689065216 (53777690707821 / 20000) (10756063842193 / 4000) := by
  exact
    packedTile65536 2688934144 2689065216 14 6053 51854 31 _ _ (54281 / 2500) (2171243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2689065216 :
    ThetaLowerSegment 2689065216 2689196288 (10756063842193 / 4000) (53782933388741 / 20000) := by
  exact
    packedTile65536 2689065216 2689196288 14 6020 51856 31 _ _ (542811 / 25000) (2171247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2689196288 :
    ThetaLowerSegment 2689196288 2689327360 (53782933388741 / 20000) (134463870016967 / 50000) := by
  exact
    packedTile65536 2689196288 2689327360 14 6021 51857 31 _ _ (2171249 / 100000) (542813 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2689327360 :
    ThetaLowerSegment 2689327360 2689458432 (134463870016967 / 50000) (16808794036973 / 6250) := by
  exact
    packedTile65536 2689327360 2689458432 14 5971 51858 31 _ _ (1085627 / 50000) (2171257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2689458432 :
    ThetaLowerSegment 2689458432 2689589504 (16808794036973 / 6250) (268953877619921 / 100000) := by
  exact
    packedTile65536 2689458432 2689589504 14 6067 51859 31 _ _ (2171259 / 100000) (1085631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2689589504 :
    ThetaLowerSegment 2689589504 2689720576 (268953877619921 / 100000)
      (268967022452177 / 100000) := by
  exact
    packedTile65536 2689589504 2689720576 14 6054 51861 31 _ _ (67852 / 3125) (2171267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2689720576 :
    ThetaLowerSegment 2689720576 2689851648 (268967022452177 / 100000)
      (67245033686417 / 25000) := by
  exact
    packedTile65536 2689720576 2689851648 14 6039 51862 31 _ _ (2171269 / 100000) (271409 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2689851648 :
    ThetaLowerSegment 2689851648 2689982720 (67245033686417 / 25000) (134496527998621 / 50000) := by
  exact
    packedTile65536 2689851648 2689982720 14 5951 51863 31 _ _ (1085637 / 50000) (2171277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2689982720 :
    ThetaLowerSegment 2689982720 2690113792 (134496527998621 / 50000)
      (269006107555311 / 100000) := by
  exact
    packedTile65536 2689982720 2690113792 14 6011 51865 31 _ _ (2171279 / 100000) (1085641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2690113792 :
    ThetaLowerSegment 2690113792 2690244864 (269006107555311 / 100000)
      (67254761557677 / 25000) := by
  exact
    packedTile65536 2690113792 2690244864 14 5959 51866 31 _ _ (2171283 / 100000) (1085643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2690244864 :
    ThetaLowerSegment 2690244864 2690375936 (67254761557677 / 25000) (67258078742919 / 25000) := by
  exact
    packedTile65536 2690244864 2690375936 14 6111 51867 31 _ _ (271411 / 12500) (2171291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2690375936 :
    ThetaLowerSegment 2690375936 2690507008 (67258078742919 / 25000) (33630692811079 / 12500) := by
  exact
    packedTile65536 2690375936 2690507008 14 6092 51868 31 _ _ (2171293 / 100000) (67853 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2690507008 :
    ThetaLowerSegment 2690507008 2690638080 (33630692811079 / 12500) (67264661025191 / 25000) := by
  exact
    packedTile65536 2690507008 2690638080 14 6034 51870 31 _ _ (1085649 / 50000) (2171301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2690638080 :
    ThetaLowerSegment 2690638080 2690769152 (67264661025191 / 25000) (67267926664903 / 25000) := by
  exact
    packedTile65536 2690638080 2690769152 14 6016 51871 31 _ _ (2171303 / 100000) (1085653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2690769152 :
    ThetaLowerSegment 2690769152 2690900224 (67267926664903 / 25000) (3363560022727 / 1250) := by
  exact
    packedTile65536 2690769152 2690900224 14 6031 51872 31 _ _ (542827 / 25000) (2171311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2690900224 :
    ThetaLowerSegment 2690900224 2691031296 (3363560022727 / 1250) (53819585481049 / 20000) := by
  exact
    packedTile65536 2690900224 2691031296 14 6045 51873 31 _ _ (2171313 / 100000) (542829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2691031296 :
    ThetaLowerSegment 2691031296 2691162368 (53819585481049 / 20000)
      (269111018281467 / 100000) := by
  exact
    packedTile65536 2691031296 2691162368 14 6029 51875 31 _ _ (1085659 / 50000) (2171321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2691162368 :
    ThetaLowerSegment 2691162368 2691293440 (269111018281467 / 100000)
      (269124243803769 / 100000) := by
  exact
    packedTile65536 2691162368 2691293440 14 6091 51876 31 _ _ (1085661 / 50000) (86853 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2691293440 :
    ThetaLowerSegment 2691293440 2691424512 (269124243803769 / 100000)
      (53827427428699 / 20000) := by
  exact
    packedTile65536 2691293440 2691424512 14 5938 51877 31 _ _ (2171327 / 100000) (217133 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2691424512 :
    ThetaLowerSegment 2691424512 2691555584 (53827427428699 / 20000)
      (269150234618119 / 100000) := by
  exact
    packedTile65536 2691424512 2691555584 14 6032 51878 31 _ _ (542833 / 25000) (434267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2691555584 :
    ThetaLowerSegment 2691555584 2691686656 (269150234618119 / 100000)
      (269163418976383 / 100000) := by
  exact
    packedTile65536 2691555584 2691686656 14 6072 51880 31 _ _ (2171337 / 100000) (108567 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2691686656 :
    ThetaLowerSegment 2691686656 2691817728 (269163418976383 / 100000)
      (53835292011287 / 20000) := by
  exact
    packedTile65536 2691686656 2691817728 14 6006 51881 31 _ _ (1085671 / 50000) (434269 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2691817728 :
    ThetaLowerSegment 2691817728 2691948800 (53835292011287 / 20000)
      (269189657503501 / 100000) := by
  exact
    packedTile65536 2691817728 2691948800 14 6078 51882 31 _ _ (2171347 / 100000) (43427 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2691948800 :
    ThetaLowerSegment 2691948800 2692079872 (269189657503501 / 100000)
      (269202915778813 / 100000) := by
  exact
    packedTile65536 2691948800 2692079872 14 6106 51883 31 _ _ (271419 / 12500) (434271 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2692079872 :
    ThetaLowerSegment 2692079872 2692210944 (269202915778813 / 100000)
      (269215952600237 / 100000) := by
  exact
    packedTile65536 2692079872 2692210944 14 6004 51885 31 _ _ (542839 / 25000) (2171359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2692210944 :
    ThetaLowerSegment 2692210944 2692342016 (269215952600237 / 100000)
      (134614534896019 / 50000) := by
  exact
    packedTile65536 2692210944 2692342016 14 6041 51886 31 _ _ (2171361 / 100000) (542841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2692342016 :
    ThetaLowerSegment 2692342016 2692473088 (134614534896019 / 50000) (16827636416957 / 6250) := by
  exact
    packedTile65536 2692342016 2692473088 14 6039 51887 31 _ _ (1085683 / 50000) (2171369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2692473088 :
    ThetaLowerSegment 2692473088 2692604160 (16827636416957 / 6250) (134627664075673 / 50000) := by
  exact
    packedTile65536 2692473088 2692604160 14 6054 51889 31 _ _ (2171371 / 100000) (1085687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2692604160 :
    ThetaLowerSegment 2692604160 2692735232 (134627664075673 / 50000)
      (134634154318537 / 50000) := by
  exact
    packedTile65536 2692604160 2692735232 14 5978 51890 31 _ _ (135711 / 6250) (2171379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2692735232 :
    ThetaLowerSegment 2692735232 2692866304 (134634154318537 / 50000) (26928141509279 / 10000) := by
  exact
    packedTile65536 2692735232 2692866304 14 6036 51891 31 _ _ (2171381 / 100000) (271423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2692866304 :
    ThetaLowerSegment 2692866304 2692997376 (26928141509279 / 10000) (134647223875781 / 50000) := by
  exact
    packedTile65536 2692866304 2692997376 14 6002 51892 31 _ _ (1085693 / 50000) (2171389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2692997376 :
    ThetaLowerSegment 2692997376 2693128448 (134647223875781 / 50000)
      (269307651980233 / 100000) := by
  exact
    packedTile65536 2692997376 2693128448 14 6081 51894 31 _ _ (2171391 / 100000) (1085697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2693128448 :
    ThetaLowerSegment 2693128448 2693259520 (269307651980233 / 100000)
      (269320728120923 / 100000) := by
  exact
    packedTile65536 2693128448 2693259520 14 6022 51895 31 _ _ (434279 / 20000) (1085699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2693259520 :
    ThetaLowerSegment 2693259520 2693390592 (269320728120923 / 100000)
      (269333558923523 / 100000) := by
  exact
    packedTile65536 2693259520 2693390592 14 5909 51896 31 _ _ (10857 / 500) (2171403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2693390592 :
    ThetaLowerSegment 2693390592 2693521664 (269333558923523 / 100000)
      (134673305619489 / 50000) := by
  exact
    packedTile65536 2693390592 2693521664 14 6011 51897 31 _ _ (434281 / 20000) (135713 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2693521664 :
    ThetaLowerSegment 2693521664 2693652736 (134673305619489 / 50000) (67339951724387 / 25000) := by
  exact
    packedTile65536 2693521664 2693652736 14 6077 51899 31 _ _ (217141 / 10000) (2171413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2693652736 :
    ThetaLowerSegment 2693652736 2693783808 (67339951724387 / 25000)
      (269372720302553 / 100000) := by
  exact
    packedTile65536 2693652736 2693783808 14 5947 51900 31 _ _ (434283 / 20000) (1085709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2693783808 :
    ThetaLowerSegment 2693783808 2693914880 (269372720302553 / 100000)
      (269386002878693 / 100000) := by
  exact
    packedTile65536 2693783808 2693914880 14 6117 51901 31 _ _ (108571 / 5000) (2171423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2693914880 :
    ThetaLowerSegment 2693914880 2694045952 (269386002878693 / 100000)
      (33674875400021 / 12500) := by
  exact
    packedTile65536 2693914880 2694045952 14 5987 51902 31 _ _ (86857 / 4000) (542857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2694045952 :
    ThetaLowerSegment 2694045952 2694177024 (33674875400021 / 12500)
      (269412185945627 / 100000) := by
  exact
    packedTile65536 2694045952 2694177024 14 6071 51904 31 _ _ (2171429 / 100000) (271429 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2694177024 :
    ThetaLowerSegment 2694177024 2694308096 (269412185945627 / 100000)
      (269425379578611 / 100000) := by
  exact
    packedTile65536 2694177024 2694308096 14 6076 51905 31 _ _ (1085717 / 50000) (2171437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2694308096 :
    ThetaLowerSegment 2694308096 2694439168 (269425379578611 / 100000)
      (134719200849147 / 50000) := by
  exact
    packedTile65536 2694308096 2694439168 14 5997 51906 31 _ _ (2171439 / 100000) (1085721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2694439168 :
    ThetaLowerSegment 2694439168 2694570240 (134719200849147 / 50000) (26945154762027 / 10000) := by
  exact
    packedTile65536 2694439168 2694570240 14 6054 51907 31 _ _ (542861 / 25000) (2171447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2694570240 :
    ThetaLowerSegment 2694570240 2694701312 (26945154762027 / 10000)
      (269464856431191 / 100000) := by
  exact
    packedTile65536 2694570240 2694701312 14 6129 51909 31 _ _ (2171449 / 100000) (542863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2694701312 :
    ThetaLowerSegment 2694701312 2694832384 (269464856431191 / 100000)
      (269478030642609 / 100000) := by
  exact
    packedTile65536 2694701312 2694832384 14 6067 51910 31 _ _ (1085727 / 50000) (2171457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2694832384 :
    ThetaLowerSegment 2694832384 2694963456 (269478030642609 / 100000)
      (269491072425363 / 100000) := by
  exact
    packedTile65536 2694832384 2694963456 14 6006 51911 31 _ _ (2171459 / 100000) (1085731 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2694963456 :
    ThetaLowerSegment 2694963456 2695094528 (269491072425363 / 100000)
      (269504099037899 / 100000) := by
  exact
    packedTile65536 2694963456 2695094528 14 5999 51913 31 _ _ (271433 / 12500) (2171467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2695094528 :
    ThetaLowerSegment 2695094528 2695225600 (269504099037899 / 100000)
      (269517160417919 / 100000) := by
  exact
    packedTile65536 2695094528 2695225600 14 6015 51914 31 _ _ (542867 / 25000) (2171471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2695225600 :
    ThetaLowerSegment 2695225600 2695356672 (269517160417919 / 100000)
      (269530415089111 / 100000) := by
  exact
    packedTile65536 2695225600 2695356672 14 6104 51915 31 _ _ (2171473 / 100000) (542869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2695356672 :
    ThetaLowerSegment 2695356672 2695487744 (269530415089111 / 100000)
      (269543578588747 / 100000) := by
  exact
    packedTile65536 2695356672 2695487744 14 6062 51916 31 _ _ (1085739 / 50000) (2171481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2695487744 :
    ThetaLowerSegment 2695487744 2695618816 (269543578588747 / 100000)
      (67389170872163 / 25000) := by
  exact
    packedTile65536 2695487744 2695618816 14 6035 51918 31 _ _ (2171483 / 100000) (1085743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2695618816 :
    ThetaLowerSegment 2695618816 2695749888 (67389170872163 / 25000) (13478492243871 / 5000) := by
  exact
    packedTile65536 2695618816 2695749888 14 6061 51919 31 _ _ (67859 / 3125) (2171491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2695749888 :
    ThetaLowerSegment 2695749888 2695880960 (13478492243871 / 5000) (134791525948923 / 50000) := by
  exact
    packedTile65536 2695749888 2695880960 14 6082 51920 31 _ _ (2171493 / 100000) (271437 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2695880960 :
    ThetaLowerSegment 2695880960 2696012032 (134791525948923 / 50000) (5391921530857 / 2000) := by
  exact
    packedTile65536 2695880960 2696012032 14 5998 51921 31 _ _ (1085749 / 50000) (2171501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2696012032 :
    ThetaLowerSegment 2696012032 2696143104 (5391921530857 / 2000) (134804602721971 / 50000) := by
  exact
    packedTile65536 2696012032 2696143104 14 6046 51923 31 _ _ (1085751 / 50000) (434301 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2696143104 :
    ThetaLowerSegment 2696143104 2696274176 (134804602721971 / 50000) (2696222214569 / 1000) := by
  exact
    packedTile65536 2696143104 2696274176 14 5994 51924 31 _ _ (2171507 / 100000) (217151 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2696274176 :
    ThetaLowerSegment 2696274176 2696405248 (2696222214569 / 1000) (13481770126737 / 5000) := by
  exact
    packedTile65536 2696274176 2696405248 14 6070 51925 31 _ _ (271439 / 12500) (434303 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2696405248 :
    ThetaLowerSegment 2696405248 2696536320 (13481770126737 / 5000) (269648694390297 / 100000) := by
  exact
    packedTile65536 2696405248 2696536320 14 6121 51926 31 _ _ (2171517 / 100000) (13572 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2696536320 :
    ThetaLowerSegment 2696536320 2696667392 (269648694390297 / 100000)
      (269661565001191 / 100000) := by
  exact
    packedTile65536 2696536320 2696667392 14 5927 51928 31 _ _ (1085761 / 50000) (86861 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2696667392 :
    ThetaLowerSegment 2696667392 2696798464 (269661565001191 / 100000)
      (134837289481251 / 50000) := by
  exact
    packedTile65536 2696667392 2696798464 14 5993 51929 31 _ _ (2171527 / 100000) (217153 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2696798464 :
    ThetaLowerSegment 2696798464 2696929536 (134837289481251 / 50000) (26968777970553 / 10000) := by
  exact
    packedTile65536 2696798464 2696929536 14 6079 51930 31 _ _ (542883 / 25000) (434307 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2696929536 :
    ThetaLowerSegment 2696929536 2697060608 (26968777970553 / 10000) (134850454406093 / 50000) := by
  exact
    packedTile65536 2696929536 2697060608 14 6046 51931 31 _ _ (135721 / 6250) (2171539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2697060608 :
    ThetaLowerSegment 2697060608 2697191680 (134850454406093 / 50000)
      (134857003773749 / 50000) := by
  exact
    packedTile65536 2697060608 2697191680 14 6032 51933 31 _ _ (2171541 / 100000) (271443 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2697191680 :
    ThetaLowerSegment 2697191680 2697322752 (134857003773749 / 50000) (67431853125239 / 25000) := by
  exact
    packedTile65536 2697191680 2697322752 14 6173 51934 31 _ _ (1085773 / 50000) (2171549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2697322752 :
    ThetaLowerSegment 2697322752 2697339136 (67431853125239 / 25000) (134864511895899 / 50000) := by
  exact
    packedTile65536 2697322752 2697339136 11 742 51935 31 _ _ (2171551 / 100000) (1085777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2697339136 :
    ThetaLowerSegment 2697339136 2697341184 (134864511895899 / 50000)
      (134864620473499 / 50000) := by
  exact
    packedTile65536 2697339136 2697341184 8 100 51935 31 _ _ (67861 / 3125) (434311 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2665341184_2697341184 :
    ThetaLowerSegment 2665341184 2697341184 (8329016425604 / 3125) (134864620473499 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2665341184 cell2665472256)
                  (ThetaLowerSegment.join cell2665603328 cell2665734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2665865472 cell2665996544)
                  (ThetaLowerSegment.join cell2666127616 cell2666258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2666389760 cell2666520832)
                  (ThetaLowerSegment.join cell2666651904 cell2666782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2666914048 cell2667045120)
                  (ThetaLowerSegment.join cell2667176192 cell2667307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2667438336 cell2667569408)
                  (ThetaLowerSegment.join cell2667700480 cell2667831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2667962624 cell2668093696)
                  (ThetaLowerSegment.join cell2668224768 cell2668355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2668486912 cell2668617984)
                  (ThetaLowerSegment.join cell2668749056 cell2668880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2669011200 cell2669142272)
                  (ThetaLowerSegment.join cell2669273344 cell2669404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2669535488 cell2669666560)
                  (ThetaLowerSegment.join cell2669797632 cell2669928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2670059776 cell2670190848)
                  (ThetaLowerSegment.join cell2670321920 cell2670452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2670584064 cell2670715136)
                  (ThetaLowerSegment.join cell2670846208 cell2670977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2671108352 cell2671239424)
                  (ThetaLowerSegment.join cell2671370496 cell2671501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2671632640 cell2671763712)
                  (ThetaLowerSegment.join cell2671894784 cell2672025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2672156928 cell2672288000)
                  (ThetaLowerSegment.join cell2672419072 cell2672550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2672681216 cell2672812288)
                  (ThetaLowerSegment.join cell2672943360 cell2673074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2673205504 cell2673336576)
                  (ThetaLowerSegment.join cell2673467648 cell2673598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2673729792 cell2673860864)
                  (ThetaLowerSegment.join cell2673991936 cell2674123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2674254080 cell2674385152)
                  (ThetaLowerSegment.join cell2674516224 cell2674647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2674778368 cell2674909440)
                  (ThetaLowerSegment.join cell2675040512 cell2675171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2675302656 cell2675433728)
                  (ThetaLowerSegment.join cell2675564800 cell2675695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2675826944 cell2675958016)
                  (ThetaLowerSegment.join cell2676089088 cell2676220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2676351232 cell2676482304)
                  (ThetaLowerSegment.join cell2676613376 cell2676744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2676875520 cell2677006592)
                  (ThetaLowerSegment.join cell2677137664 cell2677268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2677399808 cell2677530880)
                  (ThetaLowerSegment.join cell2677661952 cell2677793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2677924096 cell2678055168)
                  (ThetaLowerSegment.join cell2678186240 cell2678317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2678448384 cell2678579456)
                  (ThetaLowerSegment.join cell2678710528 cell2678841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2678972672 cell2679103744)
                  (ThetaLowerSegment.join cell2679234816 cell2679365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2679496960 cell2679628032)
                  (ThetaLowerSegment.join cell2679759104 cell2679890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2680021248 cell2680152320)
                  (ThetaLowerSegment.join cell2680283392 cell2680414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2680545536 cell2680676608)
                  (ThetaLowerSegment.join cell2680807680 cell2680938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2681069824 cell2681200896)
                  (ThetaLowerSegment.join cell2681331968 cell2681463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2681594112 cell2681725184)
                  (ThetaLowerSegment.join cell2681856256 cell2681987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2682118400 cell2682249472)
                  (ThetaLowerSegment.join cell2682380544 cell2682511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2682642688 cell2682773760)
                  (ThetaLowerSegment.join cell2682904832 cell2683035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2683166976 cell2683298048)
                  (ThetaLowerSegment.join cell2683429120 cell2683560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2683691264 cell2683822336)
                  (ThetaLowerSegment.join cell2683953408 cell2684084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2684215552 cell2684346624)
                  (ThetaLowerSegment.join cell2684477696 cell2684608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2684739840 cell2684870912)
                  (ThetaLowerSegment.join cell2685001984 cell2685133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2685264128 cell2685395200)
                  (ThetaLowerSegment.join cell2685526272 cell2685657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2685788416 cell2685919488)
                  (ThetaLowerSegment.join cell2686050560 cell2686181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2686312704 cell2686443776)
                  (ThetaLowerSegment.join cell2686574848 cell2686705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2686836992 cell2686968064)
                  (ThetaLowerSegment.join cell2687099136 cell2687230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2687361280 cell2687492352)
                  (ThetaLowerSegment.join cell2687623424 cell2687754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2687885568 cell2688016640)
                  (ThetaLowerSegment.join cell2688147712 cell2688278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2688409856 cell2688540928)
                  (ThetaLowerSegment.join cell2688672000 cell2688803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2688934144 cell2689065216)
                  (ThetaLowerSegment.join cell2689196288 cell2689327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2689458432 cell2689589504)
                  (ThetaLowerSegment.join cell2689720576 cell2689851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2689982720 cell2690113792)
                  (ThetaLowerSegment.join cell2690244864 cell2690375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2690507008 cell2690638080)
                  (ThetaLowerSegment.join cell2690769152 cell2690900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2691031296 cell2691162368)
                  (ThetaLowerSegment.join cell2691293440 cell2691424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2691555584 cell2691686656)
                  (ThetaLowerSegment.join cell2691817728 cell2691948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2692079872 cell2692210944)
                  (ThetaLowerSegment.join cell2692342016 cell2692473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2692604160 cell2692735232)
                  (ThetaLowerSegment.join cell2692866304 cell2692997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2693128448 cell2693259520)
                  (ThetaLowerSegment.join cell2693390592 cell2693521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2693652736 cell2693783808)
                  (ThetaLowerSegment.join cell2693914880 cell2694045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2694177024 cell2694308096)
                  (ThetaLowerSegment.join cell2694439168 cell2694570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2694701312 cell2694832384)
                  (ThetaLowerSegment.join cell2694963456 cell2695094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2695225600 cell2695356672)
                  (ThetaLowerSegment.join cell2695487744 cell2695618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2695749888 cell2695880960)
                  (ThetaLowerSegment.join cell2696012032 cell2696143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2696274176 cell2696405248)
                  (ThetaLowerSegment.join cell2696536320 cell2696667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2696798464 cell2696929536)
                (ThetaLowerSegment.join cell2697060608 cell2697191680))
              (ThetaLowerSegment.join cell2697322752 cell2697339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
