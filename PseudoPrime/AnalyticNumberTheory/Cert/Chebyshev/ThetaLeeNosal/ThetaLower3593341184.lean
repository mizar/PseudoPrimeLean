/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3593341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3561341184 :
    ThetaLowerSegment 3561341184 3561472256 (356127495077781 / 100000)
      (178070256482661 / 50000) := by
  exact
    packedTile65536 3561341184 3561472256 14 5919 59676 32 _ _ (2199339 / 100000) (1099671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3561472256 :
    ThetaLowerSegment 3561472256 3561603328 (178070256482661 / 50000)
      (178076799525111 / 50000) := by
  exact
    packedTile65536 3561472256 3561603328 14 5950 59678 32 _ _ (1099671 / 50000) (439869 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3561603328 :
    ThetaLowerSegment 3561603328 3561734400 (178076799525111 / 50000)
      (178083404161149 / 50000) := by
  exact
    packedTile65536 3561603328 3561734400 14 6006 59679 32 _ _ (1099673 / 50000) (2199349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3561734400 :
    ThetaLowerSegment 3561734400 3561865472 (178083404161149 / 50000)
      (178089857054049 / 50000) := by
  exact
    packedTile65536 3561734400 3561865472 14 5868 59680 32 _ _ (43987 / 2000) (2199353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3561865472 :
    ThetaLowerSegment 3561865472 3561996544 (178089857054049 / 50000) (35619279586569 / 10000) := by
  exact
    packedTile65536 3561865472 3561996544 14 5948 59681 32 _ _ (1099677 / 50000) (2199357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3561996544 :
    ThetaLowerSegment 3561996544 3562127616 (35619279586569 / 10000) (2226286762749 / 625) := by
  exact
    packedTile65536 3561996544 3562127616 14 5950 59682 32 _ _ (2199357 / 100000) (13746 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3562127616 :
    ThetaLowerSegment 3562127616 3562258688 (2226286762749 / 625) (356219084803923 / 100000) := by
  exact
    packedTile65536 3562127616 3562258688 14 6003 59683 32 _ _ (2199361 / 100000) (549841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3562258688 :
    ThetaLowerSegment 3562258688 3562389760 (356219084803923 / 100000)
      (178116104207439 / 50000) := by
  exact
    packedTile65536 3562258688 3562389760 14 5967 59684 32 _ _ (439873 / 20000) (274921 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3562389760 :
    ThetaLowerSegment 3562389760 3562520832 (178116104207439 / 50000) (35624539142667 / 10000) := by
  exact
    packedTile65536 3562389760 3562520832 14 5994 59685 32 _ _ (274921 / 12500) (2199371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3562520832 :
    ThetaLowerSegment 3562520832 3562651904 (35624539142667 / 10000) (178129221250059 / 50000) := by
  exact
    packedTile65536 3562520832 3562651904 14 5934 59686 32 _ _ (549843 / 25000) (3519 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3562651904 :
    ThetaLowerSegment 3562651904 3562782976 (178129221250059 / 50000)
      (178135841371819 / 50000) := by
  exact
    packedTile65536 3562651904 3562782976 14 6020 59687 32 _ _ (137461 / 6250) (2199379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3562782976 :
    ThetaLowerSegment 3562782976 3562914048 (178135841371819 / 50000) (3562848306313 / 1000) := by
  exact
    packedTile65536 3562782976 3562914048 14 5978 59689 32 _ _ (2199379 / 100000) (1099691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3562914048 :
    ThetaLowerSegment 3562914048 3563045120 (3562848306313 / 1000) (35629778499717 / 10000) := by
  exact
    packedTile65536 3562914048 3563045120 14 5890 59690 32 _ _ (2199383 / 100000) (1099693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3563045120 :
    ThetaLowerSegment 3563045120 3563176192 (35629778499717 / 10000) (44538846822099 / 12500) := by
  exact
    packedTile65536 3563045120 3563176192 14 5906 59691 32 _ _ (2199387 / 100000) (219939 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3563176192 :
    ThetaLowerSegment 3563176192 3563307264 (44538846822099 / 12500) (44540483168259 / 12500) := by
  exact
    packedTile65536 3563176192 3563307264 14 5952 59692 32 _ _ (219939 / 10000) (2199393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3563307264 :
    ThetaLowerSegment 3563307264 3563438336 (44540483168259 / 12500) (89084246732669 / 25000) := by
  exact
    packedTile65536 3563307264 3563438336 14 5966 59693 32 _ _ (1099697 / 50000) (2199397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3563438336 :
    ThetaLowerSegment 3563438336 3563569408 (89084246732669 / 25000) (178175064166863 / 50000) := by
  exact
    packedTile65536 3563438336 3563569408 14 5975 59694 32 _ _ (1099699 / 50000) (2199401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3563569408 :
    ThetaLowerSegment 3563569408 3563700480 (178175064166863 / 50000)
      (178181565596219 / 50000) := by
  exact
    packedTile65536 3563569408 3563700480 14 5912 59695 32 _ _ (2199401 / 100000) (549851 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3563700480 :
    ThetaLowerSegment 3563700480 3563831552 (178181565596219 / 50000)
      (356376400202803 / 100000) := by
  exact
    packedTile65536 3563700480 3563831552 14 6033 59696 32 _ _ (439881 / 20000) (137463 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3563831552 :
    ThetaLowerSegment 3563831552 3563962624 (356376400202803 / 100000) (11137171390217 / 3125) := by
  exact
    packedTile65536 3563831552 3563962624 14 5949 59697 32 _ _ (2199409 / 100000) (549853 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3563962624 :
    ThetaLowerSegment 3563962624 3564093696 (11137171390217 / 3125) (44550326872073 / 12500) := by
  exact
    packedTile65536 3563962624 3564093696 14 5970 59698 32 _ _ (549853 / 25000) (439883 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3564093696 :
    ThetaLowerSegment 3564093696 3564224768 (44550326872073 / 12500) (11137989228564 / 3125) := by
  exact
    packedTile65536 3564093696 3564224768 14 5929 59700 32 _ _ (274927 / 12500) (2199419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3564224768 :
    ThetaLowerSegment 3564224768 3564355840 (11137989228564 / 3125) (22276804889193 / 6250) := by
  exact
    packedTile65536 3564224768 3564355840 14 6012 59701 32 _ _ (109971 / 5000) (2199423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3564355840 :
    ThetaLowerSegment 3564355840 3564486912 (22276804889193 / 6250) (3564417316551 / 1000) := by
  exact
    packedTile65536 3564355840 3564486912 14 5844 59702 32 _ _ (2199423 / 100000) (1099713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3564486912 :
    ThetaLowerSegment 3564486912 3564617984 (3564417316551 / 1000) (35645508217699 / 10000) := by
  exact
    packedTile65536 3564486912 3564617984 14 6070 59703 32 _ _ (2199427 / 100000) (219943 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3564617984 :
    ThetaLowerSegment 3564617984 3564749056 (35645508217699 / 10000) (89117022402981 / 25000) := by
  exact
    packedTile65536 3564617984 3564749056 14 5914 59704 32 _ _ (2199431 / 100000) (1099717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3564749056 :
    ThetaLowerSegment 3564749056 3564880128 (89117022402981 / 25000) (178240734384473 / 50000) := by
  exact
    packedTile65536 3564749056 3564880128 14 6083 59705 32 _ _ (1099717 / 50000) (2199437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3564880128 :
    ThetaLowerSegment 3564880128 3565011200 (178240734384473 / 50000)
      (178247326100159 / 50000) := by
  exact
    packedTile65536 3564880128 3565011200 14 5994 59706 32 _ _ (1099719 / 50000) (2199441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3565011200 :
    ThetaLowerSegment 3565011200 3565142272 (178247326100159 / 50000) (22281734092409 / 6250) := by
  exact
    packedTile65536 3565011200 3565142272 14 5953 59707 32 _ _ (1099721 / 50000) (439889 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3565142272 :
    ThetaLowerSegment 3565142272 3565273344 (22281734092409 / 6250) (356520856370189 / 100000) := by
  exact
    packedTile65536 3565142272 3565273344 14 5961 59708 32 _ _ (439889 / 20000) (274931 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3565273344 :
    ThetaLowerSegment 3565273344 3565404416 (356520856370189 / 100000)
      (178266873670389 / 50000) := by
  exact
    packedTile65536 3565273344 3565404416 14 5861 59709 32 _ _ (2199449 / 100000) (549863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3565404416 :
    ThetaLowerSegment 3565404416 3565535488 (178266873670389 / 50000)
      (356546972651667 / 100000) := by
  exact
    packedTile65536 3565404416 3565535488 14 6013 59711 32 _ _ (2199453 / 100000) (68733 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3565535488 :
    ThetaLowerSegment 3565535488 3565666560 (356546972651667 / 100000)
      (356560015431677 / 100000) := by
  exact
    packedTile65536 3565535488 3565666560 14 5930 59712 32 _ _ (2199457 / 100000) (109973 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3565666560 :
    ThetaLowerSegment 3565666560 3565797632 (356560015431677 / 100000)
      (356573097819757 / 100000) := by
  exact
    packedTile65536 3565666560 3565797632 14 5948 59713 32 _ _ (109973 / 5000) (2199463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3565797632 :
    ThetaLowerSegment 3565797632 3565928704 (356573097819757 / 100000)
      (356586312199469 / 100000) := by
  exact
    packedTile65536 3565797632 3565928704 14 6008 59714 32 _ _ (274933 / 12500) (2199467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3565928704 :
    ThetaLowerSegment 3565928704 3566059776 (356586312199469 / 100000)
      (356599390236197 / 100000) := by
  exact
    packedTile65536 3565928704 3566059776 14 5946 59715 32 _ _ (549867 / 25000) (2199471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3566059776 :
    ThetaLowerSegment 3566059776 3566190848 (356599390236197 / 100000)
      (356612490285473 / 100000) := by
  exact
    packedTile65536 3566059776 3566190848 14 5956 59716 32 _ _ (2199471 / 100000) (1099737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3566190848 :
    ThetaLowerSegment 3566190848 3566321920 (356612490285473 / 100000)
      (89156395940037 / 25000) := by
  exact
    packedTile65536 3566190848 3566321920 14 5953 59717 32 _ _ (87979 / 4000) (1099739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3566321920 :
    ThetaLowerSegment 3566321920 3566452992 (89156395940037 / 25000)
      (356638738844047 / 100000) := by
  exact
    packedTile65536 3566321920 3566452992 14 5981 59718 32 _ _ (2199479 / 100000) (1099741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3566452992 :
    ThetaLowerSegment 3566452992 3566584064 (356638738844047 / 100000)
      (356651896145371 / 100000) := by
  exact
    packedTile65536 3566452992 3566584064 14 5982 59719 32 _ _ (1099741 / 50000) (439897 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3566584064 :
    ThetaLowerSegment 3566584064 3566715136 (356651896145371 / 100000)
      (356664906105061 / 100000) := by
  exact
    packedTile65536 3566584064 3566715136 14 5915 59720 32 _ _ (1099743 / 50000) (2199489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3566715136 :
    ThetaLowerSegment 3566715136 3566846208 (356664906105061 / 100000)
      (356677933684331 / 100000) := by
  exact
    packedTile65536 3566715136 3566846208 14 5923 59721 32 _ _ (219949 / 10000) (2199493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3566846208 :
    ThetaLowerSegment 3566846208 3566977280 (356677933684331 / 100000)
      (178345551024461 / 50000) := by
  exact
    packedTile65536 3566846208 3566977280 14 5987 59723 32 _ _ (2199493 / 100000) (274937 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3566977280 :
    ThetaLowerSegment 3566977280 3567108352 (178345551024461 / 50000)
      (356704182457581 / 100000) := by
  exact
    packedTile65536 3566977280 3567108352 14 5947 59724 32 _ _ (2199497 / 100000) (4399 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3567108352 :
    ThetaLowerSegment 3567108352 3567239424 (356704182457581 / 100000)
      (356717339872563 / 100000) := by
  exact
    packedTile65536 3567108352 3567239424 14 5982 59725 32 _ _ (2199501 / 100000) (137469 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3567239424 :
    ThetaLowerSegment 3567239424 3567370496 (356717339872563 / 100000)
      (356730259759059 / 100000) := by
  exact
    packedTile65536 3567239424 3567370496 14 5874 59726 32 _ _ (137469 / 6250) (2199507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3567370496 :
    ThetaLowerSegment 3567370496 3567501568 (356730259759059 / 100000)
      (356743463405583 / 100000) := by
  exact
    packedTile65536 3567370496 3567501568 14 6003 59727 32 _ _ (549877 / 25000) (2199511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3567501568 :
    ThetaLowerSegment 3567501568 3567632640 (356743463405583 / 100000)
      (356756499913207 / 100000) := by
  exact
    packedTile65536 3567501568 3567632640 14 5927 59728 32 _ _ (274939 / 12500) (439903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3567632640 :
    ThetaLowerSegment 3567632640 3567763712 (356756499913207 / 100000)
      (44596212950219 / 12500) := by
  exact
    packedTile65536 3567632640 3567763712 14 6003 59729 32 _ _ (439903 / 20000) (1099759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3567763712 :
    ThetaLowerSegment 3567763712 3567894784 (44596212950219 / 12500) (178391439360281 / 50000) := by
  exact
    packedTile65536 3567763712 3567894784 14 5990 59730 32 _ _ (2199519 / 100000) (1099761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3567894784 :
    ThetaLowerSegment 3567894784 3568025856 (178391439360281 / 50000)
      (356796161639959 / 100000) := by
  exact
    packedTile65536 3567894784 3568025856 14 6039 59731 32 _ _ (2199523 / 100000) (1099763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3568025856 :
    ThetaLowerSegment 3568025856 3568156928 (356796161639959 / 100000)
      (356809154240041 / 100000) := by
  exact
    packedTile65536 3568025856 3568156928 14 5907 59732 32 _ _ (1099763 / 50000) (2199529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3568156928 :
    ThetaLowerSegment 3568156928 3568288000 (356809154240041 / 100000)
      (356822230445891 / 100000) := by
  exact
    packedTile65536 3568156928 3568288000 14 5945 59734 32 _ _ (219953 / 10000) (2199533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3568288000 :
    ThetaLowerSegment 3568288000 3568419072 (356822230445891 / 100000)
      (356835311074589 / 100000) := by
  exact
    packedTile65536 3568288000 3568419072 14 5947 59735 32 _ _ (1099767 / 50000) (2199537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3568419072 :
    ThetaLowerSegment 3568419072 3568550144 (356835311074589 / 100000)
      (356848411516961 / 100000) := by
  exact
    packedTile65536 3568419072 3568550144 14 5956 59736 32 _ _ (2199537 / 100000) (109977 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3568550144 :
    ThetaLowerSegment 3568550144 3568681216 (356848411516961 / 100000)
      (356861648354699 / 100000) := by
  exact
    packedTile65536 3568550144 3568681216 14 6018 59737 32 _ _ (2199541 / 100000) (274943 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3568681216 :
    ThetaLowerSegment 3568681216 3568812288 (356861648354699 / 100000)
      (178437355726227 / 50000) := by
  exact
    packedTile65536 3568681216 3568812288 14 5939 59738 32 _ _ (439909 / 20000) (549887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3568812288 :
    ThetaLowerSegment 3568812288 3568943360 (178437355726227 / 50000) (35688783615537 / 10000) := by
  exact
    packedTile65536 3568812288 3568943360 14 5967 59739 32 _ _ (549887 / 25000) (2199551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3568943360 :
    ThetaLowerSegment 3568943360 3569074432 (35688783615537 / 10000) (178450421053173 / 50000) := by
  exact
    packedTile65536 3568943360 3569074432 14 5913 59740 32 _ _ (68736 / 3125) (439911 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3569074432 :
    ThetaLowerSegment 3569074432 3569205504 (178450421053173 / 50000) (35691420220949 / 10000) := by
  exact
    packedTile65536 3569074432 3569205504 14 6074 59741 32 _ _ (549889 / 25000) (2199559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3569205504 :
    ThetaLowerSegment 3569205504 3569336576 (35691420220949 / 10000) (11153978074493 / 3125) := by
  exact
    packedTile65536 3569205504 3569336576 14 5954 59742 32 _ _ (2199559 / 100000) (1099781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3569336576 :
    ThetaLowerSegment 3569336576 3569467648 (11153978074493 / 3125) (356940629935119 / 100000) := by
  exact
    packedTile65536 3569336576 3569467648 14 6061 59743 32 _ _ (2199563 / 100000) (1099783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3569467648 :
    ThetaLowerSegment 3569467648 3569598720 (356940629935119 / 100000) (22309614071097 / 6250) := by
  exact
    packedTile65536 3569467648 3569598720 14 5999 59745 32 _ _ (2199567 / 100000) (219957 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3569598720 :
    ThetaLowerSegment 3569598720 3569729792 (22309614071097 / 6250) (178483479385011 / 50000) := by
  exact
    packedTile65536 3569598720 3569729792 14 5971 59746 32 _ _ (219957 / 10000) (2199573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3569729792 :
    ThetaLowerSegment 3569729792 3569860864 (178483479385011 / 50000) (11155628163271 / 3125) := by
  exact
    packedTile65536 3569729792 3569860864 14 5975 59747 32 _ _ (1099787 / 50000) (2199577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3569860864 :
    ThetaLowerSegment 3569860864 3569991936 (11155628163271 / 3125) (2231207236998 / 625) := by
  exact
    packedTile65536 3569860864 3569991936 14 5936 59748 32 _ _ (1099789 / 50000) (2199581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3569991936 :
    ThetaLowerSegment 3569991936 3570123008 (2231207236998 / 625) (357006463185149 / 100000) := by
  exact
    packedTile65536 3569991936 3570123008 14 6049 59749 32 _ _ (2199581 / 100000) (68737 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3570123008 :
    ThetaLowerSegment 3570123008 3570254080 (357006463185149 / 100000)
      (357019440736649 / 100000) := by
  exact
    packedTile65536 3570123008 3570254080 14 5900 59750 32 _ _ (439917 / 20000) (549897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3570254080 :
    ThetaLowerSegment 3570254080 3570385152 (357019440736649 / 100000)
      (44629089407033 / 12500) := by
  exact
    packedTile65536 3570254080 3570385152 14 6035 59751 32 _ _ (2199589 / 100000) (274949 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3570385152 :
    ThetaLowerSegment 3570385152 3570516224 (44629089407033 / 12500) (11157680582286 / 3125) := by
  exact
    packedTile65536 3570385152 3570516224 14 5939 59752 32 _ _ (274949 / 12500) (439919 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3570516224 :
    ThetaLowerSegment 3570516224 3570647296 (11157680582286 / 3125) (44632351679881 / 12500) := by
  exact
    packedTile65536 3570516224 3570647296 14 5926 59753 32 _ _ (549899 / 25000) (2199599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3570647296 :
    ThetaLowerSegment 3570647296 3570778368 (44632351679881 / 12500) (44633980208731 / 12500) := by
  exact
    packedTile65536 3570647296 3570778368 14 5923 59754 32 _ _ (5499 / 250) (2199603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3570778368 :
    ThetaLowerSegment 3570778368 3570909440 (44633980208731 / 12500)
      (357084852321593 / 100000) := by
  exact
    packedTile65536 3570778368 3570909440 14 5915 59755 32 _ _ (2199603 / 100000) (1099803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3570909440 :
    ThetaLowerSegment 3570909440 3571040512 (357084852321593 / 100000)
      (71419559841679 / 20000) := by
  exact
    packedTile65536 3570909440 3571040512 14 5886 59757 32 _ _ (2199607 / 100000) (219961 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3571040512 :
    ThetaLowerSegment 3571040512 3571171584 (71419559841679 / 20000) (2856886743213 / 800) := by
  exact
    packedTile65536 3571040512 3571171584 14 5930 59758 32 _ _ (2199611 / 100000) (1099807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3571171584 :
    ThetaLowerSegment 3571171584 3571302656 (2856886743213 / 800) (357124038386011 / 100000) := by
  exact
    packedTile65536 3571171584 3571302656 14 5999 59759 32 _ _ (1099807 / 50000) (2199617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3571302656 :
    ThetaLowerSegment 3571302656 3571433728 (357124038386011 / 100000)
      (357137280086371 / 100000) := by
  exact
    packedTile65536 3571302656 3571433728 14 6020 59760 32 _ _ (1099809 / 50000) (2199621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3571433728 :
    ThetaLowerSegment 3571433728 3571564800 (357137280086371 / 100000)
      (357150486616859 / 100000) := by
  exact
    packedTile65536 3571433728 3571564800 14 6004 59761 32 _ _ (1099811 / 50000) (17597 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3571564800 :
    ThetaLowerSegment 3571564800 3571695872 (357150486616859 / 100000)
      (357163697564609 / 100000) := by
  exact
    packedTile65536 3571564800 3571695872 14 6006 59762 32 _ _ (17597 / 800) (549907 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3571695872 :
    ThetaLowerSegment 3571695872 3571826944 (357163697564609 / 100000)
      (357176802954191 / 100000) := by
  exact
    packedTile65536 3571695872 3571826944 14 5958 59763 32 _ _ (2199629 / 100000) (137477 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3571826944 :
    ThetaLowerSegment 3571826944 3571958016 (357176802954191 / 100000)
      (178594946485087 / 50000) := by
  exact
    packedTile65536 3571826944 3571958016 14 5951 59764 32 _ _ (2199633 / 100000) (549909 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3571958016 :
    ThetaLowerSegment 3571958016 3572089088 (178594946485087 / 50000)
      (178601481603643 / 50000) := by
  exact
    packedTile65536 3571958016 3572089088 14 5942 59765 32 _ _ (549909 / 25000) (2199639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3572089088 :
    ThetaLowerSegment 3572089088 3572220160 (178601481603643 / 50000)
      (178608017833903 / 50000) := by
  exact
    packedTile65536 3572089088 3572220160 14 5943 59766 32 _ _ (54991 / 2500) (2199643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3572220160 :
    ThetaLowerSegment 3572220160 3572351232 (178608017833903 / 50000) (35722900476883 / 10000) := by
  exact
    packedTile65536 3572220160 3572351232 14 5896 59768 32 _ _ (549911 / 25000) (2199647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3572351232 :
    ThetaLowerSegment 3572351232 3572482304 (35722900476883 / 10000)
      (357242055274481 / 100000) := by
  exact
    packedTile65536 3572351232 3572482304 14 5933 59769 32 _ _ (2199647 / 100000) (43993 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3572482304 :
    ThetaLowerSegment 3572482304 3572613376 (357242055274481 / 100000) (22328449611869 / 6250) := by
  exact
    packedTile65536 3572482304 3572613376 14 5973 59770 32 _ _ (2199651 / 100000) (1099827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3572613376 :
    ThetaLowerSegment 3572613376 3572744448 (22328449611869 / 6250) (357268358725079 / 100000) := by
  exact
    packedTile65536 3572613376 3572744448 14 5985 59771 32 _ _ (439931 / 20000) (1099829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3572744448 :
    ThetaLowerSegment 3572744448 3572875520 (357268358725079 / 100000)
      (357281426893257 / 100000) := by
  exact
    packedTile65536 3572744448 3572875520 14 5941 59772 32 _ _ (1099829 / 50000) (2199661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3572875520 :
    ThetaLowerSegment 3572875520 3573006592 (357281426893257 / 100000)
      (357294330110549 / 100000) := by
  exact
    packedTile65536 3572875520 3573006592 14 5866 59773 32 _ _ (1099831 / 50000) (439933 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3573006592 :
    ThetaLowerSegment 3573006592 3573137664 (357294330110549 / 100000)
      (357307532505881 / 100000) := by
  exact
    packedTile65536 3573006592 3573137664 14 6002 59774 32 _ _ (1099833 / 50000) (2199669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3573137664 :
    ThetaLowerSegment 3573137664 3573268736 (357307532505881 / 100000)
      (178660348762423 / 50000) := by
  exact
    packedTile65536 3573137664 3573268736 14 5985 59775 32 _ _ (2199669 / 100000) (274959 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3573268736 :
    ThetaLowerSegment 3573268736 3573399808 (178660348762423 / 50000)
      (357333840571021 / 100000) := by
  exact
    packedTile65536 3573268736 3573399808 14 5975 59776 32 _ _ (2199673 / 100000) (549919 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3573399808 :
    ThetaLowerSegment 3573399808 3573530880 (357333840571021 / 100000)
      (89336770106721 / 25000) := by
  exact
    packedTile65536 3573399808 3573530880 14 6019 59777 32 _ _ (2199677 / 100000) (13748 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3573530880 :
    ThetaLowerSegment 3573530880 3573661952 (89336770106721 / 25000) (89340025633121 / 25000) := by
  exact
    packedTile65536 3573530880 3573661952 14 5920 59779 32 _ _ (13748 / 625) (2199683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3573661952 :
    ThetaLowerSegment 3573661952 3573793024 (89340025633121 / 25000) (22335840500957 / 6250) := by
  exact
    packedTile65536 3573661952 3573793024 14 6067 59780 32 _ _ (549921 / 25000) (2199687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3573793024 :
    ThetaLowerSegment 3573793024 3573924096 (22335840500957 / 6250) (44673290898569 / 12500) := by
  exact
    packedTile65536 3573793024 3573924096 14 5855 59781 32 _ _ (274961 / 12500) (2199691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3573924096 :
    ThetaLowerSegment 3573924096 3574055168 (44673290898569 / 12500) (11168725405759 / 3125) := by
  exact
    packedTile65536 3573924096 3574055168 14 5858 59782 32 _ _ (549923 / 25000) (439939 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3574055168 :
    ThetaLowerSegment 3574055168 3574186240 (11168725405759 / 3125) (178706176981109 / 50000) := by
  exact
    packedTile65536 3574055168 3574186240 14 5974 59783 32 _ _ (439939 / 20000) (1099849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3574186240 :
    ThetaLowerSegment 3574186240 3574317312 (178706176981109 / 50000)
      (178712754081119 / 50000) := by
  exact
    packedTile65536 3574186240 3574317312 14 5980 59784 32 _ _ (2199699 / 100000) (1099851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3574317312 :
    ThetaLowerSegment 3574317312 3574448384 (178712754081119 / 50000) (71487692442641 / 20000) := by
  exact
    packedTile65536 3574317312 3574448384 14 5889 59785 32 _ _ (2199703 / 100000) (1099853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3574448384 :
    ThetaLowerSegment 3574448384 3574579456 (71487692442641 / 20000)
      (357451376687131 / 100000) := by
  exact
    packedTile65536 3574448384 3574579456 14 5871 59786 32 _ _ (1099853 / 50000) (2199709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3574579456 :
    ThetaLowerSegment 3574579456 3574710528 (357451376687131 / 100000)
      (357464332979031 / 100000) := by
  exact
    packedTile65536 3574579456 3574710528 14 5890 59787 32 _ _ (219971 / 10000) (2199713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3574710528 :
    ThetaLowerSegment 3574710528 3574841600 (357464332979031 / 100000)
      (71495478096267 / 20000) := by
  exact
    packedTile65536 3574710528 3574841600 14 5936 59788 32 _ _ (1099857 / 50000) (2199717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3574841600 :
    ThetaLowerSegment 3574841600 3574972672 (71495478096267 / 20000)
      (357490461199749 / 100000) := by
  exact
    packedTile65536 3574841600 3574972672 14 5942 59789 32 _ _ (2199717 / 100000) (54993 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3574972672 :
    ThetaLowerSegment 3574972672 3575103744 (357490461199749 / 100000) (71500701549 / 20) := by
  exact
    packedTile65536 3574972672 3575103744 14 5931 59791 32 _ _ (2199721 / 100000) (549931 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3575103744 :
    ThetaLowerSegment 3575103744 3575234816 (71500701549 / 20) (14300669035701 / 4000) := by
  exact
    packedTile65536 3575103744 3575234816 14 6009 59792 32 _ _ (87989 / 4000) (137483 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3575234816 :
    ThetaLowerSegment 3575234816 3575365888 (14300669035701 / 4000) (357529884665421 / 100000) := by
  exact
    packedTile65536 3575234816 3575365888 14 5982 59793 32 _ _ (137483 / 6250) (2199731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3575365888 :
    ThetaLowerSegment 3575365888 3575496960 (357529884665421 / 100000)
      (71508597693789 / 20000) := by
  exact
    packedTile65536 3575365888 3575496960 14 5957 59794 32 _ _ (549933 / 25000) (439947 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3575496960 :
    ThetaLowerSegment 3575496960 3575628032 (71508597693789 / 20000)
      (357556059300257 / 100000) := by
  exact
    packedTile65536 3575496960 3575628032 14 5942 59795 32 _ _ (274967 / 12500) (2199739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3575628032 :
    ThetaLowerSegment 3575628032 3575759104 (357556059300257 / 100000)
      (178784623367781 / 50000) := by
  exact
    packedTile65536 3575628032 3575759104 14 5995 59796 32 _ _ (2199739 / 100000) (1099871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3575759104 :
    ThetaLowerSegment 3575759104 3575890176 (178784623367781 / 50000) (35758234840487 / 10000) := by
  exact
    packedTile65536 3575759104 3575890176 14 5956 59797 32 _ _ (2199743 / 100000) (1099873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3575890176 :
    ThetaLowerSegment 3575890176 3576021248 (35758234840487 / 10000) (178797753642721 / 50000) := by
  exact
    packedTile65536 3575890176 3576021248 14 5982 59798 32 _ _ (1099873 / 50000) (2199749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3576021248 :
    ThetaLowerSegment 3576021248 3576152320 (178797753642721 / 50000) (44701079699149 / 12500) := by
  exact
    packedTile65536 3576021248 3576152320 14 5969 59799 32 _ _ (8799 / 400) (2199753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3576152320 :
    ThetaLowerSegment 3576152320 3576283392 (44701079699149 / 12500) (89405451330159 / 25000) := by
  exact
    packedTile65536 3576152320 3576283392 14 5986 59800 32 _ _ (1099877 / 50000) (2199757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3576283392 :
    ThetaLowerSegment 3576283392 3576414464 (89405451330159 / 25000)
      (357634715694469 / 100000) := by
  exact
    packedTile65536 3576283392 3576414464 14 5869 59802 32 _ _ (2199757 / 100000) (27497 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3576414464 :
    ThetaLowerSegment 3576414464 3576545536 (357634715694469 / 100000)
      (357647689884847 / 100000) := by
  exact
    packedTile65536 3576414464 3576545536 14 5898 59803 32 _ _ (2199761 / 100000) (549941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3576545536 :
    ThetaLowerSegment 3576545536 3576676608 (357647689884847 / 100000)
      (357660791685187 / 100000) := by
  exact
    packedTile65536 3576545536 3576676608 14 5956 59804 32 _ _ (439953 / 20000) (274971 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3576676608 :
    ThetaLowerSegment 3576676608 3576807680 (357660791685187 / 100000) (14306952220507 / 4000) := by
  exact
    packedTile65536 3576676608 3576807680 14 5916 59805 32 _ _ (274971 / 12500) (2199771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3576807680 :
    ThetaLowerSegment 3576807680 3576938752 (14306952220507 / 4000) (71537381030987 / 20000) := by
  exact
    packedTile65536 3576807680 3576938752 14 5955 59806 32 _ _ (549943 / 25000) (87991 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3576938752 :
    ThetaLowerSegment 3576938752 3577069824 (71537381030987 / 20000)
      (357699978423703 / 100000) := by
  exact
    packedTile65536 3576938752 3577069824 14 5943 59807 32 _ _ (68743 / 3125) (2199779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3577069824 :
    ThetaLowerSegment 3577069824 3577200896 (357699978423703 / 100000)
      (89428236530227 / 25000) := by
  exact
    packedTile65536 3577069824 3577200896 14 5895 59808 32 _ _ (2199779 / 100000) (1099891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3577200896 :
    ThetaLowerSegment 3577200896 3577331968 (89428236530227 / 25000) (44715778001387 / 12500) := by
  exact
    packedTile65536 3577200896 3577331968 14 6036 59809 32 _ _ (2199783 / 100000) (1099893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3577331968 :
    ThetaLowerSegment 3577331968 3577463040 (44715778001387 / 12500) (178869797158241 / 50000) := by
  exact
    packedTile65536 3577331968 3577463040 14 6078 59810 32 _ _ (2199787 / 100000) (219979 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3577463040 :
    ThetaLowerSegment 3577463040 3577594112 (178869797158241 / 50000) (89438199913963 / 25000) := by
  exact
    packedTile65536 3577463040 3577594112 14 6003 59811 32 _ _ (219979 / 10000) (2199793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3577594112 :
    ThetaLowerSegment 3577594112 3577725184 (89438199913963 / 25000) (11180180438777 / 3125) := by
  exact
    packedTile65536 3577594112 3577725184 14 5898 59812 32 _ _ (1099897 / 50000) (2199797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3577725184 :
    ThetaLowerSegment 3577725184 3577856256 (11180180438777 / 3125) (178889381924027 / 50000) := by
  exact
    packedTile65536 3577725184 3577856256 14 5905 59814 32 _ _ (1099899 / 50000) (2199801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3577856256 :
    ThetaLowerSegment 3577856256 3577987328 (178889381924027 / 50000) (71558406169577 / 20000) := by
  exact
    packedTile65536 3577856256 3577987328 14 6031 59815 32 _ _ (2199801 / 100000) (549951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3577987328 :
    ThetaLowerSegment 3577987328 3578118400 (71558406169577 / 20000) (35780518788159 / 10000) := by
  exact
    packedTile65536 3577987328 3578118400 14 5981 59816 32 _ _ (439961 / 20000) (68744 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3578118400 :
    ThetaLowerSegment 3578118400 3578249472 (35780518788159 / 10000)
      (357818239348387 / 100000) := by
  exact
    packedTile65536 3578118400 3578249472 14 5933 59817 32 _ _ (2199809 / 100000) (549953 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3578249472 :
    ThetaLowerSegment 3578249472 3578380544 (357818239348387 / 100000)
      (357831420621891 / 100000) := by
  exact
    packedTile65536 3578249472 3578380544 14 5992 59818 32 _ _ (549953 / 25000) (439963 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3578380544 :
    ThetaLowerSegment 3578380544 3578511616 (357831420621891 / 100000)
      (357844632716787 / 100000) := by
  exact
    packedTile65536 3578380544 3578511616 14 6006 59819 32 _ _ (274977 / 12500) (2199819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3578511616 :
    ThetaLowerSegment 3578511616 3578642688 (357844632716787 / 100000)
      (357857679849207 / 100000) := by
  exact
    packedTile65536 3578511616 3578642688 14 5931 59820 32 _ _ (109991 / 5000) (2199823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3578642688 :
    ThetaLowerSegment 3578642688 3578773760 (357857679849207 / 100000)
      (71574151999353 / 20000) := by
  exact
    packedTile65536 3578642688 3578773760 14 5946 59821 32 _ _ (2199823 / 100000) (1099913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3578773760 :
    ThetaLowerSegment 3578773760 3578904832 (71574151999353 / 20000) (89470952892589 / 25000) := by
  exact
    packedTile65536 3578773760 3578904832 14 5933 59822 32 _ _ (2199827 / 100000) (219983 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3578904832 :
    ThetaLowerSegment 3578904832 3579035904 (89470952892589 / 25000) (178948406285783 / 50000) := by
  exact
    packedTile65536 3578904832 3579035904 14 5910 59823 32 _ _ (2199831 / 100000) (1099917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3579035904 :
    ThetaLowerSegment 3579035904 3579166976 (178948406285783 / 50000) (44738727523751 / 12500) := by
  exact
    packedTile65536 3579035904 3579166976 14 5913 59825 32 _ _ (1099917 / 50000) (2199837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3579166976 :
    ThetaLowerSegment 3579166976 3579298048 (44738727523751 / 12500) (89480753704583 / 25000) := by
  exact
    packedTile65536 3579166976 3579298048 14 5998 59826 32 _ _ (1099919 / 50000) (2199841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3579298048 :
    ThetaLowerSegment 3579298048 3579429120 (89480753704583 / 25000) (178968114634613 / 50000) := by
  exact
    packedTile65536 3579298048 3579429120 14 6007 59827 32 _ _ (1099921 / 50000) (439969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3579429120 :
    ThetaLowerSegment 3579429120 3579560192 (178968114634613 / 50000) (89487292189379 / 25000) := by
  exact
    packedTile65536 3579429120 3579560192 14 5882 59828 32 _ _ (439969 / 20000) (274981 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3579560192 :
    ThetaLowerSegment 3579560192 3579691264 (89487292189379 / 25000)
      (357962119268579 / 100000) := by
  exact
    packedTile65536 3579560192 3579691264 14 5887 59829 32 _ _ (2199849 / 100000) (549963 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3579691264 :
    ThetaLowerSegment 3579691264 3579822336 (357962119268579 / 100000)
      (178987499703947 / 50000) := by
  exact
    packedTile65536 3579691264 3579822336 14 5855 59830 32 _ _ (2199853 / 100000) (137491 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3579822336 :
    ThetaLowerSegment 3579822336 3579953408 (178987499703947 / 50000)
      (178994187266187 / 50000) := by
  exact
    packedTile65536 3579822336 3579953408 14 6080 59831 32 _ _ (137491 / 6250) (2199859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3579953408 :
    ThetaLowerSegment 3579953408 3580084480 (178994187266187 / 50000)
      (179000792345837 / 50000) := by
  exact
    packedTile65536 3579953408 3580084480 14 6005 59832 32 _ _ (109993 / 5000) (2199863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3580084480 :
    ThetaLowerSegment 3580084480 3580215552 (179000792345837 / 50000)
      (179007358939877 / 50000) := by
  exact
    packedTile65536 3580084480 3580215552 14 5970 59833 32 _ _ (274983 / 12500) (2199867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3580215552 :
    ThetaLowerSegment 3580215552 3580346624 (179007358939877 / 50000)
      (179014006937951 / 50000) := by
  exact
    packedTile65536 3580215552 3580346624 14 6044 59834 32 _ _ (2199867 / 100000) (219987 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3580346624 :
    ThetaLowerSegment 3580346624 3580477696 (179014006937951 / 50000)
      (358041232900741 / 100000) := by
  exact
    packedTile65536 3580346624 3580477696 14 6009 59835 32 _ _ (2199871 / 100000) (1099937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3580477696 :
    ThetaLowerSegment 3580477696 3580608768 (358041232900741 / 100000)
      (179027210575683 / 50000) := by
  exact
    packedTile65536 3580477696 3580608768 14 5995 59837 32 _ _ (17599 / 800) (1099939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3580608768 :
    ThetaLowerSegment 3580608768 3580739840 (179027210575683 / 50000) (89516896855299 / 25000) := by
  exact
    packedTile65536 3580608768 3580739840 14 5985 59838 32 _ _ (1099939 / 50000) (2199881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3580739840 :
    ThetaLowerSegment 3580739840 3580870912 (89516896855299 / 25000) (179040297661731 / 50000) := by
  exact
    packedTile65536 3580739840 3580870912 14 5913 59839 32 _ _ (1099941 / 50000) (439977 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3580870912 :
    ThetaLowerSegment 3580870912 3581001984 (179040297661731 / 50000) (11190429638808 / 3125) := by
  exact
    packedTile65536 3580870912 3581001984 14 5979 59840 32 _ _ (1099943 / 50000) (2199889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3581001984 :
    ThetaLowerSegment 3581001984 3581133056 (11190429638808 / 3125) (358106954375523 / 100000) := by
  exact
    packedTile65536 3581001984 3581133056 14 6003 59841 32 _ _ (2199889 / 100000) (549973 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3581133056 :
    ThetaLowerSegment 3581133056 3581264128 (358106954375523 / 100000)
      (358119982141869 / 100000) := by
  exact
    packedTile65536 3581133056 3581264128 14 5922 59842 32 _ _ (2199893 / 100000) (274987 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3581264128 :
    ThetaLowerSegment 3581264128 3581395200 (358119982141869 / 100000)
      (358133027531079 / 100000) := by
  exact
    packedTile65536 3581264128 3581395200 14 5930 59843 32 _ _ (2199897 / 100000) (21999 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3581395200 :
    ThetaLowerSegment 3581395200 3581526272 (358133027531079 / 100000)
      (358146306127479 / 100000) := by
  exact
    packedTile65536 3581395200 3581526272 14 6036 59844 32 _ _ (21999 / 1000) (2199903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3581526272 :
    ThetaLowerSegment 3581526272 3581657344 (358146306127479 / 100000)
      (358159428554839 / 100000) := by
  exact
    packedTile65536 3581526272 3581657344 14 5965 59845 32 _ _ (68747 / 3125) (2199907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3581657344 :
    ThetaLowerSegment 3581657344 3581788416 (358159428554839 / 100000)
      (358172320015719 / 100000) := by
  exact
    packedTile65536 3581657344 3581788416 14 5860 59846 32 _ _ (549977 / 25000) (2199911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3581788416 :
    ThetaLowerSegment 3581788416 3581919488 (358172320015719 / 100000)
      (89546403519473 / 25000) := by
  exact
    packedTile65536 3581788416 3581919488 14 6043 59848 32 _ _ (2199911 / 100000) (1099957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3581919488 :
    ThetaLowerSegment 3581919488 3582050560 (89546403519473 / 25000) (179099356185901 / 50000) := by
  exact
    packedTile65536 3581919488 3582050560 14 5954 59849 32 _ _ (439983 / 20000) (1099959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3582050560 :
    ThetaLowerSegment 3582050560 3582181632 (179099356185901 / 50000)
      (358211808489609 / 100000) := by
  exact
    packedTile65536 3582050560 3582181632 14 5953 59850 32 _ _ (2199919 / 100000) (1099961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3582181632 :
    ThetaLowerSegment 3582181632 3582312704 (358211808489609 / 100000)
      (358224953023559 / 100000) := by
  exact
    packedTile65536 3582181632 3582312704 14 5975 59851 32 _ _ (1099961 / 50000) (87997 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3582312704 :
    ThetaLowerSegment 3582312704 3582443776 (358224953023559 / 100000)
      (358238163579189 / 100000) := by
  exact
    packedTile65536 3582312704 3582443776 14 6005 59852 32 _ _ (1099963 / 50000) (2199929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3582443776 :
    ThetaLowerSegment 3582443776 3582574848 (358238163579189 / 100000)
      (358251345559749 / 100000) := by
  exact
    packedTile65536 3582443776 3582574848 14 5992 59853 32 _ _ (219993 / 10000) (2199933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3582574848 :
    ThetaLowerSegment 3582574848 3582705920 (358251345559749 / 100000)
      (358264426361367 / 100000) := by
  exact
    packedTile65536 3582574848 3582705920 14 5946 59854 32 _ _ (2199933 / 100000) (68748 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3582705920 :
    ThetaLowerSegment 3582705920 3582836992 (358264426361367 / 100000)
      (358277533586013 / 100000) := by
  exact
    packedTile65536 3582705920 3582836992 14 5958 59855 32 _ _ (2199937 / 100000) (109997 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3582836992 :
    ThetaLowerSegment 3582836992 3582968064 (358277533586013 / 100000)
      (358290874028237 / 100000) := by
  exact
    packedTile65536 3582836992 3582968064 14 6064 59856 32 _ _ (2199941 / 100000) (274993 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3582968064 :
    ThetaLowerSegment 3582968064 3583099136 (358290874028237 / 100000)
      (71660762819769 / 20000) := by
  exact
    packedTile65536 3582968064 3583099136 14 5882 59857 32 _ _ (274993 / 12500) (2199947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3583099136 :
    ThetaLowerSegment 3583099136 3583230208 (71660762819769 / 20000) (71663371958097 / 20000) := by
  exact
    packedTile65536 3583099136 3583230208 14 5930 59858 32 _ _ (549987 / 25000) (2199951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3583230208 :
    ThetaLowerSegment 3583230208 3583361280 (71663371958097 / 20000)
      (358330000103781 / 100000) := by
  exact
    packedTile65536 3583230208 3583361280 14 5973 59860 32 _ _ (137497 / 6250) (439991 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3583361280 :
    ThetaLowerSegment 3583361280 3583492352 (358330000103781 / 100000)
      (179171554817813 / 50000) := by
  exact
    packedTile65536 3583361280 3583492352 14 5959 59861 32 _ _ (439991 / 20000) (1099979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3583492352 :
    ThetaLowerSegment 3583492352 3583623424 (179171554817813 / 50000)
      (358356131192947 / 100000) := by
  exact
    packedTile65536 3583492352 3583623424 14 5919 59862 32 _ _ (2199959 / 100000) (1099981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3583623424 :
    ThetaLowerSegment 3583623424 3583754496 (358356131192947 / 100000)
      (358369229772649 / 100000) := by
  exact
    packedTile65536 3583623424 3583754496 14 5954 59863 32 _ _ (2199963 / 100000) (1099983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3583754496 :
    ThetaLowerSegment 3583754496 3583885568 (358369229772649 / 100000)
      (358382345969941 / 100000) := by
  exact
    packedTile65536 3583754496 3583885568 14 5962 59864 32 _ _ (1099983 / 50000) (2199969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3583885568 :
    ThetaLowerSegment 3583885568 3584016640 (358382345969941 / 100000)
      (358395352192581 / 100000) := by
  exact
    packedTile65536 3583885568 3584016640 14 5912 59865 32 _ _ (219997 / 10000) (2199973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3584016640 :
    ThetaLowerSegment 3584016640 3584147712 (358395352192581 / 100000)
      (44801066528853 / 12500) := by
  exact
    packedTile65536 3584016640 3584147712 14 5991 59866 32 _ _ (2199973 / 100000) (274997 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3584147712 :
    ThetaLowerSegment 3584147712 3584278784 (44801066528853 / 12500)
      (358421567094549 / 100000) := by
  exact
    packedTile65536 3584147712 3584278784 14 5925 59867 32 _ _ (2199977 / 100000) (109999 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3584278784 :
    ThetaLowerSegment 3584278784 3584409856 (358421567094549 / 100000) (22402162898871 / 6250) := by
  exact
    packedTile65536 3584278784 3584409856 14 5927 59868 32 _ _ (2199981 / 100000) (137499 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3584409856 :
    ThetaLowerSegment 3584409856 3584540928 (22402162898871 / 6250) (89611880622 / 25) := by
  exact
    packedTile65536 3584409856 3584540928 14 5871 59869 32 _ _ (137499 / 6250) (2199987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3584540928 :
    ThetaLowerSegment 3584540928 3584672000 (89611880622 / 25) (22403791301021 / 6250) := by
  exact
    packedTile65536 3584540928 3584672000 14 5972 59871 32 _ _ (549997 / 25000) (2199991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3584672000 :
    ThetaLowerSegment 3584672000 3584803072 (22403791301021 / 6250) (2240461382303 / 625) := by
  exact
    packedTile65536 3584672000 3584803072 14 5982 59872 32 _ _ (274999 / 12500) (439999 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3584803072 :
    ThetaLowerSegment 3584803072 3584934144 (2240461382303 / 625) (71697397627711 / 20000) := by
  exact
    packedTile65536 3584803072 3584934144 14 5985 59873 32 _ _ (439999 / 20000) (1099999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3584934144 :
    ThetaLowerSegment 3584934144 3585065216 (71697397627711 / 20000) (71699989226533 / 20000) := by
  exact
    packedTile65536 3584934144 3585065216 14 5890 59874 32 _ _ (2199999 / 100000) (1100001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3585065216 :
    ThetaLowerSegment 3585065216 3585196288 (71699989226533 / 20000) (179256483975211 / 50000) := by
  exact
    packedTile65536 3585065216 3585196288 14 5919 59875 32 _ _ (2200003 / 100000) (1100003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3585196288 :
    ThetaLowerSegment 3585196288 3585327360 (179256483975211 / 50000) (89631553546637 / 25000) := by
  exact
    packedTile65536 3585196288 3585327360 14 6021 59876 32 _ _ (1100003 / 50000) (2200009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3585327360 :
    ThetaLowerSegment 3585327360 3585458432 (89631553546637 / 25000) (179269703823259 / 50000) := by
  exact
    packedTile65536 3585327360 3585458432 14 5997 59877 32 _ _ (220001 / 10000) (2200013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3585458432 :
    ThetaLowerSegment 3585458432 3585589504 (179269703823259 / 50000) (89638112882381 / 25000) := by
  exact
    packedTile65536 3585458432 3585589504 14 5929 59878 32 _ _ (1100007 / 50000) (2200017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3585589504 :
    ThetaLowerSegment 3585589504 3585720576 (89638112882381 / 25000)
      (358565521830521 / 100000) := by
  exact
    packedTile65536 3585589504 3585720576 14 5941 59879 32 _ _ (2200017 / 100000) (110001 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3585720576 :
    ThetaLowerSegment 3585720576 3585851648 (358565521830521 / 100000)
      (35857856575503 / 10000) := by
  exact
    packedTile65536 3585720576 3585851648 14 5929 59880 32 _ _ (2200021 / 100000) (275003 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3585851648 :
    ThetaLowerSegment 3585851648 3585982720 (35857856575503 / 10000) (71718380901321 / 20000) := by
  exact
    packedTile65536 3585851648 3585982720 14 6063 59881 32 _ _ (88001 / 4000) (550007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3585982720 :
    ThetaLowerSegment 3585982720 3586113792 (71718380901321 / 20000) (71720992334557 / 20000) := by
  exact
    packedTile65536 3585982720 3586113792 14 5935 59883 32 _ _ (550007 / 25000) (2200031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3586113792 :
    ThetaLowerSegment 3586113792 3586244864 (71720992334557 / 20000)
      (358617950661713 / 100000) := by
  exact
    packedTile65536 3586113792 3586244864 14 5904 59884 32 _ _ (68751 / 3125) (440007 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3586244864 :
    ThetaLowerSegment 3586244864 3586375936 (358617950661713 / 100000)
      (358630867073069 / 100000) := by
  exact
    packedTile65536 3586244864 3586375936 14 5871 59885 32 _ _ (550009 / 25000) (2200039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3586375936 :
    ThetaLowerSegment 3586375936 3586507008 (358630867073069 / 100000)
      (358643908904261 / 100000) := by
  exact
    packedTile65536 3586375936 3586507008 14 5928 59886 32 _ _ (2200039 / 100000) (1100021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3586507008 :
    ThetaLowerSegment 3586507008 3586638080 (358643908904261 / 100000)
      (179328540280851 / 50000) := by
  exact
    packedTile65536 3586507008 3586638080 14 5987 59887 32 _ _ (2200043 / 100000) (1100023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3586638080 :
    ThetaLowerSegment 3586638080 3586769152 (179328540280851 / 50000)
      (358670067439143 / 100000) := by
  exact
    packedTile65536 3586638080 3586769152 14 5903 59888 32 _ _ (2200047 / 100000) (44001 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3586769152 :
    ThetaLowerSegment 3586769152 3586900224 (358670067439143 / 100000)
      (358683223738143 / 100000) := by
  exact
    packedTile65536 3586769152 3586900224 14 5980 59889 32 _ _ (44001 / 2000) (2200053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3586900224 :
    ThetaLowerSegment 3586900224 3587031296 (358683223738143 / 100000)
      (358696347060253 / 100000) := by
  exact
    packedTile65536 3586900224 3587031296 14 5965 59890 32 _ _ (1100027 / 50000) (2200057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3587031296 :
    ThetaLowerSegment 3587031296 3587162368 (358696347060253 / 100000) (14348382688351 / 4000) := by
  exact
    packedTile65536 3587031296 3587162368 14 6009 59891 32 _ _ (1100029 / 50000) (2200061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3587162368 :
    ThetaLowerSegment 3587162368 3587293440 (14348382688351 / 4000) (179361329885893 / 50000) := by
  exact
    packedTile65536 3587162368 3587293440 14 5951 59892 32 _ _ (2200061 / 100000) (68752 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3587293440 :
    ThetaLowerSegment 3587293440 3587424512 (179361329885893 / 50000)
      (358735756758731 / 100000) := by
  exact
    packedTile65536 3587293440 3587424512 14 5953 59894 32 _ _ (440013 / 20000) (550017 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3587424512 :
    ThetaLowerSegment 3587424512 3587555584 (358735756758731 / 100000)
      (358748965973007 / 100000) := by
  exact
    packedTile65536 3587424512 3587555584 14 6004 59895 32 _ _ (2200069 / 100000) (275009 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3587555584 :
    ThetaLowerSegment 3587555584 3587686656 (358748965973007 / 100000)
      (358762034400687 / 100000) := by
  exact
    packedTile65536 3587555584 3587686656 14 5940 59896 32 _ _ (275009 / 12500) (88003 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3587686656 :
    ThetaLowerSegment 3587686656 3587817728 (358762034400687 / 100000)
      (358775212855927 / 100000) := by
  exact
    packedTile65536 3587686656 3587817728 14 5990 59897 32 _ _ (550019 / 25000) (2200079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3587817728 :
    ThetaLowerSegment 3587817728 3587948800 (358775212855927 / 100000)
      (358788360528031 / 100000) := by
  exact
    packedTile65536 3587817728 3587948800 14 5976 59898 32 _ _ (2200079 / 100000) (1100041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3587948800 :
    ThetaLowerSegment 3587948800 3588079872 (358788360528031 / 100000)
      (71760284924177 / 20000) := by
  exact
    packedTile65536 3587948800 3588079872 14 5938 59899 32 _ _ (2200083 / 100000) (1100043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3588079872 :
    ThetaLowerSegment 3588079872 3588210944 (71760284924177 / 20000)
      (358814519538709 / 100000) := by
  exact
    packedTile65536 3588079872 3588210944 14 5952 59900 32 _ _ (2200087 / 100000) (220009 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3588210944 :
    ThetaLowerSegment 3588210944 3588342016 (358814519538709 / 100000)
      (358827643075559 / 100000) := by
  exact
    packedTile65536 3588210944 3588342016 14 5965 59901 32 _ _ (220009 / 10000) (2200093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3588342016 :
    ThetaLowerSegment 3588342016 3588473088 (358827643075559 / 100000)
      (358840696233261 / 100000) := by
  exact
    packedTile65536 3588342016 3588473088 14 5933 59902 32 _ _ (1100047 / 50000) (2200097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3588473088 :
    ThetaLowerSegment 3588473088 3588604160 (358840696233261 / 100000)
      (358853907821751 / 100000) := by
  exact
    packedTile65536 3588473088 3588604160 14 6005 59903 32 _ _ (1100049 / 50000) (2200101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3588604160 :
    ThetaLowerSegment 3588604160 3588735232 (358853907821751 / 100000)
      (179433500311401 / 50000) := by
  exact
    packedTile65536 3588604160 3588735232 14 5951 59904 32 _ _ (2200101 / 100000) (275013 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3588735232 :
    ThetaLowerSegment 3588735232 3588866304 (179433500311401 / 50000)
      (358879987842617 / 100000) := by
  exact
    packedTile65536 3588735232 3588866304 14 5903 59906 32 _ _ (440021 / 20000) (550027 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3588866304 :
    ThetaLowerSegment 3588866304 3588997376 (358879987842617 / 100000)
      (358893206097489 / 100000) := by
  exact
    packedTile65536 3588866304 3588997376 14 6008 59907 32 _ _ (2200109 / 100000) (137507 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3588997376 :
    ThetaLowerSegment 3588997376 3589128448 (358893206097489 / 100000)
      (358906305564337 / 100000) := by
  exact
    packedTile65536 3588997376 3589128448 14 5954 59908 32 _ _ (137507 / 6250) (440023 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3589128448 :
    ThetaLowerSegment 3589128448 3589259520 (358906305564337 / 100000)
      (358919396254537 / 100000) := by
  exact
    packedTile65536 3589128448 3589259520 14 5950 59909 32 _ _ (550029 / 25000) (2200119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3589259520 :
    ThetaLowerSegment 3589259520 3589390592 (358919396254537 / 100000)
      (358932328559897 / 100000) := by
  exact
    packedTile65536 3589259520 3589390592 14 5878 59910 32 _ _ (55003 / 2500) (2200123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3589390592 :
    ThetaLowerSegment 3589390592 3589521664 (358932328559897 / 100000)
      (71789086498497 / 20000) := by
  exact
    packedTile65536 3589390592 3589521664 14 5956 59911 32 _ _ (2200123 / 100000) (1100063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3589521664 :
    ThetaLowerSegment 3589521664 3589652736 (71789086498497 / 20000) (44869832732017 / 12500) := by
  exact
    packedTile65536 3589521664 3589652736 14 6013 59912 32 _ _ (2200127 / 100000) (220013 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3589652736 :
    ThetaLowerSegment 3589652736 3589783808 (44869832732017 / 12500) (71794354487353 / 20000) := by
  exact
    packedTile65536 3589652736 3589783808 14 5959 59913 32 _ _ (2200131 / 100000) (1100067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3589783808 :
    ThetaLowerSegment 3589783808 3589914880 (71794354487353 / 20000)
      (358984704824417 / 100000) := by
  exact
    packedTile65536 3589783808 3589914880 14 5878 59914 32 _ _ (1100067 / 50000) (2200137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3589914880 :
    ThetaLowerSegment 3589914880 3590045952 (358984704824417 / 100000)
      (358997850648967 / 100000) := by
  exact
    packedTile65536 3589914880 3590045952 14 5975 59915 32 _ _ (1100069 / 50000) (2200141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3590045952 :
    ThetaLowerSegment 3590045952 3590177024 (358997850648967 / 100000)
      (71802194459171 / 20000) := by
  exact
    packedTile65536 3590045952 3590177024 14 5964 59916 32 _ _ (1100071 / 50000) (440029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3590177024 :
    ThetaLowerSegment 3590177024 3590308096 (71802194459171 / 20000) (71804800310909 / 20000) := by
  exact
    packedTile65536 3590177024 3590308096 14 5922 59918 32 _ _ (440029 / 20000) (550037 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3590308096 :
    ThetaLowerSegment 3590308096 3590439168 (71804800310909 / 20000) (179518553921069 / 50000) := by
  exact
    packedTile65536 3590308096 3590439168 14 5957 59919 32 _ _ (2200149 / 100000) (275019 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3590439168 :
    ThetaLowerSegment 3590439168 3590570240 (179518553921069 / 50000)
      (359050165750193 / 100000) := by
  exact
    packedTile65536 3590439168 3590570240 14 5935 59920 32 _ _ (2200153 / 100000) (550039 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3590570240 :
    ThetaLowerSegment 3590570240 3590701312 (359050165750193 / 100000)
      (71812652215741 / 20000) := by
  exact
    packedTile65536 3590570240 3590701312 14 5952 59921 32 _ _ (550039 / 25000) (2200159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3590701312 :
    ThetaLowerSegment 3590701312 3590832384 (71812652215741 / 20000) (71815261605501 / 20000) := by
  exact
    packedTile65536 3590701312 3590832384 14 5930 59922 32 _ _ (13751 / 625) (2200163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3590832384 :
    ThetaLowerSegment 3590832384 3590963456 (71815261605501 / 20000) (44886183400301 / 12500) := by
  exact
    packedTile65536 3590832384 3590963456 14 5981 59923 32 _ _ (2200163 / 100000) (1100083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3590963456 :
    ThetaLowerSegment 3590963456 3591094528 (44886183400301 / 12500) (7182050107841 / 2000) := by
  exact
    packedTile65536 3590963456 3591094528 14 5926 59924 32 _ _ (2200167 / 100000) (220017 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3591094528 :
    ThetaLowerSegment 3591094528 3591225600 (7182050107841 / 2000) (359115440197359 / 100000) := by
  exact
    packedTile65536 3591094528 3591225600 14 5879 59925 32 _ _ (2200171 / 100000) (1100087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3591225600 :
    ThetaLowerSegment 3591225600 3591356672 (359115440197359 / 100000)
      (359128390421523 / 100000) := by
  exact
    packedTile65536 3591225600 3591356672 14 5886 59926 32 _ _ (1100087 / 50000) (2200177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3591356672 :
    ThetaLowerSegment 3591356672 3591487744 (359128390421523 / 100000)
      (359141503482403 / 100000) := by
  exact
    packedTile65536 3591356672 3591487744 14 5960 59927 32 _ _ (1100089 / 50000) (2200181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3591487744 :
    ThetaLowerSegment 3591487744 3591618816 (359141503482403 / 100000)
      (71830892950913 / 20000) := by
  exact
    packedTile65536 3591487744 3591618816 14 5891 59929 32 _ _ (1100091 / 50000) (440037 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3591618816 :
    ThetaLowerSegment 3591618816 3591749888 (71830892950913 / 20000) (14366705402479 / 4000) := by
  exact
    packedTile65536 3591618816 3591749888 14 5986 59930 32 _ _ (440037 / 20000) (550047 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3591749888 :
    ThetaLowerSegment 3591749888 3591880960 (14366705402479 / 4000) (179590328990333 / 50000) := by
  exact
    packedTile65536 3591749888 3591880960 14 5919 59931 32 _ _ (2200189 / 100000) (68756 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3591880960 :
    ThetaLowerSegment 3591880960 3592012032 (179590328990333 / 50000) (71838737944761 / 20000) := by
  exact
    packedTile65536 3591880960 3592012032 14 5923 59932 32 _ _ (2200193 / 100000) (550049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3592012032 :
    ThetaLowerSegment 3592012032 3592143104 (71838737944761 / 20000) (71841347377217 / 20000) := by
  exact
    packedTile65536 3592012032 3592143104 14 5930 59933 32 _ _ (550049 / 25000) (2200199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3592143104 :
    ThetaLowerSegment 3592143104 3592274176 (71841347377217 / 20000) (71844004778777 / 20000) := by
  exact
    packedTile65536 3592143104 3592274176 14 6039 59934 32 _ _ (11001 / 500) (2200203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3592274176 :
    ThetaLowerSegment 3592274176 3592405248 (71844004778777 / 20000)
      (359232967694017 / 100000) := by
  exact
    packedTile65536 3592274176 3592405248 14 5883 59935 32 _ _ (550051 / 25000) (2200207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3592405248 :
    ThetaLowerSegment 3592405248 3592536320 (359232967694017 / 100000)
      (179623026162523 / 50000) := by
  exact
    packedTile65536 3592405248 3592536320 14 5947 59936 32 _ _ (2200207 / 100000) (220021 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3592536320 :
    ThetaLowerSegment 3592536320 3592667392 (179623026162523 / 50000) (44907390747351 / 12500) := by
  exact
    packedTile65536 3592536320 3592667392 14 5942 59937 32 _ _ (2200211 / 100000) (1100107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3592667392 :
    ThetaLowerSegment 3592667392 3592798464 (44907390747351 / 12500)
      (359272223858703 / 100000) := by
  exact
    packedTile65536 3592667392 3592798464 14 5953 59938 32 _ _ (440043 / 20000) (1100109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3592798464 :
    ThetaLowerSegment 3592798464 3592929536 (359272223858703 / 100000)
      (359285154539889 / 100000) := by
  exact
    packedTile65536 3592798464 3592929536 14 5877 59939 32 _ _ (1100109 / 50000) (2200221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3592929536 :
    ThetaLowerSegment 3592929536 3593060608 (359285154539889 / 100000)
      (359298294265673 / 100000) := by
  exact
    packedTile65536 3592929536 3593060608 14 5972 59941 32 _ _ (1100111 / 50000) (88009 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3593060608 :
    ThetaLowerSegment 3593060608 3593191680 (359298294265673 / 100000)
      (359311332804949 / 100000) := by
  exact
    packedTile65536 3593060608 3593191680 14 5926 59942 32 _ _ (1100113 / 50000) (2200229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3593191680 :
    ThetaLowerSegment 3593191680 3593322752 (359311332804949 / 100000)
      (179662263789131 / 50000) := by
  exact
    packedTile65536 3593191680 3593322752 14 5997 59943 32 _ _ (2200229 / 100000) (275029 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3593322752 :
    ThetaLowerSegment 3593322752 3593339136 (179662263789131 / 50000)
      (179663064673943 / 50000) := by
  exact
    packedTile65536 3593322752 3593339136 11 728 59944 32 _ _ (2200233 / 100000) (550059 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3593339136 :
    ThetaLowerSegment 3593339136 3593341184 (179663064673943 / 50000)
      (179663174685593 / 50000) := by
  exact
    packedTile65536 3593339136 3593341184 8 100 59944 32 _ _ (2200233 / 100000) (550059 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3561341184_3593341184 :
    ThetaLowerSegment 3561341184 3593341184 (356127495077781 / 100000)
      (179663174685593 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3561341184 cell3561472256)
                  (ThetaLowerSegment.join cell3561603328 cell3561734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3561865472 cell3561996544)
                  (ThetaLowerSegment.join cell3562127616 cell3562258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3562389760 cell3562520832)
                  (ThetaLowerSegment.join cell3562651904 cell3562782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3562914048 cell3563045120)
                  (ThetaLowerSegment.join cell3563176192 cell3563307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3563438336 cell3563569408)
                  (ThetaLowerSegment.join cell3563700480 cell3563831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3563962624 cell3564093696)
                  (ThetaLowerSegment.join cell3564224768 cell3564355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3564486912 cell3564617984)
                  (ThetaLowerSegment.join cell3564749056 cell3564880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3565011200 cell3565142272)
                  (ThetaLowerSegment.join cell3565273344 cell3565404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3565535488 cell3565666560)
                  (ThetaLowerSegment.join cell3565797632 cell3565928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3566059776 cell3566190848)
                  (ThetaLowerSegment.join cell3566321920 cell3566452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3566584064 cell3566715136)
                  (ThetaLowerSegment.join cell3566846208 cell3566977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3567108352 cell3567239424)
                  (ThetaLowerSegment.join cell3567370496 cell3567501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3567632640 cell3567763712)
                  (ThetaLowerSegment.join cell3567894784 cell3568025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3568156928 cell3568288000)
                  (ThetaLowerSegment.join cell3568419072 cell3568550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3568681216 cell3568812288)
                  (ThetaLowerSegment.join cell3568943360 cell3569074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3569205504 cell3569336576)
                  (ThetaLowerSegment.join cell3569467648 cell3569598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3569729792 cell3569860864)
                  (ThetaLowerSegment.join cell3569991936 cell3570123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3570254080 cell3570385152)
                  (ThetaLowerSegment.join cell3570516224 cell3570647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3570778368 cell3570909440)
                  (ThetaLowerSegment.join cell3571040512 cell3571171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3571302656 cell3571433728)
                  (ThetaLowerSegment.join cell3571564800 cell3571695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3571826944 cell3571958016)
                  (ThetaLowerSegment.join cell3572089088 cell3572220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3572351232 cell3572482304)
                  (ThetaLowerSegment.join cell3572613376 cell3572744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3572875520 cell3573006592)
                  (ThetaLowerSegment.join cell3573137664 cell3573268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3573399808 cell3573530880)
                  (ThetaLowerSegment.join cell3573661952 cell3573793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3573924096 cell3574055168)
                  (ThetaLowerSegment.join cell3574186240 cell3574317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3574448384 cell3574579456)
                  (ThetaLowerSegment.join cell3574710528 cell3574841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3574972672 cell3575103744)
                  (ThetaLowerSegment.join cell3575234816 cell3575365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3575496960 cell3575628032)
                  (ThetaLowerSegment.join cell3575759104 cell3575890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3576021248 cell3576152320)
                  (ThetaLowerSegment.join cell3576283392 cell3576414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3576545536 cell3576676608)
                  (ThetaLowerSegment.join cell3576807680 cell3576938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3577069824 cell3577200896)
                  (ThetaLowerSegment.join cell3577331968 cell3577463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3577594112 cell3577725184)
                  (ThetaLowerSegment.join cell3577856256 cell3577987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3578118400 cell3578249472)
                  (ThetaLowerSegment.join cell3578380544 cell3578511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3578642688 cell3578773760)
                  (ThetaLowerSegment.join cell3578904832 cell3579035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3579166976 cell3579298048)
                  (ThetaLowerSegment.join cell3579429120 cell3579560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3579691264 cell3579822336)
                  (ThetaLowerSegment.join cell3579953408 cell3580084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3580215552 cell3580346624)
                  (ThetaLowerSegment.join cell3580477696 cell3580608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3580739840 cell3580870912)
                  (ThetaLowerSegment.join cell3581001984 cell3581133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3581264128 cell3581395200)
                  (ThetaLowerSegment.join cell3581526272 cell3581657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3581788416 cell3581919488)
                  (ThetaLowerSegment.join cell3582050560 cell3582181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3582312704 cell3582443776)
                  (ThetaLowerSegment.join cell3582574848 cell3582705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3582836992 cell3582968064)
                  (ThetaLowerSegment.join cell3583099136 cell3583230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3583361280 cell3583492352)
                  (ThetaLowerSegment.join cell3583623424 cell3583754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3583885568 cell3584016640)
                  (ThetaLowerSegment.join cell3584147712 cell3584278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3584409856 cell3584540928)
                  (ThetaLowerSegment.join cell3584672000 cell3584803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3584934144 cell3585065216)
                  (ThetaLowerSegment.join cell3585196288 cell3585327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3585458432 cell3585589504)
                  (ThetaLowerSegment.join cell3585720576 cell3585851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3585982720 cell3586113792)
                  (ThetaLowerSegment.join cell3586244864 cell3586375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3586507008 cell3586638080)
                  (ThetaLowerSegment.join cell3586769152 cell3586900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3587031296 cell3587162368)
                  (ThetaLowerSegment.join cell3587293440 cell3587424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3587555584 cell3587686656)
                  (ThetaLowerSegment.join cell3587817728 cell3587948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3588079872 cell3588210944)
                  (ThetaLowerSegment.join cell3588342016 cell3588473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3588604160 cell3588735232)
                  (ThetaLowerSegment.join cell3588866304 cell3588997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3589128448 cell3589259520)
                  (ThetaLowerSegment.join cell3589390592 cell3589521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3589652736 cell3589783808)
                  (ThetaLowerSegment.join cell3589914880 cell3590045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3590177024 cell3590308096)
                  (ThetaLowerSegment.join cell3590439168 cell3590570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3590701312 cell3590832384)
                  (ThetaLowerSegment.join cell3590963456 cell3591094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3591225600 cell3591356672)
                  (ThetaLowerSegment.join cell3591487744 cell3591618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3591749888 cell3591880960)
                  (ThetaLowerSegment.join cell3592012032 cell3592143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3592274176 cell3592405248)
                  (ThetaLowerSegment.join cell3592536320 cell3592667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3592798464 cell3592929536)
                (ThetaLowerSegment.join cell3593060608 cell3593191680))
              (ThetaLowerSegment.join cell3593322752 cell3593339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
