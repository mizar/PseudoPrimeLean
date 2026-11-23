/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3241341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3209341184 :
    ThetaLowerSegment 3209341184 3209472256 (320927380206479 / 100000)
      (320940594788963 / 100000) := by
  exact
    packedTile65536 3209341184 3209472256 14 6037 56651 32 _ _ (547233 / 25000) (437787 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3209472256 :
    ThetaLowerSegment 3209472256 3209603328 (320940594788963 / 100000)
      (320953629902843 / 100000) := by
  exact
    packedTile65536 3209472256 3209603328 14 5955 56652 32 _ _ (273617 / 12500) (2188939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3209603328 :
    ThetaLowerSegment 3209603328 3209734400 (320953629902843 / 100000)
      (320966763542843 / 100000) := by
  exact
    packedTile65536 3209603328 3209734400 14 6000 56653 32 _ _ (109447 / 5000) (2188943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3209734400 :
    ThetaLowerSegment 3209734400 3209865472 (320966763542843 / 100000)
      (320979905962619 / 100000) := by
  exact
    packedTile65536 3209734400 3209865472 14 6004 56654 32 _ _ (136809 / 6250) (2188947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3209865472 :
    ThetaLowerSegment 3209865472 3209996544 (320979905962619 / 100000)
      (320992842645299 / 100000) := by
  exact
    packedTile65536 3209865472 3209996544 14 5910 56655 32 _ _ (547237 / 25000) (2188951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3209996544 :
    ThetaLowerSegment 3209996544 3210127616 (320992842645299 / 100000)
      (321006022325291 / 100000) := by
  exact
    packedTile65536 3209996544 3210127616 14 6021 56656 32 _ _ (273619 / 12500) (437791 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3210127616 :
    ThetaLowerSegment 3210127616 3210258688 (321006022325291 / 100000)
      (321019116660083 / 100000) := by
  exact
    packedTile65536 3210127616 3210258688 14 5982 56657 32 _ _ (547239 / 25000) (2188959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3210258688 :
    ThetaLowerSegment 3210258688 3210389760 (321019116660083 / 100000)
      (321032167239603 / 100000) := by
  exact
    packedTile65536 3210258688 3210389760 14 5962 56659 32 _ _ (13681 / 625) (2188963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3210389760 :
    ThetaLowerSegment 3210389760 3210520832 (321032167239603 / 100000)
      (321045185008511 / 100000) := by
  exact
    packedTile65536 3210389760 3210520832 14 5947 56660 32 _ _ (547241 / 25000) (2188967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3210520832 :
    ThetaLowerSegment 3210520832 3210651904 (321045185008511 / 100000)
      (64211658509779 / 20000) := by
  exact
    packedTile65536 3210520832 3210651904 14 5988 56661 32 _ _ (273621 / 12500) (2188971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3210651904 :
    ThetaLowerSegment 3210651904 3210782976 (64211658509779 / 20000)
      (321071389168371 / 100000) := by
  exact
    packedTile65536 3210651904 3210782976 14 5983 56662 32 _ _ (547243 / 25000) (87559 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3210782976 :
    ThetaLowerSegment 3210782976 3210914048 (321071389168371 / 100000) (12843381096333 / 4000) := by
  exact
    packedTile65536 3210782976 3210914048 14 6002 56663 32 _ _ (2188977 / 100000) (109449 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3210914048 :
    ThetaLowerSegment 3210914048 3211045120 (12843381096333 / 4000) (20068597127141 / 6250) := by
  exact
    packedTile65536 3210914048 3211045120 14 5951 56664 32 _ _ (2188981 / 100000) (273623 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3211045120 :
    ThetaLowerSegment 3211045120 3211176192 (20068597127141 / 6250) (321110668243391 / 100000) := by
  exact
    packedTile65536 3211045120 3211176192 14 5991 56666 32 _ _ (437797 / 20000) (547247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3211176192 :
    ThetaLowerSegment 3211176192 3211307264 (321110668243391 / 100000)
      (64224767440243 / 20000) := by
  exact
    packedTile65536 3211176192 3211307264 14 6016 56667 32 _ _ (2188989 / 100000) (68406 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3211307264 :
    ThetaLowerSegment 3211307264 3211438336 (64224767440243 / 20000)
      (321136958025257 / 100000) := by
  exact
    packedTile65536 3211307264 3211438336 14 5994 56668 32 _ _ (2188993 / 100000) (547249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3211438336 :
    ThetaLowerSegment 3211438336 3211569408 (321136958025257 / 100000)
      (40143753565793 / 12500) := by
  exact
    packedTile65536 3211438336 3211569408 14 5971 56669 32 _ _ (2188997 / 100000) (2189 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3211569408 :
    ThetaLowerSegment 3211569408 3211700480 (40143753565793 / 12500)
      (321162985223263 / 100000) := by
  exact
    packedTile65536 3211569408 3211700480 14 5919 56670 32 _ _ (2189001 / 100000) (547251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3211700480 :
    ThetaLowerSegment 3211700480 3211831552 (321162985223263 / 100000)
      (321176206813463 / 100000) := by
  exact
    packedTile65536 3211700480 3211831552 14 6040 56671 32 _ _ (437801 / 20000) (136813 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3211831552 :
    ThetaLowerSegment 3211831552 3211962624 (321176206813463 / 100000)
      (321189345245481 / 100000) := by
  exact
    packedTile65536 3211831552 3211962624 14 6002 56673 32 _ _ (2189009 / 100000) (547253 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3211962624 :
    ThetaLowerSegment 3211962624 3212093696 (321189345245481 / 100000)
      (32120242022013 / 10000) := by
  exact
    packedTile65536 3211962624 3212093696 14 5973 56674 32 _ _ (2189013 / 100000) (273627 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3212093696 :
    ThetaLowerSegment 3212093696 3212224768 (32120242022013 / 10000) (80303885297007 / 25000) := by
  exact
    packedTile65536 3212093696 3212224768 14 5994 56675 32 _ _ (2189017 / 100000) (109451 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3212224768 :
    ThetaLowerSegment 3212224768 3212355840 (80303885297007 / 25000) (20076786187319 / 6250) := by
  exact
    packedTile65536 3212224768 3212355840 14 5956 56676 32 _ _ (2189021 / 100000) (68407 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3212355840 :
    ThetaLowerSegment 3212355840 3212486912 (20076786187319 / 6250) (80310466596231 / 25000) := by
  exact
    packedTile65536 3212355840 3212486912 14 6070 56677 32 _ _ (1094513 / 50000) (2189029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3212486912 :
    ThetaLowerSegment 3212486912 3212617984 (80310466596231 / 25000) (160627496998917 / 50000) := by
  exact
    packedTile65536 3212486912 3212617984 14 5997 56678 32 _ _ (218903 / 10000) (2189033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3212617984 :
    ThetaLowerSegment 3212617984 3212749056 (160627496998917 / 50000) (40158508089981 / 12500) := by
  exact
    packedTile65536 3212617984 3212749056 14 5971 56679 32 _ _ (1094517 / 50000) (2189037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3212749056 :
    ThetaLowerSegment 3212749056 3212880128 (40158508089981 / 12500) (6425625248599 / 2000) := by
  exact
    packedTile65536 3212749056 3212880128 14 6029 56681 32 _ _ (1094519 / 50000) (2189041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3212880128 :
    ThetaLowerSegment 3212880128 3213011200 (6425625248599 / 2000) (160647174261513 / 50000) := by
  exact
    packedTile65536 3212880128 3213011200 14 5978 56682 32 _ _ (1094521 / 50000) (437809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3213011200 :
    ThetaLowerSegment 3213011200 3213142272 (160647174261513 / 50000) (20081704130217 / 6250) := by
  exact
    packedTile65536 3213011200 3213142272 14 5901 56683 32 _ _ (1094523 / 50000) (2189049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3213142272 :
    ThetaLowerSegment 3213142272 3213273344 (20081704130217 / 6250) (160660129047611 / 50000) := by
  exact
    packedTile65536 3213142272 3213273344 14 5935 56684 32 _ _ (43781 / 2000) (2189053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3213273344 :
    ThetaLowerSegment 3213273344 3213404416 (160660129047611 / 50000) (40166658455393 / 12500) := by
  exact
    packedTile65536 3213273344 3213404416 14 5943 56685 32 _ _ (1094527 / 50000) (2189057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3213404416 :
    ThetaLowerSegment 3213404416 3213535488 (40166658455393 / 12500) (80336592836083 / 25000) := by
  exact
    packedTile65536 3213404416 3213535488 14 5986 56686 32 _ _ (1094529 / 50000) (2189061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3213535488 :
    ThetaLowerSegment 3213535488 3213666560 (80336592836083 / 25000) (10042483322288 / 3125) := by
  exact
    packedTile65536 3213535488 3213666560 14 5982 56688 32 _ _ (1094531 / 50000) (437813 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3213666560 :
    ThetaLowerSegment 3213666560 3213797632 (10042483322288 / 3125) (160686340852329 / 50000) := by
  exact
    packedTile65536 3213666560 3213797632 14 6037 56689 32 _ _ (1094533 / 50000) (2189069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3213797632 :
    ThetaLowerSegment 3213797632 3213928704 (160686340852329 / 50000) (40173228383751 / 12500) := by
  exact
    packedTile65536 3213797632 3213928704 14 6005 56690 32 _ _ (218907 / 10000) (2189073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3213928704 :
    ThetaLowerSegment 3213928704 3214059776 (40173228383751 / 12500) (160699433691913 / 50000) := by
  exact
    packedTile65536 3213928704 3214059776 14 5957 56691 32 _ _ (1094537 / 50000) (2189077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3214059776 :
    ThetaLowerSegment 3214059776 3214190848 (160699433691913 / 50000) (80353016882549 / 25000) := by
  exact
    packedTile65536 3214059776 3214190848 14 6030 56692 32 _ _ (2189079 / 100000) (1094541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3214190848 :
    ThetaLowerSegment 3214190848 3214321920 (80353016882549 / 25000)
      (321424954661817 / 100000) := by
  exact
    packedTile65536 3214190848 3214321920 14 5887 56693 32 _ _ (2189083 / 100000) (1094543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3214321920 :
    ThetaLowerSegment 3214321920 3214452992 (321424954661817 / 100000)
      (160719078522757 / 50000) := by
  exact
    packedTile65536 3214321920 3214452992 14 6031 56694 32 _ _ (2189087 / 100000) (218909 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3214452992 :
    ThetaLowerSegment 3214452992 3214584064 (160719078522757 / 50000)
      (160725733359397 / 50000) := by
  exact
    packedTile65536 3214452992 3214584064 14 6080 56696 32 _ _ (2189091 / 100000) (1094547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3214584064 :
    ThetaLowerSegment 3214584064 3214715136 (160725733359397 / 50000)
      (321464682285309 / 100000) := by
  exact
    packedTile65536 3214584064 3214715136 14 6037 56697 32 _ _ (437819 / 20000) (1094549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3214715136 :
    ThetaLowerSegment 3214715136 3214846208 (321464682285309 / 100000)
      (160738806646551 / 50000) := by
  exact
    packedTile65536 3214715136 3214846208 14 5907 56698 32 _ _ (2189099 / 100000) (1094551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3214846208 :
    ThetaLowerSegment 3214846208 3214977280 (160738806646551 / 50000)
      (160745317038873 / 50000) := by
  exact
    packedTile65536 3214846208 3214977280 14 5948 56699 32 _ _ (2189103 / 100000) (1094553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3214977280 :
    ThetaLowerSegment 3214977280 3215108352 (160745317038873 / 50000)
      (321503797178137 / 100000) := by
  exact
    packedTile65536 3214977280 3215108352 14 6013 56700 32 _ _ (2189107 / 100000) (218911 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3215108352 :
    ThetaLowerSegment 3215108352 3215239424 (321503797178137 / 100000)
      (160758438558181 / 50000) := by
  exact
    packedTile65536 3215108352 3215239424 14 5975 56701 32 _ _ (2189111 / 100000) (1094557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3215239424 :
    ThetaLowerSegment 3215239424 3215370496 (160758438558181 / 50000)
      (321529825731587 / 100000) := by
  exact
    packedTile65536 3215239424 3215370496 14 5915 56703 32 _ _ (437823 / 20000) (1094559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3215370496 :
    ThetaLowerSegment 3215370496 3215501568 (321529825731587 / 100000)
      (160771428778497 / 50000) := by
  exact
    packedTile65536 3215370496 3215501568 14 5953 56704 32 _ _ (2189119 / 100000) (1094561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3215501568 :
    ThetaLowerSegment 3215501568 3215632640 (160771428778497 / 50000)
      (321556055779561 / 100000) := by
  exact
    packedTile65536 3215501568 3215632640 14 6029 56705 32 _ _ (2189123 / 100000) (1094563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3215632640 :
    ThetaLowerSegment 3215632640 3215763712 (321556055779561 / 100000)
      (160784620445741 / 50000) := by
  exact
    packedTile65536 3215632640 3215763712 14 6023 56706 32 _ _ (2189127 / 100000) (218913 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3215763712 :
    ThetaLowerSegment 3215763712 3215894784 (160784620445741 / 50000)
      (160791172517817 / 50000) := by
  exact
    packedTile65536 3215763712 3215894784 14 5986 56707 32 _ _ (547283 / 25000) (437827 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3215894784 :
    ThetaLowerSegment 3215894784 3216025856 (160791172517817 / 50000)
      (160797646887537 / 50000) := by
  exact
    packedTile65536 3215894784 3216025856 14 5915 56708 32 _ _ (136821 / 6250) (2189139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3216025856 :
    ThetaLowerSegment 3216025856 3216156928 (160797646887537 / 50000)
      (160804265752327 / 50000) := by
  exact
    packedTile65536 3216025856 3216156928 14 6047 56710 32 _ _ (109457 / 5000) (2189143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3216156928 :
    ThetaLowerSegment 3216156928 3216288000 (160804265752327 / 50000) (257297261291 / 80) := by
  exact
    packedTile65536 3216156928 3216288000 14 5959 56711 32 _ _ (273643 / 12500) (2189147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3216288000 :
    ThetaLowerSegment 3216288000 3216419072 (257297261291 / 80) (160817285698139 / 50000) := by
  exact
    packedTile65536 3216288000 3216419072 14 5936 56712 32 _ _ (547287 / 25000) (2189151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3216419072 :
    ThetaLowerSegment 3216419072 3216550144 (160817285698139 / 50000)
      (160823838924651 / 50000) := by
  exact
    packedTile65536 3216419072 3216550144 14 5987 56713 32 _ _ (68411 / 3125) (437831 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3216550144 :
    ThetaLowerSegment 3216550144 3216681216 (160823838924651 / 50000)
      (160830331961347 / 50000) := by
  exact
    packedTile65536 3216550144 3216681216 14 5932 56714 32 _ _ (547289 / 25000) (2189159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3216681216 :
    ThetaLowerSegment 3216681216 3216812288 (160830331961347 / 50000)
      (160836977156527 / 50000) := by
  exact
    packedTile65536 3216681216 3216812288 14 6071 56715 32 _ _ (54729 / 2500) (2189163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3216812288 :
    ThetaLowerSegment 3216812288 3216943360 (160836977156527 / 50000)
      (160843617985521 / 50000) := by
  exact
    packedTile65536 3216812288 3216943360 14 6067 56716 32 _ _ (547291 / 25000) (2189167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3216943360 :
    ThetaLowerSegment 3216943360 3217074432 (160843617985521 / 50000) (32170050451829 / 10000) := by
  exact
    packedTile65536 3216943360 3217074432 14 6061 56718 32 _ _ (136823 / 6250) (2189171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3217074432 :
    ThetaLowerSegment 3217074432 3217205504 (32170050451829 / 10000) (160856767235017 / 50000) := by
  exact
    packedTile65536 3217074432 3217205504 14 5952 56719 32 _ _ (547293 / 25000) (87567 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3217205504 :
    ThetaLowerSegment 3217205504 3217336576 (160856767235017 / 50000)
      (160863355560189 / 50000) := by
  exact
    packedTile65536 3217205504 3217336576 14 6019 56720 32 _ _ (273647 / 12500) (2189179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3217336576 :
    ThetaLowerSegment 3217336576 3217467648 (160863355560189 / 50000)
      (160869858519379 / 50000) := by
  exact
    packedTile65536 3217336576 3217467648 14 5941 56721 32 _ _ (109459 / 5000) (2189183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3217467648 :
    ThetaLowerSegment 3217467648 3217598720 (160869858519379 / 50000)
      (321752937526973 / 100000) := by
  exact
    packedTile65536 3217467648 3217598720 14 6039 56722 32 _ _ (437837 / 20000) (547297 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3217598720 :
    ThetaLowerSegment 3217598720 3217729792 (321752937526973 / 100000)
      (160883089965617 / 50000) := by
  exact
    packedTile65536 3217598720 3217729792 14 6049 56723 32 _ _ (2189189 / 100000) (273649 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3217729792 :
    ThetaLowerSegment 3217729792 3217860864 (160883089965617 / 50000)
      (321779190305233 / 100000) := by
  exact
    packedTile65536 3217729792 3217860864 14 5943 56725 32 _ _ (2189193 / 100000) (547299 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3217860864 :
    ThetaLowerSegment 3217860864 3217991936 (321779190305233 / 100000)
      (321792036513229 / 100000) := by
  exact
    packedTile65536 3217860864 3217991936 14 5868 56726 32 _ _ (2189197 / 100000) (5473 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3217991936 :
    ThetaLowerSegment 3217991936 3218123008 (321792036513229 / 100000)
      (321804917771913 / 100000) := by
  exact
    packedTile65536 3217991936 3218123008 14 5884 56727 32 _ _ (2189201 / 100000) (547301 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3218123008 :
    ThetaLowerSegment 3218123008 3218254080 (321804917771913 / 100000)
      (321818092407603 / 100000) := by
  exact
    packedTile65536 3218123008 3218254080 14 6018 56728 32 _ _ (437841 / 20000) (273651 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3218254080 :
    ThetaLowerSegment 3218254080 3218385152 (321818092407603 / 100000)
      (40228933285673 / 12500) := by
  exact
    packedTile65536 3218254080 3218385152 14 6109 56729 32 _ _ (2189209 / 100000) (547303 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3218385152 :
    ThetaLowerSegment 3218385152 3218516224 (40228933285673 / 12500) (32184464972607 / 10000) := by
  exact
    packedTile65536 3218385152 3218516224 14 6022 56730 32 _ _ (2189213 / 100000) (68413 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3218516224 :
    ThetaLowerSegment 3218516224 3218647296 (32184464972607 / 10000)
      (321857695270173 / 100000) := by
  exact
    packedTile65536 3218516224 3218647296 14 5959 56731 32 _ _ (2189217 / 100000) (109461 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3218647296 :
    ThetaLowerSegment 3218647296 3218778368 (321857695270173 / 100000)
      (64374175751807 / 20000) := by
  exact
    packedTile65536 3218647296 3218778368 14 6022 56733 32 _ _ (2189221 / 100000) (273653 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3218778368 :
    ThetaLowerSegment 3218778368 3218909440 (64374175751807 / 20000) (2011774828211 / 625) := by
  exact
    packedTile65536 3218778368 3218909440 14 5981 56734 32 _ _ (87569 / 4000) (547307 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3218909440 :
    ThetaLowerSegment 3218909440 3219040512 (2011774828211 / 625) (321897070670867 / 100000) := by
  exact
    packedTile65536 3218909440 3219040512 14 5983 56735 32 _ _ (2189229 / 100000) (136827 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3219040512 :
    ThetaLowerSegment 3219040512 3219171584 (321897070670867 / 100000)
      (321910192933469 / 100000) := by
  exact
    packedTile65536 3219040512 3219171584 14 5994 56736 32 _ _ (2189233 / 100000) (547309 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3219171584 :
    ThetaLowerSegment 3219171584 3219302656 (321910192933469 / 100000)
      (321923354626313 / 100000) := by
  exact
    packedTile65536 3219171584 3219302656 14 6012 56737 32 _ _ (2189237 / 100000) (54731 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3219302656 :
    ThetaLowerSegment 3219302656 3219433728 (321923354626313 / 100000)
      (321936303992743 / 100000) := by
  exact
    packedTile65536 3219302656 3219433728 14 5915 56738 32 _ _ (1094621 / 50000) (437849 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3219433728 :
    ThetaLowerSegment 3219433728 3219564800 (321936303992743 / 100000)
      (321949266518309 / 100000) := by
  exact
    packedTile65536 3219433728 3219564800 14 5921 56740 32 _ _ (1094623 / 50000) (2189249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3219564800 :
    ThetaLowerSegment 3219564800 3219695872 (321949266518309 / 100000)
      (321962191850309 / 100000) := by
  exact
    packedTile65536 3219564800 3219695872 14 5904 56741 32 _ _ (8757 / 400) (2189253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3219695872 :
    ThetaLowerSegment 3219695872 3219826944 (321962191850309 / 100000)
      (321975009932479 / 100000) := by
  exact
    packedTile65536 3219695872 3219826944 14 5855 56742 32 _ _ (1094627 / 50000) (2189257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3219826944 :
    ThetaLowerSegment 3219826944 3219958016 (321975009932479 / 100000)
      (321987987853903 / 100000) := by
  exact
    packedTile65536 3219826944 3219958016 14 5928 56743 32 _ _ (1094629 / 50000) (2189261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3219958016 :
    ThetaLowerSegment 3219958016 3220089088 (321987987853903 / 100000)
      (322001175968191 / 100000) := by
  exact
    packedTile65536 3219958016 3220089088 14 6024 56744 32 _ _ (1094631 / 50000) (437853 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3220089088 :
    ThetaLowerSegment 3220089088 3220220160 (322001175968191 / 100000)
      (322014272157403 / 100000) := by
  exact
    packedTile65536 3220089088 3220220160 14 5982 56745 32 _ _ (1094633 / 50000) (2189269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3220220160 :
    ThetaLowerSegment 3220220160 3220351232 (322014272157403 / 100000)
      (322027208553833 / 100000) := by
  exact
    packedTile65536 3220220160 3220351232 14 5909 56746 32 _ _ (218927 / 10000) (2189273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3220351232 :
    ThetaLowerSegment 3220351232 3220482304 (322027208553833 / 100000)
      (322040177813009 / 100000) := by
  exact
    packedTile65536 3220351232 3220482304 14 5924 56748 32 _ _ (1094637 / 50000) (2189277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3220482304 :
    ThetaLowerSegment 3220482304 3220613376 (322040177813009 / 100000)
      (322053276263283 / 100000) := by
  exact
    packedTile65536 3220482304 3220613376 14 5983 56749 32 _ _ (1094639 / 50000) (2189281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3220613376 :
    ThetaLowerSegment 3220613376 3220744448 (322053276263283 / 100000)
      (64413322235989 / 20000) := by
  exact
    packedTile65536 3220613376 3220744448 14 6091 56750 32 _ _ (1094641 / 50000) (437857 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3220744448 :
    ThetaLowerSegment 3220744448 3220875520 (64413322235989 / 20000) (12883185935123 / 4000) := by
  exact
    packedTile65536 3220744448 3220875520 14 5955 56751 32 _ _ (1094643 / 50000) (2189289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3220875520 :
    ThetaLowerSegment 3220875520 3221006592 (12883185935123 / 4000) (64418555947899 / 20000) := by
  exact
    packedTile65536 3220875520 3221006592 14 5998 56752 32 _ _ (218929 / 10000) (2189293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3221006592 :
    ThetaLowerSegment 3221006592 3221137664 (64418555947899 / 20000) (64421198425757 / 20000) := by
  exact
    packedTile65536 3221006592 3221137664 14 6035 56753 32 _ _ (1094647 / 50000) (2189297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3221137664 :
    ThetaLowerSegment 3221137664 3221268736 (64421198425757 / 20000) (40264916440949 / 12500) := by
  exact
    packedTile65536 3221137664 3221268736 14 6093 56755 32 _ _ (2189299 / 100000) (1094651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3221268736 :
    ThetaLowerSegment 3221268736 3221399808 (40264916440949 / 12500) (80533105889883 / 25000) := by
  exact
    packedTile65536 3221268736 3221399808 14 5980 56756 32 _ _ (2189303 / 100000) (1094653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3221399808 :
    ThetaLowerSegment 3221399808 3221530880 (80533105889883 / 25000)
      (322145355795981 / 100000) := by
  exact
    packedTile65536 3221399808 3221530880 14 5907 56757 32 _ _ (2189307 / 100000) (218931 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3221530880 :
    ThetaLowerSegment 3221530880 3221661952 (322145355795981 / 100000)
      (161079284143933 / 50000) := by
  exact
    packedTile65536 3221530880 3221661952 14 6035 56758 32 _ _ (2189311 / 100000) (1094657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3221661952 :
    ThetaLowerSegment 3221661952 3221793024 (161079284143933 / 50000)
      (322171671338141 / 100000) := by
  exact
    packedTile65536 3221661952 3221793024 14 5985 56759 32 _ _ (437863 / 20000) (1094659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3221793024 :
    ThetaLowerSegment 3221793024 3221924096 (322171671338141 / 100000) (20136551137421 / 6250) := by
  exact
    packedTile65536 3221793024 3221924096 14 6005 56760 32 _ _ (2189319 / 100000) (1094661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3221924096 :
    ThetaLowerSegment 3221924096 3222055168 (20136551137421 / 6250) (80549464451631 / 25000) := by
  exact
    packedTile65536 3221924096 3222055168 14 5956 56761 32 _ _ (2189323 / 100000) (1094663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3222055168 :
    ThetaLowerSegment 3222055168 3222186240 (80549464451631 / 25000)
      (322211048501699 / 100000) := by
  exact
    packedTile65536 3222055168 3222186240 14 6025 56763 32 _ _ (2189327 / 100000) (218933 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3222186240 :
    ThetaLowerSegment 3222186240 3222317312 (322211048501699 / 100000) (10069501318162 / 3125) := by
  exact
    packedTile65536 3222186240 3222317312 14 5935 56764 32 _ _ (2189331 / 100000) (1094667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3222317312 :
    ThetaLowerSegment 3222317312 3222448384 (10069501318162 / 3125) (322237070913769 / 100000) := by
  exact
    packedTile65536 3222317312 3222448384 14 5951 56765 32 _ _ (437867 / 20000) (1094669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3222448384 :
    ThetaLowerSegment 3222448384 3222579456 (322237070913769 / 100000)
      (322250044936683 / 100000) := by
  exact
    packedTile65536 3222448384 3222579456 14 5926 56766 32 _ _ (2189339 / 100000) (1094671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3222579456 :
    ThetaLowerSegment 3222579456 3222710528 (322250044936683 / 100000)
      (161131530290409 / 50000) := by
  exact
    packedTile65536 3222579456 3222710528 14 5945 56767 32 _ _ (2189343 / 100000) (1094673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3222710528 :
    ThetaLowerSegment 3222710528 3222841600 (161131530290409 / 50000) (32227627547931 / 10000) := by
  exact
    packedTile65536 3222710528 3222841600 14 6036 56768 32 _ _ (2189347 / 100000) (43787 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3222841600 :
    ThetaLowerSegment 3222841600 3222972672 (32227627547931 / 10000) (161144762715781 / 50000) := by
  exact
    packedTile65536 3222841600 3222972672 14 6052 56770 32 _ _ (2189351 / 100000) (1094677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3222972672 :
    ThetaLowerSegment 3222972672 3223103744 (161144762715781 / 50000)
      (322302685644467 / 100000) := by
  exact
    packedTile65536 3222972672 3223103744 14 6011 56771 32 _ _ (437871 / 20000) (1094679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3223103744 :
    ThetaLowerSegment 3223103744 3223234816 (322302685644467 / 100000)
      (322315874349107 / 100000) := by
  exact
    packedTile65536 3223103744 3223234816 14 6024 56772 32 _ _ (27367 / 1250) (2189363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3223234816 :
    ThetaLowerSegment 3223234816 3223365888 (322315874349107 / 100000)
      (322328973313919 / 100000) := by
  exact
    packedTile65536 3223234816 3223365888 14 5983 56773 32 _ _ (547341 / 25000) (2189367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3223365888 :
    ThetaLowerSegment 3223365888 3223496960 (322328973313919 / 100000)
      (322342107332551 / 100000) := by
  exact
    packedTile65536 3223365888 3223496960 14 5999 56774 32 _ _ (273671 / 12500) (2189371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3223496960 :
    ThetaLowerSegment 3223496960 3223628032 (322342107332551 / 100000)
      (322355114391603 / 100000) := by
  exact
    packedTile65536 3223496960 3223628032 14 5941 56775 32 _ _ (547343 / 25000) (3503 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3223628032 :
    ThetaLowerSegment 3223628032 3223759104 (322355114391603 / 100000)
      (64473646626519 / 20000) := by
  exact
    packedTile65536 3223628032 3223759104 14 5992 56777 32 _ _ (68418 / 3125) (2189379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3223759104 :
    ThetaLowerSegment 3223759104 3223890176 (64473646626519 / 20000) (64476281764287 / 20000) := by
  exact
    packedTile65536 3223759104 3223890176 14 6018 56778 32 _ _ (109469 / 5000) (2189383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3223890176 :
    ThetaLowerSegment 3223890176 3224021248 (64476281764287 / 20000)
      (322394628322027 / 100000) := by
  exact
    packedTile65536 3223890176 3224021248 14 6038 56779 32 _ _ (273673 / 12500) (2189387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3224021248 :
    ThetaLowerSegment 3224021248 3224152320 (322394628322027 / 100000)
      (322407878498203 / 100000) := by
  exact
    packedTile65536 3224021248 3224152320 14 6052 56780 32 _ _ (547347 / 25000) (2189391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3224152320 :
    ThetaLowerSegment 3224152320 3224283392 (322407878498203 / 100000)
      (322421065206219 / 100000) := by
  exact
    packedTile65536 3224152320 3224283392 14 6023 56781 32 _ _ (136837 / 6250) (437879 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3224283392 :
    ThetaLowerSegment 3224283392 3224414464 (322421065206219 / 100000)
      (322433993589599 / 100000) := by
  exact
    packedTile65536 3224283392 3224414464 14 5905 56782 32 _ _ (547349 / 25000) (2189399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3224414464 :
    ThetaLowerSegment 3224414464 3224545536 (322433993589599 / 100000)
      (322447070875799 / 100000) := by
  exact
    packedTile65536 3224414464 3224545536 14 5973 56783 32 _ _ (10947 / 500) (2189403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3224545536 :
    ThetaLowerSegment 3224545536 3224676608 (322447070875799 / 100000)
      (322460148185891 / 100000) := by
  exact
    packedTile65536 3224545536 3224676608 14 5973 56785 32 _ _ (547351 / 25000) (2189407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3224676608 :
    ThetaLowerSegment 3224676608 3224807680 (322460148185891 / 100000)
      (322473321853827 / 100000) := by
  exact
    packedTile65536 3224676608 3224807680 14 6017 56786 32 _ _ (68419 / 3125) (2189411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3224807680 :
    ThetaLowerSegment 3224807680 3224938752 (322473321853827 / 100000)
      (322486272225807 / 100000) := by
  exact
    packedTile65536 3224807680 3224938752 14 5915 56787 32 _ _ (547353 / 25000) (437883 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3224938752 :
    ThetaLowerSegment 3224938752 3225069824 (322486272225807 / 100000)
      (322499264220351 / 100000) := by
  exact
    packedTile65536 3224938752 3225069824 14 5934 56788 32 _ _ (273677 / 12500) (2189419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3225069824 :
    ThetaLowerSegment 3225069824 3225200896 (322499264220351 / 100000)
      (32251231098009 / 10000) := by
  exact
    packedTile65536 3225069824 3225200896 14 5959 56789 32 _ _ (2189421 / 100000) (136839 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3225200896 :
    ThetaLowerSegment 3225200896 3225331968 (32251231098009 / 10000) (16126270843907 / 5000) := by
  exact
    packedTile65536 3225200896 3225331968 14 5986 56790 32 _ _ (87577 / 4000) (547357 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3225331968 :
    ThetaLowerSegment 3225331968 3225463040 (16126270843907 / 5000) (161269230748061 / 50000) := by
  exact
    packedTile65536 3225331968 3225463040 14 5958 56792 32 _ _ (2189429 / 100000) (273679 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3225463040 :
    ThetaLowerSegment 3225463040 3225594112 (161269230748061 / 50000)
      (161275781531597 / 50000) := by
  exact
    packedTile65536 3225463040 3225594112 14 5984 56793 32 _ _ (2189433 / 100000) (547359 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3225594112 :
    ThetaLowerSegment 3225594112 3225725184 (161275781531597 / 50000)
      (161282371736967 / 50000) := by
  exact
    packedTile65536 3225594112 3225725184 14 6020 56794 32 _ _ (2189437 / 100000) (13684 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3225725184 :
    ThetaLowerSegment 3225725184 3225856256 (161282371736967 / 50000)
      (322577777216207 / 100000) := by
  exact
    packedTile65536 3225725184 3225856256 14 5953 56795 32 _ _ (2189441 / 100000) (547361 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3225856256 :
    ThetaLowerSegment 3225856256 3225987328 (322577777216207 / 100000)
      (322590935780657 / 100000) := by
  exact
    packedTile65536 3225856256 3225987328 14 6010 56796 32 _ _ (437889 / 20000) (273681 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3225987328 :
    ThetaLowerSegment 3225987328 3226118400 (322590935780657 / 100000)
      (80651046034139 / 25000) := by
  exact
    packedTile65536 3225987328 3226118400 14 6051 56797 32 _ _ (2189449 / 100000) (547363 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3226118400 :
    ThetaLowerSegment 3226118400 3226249472 (80651046034139 / 25000)
      (322617279254949 / 100000) := by
  exact
    packedTile65536 3226118400 3226249472 14 5981 56798 32 _ _ (2189453 / 100000) (136841 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3226249472 :
    ThetaLowerSegment 3226249472 3226380544 (322617279254949 / 100000)
      (32263044445989 / 10000) := by
  exact
    packedTile65536 3226249472 3226380544 14 6013 56800 32 _ _ (2189457 / 100000) (109473 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3226380544 :
    ThetaLowerSegment 3226380544 3226511616 (32263044445989 / 10000) (161321751202647 / 50000) := by
  exact
    packedTile65536 3226380544 3226511616 14 5964 56801 32 _ _ (2189461 / 100000) (273683 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3226511616 :
    ThetaLowerSegment 3226511616 3226642688 (161321751202647 / 50000) (10083023395892 / 3125) := by
  exact
    packedTile65536 3226511616 3226642688 14 6050 56802 32 _ _ (437893 / 20000) (547367 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3226642688 :
    ThetaLowerSegment 3226642688 3226773760 (10083023395892 / 3125) (322669900808827 / 100000) := by
  exact
    packedTile65536 3226642688 3226773760 14 6007 56803 32 _ _ (2189469 / 100000) (68421 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3226773760 :
    ThetaLowerSegment 3226773760 3226904832 (322669900808827 / 100000)
      (161341430149757 / 50000) := by
  exact
    packedTile65536 3226773760 3226904832 14 5919 56804 32 _ _ (2189473 / 100000) (547369 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3226904832 :
    ThetaLowerSegment 3226904832 3227035904 (161341430149757 / 50000)
      (322695832950739 / 100000) := by
  exact
    packedTile65536 3226904832 3227035904 14 5925 56805 32 _ _ (2189477 / 100000) (54737 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3227035904 :
    ThetaLowerSegment 3227035904 3227166976 (322695832950739 / 100000)
      (64541783457839 / 20000) := by
  exact
    packedTile65536 3227035904 3227166976 14 5976 56807 32 _ _ (2189481 / 100000) (547371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3227166976 :
    ThetaLowerSegment 3227166976 3227298048 (64541783457839 / 20000)
      (322722003847017 / 100000) := by
  exact
    packedTile65536 3227166976 3227298048 14 5977 56808 32 _ _ (1094743 / 50000) (2189489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3227298048 :
    ThetaLowerSegment 3227298048 3227429120 (322722003847017 / 100000)
      (322735116702627 / 100000) := by
  exact
    packedTile65536 3227298048 3227429120 14 5989 56809 32 _ _ (218949 / 10000) (2189493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3227429120 :
    ThetaLowerSegment 3227429120 3227560192 (322735116702627 / 100000)
      (64549610008737 / 20000) := by
  exact
    packedTile65536 3227429120 3227560192 14 5907 56810 32 _ _ (1094747 / 50000) (2189497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3227560192 :
    ThetaLowerSegment 3227560192 3227691264 (64549610008737 / 20000) (64552233027341 / 20000) := by
  exact
    packedTile65536 3227560192 3227691264 14 5990 56811 32 _ _ (1094749 / 50000) (2189501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3227691264 :
    ThetaLowerSegment 3227691264 3227822336 (64552233027341 / 20000)
      (322774234274143 / 100000) := by
  exact
    packedTile65536 3227691264 3227822336 14 5969 56812 32 _ _ (1094751 / 50000) (437901 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3227822336 :
    ThetaLowerSegment 3227822336 3227953408 (322774234274143 / 100000)
      (322787504870009 / 100000) := by
  exact
    packedTile65536 3227822336 3227953408 14 6061 56813 32 _ _ (1094753 / 50000) (2189509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3227953408 :
    ThetaLowerSegment 3227953408 3228084480 (322787504870009 / 100000)
      (322800447063619 / 100000) := by
  exact
    packedTile65536 3227953408 3228084480 14 5911 56815 32 _ _ (218951 / 10000) (2189513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3228084480 :
    ThetaLowerSegment 3228084480 3228215552 (322800447063619 / 100000)
      (322813597284703 / 100000) := by
  exact
    packedTile65536 3228084480 3228215552 14 6006 56816 32 _ _ (1094757 / 50000) (2189517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3228215552 :
    ThetaLowerSegment 3228215552 3228346624 (322813597284703 / 100000)
      (322826651191019 / 100000) := by
  exact
    packedTile65536 3228215552 3228346624 14 5962 56817 32 _ _ (1094759 / 50000) (2189521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3228346624 :
    ThetaLowerSegment 3228346624 3228477696 (322826651191019 / 100000)
      (322839821165849 / 100000) := by
  exact
    packedTile65536 3228346624 3228477696 14 6015 56818 32 _ _ (1094761 / 50000) (87581 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3228477696 :
    ThetaLowerSegment 3228477696 3228608768 (322839821165849 / 100000)
      (322853118157247 / 100000) := by
  exact
    packedTile65536 3228477696 3228608768 14 6073 56819 32 _ _ (1094763 / 50000) (2189529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3228608768 :
    ThetaLowerSegment 3228608768 3228739840 (322853118157247 / 100000)
      (322866279422077 / 100000) := by
  exact
    packedTile65536 3228608768 3228739840 14 6011 56820 32 _ _ (218953 / 10000) (2189533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3228739840 :
    ThetaLowerSegment 3228739840 3228870912 (322866279422077 / 100000)
      (322879208620347 / 100000) := by
  exact
    packedTile65536 3228739840 3228870912 14 5905 56822 32 _ _ (1094767 / 50000) (2189537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3228870912 :
    ThetaLowerSegment 3228870912 3229001984 (322879208620347 / 100000)
      (322892558233533 / 100000) := by
  exact
    packedTile65536 3228870912 3229001984 14 6097 56823 32 _ _ (1094769 / 50000) (2189541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3229001984 :
    ThetaLowerSegment 3229001984 3229133056 (322892558233533 / 100000)
      (322905590387517 / 100000) := by
  exact
    packedTile65536 3229001984 3229133056 14 5952 56824 32 _ _ (1094771 / 50000) (437909 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3229133056 :
    ThetaLowerSegment 3229133056 3229264128 (322905590387517 / 100000)
      (322918556878929 / 100000) := by
  exact
    packedTile65536 3229133056 3229264128 14 5922 56825 32 _ _ (1094773 / 50000) (2189549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3229264128 :
    ThetaLowerSegment 3229264128 3229395200 (322918556878929 / 100000)
      (64586297673427 / 20000) := by
  exact
    packedTile65536 3229264128 3229395200 14 5906 56826 32 _ _ (2189551 / 100000) (1094777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3229395200 :
    ThetaLowerSegment 3229395200 3229526272 (64586297673427 / 20000) (6458893959049 / 2000) := by
  exact
    packedTile65536 3229395200 3229526272 14 6033 56827 32 _ _ (437911 / 20000) (1094779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3229526272 :
    ThetaLowerSegment 3229526272 3229657344 (6458893959049 / 2000) (322957793704829 / 100000) := by
  exact
    packedTile65536 3229526272 3229657344 14 5981 56828 32 _ _ (2189559 / 100000) (1094781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3229657344 :
    ThetaLowerSegment 3229657344 3229788416 (322957793704829 / 100000)
      (322970996769719 / 100000) := by
  exact
    packedTile65536 3229657344 3229788416 14 6030 56830 32 _ _ (2189563 / 100000) (1094783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3229788416 :
    ThetaLowerSegment 3229788416 3229919488 (322970996769719 / 100000)
      (80746030805971 / 25000) := by
  exact
    packedTile65536 3229788416 3229919488 14 5995 56831 32 _ _ (2189567 / 100000) (218957 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3229919488 :
    ThetaLowerSegment 3229919488 3230050560 (80746030805971 / 25000) (32299718620447 / 10000) := by
  exact
    packedTile65536 3229919488 3230050560 14 5966 56832 32 _ _ (2189571 / 100000) (1094787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3230050560 :
    ThetaLowerSegment 3230050560 3230181632 (32299718620447 / 10000) (16150513774191 / 5000) := by
  exact
    packedTile65536 3230050560 3230181632 14 5978 56833 32 _ _ (87583 / 4000) (1094789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3230181632 :
    ThetaLowerSegment 3230181632 3230312704 (16150513774191 / 5000) (323023476455611 / 100000) := by
  exact
    packedTile65536 3230181632 3230312704 14 6029 56834 32 _ _ (2189579 / 100000) (1094791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3230312704 :
    ThetaLowerSegment 3230312704 3230443776 (323023476455611 / 100000)
      (80759131045177 / 25000) := by
  exact
    packedTile65536 3230312704 3230443776 14 5959 56835 32 _ _ (2189583 / 100000) (1094793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3230443776 :
    ThetaLowerSegment 3230443776 3230574848 (80759131045177 / 25000) (161524758594983 / 50000) := by
  exact
    packedTile65536 3230443776 3230574848 14 5934 56836 32 _ _ (2189587 / 100000) (218959 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3230574848 :
    ThetaLowerSegment 3230574848 3230705920 (161524758594983 / 50000) (16153145217467 / 5000) := by
  exact
    packedTile65536 3230574848 3230705920 14 6114 56838 32 _ _ (2189591 / 100000) (1094797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3230705920 :
    ThetaLowerSegment 3230705920 3230836992 (16153145217467 / 5000) (32307580982227 / 10000) := by
  exact
    packedTile65536 3230705920 3230836992 14 5894 56839 32 _ _ (437919 / 20000) (1094799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3230836992 :
    ThetaLowerSegment 3230836992 3230968064 (32307580982227 / 10000) (40386120069233 / 12500) := by
  exact
    packedTile65536 3230836992 3230968064 14 6006 56840 32 _ _ (2189599 / 100000) (1094801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3230968064 :
    ThetaLowerSegment 3230968064 3231099136 (40386120069233 / 12500) (161551003104269 / 50000) := by
  exact
    packedTile65536 3230968064 3231099136 14 5958 56841 32 _ _ (2189603 / 100000) (1094803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3231099136 :
    ThetaLowerSegment 3231099136 3231230208 (161551003104269 / 50000)
      (323115097868791 / 100000) := by
  exact
    packedTile65536 3231099136 3231230208 14 5979 56842 32 _ _ (2189607 / 100000) (218961 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3231230208 :
    ThetaLowerSegment 3231230208 3231361280 (323115097868791 / 100000) (20195514036671 / 6250) := by
  exact
    packedTile65536 3231230208 3231361280 14 5995 56843 32 _ _ (2189611 / 100000) (1094807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3231361280 :
    ThetaLowerSegment 3231361280 3231492352 (20195514036671 / 6250) (323141342570201 / 100000) := by
  exact
    packedTile65536 3231361280 3231492352 14 5991 56845 32 _ _ (437923 / 20000) (1094809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3231492352 :
    ThetaLowerSegment 3231492352 3231623424 (323141342570201 / 100000)
      (161577243426529 / 50000) := by
  exact
    packedTile65536 3231492352 3231623424 14 6003 56846 32 _ _ (2189619 / 100000) (1094811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3231623424 :
    ThetaLowerSegment 3231623424 3231754496 (161577243426529 / 50000)
      (161583769600861 / 50000) := by
  exact
    packedTile65536 3231623424 3231754496 14 5961 56847 32 _ _ (273703 / 12500) (2189627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3231754496 :
    ThetaLowerSegment 3231754496 3231885568 (161583769600861 / 50000)
      (161590310019697 / 50000) := by
  exact
    packedTile65536 3231754496 3231885568 14 5974 56848 32 _ _ (547407 / 25000) (2189631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3231885568 :
    ThetaLowerSegment 3231885568 3232016640 (161590310019697 / 50000) (32319354543709 / 10000) := by
  exact
    packedTile65536 3231885568 3232016640 14 5903 56849 32 _ _ (68426 / 3125) (437927 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3232016640 :
    ThetaLowerSegment 3232016640 3232147712 (32319354543709 / 10000) (161603309876823 / 50000) := by
  exact
    packedTile65536 3232016640 3232147712 14 5971 56850 32 _ _ (547409 / 25000) (2189639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3232147712 :
    ThetaLowerSegment 3232147712 3232278784 (161603309876823 / 50000)
      (161609929158543 / 50000) := by
  exact
    packedTile65536 3232147712 3232278784 14 6046 56851 32 _ _ (54741 / 2500) (2189643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3232278784 :
    ThetaLowerSegment 3232278784 3232409856 (161609929158543 / 50000) (32323292173319 / 10000) := by
  exact
    packedTile65536 3232278784 3232409856 14 5966 56853 32 _ _ (547411 / 25000) (2189647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3232409856 :
    ThetaLowerSegment 3232409856 3232540928 (32323292173319 / 10000) (32324585160463 / 10000) := by
  exact
    packedTile65536 3232409856 3232540928 14 5905 56854 32 _ _ (136853 / 6250) (2189651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3232540928 :
    ThetaLowerSegment 3232540928 3232672000 (32324585160463 / 10000) (32325903330967 / 10000) := by
  exact
    packedTile65536 3232540928 3232672000 14 6020 56855 32 _ _ (547413 / 25000) (437931 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3232672000 :
    ThetaLowerSegment 3232672000 3232803072 (32325903330967 / 10000) (161636064821103 / 50000) := by
  exact
    packedTile65536 3232672000 3232803072 14 5981 56856 32 _ _ (273707 / 12500) (2189659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3232803072 :
    ThetaLowerSegment 3232803072 3232934144 (161636064821103 / 50000)
      (161642584533753 / 50000) := by
  exact
    packedTile65536 3232803072 3232934144 14 5955 56857 32 _ _ (109483 / 5000) (2189663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3232934144 :
    ThetaLowerSegment 3232934144 3233065216 (161642584533753 / 50000)
      (161649196224201 / 50000) := by
  exact
    packedTile65536 3232934144 3233065216 14 6039 56858 32 _ _ (68427 / 3125) (2189667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3233065216 :
    ThetaLowerSegment 3233065216 3233196288 (161649196224201 / 50000)
      (161655740047019 / 50000) := by
  exact
    packedTile65536 3233065216 3233196288 14 5977 56860 32 _ _ (547417 / 25000) (2189671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3233196288 :
    ThetaLowerSegment 3233196288 3233327360 (161655740047019 / 50000) (258659599907 / 80) := by
  exact
    packedTile65536 3233196288 3233327360 14 5946 56861 32 _ _ (273709 / 12500) (87587 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3233327360 :
    ThetaLowerSegment 3233327360 3233458432 (258659599907 / 80) (161668751089919 / 50000) := by
  exact
    packedTile65536 3233327360 3233458432 14 5938 56862 32 _ _ (547419 / 25000) (2189679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3233458432 :
    ThetaLowerSegment 3233458432 3233589504 (161668751089919 / 50000)
      (161675405527439 / 50000) := by
  exact
    packedTile65536 3233458432 3233589504 14 6078 56863 32 _ _ (27371 / 1250) (2189683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3233589504 :
    ThetaLowerSegment 3233589504 3233720576 (161675405527439 / 50000)
      (161681922027023 / 50000) := by
  exact
    packedTile65536 3233589504 3233720576 14 5952 56864 32 _ _ (547421 / 25000) (2189687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3233720576 :
    ThetaLowerSegment 3233720576 3233851648 (161681922027023 / 50000)
      (161688546928067 / 50000) := by
  exact
    packedTile65536 3233720576 3233851648 14 6051 56865 32 _ _ (273711 / 12500) (2189691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3233851648 :
    ThetaLowerSegment 3233851648 3233982720 (161688546928067 / 50000) (32339019478337 / 10000) := by
  exact
    packedTile65536 3233851648 3233982720 14 5983 56866 32 _ _ (547423 / 25000) (437939 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3233982720 :
    ThetaLowerSegment 3233982720 3234113792 (32339019478337 / 10000)
      (323403339534461 / 100000) := by
  exact
    packedTile65536 3233982720 3234113792 14 6003 56868 32 _ _ (2189697 / 100000) (21897 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3234113792 :
    ThetaLowerSegment 3234113792 3234244864 (323403339534461 / 100000)
      (323416433946441 / 100000) := by
  exact
    packedTile65536 3234113792 3234244864 14 5980 56869 32 _ _ (2189701 / 100000) (273713 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3234244864 :
    ThetaLowerSegment 3234244864 3234375936 (323416433946441 / 100000)
      (161714752147793 / 50000) := by
  exact
    packedTile65536 3234244864 3234375936 14 5969 56870 32 _ _ (437941 / 20000) (547427 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3234375936 :
    ThetaLowerSegment 3234375936 3234507008 (161714752147793 / 50000)
      (323442495839083 / 100000) := by
  exact
    packedTile65536 3234375936 3234507008 14 5933 56871 32 _ _ (2189709 / 100000) (136857 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3234507008 :
    ThetaLowerSegment 3234507008 3234638080 (323442495839083 / 100000)
      (32345567572163 / 10000) := by
  exact
    packedTile65536 3234507008 3234638080 14 6019 56872 32 _ _ (2189713 / 100000) (547429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3234638080 :
    ThetaLowerSegment 3234638080 3234769152 (32345567572163 / 10000) (20216800055333 / 6250) := by
  exact
    packedTile65536 3234638080 3234769152 14 5994 56873 32 _ _ (2189717 / 100000) (54743 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3234769152 :
    ThetaLowerSegment 3234769152 3234900224 (20216800055333 / 6250) (161740984933711 / 50000) := by
  exact
    packedTile65536 3234769152 3234900224 14 6014 56875 32 _ _ (2189721 / 100000) (547431 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3234900224 :
    ThetaLowerSegment 3234900224 3235031296 (161740984933711 / 50000)
      (323495241790647 / 100000) := by
  exact
    packedTile65536 3234900224 3235031296 14 6061 56876 32 _ _ (87589 / 4000) (68429 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3235031296 :
    ThetaLowerSegment 3235031296 3235162368 (323495241790647 / 100000)
      (323508621034837 / 100000) := by
  exact
    packedTile65536 3235031296 3235162368 14 6110 56877 32 _ _ (2189729 / 100000) (547433 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3235162368 :
    ThetaLowerSegment 3235162368 3235293440 (323508621034837 / 100000)
      (323521807606963 / 100000) := by
  exact
    packedTile65536 3235162368 3235293440 14 6022 56878 32 _ _ (2189733 / 100000) (273717 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3235293440 :
    ThetaLowerSegment 3235293440 3235424512 (323521807606963 / 100000)
      (32353492632133 / 10000) := by
  exact
    packedTile65536 3235293440 3235424512 14 5991 56879 32 _ _ (2189737 / 100000) (109487 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3235424512 :
    ThetaLowerSegment 3235424512 3235555584 (32353492632133 / 10000) (161773992968327 / 50000) := by
  exact
    packedTile65536 3235424512 3235555584 14 5964 56880 32 _ _ (2189741 / 100000) (136859 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3235555584 :
    ThetaLowerSegment 3235555584 3235686656 (161773992968327 / 50000) (80890288765771 / 25000) := by
  exact
    packedTile65536 3235555584 3235686656 14 6014 56881 32 _ _ (437949 / 20000) (547437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3235686656 :
    ThetaLowerSegment 3235686656 3235817728 (80890288765771 / 25000) (161787087655319 / 50000) := by
  exact
    packedTile65536 3235686656 3235817728 14 5946 56883 32 _ _ (2189749 / 100000) (273719 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3235817728 :
    ThetaLowerSegment 3235817728 3235948800 (161787087655319 / 50000)
      (323587079525067 / 100000) := by
  exact
    packedTile65536 3235817728 3235948800 14 5893 56884 32 _ _ (2189753 / 100000) (547439 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3235948800 :
    ThetaLowerSegment 3235948800 3236079872 (323587079525067 / 100000)
      (64720036606191 / 20000) := by
  exact
    packedTile65536 3235948800 3236079872 14 5984 56885 32 _ _ (2189757 / 100000) (13686 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3236079872 :
    ThetaLowerSegment 3236079872 3236210944 (64720036606191 / 20000)
      (323613260283647 / 100000) := by
  exact
    packedTile65536 3236079872 3236210944 14 5972 56886 32 _ _ (2189761 / 100000) (547441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3236210944 :
    ThetaLowerSegment 3236210944 3236342016 (323613260283647 / 100000)
      (161813193962411 / 50000) := by
  exact
    packedTile65536 3236210944 3236342016 14 5995 56887 32 _ _ (437953 / 20000) (273721 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3236342016 :
    ThetaLowerSegment 3236342016 3236473088 (161813193962411 / 50000) (32363946522529 / 10000) := by
  exact
    packedTile65536 3236342016 3236473088 14 5972 56888 32 _ _ (2189769 / 100000) (547443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3236473088 :
    ThetaLowerSegment 3236473088 3236604160 (32363946522529 / 10000) (80913152609653 / 25000) := by
  exact
    packedTile65536 3236473088 3236604160 14 6003 56890 32 _ _ (1094887 / 50000) (2189777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3236604160 :
    ThetaLowerSegment 3236604160 3236735232 (80913152609653 / 25000) (40458221375549 / 12500) := by
  exact
    packedTile65536 3236604160 3236735232 14 6010 56891 32 _ _ (1094889 / 50000) (2189781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3236735232 :
    ThetaLowerSegment 3236735232 3236866304 (40458221375549 / 12500) (16183938258539 / 5000) := by
  exact
    packedTile65536 3236735232 3236866304 14 5934 56892 32 _ _ (1094891 / 50000) (437957 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3236866304 :
    ThetaLowerSegment 3236866304 3236997376 (16183938258539 / 5000) (20230742076861 / 6250) := by
  exact
    packedTile65536 3236866304 3236997376 14 5986 56893 32 _ _ (1094893 / 50000) (2189789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3236997376 :
    ThetaLowerSegment 3236997376 3237128448 (20230742076861 / 6250) (161852465473773 / 50000) := by
  exact
    packedTile65536 3236997376 3237128448 14 5963 56894 32 _ _ (218979 / 10000) (2189793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3237128448 :
    ThetaLowerSegment 3237128448 3237259520 (161852465473773 / 50000)
      (161859078651653 / 50000) := by
  exact
    packedTile65536 3237128448 3237259520 14 6040 56895 32 _ _ (1094897 / 50000) (2189797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3237259520 :
    ThetaLowerSegment 3237259520 3237390592 (161859078651653 / 50000) (40466417759633 / 12500) := by
  exact
    packedTile65536 3237259520 3237390592 14 6021 56896 32 _ _ (1094899 / 50000) (2189801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3237390592 :
    ThetaLowerSegment 3237390592 3237521664 (40466417759633 / 12500) (40468053541727 / 12500) := by
  exact
    packedTile65536 3237390592 3237521664 14 5976 56898 32 _ _ (1094901 / 50000) (437961 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3237521664 :
    ThetaLowerSegment 3237521664 3237652736 (40468053541727 / 12500) (161878703656989 / 50000) := by
  exact
    packedTile65536 3237521664 3237652736 14 5927 56899 32 _ _ (1094903 / 50000) (2189809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3237652736 :
    ThetaLowerSegment 3237652736 3237783808 (161878703656989 / 50000) (80942619572467 / 25000) := by
  exact
    packedTile65536 3237652736 3237783808 14 5969 56900 32 _ _ (218981 / 10000) (2189813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3237783808 :
    ThetaLowerSegment 3237783808 3237914880 (80942619572467 / 25000) (16189183924433 / 5000) := by
  exact
    packedTile65536 3237783808 3237914880 14 6028 56901 32 _ _ (1094907 / 50000) (2189817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3237914880 :
    ThetaLowerSegment 3237914880 3238045952 (16189183924433 / 5000) (8094918792553 / 2500) := by
  exact
    packedTile65536 3237914880 3238045952 14 5970 56902 32 _ _ (1094909 / 50000) (2189821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3238045952 :
    ThetaLowerSegment 3238045952 3238177024 (8094918792553 / 2500) (80952436526467 / 25000) := by
  exact
    packedTile65536 3238045952 3238177024 14 5934 56903 32 _ _ (1094911 / 50000) (87593 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3238177024 :
    ThetaLowerSegment 3238177024 3238308096 (80952436526467 / 25000) (161911356032807 / 50000) := by
  exact
    packedTile65536 3238177024 3238308096 14 5921 56904 32 _ _ (1094913 / 50000) (2189829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3238308096 :
    ThetaLowerSegment 3238308096 3238439168 (161911356032807 / 50000) (20239722487389 / 6250) := by
  exact
    packedTile65536 3238308096 3238439168 14 5867 56906 32 _ _ (218983 / 10000) (2189833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3238439168 :
    ThetaLowerSegment 3238439168 3238570240 (20239722487389 / 6250) (80962140758129 / 25000) := by
  exact
    packedTile65536 3238439168 3238570240 14 5938 56907 32 _ _ (1094917 / 50000) (2189837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3238570240 :
    ThetaLowerSegment 3238570240 3238701312 (80962140758129 / 25000) (80965394857397 / 25000) := by
  exact
    packedTile65536 3238570240 3238701312 14 5944 56908 32 _ _ (1094919 / 50000) (2189841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3238701312 :
    ThetaLowerSegment 3238701312 3238832384 (80965394857397 / 25000) (6477494851397 / 2000) := by
  exact
    packedTile65536 3238701312 3238832384 14 6011 56909 32 _ _ (1094921 / 50000) (437969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3238832384 :
    ThetaLowerSegment 3238832384 3238963456 (6477494851397 / 2000) (10121499107173 / 3125) := by
  exact
    packedTile65536 3238832384 3238963456 14 6041 56910 32 _ _ (1094923 / 50000) (2189849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3238963456 :
    ThetaLowerSegment 3238963456 3239094528 (10121499107173 / 3125) (40487631151717 / 12500) := by
  exact
    packedTile65536 3238963456 3239094528 14 5972 56911 32 _ _ (43797 / 2000) (2189853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3239094528 :
    ThetaLowerSegment 3239094528 3239225600 (40487631151717 / 12500) (80978554748923 / 25000) := by
  exact
    packedTile65536 3239094528 3239225600 14 6014 56913 32 _ _ (1094927 / 50000) (2189857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3239225600 :
    ThetaLowerSegment 3239225600 3239356672 (80978554748923 / 25000)
      (323927294643781 / 100000) := by
  exact
    packedTile65536 3239225600 3239356672 14 5971 56914 32 _ _ (2189859 / 100000) (1094931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3239356672 :
    ThetaLowerSegment 3239356672 3239487744 (323927294643781 / 100000)
      (323940556454109 / 100000) := by
  exact
    packedTile65536 3239356672 3239487744 14 6056 56915 32 _ _ (2189863 / 100000) (1094933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3239487744 :
    ThetaLowerSegment 3239487744 3239618816 (323940556454109 / 100000)
      (40494207851013 / 12500) := by
  exact
    packedTile65536 3239487744 3239618816 14 5985 56916 32 _ _ (2189867 / 100000) (218987 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3239618816 :
    ThetaLowerSegment 3239618816 3239749888 (40494207851013 / 12500) (8099170926801 / 2500) := by
  exact
    packedTile65536 3239618816 3239749888 14 6016 56917 32 _ _ (2189871 / 100000) (1094937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3239749888 :
    ThetaLowerSegment 3239749888 3239880960 (8099170926801 / 2500) (32398004201829 / 10000) := by
  exact
    packedTile65536 3239749888 3239880960 14 6030 56918 32 _ _ (17519 / 800) (1094939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3239880960 :
    ThetaLowerSegment 3239880960 3240012032 (32398004201829 / 10000)
      (323993227279749 / 100000) := by
  exact
    packedTile65536 3239880960 3240012032 14 6021 56919 32 _ _ (2189879 / 100000) (1094941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3240012032 :
    ThetaLowerSegment 3240012032 3240143104 (323993227279749 / 100000)
      (40500802665603 / 12500) := by
  exact
    packedTile65536 3240012032 3240143104 14 6025 56921 32 _ _ (2189883 / 100000) (1094943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3240143104 :
    ThetaLowerSegment 3240143104 3240274176 (40500802665603 / 12500) (64803869645557 / 20000) := by
  exact
    packedTile65536 3240143104 3240274176 14 5903 56922 32 _ _ (2189887 / 100000) (218989 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3240274176 :
    ThetaLowerSegment 3240274176 3240405248 (64803869645557 / 20000) (40504053555841 / 12500) := by
  exact
    packedTile65536 3240274176 3240405248 14 5973 56923 32 _ _ (2189891 / 100000) (1094947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3240405248 :
    ThetaLowerSegment 3240405248 3240536320 (40504053555841 / 12500) (81011381004707 / 25000) := by
  exact
    packedTile65536 3240405248 3240536320 14 5980 56924 32 _ _ (437979 / 20000) (1094949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3240536320 :
    ThetaLowerSegment 3240536320 3240667392 (81011381004707 / 25000) (64811742756101 / 20000) := by
  exact
    packedTile65536 3240536320 3240667392 14 6023 56925 32 _ _ (2189899 / 100000) (1094951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3240667392 :
    ThetaLowerSegment 3240667392 3240798464 (64811742756101 / 20000) (16203580067983 / 5000) := by
  exact
    packedTile65536 3240667392 3240798464 14 5885 56926 32 _ _ (2189903 / 100000) (1094953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3240798464 :
    ThetaLowerSegment 3240798464 3240929536 (16203580067983 / 5000) (324084799929149 / 100000) := by
  exact
    packedTile65536 3240798464 3240929536 14 6027 56928 32 _ _ (2189907 / 100000) (218991 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3240929536 :
    ThetaLowerSegment 3240929536 3241060608 (324084799929149 / 100000)
      (162048920424577 / 50000) := by
  exact
    packedTile65536 3240929536 3241060608 14 5955 56929 32 _ _ (2189911 / 100000) (1094957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3241060608 :
    ThetaLowerSegment 3241060608 3241191680 (162048920424577 / 50000)
      (324111017567709 / 100000) := by
  exact
    packedTile65536 3241060608 3241191680 14 6017 56930 32 _ _ (437983 / 20000) (1094959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3241191680 :
    ThetaLowerSegment 3241191680 3241322752 (324111017567709 / 100000)
      (81030996019527 / 25000) := by
  exact
    packedTile65536 3241191680 3241322752 14 5921 56931 32 _ _ (2189919 / 100000) (1094961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3241322752 :
    ThetaLowerSegment 3241322752 3241339136 (81030996019527 / 25000) (162062800120641 / 50000) := by
  exact
    packedTile65536 3241322752 3241339136 11 738 56932 32 _ _ (2189923 / 100000) (1094963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3241339136 :
    ThetaLowerSegment 3241339136 3241341184 (162062800120641 / 50000)
      (162062909616841 / 50000) := by
  exact
    packedTile65536 3241339136 3241341184 8 100 56932 32 _ _ (547481 / 25000) (2189927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3209341184_3241341184 :
    ThetaLowerSegment 3209341184 3241341184 (320927380206479 / 100000)
      (162062909616841 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3209341184 cell3209472256)
                  (ThetaLowerSegment.join cell3209603328 cell3209734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3209865472 cell3209996544)
                  (ThetaLowerSegment.join cell3210127616 cell3210258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3210389760 cell3210520832)
                  (ThetaLowerSegment.join cell3210651904 cell3210782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3210914048 cell3211045120)
                  (ThetaLowerSegment.join cell3211176192 cell3211307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3211438336 cell3211569408)
                  (ThetaLowerSegment.join cell3211700480 cell3211831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3211962624 cell3212093696)
                  (ThetaLowerSegment.join cell3212224768 cell3212355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3212486912 cell3212617984)
                  (ThetaLowerSegment.join cell3212749056 cell3212880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3213011200 cell3213142272)
                  (ThetaLowerSegment.join cell3213273344 cell3213404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3213535488 cell3213666560)
                  (ThetaLowerSegment.join cell3213797632 cell3213928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3214059776 cell3214190848)
                  (ThetaLowerSegment.join cell3214321920 cell3214452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3214584064 cell3214715136)
                  (ThetaLowerSegment.join cell3214846208 cell3214977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3215108352 cell3215239424)
                  (ThetaLowerSegment.join cell3215370496 cell3215501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3215632640 cell3215763712)
                  (ThetaLowerSegment.join cell3215894784 cell3216025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3216156928 cell3216288000)
                  (ThetaLowerSegment.join cell3216419072 cell3216550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3216681216 cell3216812288)
                  (ThetaLowerSegment.join cell3216943360 cell3217074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3217205504 cell3217336576)
                  (ThetaLowerSegment.join cell3217467648 cell3217598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3217729792 cell3217860864)
                  (ThetaLowerSegment.join cell3217991936 cell3218123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3218254080 cell3218385152)
                  (ThetaLowerSegment.join cell3218516224 cell3218647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3218778368 cell3218909440)
                  (ThetaLowerSegment.join cell3219040512 cell3219171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3219302656 cell3219433728)
                  (ThetaLowerSegment.join cell3219564800 cell3219695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3219826944 cell3219958016)
                  (ThetaLowerSegment.join cell3220089088 cell3220220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3220351232 cell3220482304)
                  (ThetaLowerSegment.join cell3220613376 cell3220744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3220875520 cell3221006592)
                  (ThetaLowerSegment.join cell3221137664 cell3221268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3221399808 cell3221530880)
                  (ThetaLowerSegment.join cell3221661952 cell3221793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3221924096 cell3222055168)
                  (ThetaLowerSegment.join cell3222186240 cell3222317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3222448384 cell3222579456)
                  (ThetaLowerSegment.join cell3222710528 cell3222841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3222972672 cell3223103744)
                  (ThetaLowerSegment.join cell3223234816 cell3223365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3223496960 cell3223628032)
                  (ThetaLowerSegment.join cell3223759104 cell3223890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3224021248 cell3224152320)
                  (ThetaLowerSegment.join cell3224283392 cell3224414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3224545536 cell3224676608)
                  (ThetaLowerSegment.join cell3224807680 cell3224938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3225069824 cell3225200896)
                  (ThetaLowerSegment.join cell3225331968 cell3225463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3225594112 cell3225725184)
                  (ThetaLowerSegment.join cell3225856256 cell3225987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3226118400 cell3226249472)
                  (ThetaLowerSegment.join cell3226380544 cell3226511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3226642688 cell3226773760)
                  (ThetaLowerSegment.join cell3226904832 cell3227035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3227166976 cell3227298048)
                  (ThetaLowerSegment.join cell3227429120 cell3227560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3227691264 cell3227822336)
                  (ThetaLowerSegment.join cell3227953408 cell3228084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3228215552 cell3228346624)
                  (ThetaLowerSegment.join cell3228477696 cell3228608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3228739840 cell3228870912)
                  (ThetaLowerSegment.join cell3229001984 cell3229133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3229264128 cell3229395200)
                  (ThetaLowerSegment.join cell3229526272 cell3229657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3229788416 cell3229919488)
                  (ThetaLowerSegment.join cell3230050560 cell3230181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3230312704 cell3230443776)
                  (ThetaLowerSegment.join cell3230574848 cell3230705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3230836992 cell3230968064)
                  (ThetaLowerSegment.join cell3231099136 cell3231230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3231361280 cell3231492352)
                  (ThetaLowerSegment.join cell3231623424 cell3231754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3231885568 cell3232016640)
                  (ThetaLowerSegment.join cell3232147712 cell3232278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3232409856 cell3232540928)
                  (ThetaLowerSegment.join cell3232672000 cell3232803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3232934144 cell3233065216)
                  (ThetaLowerSegment.join cell3233196288 cell3233327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3233458432 cell3233589504)
                  (ThetaLowerSegment.join cell3233720576 cell3233851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3233982720 cell3234113792)
                  (ThetaLowerSegment.join cell3234244864 cell3234375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3234507008 cell3234638080)
                  (ThetaLowerSegment.join cell3234769152 cell3234900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3235031296 cell3235162368)
                  (ThetaLowerSegment.join cell3235293440 cell3235424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3235555584 cell3235686656)
                  (ThetaLowerSegment.join cell3235817728 cell3235948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3236079872 cell3236210944)
                  (ThetaLowerSegment.join cell3236342016 cell3236473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3236604160 cell3236735232)
                  (ThetaLowerSegment.join cell3236866304 cell3236997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3237128448 cell3237259520)
                  (ThetaLowerSegment.join cell3237390592 cell3237521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3237652736 cell3237783808)
                  (ThetaLowerSegment.join cell3237914880 cell3238045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3238177024 cell3238308096)
                  (ThetaLowerSegment.join cell3238439168 cell3238570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3238701312 cell3238832384)
                  (ThetaLowerSegment.join cell3238963456 cell3239094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3239225600 cell3239356672)
                  (ThetaLowerSegment.join cell3239487744 cell3239618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3239749888 cell3239880960)
                  (ThetaLowerSegment.join cell3240012032 cell3240143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3240274176 cell3240405248)
                  (ThetaLowerSegment.join cell3240536320 cell3240667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3240798464 cell3240929536)
                (ThetaLowerSegment.join cell3241060608 cell3241191680))
              (ThetaLowerSegment.join cell3241322752 cell3241339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
