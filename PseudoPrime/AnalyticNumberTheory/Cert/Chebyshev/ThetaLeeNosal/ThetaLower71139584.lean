/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis8192
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis16384

/-! # Direct theta estimate up to 71139584 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell55836928 :
    ThetaLowerSegment 55836928 55853312 (2791312980113 / 50000) (558428132013 / 10000) := by
  exact
    packedTile8192 55836928 55853312 11 928 7472 26 _ _ (1783793 / 100000) (445949 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55853312 :
    ThetaLowerSegment 55853312 55869696 (558428132013 / 10000) (111718091963 / 2000) := by
  exact
    packedTile8192 55853312 55869696 11 910 7473 26 _ _ (891911 / 50000) (71353 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55869696 :
    ThetaLowerSegment 55869696 55886080 (111718091963 / 2000) (2793762167883 / 50000) := by
  exact
    packedTile8192 55869696 55886080 11 908 7474 26 _ _ (445963 / 25000) (356771 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55886080 :
    ThetaLowerSegment 55886080 55902464 (2793762167883 / 50000) (5589174425691 / 100000) := by
  exact
    packedTile8192 55886080 55902464 11 925 7475 26 _ _ (1783881 / 100000) (445971 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55902464 :
    ThetaLowerSegment 55902464 55918848 (5589174425691 / 100000) (5590801351611 / 100000) := by
  exact
    packedTile8192 55902464 55918848 11 912 7476 26 _ _ (178391 / 10000) (1783913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55918848 :
    ThetaLowerSegment 55918848 55935232 (5590801351611 / 100000) (5592394410031 / 100000) := by
  exact
    packedTile8192 55918848 55935232 11 893 7477 26 _ _ (89197 / 5000) (1783943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55935232 :
    ThetaLowerSegment 55935232 55951616 (5592394410031 / 100000) (559401960579 / 10000) := by
  exact
    packedTile8192 55935232 55951616 11 911 7478 26 _ _ (1783969 / 100000) (445993 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55951616 :
    ThetaLowerSegment 55951616 55968000 (559401960579 / 10000) (279781706199 / 5000) := by
  exact
    packedTile8192 55951616 55968000 11 905 7480 26 _ _ (891999 / 50000) (1784001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55968000 :
    ThetaLowerSegment 55968000 55984384 (279781706199 / 5000) (1399325993547 / 25000) := by
  exact
    packedTile8192 55968000 55984384 11 936 7481 26 _ _ (446007 / 25000) (1784031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55984384 :
    ThetaLowerSegment 55984384 56000768 (1399325993547 / 25000) (2799499414169 / 50000) := by
  exact
    packedTile8192 55984384 56000768 11 950 7482 26 _ _ (1784057 / 100000) (89203 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56000768 :
    ThetaLowerSegment 56000768 56017152 (2799499414169 / 50000) (175018946557 / 3125) := by
  exact
    packedTile8192 56000768 56017152 11 901 7483 26 _ _ (892043 / 50000) (1784089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56017152 :
    ThetaLowerSegment 56017152 56033536 (175018946557 / 3125) (5602235186819 / 100000) := by
  exact
    packedTile8192 56017152 56033536 11 913 7484 26 _ _ (356823 / 20000) (892059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56033536 :
    ThetaLowerSegment 56033536 56049920 (5602235186819 / 100000) (2801933839747 / 50000) := by
  exact
    packedTile8192 56033536 56049920 11 915 7485 26 _ _ (356829 / 20000) (446037 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56049920 :
    ThetaLowerSegment 56049920 56066304 (2801933839747 / 50000) (280276258857 / 5000) := by
  exact
    packedTile8192 56049920 56066304 11 929 7486 26 _ _ (892087 / 50000) (1784177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56066304 :
    ThetaLowerSegment 56066304 56082688 (280276258857 / 5000) (5607218385787 / 100000) := by
  exact
    packedTile8192 56066304 56082688 11 949 7487 26 _ _ (1784203 / 100000) (892103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56082688 :
    ThetaLowerSegment 56082688 56099072 (5607218385787 / 100000) (5608845605371 / 100000) := by
  exact
    packedTile8192 56082688 56099072 11 912 7488 26 _ _ (223029 / 12500) (356847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56099072 :
    ThetaLowerSegment 56099072 56115456 (5608845605371 / 100000) (5610533516277 / 100000) := by
  exact
    packedTile8192 56099072 56115456 11 946 7489 26 _ _ (1784261 / 100000) (223033 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56115456 :
    ThetaLowerSegment 56115456 56131840 (5610533516277 / 100000) (280609912989 / 5000) := by
  exact
    packedTile8192 56115456 56131840 11 933 7491 26 _ _ (1784291 / 100000) (892147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56131840 :
    ThetaLowerSegment 56131840 56148224 (280609912989 / 5000) (280691277981 / 5000) := by
  exact
    packedTile8192 56131840 56148224 11 912 7492 26 _ _ (11152 / 625) (1784323 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56148224 :
    ThetaLowerSegment 56148224 56164608 (280691277981 / 5000) (2807749639491 / 50000) := by
  exact
    packedTile8192 56148224 56164608 11 938 7493 26 _ _ (1784349 / 100000) (55761 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56164608 :
    ThetaLowerSegment 56164608 56180992 (2807749639491 / 50000) (2808586512773 / 50000) := by
  exact
    packedTile8192 56164608 56180992 11 938 7494 26 _ _ (892189 / 50000) (1784381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56180992 :
    ThetaLowerSegment 56180992 56197376 (2808586512773 / 50000) (2809428752877 / 50000) := by
  exact
    packedTile8192 56180992 56197376 11 944 7495 26 _ _ (1784407 / 100000) (178441 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56197376 :
    ThetaLowerSegment 56197376 56213760 (2809428752877 / 50000) (5620447439121 / 100000) := by
  exact
    packedTile8192 56197376 56213760 11 891 7496 26 _ _ (1784437 / 100000) (44611 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56213760 :
    ThetaLowerSegment 56213760 56230144 (5620447439121 / 100000) (5622099854637 / 100000) := by
  exact
    packedTile8192 56213760 56230144 11 926 7497 26 _ _ (892233 / 50000) (1784469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56230144 :
    ThetaLowerSegment 56230144 56246528 (5622099854637 / 100000) (2811855626811 / 50000) := by
  exact
    packedTile8192 56230144 56246528 11 903 7498 26 _ _ (356899 / 20000) (892249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56246528 :
    ThetaLowerSegment 56246528 56262912 (2811855626811 / 50000) (112506239433 / 2000) := by
  exact
    packedTile8192 56246528 56262912 11 897 7499 26 _ _ (446131 / 25000) (1784527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56262912 :
    ThetaLowerSegment 56262912 56279296 (112506239433 / 2000) (5626976959599 / 100000) := by
  exact
    packedTile8192 56262912 56279296 11 933 7500 26 _ _ (1784553 / 100000) (446139 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56279296 :
    ThetaLowerSegment 56279296 56295680 (5626976959599 / 100000) (5628616990457 / 100000) := by
  exact
    packedTile8192 56279296 56295680 11 919 7501 26 _ _ (892291 / 50000) (356917 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56295680 :
    ThetaLowerSegment 56295680 56312064 (5628616990457 / 100000) (1126051052671 / 20000) := by
  exact
    packedTile8192 56295680 56312064 11 918 7503 26 _ _ (1784611 / 100000) (892307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56312064 :
    ThetaLowerSegment 56312064 56328448 (1126051052671 / 20000) (1126369432447 / 20000) := by
  exact
    packedTile8192 56312064 56328448 11 892 7504 26 _ _ (11154 / 625) (1784643 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56328448 :
    ThetaLowerSegment 56328448 56344832 (1126369432447 / 20000) (225340062053 / 4000) := by
  exact
    packedTile8192 56328448 56344832 11 927 7505 26 _ _ (178467 / 10000) (1784673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56344832 :
    ThetaLowerSegment 56344832 56361216 (225340062053 / 4000) (704394942087 / 12500) := by
  exact
    packedTile8192 56344832 56361216 11 929 7506 26 _ _ (1784699 / 100000) (892351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56361216 :
    ThetaLowerSegment 56361216 56377600 (704394942087 / 12500) (35229819663 / 625) := by
  exact
    packedTile8192 56361216 56377600 11 903 7507 26 _ _ (223091 / 12500) (1784731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56377600 :
    ThetaLowerSegment 56377600 56393984 (35229819663 / 625) (2819183359419 / 50000) := by
  exact
    packedTile8192 56377600 56393984 11 894 7508 26 _ _ (1784757 / 100000) (44619 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56393984 :
    ThetaLowerSegment 56393984 56410368 (2819183359419 / 50000) (2819995437049 / 50000) := by
  exact
    packedTile8192 56393984 56410368 11 910 7509 26 _ _ (892393 / 50000) (1784789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56410368 :
    ThetaLowerSegment 56410368 56426752 (2819995437049 / 50000) (2820805743059 / 50000) := by
  exact
    packedTile8192 56410368 56426752 11 908 7510 26 _ _ (356963 / 20000) (892409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56426752 :
    ThetaLowerSegment 56426752 56443136 (2820805743059 / 50000) (2821603568327 / 50000) := by
  exact
    packedTile8192 56426752 56443136 11 894 7511 26 _ _ (446211 / 25000) (1784847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56443136 :
    ThetaLowerSegment 56443136 56459520 (2821603568327 / 50000) (564479924337 / 10000) := by
  exact
    packedTile8192 56443136 56459520 11 892 7512 26 _ _ (1784873 / 100000) (446219 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56459520 :
    ThetaLowerSegment 56459520 56475904 (564479924337 / 10000) (2823226031311 / 50000) := by
  exact
    packedTile8192 56459520 56475904 11 926 7513 26 _ _ (892451 / 50000) (356981 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56475904 :
    ThetaLowerSegment 56475904 56492288 (2823226031311 / 50000) (5648120973107 / 100000) := by
  exact
    packedTile8192 56475904 56492288 11 935 7515 26 _ _ (1784931 / 100000) (892467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56492288 :
    ThetaLowerSegment 56492288 56508672 (5648120973107 / 100000) (5649741716787 / 100000) := by
  exact
    packedTile8192 56492288 56508672 11 908 7516 26 _ _ (11156 / 625) (1784963 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56508672 :
    ThetaLowerSegment 56508672 56525056 (5649741716787 / 100000) (5651391046623 / 100000) := by
  exact
    packedTile8192 56508672 56525056 11 924 7517 26 _ _ (1784989 / 100000) (55781 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56525056 :
    ThetaLowerSegment 56525056 56541440 (5651391046623 / 100000) (5653010057949 / 100000) := by
  exact
    packedTile8192 56525056 56541440 11 907 7518 26 _ _ (892509 / 50000) (1785021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56541440 :
    ThetaLowerSegment 56541440 56557824 (5653010057949 / 100000) (706832653303 / 12500) := by
  exact
    packedTile8192 56541440 56557824 11 925 7519 26 _ _ (1785047 / 100000) (35701 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56557824 :
    ThetaLowerSegment 56557824 56574208 (706832653303 / 12500) (353518745387 / 6250) := by
  exact
    packedTile8192 56557824 56574208 11 918 7520 26 _ _ (446269 / 25000) (1785079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56574208 :
    ThetaLowerSegment 56574208 56590592 (353518745387 / 6250) (2828962185871 / 50000) := by
  exact
    packedTile8192 56574208 56590592 11 910 7521 26 _ _ (357021 / 20000) (446277 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56590592 :
    ThetaLowerSegment 56590592 56606976 (2828962185871 / 50000) (2829824405593 / 50000) := by
  exact
    packedTile8192 56590592 56606976 11 966 7522 26 _ _ (892567 / 50000) (1785137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56606976 :
    ThetaLowerSegment 56606976 56623360 (2829824405593 / 50000) (1132248592349 / 20000) := by
  exact
    packedTile8192 56606976 56623360 11 893 7523 26 _ _ (1785163 / 100000) (892583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56623360 :
    ThetaLowerSegment 56623360 56639744 (1132248592349 / 20000) (5662878197617 / 100000) := by
  exact
    packedTile8192 56623360 56639744 11 916 7524 26 _ _ (223149 / 12500) (357039 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56639744 :
    ThetaLowerSegment 56639744 56656128 (5662878197617 / 100000) (5664542023589 / 100000) := by
  exact
    packedTile8192 56639744 56656128 11 932 7525 26 _ _ (1785221 / 100000) (223153 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56656128 :
    ThetaLowerSegment 56656128 56672512 (5664542023589 / 100000) (5666202306089 / 100000) := by
  exact
    packedTile8192 56656128 56672512 11 930 7527 26 _ _ (7141 / 400) (1785253 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56672512 :
    ThetaLowerSegment 56672512 56688896 (5666202306089 / 100000) (5667887608521 / 100000) := by
  exact
    packedTile8192 56672512 56688896 11 944 7528 26 _ _ (892639 / 50000) (1785281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56688896 :
    ThetaLowerSegment 56688896 56705280 (5667887608521 / 100000) (5669612215083 / 100000) := by
  exact
    packedTile8192 56688896 56705280 11 966 7529 26 _ _ (1785307 / 100000) (178531 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56705280 :
    ThetaLowerSegment 56705280 56721664 (5669612215083 / 100000) (5671263650883 / 100000) := by
  exact
    packedTile8192 56705280 56721664 11 925 7530 26 _ _ (223167 / 12500) (1785339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56721664 :
    ThetaLowerSegment 56721664 56738048 (5671263650883 / 100000) (5672945464713 / 100000) := by
  exact
    packedTile8192 56721664 56738048 11 942 7531 26 _ _ (357073 / 20000) (223171 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56738048 :
    ThetaLowerSegment 56738048 56754432 (5672945464713 / 100000) (5674505899069 / 100000) := by
  exact
    packedTile8192 56738048 56754432 11 874 7532 26 _ _ (892697 / 50000) (1785397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56754432 :
    ThetaLowerSegment 56754432 56770816 (5674505899069 / 100000) (709525033187 / 12500) := by
  exact
    packedTile8192 56754432 56770816 11 949 7533 26 _ _ (1785423 / 100000) (892713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56770816 :
    ThetaLowerSegment 56770816 56787200 (709525033187 / 12500) (1419462059423 / 25000) := by
  exact
    packedTile8192 56770816 56787200 11 923 7534 26 _ _ (446363 / 25000) (357091 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56787200 :
    ThetaLowerSegment 56787200 56803584 (1419462059423 / 25000) (5679489094731 / 100000) := by
  exact
    packedTile8192 56787200 56803584 11 919 7535 26 _ _ (1785481 / 100000) (446371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56803584 :
    ThetaLowerSegment 56803584 56819968 (5679489094731 / 100000) (5681153189119 / 100000) := by
  exact
    packedTile8192 56803584 56819968 11 932 7536 26 _ _ (1785509 / 100000) (223189 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56819968 :
    ThetaLowerSegment 56819968 56836352 (5681153189119 / 100000) (5682783385313 / 100000) := by
  exact
    packedTile8192 56819968 56836352 11 913 7537 26 _ _ (892769 / 50000) (1785541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56836352 :
    ThetaLowerSegment 56836352 56852736 (5682783385313 / 100000) (177637032466 / 3125) := by
  exact
    packedTile8192 56836352 56852736 11 897 7538 26 _ _ (1785567 / 100000) (178557 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56852736 :
    ThetaLowerSegment 56852736 56869120 (177637032466 / 3125) (1421494001237 / 25000) := by
  exact
    packedTile8192 56852736 56869120 11 891 7540 26 _ _ (446399 / 25000) (1785599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56869120 :
    ThetaLowerSegment 56869120 56885504 (1421494001237 / 25000) (2843786176849 / 50000) := by
  exact
    packedTile8192 56869120 56885504 11 894 7541 26 _ _ (2857 / 160) (446407 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56885504 :
    ThetaLowerSegment 56885504 56901888 (2843786176849 / 50000) (177790038268 / 3125) := by
  exact
    packedTile8192 56885504 56901888 11 957 7542 26 _ _ (892827 / 50000) (1785657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56901888 :
    ThetaLowerSegment 56901888 56918272 (177790038268 / 3125) (2845455776121 / 50000) := by
  exact
    packedTile8192 56901888 56918272 11 913 7543 26 _ _ (892841 / 50000) (357137 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56918272 :
    ThetaLowerSegment 56918272 56934656 (2845455776121 / 50000) (5692549049229 / 100000) := by
  exact
    packedTile8192 56918272 56934656 11 917 7544 26 _ _ (1785711 / 100000) (892857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56934656 :
    ThetaLowerSegment 56934656 56951040 (5692549049229 / 100000) (5694227644829 / 100000) := by
  exact
    packedTile8192 56934656 56951040 11 940 7545 26 _ _ (89287 / 5000) (1785743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56951040 :
    ThetaLowerSegment 56951040 56967424 (5694227644829 / 100000) (2847918311349 / 50000) := by
  exact
    packedTile8192 56951040 56967424 11 901 7546 26 _ _ (1785769 / 100000) (446443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56967424 :
    ThetaLowerSegment 56967424 56983808 (2847918311349 / 50000) (1424349798987 / 25000) := by
  exact
    packedTile8192 56967424 56983808 11 875 7547 26 _ _ (892899 / 50000) (1785801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell56983808 :
    ThetaLowerSegment 56983808 57000192 (1424349798987 / 25000) (142477036101 / 2500) := by
  exact
    packedTile8192 56983808 57000192 11 942 7548 26 _ _ (892913 / 50000) (1785829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57000192 :
    ThetaLowerSegment 57000192 57016576 (142477036101 / 2500) (114014560047 / 2000) := by
  exact
    packedTile8192 57000192 57016576 11 922 7549 26 _ _ (357171 / 20000) (892929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57016576 :
    ThetaLowerSegment 57016576 57032960 (114014560047 / 2000) (2851179257221 / 50000) := by
  exact
    packedTile8192 57016576 57032960 11 913 7550 26 _ _ (446471 / 25000) (1785887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57032960 :
    ThetaLowerSegment 57032960 57049344 (2851179257221 / 50000) (570395511977 / 10000) := by
  exact
    packedTile8192 57032960 57049344 11 894 7552 26 _ _ (223239 / 12500) (357183 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57049344 :
    ThetaLowerSegment 57049344 57065728 (570395511977 / 10000) (2852802664627 / 50000) := by
  exact
    packedTile8192 57049344 57065728 11 924 7553 26 _ _ (1785941 / 100000) (223243 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57065728 :
    ThetaLowerSegment 57065728 57082112 (2852802664627 / 50000) (1426824160711 / 25000) := by
  exact
    packedTile8192 57065728 57082112 11 947 7554 26 _ _ (178597 / 10000) (1785973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57082112 :
    ThetaLowerSegment 57082112 57098496 (1426824160711 / 25000) (356807395621 / 6250) := by
  exact
    packedTile8192 57082112 57098496 11 908 7555 26 _ _ (1785999 / 100000) (893001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57098496 :
    ThetaLowerSegment 57098496 57114880 (356807395621 / 6250) (5710588265181 / 100000) := by
  exact
    packedTile8192 57098496 57114880 11 935 7556 26 _ _ (1786027 / 100000) (178603 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57114880 :
    ThetaLowerSegment 57114880 57131264 (5710588265181 / 100000) (1142442358017 / 20000) := by
  exact
    packedTile8192 57114880 57131264 11 909 7557 26 _ _ (223257 / 12500) (1786059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57131264 :
    ThetaLowerSegment 57131264 57147648 (1142442358017 / 20000) (1142770997657 / 20000) := by
  exact
    packedTile8192 57131264 57147648 11 920 7558 26 _ _ (357217 / 20000) (223261 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57147648 :
    ThetaLowerSegment 57147648 57164032 (1142770997657 / 20000) (714434374097 / 12500) := by
  exact
    packedTile8192 57147648 57164032 11 907 7559 26 _ _ (1786113 / 100000) (446529 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57164032 :
    ThetaLowerSegment 57164032 57180416 (714434374097 / 12500) (57171218157 / 1000) := by
  exact
    packedTile8192 57164032 57180416 11 922 7560 26 _ _ (893071 / 50000) (357229 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57180416 :
    ThetaLowerSegment 57180416 57196800 (57171218157 / 1000) (5718759734507 / 100000) := by
  exact
    packedTile8192 57180416 57196800 11 917 7561 26 _ _ (1786171 / 100000) (893087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57196800 :
    ThetaLowerSegment 57196800 57213184 (5718759734507 / 100000) (2860184549903 / 50000) := by
  exact
    packedTile8192 57196800 57213184 11 901 7562 26 _ _ (1786199 / 100000) (893101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57213184 :
    ThetaLowerSegment 57213184 57229568 (2860184549903 / 50000) (572203565053 / 10000) := by
  exact
    packedTile8192 57213184 57229568 11 933 7563 26 _ _ (446557 / 25000) (1786231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57229568 :
    ThetaLowerSegment 57229568 57245952 (572203565053 / 10000) (5723655785629 / 100000) := by
  exact
    packedTile8192 57229568 57245952 11 907 7565 26 _ _ (1786257 / 100000) (89313 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57245952 :
    ThetaLowerSegment 57245952 57262336 (5723655785629 / 100000) (715665745263 / 12500) := by
  exact
    packedTile8192 57245952 57262336 11 935 7566 26 _ _ (357257 / 20000) (111643 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57262336 :
    ThetaLowerSegment 57262336 57278720 (715665745263 / 12500) (1431736090647 / 25000) := by
  exact
    packedTile8192 57262336 57278720 11 906 7567 26 _ _ (893157 / 50000) (1786317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57278720 :
    ThetaLowerSegment 57278720 57295104 (1431736090647 / 25000) (22914644149 / 400) := by
  exact
    packedTile8192 57278720 57295104 11 961 7568 26 _ _ (893171 / 50000) (357269 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57295104 :
    ThetaLowerSegment 57295104 57311488 (22914644149 / 400) (573030449857 / 10000) := by
  exact
    packedTile8192 57295104 57311488 11 920 7569 26 _ _ (1786371 / 100000) (893187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57311488 :
    ThetaLowerSegment 57311488 57327872 (573030449857 / 10000) (573197835537 / 10000) := by
  exact
    packedTile8192 57311488 57327872 11 937 7570 26 _ _ (2233 / 125) (1786403 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57327872 :
    ThetaLowerSegment 57327872 57344256 (573197835537 / 10000) (2866818080277 / 50000) := by
  exact
    packedTile8192 57327872 57344256 11 928 7571 26 _ _ (446607 / 25000) (1786431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57344256 :
    ThetaLowerSegment 57344256 57360640 (2866818080277 / 50000) (5735299352021 / 100000) := by
  exact
    packedTile8192 57344256 57360640 11 931 7572 26 _ _ (1786457 / 100000) (89323 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57360640 :
    ThetaLowerSegment 57360640 57377024 (5735299352021 / 100000) (5736917907431 / 100000) := by
  exact
    packedTile8192 57360640 57377024 11 906 7573 26 _ _ (357297 / 20000) (223311 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57377024 :
    ThetaLowerSegment 57377024 57393408 (5736917907431 / 100000) (5738586511507 / 100000) := by
  exact
    packedTile8192 57377024 57393408 11 934 7574 26 _ _ (893257 / 50000) (1786517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57393408 :
    ThetaLowerSegment 57393408 57409792 (5738586511507 / 100000) (2870101666461 / 50000) := by
  exact
    packedTile8192 57393408 57409792 11 905 7575 26 _ _ (1786543 / 100000) (893273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57409792 :
    ThetaLowerSegment 57409792 57426176 (2870101666461 / 50000) (229671949633 / 4000) := by
  exact
    packedTile8192 57409792 57426176 11 893 7576 26 _ _ (1786571 / 100000) (893287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57426176 :
    ThetaLowerSegment 57426176 57442560 (229671949633 / 4000) (45947725109 / 800) := by
  exact
    packedTile8192 57426176 57442560 11 933 7578 26 _ _ (8933 / 500) (1786603 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57442560 :
    ThetaLowerSegment 57442560 57458944 (45947725109 / 800) (1149011147509 / 20000) := by
  exact
    packedTile8192 57442560 57458944 11 890 7579 26 _ _ (446657 / 25000) (1786631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57458944 :
    ThetaLowerSegment 57458944 57475328 (1149011147509 / 20000) (5746649435589 / 100000) := by
  exact
    packedTile8192 57458944 57475328 11 892 7580 26 _ _ (1786657 / 100000) (89333 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57475328 :
    ThetaLowerSegment 57475328 57491712 (5746649435589 / 100000) (5748282465679 / 100000) := by
  exact
    packedTile8192 57475328 57491712 11 914 7581 26 _ _ (357337 / 20000) (55834 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57491712 :
    ThetaLowerSegment 57491712 57508096 (5748282465679 / 100000) (5749953043269 / 100000) := by
  exact
    packedTile8192 57491712 57508096 11 935 7582 26 _ _ (893357 / 50000) (1786717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57508096 :
    ThetaLowerSegment 57508096 57524480 (5749953043269 / 100000) (5751589698941 / 100000) := by
  exact
    packedTile8192 57508096 57524480 11 916 7583 26 _ _ (893371 / 50000) (357349 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57524480 :
    ThetaLowerSegment 57524480 57540864 (5751589698941 / 100000) (5753265690139 / 100000) := by
  exact
    packedTile8192 57524480 57540864 11 938 7584 26 _ _ (1786771 / 100000) (893387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57540864 :
    ThetaLowerSegment 57540864 57557248 (5753265690139 / 100000) (5754895250827 / 100000) := by
  exact
    packedTile8192 57540864 57557248 11 912 7585 26 _ _ (1786799 / 100000) (893401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57557248 :
    ThetaLowerSegment 57557248 57573632 (5754895250827 / 100000) (5756533772103 / 100000) := by
  exact
    packedTile8192 57557248 57573632 11 917 7586 26 _ _ (446707 / 25000) (1786831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57573632 :
    ThetaLowerSegment 57573632 57590016 (5756533772103 / 100000) (5758170532199 / 100000) := by
  exact
    packedTile8192 57573632 57590016 11 916 7587 26 _ _ (223357 / 12500) (1786859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57590016 :
    ThetaLowerSegment 57590016 57606400 (5758170532199 / 100000) (5759789449103 / 100000) := by
  exact
    packedTile8192 57590016 57606400 11 906 7588 26 _ _ (446721 / 25000) (1786887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57606400 :
    ThetaLowerSegment 57606400 57622784 (5759789449103 / 100000) (144034450369 / 2500) := by
  exact
    packedTile8192 57606400 57622784 11 889 7589 26 _ _ (1786913 / 100000) (446729 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57622784 :
    ThetaLowerSegment 57622784 57639168 (144034450369 / 2500) (1440757287061 / 25000) := by
  exact
    packedTile8192 57622784 57639168 11 924 7590 26 _ _ (1786941 / 100000) (55842 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57639168 :
    ThetaLowerSegment 57639168 57655552 (1440757287061 / 25000) (180145477842 / 3125) := by
  exact
    packedTile8192 57639168 57655552 11 910 7592 26 _ _ (178697 / 10000) (1786973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57655552 :
    ThetaLowerSegment 57655552 57671936 (180145477842 / 3125) (2883170215029 / 50000) := by
  exact
    packedTile8192 57655552 57671936 11 943 7593 26 _ _ (893499 / 50000) (1787001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57671936 :
    ThetaLowerSegment 57671936 57688320 (2883170215029 / 50000) (5767918374899 / 100000) := by
  exact
    packedTile8192 57671936 57688320 11 883 7594 26 _ _ (1787027 / 100000) (178703 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57688320 :
    ThetaLowerSegment 57688320 57704704 (5767918374899 / 100000) (5769551743169 / 100000) := by
  exact
    packedTile8192 57688320 57704704 11 914 7595 26 _ _ (357411 / 20000) (893529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57704704 :
    ThetaLowerSegment 57704704 57721088 (5769551743169 / 100000) (144279762457 / 2500) := by
  exact
    packedTile8192 57704704 57721088 11 917 7596 26 _ _ (1787083 / 100000) (893543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57721088 :
    ThetaLowerSegment 57721088 57737472 (144279762457 / 2500) (721601649497 / 12500) := by
  exact
    packedTile8192 57721088 57737472 11 908 7597 26 _ _ (223389 / 12500) (357423 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57737472 :
    ThetaLowerSegment 57737472 57753856 (721601649497 / 12500) (721806277027 / 12500) := by
  exact
    packedTile8192 57737472 57753856 11 916 7598 26 _ _ (89357 / 5000) (1787143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57753856 :
    ThetaLowerSegment 57753856 57770240 (721806277027 / 12500) (1444014667079 / 25000) := by
  exact
    packedTile8192 57753856 57770240 11 900 7599 26 _ _ (1787169 / 100000) (446793 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57770240 :
    ThetaLowerSegment 57770240 57786624 (1444014667079 / 25000) (5777740420693 / 100000) := by
  exact
    packedTile8192 57770240 57786624 11 941 7600 26 _ _ (1787197 / 100000) (2234 / 125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57786624 :
    ThetaLowerSegment 57786624 57803008 (5777740420693 / 100000) (1444838571217 / 25000) := by
  exact
    packedTile8192 57786624 57803008 11 903 7601 26 _ _ (71489 / 4000) (446807 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57803008 :
    ThetaLowerSegment 57803008 57819392 (1444838571217 / 25000) (578096817523 / 10000) := by
  exact
    packedTile8192 57803008 57819392 11 903 7602 26 _ _ (893627 / 50000) (1787257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57819392 :
    ThetaLowerSegment 57819392 57835776 (578096817523 / 10000) (722824101821 / 12500) := by
  exact
    packedTile8192 57819392 57835776 11 909 7603 26 _ _ (893641 / 50000) (357457 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57835776 :
    ThetaLowerSegment 57835776 57852160 (722824101821 / 12500) (2892092653889 / 50000) := by
  exact
    packedTile8192 57835776 57852160 11 891 7604 26 _ _ (178731 / 10000) (1787313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57852160 :
    ThetaLowerSegment 57852160 57868544 (2892092653889 / 50000) (1157174153691 / 20000) := by
  exact
    packedTile8192 57852160 57868544 11 943 7606 26 _ _ (1787339 / 100000) (893671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57868544 :
    ThetaLowerSegment 57868544 57884928 (1157174153691 / 20000) (5787518720829 / 100000) := by
  exact
    packedTile8192 57868544 57884928 11 922 7607 26 _ _ (1787367 / 100000) (178737 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57884928 :
    ThetaLowerSegment 57884928 57901312 (5787518720829 / 100000) (361821913279 / 6250) := by
  exact
    packedTile8192 57884928 57901312 11 913 7608 26 _ _ (357479 / 20000) (893699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57901312 :
    ThetaLowerSegment 57901312 57917696 (361821913279 / 6250) (72384692261 / 1250) := by
  exact
    packedTile8192 57901312 57917696 11 909 7609 26 _ _ (55857 / 3125) (1787427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57917696 :
    ThetaLowerSegment 57917696 57934080 (72384692261 / 1250) (181012896466 / 3125) := by
  exact
    packedTile8192 57917696 57934080 11 916 7610 26 _ _ (446863 / 25000) (357491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57934080 :
    ThetaLowerSegment 57934080 57950464 (181012896466 / 3125) (362128349597 / 6250) := by
  exact
    packedTile8192 57934080 57950464 11 918 7611 26 _ _ (44687 / 2500) (1787483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57950464 :
    ThetaLowerSegment 57950464 57966848 (362128349597 / 6250) (724462709491 / 12500) := by
  exact
    packedTile8192 57950464 57966848 11 922 7612 26 _ _ (446877 / 25000) (1787511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57966848 :
    ThetaLowerSegment 57966848 57983232 (724462709491 / 12500) (5797308671691 / 100000) := by
  exact
    packedTile8192 57966848 57983232 11 899 7613 26 _ _ (1787537 / 100000) (89377 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57983232 :
    ThetaLowerSegment 57983232 57999616 (5797308671691 / 100000) (5798899604541 / 100000) := by
  exact
    packedTile8192 57983232 57999616 11 890 7614 26 _ _ (357513 / 20000) (111723 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell57999616 :
    ThetaLowerSegment 57999616 58016000 (5798899604541 / 100000) (5800544190101 / 100000) := by
  exact
    packedTile8192 57999616 58016000 11 920 7615 26 _ _ (1787593 / 100000) (446899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58016000 :
    ThetaLowerSegment 58016000 58032384 (5800544190101 / 100000) (5802199527147 / 100000) := by
  exact
    packedTile8192 58016000 58032384 11 926 7616 26 _ _ (1787621 / 100000) (223453 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58032384 :
    ThetaLowerSegment 58032384 58048768 (5802199527147 / 100000) (5803854891047 / 100000) := by
  exact
    packedTile8192 58032384 58048768 11 926 7617 26 _ _ (35753 / 2000) (1787653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58048768 :
    ThetaLowerSegment 58048768 58065152 (5803854891047 / 100000) (1161103843853 / 20000) := by
  exact
    packedTile8192 58048768 58065152 11 931 7618 26 _ _ (893839 / 50000) (1787681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58065152 :
    ThetaLowerSegment 58065152 58081536 (1161103843853 / 20000) (5807167484197 / 100000) := by
  exact
    packedTile8192 58065152 58081536 11 922 7620 26 _ _ (893853 / 50000) (1787709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58081536 :
    ThetaLowerSegment 58081536 58097920 (5807167484197 / 100000) (5808812199477 / 100000) := by
  exact
    packedTile8192 58081536 58097920 11 920 7621 26 _ _ (893867 / 50000) (1787737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58097920 :
    ThetaLowerSegment 58097920 58114304 (5808812199477 / 100000) (5810410459599 / 100000) := by
  exact
    packedTile8192 58097920 58114304 11 894 7622 26 _ _ (1787763 / 100000) (893883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58114304 :
    ThetaLowerSegment 58114304 58130688 (5810410459599 / 100000) (2906017780809 / 50000) := by
  exact
    packedTile8192 58114304 58130688 11 909 7623 26 _ _ (1787791 / 100000) (893897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58130688 :
    ThetaLowerSegment 58130688 58147072 (2906017780809 / 50000) (1162737143711 / 20000) := by
  exact
    packedTile8192 58130688 58147072 11 923 7624 26 _ _ (1787819 / 100000) (893911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58147072 :
    ThetaLowerSegment 58147072 58163456 (1162737143711 / 20000) (2907676889903 / 50000) := by
  exact
    packedTile8192 58147072 58163456 11 933 7625 26 _ _ (1787847 / 100000) (35757 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58163456 :
    ThetaLowerSegment 58163456 58179840 (2907676889903 / 50000) (5816953927931 / 100000) := by
  exact
    packedTile8192 58163456 58179840 11 895 7626 26 _ _ (14303 / 800) (893939 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58179840 :
    ThetaLowerSegment 58179840 58196224 (5816953927931 / 100000) (5818573768049 / 100000) := by
  exact
    packedTile8192 58179840 58196224 11 906 7627 26 _ _ (1787903 / 100000) (893953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58196224 :
    ThetaLowerSegment 58196224 58212608 (5818573768049 / 100000) (5820240120673 / 100000) := by
  exact
    packedTile8192 58196224 58212608 11 932 7628 26 _ _ (446983 / 25000) (357587 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58212608 :
    ThetaLowerSegment 58212608 58228992 (5820240120673 / 100000) (5821847496713 / 100000) := by
  exact
    packedTile8192 58212608 58228992 11 899 7629 26 _ _ (44699 / 2500) (1787963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58228992 :
    ThetaLowerSegment 58228992 58245376 (5821847496713 / 100000) (5823485293721 / 100000) := by
  exact
    packedTile8192 58228992 58245376 11 916 7630 26 _ _ (446997 / 25000) (1787991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58245376 :
    ThetaLowerSegment 58245376 58261760 (5823485293721 / 100000) (5825174968841 / 100000) := by
  exact
    packedTile8192 58245376 58261760 11 945 7631 26 _ _ (111751 / 6250) (1788019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58261760 :
    ThetaLowerSegment 58261760 58278144 (5825174968841 / 100000) (5826845001937 / 100000) := by
  exact
    packedTile8192 58261760 58278144 11 934 7632 26 _ _ (447011 / 25000) (1788047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58278144 :
    ThetaLowerSegment 58278144 58294528 (5826845001937 / 100000) (5828454266737 / 100000) := by
  exact
    packedTile8192 58278144 58294528 11 900 7634 26 _ _ (223509 / 12500) (71523 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58294528 :
    ThetaLowerSegment 58294528 58310912 (5828454266737 / 100000) (5830024218537 / 100000) := by
  exact
    packedTile8192 58294528 58310912 11 878 7635 26 _ _ (17881 / 1000) (1788103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58310912 :
    ThetaLowerSegment 58310912 58327296 (5830024218537 / 100000) (5831685389449 / 100000) := by
  exact
    packedTile8192 58310912 58327296 11 929 7636 26 _ _ (55879 / 3125) (1788131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58327296 :
    ThetaLowerSegment 58327296 58343680 (5831685389449 / 100000) (5833330493889 / 100000) := by
  exact
    packedTile8192 58327296 58343680 11 920 7637 26 _ _ (1788157 / 100000) (11176 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58343680 :
    ThetaLowerSegment 58343680 58360064 (5833330493889 / 100000) (2917510164357 / 50000) := by
  exact
    packedTile8192 58343680 58360064 11 945 7638 26 _ _ (357637 / 20000) (447047 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58360064 :
    ThetaLowerSegment 58360064 58376448 (2917510164357 / 50000) (1167328447581 / 20000) := by
  exact
    packedTile8192 58360064 58376448 11 907 7639 26 _ _ (1788213 / 100000) (223527 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58376448 :
    ThetaLowerSegment 58376448 58392832 (1167328447581 / 20000) (2919151756897 / 50000) := by
  exact
    packedTile8192 58376448 58392832 11 929 7640 26 _ _ (1788241 / 100000) (447061 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58392832 :
    ThetaLowerSegment 58392832 58409216 (2919151756897 / 50000) (5839907591087 / 100000) := by
  exact
    packedTile8192 58392832 58409216 11 897 7641 26 _ _ (1788269 / 100000) (111767 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58409216 :
    ThetaLowerSegment 58409216 58425600 (5839907591087 / 100000) (233660968463 / 4000) := by
  exact
    packedTile8192 58409216 58425600 11 904 7642 26 _ _ (1788297 / 100000) (17883 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58425600 :
    ThetaLowerSegment 58425600 58441984 (233660968463 / 4000) (58431569523 / 1000) := by
  exact
    packedTile8192 58425600 58441984 11 913 7643 26 _ _ (71533 / 4000) (223541 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58441984 :
    ThetaLowerSegment 58441984 58458368 (58431569523 / 1000) (5844800448707 / 100000) := by
  exact
    packedTile8192 58441984 58458368 11 919 7644 26 _ _ (1788353 / 100000) (447089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58458368 :
    ThetaLowerSegment 58458368 58474752 (5844800448707 / 100000) (5846402838083 / 100000) := by
  exact
    packedTile8192 58458368 58474752 11 896 7645 26 _ _ (1788381 / 100000) (55887 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58474752 :
    ThetaLowerSegment 58474752 58491136 (5846402838083 / 100000) (5848048174363 / 100000) := by
  exact
    packedTile8192 58474752 58491136 11 920 7646 26 _ _ (1788409 / 100000) (447103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58491136 :
    ThetaLowerSegment 58491136 58507520 (5848048174363 / 100000) (5849700690151 / 100000) := by
  exact
    packedTile8192 58491136 58507520 11 924 7647 26 _ _ (1788437 / 100000) (44711 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58507520 :
    ThetaLowerSegment 58507520 58523904 (5849700690151 / 100000) (5851410462691 / 100000) := by
  exact
    packedTile8192 58507520 58523904 11 956 7649 26 _ _ (357693 / 20000) (447117 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58523904 :
    ThetaLowerSegment 58523904 58540288 (5851410462691 / 100000) (2926498427991 / 50000) := by
  exact
    packedTile8192 58523904 58540288 11 887 7650 26 _ _ (1788493 / 100000) (111781 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58540288 :
    ThetaLowerSegment 58540288 58556672 (2926498427991 / 50000) (1463670410691 / 25000) := by
  exact
    packedTile8192 58540288 58556672 11 942 7651 26 _ _ (1788521 / 100000) (447131 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58556672 :
    ThetaLowerSegment 58556672 58573056 (1463670410691 / 25000) (2928168919569 / 50000) := by
  exact
    packedTile8192 58556672 58573056 11 926 7652 26 _ _ (1788549 / 100000) (223569 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58573056 :
    ThetaLowerSegment 58573056 58589440 (2928168919569 / 50000) (2928973779219 / 50000) := by
  exact
    packedTile8192 58573056 58589440 11 900 7653 26 _ _ (1788577 / 100000) (89429 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58589440 :
    ThetaLowerSegment 58589440 58605824 (2928973779219 / 50000) (5859609172483 / 100000) := by
  exact
    packedTile8192 58589440 58605824 11 929 7654 26 _ _ (357721 / 20000) (55894 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58605824 :
    ThetaLowerSegment 58605824 58622208 (5859609172483 / 100000) (2930633617637 / 50000) := by
  exact
    packedTile8192 58605824 58622208 11 927 7655 26 _ _ (1788633 / 100000) (447159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58622208 :
    ThetaLowerSegment 58622208 58638592 (2930633617637 / 50000) (5862936055987 / 100000) := by
  exact
    packedTile8192 58622208 58638592 11 933 7656 26 _ _ (1788661 / 100000) (223583 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58638592 :
    ThetaLowerSegment 58638592 58654976 (5862936055987 / 100000) (2932286353211 / 50000) := by
  exact
    packedTile8192 58638592 58654976 11 915 7657 26 _ _ (1788689 / 100000) (447173 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58654976 :
    ThetaLowerSegment 58654976 58671360 (2932286353211 / 50000) (5866141411231 / 100000) := by
  exact
    packedTile8192 58654976 58671360 11 877 7658 26 _ _ (1788717 / 100000) (22359 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58671360 :
    ThetaLowerSegment 58671360 58687744 (5866141411231 / 100000) (5867815676551 / 100000) := by
  exact
    packedTile8192 58671360 58687744 11 936 7659 26 _ _ (357749 / 20000) (447187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58687744 :
    ThetaLowerSegment 58687744 58704128 (5867815676551 / 100000) (1467351473937 / 25000) := by
  exact
    packedTile8192 58687744 58704128 11 889 7660 26 _ _ (1788773 / 100000) (223597 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58704128 :
    ThetaLowerSegment 58704128 58720512 (1467351473937 / 25000) (1467766475769 / 25000) := by
  exact
    packedTile8192 58704128 58720512 11 928 7661 26 _ _ (1788801 / 100000) (447201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58720512 :
    ThetaLowerSegment 58720512 58736896 (1467766475769 / 25000) (36704369394 / 625) := by
  exact
    packedTile8192 58720512 58736896 11 913 7662 26 _ _ (447207 / 25000) (1788831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58736896 :
    ThetaLowerSegment 58736896 58753280 (36704369394 / 625) (367150354479 / 6250) := by
  exact
    packedTile8192 58736896 58753280 11 954 7664 26 _ _ (223607 / 12500) (1788859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58753280 :
    ThetaLowerSegment 58753280 58769664 (367150354479 / 6250) (293799799477 / 5000) := by
  exact
    packedTile8192 58753280 58769664 11 889 7665 26 _ _ (447221 / 25000) (1788887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58769664 :
    ThetaLowerSegment 58769664 58786048 (293799799477 / 5000) (1469418050021 / 25000) := by
  exact
    packedTile8192 58769664 58786048 11 937 7666 26 _ _ (111807 / 6250) (357783 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58786048 :
    ThetaLowerSegment 58786048 58802432 (1469418050021 / 25000) (1469830400691 / 25000) := by
  exact
    packedTile8192 58786048 58802432 11 922 7667 26 _ _ (89447 / 5000) (1788943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58802432 :
    ThetaLowerSegment 58802432 58818816 (1469830400691 / 25000) (294052129499 / 5000) := by
  exact
    packedTile8192 58802432 58818816 11 962 7668 26 _ _ (223621 / 12500) (1788971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58818816 :
    ThetaLowerSegment 58818816 58835200 (294052129499 / 5000) (1470681956053 / 25000) := by
  exact
    packedTile8192 58818816 58835200 11 942 7669 26 _ _ (447249 / 25000) (1788999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58835200 :
    ThetaLowerSegment 58835200 58851584 (1470681956053 / 25000) (1471077777613 / 25000) := by
  exact
    packedTile8192 58835200 58851584 11 885 7670 26 _ _ (55907 / 3125) (1789027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58851584 :
    ThetaLowerSegment 58851584 58867968 (1471077777613 / 25000) (5885965982627 / 100000) := by
  exact
    packedTile8192 58851584 58867968 11 925 7671 26 _ _ (1789051 / 100000) (894527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58867968 :
    ThetaLowerSegment 58867968 58884352 (5885965982627 / 100000) (5887576153727 / 100000) := by
  exact
    packedTile8192 58867968 58884352 11 900 7672 26 _ _ (1789079 / 100000) (894541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58884352 :
    ThetaLowerSegment 58884352 58900736 (5887576153727 / 100000) (5889254336093 / 100000) := by
  exact
    packedTile8192 58884352 58900736 11 938 7673 26 _ _ (1789107 / 100000) (178911 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58900736 :
    ThetaLowerSegment 58900736 58917120 (5889254336093 / 100000) (5890825196623 / 100000) := by
  exact
    packedTile8192 58900736 58917120 11 878 7674 26 _ _ (357827 / 20000) (894569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58917120 :
    ThetaLowerSegment 58917120 58933504 (5890825196623 / 100000) (9428051293 / 160) := by
  exact
    packedTile8192 58917120 58933504 11 954 7675 26 _ _ (1789163 / 100000) (894583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58933504 :
    ThetaLowerSegment 58933504 58949888 (9428051293 / 160) (2947059535271 / 50000) := by
  exact
    packedTile8192 58933504 58949888 11 887 7676 26 _ _ (1789191 / 100000) (894597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58949888 :
    ThetaLowerSegment 58949888 58966272 (2947059535271 / 50000) (2947845001973 / 50000) := by
  exact
    packedTile8192 58949888 58966272 11 878 7677 26 _ _ (894609 / 50000) (1789221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58966272 :
    ThetaLowerSegment 58966272 58982656 (2947845001973 / 50000) (2948678790609 / 50000) := by
  exact
    packedTile8192 58966272 58982656 11 932 7678 26 _ _ (894623 / 50000) (1789249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58982656 :
    ThetaLowerSegment 58982656 58999040 (2948678790609 / 50000) (1474742429273 / 25000) := by
  exact
    packedTile8192 58982656 58999040 11 901 7680 26 _ _ (894637 / 50000) (1789277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell58999040 :
    ThetaLowerSegment 58999040 59015424 (1474742429273 / 25000) (590057829959 / 10000) := by
  exact
    packedTile8192 58999040 59015424 11 899 7681 26 _ _ (894651 / 50000) (357861 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59015424 :
    ThetaLowerSegment 59015424 59031808 (590057829959 / 10000) (1180453843099 / 20000) := by
  exact
    packedTile8192 59015424 59031808 11 945 7682 26 _ _ (1789329 / 100000) (447333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59031808 :
    ThetaLowerSegment 59031808 59048192 (1180453843099 / 20000) (5903954789789 / 100000) := by
  exact
    packedTile8192 59031808 59048192 11 942 7683 26 _ _ (1789357 / 100000) (22367 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59048192 :
    ThetaLowerSegment 59048192 59064576 (5903954789789 / 100000) (184547515677 / 3125) := by
  exact
    packedTile8192 59048192 59064576 11 875 7684 26 _ _ (357877 / 20000) (447347 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59064576 :
    ThetaLowerSegment 59064576 59080960 (184547515677 / 3125) (590713455219 / 10000) := by
  exact
    packedTile8192 59064576 59080960 11 902 7685 26 _ _ (1789413 / 100000) (223677 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59080960 :
    ThetaLowerSegment 59080960 59097344 (590713455219 / 10000) (590879873139 / 10000) := by
  exact
    packedTile8192 59080960 59097344 11 930 7686 26 _ _ (11184 / 625) (1789443 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59097344 :
    ThetaLowerSegment 59097344 59113728 (590879873139 / 10000) (2955203731561 / 50000) := by
  exact
    packedTile8192 59097344 59113728 11 899 7687 26 _ _ (447367 / 25000) (1789471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59113728 :
    ThetaLowerSegment 59113728 59130112 (2955203731561 / 50000) (591206811541 / 10000) := by
  exact
    packedTile8192 59113728 59130112 11 928 7688 26 _ _ (223687 / 12500) (1789499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59130112 :
    ThetaLowerSegment 59130112 59146496 (591206811541 / 10000) (2956827711599 / 50000) := by
  exact
    packedTile8192 59130112 59146496 11 887 7689 26 _ _ (447381 / 25000) (1789527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59146496 :
    ThetaLowerSegment 59146496 59162880 (2956827711599 / 50000) (5915285704159 / 100000) := by
  exact
    packedTile8192 59146496 59162880 11 911 7690 26 _ _ (1789551 / 100000) (894777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59162880 :
    ThetaLowerSegment 59162880 59179264 (5915285704159 / 100000) (5916964329261 / 100000) := by
  exact
    packedTile8192 59162880 59179264 11 938 7691 26 _ _ (1789579 / 100000) (894791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59179264 :
    ThetaLowerSegment 59179264 59195648 (5916964329261 / 100000) (591858750281 / 10000) := by
  exact
    packedTile8192 59179264 59195648 11 907 7692 26 _ _ (1789607 / 100000) (178961 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59195648 :
    ThetaLowerSegment 59195648 59212032 (591858750281 / 10000) (2960095507437 / 50000) := by
  exact
    packedTile8192 59195648 59212032 11 896 7693 26 _ _ (894817 / 50000) (1789637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59212032 :
    ThetaLowerSegment 59212032 59228416 (2960095507437 / 50000) (148045624407 / 2500) := by
  exact
    packedTile8192 59212032 59228416 11 913 7694 26 _ _ (894831 / 50000) (357933 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59228416 :
    ThetaLowerSegment 59228416 59244800 (148045624407 / 2500) (296170890019 / 5000) := by
  exact
    packedTile8192 59228416 59244800 11 890 7696 26 _ _ (178969 / 10000) (1789693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59244800 :
    ThetaLowerSegment 59244800 59261184 (296170890019 / 5000) (5925030335397 / 100000) := by
  exact
    packedTile8192 59244800 59261184 11 901 7697 26 _ _ (1789717 / 100000) (44743 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59261184 :
    ThetaLowerSegment 59261184 59277568 (5925030335397 / 100000) (1481672357253 / 25000) := by
  exact
    packedTile8192 59261184 59277568 11 927 7698 26 _ _ (357949 / 20000) (447437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59277568 :
    ThetaLowerSegment 59277568 59293952 (1481672357253 / 25000) (5928344969037 / 100000) := by
  exact
    packedTile8192 59277568 59293952 11 925 7699 26 _ _ (1789773 / 100000) (111861 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59293952 :
    ThetaLowerSegment 59293952 59310336 (5928344969037 / 100000) (5929975476837 / 100000) := by
  exact
    packedTile8192 59293952 59310336 11 911 7700 26 _ _ (8949 / 500) (1789803 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59310336 :
    ThetaLowerSegment 59310336 59326720 (5929975476837 / 100000) (5931607799973 / 100000) := by
  exact
    packedTile8192 59310336 59326720 11 912 7701 26 _ _ (447457 / 25000) (1789831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59326720 :
    ThetaLowerSegment 59326720 59343104 (5931607799973 / 100000) (5933304583461 / 100000) := by
  exact
    packedTile8192 59326720 59343104 11 948 7702 26 _ _ (55933 / 3125) (1789859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59343104 :
    ThetaLowerSegment 59343104 59359488 (5933304583461 / 100000) (118697701003 / 2000) := by
  exact
    packedTile8192 59343104 59359488 11 883 7703 26 _ _ (1789883 / 100000) (894943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59359488 :
    ThetaLowerSegment 59359488 59375872 (118697701003 / 2000) (5936497759961 / 100000) := by
  exact
    packedTile8192 59359488 59375872 11 901 7704 26 _ _ (1789911 / 100000) (894957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59375872 :
    ThetaLowerSegment 59375872 59392256 (5936497759961 / 100000) (5938108704161 / 100000) := by
  exact
    packedTile8192 59375872 59392256 11 900 7705 26 _ _ (894969 / 50000) (1789941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59392256 :
    ThetaLowerSegment 59392256 59408640 (5938108704161 / 100000) (5939716093629 / 100000) := by
  exact
    packedTile8192 59392256 59408640 11 898 7706 26 _ _ (894983 / 50000) (1789969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59408640 :
    ThetaLowerSegment 59408640 59425024 (5939716093629 / 100000) (1188282959587 / 20000) := by
  exact
    packedTile8192 59408640 59425024 11 949 7707 26 _ _ (894997 / 50000) (1789997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59425024 :
    ThetaLowerSegment 59425024 59441408 (1188282959587 / 20000) (297151738347 / 5000) := by
  exact
    packedTile8192 59425024 59441408 11 905 7708 26 _ _ (1790021 / 100000) (223753 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59441408 :
    ThetaLowerSegment 59441408 59457792 (297151738347 / 5000) (5944694142363 / 100000) := by
  exact
    packedTile8192 59441408 59457792 11 927 7709 26 _ _ (1790049 / 100000) (447513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59457792 :
    ThetaLowerSegment 59457792 59474176 (5944694142363 / 100000) (1189258178031 / 20000) := by
  exact
    packedTile8192 59457792 59474176 11 892 7710 26 _ _ (447519 / 25000) (1790079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59474176 :
    ThetaLowerSegment 59474176 59490560 (1189258178031 / 20000) (5947948526459 / 100000) := by
  exact
    packedTile8192 59474176 59490560 11 926 7711 26 _ _ (223763 / 12500) (1790107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59490560 :
    ThetaLowerSegment 59490560 59506944 (5947948526459 / 100000) (5949584706193 / 100000) := by
  exact
    packedTile8192 59490560 59506944 11 914 7713 26 _ _ (1790131 / 100000) (895067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59506944 :
    ThetaLowerSegment 59506944 59523328 (5949584706193 / 100000) (5951256714699 / 100000) := by
  exact
    packedTile8192 59506944 59523328 11 934 7714 26 _ _ (1790159 / 100000) (895081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59523328 :
    ThetaLowerSegment 59523328 59539712 (5951256714699 / 100000) (1190584675573 / 20000) := by
  exact
    packedTile8192 59523328 59539712 11 931 7715 26 _ _ (895093 / 50000) (1790189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59539712 :
    ThetaLowerSegment 59539712 59556096 (1190584675573 / 20000) (5954539941107 / 100000) := by
  exact
    packedTile8192 59539712 59556096 11 903 7716 26 _ _ (895107 / 50000) (1790217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59556096 :
    ThetaLowerSegment 59556096 59572480 (5954539941107 / 100000) (2978071103401 / 50000) := by
  exact
    packedTile8192 59556096 59572480 11 895 7717 26 _ _ (1790241 / 100000) (447561 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59572480 :
    ThetaLowerSegment 59572480 59588864 (2978071103401 / 50000) (5957776722399 / 100000) := by
  exact
    packedTile8192 59572480 59588864 11 913 7718 26 _ _ (1790269 / 100000) (55946 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59588864 :
    ThetaLowerSegment 59588864 59605248 (5957776722399 / 100000) (1191886907299 / 20000) := by
  exact
    packedTile8192 59588864 59605248 11 926 7719 26 _ _ (223787 / 12500) (1790299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59605248 :
    ThetaLowerSegment 59605248 59621632 (1191886907299 / 20000) (5961138924943 / 100000) := by
  exact
    packedTile8192 59605248 59621632 11 952 7720 26 _ _ (447581 / 25000) (1790327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59621632 :
    ThetaLowerSegment 59621632 59638016 (5961138924943 / 100000) (2981386757703 / 50000) := by
  exact
    packedTile8192 59621632 59638016 11 913 7721 26 _ _ (1790351 / 100000) (895177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59638016 :
    ThetaLowerSegment 59638016 59654400 (2981386757703 / 50000) (2982181685979 / 50000) := by
  exact
    packedTile8192 59638016 59654400 11 888 7722 26 _ _ (1790379 / 100000) (895191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59654400 :
    ThetaLowerSegment 59654400 59670784 (2982181685979 / 50000) (1491497712753 / 25000) := by
  exact
    packedTile8192 59654400 59670784 11 909 7723 26 _ _ (895203 / 50000) (1790409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59670784 :
    ThetaLowerSegment 59670784 59687168 (1491497712753 / 25000) (2983827082099 / 50000) := by
  exact
    packedTile8192 59670784 59687168 11 929 7724 26 _ _ (895217 / 50000) (1790437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59687168 :
    ThetaLowerSegment 59687168 59703552 (2983827082099 / 50000) (5969274531403 / 100000) := by
  exact
    packedTile8192 59687168 59703552 11 905 7725 26 _ _ (1790461 / 100000) (55952 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59703552 :
    ThetaLowerSegment 59703552 59719936 (5969274531403 / 100000) (2985452833441 / 50000) := by
  exact
    packedTile8192 59703552 59719936 11 911 7726 26 _ _ (1790489 / 100000) (447623 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59719936 :
    ThetaLowerSegment 59719936 59736320 (2985452833441 / 50000) (2986268413479 / 50000) := by
  exact
    packedTile8192 59719936 59736320 11 911 7727 26 _ _ (447629 / 25000) (1790519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59736320 :
    ThetaLowerSegment 59736320 59752704 (2986268413479 / 50000) (597416264091 / 10000) := by
  exact
    packedTile8192 59736320 59752704 11 908 7728 26 _ _ (111909 / 6250) (1790547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59752704 :
    ThetaLowerSegment 59752704 59769088 (597416264091 / 10000) (746977588707 / 12500) := by
  exact
    packedTile8192 59752704 59769088 11 926 7729 26 _ _ (1790571 / 100000) (895287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59769088 :
    ThetaLowerSegment 59769088 59785472 (746977588707 / 12500) (373593096687 / 6250) := by
  exact
    packedTile8192 59769088 59785472 11 932 7731 26 _ _ (895299 / 50000) (1790601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59785472 :
    ThetaLowerSegment 59785472 59801856 (373593096687 / 6250) (1494785126041 / 25000) := by
  exact
    packedTile8192 59785472 59801856 11 922 7732 26 _ _ (895313 / 50000) (1790629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59801856 :
    ThetaLowerSegment 59801856 59818240 (1494785126041 / 25000) (5980768207741 / 100000) := by
  exact
    packedTile8192 59801856 59818240 11 909 7733 26 _ _ (1790653 / 100000) (55958 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59818240 :
    ThetaLowerSegment 59818240 59834624 (5980768207741 / 100000) (2991208712471 / 50000) := by
  exact
    packedTile8192 59818240 59834624 11 921 7734 26 _ _ (1790681 / 100000) (447671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59834624 :
    ThetaLowerSegment 59834624 59851008 (2991208712471 / 50000) (598411143471 / 10000) := by
  exact
    packedTile8192 59834624 59851008 11 946 7735 26 _ _ (447677 / 25000) (1790711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59851008 :
    ThetaLowerSegment 59851008 59867392 (598411143471 / 10000) (239429568513 / 4000) := by
  exact
    packedTile8192 59851008 59867392 11 909 7736 26 _ _ (358147 / 20000) (895369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59867392 :
    ThetaLowerSegment 59867392 59883776 (239429568513 / 4000) (1197473761431 / 20000) := by
  exact
    packedTile8192 59867392 59883776 11 910 7737 26 _ _ (1790763 / 100000) (895383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59883776 :
    ThetaLowerSegment 59883776 59900160 (1197473761431 / 20000) (1197798252579 / 20000) := by
  exact
    packedTile8192 59883776 59900160 11 906 7738 26 _ _ (179079 / 10000) (1790793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59900160 :
    ThetaLowerSegment 59900160 59916544 (1197798252579 / 20000) (5990628069633 / 100000) := by
  exact
    packedTile8192 59900160 59916544 11 914 7739 26 _ _ (1790817 / 100000) (89541 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59916544 :
    ThetaLowerSegment 59916544 59932928 (5990628069633 / 100000) (5992229085063 / 100000) := by
  exact
    packedTile8192 59916544 59932928 11 894 7740 26 _ _ (358169 / 20000) (55964 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59932928 :
    ThetaLowerSegment 59932928 59949312 (5992229085063 / 100000) (5993858778583 / 100000) := by
  exact
    packedTile8192 59932928 59949312 11 910 7741 26 _ _ (223859 / 12500) (14327 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59949312 :
    ThetaLowerSegment 59949312 59965696 (5993858778583 / 100000) (5995509987461 / 100000) := by
  exact
    packedTile8192 59949312 59965696 11 922 7742 26 _ _ (1790899 / 100000) (895451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59965696 :
    ThetaLowerSegment 59965696 59982080 (5995509987461 / 100000) (2998542106147 / 50000) := by
  exact
    packedTile8192 59965696 59982080 11 879 7743 26 _ _ (1790927 / 100000) (179093 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59982080 :
    ThetaLowerSegment 59982080 59998464 (2998542106147 / 50000) (2999389227389 / 50000) := by
  exact
    packedTile8192 59982080 59998464 11 946 7744 26 _ _ (895477 / 50000) (1790957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell59998464 :
    ThetaLowerSegment 59998464 60014848 (2999389227389 / 50000) (1200084156871 / 20000) := by
  exact
    packedTile8192 59998464 60014848 11 917 7745 26 _ _ (1790981 / 100000) (223873 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60014848 :
    ThetaLowerSegment 60014848 60031232 (1200084156871 / 20000) (6002057766581 / 100000) := by
  exact
    packedTile8192 60014848 60031232 11 914 7746 26 _ _ (1791009 / 100000) (447753 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60031232 :
    ThetaLowerSegment 60031232 60047616 (6002057766581 / 100000) (6003684027269 / 100000) := by
  exact
    packedTile8192 60031232 60047616 11 908 7747 26 _ _ (447759 / 25000) (1791039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60047616 :
    ThetaLowerSegment 60047616 60064000 (6003684027269 / 100000) (1501329816947 / 25000) := by
  exact
    packedTile8192 60047616 60064000 11 913 7749 26 _ _ (1791063 / 100000) (895533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60064000 :
    ThetaLowerSegment 60064000 60080384 (1501329816947 / 25000) (6006965280417 / 100000) := by
  exact
    packedTile8192 60064000 60080384 11 919 7750 26 _ _ (1791091 / 100000) (895547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60080384 :
    ThetaLowerSegment 60080384 60096768 (6006965280417 / 100000) (6008562957673 / 100000) := by
  exact
    packedTile8192 60080384 60096768 11 892 7751 26 _ _ (895559 / 50000) (1791121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60096768 :
    ThetaLowerSegment 60096768 60113152 (6008562957673 / 100000) (1502546881547 / 25000) := by
  exact
    packedTile8192 60096768 60113152 11 907 7752 26 _ _ (358229 / 20000) (447787 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60113152 :
    ThetaLowerSegment 60113152 60129536 (1502546881547 / 25000) (1502953477591 / 25000) := by
  exact
    packedTile8192 60113152 60129536 11 908 7753 26 _ _ (447793 / 25000) (71647 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60129536 :
    ThetaLowerSegment 60129536 60145920 (1502953477591 / 25000) (1503357393191 / 25000) := by
  exact
    packedTile8192 60129536 60145920 11 902 7754 26 _ _ (2239 / 125) (1791203 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60145920 :
    ThetaLowerSegment 60145920 60162304 (1503357393191 / 25000) (3007562036753 / 50000) := by
  exact
    packedTile8192 60145920 60162304 11 946 7755 26 _ _ (1791227 / 100000) (179123 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60162304 :
    ThetaLowerSegment 60162304 60178688 (3007562036753 / 50000) (376047915839 / 6250) := by
  exact
    packedTile8192 60162304 60178688 11 917 7756 26 _ _ (895627 / 50000) (1791257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60178688 :
    ThetaLowerSegment 60178688 60195072 (376047915839 / 6250) (3009187611881 / 50000) := by
  exact
    packedTile8192 60178688 60195072 11 898 7757 26 _ _ (1791281 / 100000) (447821 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60195072 :
    ThetaLowerSegment 60195072 60211456 (3009187611881 / 50000) (1504999537429 / 25000) := by
  exact
    packedTile8192 60195072 60211456 11 906 7758 26 _ _ (1791309 / 100000) (111957 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60211456 :
    ThetaLowerSegment 60211456 60227840 (1504999537429 / 25000) (1505427666733 / 25000) := by
  exact
    packedTile8192 60211456 60227840 11 956 7759 26 _ _ (223917 / 12500) (1791339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60227840 :
    ThetaLowerSegment 60227840 60244224 (1505427666733 / 25000) (60233873827 / 1000) := by
  exact
    packedTile8192 60227840 60244224 11 936 7760 26 _ _ (1791363 / 100000) (895683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60244224 :
    ThetaLowerSegment 60244224 60260608 (60233873827 / 1000) (602500142509 / 10000) := by
  exact
    packedTile8192 60244224 60260608 11 901 7761 26 _ _ (179139 / 10000) (1791393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60260608 :
    ThetaLowerSegment 60260608 60276992 (602500142509 / 10000) (1506645363721 / 25000) := by
  exact
    packedTile8192 60260608 60276992 11 882 7762 26 _ _ (1791417 / 100000) (89571 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60276992 :
    ThetaLowerSegment 60276992 60293376 (1506645363721 / 25000) (6028209878389 / 100000) := by
  exact
    packedTile8192 60276992 60293376 11 909 7763 26 _ _ (358289 / 20000) (223931 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60293376 :
    ThetaLowerSegment 60293376 60309760 (6028209878389 / 100000) (1205976264353 / 20000) := by
  exact
    packedTile8192 60293376 60309760 11 933 7764 26 _ _ (111967 / 6250) (71659 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60309760 :
    ThetaLowerSegment 60309760 60326144 (1205976264353 / 20000) (3015774603667 / 50000) := by
  exact
    packedTile8192 60309760 60326144 11 931 7765 26 _ _ (1791499 / 100000) (895751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60326144 :
    ThetaLowerSegment 60326144 60342528 (3015774603667 / 50000) (301659960139 / 5000) := by
  exact
    packedTile8192 60326144 60342528 11 921 7766 26 _ _ (895763 / 50000) (1791529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60342528 :
    ThetaLowerSegment 60342528 60358912 (301659960139 / 5000) (3017411174899 / 50000) := by
  exact
    packedTile8192 60342528 60358912 11 906 7768 26 _ _ (1791553 / 100000) (447889 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60358912 :
    ThetaLowerSegment 60358912 60375296 (3017411174899 / 50000) (3018252321709 / 50000) := by
  exact
    packedTile8192 60358912 60375296 11 939 7769 26 _ _ (89579 / 5000) (1791583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60375296 :
    ThetaLowerSegment 60375296 60391680 (3018252321709 / 50000) (3019063920133 / 50000) := by
  exact
    packedTile8192 60375296 60391680 11 906 7770 26 _ _ (223951 / 12500) (1791611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60391680 :
    ThetaLowerSegment 60391680 60408064 (3019063920133 / 50000) (1509957473379 / 25000) := by
  exact
    packedTile8192 60391680 60408064 11 950 7771 26 _ _ (358327 / 20000) (895819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60408064 :
    ThetaLowerSegment 60408064 60424448 (1509957473379 / 25000) (1510362388991 / 25000) := by
  exact
    packedTile8192 60408064 60424448 11 904 7772 26 _ _ (895831 / 50000) (358333 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60424448 :
    ThetaLowerSegment 60424448 60440832 (1510362388991 / 25000) (1208619223631 / 20000) := by
  exact
    packedTile8192 60424448 60440832 11 919 7773 26 _ _ (1791689 / 100000) (447923 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60440832 :
    ThetaLowerSegment 60440832 60457216 (1208619223631 / 20000) (6044660286223 / 100000) := by
  exact
    packedTile8192 60440832 60457216 11 873 7774 26 _ _ (447929 / 25000) (1791719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60457216 :
    ThetaLowerSegment 60457216 60473600 (6044660286223 / 100000) (6046308689783 / 100000) := by
  exact
    packedTile8192 60457216 60473600 11 920 7775 26 _ _ (1791743 / 100000) (895873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60473600 :
    ThetaLowerSegment 60473600 60489984 (6046308689783 / 100000) (6047973244113 / 100000) := by
  exact
    packedTile8192 60473600 60489984 11 929 7776 26 _ _ (179177 / 10000) (1791773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60489984 :
    ThetaLowerSegment 60489984 60506368 (6047973244113 / 100000) (3024808160981 / 50000) := by
  exact
    packedTile8192 60489984 60506368 11 917 7777 26 _ _ (1791797 / 100000) (8959 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60506368 :
    ThetaLowerSegment 60506368 60522752 (3024808160981 / 50000) (3025601043101 / 50000) := by
  exact
    packedTile8192 60506368 60522752 11 885 7778 26 _ _ (111989 / 6250) (1791827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60522752 :
    ThetaLowerSegment 60522752 60539136 (3025601043101 / 50000) (6052812960251 / 100000) := by
  exact
    packedTile8192 60522752 60539136 11 899 7779 26 _ _ (1791851 / 100000) (895927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60539136 :
    ThetaLowerSegment 60539136 60555520 (6052812960251 / 100000) (605446328081 / 10000) := by
  exact
    packedTile8192 60539136 60555520 11 921 7780 26 _ _ (1791879 / 100000) (895941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60555520 :
    ThetaLowerSegment 60555520 60571904 (605446328081 / 10000) (1514023030841 / 25000) := by
  exact
    packedTile8192 60555520 60571904 11 909 7781 26 _ _ (895953 / 50000) (1791909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60571904 :
    ThetaLowerSegment 60571904 60588288 (1514023030841 / 25000) (6057738909791 / 100000) := by
  exact
    packedTile8192 60571904 60588288 11 919 7782 26 _ _ (1791933 / 100000) (55998 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60588288 :
    ThetaLowerSegment 60588288 60604672 (6057738909791 / 100000) (6059349881831 / 100000) := by
  exact
    packedTile8192 60588288 60604672 11 899 7783 26 _ _ (44799 / 2500) (1791963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60604672 :
    ThetaLowerSegment 60604672 60621056 (6059349881831 / 100000) (1515263515367 / 25000) := by
  exact
    packedTile8192 60604672 60621056 11 951 7784 26 _ _ (1791987 / 100000) (179199 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60621056 :
    ThetaLowerSegment 60621056 60637440 (1515263515367 / 25000) (189460691833 / 3125) := by
  exact
    packedTile8192 60621056 60637440 11 942 7785 26 _ _ (896007 / 50000) (1792017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60637440 :
    ThetaLowerSegment 60637440 60653824 (189460691833 / 3125) (6064399776581 / 100000) := by
  exact
    packedTile8192 60637440 60653824 11 925 7787 26 _ _ (1792041 / 100000) (448011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60653824 :
    ThetaLowerSegment 60653824 60670208 (6064399776581 / 100000) (6066034142597 / 100000) := by
  exact
    packedTile8192 60653824 60670208 11 912 7788 26 _ _ (448017 / 25000) (1792071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60670208 :
    ThetaLowerSegment 60670208 60686592 (6066034142597 / 100000) (3033836954761 / 50000) := by
  exact
    packedTile8192 60670208 60686592 11 915 7789 26 _ _ (358419 / 20000) (896049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60686592 :
    ThetaLowerSegment 60686592 60702976 (3033836954761 / 50000) (3034641617539 / 50000) := by
  exact
    packedTile8192 60686592 60702976 11 898 7790 26 _ _ (896061 / 50000) (14337 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60702976 :
    ThetaLowerSegment 60702976 60719360 (3034641617539 / 50000) (3035451668887 / 50000) := by
  exact
    packedTile8192 60702976 60719360 11 904 7791 26 _ _ (1792149 / 100000) (224019 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60719360 :
    ThetaLowerSegment 60719360 60735744 (3035451668887 / 50000) (3036278758111 / 50000) := by
  exact
    packedTile8192 60719360 60735744 11 923 7792 26 _ _ (112011 / 6250) (1792179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60735744 :
    ThetaLowerSegment 60735744 60752128 (3036278758111 / 50000) (1518556066253 / 25000) := by
  exact
    packedTile8192 60735744 60752128 11 930 7793 26 _ _ (1792203 / 100000) (896103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60752128 :
    ThetaLowerSegment 60752128 60768512 (1518556066253 / 25000) (759490860439 / 12500) := by
  exact
    packedTile8192 60752128 60768512 11 950 7794 26 _ _ (179223 / 10000) (1792233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60768512 :
    ThetaLowerSegment 60768512 60784896 (759490860439 / 12500) (6077545291583 / 100000) := by
  exact
    packedTile8192 60768512 60784896 11 903 7795 26 _ _ (1792257 / 100000) (89613 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60784896 :
    ThetaLowerSegment 60784896 60801280 (6077545291583 / 100000) (1215829160239 / 20000) := by
  exact
    packedTile8192 60784896 60801280 11 893 7796 26 _ _ (448071 / 25000) (1792287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60801280 :
    ThetaLowerSegment 60801280 60817664 (1215829160239 / 20000) (6080801896559 / 100000) := by
  exact
    packedTile8192 60801280 60817664 11 924 7797 26 _ _ (1792311 / 100000) (896157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60817664 :
    ThetaLowerSegment 60817664 60834048 (6080801896559 / 100000) (6082502825321 / 100000) := by
  exact
    packedTile8192 60817664 60834048 11 949 7798 26 _ _ (896169 / 50000) (1792341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60834048 :
    ThetaLowerSegment 60834048 60850432 (6082502825321 / 100000) (6084198402611 / 100000) := by
  exact
    packedTile8192 60834048 60850432 11 946 7799 26 _ _ (358473 / 20000) (112023 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60850432 :
    ThetaLowerSegment 60850432 60866816 (6084198402611 / 100000) (3042906673451 / 50000) := by
  exact
    packedTile8192 60850432 60866816 11 901 7800 26 _ _ (1792391 / 100000) (896197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60866816 :
    ThetaLowerSegment 60866816 60883200 (3042906673451 / 50000) (380465165929 / 6250) := by
  exact
    packedTile8192 60866816 60883200 11 909 7801 26 _ _ (896209 / 50000) (1792421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60883200 :
    ThetaLowerSegment 60883200 60899584 (380465165929 / 6250) (3044544059687 / 50000) := by
  exact
    packedTile8192 60883200 60899584 11 918 7802 26 _ _ (358489 / 20000) (56014 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60899584 :
    ThetaLowerSegment 60899584 60915968 (3044544059687 / 50000) (3045346190907 / 50000) := by
  exact
    packedTile8192 60899584 60915968 11 895 7803 26 _ _ (224059 / 12500) (71699 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60915968 :
    ThetaLowerSegment 60915968 60932352 (3045346190907 / 50000) (1523089851471 / 25000) := by
  exact
    packedTile8192 60915968 60932352 11 930 7804 26 _ _ (1792499 / 100000) (896251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60932352 :
    ThetaLowerSegment 60932352 60948736 (1523089851471 / 25000) (3046976480749 / 50000) := by
  exact
    packedTile8192 60932352 60948736 11 889 7805 26 _ _ (896263 / 50000) (1792529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60948736 :
    ThetaLowerSegment 60948736 60965120 (3046976480749 / 50000) (3047813603 / 50) := by
  exact
    packedTile8192 60948736 60965120 11 934 7806 26 _ _ (1792553 / 100000) (448139 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60965120 :
    ThetaLowerSegment 60965120 60981504 (3047813603 / 50) (38107842929 / 625) := by
  exact
    packedTile8192 60965120 60981504 11 908 7808 26 _ _ (89629 / 5000) (1792583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60981504 :
    ThetaLowerSegment 60981504 60997888 (38107842929 / 625) (6098916615329 / 100000) := by
  exact
    packedTile8192 60981504 60997888 11 927 7809 26 _ _ (1792607 / 100000) (179261 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell60997888 :
    ThetaLowerSegment 60997888 61014272 (6098916615329 / 100000) (190642626408 / 3125) := by
  exact
    packedTile8192 60997888 61014272 11 919 7810 26 _ _ (1792633 / 100000) (448159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61014272 :
    ThetaLowerSegment 61014272 61030656 (190642626408 / 3125) (762781591347 / 12500) := by
  exact
    packedTile8192 61014272 61030656 11 942 7811 26 _ _ (89633 / 5000) (1792663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61030656 :
    ThetaLowerSegment 61030656 61047040 (762781591347 / 12500) (6103839258771 / 100000) := by
  exact
    packedTile8192 61030656 61047040 11 885 7812 26 _ _ (1792687 / 100000) (179269 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61047040 :
    ThetaLowerSegment 61047040 61063424 (6103839258771 / 100000) (6105459872227 / 100000) := by
  exact
    packedTile8192 61047040 61063424 11 904 7813 26 _ _ (896357 / 50000) (1792717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61063424 :
    ThetaLowerSegment 61063424 61079808 (6105459872227 / 100000) (6107098437501 / 100000) := by
  exact
    packedTile8192 61063424 61079808 11 914 7814 26 _ _ (1792741 / 100000) (224093 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61079808 :
    ThetaLowerSegment 61079808 61096192 (6107098437501 / 100000) (6108740612989 / 100000) := by
  exact
    packedTile8192 61079808 61096192 11 916 7815 26 _ _ (56024 / 3125) (1792771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61096192 :
    ThetaLowerSegment 61096192 61112576 (6108740612989 / 100000) (6110318272589 / 100000) := by
  exact
    packedTile8192 61096192 61112576 11 880 7816 26 _ _ (358559 / 20000) (896399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61112576 :
    ThetaLowerSegment 61112576 61128960 (6110318272589 / 100000) (1222395684967 / 20000) := by
  exact
    packedTile8192 61112576 61128960 11 926 7817 26 _ _ (1792821 / 100000) (224103 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61128960 :
    ThetaLowerSegment 61128960 61145344 (1222395684967 / 20000) (6113599159427 / 100000) := by
  exact
    packedTile8192 61128960 61145344 11 904 7818 26 _ _ (112053 / 6250) (1792851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61145344 :
    ThetaLowerSegment 61145344 61161728 (6113599159427 / 100000) (6115194818177 / 100000) := by
  exact
    packedTile8192 61145344 61161728 11 890 7819 26 _ _ (14343 / 800) (896439 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61161728 :
    ThetaLowerSegment 61161728 61178112 (6115194818177 / 100000) (6116795879663 / 100000) := by
  exact
    packedTile8192 61161728 61178112 11 893 7820 26 _ _ (896451 / 50000) (358581 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61178112 :
    ThetaLowerSegment 61178112 61194496 (6116795879663 / 100000) (1223684771839 / 20000) := by
  exact
    packedTile8192 61178112 61194496 11 908 7821 26 _ _ (1792929 / 100000) (448233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61194496 :
    ThetaLowerSegment 61194496 61210880 (1223684771839 / 20000) (1224012524013 / 20000) := by
  exact
    packedTile8192 61194496 61210880 11 914 7822 26 _ _ (358591 / 20000) (896479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61210880 :
    ThetaLowerSegment 61210880 61227264 (1224012524013 / 20000) (6121722921397 / 100000) := by
  exact
    packedTile8192 61210880 61227264 11 926 7823 26 _ _ (896491 / 50000) (358597 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61227264 :
    ThetaLowerSegment 61227264 61243648 (6121722921397 / 100000) (76541864757 / 1250) := by
  exact
    packedTile8192 61227264 61243648 11 907 7824 26 _ _ (1793009 / 100000) (448253 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61243648 :
    ThetaLowerSegment 61243648 61260032 (76541864757 / 1250) (12249979617 / 200) := by
  exact
    packedTile8192 61243648 61260032 11 915 7825 26 _ _ (448259 / 25000) (1793039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61260032 :
    ThetaLowerSegment 61260032 61276416 (12249979617 / 200) (1531661649447 / 25000) := by
  exact
    packedTile8192 61260032 61276416 11 924 7826 26 _ _ (896531 / 50000) (358613 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61276416 :
    ThetaLowerSegment 61276416 61292800 (1531661649447 / 25000) (191508136809 / 3125) := by
  exact
    packedTile8192 61276416 61292800 11 900 7827 26 _ _ (1793089 / 100000) (448273 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61292800 :
    ThetaLowerSegment 61292800 61309184 (191508136809 / 3125) (766229341717 / 12500) := by
  exact
    packedTile8192 61292800 61309184 11 878 7828 26 _ _ (448279 / 25000) (1793119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61309184 :
    ThetaLowerSegment 61309184 61325568 (766229341717 / 12500) (6131446769293 / 100000) := by
  exact
    packedTile8192 61309184 61325568 11 899 7830 26 _ _ (1793143 / 100000) (896573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61325568 :
    ThetaLowerSegment 61325568 61341952 (6131446769293 / 100000) (3066527620943 / 50000) := by
  exact
    packedTile8192 61325568 61341952 11 897 7831 26 _ _ (1793169 / 100000) (448293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61341952 :
    ThetaLowerSegment 61341952 61358336 (3066527620943 / 50000) (3067346214917 / 50000) := by
  exact
    packedTile8192 61341952 61358336 11 913 7832 26 _ _ (448299 / 25000) (1793199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61358336 :
    ThetaLowerSegment 61358336 61374720 (3067346214917 / 50000) (767041429457 / 12500) := by
  exact
    packedTile8192 61358336 61374720 11 914 7833 26 _ _ (1793223 / 100000) (896613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61374720 :
    ThetaLowerSegment 61374720 61391104 (767041429457 / 12500) (767249446341 / 12500) := by
  exact
    packedTile8192 61374720 61391104 11 928 7834 26 _ _ (1793249 / 100000) (448313 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61391104 :
    ThetaLowerSegment 61391104 61407488 (767249446341 / 12500) (1534900138187 / 25000) := by
  exact
    packedTile8192 61391104 61407488 11 895 7835 26 _ _ (448319 / 25000) (1793279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61407488 :
    ThetaLowerSegment 61407488 61423872 (1534900138187 / 25000) (6141219905357 / 100000) := by
  exact
    packedTile8192 61407488 61423872 11 903 7836 26 _ _ (1793303 / 100000) (896653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61423872 :
    ThetaLowerSegment 61423872 61440256 (6141219905357 / 100000) (122857287761 / 2000) := by
  exact
    packedTile8192 61423872 61440256 11 917 7837 26 _ _ (1793329 / 100000) (448333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61440256 :
    ThetaLowerSegment 61440256 61456640 (122857287761 / 2000) (3072259827819 / 50000) := by
  exact
    packedTile8192 61440256 61456640 11 923 7838 26 _ _ (448339 / 25000) (1793359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61456640 :
    ThetaLowerSegment 61456640 61473024 (3072259827819 / 50000) (1536546875457 / 25000) := by
  exact
    packedTile8192 61456640 61473024 11 930 7839 26 _ _ (1793383 / 100000) (896693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61473024 :
    ThetaLowerSegment 61473024 61489408 (1536546875457 / 25000) (6147867926061 / 100000) := by
  exact
    packedTile8192 61473024 61489408 11 937 7840 26 _ _ (1793409 / 100000) (448353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61489408 :
    ThetaLowerSegment 61489408 61505792 (6147867926061 / 100000) (6149473051281 / 100000) := by
  exact
    packedTile8192 61489408 61505792 11 895 7841 26 _ _ (448359 / 25000) (1793439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61505792 :
    ThetaLowerSegment 61505792 61522176 (6149473051281 / 100000) (6151094341833 / 100000) := by
  exact
    packedTile8192 61505792 61522176 11 904 7842 26 _ _ (1793463 / 100000) (896733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61522176 :
    ThetaLowerSegment 61522176 61538560 (6151094341833 / 100000) (7690892328 / 125) := by
  exact
    packedTile8192 61522176 61538560 11 903 7843 26 _ _ (1793489 / 100000) (448373 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61538560 :
    ThetaLowerSegment 61538560 61554944 (7690892328 / 125) (192322975027 / 3125) := by
  exact
    packedTile8192 61538560 61554944 11 904 7844 26 _ _ (448379 / 25000) (1793519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61554944 :
    ThetaLowerSegment 61554944 61571328 (192322975027 / 3125) (6155969118537 / 100000) := by
  exact
    packedTile8192 61554944 61571328 11 911 7845 26 _ _ (1793543 / 100000) (896773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61571328 :
    ThetaLowerSegment 61571328 61587712 (6155969118537 / 100000) (615757794993 / 10000) := by
  exact
    packedTile8192 61571328 61587712 11 897 7846 26 _ _ (1793569 / 100000) (448393 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61587712 :
    ThetaLowerSegment 61587712 61604096 (615757794993 / 10000) (615919218633 / 10000) := by
  exact
    packedTile8192 61587712 61604096 11 900 7847 26 _ _ (448399 / 25000) (1793599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61604096 :
    ThetaLowerSegment 61604096 61620480 (615919218633 / 10000) (61608692229 / 1000) := by
  exact
    packedTile8192 61604096 61620480 11 935 7848 26 _ _ (896811 / 50000) (14349 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61620480 :
    ThetaLowerSegment 61620480 61636864 (61608692229 / 1000) (3081247134447 / 50000) := by
  exact
    packedTile8192 61620480 61636864 11 906 7849 26 _ _ (1793649 / 100000) (448413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61636864 :
    ThetaLowerSegment 61636864 61653248 (3081247134447 / 50000) (3082047113943 / 50000) := by
  exact
    packedTile8192 61636864 61653248 11 892 7850 26 _ _ (448419 / 25000) (1793679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61653248 :
    ThetaLowerSegment 61653248 61669632 (3082047113943 / 50000) (1541441937963 / 25000) := by
  exact
    packedTile8192 61653248 61669632 11 933 7851 26 _ _ (896851 / 50000) (358741 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61669632 :
    ThetaLowerSegment 61669632 61686016 (1541441937963 / 25000) (61674036327 / 1000) := by
  exact
    packedTile8192 61669632 61686016 11 912 7853 26 _ _ (1793729 / 100000) (448433 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61686016 :
    ThetaLowerSegment 61686016 61702400 (61674036327 / 1000) (308451976863 / 5000) := by
  exact
    packedTile8192 61686016 61702400 11 912 7854 26 _ _ (358751 / 20000) (896879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61702400 :
    ThetaLowerSegment 61702400 61718784 (308451976863 / 5000) (3085318898511 / 50000) := by
  exact
    packedTile8192 61702400 61718784 11 891 7855 26 _ _ (896891 / 50000) (358757 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61718784 :
    ThetaLowerSegment 61718784 61735168 (3085318898511 / 50000) (3086156606847 / 50000) := by
  exact
    packedTile8192 61718784 61735168 11 934 7856 26 _ _ (112113 / 6250) (1793811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61735168 :
    ThetaLowerSegment 61735168 61751552 (3086156606847 / 50000) (6173958160389 / 100000) := by
  exact
    packedTile8192 61735168 61751552 11 917 7857 26 _ _ (358767 / 20000) (896919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61751552 :
    ThetaLowerSegment 61751552 61767936 (6173958160389 / 100000) (1543896298079 / 25000) := by
  exact
    packedTile8192 61751552 61767936 11 907 7858 26 _ _ (1793861 / 100000) (224233 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61767936 :
    ThetaLowerSegment 61767936 61784320 (1543896298079 / 25000) (1544298577463 / 25000) := by
  exact
    packedTile8192 61767936 61784320 11 897 7859 26 _ _ (56059 / 3125) (1793891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61784320 :
    ThetaLowerSegment 61784320 61800704 (1544298577463 / 25000) (3089409798421 / 50000) := by
  exact
    packedTile8192 61784320 61800704 11 906 7860 26 _ _ (358783 / 20000) (896959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61800704 :
    ThetaLowerSegment 61800704 61817088 (3089409798421 / 50000) (154511660867 / 2500) := by
  exact
    packedTile8192 61800704 61817088 11 918 7861 26 _ _ (1793941 / 100000) (224243 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61817088 :
    ThetaLowerSegment 61817088 61833472 (154511660867 / 2500) (772765507639 / 12500) := by
  exact
    packedTile8192 61817088 61833472 11 924 7862 26 _ _ (112123 / 6250) (1793971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61833472 :
    ThetaLowerSegment 61833472 61849856 (772765507639 / 12500) (309188906179 / 5000) := by
  exact
    packedTile8192 61833472 61849856 11 922 7863 26 _ _ (896997 / 50000) (1793997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61849856 :
    ThetaLowerSegment 61849856 61866240 (309188906179 / 5000) (6185426828879 / 100000) := by
  exact
    packedTile8192 61849856 61866240 11 919 7864 26 _ _ (1794021 / 100000) (224253 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61866240 :
    ThetaLowerSegment 61866240 61882624 (6185426828879 / 100000) (309354136713 / 5000) := by
  exact
    packedTile8192 61866240 61882624 11 923 7865 26 _ _ (1794047 / 100000) (35881 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61882624 :
    ThetaLowerSegment 61882624 61899008 (309354136713 / 5000) (6188681253303 / 100000) := by
  exact
    packedTile8192 61882624 61899008 11 891 7866 26 _ _ (1794073 / 100000) (448519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61899008 :
    ThetaLowerSegment 61899008 61915392 (6188681253303 / 100000) (6190283384603 / 100000) := by
  exact
    packedTile8192 61899008 61915392 11 893 7867 26 _ _ (17941 / 1000) (1794103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61915392 :
    ThetaLowerSegment 61915392 61931776 (6190283384603 / 100000) (6191980627799 / 100000) := by
  exact
    packedTile8192 61915392 61931776 11 946 7868 26 _ _ (897063 / 50000) (1794129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61931776 :
    ThetaLowerSegment 61931776 61948160 (6191980627799 / 100000) (6193627660253 / 100000) := by
  exact
    packedTile8192 61931776 61948160 11 918 7869 26 _ _ (1794153 / 100000) (448539 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61948160 :
    ThetaLowerSegment 61948160 61964544 (6193627660253 / 100000) (6195253186427 / 100000) := by
  exact
    packedTile8192 61948160 61964544 11 906 7870 26 _ _ (1794179 / 100000) (897091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61964544 :
    ThetaLowerSegment 61964544 61980928 (6195253186427 / 100000) (6196859000797 / 100000) := by
  exact
    packedTile8192 61964544 61980928 11 895 7871 26 _ _ (897103 / 50000) (1794209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61980928 :
    ThetaLowerSegment 61980928 61997312 (6196859000797 / 100000) (6198540196181 / 100000) := by
  exact
    packedTile8192 61980928 61997312 11 937 7872 26 _ _ (224279 / 12500) (358847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell61997312 :
    ThetaLowerSegment 61997312 62013696 (6198540196181 / 100000) (1240033158967 / 20000) := by
  exact
    packedTile8192 61997312 62013696 11 906 7873 26 _ _ (1794259 / 100000) (897131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62013696 :
    ThetaLowerSegment 62013696 62030080 (1240033158967 / 20000) (1240370484547 / 20000) := by
  exact
    packedTile8192 62013696 62030080 11 940 7874 26 _ _ (358857 / 20000) (112143 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62030080 :
    ThetaLowerSegment 62030080 62046464 (1240370484547 / 20000) (6203427827793 / 100000) := by
  exact
    packedTile8192 62030080 62046464 11 878 7875 26 _ _ (1794311 / 100000) (897157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62046464 :
    ThetaLowerSegment 62046464 62062848 (6203427827793 / 100000) (6205069647063 / 100000) := by
  exact
    packedTile8192 62046464 62062848 11 915 7876 26 _ _ (897169 / 50000) (1794341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62062848 :
    ThetaLowerSegment 62062848 62079232 (6205069647063 / 100000) (6206738405583 / 100000) := by
  exact
    packedTile8192 62062848 62079232 11 930 7877 26 _ _ (448591 / 25000) (1794367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62079232 :
    ThetaLowerSegment 62079232 62095616 (6206738405583 / 100000) (1552102245901 / 25000) := by
  exact
    packedTile8192 62079232 62095616 11 931 7879 26 _ _ (1794391 / 100000) (897197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62095616 :
    ThetaLowerSegment 62095616 62112000 (1552102245901 / 25000) (6210079585831 / 100000) := by
  exact
    packedTile8192 62095616 62112000 11 931 7880 26 _ _ (1794417 / 100000) (89721 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62112000 :
    ThetaLowerSegment 62112000 62128384 (6210079585831 / 100000) (3105855367259 / 50000) := by
  exact
    packedTile8192 62112000 62128384 11 909 7881 26 _ _ (1794443 / 100000) (897223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62128384 :
    ThetaLowerSegment 62128384 62144768 (3105855367259 / 50000) (3106722096269 / 50000) := by
  exact
    packedTile8192 62128384 62144768 11 966 7882 26 _ _ (179447 / 10000) (1794473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62144768 :
    ThetaLowerSegment 62144768 62161152 (3106722096269 / 50000) (621500002057 / 10000) := by
  exact
    packedTile8192 62144768 62161152 11 867 7883 26 _ _ (56078 / 3125) (1794499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62161152 :
    ThetaLowerSegment 62161152 62177536 (621500002057 / 10000) (1554154670079 / 25000) := by
  exact
    packedTile8192 62161152 62177536 11 902 7884 26 _ _ (1794523 / 100000) (897263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62177536 :
    ThetaLowerSegment 62177536 62193920 (1554154670079 / 25000) (3109136627247 / 50000) := by
  exact
    packedTile8192 62177536 62193920 11 922 7885 26 _ _ (1794549 / 100000) (224319 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62193920 :
    ThetaLowerSegment 62193920 62210304 (3109136627247 / 50000) (6219872220819 / 100000) := by
  exact
    packedTile8192 62193920 62210304 11 891 7886 26 _ _ (71783 / 4000) (897289 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62210304 :
    ThetaLowerSegment 62210304 62226688 (6219872220819 / 100000) (6221508897843 / 100000) := by
  exact
    packedTile8192 62210304 62226688 11 912 7887 26 _ _ (897301 / 50000) (358921 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62226688 :
    ThetaLowerSegment 62226688 62243072 (6221508897843 / 100000) (1244629837567 / 20000) := by
  exact
    packedTile8192 62226688 62243072 11 914 7888 26 _ _ (448657 / 25000) (1794631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62243072 :
    ThetaLowerSegment 62243072 62259456 (1244629837567 / 20000) (6224753608511 / 100000) := by
  exact
    packedTile8192 62243072 62259456 11 894 7889 26 _ _ (897327 / 50000) (1794657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62259456 :
    ThetaLowerSegment 62259456 62275840 (6224753608511 / 100000) (1556592654023 / 25000) := by
  exact
    packedTile8192 62259456 62275840 11 901 7890 26 _ _ (1794681 / 100000) (448671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62275840 :
    ThetaLowerSegment 62275840 62292224 (1556592654023 / 25000) (6228048667137 / 100000) := by
  exact
    packedTile8192 62275840 62292224 11 935 7891 26 _ _ (1794707 / 100000) (179471 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62292224 :
    ThetaLowerSegment 62292224 62308608 (6228048667137 / 100000) (194678287678 / 3125) := by
  exact
    packedTile8192 62292224 62308608 11 923 7892 26 _ _ (1794733 / 100000) (112171 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62308608 :
    ThetaLowerSegment 62308608 62324992 (194678287678 / 3125) (778922464597 / 12500) := by
  exact
    packedTile8192 62308608 62324992 11 933 7893 26 _ _ (44869 / 2500) (1794763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62324992 :
    ThetaLowerSegment 62324992 62341376 (778922464597 / 12500) (1558260422153 / 25000) := by
  exact
    packedTile8192 62324992 62341376 11 926 7894 26 _ _ (897393 / 50000) (1794789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62341376 :
    ThetaLowerSegment 62341376 62357760 (1558260422153 / 25000) (1558678613349 / 25000) := by
  exact
    packedTile8192 62341376 62357760 11 932 7895 26 _ _ (448703 / 25000) (358963 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62357760 :
    ThetaLowerSegment 62357760 62374144 (1558678613349 / 25000) (1559073477709 / 25000) := by
  exact
    packedTile8192 62357760 62374144 11 880 7896 26 _ _ (897419 / 50000) (1794841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62374144 :
    ThetaLowerSegment 62374144 62390528 (1559073477709 / 25000) (6237929032851 / 100000) := by
  exact
    packedTile8192 62374144 62390528 11 911 7897 26 _ _ (358973 / 20000) (448717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62390528 :
    ThetaLowerSegment 62390528 62406912 (6237929032851 / 100000) (3119783884167 / 50000) := by
  exact
    packedTile8192 62390528 62406912 11 913 7898 26 _ _ (1794891 / 100000) (897447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62406912 :
    ThetaLowerSegment 62406912 62423296 (3119783884167 / 50000) (3120605956153 / 50000) := by
  exact
    packedTile8192 62406912 62423296 11 916 7899 26 _ _ (1794917 / 100000) (44873 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62423296 :
    ThetaLowerSegment 62423296 62439680 (3120605956153 / 50000) (195089140319 / 3125) := by
  exact
    packedTile8192 62423296 62439680 11 914 7900 26 _ _ (1794943 / 100000) (897473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62439680 :
    ThetaLowerSegment 62439680 62456064 (195089140319 / 3125) (1561117888287 / 25000) := by
  exact
    packedTile8192 62439680 62456064 11 902 7901 26 _ _ (179497 / 10000) (1794973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62456064 :
    ThetaLowerSegment 62456064 62472448 (1561117888287 / 25000) (1561528044873 / 25000) := by
  exact
    packedTile8192 62456064 62472448 11 914 7902 26 _ _ (448749 / 25000) (1794999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62472448 :
    ThetaLowerSegment 62472448 62488832 (1561528044873 / 25000) (780968206189 / 12500) := by
  exact
    packedTile8192 62472448 62488832 11 910 7903 26 _ _ (897511 / 50000) (71801 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62488832 :
    ThetaLowerSegment 62488832 62505216 (780968206189 / 12500) (390586981783 / 6250) := by
  exact
    packedTile8192 62488832 62505216 11 917 7904 26 _ _ (224381 / 12500) (1795051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62505216 :
    ThetaLowerSegment 62505216 62521600 (390586981783 / 6250) (3125516203539 / 50000) := by
  exact
    packedTile8192 62505216 62521600 11 914 7906 26 _ _ (71803 / 4000) (897539 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62521600 :
    ThetaLowerSegment 62521600 62537984 (3125516203539 / 50000) (6252664153887 / 100000) := by
  exact
    packedTile8192 62521600 62537984 11 909 7907 26 _ _ (1795101 / 100000) (56097 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62537984 :
    ThetaLowerSegment 62537984 62554368 (6252664153887 / 100000) (625426002179 / 10000) := by
  exact
    packedTile8192 62537984 62554368 11 889 7908 26 _ _ (1795127 / 100000) (179513 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62554368 :
    ThetaLowerSegment 62554368 62570752 (625426002179 / 10000) (3127912697603 / 50000) := by
  exact
    packedTile8192 62554368 62570752 11 872 7909 26 _ _ (1795153 / 100000) (448789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62570752 :
    ThetaLowerSegment 62570752 62587136 (3127912697603 / 50000) (6257439261127 / 100000) := by
  exact
    packedTile8192 62570752 62587136 11 899 7910 26 _ _ (1795179 / 100000) (897591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62587136 :
    ThetaLowerSegment 62587136 62603520 (6257439261127 / 100000) (6259115983531 / 100000) := by
  exact
    packedTile8192 62587136 62603520 11 934 7911 26 _ _ (897603 / 50000) (1795209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62603520 :
    ThetaLowerSegment 62603520 62619904 (6259115983531 / 100000) (1252150647023 / 20000) := by
  exact
    packedTile8192 62603520 62619904 11 912 7912 26 _ _ (56101 / 3125) (359047 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62619904 :
    ThetaLowerSegment 62619904 62636288 (1252150647023 / 20000) (6262349219477 / 100000) := by
  exact
    packedTile8192 62619904 62636288 11 889 7913 26 _ _ (897629 / 50000) (1795261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62636288 :
    ThetaLowerSegment 62636288 62652672 (6262349219477 / 100000) (6263979337349 / 100000) := by
  exact
    packedTile8192 62636288 62652672 11 908 7914 26 _ _ (448821 / 25000) (1795287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62652672 :
    ThetaLowerSegment 62652672 62669056 (6263979337349 / 100000) (6265643589719 / 100000) := by
  exact
    packedTile8192 62652672 62669056 11 927 7915 26 _ _ (179531 / 10000) (1795313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62669056 :
    ThetaLowerSegment 62669056 62685440 (6265643589719 / 100000) (6267259392119 / 100000) := by
  exact
    packedTile8192 62669056 62685440 11 900 7916 26 _ _ (224417 / 12500) (1795339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62685440 :
    ThetaLowerSegment 62685440 62701824 (6267259392119 / 100000) (1253783302249 / 20000) := by
  exact
    packedTile8192 62685440 62701824 11 923 7917 26 _ _ (897681 / 50000) (359073 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62701824 :
    ThetaLowerSegment 62701824 62718208 (1253783302249 / 20000) (1567647004601 / 25000) := by
  exact
    packedTile8192 62701824 62718208 11 931 7918 26 _ _ (1795389 / 100000) (56106 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62718208 :
    ThetaLowerSegment 62718208 62734592 (1567647004601 / 25000) (6272216459809 / 100000) := by
  exact
    packedTile8192 62718208 62734592 11 907 7919 26 _ _ (359083 / 20000) (897709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62734592 :
    ThetaLowerSegment 62734592 62750976 (6272216459809 / 100000) (1568468412963 / 25000) := by
  exact
    packedTile8192 62734592 62750976 11 923 7920 26 _ _ (1795441 / 100000) (448861 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62750976 :
    ThetaLowerSegment 62750976 62767360 (1568468412963 / 25000) (3137760945279 / 50000) := by
  exact
    packedTile8192 62750976 62767360 11 918 7921 26 _ _ (1795467 / 100000) (179547 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62767360 :
    ThetaLowerSegment 62767360 62783744 (3137760945279 / 50000) (1255437980711 / 20000) := by
  exact
    packedTile8192 62767360 62783744 11 929 7922 26 _ _ (1795493 / 100000) (224437 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62783744 :
    ThetaLowerSegment 62783744 62800128 (1255437980711 / 20000) (6278863327263 / 100000) := by
  exact
    packedTile8192 62783744 62800128 11 932 7923 26 _ _ (1795519 / 100000) (897761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62800128 :
    ThetaLowerSegment 62800128 62816512 (6278863327263 / 100000) (1570120278327 / 25000) := by
  exact
    packedTile8192 62800128 62816512 11 901 7924 26 _ _ (359109 / 20000) (448887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62816512 :
    ThetaLowerSegment 62816512 62832896 (1570120278327 / 25000) (1570526077373 / 25000) := by
  exact
    packedTile8192 62816512 62832896 11 904 7925 26 _ _ (1795571 / 100000) (897787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62832896 :
    ThetaLowerSegment 62832896 62849280 (1570526077373 / 25000) (314186376459 / 5000) := by
  exact
    packedTile8192 62832896 62849280 11 904 7926 26 _ _ (1795597 / 100000) (4489 / 250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62849280 :
    ThetaLowerSegment 62849280 62865664 (314186376459 / 5000) (1571345324721 / 25000) := by
  exact
    packedTile8192 62849280 62865664 11 921 7927 26 _ _ (224453 / 12500) (1795627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62865664 :
    ThetaLowerSegment 62865664 62882048 (1571345324721 / 25000) (1571749345971 / 25000) := by
  exact
    packedTile8192 62865664 62882048 11 900 7928 26 _ _ (35913 / 2000) (1795653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62882048 :
    ThetaLowerSegment 62882048 62898432 (1571749345971 / 25000) (1572158760099 / 25000) := by
  exact
    packedTile8192 62882048 62898432 11 912 7929 26 _ _ (448919 / 25000) (1795679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62898432 :
    ThetaLowerSegment 62898432 62914816 (1572158760099 / 25000) (3145160602287 / 50000) := by
  exact
    packedTile8192 62898432 62914816 11 939 7930 26 _ _ (897851 / 50000) (359141 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62914816 :
    ThetaLowerSegment 62914816 62931200 (3145160602287 / 50000) (3145975862799 / 50000) := by
  exact
    packedTile8192 62914816 62931200 11 908 7931 26 _ _ (112233 / 6250) (1795731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62931200 :
    ThetaLowerSegment 62931200 62947584 (3145975862799 / 50000) (314680460327 / 5000) := by
  exact
    packedTile8192 62931200 62947584 11 923 7932 26 _ _ (897877 / 50000) (1795757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62947584 :
    ThetaLowerSegment 62947584 62963968 (314680460327 / 5000) (78690429843 / 1250) := by
  exact
    packedTile8192 62947584 62963968 11 905 7933 26 _ _ (89789 / 5000) (1795783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62963968 :
    ThetaLowerSegment 62963968 62980352 (78690429843 / 1250) (629684163381 / 10000) := by
  exact
    packedTile8192 62963968 62980352 11 895 7934 26 _ _ (897903 / 50000) (1795809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62980352 :
    ThetaLowerSegment 62980352 62996736 (629684163381 / 10000) (3149244205877 / 50000) := by
  exact
    packedTile8192 62980352 62996736 11 917 7936 26 _ _ (224479 / 12500) (359167 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell62996736 :
    ThetaLowerSegment 62996736 63013120 (3149244205877 / 50000) (1575032007527 / 25000) := by
  exact
    packedTile8192 62996736 63013120 11 913 7937 26 _ _ (897929 / 50000) (1795861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63013120 :
    ThetaLowerSegment 63013120 63029504 (1575032007527 / 25000) (31508838361 / 500) := by
  exact
    packedTile8192 63013120 63029504 11 913 7938 26 _ _ (448971 / 25000) (1795887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63029504 :
    ThetaLowerSegment 63029504 63045888 (31508838361 / 500) (630336423619 / 10000) := by
  exact
    packedTile8192 63029504 63045888 11 889 7939 26 _ _ (179591 / 10000) (1795913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63045888 :
    ThetaLowerSegment 63045888 63062272 (630336423619 / 10000) (3152480411647 / 50000) := by
  exact
    packedTile8192 63045888 63062272 11 889 7940 26 _ _ (56123 / 3125) (1795939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63062272 :
    ThetaLowerSegment 63062272 63078656 (3152480411647 / 50000) (394167472433 / 6250) := by
  exact
    packedTile8192 63062272 63078656 11 957 7941 26 _ _ (897981 / 50000) (359193 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63078656 :
    ThetaLowerSegment 63078656 63095040 (394167472433 / 6250) (1577077130011 / 25000) := by
  exact
    packedTile8192 63078656 63095040 11 907 7942 26 _ _ (448997 / 25000) (1795991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63095040 :
    ThetaLowerSegment 63095040 63111424 (1577077130011 / 25000) (197185266396 / 3125) := by
  exact
    packedTile8192 63095040 63111424 11 902 7943 26 _ _ (898007 / 50000) (1796017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63111424 :
    ThetaLowerSegment 63111424 63127808 (197185266396 / 3125) (197235555516 / 3125) := by
  exact
    packedTile8192 63111424 63127808 11 896 7944 26 _ _ (44901 / 2500) (1796043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63127808 :
    ThetaLowerSegment 63127808 63144192 (197235555516 / 3125) (3156576219923 / 50000) := by
  exact
    packedTile8192 63127808 63144192 11 899 7945 26 _ _ (898033 / 50000) (1796069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63144192 :
    ThetaLowerSegment 63144192 63160576 (3156576219923 / 50000) (3157396135921 / 50000) := by
  exact
    packedTile8192 63144192 63160576 11 913 7946 26 _ _ (449023 / 25000) (359219 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63160576 :
    ThetaLowerSegment 63160576 63176960 (3157396135921 / 50000) (3158225942437 / 50000) := by
  exact
    packedTile8192 63160576 63176960 11 924 7947 26 _ _ (898059 / 50000) (1796121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63176960 :
    ThetaLowerSegment 63176960 63193344 (3158225942437 / 50000) (3159047678317 / 50000) := by
  exact
    packedTile8192 63176960 63193344 11 915 7948 26 _ _ (112259 / 6250) (1796147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63193344 :
    ThetaLowerSegment 63193344 63209728 (3159047678317 / 50000) (631975501679 / 10000) := by
  exact
    packedTile8192 63193344 63209728 11 924 7949 26 _ _ (1796169 / 100000) (449043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63209728 :
    ThetaLowerSegment 63209728 63226112 (631975501679 / 10000) (1264283299433 / 20000) := by
  exact
    packedTile8192 63209728 63226112 11 925 7950 26 _ _ (359239 / 20000) (898099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63226112 :
    ThetaLowerSegment 63226112 63242496 (1264283299433 / 20000) (6323043873391 / 100000) := by
  exact
    packedTile8192 63226112 63242496 11 906 7951 26 _ _ (1796221 / 100000) (56132 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63242496 :
    ThetaLowerSegment 63242496 63258880 (6323043873391 / 100000) (6324696420631 / 100000) := by
  exact
    packedTile8192 63242496 63258880 11 920 7952 26 _ _ (1796247 / 100000) (1437 / 80) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63258880 :
    ThetaLowerSegment 63258880 63275264 (6324696420631 / 100000) (1581578715651 / 25000) := by
  exact
    packedTile8192 63258880 63275264 11 901 7953 26 _ _ (1796273 / 100000) (449069 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63275264 :
    ThetaLowerSegment 63275264 63291648 (1581578715651 / 25000) (6327994402169 / 100000) := by
  exact
    packedTile8192 63275264 63291648 11 935 7954 26 _ _ (1796299 / 100000) (898151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63291648 :
    ThetaLowerSegment 63291648 63308032 (6327994402169 / 100000) (3164824408747 / 50000) := by
  exact
    packedTile8192 63291648 63308032 11 921 7955 26 _ _ (71853 / 4000) (224541 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63308032 :
    ThetaLowerSegment 63308032 63324416 (3164824408747 / 50000) (6331184697599 / 100000) := by
  exact
    packedTile8192 63308032 63324416 11 855 7956 26 _ _ (1796351 / 100000) (898177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63324416 :
    ThetaLowerSegment 63324416 63340800 (6331184697599 / 100000) (1583200808319 / 25000) := by
  exact
    packedTile8192 63324416 63340800 11 901 7957 26 _ _ (1796377 / 100000) (89819 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63340800 :
    ThetaLowerSegment 63340800 63357184 (1583200808319 / 25000) (1583613981009 / 25000) := by
  exact
    packedTile8192 63340800 63357184 11 920 7958 26 _ _ (1796403 / 100000) (898203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63357184 :
    ThetaLowerSegment 63357184 63373568 (1583613981009 / 25000) (316805252247 / 5000) := by
  exact
    packedTile8192 63357184 63373568 11 918 7959 26 _ _ (449107 / 25000) (1796431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63373568 :
    ThetaLowerSegment 63373568 63389952 (316805252247 / 5000) (158444393679 / 2500) := by
  exact
    packedTile8192 63373568 63389952 11 930 7960 26 _ _ (898227 / 50000) (1796457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63389952 :
    ThetaLowerSegment 63389952 63406336 (158444393679 / 2500) (158485757631 / 2500) := by
  exact
    packedTile8192 63389952 63406336 11 921 7961 26 _ _ (11228 / 625) (1796483 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63406336 :
    ThetaLowerSegment 63406336 63422720 (158485757631 / 2500) (3170526275079 / 50000) := by
  exact
    packedTile8192 63406336 63422720 11 903 7962 26 _ _ (898253 / 50000) (1796509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63422720 :
    ThetaLowerSegment 63422720 63439104 (3170526275079 / 50000) (3171368848587 / 50000) := by
  exact
    packedTile8192 63422720 63439104 11 938 7963 26 _ _ (449133 / 25000) (359307 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63439104 :
    ThetaLowerSegment 63439104 63455488 (3171368848587 / 50000) (1586101674889 / 25000) := by
  exact
    packedTile8192 63439104 63455488 11 929 7964 26 _ _ (898279 / 50000) (1796561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63455488 :
    ThetaLowerSegment 63455488 63471872 (1586101674889 / 25000) (6346057759333 / 100000) := by
  exact
    packedTile8192 63455488 63471872 11 919 7965 26 _ _ (1796583 / 100000) (898293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63471872 :
    ThetaLowerSegment 63471872 63488256 (6346057759333 / 100000) (396730455231 / 6250) := by
  exact
    packedTile8192 63471872 63488256 11 907 7966 26 _ _ (1796609 / 100000) (449153 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63488256 :
    ThetaLowerSegment 63488256 63504640 (396730455231 / 6250) (6349313238371 / 100000) := by
  exact
    packedTile8192 63488256 63504640 11 905 7967 26 _ _ (359327 / 20000) (898319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63504640 :
    ThetaLowerSegment 63504640 63521024 (6349313238371 / 100000) (6350872740119 / 100000) := by
  exact
    packedTile8192 63504640 63521024 11 868 7968 26 _ _ (1796661 / 100000) (224583 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63521024 :
    ThetaLowerSegment 63521024 63537408 (6350872740119 / 100000) (1588147144051 / 25000) := by
  exact
    packedTile8192 63521024 63537408 11 955 7970 26 _ _ (1796687 / 100000) (179669 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63537408 :
    ThetaLowerSegment 63537408 63553792 (1588147144051 / 25000) (1588558141921 / 25000) := by
  exact
    packedTile8192 63537408 63553792 11 915 7971 26 _ _ (224589 / 12500) (359343 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63553792 :
    ThetaLowerSegment 63553792 63570176 (1588558141921 / 25000) (3177941884953 / 50000) := by
  exact
    packedTile8192 63553792 63570176 11 919 7972 26 _ _ (898369 / 50000) (1796741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63570176 :
    ThetaLowerSegment 63570176 63586560 (3177941884953 / 50000) (3178765701247 / 50000) := by
  exact
    packedTile8192 63570176 63586560 11 917 7973 26 _ _ (449191 / 25000) (1796767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63586560 :
    ThetaLowerSegment 63586560 63602944 (3178765701247 / 50000) (1589787577571 / 25000) := by
  exact
    packedTile8192 63586560 63602944 11 901 7974 26 _ _ (179679 / 10000) (1796793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63602944 :
    ThetaLowerSegment 63602944 63619328 (1589787577571 / 25000) (1590191861171 / 25000) := by
  exact
    packedTile8192 63602944 63619328 11 900 7975 26 _ _ (112301 / 6250) (1796819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63619328 :
    ThetaLowerSegment 63619328 63635712 (1590191861171 / 25000) (3181208472361 / 50000) := by
  exact
    packedTile8192 63619328 63635712 11 918 7976 26 _ _ (1796841 / 100000) (449211 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63635712 :
    ThetaLowerSegment 63635712 63652096 (3181208472361 / 50000) (636404131249 / 10000) := by
  exact
    packedTile8192 63635712 63652096 11 904 7977 26 _ _ (1796867 / 100000) (179687 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63652096 :
    ThetaLowerSegment 63652096 63668480 (636404131249 / 10000) (39785478032 / 625) := by
  exact
    packedTile8192 63652096 63668480 11 910 7978 26 _ _ (1796893 / 100000) (56153 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63668480 :
    ThetaLowerSegment 63668480 63684864 (39785478032 / 625) (3183677403733 / 50000) := by
  exact
    packedTile8192 63668480 63684864 11 934 7979 26 _ _ (1796919 / 100000) (898461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63684864 :
    ThetaLowerSegment 63684864 63701248 (3183677403733 / 50000) (127378937997 / 2000) := by
  exact
    packedTile8192 63684864 63701248 11 886 7980 26 _ _ (112309 / 6250) (1796947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63701248 :
    ThetaLowerSegment 63701248 63717632 (127378937997 / 2000) (159263700003 / 2500) := by
  exact
    packedTile8192 63701248 63717632 11 891 7981 26 _ _ (179697 / 10000) (1796973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63717632 :
    ThetaLowerSegment 63717632 63734016 (159263700003 / 2500) (318610511071 / 5000) := by
  exact
    packedTile8192 63717632 63734016 11 925 7982 26 _ _ (449249 / 25000) (1796999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63734016 :
    ThetaLowerSegment 63734016 63750400 (318610511071 / 5000) (127477629019 / 2000) := by
  exact
    packedTile8192 63734016 63750400 11 930 7983 26 _ _ (1797021 / 100000) (56157 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63750400 :
    ThetaLowerSegment 63750400 63766784 (127477629019 / 2000) (6375518560767 / 100000) := by
  exact
    packedTile8192 63750400 63766784 11 911 7984 26 _ _ (1797047 / 100000) (35941 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63766784 :
    ThetaLowerSegment 63766784 63783168 (6375518560767 / 100000) (6377157491343 / 100000) := by
  exact
    packedTile8192 63766784 63783168 11 912 7985 26 _ _ (1797073 / 100000) (449269 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63783168 :
    ThetaLowerSegment 63783168 63799552 (6377157491343 / 100000) (6378875517031 / 100000) := by
  exact
    packedTile8192 63783168 63799552 11 956 7986 26 _ _ (898549 / 50000) (1797101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63799552 :
    ThetaLowerSegment 63799552 63815936 (6378875517031 / 100000) (6380543248103 / 100000) := by
  exact
    packedTile8192 63799552 63815936 11 928 7987 26 _ _ (449281 / 25000) (1797127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63815936 :
    ThetaLowerSegment 63815936 63832320 (6380543248103 / 100000) (6382151697353 / 100000) := by
  exact
    packedTile8192 63815936 63832320 11 895 7988 26 _ _ (35943 / 2000) (1797153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63832320 :
    ThetaLowerSegment 63832320 63848704 (6382151697353 / 100000) (6383828462561 / 100000) := by
  exact
    packedTile8192 63832320 63848704 11 933 7989 26 _ _ (224647 / 12500) (1797179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63848704 :
    ThetaLowerSegment 63848704 63865088 (6383828462561 / 100000) (6385431565853 / 100000) := by
  exact
    packedTile8192 63848704 63865088 11 892 7990 26 _ _ (1797201 / 100000) (449301 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63865088 :
    ThetaLowerSegment 63865088 63881472 (6385431565853 / 100000) (6387135337049 / 100000) := by
  exact
    packedTile8192 63865088 63881472 11 948 7991 26 _ _ (1797227 / 100000) (179723 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63881472 :
    ThetaLowerSegment 63881472 63897856 (6387135337049 / 100000) (6388772633621 / 100000) := by
  exact
    packedTile8192 63881472 63897856 11 911 7992 26 _ _ (449313 / 25000) (359451 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63897856 :
    ThetaLowerSegment 63897856 63914240 (6388772633621 / 100000) (6390418940269 / 100000) := by
  exact
    packedTile8192 63897856 63914240 11 916 7993 26 _ _ (898639 / 50000) (1797281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63914240 :
    ThetaLowerSegment 63914240 63930624 (6390418940269 / 100000) (51136493409 / 800) := by
  exact
    packedTile8192 63914240 63930624 11 914 7994 26 _ _ (224663 / 12500) (1797307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63930624 :
    ThetaLowerSegment 63930624 63947008 (51136493409 / 800) (6393711624147 / 100000) := by
  exact
    packedTile8192 63930624 63947008 11 918 7995 26 _ _ (1797329 / 100000) (449333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63947008 :
    ThetaLowerSegment 63947008 63963392 (6393711624147 / 100000) (6395350811907 / 100000) := by
  exact
    packedTile8192 63947008 63963392 11 912 7996 26 _ _ (359471 / 20000) (898679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63963392 :
    ThetaLowerSegment 63963392 63979776 (6395350811907 / 100000) (6396975644331 / 100000) := by
  exact
    packedTile8192 63963392 63979776 11 904 7997 26 _ _ (1797381 / 100000) (224673 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63979776 :
    ThetaLowerSegment 63979776 63996160 (6396975644331 / 100000) (6398595107137 / 100000) := by
  exact
    packedTile8192 63979776 63996160 11 901 7998 26 _ _ (898703 / 50000) (1797409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell63996160 :
    ThetaLowerSegment 63996160 64012544 (6398595107137 / 100000) (6400203808777 / 100000) := by
  exact
    packedTile8192 63996160 64012544 11 895 7999 26 _ _ (224679 / 12500) (359487 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64012544 :
    ThetaLowerSegment 64012544 64028928 (6400203808777 / 100000) (80023195897 / 1250) := by
  exact
    packedTile8192 64012544 64028928 11 919 8000 26 _ _ (1797457 / 100000) (89873 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64028928 :
    ThetaLowerSegment 64028928 64045312 (80023195897 / 1250) (6403485988841 / 100000) := by
  exact
    packedTile8192 64028928 64045312 11 907 8001 26 _ _ (1797483 / 100000) (898743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64045312 :
    ThetaLowerSegment 64045312 64061696 (6403485988841 / 100000) (6405125317049 / 100000) := by
  exact
    packedTile8192 64045312 64061696 11 912 8002 26 _ _ (1797509 / 100000) (224689 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64061696 :
    ThetaLowerSegment 64061696 64078080 (6405125317049 / 100000) (1281357247693 / 20000) := by
  exact
    packedTile8192 64061696 64078080 11 924 8003 26 _ _ (898767 / 50000) (1797537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64078080 :
    ThetaLowerSegment 64078080 64094464 (1281357247693 / 20000) (256337312137 / 4000) := by
  exact
    packedTile8192 64078080 64094464 11 916 8004 26 _ _ (44939 / 2500) (1797563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64094464 :
    ThetaLowerSegment 64094464 64110848 (256337312137 / 4000) (1282021630529 / 20000) := by
  exact
    packedTile8192 64094464 64110848 11 932 8005 26 _ _ (359517 / 20000) (449397 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64110848 :
    ThetaLowerSegment 64110848 64127232 (1282021630529 / 20000) (1602928354817 / 25000) := by
  exact
    packedTile8192 64110848 64127232 11 893 8006 26 _ _ (1797611 / 100000) (898807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64127232 :
    ThetaLowerSegment 64127232 64143616 (1602928354817 / 25000) (801673826707 / 12500) := by
  exact
    packedTile8192 64127232 64143616 11 933 8007 26 _ _ (449409 / 25000) (1797639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64143616 :
    ThetaLowerSegment 64143616 64160000 (801673826707 / 12500) (32075150407 / 500) := by
  exact
    packedTile8192 64143616 64160000 11 912 8008 26 _ _ (898831 / 50000) (359533 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64160000 :
    ThetaLowerSegment 64160000 64176384 (32075150407 / 500) (802073359901 / 12500) := by
  exact
    packedTile8192 64160000 64176384 11 866 8009 26 _ _ (224711 / 12500) (1797691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64176384 :
    ThetaLowerSegment 64176384 64192768 (802073359901 / 12500) (802278299183 / 12500) := by
  exact
    packedTile8192 64176384 64192768 11 912 8011 26 _ _ (1797713 / 100000) (449429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64192768 :
    ThetaLowerSegment 64192768 64209152 (802278299183 / 12500) (6419918065863 / 100000) := by
  exact
    packedTile8192 64192768 64209152 11 941 8012 26 _ _ (1797739 / 100000) (898871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64209152 :
    ThetaLowerSegment 64209152 64225536 (6419918065863 / 100000) (6421557626631 / 100000) := by
  exact
    packedTile8192 64209152 64225536 11 912 8013 26 _ _ (449441 / 25000) (1797767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64225536 :
    ThetaLowerSegment 64225536 64241920 (6421557626631 / 100000) (6423121703931 / 100000) := by
  exact
    packedTile8192 64225536 64241920 11 870 8014 26 _ _ (179779 / 10000) (1797793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64241920 :
    ThetaLowerSegment 64241920 64258304 (6423121703931 / 100000) (3212395937033 / 50000) := by
  exact
    packedTile8192 64241920 64258304 11 929 8015 26 _ _ (359563 / 20000) (898909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64258304 :
    ThetaLowerSegment 64258304 64274688 (3212395937033 / 50000) (321321755037 / 5000) := by
  exact
    packedTile8192 64258304 64274688 11 914 8016 26 _ _ (1797841 / 100000) (449461 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64274688 :
    ThetaLowerSegment 64274688 64291072 (321321755037 / 5000) (3214083222849 / 50000) := by
  exact
    packedTile8192 64274688 64291072 11 963 8017 26 _ _ (898933 / 50000) (1797869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64291072 :
    ThetaLowerSegment 64291072 64307456 (3214083222849 / 50000) (642977735693 / 10000) := by
  exact
    packedTile8192 64291072 64307456 11 896 8018 26 _ _ (449473 / 25000) (359579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64307456 :
    ThetaLowerSegment 64307456 64323840 (642977735693 / 10000) (321568875153 / 5000) := by
  exact
    packedTile8192 64307456 64323840 11 890 8019 26 _ _ (1797917 / 100000) (11237 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64323840 :
    ThetaLowerSegment 64323840 64340224 (321568875153 / 5000) (3216514007367 / 50000) := by
  exact
    packedTile8192 64323840 64340224 11 918 8020 26 _ _ (1797943 / 100000) (898973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64340224 :
    ThetaLowerSegment 64340224 64356608 (3216514007367 / 50000) (3217332981791 / 50000) := by
  exact
    packedTile8192 64340224 64356608 11 911 8021 26 _ _ (112373 / 6250) (1797971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64356608 :
    ThetaLowerSegment 64356608 64372992 (3217332981791 / 50000) (3218156463043 / 50000) := by
  exact
    packedTile8192 64356608 64372992 11 916 8022 26 _ _ (898997 / 50000) (1797997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64372992 :
    ThetaLowerSegment 64372992 64389376 (3218156463043 / 50000) (6437961709509 / 100000) := by
  exact
    packedTile8192 64372992 64389376 11 917 8023 26 _ _ (1798019 / 100000) (899011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64389376 :
    ThetaLowerSegment 64389376 64405760 (6437961709509 / 100000) (6439624900209 / 100000) := by
  exact
    packedTile8192 64389376 64405760 11 925 8024 26 _ _ (449511 / 25000) (1798047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64405760 :
    ThetaLowerSegment 64405760 64422144 (6439624900209 / 100000) (6441275528469 / 100000) := by
  exact
    packedTile8192 64405760 64422144 11 918 8025 26 _ _ (179807 / 10000) (1798073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64422144 :
    ThetaLowerSegment 64422144 64438528 (6441275528469 / 100000) (6442897410159 / 100000) := by
  exact
    packedTile8192 64422144 64438528 11 902 8026 26 _ _ (359619 / 20000) (899049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64438528 :
    ThetaLowerSegment 64438528 64454912 (6442897410159 / 100000) (6444533700269 / 100000) := by
  exact
    packedTile8192 64438528 64454912 11 910 8027 26 _ _ (1798121 / 100000) (449531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64454912 :
    ThetaLowerSegment 64454912 64471296 (6444533700269 / 100000) (1289230765963 / 20000) := by
  exact
    packedTile8192 64454912 64471296 11 901 8028 26 _ _ (899073 / 50000) (1798149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64471296 :
    ThetaLowerSegment 64471296 64487680 (1289230765963 / 20000) (6447734423003 / 100000) := by
  exact
    packedTile8192 64471296 64487680 11 879 8029 26 _ _ (449543 / 25000) (71927 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64487680 :
    ThetaLowerSegment 64487680 64504064 (6447734423003 / 100000) (6449385167849 / 100000) := by
  exact
    packedTile8192 64487680 64504064 11 918 8030 26 _ _ (1798197 / 100000) (8991 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64504064 :
    ThetaLowerSegment 64504064 64520448 (6449385167849 / 100000) (6451050321421 / 100000) := by
  exact
    packedTile8192 64504064 64520448 11 926 8031 26 _ _ (899111 / 50000) (71929 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64520448 :
    ThetaLowerSegment 64520448 64536832 (6451050321421 / 100000) (6452699314837 / 100000) := by
  exact
    packedTile8192 64520448 64536832 11 917 8032 26 _ _ (224781 / 12500) (1798251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64536832 :
    ThetaLowerSegment 64536832 64553216 (6452699314837 / 100000) (6454317760537 / 100000) := by
  exact
    packedTile8192 64536832 64553216 11 900 8033 26 _ _ (1798273 / 100000) (449569 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64553216 :
    ThetaLowerSegment 64553216 64569600 (6454317760537 / 100000) (6455929036441 / 100000) := by
  exact
    packedTile8192 64553216 64569600 11 896 8034 26 _ _ (1798299 / 100000) (899151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64569600 :
    ThetaLowerSegment 64569600 64585984 (6455929036441 / 100000) (6457525948153 / 100000) := by
  exact
    packedTile8192 64569600 64585984 11 888 8035 26 _ _ (449581 / 25000) (1798327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64585984 :
    ThetaLowerSegment 64585984 64602368 (6457525948153 / 100000) (3229562340207 / 50000) := by
  exact
    packedTile8192 64585984 64602368 11 889 8036 26 _ _ (1798349 / 100000) (112397 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64602368 :
    ThetaLowerSegment 64602368 64618752 (3229562340207 / 50000) (6460723435789 / 100000) := by
  exact
    packedTile8192 64602368 64618752 11 889 8037 26 _ _ (14387 / 800) (899189 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64618752 :
    ThetaLowerSegment 64618752 64635136 (6460723435789 / 100000) (6462345592589 / 100000) := by
  exact
    packedTile8192 64618752 64635136 11 902 8038 26 _ _ (2248 / 125) (1798403 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64635136 :
    ThetaLowerSegment 64635136 64651520 (6462345592589 / 100000) (6463985756189 / 100000) := by
  exact
    packedTile8192 64635136 64651520 11 912 8039 26 _ _ (71937 / 4000) (449607 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64651520 :
    ThetaLowerSegment 64651520 64667904 (6463985756189 / 100000) (1616405137037 / 25000) := by
  exact
    packedTile8192 64651520 64667904 11 909 8040 26 _ _ (1798451 / 100000) (899227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64667904 :
    ThetaLowerSegment 64667904 64684288 (1616405137037 / 25000) (1616817887279 / 25000) := by
  exact
    packedTile8192 64667904 64684288 11 918 8041 26 _ _ (449619 / 25000) (1798479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64684288 :
    ThetaLowerSegment 64684288 64700672 (1616817887279 / 25000) (3234461286517 / 50000) := by
  exact
    packedTile8192 64684288 64700672 11 918 8042 26 _ _ (1798501 / 100000) (224813 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64700672 :
    ThetaLowerSegment 64700672 64717056 (3234461286517 / 50000) (129411112711 / 2000) := by
  exact
    packedTile8192 64700672 64717056 11 908 8043 26 _ _ (1798527 / 100000) (179853 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64717056 :
    ThetaLowerSegment 64717056 64733440 (129411112711 / 2000) (3236092561831 / 50000) := by
  exact
    packedTile8192 64717056 64733440 11 906 8044 26 _ _ (224819 / 12500) (359711 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64733440 :
    ThetaLowerSegment 64733440 64749824 (3236092561831 / 50000) (6473755281383 / 100000) := by
  exact
    packedTile8192 64733440 64749824 11 873 8045 26 _ _ (1798577 / 100000) (89929 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64749824 :
    ThetaLowerSegment 64749824 64766208 (6473755281383 / 100000) (6475392010113 / 100000) := by
  exact
    packedTile8192 64749824 64766208 11 910 8046 26 _ _ (1798603 / 100000) (899303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64766208 :
    ThetaLowerSegment 64766208 64782592 (6475392010113 / 100000) (6476980198637 / 100000) := by
  exact
    packedTile8192 64766208 64782592 11 883 8047 26 _ _ (449657 / 25000) (1798631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64782592 :
    ThetaLowerSegment 64782592 64798976 (6476980198637 / 100000) (404915471873 / 6250) := by
  exact
    packedTile8192 64782592 64798976 11 927 8048 26 _ _ (1798653 / 100000) (56208 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64798976 :
    ThetaLowerSegment 64798976 64815360 (404915471873 / 6250) (12960561501 / 200) := by
  exact
    packedTile8192 64798976 64815360 11 908 8049 26 _ _ (1798679 / 100000) (899341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64815360 :
    ThetaLowerSegment 64815360 64831744 (12960561501 / 200) (1620478043757 / 25000) := by
  exact
    packedTile8192 64815360 64831744 11 907 8050 26 _ _ (112419 / 6250) (1798707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64831744 :
    ThetaLowerSegment 64831744 64848128 (1620478043757 / 25000) (324179069777 / 5000) := by
  exact
    packedTile8192 64831744 64848128 11 928 8051 26 _ _ (1798729 / 100000) (449683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64848128 :
    ThetaLowerSegment 64848128 64864512 (324179069777 / 5000) (810642389563 / 12500) := by
  exact
    packedTile8192 64848128 64864512 11 866 8052 26 _ _ (899377 / 50000) (1798757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64864512 :
    ThetaLowerSegment 64864512 64880896 (810642389563 / 12500) (202711750197 / 3125) := by
  exact
    packedTile8192 64864512 64880896 11 910 8053 26 _ _ (89939 / 5000) (1798783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64880896 :
    ThetaLowerSegment 64880896 64897280 (202711750197 / 3125) (1622116720751 / 25000) := by
  exact
    packedTile8192 64880896 64897280 11 940 8054 26 _ _ (359761 / 20000) (224851 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64897280 :
    ThetaLowerSegment 64897280 64913664 (1622116720751 / 25000) (3245052808567 / 50000) := by
  exact
    packedTile8192 64897280 64913664 11 911 8055 26 _ _ (179883 / 10000) (1798833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64913664 :
    ThetaLowerSegment 64913664 64930048 (3245052808567 / 50000) (6491726385489 / 100000) := by
  exact
    packedTile8192 64913664 64930048 11 901 8056 26 _ _ (359771 / 20000) (899429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64930048 :
    ThetaLowerSegment 64930048 64946432 (6491726385489 / 100000) (3246695175207 / 50000) := by
  exact
    packedTile8192 64930048 64946432 11 925 8057 26 _ _ (1798881 / 100000) (449721 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64946432 :
    ThetaLowerSegment 64946432 64962816 (3246695175207 / 50000) (202968649171 / 3125) := by
  exact
    packedTile8192 64946432 64962816 11 893 8058 26 _ _ (899453 / 50000) (1798909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64962816 :
    ThetaLowerSegment 64962816 64979200 (202968649171 / 3125) (6496671578233 / 100000) := by
  exact
    packedTile8192 64962816 64979200 11 931 8059 26 _ _ (1798931 / 100000) (899467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64979200 :
    ThetaLowerSegment 64979200 64995584 (6496671578233 / 100000) (6498292437589 / 100000) := by
  exact
    packedTile8192 64979200 64995584 11 901 8060 26 _ _ (449739 / 25000) (1798959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell64995584 :
    ThetaLowerSegment 64995584 65011968 (6498292437589 / 100000) (6499936706223 / 100000) := by
  exact
    packedTile8192 64995584 65011968 11 914 8061 26 _ _ (1798981 / 100000) (224873 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65011968 :
    ThetaLowerSegment 65011968 65028352 (6499936706223 / 100000) (1625406493449 / 25000) := by
  exact
    packedTile8192 65011968 65028352 11 939 8062 26 _ _ (1799007 / 100000) (179901 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65028352 :
    ThetaLowerSegment 65028352 65044736 (1625406493449 / 25000) (1625833313791 / 25000) := by
  exact
    packedTile8192 65028352 65044736 11 949 8064 26 _ _ (224879 / 12500) (359807 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65044736 :
    ThetaLowerSegment 65044736 65061120 (1625833313791 / 25000) (6504907430039 / 100000) := by
  exact
    packedTile8192 65044736 65061120 11 875 8065 26 _ _ (1799057 / 100000) (89953 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65061120 :
    ThetaLowerSegment 65061120 65077504 (6504907430039 / 100000) (1301311797463 / 20000) := by
  exact
    packedTile8192 65061120 65077504 11 918 8066 26 _ _ (899541 / 50000) (359817 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65077504 :
    ThetaLowerSegment 65077504 65093888 (1301311797463 / 20000) (6508199772899 / 100000) := by
  exact
    packedTile8192 65077504 65093888 11 912 8067 26 _ _ (1799107 / 100000) (179911 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65093888 :
    ThetaLowerSegment 65093888 65110272 (6508199772899 / 100000) (6509811796067 / 100000) := by
  exact
    packedTile8192 65093888 65110272 11 896 8068 26 _ _ (1799133 / 100000) (56223 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65110272 :
    ThetaLowerSegment 65110272 65126656 (6509811796067 / 100000) (6511409448371 / 100000) := by
  exact
    packedTile8192 65110272 65126656 11 888 8069 26 _ _ (899579 / 50000) (1799161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65126656 :
    ThetaLowerSegment 65126656 65143040 (6511409448371 / 100000) (3256504461029 / 50000) := by
  exact
    packedTile8192 65126656 65143040 11 889 8070 26 _ _ (1799183 / 100000) (899593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65143040 :
    ThetaLowerSegment 65143040 65159424 (3256504461029 / 50000) (3257328498293 / 50000) := by
  exact
    packedTile8192 65143040 65159424 11 916 8071 26 _ _ (224901 / 12500) (1799211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65159424 :
    ThetaLowerSegment 65159424 65175808 (3257328498293 / 50000) (6516270908587 / 100000) := by
  exact
    packedTile8192 65159424 65175808 11 897 8072 26 _ _ (1799233 / 100000) (449809 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65175808 :
    ThetaLowerSegment 65175808 65192192 (6516270908587 / 100000) (6517899237077 / 100000) := by
  exact
    packedTile8192 65175808 65192192 11 905 8073 26 _ _ (899629 / 50000) (1799261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65192192 :
    ThetaLowerSegment 65192192 65208576 (6517899237077 / 100000) (1303904438249 / 20000) := by
  exact
    packedTile8192 65192192 65208576 11 902 8074 26 _ _ (449821 / 25000) (1799287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65208576 :
    ThetaLowerSegment 65208576 65224960 (1303904438249 / 20000) (8151415716 / 125) := by
  exact
    packedTile8192 65208576 65224960 11 895 8075 26 _ _ (1799309 / 100000) (112457 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65224960 :
    ThetaLowerSegment 65224960 65241344 (8151415716 / 125) (1630706886357 / 25000) := by
  exact
    packedTile8192 65224960 65241344 11 942 8076 26 _ _ (899667 / 50000) (1799337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65241344 :
    ThetaLowerSegment 65241344 65257728 (1630706886357 / 25000) (6524409181989 / 100000) := by
  exact
    packedTile8192 65241344 65257728 11 879 8077 26 _ _ (1799359 / 100000) (899681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65257728 :
    ThetaLowerSegment 65257728 65274112 (6524409181989 / 100000) (6526079010341 / 100000) := by
  exact
    packedTile8192 65257728 65274112 11 928 8078 26 _ _ (224923 / 12500) (1799387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65274112 :
    ThetaLowerSegment 65274112 65290496 (6526079010341 / 100000) (3263875330651 / 50000) := by
  exact
    packedTile8192 65274112 65290496 11 929 8079 26 _ _ (1799409 / 100000) (449853 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65290496 :
    ThetaLowerSegment 65290496 65306880 (3263875330651 / 50000) (204043548267 / 3125) := by
  exact
    packedTile8192 65290496 65306880 11 913 8080 26 _ _ (899717 / 50000) (1799437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65306880 :
    ThetaLowerSegment 65306880 65323264 (204043548267 / 3125) (6531025653857 / 100000) := by
  exact
    packedTile8192 65306880 65323264 11 907 8081 26 _ _ (1799459 / 100000) (899731 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65323264 :
    ThetaLowerSegment 65323264 65339648 (6531025653857 / 100000) (6532664983781 / 100000) := by
  exact
    packedTile8192 65323264 65339648 11 911 8082 26 _ _ (449871 / 25000) (1799487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65339648 :
    ThetaLowerSegment 65339648 65356032 (6532664983781 / 100000) (653432233157 / 10000) := by
  exact
    packedTile8192 65339648 65356032 11 921 8083 26 _ _ (1799509 / 100000) (224939 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65356032 :
    ThetaLowerSegment 65356032 65372416 (653432233157 / 10000) (1307173626427 / 20000) := by
  exact
    packedTile8192 65356032 65372416 11 859 8084 26 _ _ (359907 / 20000) (899769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65372416 :
    ThetaLowerSegment 65372416 65388800 (1307173626427 / 20000) (261500517199 / 4000) := by
  exact
    packedTile8192 65372416 65388800 11 914 8085 26 _ _ (44989 / 2500) (1799563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65388800 :
    ThetaLowerSegment 65388800 65405184 (261500517199 / 4000) (1307817873287 / 20000) := by
  exact
    packedTile8192 65388800 65405184 11 876 8086 26 _ _ (359917 / 20000) (449897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65405184 :
    ThetaLowerSegment 65405184 65421568 (1307817873287 / 20000) (1308167357549 / 20000) := by
  exact
    packedTile8192 65405184 65421568 11 971 8087 26 _ _ (179961 / 10000) (1799613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65421568 :
    ThetaLowerSegment 65421568 65437952 (1308167357549 / 20000) (261700273961 / 4000) := by
  exact
    packedTile8192 65421568 65437952 11 928 8088 26 _ _ (359927 / 20000) (899819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65437952 :
    ThetaLowerSegment 65437952 65454336 (261700273961 / 4000) (1308833227109 / 20000) := by
  exact
    packedTile8192 65437952 65454336 11 922 8089 26 _ _ (89983 / 5000) (1799663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65454336 :
    ThetaLowerSegment 65454336 65470720 (1308833227109 / 20000) (261835609351 / 4000) := by
  exact
    packedTile8192 65454336 65470720 11 958 8090 26 _ _ (359937 / 20000) (224961 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65470720 :
    ThetaLowerSegment 65470720 65487104 (261835609351 / 4000) (261902198621 / 4000) := by
  exact
    packedTile8192 65470720 65487104 11 925 8091 26 _ _ (179971 / 10000) (1799713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65487104 :
    ThetaLowerSegment 65487104 65503488 (261902198621 / 4000) (16373049301 / 250) := by
  exact
    packedTile8192 65487104 65503488 11 925 8092 26 _ _ (359947 / 20000) (899869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65503488 :
    ThetaLowerSegment 65503488 65519872 (16373049301 / 250) (81884773901 / 1250) := by
  exact
    packedTile8192 65503488 65519872 11 868 8093 26 _ _ (22497 / 1250) (1799763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65519872 :
    ThetaLowerSegment 65519872 65536256 (81884773901 / 1250) (327620805843 / 5000) := by
  exact
    packedTile8192 65519872 65536256 11 908 8094 26 _ _ (359957 / 20000) (449947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65536256 :
    ThetaLowerSegment 65536256 65552640 (327620805843 / 5000) (131080682921 / 2000) := by
  exact
    packedTile8192 65536256 65552640 11 899 8095 26 _ _ (179981 / 10000) (1799813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65552640 :
    ThetaLowerSegment 65552640 65569024 (131080682921 / 2000) (1311129719609 / 20000) := by
  exact
    packedTile8192 65552640 65569024 11 897 8096 26 _ _ (359967 / 20000) (899919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65569024 :
    ThetaLowerSegment 65569024 65585408 (1311129719609 / 20000) (1311462693709 / 20000) := by
  exact
    packedTile8192 65569024 65585408 11 925 8097 26 _ _ (89993 / 5000) (1799863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65585408 :
    ThetaLowerSegment 65585408 65601792 (1311462693709 / 20000) (1311777313607 / 20000) := by
  exact
    packedTile8192 65585408 65601792 11 874 8098 26 _ _ (359977 / 20000) (112493 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65601792 :
    ThetaLowerSegment 65601792 65618176 (1311777313607 / 20000) (1312104897227 / 20000) := by
  exact
    packedTile8192 65601792 65618176 11 910 8099 26 _ _ (179991 / 10000) (1799913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65618176 :
    ThetaLowerSegment 65618176 65634560 (1312104897227 / 20000) (328109291307 / 5000) := by
  exact
    packedTile8192 65618176 65634560 11 923 8100 26 _ _ (359987 / 20000) (899969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65634560 :
    ThetaLowerSegment 65634560 65650944 (328109291307 / 5000) (328190019513 / 5000) := by
  exact
    packedTile8192 65634560 65650944 11 897 8101 26 _ _ (44999 / 2500) (1799963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65650944 :
    ThetaLowerSegment 65650944 65667328 (328190019513 / 5000) (1313073635439 / 20000) := by
  exact
    packedTile8192 65650944 65667328 11 871 8102 26 _ _ (359997 / 20000) (449997 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65667328 :
    ThetaLowerSegment 65667328 65683712 (1313073635439 / 20000) (1313408797301 / 20000) := by
  exact
    packedTile8192 65667328 65683712 11 931 8103 26 _ _ (180001 / 10000) (1800013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65683712 :
    ThetaLowerSegment 65683712 65700096 (1313408797301 / 20000) (131374252379 / 2000) := by
  exact
    packedTile8192 65683712 65700096 11 927 8104 26 _ _ (360007 / 20000) (900019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65700096 :
    ThetaLowerSegment 65700096 65716480 (131374252379 / 2000) (657030927217 / 10000) := by
  exact
    packedTile8192 65700096 65716480 11 887 8105 26 _ _ (90003 / 5000) (1800063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65716480 :
    ThetaLowerSegment 65716480 65732864 (657030927217 / 10000) (131438874987 / 2000) := by
  exact
    packedTile8192 65716480 65732864 11 908 8106 26 _ _ (360017 / 20000) (225011 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65732864 :
    ThetaLowerSegment 65732864 65749248 (131438874987 / 2000) (262944354007 / 4000) := by
  exact
    packedTile8192 65732864 65749248 11 925 8107 26 _ _ (1800109 / 100000) (112507 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65749248 :
    ThetaLowerSegment 65749248 65765632 (262944354007 / 4000) (6575205569033 / 100000) := by
  exact
    packedTile8192 65749248 65765632 11 887 8108 26 _ _ (900067 / 50000) (1800137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65765632 :
    ThetaLowerSegment 65765632 65782016 (6575205569033 / 100000) (3288408355669 / 50000) := by
  exact
    packedTile8192 65765632 65782016 11 895 8109 26 _ _ (1800159 / 100000) (900081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65782016 :
    ThetaLowerSegment 65782016 65798400 (3288408355669 / 50000) (3289228339481 / 50000) := by
  exact
    packedTile8192 65782016 65798400 11 911 8110 26 _ _ (225023 / 12500) (1800187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65798400 :
    ThetaLowerSegment 65798400 65814784 (3289228339481 / 50000) (6580129073123 / 100000) := by
  exact
    packedTile8192 65798400 65814784 11 929 8111 26 _ _ (1800209 / 100000) (450053 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65814784 :
    ThetaLowerSegment 65814784 65831168 (6580129073123 / 100000) (6581803290743 / 100000) := by
  exact
    packedTile8192 65814784 65831168 11 930 8112 26 _ _ (900117 / 50000) (1800237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65831168 :
    ThetaLowerSegment 65831168 65847552 (6581803290743 / 100000) (6583434325397 / 100000) := by
  exact
    packedTile8192 65831168 65847552 11 906 8113 26 _ _ (1800259 / 100000) (900131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65847552 :
    ThetaLowerSegment 65847552 65863936 (6583434325397 / 100000) (6585068983269 / 100000) := by
  exact
    packedTile8192 65847552 65863936 11 908 8114 26 _ _ (450071 / 25000) (1800287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65863936 :
    ThetaLowerSegment 65863936 65880320 (6585068983269 / 100000) (3293359933311 / 50000) := by
  exact
    packedTile8192 65863936 65880320 11 917 8115 26 _ _ (1800309 / 100000) (225039 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65880320 :
    ThetaLowerSegment 65880320 65896704 (3293359933311 / 50000) (3294152080271 / 50000) := by
  exact
    packedTile8192 65880320 65896704 11 880 8116 26 _ _ (900167 / 50000) (1800337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65896704 :
    ThetaLowerSegment 65896704 65913088 (3294152080271 / 50000) (3294998248531 / 50000) := by
  exact
    packedTile8192 65896704 65913088 11 940 8117 26 _ _ (900179 / 50000) (1800361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65913088 :
    ThetaLowerSegment 65913088 65929472 (3294998248531 / 50000) (6591669052869 / 100000) := by
  exact
    packedTile8192 65913088 65929472 11 929 8118 26 _ _ (1800383 / 100000) (900193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65929472 :
    ThetaLowerSegment 65929472 65945856 (6591669052869 / 100000) (6593285819253 / 100000) := by
  exact
    packedTile8192 65929472 65945856 11 898 8119 26 _ _ (225051 / 12500) (1800411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65945856 :
    ThetaLowerSegment 65945856 65962240 (6593285819253 / 100000) (3297457605559 / 50000) := by
  exact
    packedTile8192 65945856 65962240 11 905 8120 26 _ _ (1800433 / 100000) (450109 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65962240 :
    ThetaLowerSegment 65962240 65978624 (3297457605559 / 50000) (1649147859379 / 25000) := by
  exact
    packedTile8192 65962240 65978624 11 931 8121 26 _ _ (900229 / 50000) (1800461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65978624 :
    ThetaLowerSegment 65978624 65995008 (1649147859379 / 25000) (329913114287 / 5000) := by
  exact
    packedTile8192 65978624 65995008 11 928 8122 26 _ _ (1800483 / 100000) (900243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell65995008 :
    ThetaLowerSegment 65995008 66011392 (329913114287 / 5000) (6599956562827 / 100000) := by
  exact
    packedTile8192 65995008 66011392 11 941 8123 26 _ _ (1800507 / 100000) (180051 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66011392 :
    ThetaLowerSegment 66011392 66027776 (6599956562827 / 100000) (6601559036307 / 100000) := by
  exact
    packedTile8192 66011392 66027776 11 890 8124 26 _ _ (450133 / 25000) (360107 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66027776 :
    ThetaLowerSegment 66027776 66044160 (6601559036307 / 100000) (6603193942063 / 100000) := by
  exact
    packedTile8192 66027776 66044160 11 908 8125 26 _ _ (1800557 / 100000) (22507 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66044160 :
    ThetaLowerSegment 66044160 66060544 (6603193942063 / 100000) (6604877486233 / 100000) := by
  exact
    packedTile8192 66044160 66060544 11 935 8126 26 _ _ (900291 / 50000) (360117 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66060544 :
    ThetaLowerSegment 66060544 66076928 (6604877486233 / 100000) (3303255318391 / 50000) := by
  exact
    packedTile8192 66060544 66076928 11 907 8127 26 _ _ (1800607 / 100000) (180061 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66076928 :
    ThetaLowerSegment 66076928 66093312 (3303255318391 / 50000) (660818342391 / 10000) := by
  exact
    packedTile8192 66076928 66093312 11 929 8128 26 _ _ (225079 / 12500) (360127 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66093312 :
    ThetaLowerSegment 66093312 66109696 (660818342391 / 10000) (3304908309451 / 50000) := by
  exact
    packedTile8192 66093312 66109696 11 907 8129 26 _ _ (112541 / 6250) (1800659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66109696 :
    ThetaLowerSegment 66109696 66126080 (3304908309451 / 50000) (6611435431121 / 100000) := by
  exact
    packedTile8192 66109696 66126080 11 899 8130 26 _ _ (1800681 / 100000) (450171 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66126080 :
    ThetaLowerSegment 66126080 66142464 (6611435431121 / 100000) (6613032657343 / 100000) := by
  exact
    packedTile8192 66126080 66142464 11 887 8131 26 _ _ (900353 / 50000) (1800709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66142464 :
    ThetaLowerSegment 66142464 66158848 (6613032657343 / 100000) (1653661077897 / 25000) := by
  exact
    packedTile8192 66142464 66158848 11 895 8132 26 _ _ (1800731 / 100000) (900367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66158848 :
    ThetaLowerSegment 66158848 66175232 (1653661077897 / 25000) (3308191920459 / 50000) := by
  exact
    packedTile8192 66158848 66175232 11 966 8133 26 _ _ (360151 / 20000) (900379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66175232 :
    ThetaLowerSegment 66175232 66191616 (3308191920459 / 50000) (3309011275359 / 50000) := by
  exact
    packedTile8192 66175232 66191616 11 910 8134 26 _ _ (90039 / 5000) (1800783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66191616 :
    ThetaLowerSegment 66191616 66208000 (3309011275359 / 50000) (3309825239219 / 50000) := by
  exact
    packedTile8192 66191616 66208000 11 904 8135 26 _ _ (360161 / 20000) (225101 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66208000 :
    ThetaLowerSegment 66208000 66224384 (3309825239219 / 50000) (1655329061547 / 25000) := by
  exact
    packedTile8192 66208000 66224384 11 925 8136 26 _ _ (180083 / 10000) (1800833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66224384 :
    ThetaLowerSegment 66224384 66240768 (1655329061547 / 25000) (3311491018069 / 50000) := by
  exact
    packedTile8192 66224384 66240768 11 925 8137 26 _ _ (900427 / 50000) (1800857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66240768 :
    ThetaLowerSegment 66240768 66257152 (3311491018069 / 50000) (6624637043939 / 100000) := by
  exact
    packedTile8192 66240768 66257152 11 919 8138 26 _ _ (1800879 / 100000) (900441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66257152 :
    ThetaLowerSegment 66257152 66273536 (6624637043939 / 100000) (1325242206807 / 20000) := by
  exact
    packedTile8192 66257152 66273536 11 874 8139 26 _ _ (225113 / 12500) (1800907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66273536 :
    ThetaLowerSegment 66273536 66289920 (1325242206807 / 20000) (3313918636461 / 50000) := by
  exact
    packedTile8192 66273536 66289920 11 903 8140 26 _ _ (1800929 / 100000) (450233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66289920 :
    ThetaLowerSegment 66289920 66306304 (3313918636461 / 50000) (265181999169 / 4000) := by
  exact
    packedTile8192 66289920 66306304 11 951 8141 26 _ _ (1800953 / 100000) (450239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66306304 :
    ThetaLowerSegment 66306304 66322688 (265181999169 / 4000) (6631237495611 / 100000) := by
  exact
    packedTile8192 66306304 66322688 11 937 8142 26 _ _ (900489 / 50000) (1800981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66322688 :
    ThetaLowerSegment 66322688 66339072 (6631237495611 / 100000) (1326578163273 / 20000) := by
  exact
    packedTile8192 66322688 66339072 11 918 8143 26 _ _ (1801003 / 100000) (900503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66339072 :
    ThetaLowerSegment 66339072 66355456 (1326578163273 / 20000) (6634518944773 / 100000) := by
  exact
    packedTile8192 66339072 66355456 11 904 8144 26 _ _ (1801027 / 100000) (180103 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66355456 :
    ThetaLowerSegment 66355456 66371840 (6634518944773 / 100000) (6636156101041 / 100000) := by
  exact
    packedTile8192 66355456 66371840 11 909 8145 26 _ _ (450263 / 25000) (360211 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66371840 :
    ThetaLowerSegment 66371840 66388224 (6636156101041 / 100000) (414868158637 / 6250) := by
  exact
    packedTile8192 66371840 66388224 11 963 8146 26 _ _ (1801077 / 100000) (45027 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66388224 :
    ThetaLowerSegment 66388224 66404608 (414868158637 / 6250) (3319742256731 / 50000) := by
  exact
    packedTile8192 66388224 66404608 11 885 8147 26 _ _ (900551 / 50000) (360221 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66404608 :
    ThetaLowerSegment 66404608 66420992 (3319742256731 / 50000) (1660280434249 / 25000) := by
  exact
    packedTile8192 66404608 66420992 11 909 8148 26 _ _ (900563 / 50000) (1801129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66420992 :
    ThetaLowerSegment 66420992 66437376 (1660280434249 / 25000) (1660683892073 / 25000) := by
  exact
    packedTile8192 66420992 66437376 11 896 8149 26 _ _ (1801151 / 100000) (900577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66437376 :
    ThetaLowerSegment 66437376 66453760 (1660683892073 / 25000) (1661092308731 / 25000) := by
  exact
    packedTile8192 66437376 66453760 11 907 8150 26 _ _ (225147 / 12500) (1801179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66453760 :
    ThetaLowerSegment 66453760 66470144 (1661092308731 / 25000) (1661502982331 / 25000) := by
  exact
    packedTile8192 66453760 66470144 11 912 8151 26 _ _ (4503 / 250) (1801203 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66470144 :
    ThetaLowerSegment 66470144 66486528 (1661502982331 / 25000) (6647645640399 / 100000) := by
  exact
    packedTile8192 66470144 66486528 11 907 8152 26 _ _ (72049 / 4000) (450307 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66486528 :
    ThetaLowerSegment 66486528 66502912 (6647645640399 / 100000) (6649299186981 / 100000) := by
  exact
    packedTile8192 66486528 66502912 11 918 8153 26 _ _ (1801249 / 100000) (450313 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66502912 :
    ThetaLowerSegment 66502912 66519296 (6649299186981 / 100000) (6650950955239 / 100000) := by
  exact
    packedTile8192 66502912 66519296 11 917 8154 26 _ _ (900637 / 50000) (1801277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66519296 :
    ThetaLowerSegment 66519296 66535680 (6650950955239 / 100000) (3326297770613 / 50000) := by
  exact
    packedTile8192 66519296 66535680 11 913 8155 26 _ _ (1801299 / 100000) (900651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66535680 :
    ThetaLowerSegment 66535680 66552064 (3326297770613 / 50000) (6654196917373 / 100000) := by
  exact
    packedTile8192 66535680 66552064 11 889 8156 26 _ _ (1801323 / 100000) (900663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66552064 :
    ThetaLowerSegment 66552064 66568448 (6654196917373 / 100000) (6655832541357 / 100000) := by
  exact
    packedTile8192 66552064 66568448 11 908 8157 26 _ _ (450337 / 25000) (1801351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66568448 :
    ThetaLowerSegment 66568448 66584832 (6655832541357 / 100000) (3328724186469 / 50000) := by
  exact
    packedTile8192 66568448 66584832 11 897 8158 26 _ _ (1801373 / 100000) (56293 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66584832 :
    ThetaLowerSegment 66584832 66601216 (3328724186469 / 50000) (665913448053 / 10000) := by
  exact
    packedTile8192 66584832 66601216 11 936 8159 26 _ _ (1801397 / 100000) (9007 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66601216 :
    ThetaLowerSegment 66601216 66617600 (665913448053 / 10000) (3330399497229 / 50000) := by
  exact
    packedTile8192 66601216 66617600 11 924 8160 26 _ _ (900711 / 50000) (72057 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66617600 :
    ThetaLowerSegment 66617600 66633984 (3330399497229 / 50000) (1665606425049 / 25000) := by
  exact
    packedTile8192 66617600 66633984 11 903 8161 26 _ _ (900723 / 50000) (1801449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66633984 :
    ThetaLowerSegment 66633984 66650368 (1665606425049 / 25000) (3332028916461 / 50000) := by
  exact
    packedTile8192 66633984 66650368 11 906 8162 26 _ _ (1801471 / 100000) (900737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66650368 :
    ThetaLowerSegment 66650368 66666752 (3332028916461 / 50000) (666574763617 / 10000) := by
  exact
    packedTile8192 66650368 66666752 11 938 8163 26 _ _ (225187 / 12500) (1801499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66666752 :
    ThetaLowerSegment 66666752 66683136 (666574763617 / 10000) (666738161481 / 10000) := by
  exact
    packedTile8192 66666752 66683136 11 907 8164 26 _ _ (22519 / 1250) (1801523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66683136 :
    ThetaLowerSegment 66683136 66699520 (666738161481 / 10000) (666903903621 / 10000) := by
  exact
    packedTile8192 66683136 66699520 11 920 8165 26 _ _ (360309 / 20000) (450387 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66699520 :
    ThetaLowerSegment 66699520 66715904 (666903903621 / 10000) (1334133891231 / 20000) := by
  exact
    packedTile8192 66699520 66715904 11 905 8166 26 _ _ (1801569 / 100000) (450393 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66715904 :
    ThetaLowerSegment 66715904 66732288 (1334133891231 / 20000) (6672274676409 / 100000) := by
  exact
    packedTile8192 66715904 66732288 11 891 8167 26 _ _ (900797 / 50000) (1801597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66732288 :
    ThetaLowerSegment 66732288 66748672 (6672274676409 / 100000) (1334779947169 / 20000) := by
  exact
    packedTile8192 66732288 66748672 11 902 8168 26 _ _ (900809 / 50000) (1801621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66748672 :
    ThetaLowerSegment 66748672 66765056 (1334779947169 / 20000) (6675524817831 / 100000) := by
  exact
    packedTile8192 66748672 66765056 11 902 8169 26 _ _ (1801643 / 100000) (900823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66765056 :
    ThetaLowerSegment 66765056 66781440 (6675524817831 / 100000) (6677182352391 / 100000) := by
  exact
    packedTile8192 66765056 66781440 11 920 8170 26 _ _ (450417 / 25000) (1801671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66781440 :
    ThetaLowerSegment 66781440 66797824 (6677182352391 / 100000) (267152299143 / 4000) := by
  exact
    packedTile8192 66781440 66797824 11 902 8171 26 _ _ (450423 / 25000) (360339 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66797824 :
    ThetaLowerSegment 66797824 66814208 (267152299143 / 4000) (668042001529 / 10000) := by
  exact
    packedTile8192 66797824 66814208 11 895 8172 26 _ _ (1801717 / 100000) (45043 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66814208 :
    ThetaLowerSegment 66814208 66830592 (668042001529 / 10000) (6682028970003 / 100000) := by
  exact
    packedTile8192 66814208 66830592 11 893 8173 26 _ _ (1801741 / 100000) (112609 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66830592 :
    ThetaLowerSegment 66830592 66846976 (6682028970003 / 100000) (6683637947041 / 100000) := by
  exact
    packedTile8192 66830592 66846976 11 893 8174 26 _ _ (900883 / 50000) (1801769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66846976 :
    ThetaLowerSegment 66846976 66863360 (6683637947041 / 100000) (6685329827851 / 100000) := by
  exact
    packedTile8192 66846976 66863360 11 939 8176 26 _ _ (180179 / 10000) (1801793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66863360 :
    ThetaLowerSegment 66863360 66879744 (6685329827851 / 100000) (3343501856993 / 50000) := by
  exact
    packedTile8192 66863360 66879744 11 929 8177 26 _ _ (360363 / 20000) (900909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66879744 :
    ThetaLowerSegment 66879744 66896128 (3343501856993 / 50000) (6688659604027 / 100000) := by
  exact
    packedTile8192 66879744 66896128 11 919 8178 26 _ _ (1801839 / 100000) (900921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66896128 :
    ThetaLowerSegment 66896128 66912512 (6688659604027 / 100000) (6690229027571 / 100000) := by
  exact
    packedTile8192 66896128 66912512 11 871 8179 26 _ _ (225233 / 12500) (1801867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66912512 :
    ThetaLowerSegment 66912512 66928896 (6690229027571 / 100000) (6691881358867 / 100000) := by
  exact
    packedTile8192 66912512 66928896 11 917 8180 26 _ _ (56309 / 3125) (1801891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66928896 :
    ThetaLowerSegment 66928896 66945280 (6691881358867 / 100000) (6693524703523 / 100000) := by
  exact
    packedTile8192 66928896 66945280 11 912 8181 26 _ _ (1801913 / 100000) (450479 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66945280 :
    ThetaLowerSegment 66945280 66961664 (6693524703523 / 100000) (3347572322443 / 50000) := by
  exact
    packedTile8192 66945280 66961664 11 899 8182 26 _ _ (1801937 / 100000) (90097 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66961664 :
    ThetaLowerSegment 66961664 66978048 (3347572322443 / 50000) (3348377799457 / 50000) := by
  exact
    packedTile8192 66961664 66978048 11 894 8183 26 _ _ (900981 / 50000) (360393 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66978048 :
    ThetaLowerSegment 66978048 66994432 (3348377799457 / 50000) (167460831197 / 2500) := by
  exact
    packedTile8192 66978048 66994432 11 931 8184 26 _ _ (900993 / 50000) (1801989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell66994432 :
    ThetaLowerSegment 66994432 67010816 (167460831197 / 2500) (6700053255769 / 100000) := by
  exact
    packedTile8192 66994432 67010816 11 899 8185 26 _ _ (1802011 / 100000) (901007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67010816 :
    ThetaLowerSegment 67010816 67027200 (6700053255769 / 100000) (6701689503549 / 100000) := by
  exact
    packedTile8192 67010816 67027200 11 908 8186 26 _ _ (360407 / 20000) (901019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67027200 :
    ThetaLowerSegment 67027200 67043584 (6701689503549 / 100000) (6703322169003 / 100000) := by
  exact
    packedTile8192 67027200 67043584 11 906 8187 26 _ _ (1802059 / 100000) (901031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67043584 :
    ThetaLowerSegment 67043584 67059968 (6703322169003 / 100000) (6704936836267 / 100000) := by
  exact
    packedTile8192 67043584 67059968 11 896 8188 26 _ _ (450521 / 25000) (1802087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67059968 :
    ThetaLowerSegment 67059968 67076352 (6704936836267 / 100000) (6706580358763 / 100000) := by
  exact
    packedTile8192 67059968 67076352 11 912 8189 26 _ _ (450527 / 25000) (1802111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67076352 :
    ThetaLowerSegment 67076352 67092736 (6706580358763 / 100000) (838526411141 / 12500) := by
  exact
    packedTile8192 67076352 67092736 11 905 8190 26 _ _ (1802133 / 100000) (225267 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67092736 :
    ThetaLowerSegment 67092736 67109120 (838526411141 / 12500) (3354947251883 / 50000) := by
  exact
    packedTile16384 67092736 67109120 11 934 8191 26 _ _ (1802157 / 100000) (22527 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67109120 :
    ThetaLowerSegment 67109120 67125504 (3354947251883 / 50000) (838933926627 / 12500) := by
  exact
    packedTile16384 67109120 67125504 11 875 8192 26 _ _ (901091 / 50000) (360437 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67125504 :
    ThetaLowerSegment 67125504 67141888 (838933926627 / 12500) (671310961827 / 10000) := by
  exact
    packedTile16384 67125504 67141888 11 909 8193 26 _ _ (901103 / 50000) (1802209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67141888 :
    ThetaLowerSegment 67141888 67158272 (671310961827 / 10000) (671472081189 / 10000) := by
  exact
    packedTile16384 67141888 67158272 11 894 8194 26 _ _ (180223 / 10000) (1802233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67158272 :
    ThetaLowerSegment 67158272 67174656 (671472081189 / 10000) (671638609551 / 10000) := by
  exact
    packedTile16384 67158272 67174656 11 924 8195 26 _ _ (360451 / 20000) (901129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67174656 :
    ThetaLowerSegment 67174656 67191040 (671638609551 / 10000) (6718031576237 / 100000) := by
  exact
    packedTile16384 67174656 67191040 11 913 8196 26 _ _ (1802279 / 100000) (901141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67191040 :
    ThetaLowerSegment 67191040 67207424 (6718031576237 / 100000) (6719713125869 / 100000) := by
  exact
    packedTile16384 67191040 67207424 11 933 8197 26 _ _ (56322 / 3125) (1802307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67207424 :
    ThetaLowerSegment 67207424 67223808 (6719713125869 / 100000) (6721319000117 / 100000) := by
  exact
    packedTile16384 67207424 67223808 11 891 8198 26 _ _ (225291 / 12500) (1802331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67223808 :
    ThetaLowerSegment 67223808 67240192 (6721319000117 / 100000) (6722950128677 / 100000) := by
  exact
    packedTile16384 67223808 67240192 11 905 8199 26 _ _ (112647 / 6250) (360471 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67240192 :
    ThetaLowerSegment 67240192 67256576 (6722950128677 / 100000) (3362319477963 / 50000) := by
  exact
    packedTile16384 67240192 67256576 11 937 8200 26 _ _ (1802377 / 100000) (90119 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67256576 :
    ThetaLowerSegment 67256576 67272960 (3362319477963 / 50000) (336312515121 / 5000) := by
  exact
    packedTile16384 67256576 67272960 11 894 8201 26 _ _ (1802401 / 100000) (450601 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67272960 :
    ThetaLowerSegment 67272960 67289344 (336312515121 / 5000) (1345592160749 / 20000) := by
  exact
    packedTile16384 67272960 67289344 11 949 8202 26 _ _ (72097 / 4000) (450607 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67289344 :
    ThetaLowerSegment 67289344 67305728 (1345592160749 / 20000) (1345917322729 / 20000) := by
  exact
    packedTile16384 67289344 67305728 11 902 8203 26 _ _ (36049 / 2000) (1802453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67305728 :
    ThetaLowerSegment 67305728 67322112 (1345917322729 / 20000) (1346254385367 / 20000) := by
  exact
    packedTile16384 67305728 67322112 11 935 8204 26 _ _ (901237 / 50000) (1802477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67322112 :
    ThetaLowerSegment 67322112 67338496 (1346254385367 / 20000) (6732924817501 / 100000) := by
  exact
    packedTile16384 67322112 67338496 11 917 8205 26 _ _ (901249 / 50000) (1802501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67338496 :
    ThetaLowerSegment 67338496 67354880 (6732924817501 / 100000) (6734514642787 / 100000) := by
  exact
    packedTile16384 67338496 67354880 11 882 8206 26 _ _ (1802523 / 100000) (901263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67354880 :
    ThetaLowerSegment 67354880 67371264 (6734514642787 / 100000) (3368080184099 / 50000) := by
  exact
    packedTile16384 67354880 67371264 11 913 8207 26 _ _ (1802547 / 100000) (36051 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67371264 :
    ThetaLowerSegment 67371264 67387648 (3368080184099 / 50000) (1347559060019 / 20000) := by
  exact
    packedTile16384 67371264 67387648 11 907 8208 26 _ _ (1802571 / 100000) (901287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67387648 :
    ThetaLowerSegment 67387648 67404032 (1347559060019 / 20000) (6739448280627 / 100000) := by
  exact
    packedTile16384 67387648 67404032 11 917 8208 26 _ _ (450649 / 25000) (1802599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67404032 :
    ThetaLowerSegment 67404032 67420416 (6739448280627 / 100000) (6741112098887 / 100000) := by
  exact
    packedTile16384 67404032 67420416 11 923 8209 26 _ _ (90131 / 5000) (1802623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67420416 :
    ThetaLowerSegment 67420416 67436800 (6741112098887 / 100000) (1348551222043 / 20000) := by
  exact
    packedTile16384 67420416 67436800 11 912 8210 26 _ _ (450661 / 25000) (1802647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67436800 :
    ThetaLowerSegment 67436800 67453184 (1348551222043 / 20000) (843051144711 / 12500) := by
  exact
    packedTile16384 67436800 67453184 11 917 8211 26 _ _ (1802669 / 100000) (112667 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67453184 :
    ThetaLowerSegment 67453184 67469568 (843051144711 / 12500) (210815514948 / 3125) := by
  exact
    packedTile16384 67453184 67469568 11 936 8212 26 _ _ (1802693 / 100000) (225337 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67469568 :
    ThetaLowerSegment 67469568 67485952 (210815514948 / 3125) (1349542703097 / 20000) := by
  exact
    packedTile16384 67469568 67485952 11 897 8213 26 _ _ (1802717 / 100000) (11267 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67485952 :
    ThetaLowerSegment 67485952 67502336 (1349542703097 / 20000) (6749359418931 / 100000) := by
  exact
    packedTile16384 67485952 67502336 11 913 8214 26 _ _ (901371 / 50000) (360549 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67502336 :
    ThetaLowerSegment 67502336 67518720 (6749359418931 / 100000) (1350197823879 / 20000) := by
  exact
    packedTile16384 67502336 67518720 11 904 8215 26 _ _ (901383 / 50000) (1802769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67518720 :
    ThetaLowerSegment 67518720 67535104 (1350197823879 / 20000) (1350521604963 / 20000) := by
  exact
    packedTile16384 67518720 67535104 11 898 8216 26 _ _ (180279 / 10000) (1802793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67535104 :
    ThetaLowerSegment 67535104 67551488 (1350521604963 / 20000) (54034060797 / 800) := by
  exact
    packedTile16384 67535104 67551488 11 915 8217 26 _ _ (901407 / 50000) (1802817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67551488 :
    ThetaLowerSegment 67551488 67567872 (54034060797 / 800) (3377942781621 / 50000) := by
  exact
    packedTile16384 67551488 67567872 11 903 8218 26 _ _ (1802839 / 100000) (901421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67567872 :
    ThetaLowerSegment 67567872 67584256 (3377942781621 / 50000) (270303282293 / 4000) := by
  exact
    packedTile16384 67567872 67584256 11 941 8219 26 _ _ (1802863 / 100000) (901433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67584256 :
    ThetaLowerSegment 67584256 67600640 (270303282293 / 4000) (1689807023289 / 25000) := by
  exact
    packedTile16384 67584256 67600640 11 913 8220 26 _ _ (1802887 / 100000) (180289 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67600640 :
    ThetaLowerSegment 67600640 67617024 (1689807023289 / 25000) (6760863333433 / 100000) := by
  exact
    packedTile16384 67600640 67617024 11 907 8221 26 _ _ (1802911 / 100000) (901457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67617024 :
    ThetaLowerSegment 67617024 67633408 (6760863333433 / 100000) (6762410252521 / 100000) := by
  exact
    packedTile16384 67617024 67633408 11 858 8222 26 _ _ (225367 / 12500) (1802939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67633408 :
    ThetaLowerSegment 67633408 67649792 (6762410252521 / 100000) (6764085202361 / 100000) := by
  exact
    packedTile16384 67633408 67649792 11 929 8223 26 _ _ (22537 / 1250) (1802963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67649792 :
    ThetaLowerSegment 67649792 67666176 (6764085202361 / 100000) (6765740341673 / 100000) := by
  exact
    packedTile16384 67649792 67666176 11 918 8224 26 _ _ (225373 / 12500) (1802987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67666176 :
    ThetaLowerSegment 67666176 67682560 (6765740341673 / 100000) (6767395503017 / 100000) := by
  exact
    packedTile16384 67666176 67682560 11 918 8225 26 _ _ (56344 / 3125) (1803011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67682560 :
    ThetaLowerSegment 67682560 67698944 (6767395503017 / 100000) (6769012822721 / 100000) := by
  exact
    packedTile16384 67682560 67698944 11 897 8226 26 _ _ (225379 / 12500) (360607 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67698944 :
    ThetaLowerSegment 67698944 67715328 (6769012822721 / 100000) (1692665654969 / 25000) := by
  exact
    packedTile16384 67698944 67715328 11 915 8227 26 _ _ (1803057 / 100000) (90153 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67715328 :
    ThetaLowerSegment 67715328 67731712 (1692665654969 / 25000) (6772334075963 / 100000) := by
  exact
    packedTile16384 67715328 67731712 11 927 8228 26 _ _ (1803081 / 100000) (450771 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67731712 :
    ThetaLowerSegment 67731712 67764480 (6772334075963 / 100000) (3387806961979 / 50000) := by
  exact
    packedTile16384 67731712 67764480 12 1819 8229 26 _ _ (360621 / 20000) (450777 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67764480 :
    ThetaLowerSegment 67764480 67797248 (3387806961979 / 50000) (271153590587 / 4000) := by
  exact
    packedTile16384 67764480 67797248 12 1789 8231 26 _ _ (1803153 / 100000) (450789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67797248 :
    ThetaLowerSegment 67797248 67813632 (271153590587 / 4000) (6780487891303 / 100000) := by
  exact
    packedTile16384 67797248 67813632 11 914 8233 26 _ _ (901601 / 50000) (360641 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67813632 :
    ThetaLowerSegment 67813632 67830016 (6780487891303 / 100000) (6782112597929 / 100000) := by
  exact
    packedTile16384 67813632 67830016 11 901 8234 26 _ _ (901613 / 50000) (1803229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67830016 :
    ThetaLowerSegment 67830016 67846400 (6782112597929 / 100000) (6783742735929 / 100000) := by
  exact
    packedTile16384 67830016 67846400 11 904 8235 26 _ _ (7213 / 400) (1803253 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67846400 :
    ThetaLowerSegment 67846400 67862784 (6783742735929 / 100000) (6785432403667 / 100000) := by
  exact
    packedTile16384 67846400 67862784 11 937 8236 26 _ _ (901637 / 50000) (1803277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67862784 :
    ThetaLowerSegment 67862784 67879168 (6785432403667 / 100000) (6787033732291 / 100000) := by
  exact
    packedTile16384 67862784 67879168 11 888 8237 26 _ _ (901649 / 50000) (1803301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67879168 :
    ThetaLowerSegment 67879168 67895552 (6787033732291 / 100000) (6788667542023 / 100000) := by
  exact
    packedTile16384 67879168 67895552 11 906 8238 26 _ _ (901661 / 50000) (72133 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67895552 :
    ThetaLowerSegment 67895552 67911936 (6788667542023 / 100000) (1358067488269 / 20000) := by
  exact
    packedTile16384 67895552 67911936 11 926 8239 26 _ _ (1803347 / 100000) (36067 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67911936 :
    ThetaLowerSegment 67911936 67928320 (1358067488269 / 20000) (42450034747 / 625) := by
  exact
    packedTile16384 67911936 67928320 11 925 8240 26 _ _ (1803371 / 100000) (901687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67928320 :
    ThetaLowerSegment 67928320 67961088 (42450034747 / 625) (679529134521 / 10000) := by
  exact
    packedTile16384 67928320 67961088 12 1822 8241 26 _ _ (360679 / 20000) (901699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67961088 :
    ThetaLowerSegment 67961088 67993856 (679529134521 / 10000) (3399279591963 / 50000) := by
  exact
    packedTile16384 67961088 67993856 12 1812 8243 26 _ _ (1803443 / 100000) (901723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell67993856 :
    ThetaLowerSegment 67993856 68026624 (3399279591963 / 50000) (212556759021 / 3125) := by
  exact
    packedTile16384 67993856 68026624 12 1806 8245 26 _ _ (1803491 / 100000) (901747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68026624 :
    ThetaLowerSegment 68026624 68059392 (212556759021 / 3125) (272204454177 / 4000) := by
  exact
    packedTile16384 68026624 68059392 12 1827 8247 26 _ _ (1803539 / 100000) (901771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68059392 :
    ThetaLowerSegment 68059392 68092160 (272204454177 / 4000) (272336116101 / 4000) := by
  exact
    packedTile16384 68059392 68092160 12 1825 8249 26 _ _ (450897 / 25000) (1803591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68092160 :
    ThetaLowerSegment 68092160 68124928 (272336116101 / 4000) (6811636821873 / 100000) := by
  exact
    packedTile16384 68092160 68124928 12 1793 8251 26 _ _ (450909 / 25000) (1803639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68124928 :
    ThetaLowerSegment 68124928 68141312 (6811636821873 / 100000) (6813269155893 / 100000) := by
  exact
    packedTile16384 68124928 68141312 11 905 8253 26 _ _ (450921 / 25000) (1803687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68141312 :
    ThetaLowerSegment 68141312 68157696 (6813269155893 / 100000) (6814892493093 / 100000) := by
  exact
    packedTile16384 68141312 68157696 11 900 8254 26 _ _ (450927 / 25000) (1803711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68157696 :
    ThetaLowerSegment 68157696 68174080 (6814892493093 / 100000) (6816523066821 / 100000) := by
  exact
    packedTile16384 68157696 68174080 11 904 8255 26 _ _ (450933 / 25000) (360747 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68174080 :
    ThetaLowerSegment 68174080 68190464 (6816523066821 / 100000) (6818132017173 / 100000) := by
  exact
    packedTile16384 68174080 68190464 11 892 8256 26 _ _ (450939 / 25000) (1803759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68190464 :
    ThetaLowerSegment 68190464 68206848 (6818132017173 / 100000) (6819804121233 / 100000) := by
  exact
    packedTile16384 68190464 68206848 11 927 8257 26 _ _ (90189 / 5000) (1803783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68206848 :
    ThetaLowerSegment 68206848 68223232 (6819804121233 / 100000) (1364292002661 / 20000) := by
  exact
    packedTile16384 68206848 68223232 11 918 8258 26 _ _ (450951 / 25000) (1803807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68223232 :
    ThetaLowerSegment 68223232 68239616 (1364292002661 / 20000) (272924420637 / 4000) := by
  exact
    packedTile16384 68223232 68239616 11 915 8259 26 _ _ (450957 / 25000) (1803831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68239616 :
    ThetaLowerSegment 68239616 68272384 (272924420637 / 4000) (6826409761233 / 100000) := by
  exact
    packedTile16384 68239616 68272384 12 1829 8260 26 _ _ (450963 / 25000) (360771 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68272384 :
    ThetaLowerSegment 68272384 68305152 (6826409761233 / 100000) (6829669408533 / 100000) := by
  exact
    packedTile16384 68272384 68305152 12 1807 8262 26 _ _ (18039 / 1000) (1803903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68305152 :
    ThetaLowerSegment 68305152 68337920 (6829669408533 / 100000) (6832894867557 / 100000) := by
  exact
    packedTile16384 68305152 68337920 12 1788 8264 26 _ _ (450987 / 25000) (1803951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68337920 :
    ThetaLowerSegment 68337920 68354304 (6832894867557 / 100000) (6834558151869 / 100000) := by
  exact
    packedTile16384 68337920 68354304 11 922 8266 26 _ _ (450999 / 25000) (1803999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68354304 :
    ThetaLowerSegment 68354304 68370688 (6834558151869 / 100000) (6836129453289 / 100000) := by
  exact
    packedTile16384 68354304 68370688 11 871 8267 26 _ _ (90201 / 5000) (1804023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68370688 :
    ThetaLowerSegment 68370688 68387072 (6836129453289 / 100000) (6837747680757 / 100000) := by
  exact
    packedTile16384 68370688 68387072 11 897 8268 26 _ _ (451011 / 25000) (1804047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68387072 :
    ThetaLowerSegment 68387072 68403456 (6837747680757 / 100000) (6839430876201 / 100000) := by
  exact
    packedTile16384 68387072 68403456 11 933 8269 26 _ _ (451017 / 25000) (1804071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68403456 :
    ThetaLowerSegment 68403456 68419840 (6839430876201 / 100000) (6841081620381 / 100000) := by
  exact
    packedTile16384 68403456 68419840 11 915 8270 26 _ _ (451023 / 25000) (360819 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68419840 :
    ThetaLowerSegment 68419840 68436224 (6841081620381 / 100000) (6842683675389 / 100000) := by
  exact
    packedTile16384 68419840 68436224 11 888 8271 26 _ _ (451029 / 25000) (1804119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68436224 :
    ThetaLowerSegment 68436224 68452608 (6842683675389 / 100000) (6844267710309 / 100000) := by
  exact
    packedTile16384 68436224 68452608 11 878 8272 26 _ _ (90207 / 5000) (1804143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68452608 :
    ThetaLowerSegment 68452608 68468992 (6844267710309 / 100000) (6845987078601 / 100000) := by
  exact
    packedTile16384 68452608 68468992 11 953 8273 26 _ _ (451041 / 25000) (1804167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68468992 :
    ThetaLowerSegment 68468992 68485376 (6845987078601 / 100000) (6847637910621 / 100000) := by
  exact
    packedTile16384 68468992 68485376 11 915 8274 26 _ _ (451047 / 25000) (1804191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68485376 :
    ThetaLowerSegment 68485376 68501760 (6847637910621 / 100000) (6849297785661 / 100000) := by
  exact
    packedTile16384 68485376 68501760 11 920 8275 26 _ _ (451053 / 25000) (360843 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68501760 :
    ThetaLowerSegment 68501760 68518144 (6849297785661 / 100000) (3425459896463 / 50000) := by
  exact
    packedTile16384 68501760 68518144 11 899 8276 26 _ _ (360847 / 20000) (902119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68518144 :
    ThetaLowerSegment 68518144 68534528 (3425459896463 / 50000) (3426271813013 / 50000) := by
  exact
    packedTile16384 68518144 68534528 11 900 8277 26 _ _ (1804259 / 100000) (902131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68534528 :
    ThetaLowerSegment 68534528 68550912 (3426271813013 / 50000) (1370827361583 / 20000) := by
  exact
    packedTile16384 68534528 68550912 11 883 8278 26 _ _ (1804283 / 100000) (902143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68550912 :
    ThetaLowerSegment 68550912 68567296 (1370827361583 / 20000) (342789387441 / 5000) := by
  exact
    packedTile16384 68550912 68567296 11 915 8279 26 _ _ (1804307 / 100000) (180431 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68567296 :
    ThetaLowerSegment 68567296 68583680 (342789387441 / 5000) (428590032251 / 6250) := by
  exact
    packedTile16384 68567296 68583680 11 916 8280 26 _ _ (1804331 / 100000) (902167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68583680 :
    ThetaLowerSegment 68583680 68600064 (428590032251 / 6250) (214346440243 / 3125) := by
  exact
    packedTile16384 68583680 68600064 11 912 8281 26 _ _ (360871 / 20000) (902179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68600064 :
    ThetaLowerSegment 68600064 68616448 (214346440243 / 3125) (3430345992543 / 50000) := by
  exact
    packedTile16384 68600064 68616448 11 890 8282 26 _ _ (1804379 / 100000) (902191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68616448 :
    ThetaLowerSegment 68616448 68632832 (3430345992543 / 50000) (6862317752189 / 100000) := by
  exact
    packedTile16384 68616448 68632832 11 901 8283 26 _ _ (1804403 / 100000) (902203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68632832 :
    ThetaLowerSegment 68632832 68649216 (6862317752189 / 100000) (1372787625527 / 20000) := by
  exact
    packedTile16384 68632832 68649216 11 898 8284 26 _ _ (1804427 / 100000) (180443 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68649216 :
    ThetaLowerSegment 68649216 68665600 (1372787625527 / 20000) (6865630702673 / 100000) := by
  exact
    packedTile16384 68649216 68665600 11 938 8285 26 _ _ (1804451 / 100000) (902227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68665600 :
    ThetaLowerSegment 68665600 68681984 (6865630702673 / 100000) (6867247511377 / 100000) := by
  exact
    packedTile16384 68665600 68681984 11 896 8286 26 _ _ (902237 / 50000) (1804477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68681984 :
    ThetaLowerSegment 68681984 68698368 (6867247511377 / 100000) (6868866146083 / 100000) := by
  exact
    packedTile16384 68681984 68698368 11 897 8287 26 _ _ (902249 / 50000) (1804501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68698368 :
    ThetaLowerSegment 68698368 68714752 (6868866146083 / 100000) (6870551569631 / 100000) := by
  exact
    packedTile16384 68698368 68714752 11 934 8288 26 _ _ (902261 / 50000) (72181 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68714752 :
    ThetaLowerSegment 68714752 68731136 (6870551569631 / 100000) (1374436575843 / 20000) := by
  exact
    packedTile16384 68714752 68731136 11 904 8289 26 _ _ (902273 / 50000) (1804549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68731136 :
    ThetaLowerSegment 68731136 68747520 (1374436575843 / 20000) (1374758150217 / 20000) := by
  exact
    packedTile16384 68731136 68747520 11 891 8290 26 _ _ (180457 / 10000) (1804573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68747520 :
    ThetaLowerSegment 68747520 68763904 (1374758150217 / 20000) (1375081172543 / 20000) := by
  exact
    packedTile16384 68747520 68763904 11 895 8291 26 _ _ (902297 / 50000) (1804597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68763904 :
    ThetaLowerSegment 68763904 68780288 (1375081172543 / 20000) (3438532152869 / 50000) := by
  exact
    packedTile16384 68763904 68780288 11 919 8292 26 _ _ (1804617 / 100000) (90231 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68780288 :
    ThetaLowerSegment 68780288 68796672 (3438532152869 / 50000) (1375743832307 / 20000) := by
  exact
    packedTile16384 68780288 68796672 11 917 8293 26 _ _ (1804641 / 100000) (451161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68796672 :
    ThetaLowerSegment 68796672 68813056 (1375743832307 / 20000) (688026215011 / 10000) := by
  exact
    packedTile16384 68796672 68813056 11 855 8294 26 _ _ (360933 / 20000) (451167 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68813056 :
    ThetaLowerSegment 68813056 68829440 (688026215011 / 10000) (6881862909253 / 100000) := by
  exact
    packedTile16384 68813056 68829440 11 887 8295 26 _ _ (1804689 / 100000) (451173 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68829440 :
    ThetaLowerSegment 68829440 68845824 (6881862909253 / 100000) (172088938369 / 2500) := by
  exact
    packedTile16384 68829440 68845824 11 939 8296 26 _ _ (1804713 / 100000) (451179 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68845824 :
    ThetaLowerSegment 68845824 68862208 (172088938369 / 2500) (6885198040693 / 100000) := by
  exact
    packedTile16384 68845824 68862208 11 909 8297 26 _ _ (1804737 / 100000) (90237 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68862208 :
    ThetaLowerSegment 68862208 68878592 (6885198040693 / 100000) (6886849396093 / 100000) := by
  exact
    packedTile16384 68862208 68878592 11 915 8298 26 _ _ (45119 / 2500) (1804763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68878592 :
    ThetaLowerSegment 68878592 68894976 (6886849396093 / 100000) (6888522430861 / 100000) := by
  exact
    packedTile16384 68878592 68894976 11 927 8299 26 _ _ (112799 / 6250) (1804787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68894976 :
    ThetaLowerSegment 68894976 68911360 (6888522430861 / 100000) (275604643053 / 4000) := by
  exact
    packedTile16384 68894976 68911360 11 883 8300 26 _ _ (225601 / 12500) (1804811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68911360 :
    ThetaLowerSegment 68911360 68927744 (275604643053 / 4000) (6891753058949 / 100000) := by
  exact
    packedTile16384 68911360 68927744 11 907 8301 26 _ _ (56401 / 3125) (360967 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68927744 :
    ThetaLowerSegment 68927744 68944128 (6891753058949 / 100000) (6893352160479 / 100000) := by
  exact
    packedTile16384 68927744 68944128 11 886 8302 26 _ _ (360971 / 20000) (902429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68944128 :
    ThetaLowerSegment 68944128 68960512 (6893352160479 / 100000) (6894987380853 / 100000) := by
  exact
    packedTile16384 68944128 68960512 11 906 8303 26 _ _ (1804879 / 100000) (902441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68960512 :
    ThetaLowerSegment 68960512 68976896 (6894987380853 / 100000) (6896651501419 / 100000) := by
  exact
    packedTile16384 68960512 68976896 11 922 8304 26 _ _ (1804903 / 100000) (902453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68976896 :
    ThetaLowerSegment 68976896 68993280 (6896651501419 / 100000) (3449153309739 / 50000) := by
  exact
    packedTile16384 68976896 68993280 11 917 8305 26 _ _ (1804927 / 100000) (180493 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell68993280 :
    ThetaLowerSegment 68993280 69009664 (3449153309739 / 50000) (3450007051089 / 50000) := by
  exact
    packedTile16384 68993280 69009664 11 946 8306 26 _ _ (36099 / 2000) (1804953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69009664 :
    ThetaLowerSegment 69009664 69026048 (3450007051089 / 50000) (3450801239649 / 50000) := by
  exact
    packedTile16384 69009664 69026048 11 880 8307 26 _ _ (902487 / 50000) (1804977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69026048 :
    ThetaLowerSegment 69026048 69042432 (3450801239649 / 50000) (3451609878753 / 50000) := by
  exact
    packedTile16384 69026048 69042432 11 896 8308 26 _ _ (902499 / 50000) (1805001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69042432 :
    ThetaLowerSegment 69042432 69058816 (3451609878753 / 50000) (3452438383851 / 50000) := by
  exact
    packedTile16384 69042432 69058816 11 918 8309 26 _ _ (902511 / 50000) (72201 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69058816 :
    ThetaLowerSegment 69058816 69075200 (3452438383851 / 50000) (3453250654101 / 50000) := by
  exact
    packedTile16384 69058816 69075200 11 900 8310 26 _ _ (361009 / 20000) (225631 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69075200 :
    ThetaLowerSegment 69075200 69091584 (3453250654101 / 50000) (1727037785317 / 25000) := by
  exact
    packedTile16384 69075200 69091584 11 914 8311 26 _ _ (1805069 / 100000) (112817 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69091584 :
    ThetaLowerSegment 69091584 69107968 (1727037785317 / 25000) (431858275171 / 6250) := by
  exact
    packedTile16384 69091584 69107968 11 876 8312 26 _ _ (1805093 / 100000) (225637 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69107968 :
    ThetaLowerSegment 69107968 69124352 (431858275171 / 6250) (3455701970539 / 50000) := by
  exact
    packedTile16384 69107968 69124352 11 926 8313 26 _ _ (1805117 / 100000) (11282 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69124352 :
    ThetaLowerSegment 69124352 69140736 (3455701970539 / 50000) (3456542263209 / 50000) := by
  exact
    packedTile16384 69124352 69140736 11 931 8314 26 _ _ (90257 / 5000) (1805143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69140736 :
    ThetaLowerSegment 69140736 69157120 (3456542263209 / 50000) (691466043459 / 10000) := by
  exact
    packedTile16384 69140736 69157120 11 873 8315 26 _ _ (451291 / 25000) (1805167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69157120 :
    ThetaLowerSegment 69157120 69173504 (691466043459 / 10000) (691630315567 / 10000) := by
  exact
    packedTile16384 69157120 69173504 11 910 8316 26 _ _ (451297 / 25000) (1805191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69173504 :
    ThetaLowerSegment 69173504 69189888 (691630315567 / 10000) (3458960312363 / 50000) := by
  exact
    packedTile16384 69173504 69189888 11 896 8317 26 _ _ (1805211 / 100000) (902607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69189888 :
    ThetaLowerSegment 69189888 69206272 (3458960312363 / 50000) (1729889041909 / 25000) := by
  exact
    packedTile16384 69189888 69206272 11 906 8318 26 _ _ (361047 / 20000) (902619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69206272 :
    ThetaLowerSegment 69206272 69222656 (1729889041909 / 25000) (1730304251479 / 25000) := by
  exact
    packedTile16384 69206272 69222656 11 920 8319 26 _ _ (1805259 / 100000) (902631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69222656 :
    ThetaLowerSegment 69222656 69239040 (1730304251479 / 25000) (3461389287423 / 50000) := by
  exact
    packedTile16384 69222656 69239040 11 865 8320 26 _ _ (902641 / 50000) (361057 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69239040 :
    ThetaLowerSegment 69239040 69255424 (3461389287423 / 50000) (216387661111 / 3125) := by
  exact
    packedTile16384 69239040 69255424 11 901 8320 26 _ _ (902653 / 50000) (1805309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69255424 :
    ThetaLowerSegment 69255424 69271808 (216387661111 / 3125) (3462992409651 / 50000) := by
  exact
    packedTile16384 69255424 69271808 11 875 8321 26 _ _ (180533 / 10000) (1805333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69271808 :
    ThetaLowerSegment 69271808 69288192 (3462992409651 / 50000) (865957974699 / 12500) := by
  exact
    packedTile16384 69271808 69288192 11 930 8322 26 _ _ (1805353 / 100000) (451339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69288192 :
    ThetaLowerSegment 69288192 69304576 (865957974699 / 12500) (6929326549809 / 100000) := by
  exact
    packedTile16384 69288192 69304576 11 921 8323 26 _ _ (1805377 / 100000) (90269 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69304576 :
    ThetaLowerSegment 69304576 69320960 (6929326549809 / 100000) (1732737401327 / 25000) := by
  exact
    packedTile16384 69304576 69320960 11 899 8324 26 _ _ (1805401 / 100000) (451351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69320960 :
    ThetaLowerSegment 69320960 69337344 (1732737401327 / 25000) (1733155808339 / 25000) := by
  exact
    packedTile16384 69320960 69337344 11 927 8325 26 _ _ (112839 / 6250) (1805427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69337344 :
    ThetaLowerSegment 69337344 69353728 (1733155808339 / 25000) (1733568804569 / 25000) := by
  exact
    packedTile16384 69337344 69353728 11 915 8326 26 _ _ (225681 / 12500) (1805451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69353728 :
    ThetaLowerSegment 69353728 69370112 (1733568804569 / 25000) (1733983611761 / 25000) := by
  exact
    packedTile16384 69353728 69370112 11 919 8327 26 _ _ (56421 / 3125) (72219 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69370112 :
    ThetaLowerSegment 69370112 69386496 (1733983611761 / 25000) (6937568420019 / 100000) := by
  exact
    packedTile16384 69370112 69386496 11 905 8328 26 _ _ (361099 / 20000) (902749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69386496 :
    ThetaLowerSegment 69386496 69402880 (6937568420019 / 100000) (6939287274107 / 100000) := by
  exact
    packedTile16384 69386496 69402880 11 952 8329 26 _ _ (1805519 / 100000) (902761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69402880 :
    ThetaLowerSegment 69402880 69419264 (6939287274107 / 100000) (1388187507899 / 20000) := by
  exact
    packedTile16384 69402880 69419264 11 914 8330 26 _ _ (902771 / 50000) (361109 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69419264 :
    ThetaLowerSegment 69419264 69435648 (1388187507899 / 20000) (1388507093081 / 20000) := by
  exact
    packedTile16384 69419264 69435648 11 885 8331 26 _ _ (902783 / 50000) (1805569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69435648 :
    ThetaLowerSegment 69435648 69452032 (1388507093081 / 20000) (277769164353 / 4000) := by
  exact
    packedTile16384 69435648 69452032 11 938 8332 26 _ _ (180559 / 10000) (1805593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69452032 :
    ThetaLowerSegment 69452032 69468416 (277769164353 / 4000) (1736468505567 / 25000) := by
  exact
    packedTile16384 69452032 69468416 11 911 8333 26 _ _ (1805613 / 100000) (112851 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69468416 :
    ThetaLowerSegment 69468416 69484800 (1736468505567 / 25000) (6947497289931 / 100000) := by
  exact
    packedTile16384 69468416 69484800 11 899 8334 26 _ _ (1805637 / 100000) (45141 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69484800 :
    ThetaLowerSegment 69484800 69501184 (6947497289931 / 100000) (6949158497131 / 100000) := by
  exact
    packedTile16384 69484800 69501184 11 920 8335 26 _ _ (90283 / 5000) (1805663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69501184 :
    ThetaLowerSegment 69501184 69517568 (6949158497131 / 100000) (6950780001363 / 100000) := by
  exact
    packedTile16384 69501184 69517568 11 898 8336 26 _ _ (451421 / 25000) (1805687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69517568 :
    ThetaLowerSegment 69517568 69533952 (6950780001363 / 100000) (1390487889403 / 20000) := by
  exact
    packedTile16384 69517568 69533952 11 919 8337 26 _ _ (451427 / 25000) (1805711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69533952 :
    ThetaLowerSegment 69533952 69550336 (1390487889403 / 20000) (6954079050763 / 100000) := by
  exact
    packedTile16384 69533952 69550336 11 908 8338 26 _ _ (1805731 / 100000) (902867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69550336 :
    ThetaLowerSegment 69550336 69566720 (6954079050763 / 100000) (6955780071973 / 100000) := by
  exact
    packedTile16384 69550336 69566720 11 942 8339 26 _ _ (361151 / 20000) (902879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69566720 :
    ThetaLowerSegment 69566720 69599488 (6955780071973 / 100000) (6959030472373 / 100000) := by
  exact
    packedTile16384 69566720 69599488 12 1800 8340 26 _ _ (902889 / 50000) (1805781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69599488 :
    ThetaLowerSegment 69599488 69615872 (6959030472373 / 100000) (6960644879923 / 100000) := by
  exact
    packedTile16384 69599488 69615872 11 894 8342 26 _ _ (72233 / 4000) (451457 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69615872 :
    ThetaLowerSegment 69615872 69632256 (6960644879923 / 100000) (6962270144023 / 100000) := by
  exact
    packedTile16384 69615872 69632256 11 900 8343 26 _ _ (1805849 / 100000) (451463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69632256 :
    ThetaLowerSegment 69632256 69648640 (6962270144023 / 100000) (1392790282171 / 20000) := by
  exact
    packedTile16384 69632256 69648640 11 931 8344 26 _ _ (112867 / 6250) (14447 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69648640 :
    ThetaLowerSegment 69648640 69665024 (1392790282171 / 20000) (6965609223383 / 100000) := by
  exact
    packedTile16384 69648640 69665024 11 918 8345 26 _ _ (225737 / 12500) (1805899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69665024 :
    ThetaLowerSegment 69665024 69697792 (6965609223383 / 100000) (3484452512779 / 50000) := by
  exact
    packedTile16384 69665024 69697792 12 1825 8346 26 _ _ (1805919 / 100000) (902961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69697792 :
    ThetaLowerSegment 69697792 69730560 (3484452512779 / 50000) (3486104971669 / 50000) := by
  exact
    packedTile16384 69697792 69730560 12 1830 8348 26 _ _ (902983 / 50000) (1805969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69730560 :
    ThetaLowerSegment 69730560 69763328 (3486104971669 / 50000) (871939368391 / 12500) := by
  exact
    packedTile16384 69730560 69763328 12 1830 8350 26 _ _ (1806013 / 100000) (56438 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69763328 :
    ThetaLowerSegment 69763328 69796096 (871939368391 / 12500) (872348440981 / 12500) := by
  exact
    packedTile16384 69763328 69796096 12 1812 8352 26 _ _ (90303 / 5000) (1806063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69796096 :
    ThetaLowerSegment 69796096 69828864 (872348440981 / 12500) (6982047550983 / 100000) := by
  exact
    packedTile16384 69796096 69828864 12 1805 8354 26 _ _ (1806107 / 100000) (180611 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69828864 :
    ThetaLowerSegment 69828864 69861632 (6982047550983 / 100000) (1397053584713 / 20000) := by
  exact
    packedTile16384 69828864 69861632 12 1783 8356 26 _ _ (903077 / 50000) (1806157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69861632 :
    ThetaLowerSegment 69861632 69894400 (1397053584713 / 20000) (873567369197 / 12500) := by
  exact
    packedTile16384 69861632 69894400 12 1811 8358 26 _ _ (1806201 / 100000) (451551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69894400 :
    ThetaLowerSegment 69894400 69927168 (873567369197 / 12500) (436987451951 / 6250) := by
  exact
    packedTile16384 69894400 69927168 12 1805 8360 26 _ _ (225781 / 12500) (1806251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69927168 :
    ThetaLowerSegment 69927168 69943552 (436987451951 / 6250) (6993441153371 / 100000) := by
  exact
    packedTile16384 69927168 69943552 11 909 8362 26 _ _ (361259 / 20000) (903149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69943552 :
    ThetaLowerSegment 69943552 69959936 (6993441153371 / 100000) (6995066839571 / 100000) := by
  exact
    packedTile16384 69943552 69959936 11 900 8363 26 _ _ (903159 / 50000) (1806321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69959936 :
    ThetaLowerSegment 69959936 69976320 (6995066839571 / 100000) (279866762597 / 4000) := by
  exact
    packedTile16384 69959936 69976320 11 887 8364 26 _ _ (903171 / 50000) (361269 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69976320 :
    ThetaLowerSegment 69976320 69992704 (279866762597 / 4000) (1399650288133 / 20000) := by
  exact
    packedTile16384 69976320 69992704 11 876 8365 26 _ _ (361273 / 20000) (56449 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell69992704 :
    ThetaLowerSegment 69992704 70009088 (1399650288133 / 20000) (3499939498577 / 50000) := by
  exact
    packedTile16384 69992704 70009088 11 901 8366 26 _ _ (1806389 / 100000) (225799 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70009088 :
    ThetaLowerSegment 70009088 70025472 (3499939498577 / 50000) (3500781286569 / 50000) := by
  exact
    packedTile16384 70009088 70025472 11 932 8367 26 _ _ (451603 / 25000) (361283 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70025472 :
    ThetaLowerSegment 70025472 70041856 (3500781286569 / 50000) (7003182945333 / 100000) := by
  exact
    packedTile16384 70025472 70041856 11 897 8368 26 _ _ (361287 / 20000) (903219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70041856 :
    ThetaLowerSegment 70041856 70058240 (7003182945333 / 100000) (7004830435941 / 100000) := by
  exact
    packedTile16384 70041856 70058240 11 912 8369 26 _ _ (1806459 / 100000) (903231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70058240 :
    ThetaLowerSegment 70058240 70074624 (7004830435941 / 100000) (7006438204921 / 100000) := by
  exact
    packedTile16384 70058240 70074624 11 890 8370 26 _ _ (903241 / 50000) (361297 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70074624 :
    ThetaLowerSegment 70074624 70091008 (7006438204921 / 100000) (7008067673333 / 100000) := by
  exact
    packedTile16384 70074624 70091008 11 902 8371 26 _ _ (903253 / 50000) (1806509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70091008 :
    ThetaLowerSegment 70091008 70107392 (7008067673333 / 100000) (7009758584477 / 100000) := by
  exact
    packedTile16384 70091008 70107392 11 936 8372 26 _ _ (1806529 / 100000) (451633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70107392 :
    ThetaLowerSegment 70107392 70123776 (7009758584477 / 100000) (7011366415757 / 100000) := by
  exact
    packedTile16384 70107392 70123776 11 890 8373 26 _ _ (225819 / 12500) (361311 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70123776 :
    ThetaLowerSegment 70123776 70140160 (7011366415757 / 100000) (7012981494701 / 100000) := by
  exact
    packedTile16384 70123776 70140160 11 894 8373 26 _ _ (112911 / 6250) (1806579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70140160 :
    ThetaLowerSegment 70140160 70156544 (7012981494701 / 100000) (17536523101 / 250) := by
  exact
    packedTile16384 70140160 70156544 11 901 8374 26 _ _ (1806599 / 100000) (903301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70156544 :
    ThetaLowerSegment 70156544 70172928 (17536523101 / 250) (3508138376253 / 50000) := by
  exact
    packedTile16384 70156544 70172928 11 923 8375 26 _ _ (903311 / 50000) (14453 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70172928 :
    ThetaLowerSegment 70172928 70189312 (3508138376253 / 50000) (3508976659997 / 50000) := by
  exact
    packedTile16384 70172928 70189312 11 928 8376 26 _ _ (903323 / 50000) (1806649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70189312 :
    ThetaLowerSegment 70189312 70205696 (3508976659997 / 50000) (3509786047709 / 50000) := by
  exact
    packedTile16384 70189312 70205696 11 896 8377 26 _ _ (1806669 / 100000) (112917 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70205696 :
    ThetaLowerSegment 70205696 70222080 (3509786047709 / 50000) (7021152951793 / 100000) := by
  exact
    packedTile16384 70205696 70222080 11 875 8378 26 _ _ (1806693 / 100000) (225837 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70222080 :
    ThetaLowerSegment 70222080 70238464 (7021152951793 / 100000) (7022829584241 / 100000) := by
  exact
    packedTile16384 70222080 70238464 11 928 8379 26 _ _ (451679 / 25000) (1806719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70238464 :
    ThetaLowerSegment 70238464 70254848 (7022829584241 / 100000) (7024506238033 / 100000) := by
  exact
    packedTile16384 70238464 70254848 11 928 8380 26 _ _ (1806739 / 100000) (903371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70254848 :
    ThetaLowerSegment 70254848 70271232 (7024506238033 / 100000) (7026154004977 / 100000) := by
  exact
    packedTile16384 70254848 70271232 11 912 8381 26 _ _ (903381 / 50000) (361353 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70271232 :
    ThetaLowerSegment 70271232 70287616 (7026154004977 / 100000) (7027774692019 / 100000) := by
  exact
    packedTile16384 70271232 70287616 11 897 8382 26 _ _ (903393 / 50000) (1806789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70287616 :
    ThetaLowerSegment 70287616 70304000 (7027774692019 / 100000) (7029458638007 / 100000) := by
  exact
    packedTile16384 70287616 70304000 11 932 8383 26 _ _ (1806809 / 100000) (451703 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70304000 :
    ThetaLowerSegment 70304000 70320384 (7029458638007 / 100000) (7031090207303 / 100000) := by
  exact
    packedTile16384 70304000 70320384 11 903 8384 26 _ _ (112927 / 6250) (361367 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70320384 :
    ThetaLowerSegment 70320384 70336768 (7031090207303 / 100000) (7032723605127 / 100000) := by
  exact
    packedTile16384 70320384 70336768 11 904 8385 26 _ _ (225857 / 12500) (1806859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70336768 :
    ThetaLowerSegment 70336768 70353152 (7032723605127 / 100000) (7034367865017 / 100000) := by
  exact
    packedTile16384 70336768 70353152 11 910 8386 26 _ _ (1806879 / 100000) (903441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70353152 :
    ThetaLowerSegment 70353152 70369536 (7034367865017 / 100000) (7036003111327 / 100000) := by
  exact
    packedTile16384 70353152 70369536 11 905 8387 26 _ _ (903451 / 50000) (361381 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70369536 :
    ThetaLowerSegment 70369536 70385920 (7036003111327 / 100000) (7037613082393 / 100000) := by
  exact
    packedTile16384 70369536 70385920 11 891 8388 26 _ _ (903463 / 50000) (1806929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70385920 :
    ThetaLowerSegment 70385920 70402304 (7037613082393 / 100000) (7039275475473 / 100000) := by
  exact
    packedTile16384 70385920 70402304 11 920 8389 26 _ _ (1806949 / 100000) (225869 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70402304 :
    ThetaLowerSegment 70402304 70418688 (7039275475473 / 100000) (1408193360253 / 20000) := by
  exact
    packedTile16384 70402304 70418688 11 936 8390 26 _ _ (451743 / 25000) (72279 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70418688 :
    ThetaLowerSegment 70418688 70451456 (1408193360253 / 20000) (1408851829231 / 20000) := by
  exact
    packedTile16384 70418688 70451456 12 1822 8391 26 _ _ (361399 / 20000) (903499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70451456 :
    ThetaLowerSegment 70451456 70484224 (1408851829231 / 20000) (7047551576679 / 100000) := by
  exact
    packedTile16384 70451456 70484224 12 1822 8393 26 _ _ (903521 / 50000) (361409 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70484224 :
    ThetaLowerSegment 70484224 70516992 (7047551576679 / 100000) (7050820598871 / 100000) := by
  exact
    packedTile16384 70484224 70516992 12 1809 8395 26 _ _ (112943 / 6250) (1807091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70516992 :
    ThetaLowerSegment 70516992 70549760 (7050820598871 / 100000) (3527070152933 / 50000) := by
  exact
    packedTile16384 70516992 70549760 12 1837 8397 26 _ _ (361427 / 20000) (903569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70549760 :
    ThetaLowerSegment 70549760 70582528 (3527070152933 / 50000) (3528714687643 / 50000) := by
  exact
    packedTile16384 70549760 70582528 12 1820 8399 26 _ _ (1807181 / 100000) (112949 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70582528 :
    ThetaLowerSegment 70582528 70615296 (3528714687643 / 50000) (3530362879579 / 50000) := by
  exact
    packedTile16384 70582528 70615296 12 1824 8401 26 _ _ (451807 / 25000) (1807231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70615296 :
    ThetaLowerSegment 70615296 70648064 (3530362879579 / 50000) (1765963537613 / 25000) := by
  exact
    packedTile16384 70615296 70648064 12 1731 8403 26 _ _ (903637 / 50000) (1807277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70648064 :
    ThetaLowerSegment 70648064 70664448 (1765963537613 / 25000) (7065515078451 / 100000) := by
  exact
    packedTile16384 70648064 70664448 11 919 8405 26 _ _ (1807321 / 100000) (451831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70664448 :
    ThetaLowerSegment 70664448 70680832 (7065515078451 / 100000) (7067168798211 / 100000) := by
  exact
    packedTile16384 70664448 70680832 11 915 8406 26 _ _ (112959 / 6250) (1807347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70680832 :
    ThetaLowerSegment 70680832 70713600 (7067168798211 / 100000) (3535201088887 / 50000) := by
  exact
    packedTile16384 70680832 70713600 12 1789 8407 26 _ _ (1807367 / 100000) (180737 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70713600 :
    ThetaLowerSegment 70713600 70729984 (3535201088887 / 50000) (7072081264451 / 100000) := by
  exact
    packedTile16384 70713600 70729984 11 929 8409 26 _ _ (1807413 / 100000) (225927 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70729984 :
    ThetaLowerSegment 70729984 70762752 (7072081264451 / 100000) (3537684496177 / 50000) := by
  exact
    packedTile16384 70729984 70762752 12 1819 8410 26 _ _ (1807437 / 100000) (22593 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70762752 :
    ThetaLowerSegment 70762752 70795520 (3537684496177 / 50000) (35392768887 / 500) := by
  exact
    packedTile16384 70762752 70795520 12 1762 8412 26 _ _ (1807483 / 100000) (903743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70795520 :
    ThetaLowerSegment 70795520 70811904 (35392768887 / 500) (7080175130913 / 100000) := by
  exact
    packedTile16384 70795520 70811904 11 897 8414 26 _ _ (1807529 / 100000) (451883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70811904 :
    ThetaLowerSegment 70811904 70828288 (7080175130913 / 100000) (1416360747053 / 20000) := by
  exact
    packedTile16384 70811904 70828288 11 901 8414 26 _ _ (56486 / 3125) (361511 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70828288 :
    ThetaLowerSegment 70828288 70844672 (1416360747053 / 20000) (1416681772373 / 20000) := by
  exact
    packedTile16384 70828288 70844672 11 888 8415 26 _ _ (72303 / 4000) (903789 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70844672 :
    ThetaLowerSegment 70844672 70861056 (1416681772373 / 20000) (141701256299 / 2000) := by
  exact
    packedTile16384 70844672 70861056 11 915 8416 26 _ _ (1807599 / 100000) (903801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70861056 :
    ThetaLowerSegment 70861056 70877440 (141701256299 / 2000) (3543364721217 / 50000) := by
  exact
    packedTile16384 70861056 70877440 11 922 8417 26 _ _ (903811 / 50000) (14461 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70877440 :
    ThetaLowerSegment 70877440 70893824 (3543364721217 / 50000) (3544167315597 / 50000) := by
  exact
    packedTile16384 70877440 70893824 11 888 8418 26 _ _ (361529 / 20000) (56489 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70893824 :
    ThetaLowerSegment 70893824 70910208 (3544167315597 / 50000) (708998322441 / 10000) := by
  exact
    packedTile16384 70893824 70910208 11 912 8419 26 _ _ (451917 / 25000) (1807671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70910208 :
    ThetaLowerSegment 70910208 70926592 (708998322441 / 10000) (7091611954001 / 100000) := by
  exact
    packedTile16384 70910208 70926592 11 901 8420 26 _ _ (1807691 / 100000) (903847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70926592 :
    ThetaLowerSegment 70926592 70942976 (7091611954001 / 100000) (1418655371719 / 20000) := by
  exact
    packedTile16384 70926592 70942976 11 921 8421 26 _ _ (903857 / 50000) (1807717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70942976 :
    ThetaLowerSegment 70942976 70959360 (1418655371719 / 20000) (221715800926 / 3125) := by
  exact
    packedTile16384 70942976 70959360 11 901 8422 26 _ _ (1807737 / 100000) (90387 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70959360 :
    ThetaLowerSegment 70959360 70975744 (221715800926 / 3125) (443536790887 / 6250) := by
  exact
    packedTile16384 70959360 70975744 11 931 8423 26 _ _ (22597 / 1250) (1807763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70975744 :
    ThetaLowerSegment 70975744 70992128 (443536790887 / 6250) (3549109637229 / 50000) := by
  exact
    packedTile16384 70975744 70992128 11 902 8424 26 _ _ (1807783 / 100000) (903893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell70992128 :
    ThetaLowerSegment 70992128 71008512 (3549109637229 / 50000) (1774952083983 / 25000) := by
  exact
    packedTile16384 70992128 71008512 11 879 8425 26 _ _ (903903 / 50000) (1807809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71008512 :
    ThetaLowerSegment 71008512 71024896 (1774952083983 / 25000) (3550743905001 / 50000) := by
  exact
    packedTile16384 71008512 71024896 11 929 8426 26 _ _ (180783 / 10000) (1807833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71024896 :
    ThetaLowerSegment 71024896 71041280 (3550743905001 / 50000) (7103094991319 / 100000) := by
  exact
    packedTile16384 71024896 71041280 11 889 8427 26 _ _ (1807853 / 100000) (112991 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71041280 :
    ThetaLowerSegment 71041280 71057664 (7103094991319 / 100000) (7104707616711 / 100000) := by
  exact
    packedTile16384 71041280 71057664 11 892 8428 26 _ _ (451969 / 25000) (1807879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71057664 :
    ThetaLowerSegment 71057664 71074048 (7104707616711 / 100000) (1776585037377 / 25000) := by
  exact
    packedTile16384 71057664 71074048 11 903 8429 26 _ _ (1807899 / 100000) (903951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71074048 :
    ThetaLowerSegment 71074048 71090432 (1776585037377 / 25000) (1777006283203 / 25000) := by
  exact
    packedTile16384 71074048 71090432 11 932 8430 26 _ _ (903961 / 50000) (72317 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71090432 :
    ThetaLowerSegment 71090432 71106816 (1777006283203 / 25000) (222177537826 / 3125) := by
  exact
    packedTile16384 71090432 71106816 11 916 8431 26 _ _ (361589 / 20000) (451987 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71106816 :
    ThetaLowerSegment 71106816 71123200 (222177537826 / 3125) (222227143948 / 3125) := by
  exact
    packedTile16384 71106816 71123200 11 878 8432 26 _ _ (56499 / 3125) (1807971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71123200 :
    ThetaLowerSegment 71123200 71139584 (222227143948 / 3125) (7112973541849 / 100000) := by
  exact
    packedTile16384 71123200 71139584 11 943 8433 26 _ _ (1807991 / 100000) (903997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_55836928_71139584 :
    ThetaLowerSegment 55836928 71139584 (2791312980113 / 50000) (7112973541849 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell55836928 cell55853312)
                      (ThetaLowerSegment.join cell55869696 cell55886080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell55902464 cell55918848)
                      (ThetaLowerSegment.join cell55935232 cell55951616)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell55968000 cell55984384)
                      (ThetaLowerSegment.join cell56000768 cell56017152))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56033536 cell56049920)
                      (ThetaLowerSegment.join cell56066304 cell56082688))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56099072 cell56115456)
                      (ThetaLowerSegment.join cell56131840 cell56148224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56164608 cell56180992)
                      (ThetaLowerSegment.join cell56197376 cell56213760)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56230144 cell56246528)
                      (ThetaLowerSegment.join cell56262912 cell56279296))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56295680 cell56312064)
                      (ThetaLowerSegment.join cell56328448 cell56344832)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56361216 cell56377600)
                      (ThetaLowerSegment.join cell56393984 cell56410368))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56426752 cell56443136)
                      (ThetaLowerSegment.join cell56459520 cell56475904)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56492288 cell56508672)
                      (ThetaLowerSegment.join cell56525056 cell56541440))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56557824 cell56574208)
                      (ThetaLowerSegment.join cell56590592 cell56606976))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56623360 cell56639744)
                      (ThetaLowerSegment.join cell56656128 cell56672512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56688896 cell56705280)
                      (ThetaLowerSegment.join cell56721664 cell56738048)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56754432 cell56770816)
                      (ThetaLowerSegment.join cell56787200 cell56803584))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56819968 cell56836352)
                      (ThetaLowerSegment.join cell56852736 cell56869120))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56885504 cell56901888)
                      (ThetaLowerSegment.join cell56918272 cell56934656))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell56951040 cell56967424)
                      (ThetaLowerSegment.join cell56983808 cell57000192)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57016576 cell57032960)
                      (ThetaLowerSegment.join cell57049344 cell57065728))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57082112 cell57098496)
                      (ThetaLowerSegment.join cell57114880 cell57131264))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57147648 cell57164032)
                      (ThetaLowerSegment.join cell57180416 cell57196800))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57213184 cell57229568)
                      (ThetaLowerSegment.join cell57245952 cell57262336)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57278720 cell57295104)
                      (ThetaLowerSegment.join cell57311488 cell57327872))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57344256 cell57360640)
                      (ThetaLowerSegment.join cell57377024 cell57393408)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57409792 cell57426176)
                      (ThetaLowerSegment.join cell57442560 cell57458944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57475328 cell57491712)
                      (ThetaLowerSegment.join cell57508096 cell57524480)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57540864 cell57557248)
                      (ThetaLowerSegment.join cell57573632 cell57590016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57606400 cell57622784)
                      (ThetaLowerSegment.join cell57639168 cell57655552))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57671936 cell57688320)
                      (ThetaLowerSegment.join cell57704704 cell57721088))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57737472 cell57753856)
                      (ThetaLowerSegment.join cell57770240 cell57786624)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57803008 cell57819392)
                      (ThetaLowerSegment.join cell57835776 cell57852160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57868544 cell57884928)
                      (ThetaLowerSegment.join cell57901312 cell57917696)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57934080 cell57950464)
                      (ThetaLowerSegment.join cell57966848 cell57983232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell57999616 cell58016000)
                      (ThetaLowerSegment.join cell58032384 cell58048768)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58065152 cell58081536)
                      (ThetaLowerSegment.join cell58097920 cell58114304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58130688 cell58147072)
                      (ThetaLowerSegment.join cell58163456 cell58179840))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58196224 cell58212608)
                      (ThetaLowerSegment.join cell58228992 cell58245376))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58261760 cell58278144)
                      (ThetaLowerSegment.join cell58294528 cell58310912)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58327296 cell58343680)
                      (ThetaLowerSegment.join cell58360064 cell58376448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58392832 cell58409216)
                      (ThetaLowerSegment.join cell58425600 cell58441984)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58458368 cell58474752)
                      (ThetaLowerSegment.join cell58491136 cell58507520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58523904 cell58540288)
                      (ThetaLowerSegment.join cell58556672 cell58573056)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58589440 cell58605824)
                      (ThetaLowerSegment.join cell58622208 cell58638592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58654976 cell58671360)
                      (ThetaLowerSegment.join cell58687744 cell58704128))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58720512 cell58736896)
                      (ThetaLowerSegment.join cell58753280 cell58769664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58786048 cell58802432)
                      (ThetaLowerSegment.join cell58818816 cell58835200)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58851584 cell58867968)
                      (ThetaLowerSegment.join cell58884352 cell58900736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58917120 cell58933504)
                      (ThetaLowerSegment.join cell58949888 cell58966272))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell58982656 cell58999040)
                      (ThetaLowerSegment.join cell59015424 cell59031808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59048192 cell59064576)
                      (ThetaLowerSegment.join cell59080960 cell59097344)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59113728 cell59130112)
                      (ThetaLowerSegment.join cell59146496 cell59162880))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59179264 cell59195648)
                      (ThetaLowerSegment.join cell59212032 cell59228416))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59244800 cell59261184)
                      (ThetaLowerSegment.join cell59277568 cell59293952))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59310336 cell59326720)
                      (ThetaLowerSegment.join cell59343104 cell59359488)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59375872 cell59392256)
                      (ThetaLowerSegment.join cell59408640 cell59425024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59441408 cell59457792)
                      (ThetaLowerSegment.join cell59474176 cell59490560)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59506944 cell59523328)
                      (ThetaLowerSegment.join cell59539712 cell59556096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59572480 cell59588864)
                      (ThetaLowerSegment.join cell59605248 cell59621632)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59638016 cell59654400)
                      (ThetaLowerSegment.join cell59670784 cell59687168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59703552 cell59719936)
                      (ThetaLowerSegment.join cell59736320 cell59752704))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59769088 cell59785472)
                      (ThetaLowerSegment.join cell59801856 cell59818240))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59834624 cell59851008)
                      (ThetaLowerSegment.join cell59867392 cell59883776)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59900160 cell59916544)
                      (ThetaLowerSegment.join cell59932928 cell59949312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell59965696 cell59982080)
                      (ThetaLowerSegment.join cell59998464 cell60014848))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60031232 cell60047616)
                      (ThetaLowerSegment.join cell60064000 cell60080384))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60096768 cell60113152)
                      (ThetaLowerSegment.join cell60129536 cell60145920)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60162304 cell60178688)
                      (ThetaLowerSegment.join cell60195072 cell60211456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60227840 cell60244224)
                      (ThetaLowerSegment.join cell60260608 cell60276992))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60293376 cell60309760)
                      (ThetaLowerSegment.join cell60326144 cell60342528))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60358912 cell60375296)
                      (ThetaLowerSegment.join cell60391680 cell60408064)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60424448 cell60440832)
                      (ThetaLowerSegment.join cell60457216 cell60473600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60489984 cell60506368)
                      (ThetaLowerSegment.join cell60522752 cell60539136)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60555520 cell60571904)
                      (ThetaLowerSegment.join cell60588288 cell60604672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60621056 cell60637440)
                      (ThetaLowerSegment.join cell60653824 cell60670208)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60686592 cell60702976)
                      (ThetaLowerSegment.join cell60719360 cell60735744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60752128 cell60768512)
                      (ThetaLowerSegment.join cell60784896 cell60801280))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60817664 cell60834048)
                      (ThetaLowerSegment.join cell60850432 cell60866816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60883200 cell60899584)
                      (ThetaLowerSegment.join cell60915968 cell60932352)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell60948736 cell60965120)
                      (ThetaLowerSegment.join cell60981504 cell60997888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61014272 cell61030656)
                      (ThetaLowerSegment.join cell61047040 cell61063424))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61079808 cell61096192)
                      (ThetaLowerSegment.join cell61112576 cell61128960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61145344 cell61161728)
                      (ThetaLowerSegment.join cell61178112 cell61194496)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61210880 cell61227264)
                      (ThetaLowerSegment.join cell61243648 cell61260032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61276416 cell61292800)
                      (ThetaLowerSegment.join cell61309184 cell61325568))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61341952 cell61358336)
                      (ThetaLowerSegment.join cell61374720 cell61391104))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61407488 cell61423872)
                      (ThetaLowerSegment.join cell61440256 cell61456640)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61473024 cell61489408)
                      (ThetaLowerSegment.join cell61505792 cell61522176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61538560 cell61554944)
                      (ThetaLowerSegment.join cell61571328 cell61587712)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61604096 cell61620480)
                      (ThetaLowerSegment.join cell61636864 cell61653248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61669632 cell61686016)
                      (ThetaLowerSegment.join cell61702400 cell61718784)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61735168 cell61751552)
                      (ThetaLowerSegment.join cell61767936 cell61784320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61800704 cell61817088)
                      (ThetaLowerSegment.join cell61833472 cell61849856))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61866240 cell61882624)
                      (ThetaLowerSegment.join cell61899008 cell61915392))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61931776 cell61948160)
                      (ThetaLowerSegment.join cell61964544 cell61980928)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell61997312 cell62013696)
                      (ThetaLowerSegment.join cell62030080 cell62046464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62062848 cell62079232)
                      (ThetaLowerSegment.join cell62095616 cell62112000)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62128384 cell62144768)
                      (ThetaLowerSegment.join cell62161152 cell62177536))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62193920 cell62210304)
                      (ThetaLowerSegment.join cell62226688 cell62243072)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62259456 cell62275840)
                      (ThetaLowerSegment.join cell62292224 cell62308608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62324992 cell62341376)
                      (ThetaLowerSegment.join cell62357760 cell62374144))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62390528 cell62406912)
                      (ThetaLowerSegment.join cell62423296 cell62439680))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62456064 cell62472448)
                      (ThetaLowerSegment.join cell62488832 cell62505216)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62521600 cell62537984)
                      (ThetaLowerSegment.join cell62554368 cell62570752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62587136 cell62603520)
                      (ThetaLowerSegment.join cell62619904 cell62636288)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62652672 cell62669056)
                      (ThetaLowerSegment.join cell62685440 cell62701824))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62718208 cell62734592)
                      (ThetaLowerSegment.join cell62750976 cell62767360)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62783744 cell62800128)
                      (ThetaLowerSegment.join cell62816512 cell62832896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62849280 cell62865664)
                      (ThetaLowerSegment.join cell62882048 cell62898432))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62914816 cell62931200)
                      (ThetaLowerSegment.join cell62947584 cell62963968))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell62980352 cell62996736)
                      (ThetaLowerSegment.join cell63013120 cell63029504)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63045888 cell63062272)
                      (ThetaLowerSegment.join cell63078656 cell63095040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63111424 cell63127808)
                      (ThetaLowerSegment.join cell63144192 cell63160576))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63176960 cell63193344)
                      (ThetaLowerSegment.join cell63209728 cell63226112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63242496 cell63258880)
                      (ThetaLowerSegment.join cell63275264 cell63291648)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63308032 cell63324416)
                      (ThetaLowerSegment.join cell63340800 cell63357184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63373568 cell63389952)
                      (ThetaLowerSegment.join cell63406336 cell63422720))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63439104 cell63455488)
                      (ThetaLowerSegment.join cell63471872 cell63488256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63504640 cell63521024)
                      (ThetaLowerSegment.join cell63537408 cell63553792)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63570176 cell63586560)
                      (ThetaLowerSegment.join cell63602944 cell63619328))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63635712 cell63652096)
                      (ThetaLowerSegment.join cell63668480 cell63684864)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63701248 cell63717632)
                      (ThetaLowerSegment.join cell63734016 cell63750400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63766784 cell63783168)
                      (ThetaLowerSegment.join cell63799552 cell63815936)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63832320 cell63848704)
                      (ThetaLowerSegment.join cell63865088 cell63881472))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63897856 cell63914240)
                      (ThetaLowerSegment.join cell63930624 cell63947008))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell63963392 cell63979776)
                      (ThetaLowerSegment.join cell63996160 cell64012544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64028928 cell64045312)
                      (ThetaLowerSegment.join cell64061696 cell64078080)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64094464 cell64110848)
                      (ThetaLowerSegment.join cell64127232 cell64143616))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64160000 cell64176384)
                      (ThetaLowerSegment.join cell64192768 cell64209152)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64225536 cell64241920)
                      (ThetaLowerSegment.join cell64258304 cell64274688))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64291072 cell64307456)
                      (ThetaLowerSegment.join cell64323840 cell64340224)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64356608 cell64372992)
                      (ThetaLowerSegment.join cell64389376 cell64405760))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64422144 cell64438528)
                      (ThetaLowerSegment.join cell64454912 cell64471296))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64487680 cell64504064)
                      (ThetaLowerSegment.join cell64520448 cell64536832))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64553216 cell64569600)
                      (ThetaLowerSegment.join cell64585984 cell64602368)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64618752 cell64635136)
                      (ThetaLowerSegment.join cell64651520 cell64667904))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64684288 cell64700672)
                      (ThetaLowerSegment.join cell64717056 cell64733440)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64749824 cell64766208)
                      (ThetaLowerSegment.join cell64782592 cell64798976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64815360 cell64831744)
                      (ThetaLowerSegment.join cell64848128 cell64864512)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64880896 cell64897280)
                      (ThetaLowerSegment.join cell64913664 cell64930048))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell64946432 cell64962816)
                      (ThetaLowerSegment.join cell64979200 cell64995584))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65011968 cell65028352)
                      (ThetaLowerSegment.join cell65044736 cell65061120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65077504 cell65093888)
                      (ThetaLowerSegment.join cell65110272 cell65126656)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65143040 cell65159424)
                      (ThetaLowerSegment.join cell65175808 cell65192192))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65208576 cell65224960)
                      (ThetaLowerSegment.join cell65241344 cell65257728))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65274112 cell65290496)
                      (ThetaLowerSegment.join cell65306880 cell65323264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65339648 cell65356032)
                      (ThetaLowerSegment.join cell65372416 cell65388800)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65405184 cell65421568)
                      (ThetaLowerSegment.join cell65437952 cell65454336))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65470720 cell65487104)
                      (ThetaLowerSegment.join cell65503488 cell65519872))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65536256 cell65552640)
                      (ThetaLowerSegment.join cell65569024 cell65585408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65601792 cell65618176)
                      (ThetaLowerSegment.join cell65634560 cell65650944)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65667328 cell65683712)
                      (ThetaLowerSegment.join cell65700096 cell65716480))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65732864 cell65749248)
                      (ThetaLowerSegment.join cell65765632 cell65782016)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65798400 cell65814784)
                      (ThetaLowerSegment.join cell65831168 cell65847552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65863936 cell65880320)
                      (ThetaLowerSegment.join cell65896704 cell65913088)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65929472 cell65945856)
                      (ThetaLowerSegment.join cell65962240 cell65978624))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell65995008 cell66011392)
                      (ThetaLowerSegment.join cell66027776 cell66044160))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66060544 cell66076928)
                      (ThetaLowerSegment.join cell66093312 cell66109696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66126080 cell66142464)
                      (ThetaLowerSegment.join cell66158848 cell66175232)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66191616 cell66208000)
                      (ThetaLowerSegment.join cell66224384 cell66240768))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66257152 cell66273536)
                      (ThetaLowerSegment.join cell66289920 cell66306304)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66322688 cell66339072)
                      (ThetaLowerSegment.join cell66355456 cell66371840))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66388224 cell66404608)
                      (ThetaLowerSegment.join cell66420992 cell66437376)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66453760 cell66470144)
                      (ThetaLowerSegment.join cell66486528 cell66502912))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66519296 cell66535680)
                      (ThetaLowerSegment.join cell66552064 cell66568448))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66584832 cell66601216)
                      (ThetaLowerSegment.join cell66617600 cell66633984))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66650368 cell66666752)
                      (ThetaLowerSegment.join cell66683136 cell66699520)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66715904 cell66732288)
                      (ThetaLowerSegment.join cell66748672 cell66765056))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66781440 cell66797824)
                      (ThetaLowerSegment.join cell66814208 cell66830592)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66846976 cell66863360)
                      (ThetaLowerSegment.join cell66879744 cell66896128))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66912512 cell66928896)
                      (ThetaLowerSegment.join cell66945280 cell66961664)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell66978048 cell66994432)
                      (ThetaLowerSegment.join cell67010816 cell67027200))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67043584 cell67059968)
                      (ThetaLowerSegment.join cell67076352 cell67092736))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67109120 cell67125504)
                      (ThetaLowerSegment.join cell67141888 cell67158272))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67174656 cell67191040)
                      (ThetaLowerSegment.join cell67207424 cell67223808)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67240192 cell67256576)
                      (ThetaLowerSegment.join cell67272960 cell67289344))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67305728 cell67322112)
                      (ThetaLowerSegment.join cell67338496 cell67354880))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67371264 cell67387648)
                      (ThetaLowerSegment.join cell67404032 cell67420416))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67436800 cell67453184)
                      (ThetaLowerSegment.join cell67469568 cell67485952)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67502336 cell67518720)
                      (ThetaLowerSegment.join cell67535104 cell67551488))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67567872 cell67584256)
                      (ThetaLowerSegment.join cell67600640 cell67617024))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67633408 cell67649792)
                      (ThetaLowerSegment.join cell67666176 cell67682560))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67698944 cell67715328)
                      (ThetaLowerSegment.join cell67731712 cell67764480)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67797248 cell67813632)
                      (ThetaLowerSegment.join cell67830016 cell67846400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67862784 cell67879168)
                      (ThetaLowerSegment.join cell67895552 cell67911936)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell67928320 cell67961088)
                      (ThetaLowerSegment.join cell67993856 cell68026624))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68059392 cell68092160)
                      (ThetaLowerSegment.join cell68124928 cell68141312)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68157696 cell68174080)
                      (ThetaLowerSegment.join cell68190464 cell68206848))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68223232 cell68239616)
                      (ThetaLowerSegment.join cell68272384 cell68305152))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68337920 cell68354304)
                      (ThetaLowerSegment.join cell68370688 cell68387072))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68403456 cell68419840)
                      (ThetaLowerSegment.join cell68436224 cell68452608)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68468992 cell68485376)
                      (ThetaLowerSegment.join cell68501760 cell68518144))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68534528 cell68550912)
                      (ThetaLowerSegment.join cell68567296 cell68583680))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68600064 cell68616448)
                      (ThetaLowerSegment.join cell68632832 cell68649216))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68665600 cell68681984)
                      (ThetaLowerSegment.join cell68698368 cell68714752)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68731136 cell68747520)
                      (ThetaLowerSegment.join cell68763904 cell68780288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68796672 cell68813056)
                      (ThetaLowerSegment.join cell68829440 cell68845824))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68862208 cell68878592)
                      (ThetaLowerSegment.join cell68894976 cell68911360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68927744 cell68944128)
                      (ThetaLowerSegment.join cell68960512 cell68976896)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell68993280 cell69009664)
                      (ThetaLowerSegment.join cell69026048 cell69042432))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69058816 cell69075200)
                      (ThetaLowerSegment.join cell69091584 cell69107968)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69124352 cell69140736)
                      (ThetaLowerSegment.join cell69157120 cell69173504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69189888 cell69206272)
                      (ThetaLowerSegment.join cell69222656 cell69239040)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69255424 cell69271808)
                      (ThetaLowerSegment.join cell69288192 cell69304576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69320960 cell69337344)
                      (ThetaLowerSegment.join cell69353728 cell69370112))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69386496 cell69402880)
                      (ThetaLowerSegment.join cell69419264 cell69435648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69452032 cell69468416)
                      (ThetaLowerSegment.join cell69484800 cell69501184)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69517568 cell69533952)
                      (ThetaLowerSegment.join cell69550336 cell69566720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69599488 cell69615872)
                      (ThetaLowerSegment.join cell69632256 cell69648640))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69665024 cell69697792)
                      (ThetaLowerSegment.join cell69730560 cell69763328))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69796096 cell69828864)
                      (ThetaLowerSegment.join cell69861632 cell69894400)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69927168 cell69943552)
                      (ThetaLowerSegment.join cell69959936 cell69976320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell69992704 cell70009088)
                      (ThetaLowerSegment.join cell70025472 cell70041856))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell70058240 cell70074624)
                      (ThetaLowerSegment.join cell70091008 cell70107392))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell70123776 cell70140160)
                      (ThetaLowerSegment.join cell70156544 cell70172928)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell70189312 cell70205696)
                      (ThetaLowerSegment.join cell70222080 cell70238464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell70254848 cell70271232)
                      (ThetaLowerSegment.join cell70287616 cell70304000)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell70320384 cell70336768)
                      (ThetaLowerSegment.join cell70353152 cell70369536))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell70385920 cell70402304)
                      (ThetaLowerSegment.join cell70418688 cell70451456)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell70484224 cell70516992)
                      (ThetaLowerSegment.join cell70549760 cell70582528))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell70615296 cell70648064)
                      (ThetaLowerSegment.join cell70664448 cell70680832))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell70713600 cell70729984)
                      (ThetaLowerSegment.join cell70762752 cell70795520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell70811904 cell70828288)
                      (ThetaLowerSegment.join cell70844672 cell70861056)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell70877440 cell70893824)
                      (ThetaLowerSegment.join cell70910208 cell70926592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell70942976 cell70959360)
                      (ThetaLowerSegment.join cell70975744 cell70992128)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell71008512 cell71024896)
              (ThetaLowerSegment.join cell71041280 cell71057664))
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell71074048 cell71090432)
              (ThetaLowerSegment.join cell71106816 cell71123200))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
