/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaDivisorBase4096

/-! # Direct theta estimate up to 13922560 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell8096000 :
    ThetaLowerSegment 8096000 8104192 (404582206079 / 50000) (80995339291 / 10000) := by
  exact
    thetaTile4096 8096000 8104192 7 6 496 2845 23 _ _ (1590687 / 100000) (159069 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8104192 :
    ThetaLowerSegment 8104192 8112384 (80995339291 / 10000) (405389505941 / 50000) := by
  exact
    thetaTile4096 8104192 8112384 7 6 519 2846 23 _ _ (397697 / 25000) (1590791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8112384 :
    ThetaLowerSegment 8112384 8120576 (405389505941 / 50000) (811591956161 / 100000) := by
  exact
    thetaTile4096 8112384 8120576 7 6 511 2848 23 _ _ (1590889 / 100000) (397723 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8120576 :
    ThetaLowerSegment 8120576 8128768 (811591956161 / 100000) (812463818681 / 100000) := by
  exact
    thetaTile4096 8120576 8128768 7 6 548 2849 23 _ _ (159099 / 10000) (1590993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8128768 :
    ThetaLowerSegment 8128768 8136960 (812463818681 / 100000) (813252999321 / 100000) := by
  exact
    thetaTile4096 8128768 8136960 7 6 496 2851 23 _ _ (159109 / 10000) (1591093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8136960 :
    ThetaLowerSegment 8136960 8145152 (813252999321 / 100000) (814051777203 / 100000) := by
  exact
    thetaTile4096 8136960 8145152 7 6 502 2852 23 _ _ (1591191 / 100000) (795597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8145152 :
    ThetaLowerSegment 8145152 8153344 (814051777203 / 100000) (814874475167 / 100000) := by
  exact
    thetaTile4096 8145152 8153344 7 6 517 2853 23 _ _ (397823 / 25000) (318259 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8153344 :
    ThetaLowerSegment 8153344 8161536 (814874475167 / 100000) (815703590399 / 100000) := by
  exact
    thetaTile4096 8153344 8161536 7 6 521 2855 23 _ _ (49731 / 3125) (318279 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8161536 :
    ThetaLowerSegment 8161536 8169728 (815703590399 / 100000) (408264787633 / 50000) := by
  exact
    thetaTile4096 8161536 8169728 7 6 519 2856 23 _ _ (1591493 / 100000) (198937 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8169728 :
    ThetaLowerSegment 8169728 8177920 (408264787633 / 50000) (408662685883 / 50000) := by
  exact
    thetaTile4096 8169728 8177920 7 6 500 2858 23 _ _ (1591593 / 100000) (397899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8177920 :
    ThetaLowerSegment 8177920 8186112 (408662685883 / 50000) (409092442993 / 50000) := by
  exact
    thetaTile4096 8177920 8186112 7 6 540 2859 23 _ _ (1591693 / 100000) (99481 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8186112 :
    ThetaLowerSegment 8186112 8194304 (409092442993 / 50000) (163797111573 / 20000) := by
  exact
    thetaTile4096 8186112 8194304 7 6 503 2861 23 _ _ (1591793 / 100000) (397949 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8194304 :
    ThetaLowerSegment 8194304 8202496 (163797111573 / 20000) (204952937583 / 25000) := by
  exact
    thetaTile4096 8194304 8202496 7 6 519 2862 23 _ _ (1591893 / 100000) (198987 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8202496 :
    ThetaLowerSegment 8202496 8210688 (204952937583 / 25000) (164131419723 / 20000) := by
  exact
    thetaTile4096 8202496 8210688 7 6 531 2864 23 _ _ (1591993 / 100000) (397999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8210688 :
    ThetaLowerSegment 8210688 8218880 (164131419723 / 20000) (410741697441 / 50000) := by
  exact
    thetaTile4096 8210688 8218880 7 6 519 2865 23 _ _ (1592093 / 100000) (49753 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8218880 :
    ThetaLowerSegment 8218880 8227072 (410741697441 / 50000) (82227312261 / 10000) := by
  exact
    thetaTile4096 8218880 8227072 7 6 496 2866 23 _ _ (1592193 / 100000) (398049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8227072 :
    ThetaLowerSegment 8227072 8235264 (82227312261 / 10000) (411560111243 / 50000) := by
  exact
    thetaTile4096 8227072 8235264 7 6 532 2868 23 _ _ (1592293 / 100000) (199037 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8235264 :
    ThetaLowerSegment 8235264 8243456 (411560111243 / 50000) (411978114143 / 50000) := by
  exact
    thetaTile4096 8235264 8243456 7 6 525 2869 23 _ _ (199049 / 12500) (318479 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8243456 :
    ThetaLowerSegment 8243456 8251648 (411978114143 / 50000) (412386588341 / 50000) := by
  exact
    thetaTile4096 8243456 8251648 7 6 513 2871 23 _ _ (398123 / 25000) (318499 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8251648 :
    ThetaLowerSegment 8251648 8259840 (412386588341 / 50000) (825571064773 / 100000) := by
  exact
    thetaTile4096 8251648 8259840 7 6 501 2872 23 _ _ (1592591 / 100000) (796297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8259840 :
    ThetaLowerSegment 8259840 8268032 (825571064773 / 100000) (826353075563 / 100000) := by
  exact
    thetaTile4096 8259840 8268032 7 6 491 2873 23 _ _ (159269 / 10000) (1592693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8268032 :
    ThetaLowerSegment 8268032 8276224 (826353075563 / 100000) (165438813631 / 20000) := by
  exact
    thetaTile4096 8268032 8276224 7 6 528 2875 23 _ _ (1592789 / 100000) (199099 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8276224 :
    ThetaLowerSegment 8276224 8284416 (165438813631 / 20000) (828031927243 / 100000) := by
  exact
    thetaTile4096 8276224 8284416 7 6 526 2876 23 _ _ (199111 / 12500) (1592891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8284416 :
    ThetaLowerSegment 8284416 8292608 (828031927243 / 100000) (165767595733 / 20000) := by
  exact
    thetaTile4096 8284416 8292608 7 6 506 2878 23 _ _ (1592987 / 100000) (159299 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8292608 :
    ThetaLowerSegment 8292608 8300800 (165767595733 / 20000) (829652045611 / 100000) := by
  exact
    thetaTile4096 8292608 8300800 7 6 511 2879 23 _ _ (796543 / 50000) (1593089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8300800 :
    ThetaLowerSegment 8300800 8308992 (829652045611 / 100000) (415236267943 / 50000) := by
  exact
    thetaTile4096 8300800 8308992 7 6 515 2881 23 _ _ (318637 / 20000) (398297 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8308992 :
    ThetaLowerSegment 8308992 8317184 (415236267943 / 50000) (831293076631 / 100000) := by
  exact
    thetaTile4096 8308992 8317184 7 6 515 2882 23 _ _ (1593283 / 100000) (796643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8317184 :
    ThetaLowerSegment 8317184 8325376 (831293076631 / 100000) (832110481597 / 100000) := by
  exact
    thetaTile4096 8317184 8325376 7 6 513 2883 23 _ _ (796691 / 50000) (318677 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8325376 :
    ThetaLowerSegment 8325376 8333568 (832110481597 / 100000) (832921562917 / 100000) := by
  exact
    thetaTile4096 8325376 8333568 7 6 509 2885 23 _ _ (39837 / 2500) (1593483 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8333568 :
    ThetaLowerSegment 8333568 8341760 (832921562917 / 100000) (833747036839 / 100000) := by
  exact
    thetaTile4096 8333568 8341760 7 6 518 2886 23 _ _ (1593579 / 100000) (796791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8341760 :
    ThetaLowerSegment 8341760 8349952 (833747036839 / 100000) (834607622419 / 100000) := by
  exact
    thetaTile4096 8341760 8349952 7 6 540 2888 23 _ _ (1593677 / 100000) (19921 / 1250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8349952 :
    ThetaLowerSegment 8349952 8358144 (834607622419 / 100000) (417706239397 / 50000) := by
  exact
    thetaTile4096 8349952 8358144 7 6 505 2889 23 _ _ (63751 / 4000) (796889 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8358144 :
    ThetaLowerSegment 8358144 8366336 (417706239397 / 50000) (418104707647 / 50000) := by
  exact
    thetaTile4096 8358144 8366336 7 6 500 2891 23 _ _ (1593873 / 100000) (398469 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8366336 :
    ThetaLowerSegment 8366336 8374528 (418104707647 / 50000) (26156549648 / 3125) := by
  exact
    thetaTile4096 8366336 8374528 7 6 502 2892 23 _ _ (1593971 / 100000) (796987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8374528 :
    ThetaLowerSegment 8374528 8382720 (26156549648 / 3125) (837846474961 / 100000) := by
  exact
    thetaTile4096 8374528 8382720 7 6 525 2893 23 _ _ (1594069 / 100000) (199259 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8382720 :
    ThetaLowerSegment 8382720 8390912 (837846474961 / 100000) (838675441801 / 100000) := by
  exact
    thetaTile4096 8382720 8390912 7 6 520 2895 23 _ _ (1594167 / 100000) (159417 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8390912 :
    ThetaLowerSegment 8390912 8399104 (838675441801 / 100000) (839486922177 / 100000) := by
  exact
    thetaTile4096 8390912 8399104 7 6 509 2896 23 _ _ (199283 / 12500) (1594267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8399104 :
    ThetaLowerSegment 8399104 8407296 (839486922177 / 100000) (1344464769 / 160) := by
  exact
    thetaTile4096 8399104 8407296 7 6 504 2898 23 _ _ (797181 / 50000) (318873 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8407296 :
    ThetaLowerSegment 8407296 8415488 (1344464769 / 160) (168226471101 / 20000) := by
  exact
    thetaTile4096 8407296 8415488 7 6 528 2899 23 _ _ (79723 / 5000) (1594463 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8415488 :
    ThetaLowerSegment 8415488 8423680 (168226471101 / 20000) (33677823183 / 4000) := by
  exact
    thetaTile4096 8415488 8423680 7 6 510 2900 23 _ _ (1594557 / 100000) (9966 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8423680 :
    ThetaLowerSegment 8423680 8431872 (33677823183 / 4000) (842728554689 / 100000) := by
  exact
    thetaTile4096 8423680 8431872 7 6 491 2902 23 _ _ (797327 / 50000) (1594657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8431872 :
    ThetaLowerSegment 8431872 8440064 (842728554689 / 100000) (26360833186 / 3125) := by
  exact
    thetaTile4096 8431872 8440064 7 6 513 2903 23 _ _ (1594751 / 100000) (797377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8440064 :
    ThetaLowerSegment 8440064 8448256 (26360833186 / 3125) (844336112207 / 100000) := by
  exact
    thetaTile4096 8440064 8448256 7 6 495 2905 23 _ _ (1594849 / 100000) (398713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8448256 :
    ThetaLowerSegment 8448256 8456448 (844336112207 / 100000) (845157509397 / 100000) := by
  exact
    thetaTile4096 8448256 8456448 7 6 515 2906 23 _ _ (797473 / 50000) (1594949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8456448 :
    ThetaLowerSegment 8456448 8464640 (845157509397 / 100000) (845974170901 / 100000) := by
  exact
    thetaTile4096 8456448 8464640 7 6 512 2907 23 _ _ (797521 / 50000) (319009 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8464640 :
    ThetaLowerSegment 8464640 8472832 (845974170901 / 100000) (423385072631 / 50000) := by
  exact
    thetaTile4096 8464640 8472832 7 6 499 2909 23 _ _ (1595139 / 100000) (797571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8472832 :
    ThetaLowerSegment 8472832 8481024 (423385072631 / 50000) (423811798261 / 50000) := by
  exact
    thetaTile4096 8472832 8481024 7 6 535 2910 23 _ _ (398809 / 25000) (1595239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8481024 :
    ThetaLowerSegment 8481024 8489216 (423811798261 / 50000) (16968935767 / 2000) := by
  exact
    thetaTile4096 8481024 8489216 7 6 516 2912 23 _ _ (1595333 / 100000) (199417 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8489216 :
    ThetaLowerSegment 8489216 8497408 (16968935767 / 2000) (212321496001 / 25000) := by
  exact
    thetaTile4096 8489216 8497408 7 6 526 2913 23 _ _ (1595429 / 100000) (199429 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8497408 :
    ThetaLowerSegment 8497408 8505600 (212321496001 / 25000) (85010129779 / 10000) := by
  exact
    thetaTile4096 8497408 8505600 7 6 511 2915 23 _ _ (797763 / 50000) (1595529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8505600 :
    ThetaLowerSegment 8505600 8513792 (85010129779 / 10000) (212733154213 / 25000) := by
  exact
    thetaTile4096 8505600 8513792 7 6 521 2916 23 _ _ (797811 / 50000) (2553 / 160) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8513792 :
    ThetaLowerSegment 8513792 8521984 (212733154213 / 25000) (26617275497 / 3125) := by
  exact
    thetaTile4096 8513792 8521984 7 6 514 2917 23 _ _ (797859 / 50000) (1595721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8521984 :
    ThetaLowerSegment 8521984 8530176 (26617275497 / 3125) (426296904941 / 50000) := by
  exact
    thetaTile4096 8521984 8530176 7 6 527 2919 23 _ _ (797907 / 50000) (1595817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8530176 :
    ThetaLowerSegment 8530176 8538368 (426296904941 / 50000) (853409320403 / 100000) := by
  exact
    thetaTile4096 8530176 8538368 7 6 511 2920 23 _ _ (1595911 / 100000) (797957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8538368 :
    ThetaLowerSegment 8538368 8546560 (853409320403 / 100000) (854245628071 / 100000) := by
  exact
    thetaTile4096 8538368 8546560 7 6 524 2922 23 _ _ (1596007 / 100000) (159601 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8546560 :
    ThetaLowerSegment 8546560 8554752 (854245628071 / 100000) (855093158233 / 100000) := by
  exact
    thetaTile4096 8546560 8554752 7 6 531 2923 23 _ _ (798051 / 50000) (319221 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8554752 :
    ThetaLowerSegment 8554752 8562944 (855093158233 / 100000) (855884872441 / 100000) := by
  exact
    thetaTile4096 8554752 8562944 7 6 496 2924 23 _ _ (798099 / 50000) (1596201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8562944 :
    ThetaLowerSegment 8562944 8571136 (855884872441 / 100000) (856698982381 / 100000) := by
  exact
    thetaTile4096 8562944 8571136 7 6 510 2926 23 _ _ (798147 / 50000) (1596297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8571136 :
    ThetaLowerSegment 8571136 8579328 (856698982381 / 100000) (857564225761 / 100000) := by
  exact
    thetaTile4096 8571136 8579328 7 6 542 2927 23 _ _ (159639 / 10000) (1596393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8579328 :
    ThetaLowerSegment 8579328 8587520 (857564225761 / 100000) (858368854201 / 100000) := by
  exact
    thetaTile4096 8579328 8587520 7 6 504 2929 23 _ _ (319297 / 20000) (199561 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8587520 :
    ThetaLowerSegment 8587520 8595712 (858368854201 / 100000) (214796176773 / 25000) := by
  exact
    thetaTile4096 8587520 8595712 7 6 511 2930 23 _ _ (1596581 / 100000) (199573 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8595712 :
    ThetaLowerSegment 8595712 8603904 (214796176773 / 25000) (107502071911 / 12500) := by
  exact
    thetaTile4096 8595712 8603904 7 6 521 2931 23 _ _ (399169 / 25000) (1596679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8603904 :
    ThetaLowerSegment 8603904 8612096 (107502071911 / 12500) (430431431959 / 50000) := by
  exact
    thetaTile4096 8603904 8612096 7 6 530 2933 23 _ _ (1596771 / 100000) (798387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8612096 :
    ThetaLowerSegment 8612096 8620288 (430431431959 / 50000) (43083623749 / 5000) := by
  exact
    thetaTile4096 8612096 8620288 7 6 507 2934 23 _ _ (798433 / 50000) (1596869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8620288 :
    ThetaLowerSegment 8620288 8628480 (43083623749 / 5000) (172498981979 / 20000) := by
  exact
    thetaTile4096 8620288 8628480 7 6 515 2936 23 _ _ (1596961 / 100000) (399241 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8628480 :
    ThetaLowerSegment 8628480 8636672 (172498981979 / 20000) (172658687579 / 20000) := by
  exact
    thetaTile4096 8628480 8636672 7 6 500 2937 23 _ _ (49908 / 3125) (1597059 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8636672 :
    ThetaLowerSegment 8636672 8644864 (172658687579 / 20000) (432053193877 / 50000) := by
  exact
    thetaTile4096 8636672 8644864 7 6 509 2938 23 _ _ (1597151 / 100000) (798577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8644864 :
    ThetaLowerSegment 8644864 8653056 (432053193877 / 50000) (86493056669 / 10000) := by
  exact
    thetaTile4096 8644864 8653056 7 6 516 2940 23 _ _ (798623 / 50000) (1597249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8653056 :
    ThetaLowerSegment 8653056 8661248 (86493056669 / 10000) (432893370733 / 50000) := by
  exact
    thetaTile4096 8653056 8661248 7 6 536 2941 23 _ _ (1597341 / 100000) (49917 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8661248 :
    ThetaLowerSegment 8661248 8669440 (432893370733 / 50000) (108324380447 / 12500) := by
  exact
    thetaTile4096 8661248 8669440 7 6 506 2942 23 _ _ (319487 / 20000) (798719 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8669440 :
    ThetaLowerSegment 8669440 8677632 (108324380447 / 12500) (433689715403 / 50000) := by
  exact
    thetaTile4096 8669440 8677632 7 6 491 2944 23 _ _ (159753 / 10000) (1597533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8677632 :
    ThetaLowerSegment 8677632 8685824 (433689715403 / 50000) (434107494079 / 50000) := by
  exact
    thetaTile4096 8677632 8685824 7 6 523 2945 23 _ _ (199703 / 12500) (1597627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8685824 :
    ThetaLowerSegment 8685824 8694016 (434107494079 / 50000) (869041008881 / 100000) := by
  exact
    thetaTile4096 8685824 8694016 7 6 517 2947 23 _ _ (1597719 / 100000) (798861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8694016 :
    ThetaLowerSegment 8694016 8702208 (869041008881 / 100000) (217467568457 / 25000) := by
  exact
    thetaTile4096 8694016 8702208 7 6 519 2948 23 _ _ (1597813 / 100000) (199727 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8702208 :
    ThetaLowerSegment 8702208 8710400 (217467568457 / 25000) (870674021049 / 100000) := by
  exact
    thetaTile4096 8702208 8710400 7 6 503 2949 23 _ _ (1597907 / 100000) (159791 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8710400 :
    ThetaLowerSegment 8710400 8718592 (870674021049 / 100000) (43576127979 / 5000) := by
  exact
    thetaTile4096 8710400 8718592 7 6 531 2951 23 _ _ (1598001 / 100000) (399501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8718592 :
    ThetaLowerSegment 8718592 8726784 (43576127979 / 5000) (10904499517 / 1250) := by
  exact
    thetaTile4096 8718592 8726784 7 6 524 2952 23 _ _ (319619 / 20000) (799049 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8726784 :
    ThetaLowerSegment 8726784 8734976 (10904499517 / 1250) (873179832317 / 100000) := by
  exact
    thetaTile4096 8726784 8734976 7 6 513 2954 23 _ _ (1598189 / 100000) (99887 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8734976 :
    ThetaLowerSegment 8734976 8743168 (873179832317 / 100000) (174797712703 / 20000) := by
  exact
    thetaTile4096 8734976 8743168 7 6 506 2955 23 _ _ (1598283 / 100000) (799143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8743168 :
    ThetaLowerSegment 8743168 8751360 (174797712703 / 20000) (437399470327 / 50000) := by
  exact
    thetaTile4096 8743168 8751360 7 6 507 2956 23 _ _ (1598377 / 100000) (79919 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8751360 :
    ThetaLowerSegment 8751360 8759552 (437399470327 / 50000) (27363192272 / 3125) := by
  exact
    thetaTile4096 8751360 8759552 7 6 515 2958 23 _ _ (159847 / 10000) (1598473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8759552 :
    ThetaLowerSegment 8759552 8767744 (27363192272 / 3125) (219114550419 / 25000) := by
  exact
    thetaTile4096 8759552 8767744 7 6 523 2959 23 _ _ (399641 / 25000) (1598567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8767744 :
    ThetaLowerSegment 8767744 8775936 (219114550419 / 25000) (219322375959 / 25000) := by
  exact
    thetaTile4096 8767744 8775936 7 6 520 2961 23 _ _ (799329 / 50000) (1598661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8775936 :
    ThetaLowerSegment 8775936 8784128 (219322375959 / 25000) (878122453107 / 100000) := by
  exact
    thetaTile4096 8775936 8784128 7 6 521 2962 23 _ _ (1598751 / 100000) (799377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8784128 :
    ThetaLowerSegment 8784128 8792320 (878122453107 / 100000) (175785014559 / 20000) := by
  exact
    thetaTile4096 8784128 8792320 7 6 502 2963 23 _ _ (399711 / 25000) (1598847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8792320 :
    ThetaLowerSegment 8792320 8800512 (175785014559 / 20000) (439877460549 / 50000) := by
  exact
    thetaTile4096 8792320 8800512 7 6 519 2965 23 _ _ (1598937 / 100000) (79947 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8800512 :
    ThetaLowerSegment 8800512 8808704 (439877460549 / 50000) (880556035629 / 100000) := by
  exact
    thetaTile4096 8800512 8808704 7 6 501 2966 23 _ _ (1599031 / 100000) (799517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8808704 :
    ThetaLowerSegment 8808704 8816896 (880556035629 / 100000) (176273997949 / 20000) := by
  exact
    thetaTile4096 8808704 8816896 7 6 509 2967 23 _ _ (399781 / 25000) (1599127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8816896 :
    ThetaLowerSegment 8816896 8825088 (176273997949 / 20000) (110271799487 / 12500) := by
  exact
    thetaTile4096 8816896 8825088 7 6 503 2969 23 _ _ (1599217 / 100000) (79961 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8825088 :
    ThetaLowerSegment 8825088 8833280 (110271799487 / 12500) (883010834503 / 100000) := by
  exact
    thetaTile4096 8825088 8833280 7 6 523 2970 23 _ _ (1599309 / 100000) (99957 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8833280 :
    ThetaLowerSegment 8833280 8841472 (883010834503 / 100000) (883805737297 / 100000) := by
  exact
    thetaTile4096 8833280 8841472 7 6 497 2972 23 _ _ (799701 / 50000) (319881 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8841472 :
    ThetaLowerSegment 8841472 8849664 (883805737297 / 100000) (884631076717 / 100000) := by
  exact
    thetaTile4096 8841472 8849664 7 6 516 2973 23 _ _ (319899 / 20000) (799749 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8849664 :
    ThetaLowerSegment 8849664 8857856 (884631076717 / 100000) (885434069893 / 100000) := by
  exact
    thetaTile4096 8849664 8857856 7 6 502 2974 23 _ _ (399897 / 25000) (1599591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8857856 :
    ThetaLowerSegment 8857856 8866048 (885434069893 / 100000) (886229110853 / 100000) := by
  exact
    thetaTile4096 8857856 8866048 7 6 497 2976 23 _ _ (9998 / 625) (1599683 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8866048 :
    ThetaLowerSegment 8866048 8874240 (886229110853 / 100000) (887065791609 / 100000) := by
  exact
    thetaTile4096 8866048 8874240 7 6 523 2977 23 _ _ (399943 / 25000) (63991 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8874240 :
    ThetaLowerSegment 8874240 8882432 (887065791609 / 100000) (443936861717 / 50000) := by
  exact
    thetaTile4096 8874240 8882432 7 6 505 2978 23 _ _ (319973 / 20000) (399967 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8882432 :
    ThetaLowerSegment 8882432 8890624 (443936861717 / 50000) (888681701719 / 100000) := by
  exact
    thetaTile4096 8882432 8890624 7 6 505 2980 23 _ _ (1599957 / 100000) (39999 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8890624 :
    ThetaLowerSegment 8890624 8898816 (888681701719 / 100000) (222380431861 / 25000) := by
  exact
    thetaTile4096 8890624 8898816 7 6 525 2981 23 _ _ (1600049 / 100000) (400013 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8898816 :
    ThetaLowerSegment 8898816 8907008 (222380431861 / 25000) (890300996111 / 100000) := by
  exact
    thetaTile4096 8898816 8907008 7 6 487 2983 23 _ _ (1600141 / 100000) (100009 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8907008 :
    ThetaLowerSegment 8907008 8915200 (890300996111 / 100000) (891149119601 / 100000) := by
  exact
    thetaTile4096 8907008 8915200 7 6 530 2984 23 _ _ (1600233 / 100000) (400059 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8915200 :
    ThetaLowerSegment 8915200 8923392 (891149119601 / 100000) (445991444463 / 50000) := by
  exact
    thetaTile4096 8915200 8923392 7 6 521 2985 23 _ _ (64013 / 4000) (200041 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8923392 :
    ThetaLowerSegment 8923392 8931584 (445991444463 / 50000) (178562060903 / 20000) := by
  exact
    thetaTile4096 8923392 8931584 7 6 517 2987 23 _ _ (1600417 / 100000) (80021 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8931584 :
    ThetaLowerSegment 8931584 8939776 (178562060903 / 20000) (446820484343 / 50000) := by
  exact
    thetaTile4096 8931584 8939776 7 6 519 2988 23 _ _ (1600509 / 100000) (50016 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8939776 :
    ThetaLowerSegment 8939776 8947968 (446820484343 / 50000) (447230238199 / 50000) := by
  exact
    thetaTile4096 8939776 8947968 7 6 512 2989 23 _ _ (1600601 / 100000) (400151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8947968 :
    ThetaLowerSegment 8947968 8956160 (447230238199 / 50000) (89528643347 / 10000) := by
  exact
    thetaTile4096 8947968 8956160 7 6 516 2991 23 _ _ (400173 / 25000) (320139 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8956160 :
    ThetaLowerSegment 8956160 8964352 (89528643347 / 10000) (448032207247 / 50000) := by
  exact
    thetaTile4096 8956160 8964352 7 6 486 2992 23 _ _ (100049 / 6250) (1600787 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8964352 :
    ThetaLowerSegment 8964352 8972544 (448032207247 / 50000) (896876058119 / 100000) := by
  exact
    thetaTile4096 8964352 8972544 7 6 507 2994 23 _ _ (12807 / 800) (800439 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8972544 :
    ThetaLowerSegment 8972544 8980736 (896876058119 / 100000) (179537229383 / 20000) := by
  exact
    thetaTile4096 8972544 8980736 7 6 506 2995 23 _ _ (800483 / 50000) (1600969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8980736 :
    ThetaLowerSegment 8980736 8988928 (179537229383 / 20000) (898545915061 / 100000) := by
  exact
    thetaTile4096 8980736 8988928 7 6 537 2996 23 _ _ (800529 / 50000) (1601061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8988928 :
    ThetaLowerSegment 8988928 8997120 (898545915061 / 100000) (899384917137 / 100000) := by
  exact
    thetaTile4096 8988928 8997120 7 6 524 2998 23 _ _ (1601149 / 100000) (50036 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell8997120 :
    ThetaLowerSegment 8997120 9005312 (899384917137 / 100000) (900158316057 / 100000) := by
  exact
    thetaTile4096 8997120 9005312 7 6 483 2999 23 _ _ (40031 / 2500) (1601243 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9005312 :
    ThetaLowerSegment 9005312 9013504 (900158316057 / 100000) (900942968247 / 100000) := by
  exact
    thetaTile4096 9005312 9013504 7 6 490 3000 23 _ _ (1601331 / 100000) (800667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9013504 :
    ThetaLowerSegment 9013504 9021696 (900942968247 / 100000) (901764497733 / 100000) := by
  exact
    thetaTile4096 9013504 9021696 7 6 513 3002 23 _ _ (800711 / 50000) (64057 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9021696 :
    ThetaLowerSegment 9021696 9029888 (901764497733 / 100000) (451280224847 / 50000) := by
  exact
    thetaTile4096 9021696 9029888 7 6 497 3003 23 _ _ (1601513 / 100000) (400379 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9029888 :
    ThetaLowerSegment 9029888 9038080 (451280224847 / 50000) (451695040283 / 50000) := by
  exact
    thetaTile4096 9029888 9038080 7 6 518 3004 23 _ _ (400401 / 25000) (1601607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9038080 :
    ThetaLowerSegment 9038080 9046272 (451695040283 / 50000) (226052937397 / 25000) := by
  exact
    thetaTile4096 9038080 9046272 7 6 513 3006 23 _ _ (800847 / 50000) (1601697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9046272 :
    ThetaLowerSegment 9046272 9054464 (226052937397 / 25000) (905001429593 / 100000) := by
  exact
    thetaTile4096 9046272 9054464 7 6 493 3007 23 _ _ (320357 / 20000) (400447 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9054464 :
    ThetaLowerSegment 9054464 9062656 (905001429593 / 100000) (28306774499 / 3125) := by
  exact
    thetaTile4096 9054464 9062656 7 6 509 3009 23 _ _ (2563 / 160) (800939 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9062656 :
    ThetaLowerSegment 9062656 9070848 (28306774499 / 3125) (56665612893 / 6250) := by
  exact
    thetaTile4096 9062656 9070848 7 6 520 3010 23 _ _ (800983 / 50000) (1601969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9070848 :
    ThetaLowerSegment 9070848 9079040 (56665612893 / 6250) (1134317548 / 125) := by
  exact
    thetaTile4096 9070848 9079040 7 6 502 3011 23 _ _ (200257 / 12500) (1602059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9079040 :
    ThetaLowerSegment 9079040 9087232 (1134317548 / 125) (28384374109 / 3125) := by
  exact
    thetaTile4096 9079040 9087232 7 6 528 3013 23 _ _ (801073 / 50000) (1602149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9087232 :
    ThetaLowerSegment 9087232 9095424 (28384374109 / 3125) (909121919069 / 100000) := by
  exact
    thetaTile4096 9087232 9095424 7 6 513 3014 23 _ _ (1602237 / 100000) (10014 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9095424 :
    ThetaLowerSegment 9095424 9103616 (909121919069 / 100000) (909955129109 / 100000) := by
  exact
    thetaTile4096 9095424 9103616 7 6 520 3015 23 _ _ (1602327 / 100000) (160233 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9103616 :
    ThetaLowerSegment 9103616 9111808 (909955129109 / 100000) (113844341899 / 12500) := by
  exact
    thetaTile4096 9103616 9111808 7 6 499 3017 23 _ _ (1602417 / 100000) (80121 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9111808 :
    ThetaLowerSegment 9111808 9120000 (113844341899 / 12500) (911551181171 / 100000) := by
  exact
    thetaTile4096 9111808 9120000 7 6 497 3018 23 _ _ (1602507 / 100000) (160251 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9120000 :
    ThetaLowerSegment 9120000 9128192 (911551181171 / 100000) (912358890059 / 100000) := by
  exact
    thetaTile4096 9120000 9128192 7 6 504 3019 23 _ _ (1602597 / 100000) (8013 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9128192 :
    ThetaLowerSegment 9128192 9136384 (912358890059 / 100000) (182635572521 / 20000) := by
  exact
    thetaTile4096 9128192 9136384 7 6 511 3021 23 _ _ (801343 / 50000) (1602689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9136384 :
    ThetaLowerSegment 9136384 9144576 (182635572521 / 20000) (914040156093 / 100000) := by
  exact
    thetaTile4096 9136384 9144576 7 6 538 3022 23 _ _ (200347 / 12500) (1602779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9144576 :
    ThetaLowerSegment 9144576 9152768 (914040156093 / 100000) (914848000557 / 100000) := by
  exact
    thetaTile4096 9144576 9152768 7 6 504 3024 23 _ _ (801433 / 50000) (1602869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9152768 :
    ThetaLowerSegment 9152768 9160960 (914848000557 / 100000) (915643066237 / 100000) := by
  exact
    thetaTile4096 9152768 9160960 7 6 496 3025 23 _ _ (320591 / 20000) (801479 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9160960 :
    ThetaLowerSegment 9160960 9169152 (915643066237 / 100000) (114557777779 / 12500) := by
  exact
    thetaTile4096 9160960 9169152 7 6 511 3026 23 _ _ (320609 / 20000) (200381 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9169152 :
    ThetaLowerSegment 9169152 9177344 (114557777779 / 12500) (57330589961 / 6250) := by
  exact
    thetaTile4096 9169152 9177344 7 6 516 3028 23 _ _ (801567 / 50000) (1603137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9177344 :
    ThetaLowerSegment 9177344 9185536 (57330589961 / 6250) (229529175611 / 25000) := by
  exact
    thetaTile4096 9177344 9185536 7 6 516 3029 23 _ _ (1603223 / 100000) (801613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9185536 :
    ThetaLowerSegment 9185536 9193728 (229529175611 / 25000) (183789123053 / 20000) := by
  exact
    thetaTile4096 9185536 9193728 7 6 517 3030 23 _ _ (1603313 / 100000) (400829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9193728 :
    ThetaLowerSegment 9193728 9201920 (183789123053 / 20000) (919774574099 / 100000) := by
  exact
    thetaTile4096 9193728 9201920 7 6 517 3032 23 _ _ (801701 / 50000) (320681 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9201920 :
    ThetaLowerSegment 9201920 9210112 (919774574099 / 100000) (184113981127 / 20000) := by
  exact
    thetaTile4096 9201920 9210112 7 6 496 3033 23 _ _ (1603491 / 100000) (801747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9210112 :
    ThetaLowerSegment 9210112 9218304 (184113981127 / 20000) (184282998459 / 20000) := by
  exact
    thetaTile4096 9210112 9218304 7 6 527 3034 23 _ _ (80179 / 5000) (1603583 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9218304 :
    ThetaLowerSegment 9218304 9226496 (184282998459 / 20000) (230562625961 / 25000) := by
  exact
    thetaTile4096 9218304 9226496 7 6 521 3036 23 _ _ (1603669 / 100000) (200459 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9226496 :
    ThetaLowerSegment 9226496 9234688 (230562625961 / 25000) (461543832499 / 50000) := by
  exact
    thetaTile4096 9226496 9234688 7 6 522 3037 23 _ _ (1603757 / 100000) (20047 / 1250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9234688 :
    ThetaLowerSegment 9234688 9242880 (461543832499 / 50000) (230977609499 / 25000) := by
  exact
    thetaTile4096 9234688 9242880 7 6 513 3038 23 _ _ (801923 / 50000) (1603849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9242880 :
    ThetaLowerSegment 9242880 9251072 (230977609499 / 25000) (924742880261 / 100000) := by
  exact
    thetaTile4096 9242880 9251072 7 6 519 3040 23 _ _ (320787 / 20000) (801969 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9251072 :
    ThetaLowerSegment 9251072 9259264 (924742880261 / 100000) (462781268007 / 50000) := by
  exact
    thetaTile4096 9251072 9259264 7 6 511 3041 23 _ _ (1604023 / 100000) (802013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9259264 :
    ThetaLowerSegment 9259264 9267456 (462781268007 / 50000) (463175879559 / 50000) := by
  exact
    thetaTile4096 9259264 9267456 7 6 492 3042 23 _ _ (100257 / 6250) (320823 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9267456 :
    ThetaLowerSegment 9267456 9275648 (463175879559 / 50000) (463589763159 / 50000) := by
  exact
    thetaTile4096 9267456 9275648 7 6 516 3044 23 _ _ (8021 / 500) (1604203 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9275648 :
    ThetaLowerSegment 9275648 9283840 (463589763159 / 50000) (37120101063 / 4000) := by
  exact
    thetaTile4096 9275648 9283840 7 6 513 3045 23 _ _ (1604289 / 100000) (401073 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9283840 :
    ThetaLowerSegment 9283840 9292032 (37120101063 / 4000) (116099987743 / 12500) := by
  exact
    thetaTile4096 9283840 9292032 7 6 497 3046 23 _ _ (1604377 / 100000) (80219 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9292032 :
    ThetaLowerSegment 9292032 9300224 (116099987743 / 12500) (116205882433 / 12500) := by
  exact
    thetaTile4096 9292032 9300224 7 6 528 3048 23 _ _ (320893 / 20000) (401117 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9300224 :
    ThetaLowerSegment 9300224 9308416 (116205882433 / 12500) (930450940517 / 100000) := by
  exact
    thetaTile4096 9300224 9308416 7 6 501 3049 23 _ _ (1604553 / 100000) (401139 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9308416 :
    ThetaLowerSegment 9308416 9316608 (930450940517 / 100000) (465646688521 / 50000) := by
  exact
    thetaTile4096 9308416 9316608 7 6 525 3050 23 _ _ (1604641 / 100000) (401161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9316608 :
    ThetaLowerSegment 9316608 9324800 (465646688521 / 50000) (58255382073 / 6250) := by
  exact
    thetaTile4096 9316608 9324800 7 6 494 3052 23 _ _ (1604729 / 100000) (401183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9324800 :
    ThetaLowerSegment 9324800 9332992 (58255382073 / 6250) (932896545753 / 100000) := by
  exact
    thetaTile4096 9324800 9332992 7 6 505 3053 23 _ _ (1604817 / 100000) (80241 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9332992 :
    ThetaLowerSegment 9332992 9341184 (932896545753 / 100000) (933711837493 / 100000) := by
  exact
    thetaTile4096 9332992 9341184 7 6 508 3054 23 _ _ (320981 / 20000) (401227 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9341184 :
    ThetaLowerSegment 9341184 9349376 (933711837493 / 100000) (233642627187 / 25000) := by
  exact
    thetaTile4096 9341184 9349376 7 6 535 3056 23 _ _ (1604993 / 100000) (401249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9349376 :
    ThetaLowerSegment 9349376 9357568 (233642627187 / 25000) (187076856963 / 20000) := by
  exact
    thetaTile4096 9349376 9357568 7 6 507 3057 23 _ _ (1605081 / 100000) (401271 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9357568 :
    ThetaLowerSegment 9357568 9365760 (187076856963 / 20000) (187245399603 / 20000) := by
  exact
    thetaTile4096 9357568 9365760 7 6 525 3059 23 _ _ (100323 / 6250) (1605171 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9365760 :
    ThetaLowerSegment 9365760 9373952 (187245399603 / 20000) (187405925203 / 20000) := by
  exact
    thetaTile4096 9365760 9373952 7 6 500 3060 23 _ _ (200657 / 12500) (1605259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9373952 :
    ThetaLowerSegment 9373952 9382144 (187405925203 / 20000) (937822665457 / 100000) := by
  exact
    thetaTile4096 9373952 9382144 7 6 494 3061 23 _ _ (1605343 / 100000) (802673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9382144 :
    ThetaLowerSegment 9382144 9390336 (937822665457 / 100000) (938663910777 / 100000) := by
  exact
    thetaTile4096 9382144 9390336 7 6 524 3063 23 _ _ (160543 / 10000) (1605433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9390336 :
    ThetaLowerSegment 9390336 9398528 (938663910777 / 100000) (939471486331 / 100000) := by
  exact
    thetaTile4096 9390336 9398528 7 6 503 3064 23 _ _ (802759 / 50000) (1605521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9398528 :
    ThetaLowerSegment 9398528 9406720 (939471486331 / 100000) (940287133671 / 100000) := by
  exact
    thetaTile4096 9398528 9406720 7 6 508 3065 23 _ _ (321121 / 20000) (200701 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9406720 :
    ThetaLowerSegment 9406720 9414912 (940287133671 / 100000) (941104430899 / 100000) := by
  exact
    thetaTile4096 9406720 9414912 7 6 509 3067 23 _ _ (401423 / 25000) (321139 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9414912 :
    ThetaLowerSegment 9414912 9423104 (941104430899 / 100000) (470951251531 / 50000) := by
  exact
    thetaTile4096 9414912 9423104 7 6 497 3068 23 _ _ (1605779 / 100000) (802891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9423104 :
    ThetaLowerSegment 9423104 9431296 (470951251531 / 50000) (117838380241 / 12500) := by
  exact
    thetaTile4096 9423104 9431296 7 6 501 3069 23 _ _ (802933 / 50000) (1605869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9431296 :
    ThetaLowerSegment 9431296 9439488 (117838380241 / 12500) (471756615167 / 50000) := by
  exact
    thetaTile4096 9431296 9439488 7 6 502 3071 23 _ _ (1605953 / 100000) (401489 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9439488 :
    ThetaLowerSegment 9439488 9447680 (471756615167 / 50000) (472166958387 / 50000) := by
  exact
    thetaTile4096 9439488 9447680 7 6 511 3072 23 _ _ (40151 / 2500) (1606043 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9447680 :
    ThetaLowerSegment 9447680 9455872 (472166958387 / 50000) (94514661653 / 10000) := by
  exact
    thetaTile4096 9447680 9455872 7 6 506 3073 23 _ _ (803063 / 50000) (1606129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9455872 :
    ThetaLowerSegment 9455872 9464064 (94514661653 / 10000) (189191550819 / 20000) := by
  exact
    thetaTile4096 9455872 9464064 7 6 505 3075 23 _ _ (1606213 / 100000) (200777 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9464064 :
    ThetaLowerSegment 9464064 9472256 (189191550819 / 20000) (189357963499 / 20000) := by
  exact
    thetaTile4096 9464064 9472256 7 6 518 3076 23 _ _ (16063 / 1000) (1606303 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9472256 :
    ThetaLowerSegment 9472256 9480448 (189357963499 / 20000) (947596223267 / 100000) := by
  exact
    thetaTile4096 9472256 9480448 7 6 502 3077 23 _ _ (803193 / 50000) (1606389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9480448 :
    ThetaLowerSegment 9480448 9488640 (947596223267 / 100000) (94841713097 / 10000) := by
  exact
    thetaTile4096 9480448 9488640 7 6 511 3079 23 _ _ (1606473 / 100000) (401619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9488640 :
    ThetaLowerSegment 9488640 9496832 (94841713097 / 10000) (474616631471 / 50000) := by
  exact
    thetaTile4096 9488640 9496832 7 6 508 3080 23 _ _ (1606559 / 100000) (803281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9496832 :
    ThetaLowerSegment 9496832 9505024 (474616631471 / 50000) (475027932591 / 50000) := by
  exact
    thetaTile4096 9496832 9505024 7 6 512 3081 23 _ _ (321329 / 20000) (200831 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9505024 :
    ThetaLowerSegment 9505024 9513216 (475027932591 / 50000) (475444076179 / 50000) := by
  exact
    thetaTile4096 9505024 9513216 7 6 518 3083 23 _ _ (401683 / 25000) (321347 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9513216 :
    ThetaLowerSegment 9513216 9521408 (475444076179 / 50000) (118962449431 / 12500) := by
  exact
    thetaTile4096 9513216 9521408 7 6 505 3084 23 _ _ (803409 / 50000) (1606821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9521408 :
    ThetaLowerSegment 9521408 9529600 (118962449431 / 12500) (119060872301 / 12500) := by
  exact
    thetaTile4096 9521408 9529600 7 6 490 3085 23 _ _ (200863 / 12500) (1606907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9529600 :
    ThetaLowerSegment 9529600 9537792 (119060872301 / 12500) (476662110099 / 50000) := by
  exact
    thetaTile4096 9529600 9537792 7 6 521 3087 23 _ _ (160699 / 10000) (1606993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9537792 :
    ThetaLowerSegment 9537792 9545984 (476662110099 / 50000) (95414704311 / 10000) := by
  exact
    thetaTile4096 9537792 9545984 7 6 512 3088 23 _ _ (401769 / 25000) (1607079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9545984 :
    ThetaLowerSegment 9545984 9554176 (95414704311 / 10000) (238742075723 / 25000) := by
  exact
    thetaTile4096 9545984 9554176 7 6 511 3089 23 _ _ (803581 / 50000) (321433 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9554176 :
    ThetaLowerSegment 9554176 9562368 (238742075723 / 25000) (955789606109 / 100000) := by
  exact
    thetaTile4096 9554176 9562368 7 6 511 3090 23 _ _ (1607247 / 100000) (6429 / 400) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9562368 :
    ThetaLowerSegment 9562368 9570560 (955789606109 / 100000) (59787380913 / 6250) := by
  exact
    thetaTile4096 9562368 9570560 7 6 503 3092 23 _ _ (1607333 / 100000) (200917 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9570560 :
    ThetaLowerSegment 9570560 9578752 (59787380913 / 6250) (957432345069 / 100000) := by
  exact
    thetaTile4096 9570560 9578752 7 6 519 3093 23 _ _ (1607419 / 100000) (803711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9578752 :
    ThetaLowerSegment 9578752 9586944 (957432345069 / 100000) (958319687277 / 100000) := by
  exact
    thetaTile4096 9578752 9586944 7 6 552 3094 23 _ _ (100469 / 6250) (1607507 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9586944 :
    ThetaLowerSegment 9586944 9595136 (958319687277 / 100000) (959139558177 / 100000) := by
  exact
    thetaTile4096 9586944 9595136 7 6 510 3096 23 _ _ (160759 / 10000) (1607593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9595136 :
    ThetaLowerSegment 9595136 9603328 (959139558177 / 100000) (119993125419 / 12500) := by
  exact
    thetaTile4096 9595136 9603328 7 6 501 3097 23 _ _ (64307 / 4000) (803839 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9603328 :
    ThetaLowerSegment 9603328 9611520 (119993125419 / 12500) (960724767437 / 100000) := by
  exact
    thetaTile4096 9603328 9611520 7 6 485 3098 23 _ _ (1607761 / 100000) (401941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9611520 :
    ThetaLowerSegment 9611520 9619712 (960724767437 / 100000) (7692589681 / 800) := by
  exact
    thetaTile4096 9611520 9619712 7 6 528 3100 23 _ _ (803923 / 50000) (1607849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9619712 :
    ThetaLowerSegment 9619712 9627904 (7692589681 / 800) (120299822341 / 12500) := by
  exact
    thetaTile4096 9619712 9627904 7 6 513 3101 23 _ _ (1607931 / 100000) (803967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9627904 :
    ThetaLowerSegment 9627904 9636096 (120299822341 / 12500) (120400524343 / 12500) := by
  exact
    thetaTile4096 9627904 9636096 7 6 501 3102 23 _ _ (100501 / 6250) (1608019 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9636096 :
    ThetaLowerSegment 9636096 9644288 (120400524343 / 12500) (964016285749 / 100000) := by
  exact
    thetaTile4096 9636096 9644288 7 6 505 3104 23 _ _ (1608101 / 100000) (201013 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9644288 :
    ThetaLowerSegment 9644288 9652480 (964016285749 / 100000) (964867016143 / 100000) := by
  exact
    thetaTile4096 9644288 9652480 7 6 529 3105 23 _ _ (804093 / 50000) (1608189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9652480 :
    ThetaLowerSegment 9652480 9660672 (964867016143 / 100000) (965680801269 / 100000) := by
  exact
    thetaTile4096 9652480 9660672 7 6 506 3106 23 _ _ (1608271 / 100000) (804137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9660672 :
    ThetaLowerSegment 9660672 9668864 (965680801269 / 100000) (193302142593 / 20000) := by
  exact
    thetaTile4096 9660672 9668864 7 6 516 3108 23 _ _ (402089 / 25000) (1608359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9668864 :
    ThetaLowerSegment 9668864 9677056 (193302142593 / 20000) (967318150347 / 100000) := by
  exact
    thetaTile4096 9668864 9677056 7 6 502 3109 23 _ _ (1608441 / 100000) (402111 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9677056 :
    ThetaLowerSegment 9677056 9685248 (967318150347 / 100000) (968151366297 / 100000) := by
  exact
    thetaTile4096 9677056 9685248 7 6 518 3110 23 _ _ (64341 / 4000) (100533 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9685248 :
    ThetaLowerSegment 9685248 9693440 (968151366297 / 100000) (968966931567 / 100000) := by
  exact
    thetaTile4096 9685248 9693440 7 6 507 3112 23 _ _ (160861 / 10000) (1608613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9693440 :
    ThetaLowerSegment 9693440 9701632 (968966931567 / 100000) (969739104687 / 100000) := by
  exact
    thetaTile4096 9693440 9701632 7 6 480 3113 23 _ _ (804347 / 50000) (1608697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9701632 :
    ThetaLowerSegment 9701632 9709824 (969739104687 / 100000) (970572452209 / 100000) := by
  exact
    thetaTile4096 9701632 9709824 7 6 518 3114 23 _ _ (1608779 / 100000) (804391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9709824 :
    ThetaLowerSegment 9709824 9718016 (970572452209 / 100000) (971370448257 / 100000) := by
  exact
    thetaTile4096 9709824 9718016 7 6 496 3116 23 _ _ (1608863 / 100000) (804433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9718016 :
    ThetaLowerSegment 9718016 9726208 (971370448257 / 100000) (972195838581 / 100000) := by
  exact
    thetaTile4096 9718016 9726208 7 6 513 3117 23 _ _ (402237 / 25000) (1608951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9726208 :
    ThetaLowerSegment 9726208 9734400 (972195838581 / 100000) (194608759689 / 20000) := by
  exact
    thetaTile4096 9726208 9734400 7 6 527 3118 23 _ _ (201129 / 12500) (321807 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9734400 :
    ThetaLowerSegment 9734400 9742592 (194608759689 / 20000) (973859620257 / 100000) := by
  exact
    thetaTile4096 9734400 9742592 7 6 507 3120 23 _ _ (402279 / 25000) (1609119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9742592 :
    ThetaLowerSegment 9742592 9750784 (973859620257 / 100000) (974696404257 / 100000) := by
  exact
    thetaTile4096 9742592 9750784 7 6 520 3121 23 _ _ (4023 / 250) (1609203 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9750784 :
    ThetaLowerSegment 9750784 9758976 (974696404257 / 100000) (975494609121 / 100000) := by
  exact
    thetaTile4096 9750784 9758976 7 6 496 3122 23 _ _ (402321 / 25000) (1609287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9758976 :
    ThetaLowerSegment 9758976 9767168 (975494609121 / 100000) (976291246281 / 100000) := by
  exact
    thetaTile4096 9758976 9767168 7 6 495 3123 23 _ _ (201171 / 12500) (1609371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9767168 :
    ThetaLowerSegment 9767168 9775360 (976291246281 / 100000) (195423057141 / 20000) := by
  exact
    thetaTile4096 9767168 9775360 7 6 512 3125 23 _ _ (402363 / 25000) (321891 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9775360 :
    ThetaLowerSegment 9775360 9783552 (195423057141 / 20000) (977916834633 / 100000) := by
  exact
    thetaTile4096 9775360 9783552 7 6 498 3126 23 _ _ (50298 / 3125) (1609539 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9783552 :
    ThetaLowerSegment 9783552 9791744 (977916834633 / 100000) (978742569693 / 100000) := by
  exact
    thetaTile4096 9783552 9791744 7 6 513 3127 23 _ _ (80481 / 5000) (1609623 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9791744 :
    ThetaLowerSegment 9791744 9799936 (978742569693 / 100000) (979579615773 / 100000) := by
  exact
    thetaTile4096 9791744 9799936 7 6 520 3129 23 _ _ (201213 / 12500) (1609707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9799936 :
    ThetaLowerSegment 9799936 9808128 (979579615773 / 100000) (196085272747 / 20000) := by
  exact
    thetaTile4096 9799936 9808128 7 6 526 3130 23 _ _ (1609787 / 100000) (160979 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9808128 :
    ThetaLowerSegment 9808128 9816320 (196085272747 / 20000) (30662824091 / 3125) := by
  exact
    thetaTile4096 9808128 9816320 7 6 487 3131 23 _ _ (1609871 / 100000) (804937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9816320 :
    ThetaLowerSegment 9816320 9824512 (30662824091 / 3125) (491022968519 / 50000) := by
  exact
    thetaTile4096 9816320 9824512 7 6 519 3133 23 _ _ (804977 / 50000) (1609957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9824512 :
    ThetaLowerSegment 9824512 9832704 (491022968519 / 50000) (491448018551 / 50000) := by
  exact
    thetaTile4096 9824512 9832704 7 6 528 3134 23 _ _ (805019 / 50000) (1610041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9832704 :
    ThetaLowerSegment 9832704 9840896 (491448018551 / 50000) (983683386271 / 100000) := by
  exact
    thetaTile4096 9832704 9840896 7 6 489 3135 23 _ _ (1610121 / 100000) (402531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9840896 :
    ThetaLowerSegment 9840896 9849088 (983683386271 / 100000) (984478827047 / 100000) := by
  exact
    thetaTile4096 9840896 9849088 7 6 494 3137 23 _ _ (402551 / 25000) (1610207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9849088 :
    ThetaLowerSegment 9849088 9857280 (984478827047 / 100000) (246317369491 / 25000) := by
  exact
    thetaTile4096 9849088 9857280 7 6 491 3138 23 _ _ (1610287 / 100000) (161029 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9857280 :
    ThetaLowerSegment 9857280 9865472 (246317369491 / 25000) (246526717721 / 25000) := by
  exact
    thetaTile4096 9857280 9865472 7 6 520 3139 23 _ _ (1610371 / 100000) (805187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9865472 :
    ThetaLowerSegment 9865472 9873664 (246526717721 / 25000) (123364414849 / 12500) := by
  exact
    thetaTile4096 9865472 9873664 7 6 502 3140 23 _ _ (805227 / 50000) (1610457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9873664 :
    ThetaLowerSegment 9873664 9881856 (123364414849 / 12500) (987728639977 / 100000) := by
  exact
    thetaTile4096 9873664 9881856 7 6 505 3142 23 _ _ (1610537 / 100000) (80527 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9881856 :
    ThetaLowerSegment 9881856 9890048 (987728639977 / 100000) (988540392457 / 100000) := by
  exact
    thetaTile4096 9881856 9890048 7 6 504 3143 23 _ _ (80531 / 5000) (1610623 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9890048 :
    ThetaLowerSegment 9890048 9898240 (988540392457 / 100000) (989374736093 / 100000) := by
  exact
    thetaTile4096 9890048 9898240 7 6 518 3144 23 _ _ (805351 / 50000) (322141 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9898240 :
    ThetaLowerSegment 9898240 9906432 (989374736093 / 100000) (990170463883 / 100000) := by
  exact
    thetaTile4096 9898240 9906432 7 6 494 3146 23 _ _ (322157 / 20000) (402697 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9906432 :
    ThetaLowerSegment 9906432 9914624 (990170463883 / 100000) (990963010939 / 100000) := by
  exact
    thetaTile4096 9906432 9914624 7 6 492 3147 23 _ _ (402717 / 25000) (1610871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9914624 :
    ThetaLowerSegment 9914624 9922816 (990963010939 / 100000) (495891492499 / 50000) := by
  exact
    thetaTile4096 9914624 9922816 7 6 509 3148 23 _ _ (1610951 / 100000) (805477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9922816 :
    ThetaLowerSegment 9922816 9931008 (495891492499 / 50000) (992593334597 / 100000) := by
  exact
    thetaTile4096 9922816 9931008 7 6 503 3150 23 _ _ (1611033 / 100000) (402759 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9931008 :
    ThetaLowerSegment 9931008 9939200 (992593334597 / 100000) (993429503801 / 100000) := by
  exact
    thetaTile4096 9931008 9939200 7 6 519 3151 23 _ _ (402779 / 25000) (1611119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9939200 :
    ThetaLowerSegment 9939200 9947392 (993429503801 / 100000) (994251214781 / 100000) := by
  exact
    thetaTile4096 9939200 9947392 7 6 510 3152 23 _ _ (805599 / 50000) (1611201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9947392 :
    ThetaLowerSegment 9947392 9955584 (994251214781 / 100000) (995066522967 / 100000) := by
  exact
    thetaTile4096 9947392 9955584 7 6 506 3153 23 _ _ (1611281 / 100000) (402821 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9955584 :
    ThetaLowerSegment 9955584 9963776 (995066522967 / 100000) (995862536289 / 100000) := by
  exact
    thetaTile4096 9955584 9963776 7 6 494 3155 23 _ _ (1611363 / 100000) (805683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9963776 :
    ThetaLowerSegment 9963776 9971968 (995862536289 / 100000) (498341380897 / 50000) := by
  exact
    thetaTile4096 9963776 9971968 7 6 509 3156 23 _ _ (322289 / 20000) (201431 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9971968 :
    ThetaLowerSegment 9971968 9980160 (498341380897 / 50000) (7979946879 / 800) := by
  exact
    thetaTile4096 9971968 9980160 7 6 503 3157 23 _ _ (1611527 / 100000) (161153 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9980160 :
    ThetaLowerSegment 9980160 9988352 (7979946879 / 800) (249570359169 / 25000) := by
  exact
    thetaTile4096 9980160 9988352 7 6 489 3159 23 _ _ (1611609 / 100000) (402903 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9988352 :
    ThetaLowerSegment 9988352 9996544 (249570359169 / 25000) (249769403131 / 25000) := by
  exact
    thetaTile4096 9988352 9996544 7 6 494 3160 23 _ _ (402923 / 25000) (322339 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell9996544 :
    ThetaLowerSegment 9996544 10004736 (249769403131 / 25000) (199978956287 / 20000) := by
  exact
    thetaTile4096 9996544 10004736 7 6 507 3161 23 _ _ (1611773 / 100000) (50368 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10004736 :
    ThetaLowerSegment 10004736 10012928 (199978956287 / 20000) (50035921967 / 5000) := by
  exact
    thetaTile4096 10004736 10012928 7 6 511 3163 23 _ _ (322371 / 20000) (805929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10012928 :
    ThetaLowerSegment 10012928 10021120 (50035921967 / 5000) (100154052721 / 10000) := by
  exact
    thetaTile4096 10012928 10021120 7 6 510 3164 23 _ _ (1611937 / 100000) (80597 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10021120 :
    ThetaLowerSegment 10021120 10029312 (100154052721 / 10000) (1002380389109 / 100000) := by
  exact
    thetaTile4096 10021120 10029312 7 6 521 3165 23 _ _ (1612019 / 100000) (806011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10029312 :
    ThetaLowerSegment 10029312 10037504 (1002380389109 / 100000) (1003192888013 / 100000) := by
  exact
    thetaTile4096 10029312 10037504 7 6 504 3166 23 _ _ (1612101 / 100000) (201513 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10037504 :
    ThetaLowerSegment 10037504 10045696 (1003192888013 / 100000) (1004031222653 / 100000) := by
  exact
    thetaTile4096 10037504 10045696 7 6 520 3168 23 _ _ (806091 / 50000) (322437 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10045696 :
    ThetaLowerSegment 10045696 10053888 (1004031222653 / 100000) (1004864763141 / 100000) := by
  exact
    thetaTile4096 10045696 10053888 7 6 517 3169 23 _ _ (201533 / 12500) (1612267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10053888 :
    ThetaLowerSegment 10053888 10062080 (1004864763141 / 100000) (1005696733161 / 100000) := by
  exact
    thetaTile4096 10053888 10062080 7 6 516 3170 23 _ _ (322469 / 20000) (403087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10062080 :
    ThetaLowerSegment 10062080 10070272 (1005696733161 / 100000) (201298009449 / 20000) := by
  exact
    thetaTile4096 10062080 10070272 7 6 492 3172 23 _ _ (1612427 / 100000) (161243 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10070272 :
    ThetaLowerSegment 10070272 10078464 (201298009449 / 20000) (1007307588801 / 100000) := by
  exact
    thetaTile4096 10070272 10078464 7 6 507 3173 23 _ _ (403127 / 25000) (1612511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10078464 :
    ThetaLowerSegment 10078464 10086656 (1007307588801 / 100000) (1008147748191 / 100000) := by
  exact
    thetaTile4096 10078464 10086656 7 6 521 3174 23 _ _ (161259 / 10000) (1612593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10086656 :
    ThetaLowerSegment 10086656 10094848 (1008147748191 / 100000) (252244568439 / 25000) := by
  exact
    thetaTile4096 10086656 10094848 7 6 515 3175 23 _ _ (1612671 / 100000) (806337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10094848 :
    ThetaLowerSegment 10094848 10103040 (252244568439 / 25000) (252446162439 / 25000) := by
  exact
    thetaTile4096 10094848 10103040 7 6 500 3177 23 _ _ (100797 / 6250) (322551 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10103040 :
    ThetaLowerSegment 10103040 10111232 (252446162439 / 25000) (252649379397 / 25000) := by
  exact
    thetaTile4096 10103040 10111232 7 6 504 3178 23 _ _ (1612833 / 100000) (403209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10111232 :
    ThetaLowerSegment 10111232 10119424 (252649379397 / 25000) (505707632493 / 50000) := by
  exact
    thetaTile4096 10111232 10119424 7 6 507 3179 23 _ _ (806457 / 50000) (1612917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10119424 :
    ThetaLowerSegment 10119424 10127616 (505707632493 / 50000) (1012239505431 / 100000) := by
  exact
    thetaTile4096 10119424 10127616 7 6 511 3181 23 _ _ (322599 / 20000) (806499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10127616 :
    ThetaLowerSegment 10127616 10135808 (1012239505431 / 100000) (1013031525747 / 100000) := by
  exact
    thetaTile4096 10127616 10135808 7 6 491 3182 23 _ _ (403269 / 25000) (1613079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10135808 :
    ThetaLowerSegment 10135808 10144000 (1013031525747 / 100000) (506953734999 / 50000) := by
  exact
    thetaTile4096 10135808 10144000 7 6 543 3183 23 _ _ (1613157 / 100000) (40329 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10144000 :
    ThetaLowerSegment 10144000 10152192 (506953734999 / 50000) (63421142973 / 6250) := by
  exact
    thetaTile4096 10144000 10152192 7 6 515 3184 23 _ _ (806619 / 50000) (1613241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10152192 :
    ThetaLowerSegment 10152192 10160384 (63421142973 / 6250) (1015530427197 / 100000) := by
  exact
    thetaTile4096 10152192 10160384 7 6 491 3186 23 _ _ (1613319 / 100000) (806661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10160384 :
    ThetaLowerSegment 10160384 10168576 (1015530427197 / 100000) (1016333899899 / 100000) := by
  exact
    thetaTile4096 10160384 10168576 7 6 498 3187 23 _ _ (1613399 / 100000) (806701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10168576 :
    ThetaLowerSegment 10168576 10176768 (1016333899899 / 100000) (1017143866859 / 100000) := by
  exact
    thetaTile4096 10168576 10176768 7 6 502 3188 23 _ _ (40337 / 2500) (1613483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10176768 :
    ThetaLowerSegment 10176768 10184960 (1017143866859 / 100000) (1017955487539 / 100000) := by
  exact
    thetaTile4096 10176768 10184960 7 6 503 3190 23 _ _ (40339 / 2500) (1613563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10184960 :
    ThetaLowerSegment 10184960 10193152 (1017955487539 / 100000) (1018742944347 / 100000) := by
  exact
    thetaTile4096 10184960 10193152 7 6 488 3191 23 _ _ (1613641 / 100000) (403411 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10193152 :
    ThetaLowerSegment 10193152 10201344 (1018742944347 / 100000) (254886240921 / 25000) := by
  exact
    thetaTile4096 10193152 10201344 7 6 497 3192 23 _ _ (1613721 / 100000) (403431 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10201344 :
    ThetaLowerSegment 10201344 10209536 (254886240921 / 25000) (510188035857 / 50000) := by
  exact
    thetaTile4096 10201344 10209536 7 6 515 3193 23 _ _ (806901 / 50000) (322761 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10209536 :
    ThetaLowerSegment 10209536 10217728 (510188035857 / 50000) (255288087239 / 25000) := by
  exact
    thetaTile4096 10209536 10217728 7 6 481 3195 23 _ _ (806941 / 50000) (322777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10217728 :
    ThetaLowerSegment 10217728 10225920 (255288087239 / 25000) (510998225541 / 50000) := by
  exact
    thetaTile4096 10217728 10225920 7 6 523 3196 23 _ _ (806981 / 50000) (322793 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10225920 :
    ThetaLowerSegment 10225920 10234112 (510998225541 / 50000) (511417876461 / 50000) := by
  exact
    thetaTile4096 10225920 10234112 7 6 520 3197 23 _ _ (807021 / 50000) (322809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10234112 :
    ThetaLowerSegment 10234112 10242304 (511417876461 / 50000) (63977171457 / 6250) := by
  exact
    thetaTile4096 10234112 10242304 7 6 495 3199 23 _ _ (807061 / 50000) (12913 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10242304 :
    ThetaLowerSegment 10242304 10250496 (63977171457 / 6250) (256112882381 / 25000) := by
  exact
    thetaTile4096 10242304 10250496 7 6 506 3200 23 _ _ (807101 / 50000) (322841 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10250496 :
    ThetaLowerSegment 10250496 10258688 (256112882381 / 25000) (102527965619 / 10000) := by
  exact
    thetaTile4096 10250496 10258688 7 6 513 3201 23 _ _ (807141 / 50000) (322857 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10258688 :
    ThetaLowerSegment 10258688 10266880 (102527965619 / 10000) (12826589953 / 1250) := by
  exact
    thetaTile4096 10258688 10266880 7 6 525 3202 23 _ _ (807181 / 50000) (322873 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10266880 :
    ThetaLowerSegment 10266880 10275072 (12826589953 / 1250) (513480931377 / 50000) := by
  exact
    thetaTile4096 10266880 10275072 7 6 517 3204 23 _ _ (807221 / 50000) (322889 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10275072 :
    ThetaLowerSegment 10275072 10283264 (513480931377 / 50000) (513879718311 / 50000) := by
  exact
    thetaTile4096 10275072 10283264 7 6 494 3205 23 _ _ (807261 / 50000) (64581 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10283264 :
    ThetaLowerSegment 10283264 10291456 (513879718311 / 50000) (1028584497733 / 100000) := by
  exact
    thetaTile4096 10283264 10291456 7 6 511 3206 23 _ _ (1614601 / 100000) (403651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10291456 :
    ThetaLowerSegment 10291456 10299648 (1028584497733 / 100000) (257349170569 / 25000) := by
  exact
    thetaTile4096 10291456 10299648 7 6 503 3208 23 _ _ (1614681 / 100000) (403671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10299648 :
    ThetaLowerSegment 10299648 10307840 (257349170569 / 25000) (515103646149 / 50000) := by
  exact
    thetaTile4096 10299648 10307840 7 6 502 3209 23 _ _ (1614761 / 100000) (403691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10307840 :
    ThetaLowerSegment 10307840 10316032 (515103646149 / 50000) (515500896789 / 50000) := by
  exact
    thetaTile4096 10307840 10316032 7 6 492 3210 23 _ _ (40371 / 2500) (1614843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10316032 :
    ThetaLowerSegment 10316032 10324224 (515500896789 / 50000) (1031833476863 / 100000) := by
  exact
    thetaTile4096 10316032 10324224 7 6 515 3211 23 _ _ (1614919 / 100000) (807461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10324224 :
    ThetaLowerSegment 10324224 10332416 (1031833476863 / 100000) (516337445671 / 50000) := by
  exact
    thetaTile4096 10324224 10332416 7 6 521 3213 23 _ _ (1614999 / 100000) (807501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10332416 :
    ThetaLowerSegment 10332416 10340608 (516337445671 / 50000) (258377471667 / 25000) := by
  exact
    thetaTile4096 10332416 10340608 7 6 517 3214 23 _ _ (807539 / 50000) (1615081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10340608 :
    ThetaLowerSegment 10340608 10348800 (258377471667 / 25000) (1034283546871 / 100000) := by
  exact
    thetaTile4096 10340608 10348800 7 6 479 3215 23 _ _ (1615157 / 100000) (40379 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10348800 :
    ThetaLowerSegment 10348800 10356992 (1034283546871 / 100000) (258774810389 / 25000) := by
  exact
    thetaTile4096 10348800 10356992 7 6 505 3216 23 _ _ (1615237 / 100000) (40381 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10356992 :
    ThetaLowerSegment 10356992 10365184 (258774810389 / 25000) (258984801469 / 25000) := by
  exact
    thetaTile4096 10356992 10365184 7 6 520 3218 23 _ _ (403829 / 25000) (1615319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10365184 :
    ThetaLowerSegment 10365184 10373376 (258984801469 / 25000) (259194802819 / 25000) := by
  exact
    thetaTile4096 10365184 10373376 7 6 520 3219 23 _ _ (323079 / 20000) (807699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10373376 :
    ThetaLowerSegment 10373376 10381568 (259194802819 / 25000) (518781358083 / 50000) := by
  exact
    thetaTile4096 10373376 10381568 7 6 485 3220 23 _ _ (807737 / 50000) (1615477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10381568 :
    ThetaLowerSegment 10381568 10389760 (518781358083 / 50000) (1038388263749 / 100000) := by
  exact
    thetaTile4096 10381568 10389760 7 6 511 3222 23 _ _ (1615553 / 100000) (403889 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10389760 :
    ThetaLowerSegment 10389760 10397952 (1038388263749 / 100000) (1039242933077 / 100000) := by
  exact
    thetaTile4096 10389760 10397952 7 6 529 3223 23 _ _ (100977 / 6250) (323127 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10397952 :
    ThetaLowerSegment 10397952 10406144 (1039242933077 / 100000) (1040062098047 / 100000) := by
  exact
    thetaTile4096 10397952 10406144 7 6 507 3224 23 _ _ (161571 / 10000) (1615713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10406144 :
    ThetaLowerSegment 10406144 10414336 (1040062098047 / 100000) (104088130307 / 10000) := by
  exact
    thetaTile4096 10406144 10414336 7 6 507 3225 23 _ _ (1615789 / 100000) (100987 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10414336 :
    ThetaLowerSegment 10414336 10422528 (104088130307 / 10000) (520858353413 / 50000) := by
  exact
    thetaTile4096 10414336 10422528 7 6 517 3227 23 _ _ (403967 / 25000) (1615871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10422528 :
    ThetaLowerSegment 10422528 10430720 (520858353413 / 50000) (1042542455743 / 100000) := by
  exact
    thetaTile4096 10422528 10430720 7 6 511 3228 23 _ _ (1615947 / 100000) (32319 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10430720 :
    ThetaLowerSegment 10430720 10438912 (1042542455743 / 100000) (1043366628493 / 100000) := by
  exact
    thetaTile4096 10430720 10438912 7 6 510 3229 23 _ _ (64641 / 4000) (404007 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10438912 :
    ThetaLowerSegment 10438912 10447104 (1043366628493 / 100000) (1044185993221 / 100000) := by
  exact
    thetaTile4096 10438912 10447104 7 6 507 3230 23 _ _ (202013 / 12500) (1616107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10447104 :
    ThetaLowerSegment 10447104 10455296 (1044185993221 / 100000) (1045007013677 / 100000) := by
  exact
    thetaTile4096 10447104 10455296 7 6 508 3232 23 _ _ (808091 / 50000) (323237 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10455296 :
    ThetaLowerSegment 10455296 10463488 (1045007013677 / 100000) (1045811911157 / 100000) := by
  exact
    thetaTile4096 10455296 10463488 7 6 498 3233 23 _ _ (80813 / 5000) (1616263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10463488 :
    ThetaLowerSegment 10463488 10471680 (1045811911157 / 100000) (1046665338149 / 100000) := by
  exact
    thetaTile4096 10463488 10471680 7 6 528 3234 23 _ _ (1616339 / 100000) (808171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10471680 :
    ThetaLowerSegment 10471680 10479872 (1046665338149 / 100000) (1047480012317 / 100000) := by
  exact
    thetaTile4096 10471680 10479872 7 6 504 3235 23 _ _ (1616417 / 100000) (80821 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10479872 :
    ThetaLowerSegment 10479872 10488064 (1047480012317 / 100000) (1048291492807 / 100000) := by
  exact
    thetaTile4096 10479872 10488064 7 6 502 3237 23 _ _ (323299 / 20000) (808249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10488064 :
    ThetaLowerSegment 10488064 10496256 (1048291492807 / 100000) (52456686367 / 5000) := by
  exact
    thetaTile4096 10488064 10496256 7 6 521 3238 23 _ _ (1616573 / 100000) (50518 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10496256 :
    ThetaLowerSegment 10496256 10504448 (52456686367 / 5000) (524975876373 / 50000) := by
  exact
    thetaTile4096 10496256 10504448 7 6 506 3239 23 _ _ (1616651 / 100000) (808327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10504448 :
    ThetaLowerSegment 10504448 10512640 (524975876373 / 50000) (210155580253 / 20000) := by
  exact
    thetaTile4096 10504448 10512640 7 6 511 3241 23 _ _ (1616729 / 100000) (404183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10512640 :
    ThetaLowerSegment 10512640 10520832 (210155580253 / 20000) (262896980393 / 25000) := by
  exact
    thetaTile4096 10512640 10520832 7 6 501 3242 23 _ _ (1616807 / 100000) (161681 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10520832 :
    ThetaLowerSegment 10520832 10529024 (262896980393 / 25000) (1052388279647 / 100000) := by
  exact
    thetaTile4096 10520832 10529024 7 6 495 3243 23 _ _ (323377 / 20000) (202111 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10529024 :
    ThetaLowerSegment 10529024 10537216 (1052388279647 / 100000) (65825504993 / 6250) := by
  exact
    thetaTile4096 10529024 10537216 7 6 507 3244 23 _ _ (1616963 / 100000) (808483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10537216 :
    ThetaLowerSegment 10537216 10545408 (65825504993 / 6250) (105401983447 / 10000) := by
  exact
    thetaTile4096 10537216 10545408 7 6 502 3246 23 _ _ (1617041 / 100000) (404261 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10545408 :
    ThetaLowerSegment 10545408 10553600 (105401983447 / 10000) (1054855884993 / 100000) := by
  exact
    thetaTile4096 10545408 10553600 7 6 517 3247 23 _ _ (1617119 / 100000) (808561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10553600 :
    ThetaLowerSegment 10553600 10561792 (1054855884993 / 100000) (1055688740933 / 100000) := by
  exact
    thetaTile4096 10553600 10561792 7 6 515 3248 23 _ _ (404299 / 25000) (1617199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10561792 :
    ThetaLowerSegment 10561792 10569984 (1055688740933 / 100000) (211305297773 / 20000) := by
  exact
    thetaTile4096 10561792 10569984 7 6 518 3249 23 _ _ (808637 / 50000) (1617277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10569984 :
    ThetaLowerSegment 10569984 10578176 (211305297773 / 20000) (528660304103 / 50000) := by
  exact
    thetaTile4096 10569984 10578176 7 6 491 3251 23 _ _ (1617351 / 100000) (808677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10578176 :
    ThetaLowerSegment 10578176 10586368 (528660304103 / 50000) (529074365927 / 50000) := by
  exact
    thetaTile4096 10578176 10586368 7 6 512 3252 23 _ _ (1617429 / 100000) (202179 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10586368 :
    ThetaLowerSegment 10586368 10594560 (529074365927 / 50000) (529485212451 / 50000) := by
  exact
    thetaTile4096 10586368 10594560 7 6 508 3253 23 _ _ (808753 / 50000) (1617509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10594560 :
    ThetaLowerSegment 10594560 10602752 (529485212451 / 50000) (529885564491 / 50000) := by
  exact
    thetaTile4096 10594560 10602752 7 6 495 3254 23 _ _ (101099 / 6250) (1617587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10602752 :
    ThetaLowerSegment 10602752 10610944 (529885564491 / 50000) (265145798701 / 25000) := by
  exact
    thetaTile4096 10602752 10610944 7 6 502 3256 23 _ _ (1617661 / 100000) (50552 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10610944 :
    ThetaLowerSegment 10610944 10619136 (265145798701 / 25000) (530695223033 / 50000) := by
  exact
    thetaTile4096 10610944 10619136 7 6 499 3257 23 _ _ (808869 / 50000) (1617741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10619136 :
    ThetaLowerSegment 10619136 10627328 (530695223033 / 50000) (132779368187 / 12500) := by
  exact
    thetaTile4096 10619136 10627328 7 6 522 3258 23 _ _ (323563 / 20000) (808909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10627328 :
    ThetaLowerSegment 10627328 10635520 (132779368187 / 12500) (53152760837 / 5000) := by
  exact
    thetaTile4096 10627328 10635520 7 6 507 3259 23 _ _ (404473 / 25000) (323579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10635520 :
    ThetaLowerSegment 10635520 10643712 (53152760837 / 5000) (1063875527023 / 100000) := by
  exact
    thetaTile4096 10635520 10643712 7 6 507 3261 23 _ _ (1617969 / 100000) (404493 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10643712 :
    ThetaLowerSegment 10643712 10651904 (1063875527023 / 100000) (1064715292897 / 100000) := by
  exact
    thetaTile4096 10643712 10651904 7 6 519 3262 23 _ _ (809023 / 50000) (1618049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10651904 :
    ThetaLowerSegment 10651904 10660096 (1064715292897 / 100000) (266379875007 / 25000) := by
  exact
    thetaTile4096 10651904 10660096 7 6 497 3263 23 _ _ (1618123 / 100000) (809063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10660096 :
    ThetaLowerSegment 10660096 10668288 (266379875007 / 25000) (266584172757 / 25000) := by
  exact
    thetaTile4096 10660096 10668288 7 6 505 3264 23 _ _ (8091 / 500) (1618203 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10668288 :
    ThetaLowerSegment 10668288 10676480 (266584172757 / 25000) (1067208942331 / 100000) := by
  exact
    thetaTile4096 10668288 10676480 7 6 539 3266 23 _ _ (1618277 / 100000) (40457 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10676480 :
    ThetaLowerSegment 10676480 10684672 (1067208942331 / 100000) (1068026211101 / 100000) := by
  exact
    thetaTile4096 10676480 10684672 7 6 505 3267 23 _ _ (809177 / 50000) (1618357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10684672 :
    ThetaLowerSegment 10684672 10692864 (1068026211101 / 100000) (534426614671 / 50000) := by
  exact
    thetaTile4096 10684672 10692864 7 6 511 3268 23 _ _ (1618431 / 100000) (809217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10692864 :
    ThetaLowerSegment 10692864 10701056 (534426614671 / 50000) (1069673812391 / 100000) := by
  exact
    thetaTile4096 10692864 10701056 7 6 507 3269 23 _ _ (1618507 / 100000) (161851 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10701056 :
    ThetaLowerSegment 10701056 10709248 (1069673812391 / 100000) (1070505764567 / 100000) := by
  exact
    thetaTile4096 10701056 10709248 7 6 514 3271 23 _ _ (202323 / 12500) (1618587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10709248 :
    ThetaLowerSegment 10709248 10717440 (1070505764567 / 100000) (1071368510347 / 100000) := by
  exact
    thetaTile4096 10709248 10717440 7 6 533 3272 23 _ _ (80933 / 5000) (1618663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10717440 :
    ThetaLowerSegment 10717440 10725632 (1071368510347 / 100000) (536081655107 / 50000) := by
  exact
    thetaTile4096 10717440 10725632 7 6 491 3273 23 _ _ (1618737 / 100000) (80937 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10725632 :
    ThetaLowerSegment 10725632 10733824 (536081655107 / 50000) (536489595983 / 50000) := by
  exact
    thetaTile4096 10725632 10733824 7 6 504 3275 23 _ _ (1618813 / 100000) (50588 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10733824 :
    ThetaLowerSegment 10733824 10742016 (536489595983 / 50000) (268453230079 / 25000) := by
  exact
    thetaTile4096 10733824 10742016 7 6 515 3276 23 _ _ (161889 / 10000) (1618893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10742016 :
    ThetaLowerSegment 10742016 10750208 (268453230079 / 25000) (537303916311 / 50000) := by
  exact
    thetaTile4096 10742016 10750208 7 6 491 3277 23 _ _ (809483 / 50000) (1618969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10750208 :
    ThetaLowerSegment 10750208 10758400 (537303916311 / 50000) (53770786729 / 5000) := by
  exact
    thetaTile4096 10750208 10758400 7 6 499 3278 23 _ _ (809521 / 50000) (323809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10758400 :
    ThetaLowerSegment 10758400 10766592 (53770786729 / 5000) (269057942513 / 25000) := by
  exact
    thetaTile4096 10758400 10766592 7 6 504 3280 23 _ _ (809559 / 50000) (1619121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10766592 :
    ThetaLowerSegment 10766592 10774784 (269057942513 / 25000) (67312859049 / 6250) := by
  exact
    thetaTile4096 10766592 10774784 7 6 478 3281 23 _ _ (809597 / 50000) (1619197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10774784 :
    ThetaLowerSegment 10774784 10782976 (67312859049 / 6250) (269461131661 / 25000) := by
  exact
    thetaTile4096 10774784 10782976 7 6 518 3282 23 _ _ (161927 / 10000) (1619273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10782976 :
    ThetaLowerSegment 10782976 10791168 (269461131661 / 25000) (269655453181 / 25000) := by
  exact
    thetaTile4096 10782976 10791168 7 6 480 3283 23 _ _ (809673 / 50000) (1619349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10791168 :
    ThetaLowerSegment 10791168 10799360 (269655453181 / 25000) (269864358619 / 25000) := by
  exact
    thetaTile4096 10791168 10799360 7 6 516 3284 23 _ _ (809711 / 50000) (64777 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10799360 :
    ThetaLowerSegment 10799360 10807552 (269864358619 / 25000) (67517306279 / 6250) := by
  exact
    thetaTile4096 10799360 10807552 7 6 506 3286 23 _ _ (809749 / 50000) (1619501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10807552 :
    ThetaLowerSegment 10807552 10815744 (67517306279 / 6250) (270275720801 / 25000) := by
  exact
    thetaTile4096 10807552 10815744 7 6 510 3287 23 _ _ (809787 / 50000) (1619577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10815744 :
    ThetaLowerSegment 10815744 10823936 (270275720801 / 25000) (33809468447 / 3125) := by
  exact
    thetaTile4096 10815744 10823936 7 6 494 3288 23 _ _ (32393 / 2000) (1619653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10823936 :
    ThetaLowerSegment 10823936 10832128 (33809468447 / 3125) (108269827577 / 10000) := by
  exact
    thetaTile4096 10823936 10832128 7 6 491 3289 23 _ _ (809863 / 50000) (1619729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10832128 :
    ThetaLowerSegment 10832128 10840320 (108269827577 / 10000) (216712973861 / 20000) := by
  exact
    thetaTile4096 10832128 10840320 7 6 535 3291 23 _ _ (1619801 / 100000) (404951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10840320 :
    ThetaLowerSegment 10840320 10848512 (216712973861 / 20000) (271098156613 / 25000) := by
  exact
    thetaTile4096 10840320 10848512 7 6 511 3292 23 _ _ (1619877 / 100000) (40497 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10848512 :
    ThetaLowerSegment 10848512 10856704 (271098156613 / 25000) (271301865577 / 25000) := by
  exact
    thetaTile4096 10848512 10856704 7 6 503 3293 23 _ _ (101247 / 6250) (323991 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10856704 :
    ThetaLowerSegment 10856704 10864896 (271301865577 / 25000) (271510849189 / 25000) := by
  exact
    thetaTile4096 10856704 10864896 7 6 516 3294 23 _ _ (405007 / 25000) (1620031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10864896 :
    ThetaLowerSegment 10864896 10873088 (271510849189 / 25000) (1086855068359 / 100000) := by
  exact
    thetaTile4096 10864896 10873088 7 6 501 3296 23 _ _ (1620103 / 100000) (810053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10873088 :
    ThetaLowerSegment 10873088 10881280 (1086855068359 / 100000) (1087648956069 / 100000) := by
  exact
    thetaTile4096 10873088 10881280 7 6 490 3297 23 _ _ (1620179 / 100000) (810091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10881280 :
    ThetaLowerSegment 10881280 10889472 (1087648956069 / 100000) (1088468804593 / 100000) := by
  exact
    thetaTile4096 10881280 10889472 7 6 506 3298 23 _ _ (810127 / 50000) (1620257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10889472 :
    ThetaLowerSegment 10889472 10897664 (1088468804593 / 100000) (544643535369 / 50000) := by
  exact
    thetaTile4096 10889472 10897664 7 6 505 3299 23 _ _ (1620329 / 100000) (405083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10897664 :
    ThetaLowerSegment 10897664 10905856 (544643535369 / 50000) (545072132227 / 50000) := by
  exact
    thetaTile4096 10897664 10905856 7 6 529 3301 23 _ _ (405101 / 25000) (1620407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10905856 :
    ThetaLowerSegment 10905856 10914048 (545072132227 / 50000) (545468339587 / 50000) := by
  exact
    thetaTile4096 10905856 10914048 7 6 489 3302 23 _ _ (10128 / 625) (1620483 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10914048 :
    ThetaLowerSegment 10914048 10922240 (545468339587 / 50000) (1091751818339 / 100000) := by
  exact
    thetaTile4096 10914048 10922240 7 6 503 3303 23 _ _ (324111 / 20000) (810279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10922240 :
    ThetaLowerSegment 10922240 10930432 (1091751818339 / 100000) (1092607510979 / 100000) := by
  exact
    thetaTile4096 10922240 10930432 7 6 528 3304 23 _ _ (162063 / 10000) (1620633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10930432 :
    ThetaLowerSegment 10930432 10938624 (1092607510979 / 100000) (1093408139249 / 100000) := by
  exact
    thetaTile4096 10930432 10938624 7 6 494 3306 23 _ _ (324141 / 20000) (405177 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10938624 :
    ThetaLowerSegment 10938624 10946816 (1093408139249 / 100000) (1094255807189 / 100000) := by
  exact
    thetaTile4096 10938624 10946816 7 6 523 3307 23 _ _ (81039 / 5000) (1620783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10946816 :
    ThetaLowerSegment 10946816 10955008 (1094255807189 / 100000) (1095071096751 / 100000) := by
  exact
    thetaTile4096 10946816 10955008 7 6 503 3308 23 _ _ (810427 / 50000) (1620857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10955008 :
    ThetaLowerSegment 10955008 10963200 (1095071096751 / 100000) (273977279261 / 25000) := by
  exact
    thetaTile4096 10955008 10963200 7 6 517 3309 23 _ _ (1620929 / 100000) (405233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10963200 :
    ThetaLowerSegment 10963200 10971392 (273977279261 / 25000) (274175852251 / 25000) := by
  exact
    thetaTile4096 10963200 10971392 7 6 490 3311 23 _ _ (405251 / 25000) (1621007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10971392 :
    ThetaLowerSegment 10971392 10979584 (274175852251 / 25000) (43900493097 / 4000) := by
  exact
    thetaTile4096 10971392 10979584 7 6 499 3312 23 _ _ (1621079 / 100000) (810541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10979584 :
    ThetaLowerSegment 10979584 10987776 (43900493097 / 4000) (1098342357761 / 100000) := by
  exact
    thetaTile4096 10979584 10987776 7 6 512 3313 23 _ _ (1621153 / 100000) (405289 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10987776 :
    ThetaLowerSegment 10987776 10995968 (1098342357761 / 100000) (1099156214217 / 100000) := by
  exact
    thetaTile4096 10987776 10995968 7 6 502 3314 23 _ _ (405307 / 25000) (1621231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell10995968 :
    ThetaLowerSegment 10995968 11004160 (1099156214217 / 100000) (1099984699539 / 100000) := by
  exact
    thetaTile4096 10995968 11004160 7 6 511 3316 23 _ _ (810651 / 50000) (324261 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11004160 :
    ThetaLowerSegment 11004160 11012352 (1099984699539 / 100000) (137596383423 / 12500) := by
  exact
    thetaTile4096 11004160 11012352 7 6 485 3317 23 _ _ (1621377 / 100000) (81069 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11012352 :
    ThetaLowerSegment 11012352 11020544 (137596383423 / 12500) (1101563956923 / 100000) := by
  exact
    thetaTile4096 11012352 11020544 7 6 489 3318 23 _ _ (1621451 / 100000) (810727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11020544 :
    ThetaLowerSegment 11020544 11028736 (1101563956923 / 100000) (1102387692131 / 100000) := by
  exact
    thetaTile4096 11020544 11028736 7 6 508 3319 23 _ _ (810763 / 50000) (1621529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11028736 :
    ThetaLowerSegment 11028736 11036928 (1102387692131 / 100000) (1103193627331 / 100000) := by
  exact
    thetaTile4096 11028736 11036928 7 6 497 3320 23 _ _ (2027 / 125) (1621603 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11036928 :
    ThetaLowerSegment 11036928 11045120 (1103193627331 / 100000) (1104036897811 / 100000) := by
  exact
    thetaTile4096 11036928 11045120 7 6 520 3322 23 _ _ (810837 / 50000) (1621677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11045120 :
    ThetaLowerSegment 11045120 11053312 (1104036897811 / 100000) (220973770907 / 20000) := by
  exact
    thetaTile4096 11045120 11053312 7 6 513 3323 23 _ _ (405437 / 25000) (1621751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11053312 :
    ThetaLowerSegment 11053312 11061504 (220973770907 / 20000) (221142440499 / 20000) := by
  exact
    thetaTile4096 11053312 11061504 7 6 520 3324 23 _ _ (1621823 / 100000) (810913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11061504 :
    ThetaLowerSegment 11061504 11069696 (221142440499 / 20000) (553264008343 / 50000) := by
  exact
    thetaTile4096 11061504 11069696 7 6 503 3325 23 _ _ (1621897 / 100000) (16219 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11069696 :
    ThetaLowerSegment 11069696 11077888 (553264008343 / 50000) (553679232919 / 50000) := by
  exact
    thetaTile4096 11069696 11077888 7 6 512 3327 23 _ _ (1621971 / 100000) (810987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11077888 :
    ThetaLowerSegment 11077888 11086080 (553679232919 / 50000) (554084744169 / 50000) := by
  exact
    thetaTile4096 11077888 11086080 7 6 500 3328 23 _ _ (324409 / 20000) (50689 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11086080 :
    ThetaLowerSegment 11086080 11094272 (554084744169 / 50000) (1109027589289 / 100000) := by
  exact
    thetaTile4096 11086080 11094272 7 6 529 3329 23 _ _ (1622119 / 100000) (811061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11094272 :
    ThetaLowerSegment 11094272 11102464 (1109027589289 / 100000) (1109845174057 / 100000) := by
  exact
    thetaTile4096 11094272 11102464 7 6 504 3330 23 _ _ (101387 / 6250) (324439 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11102464 :
    ThetaLowerSegment 11102464 11110656 (1109845174057 / 100000) (1110683885579 / 100000) := by
  exact
    thetaTile4096 11102464 11110656 7 6 517 3332 23 _ _ (811133 / 50000) (1622269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11110656 :
    ThetaLowerSegment 11110656 11118848 (1110683885579 / 100000) (1111485321539 / 100000) := by
  exact
    thetaTile4096 11110656 11118848 7 6 494 3333 23 _ _ (81117 / 5000) (1622343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11118848 :
    ThetaLowerSegment 11118848 11127040 (1111485321539 / 100000) (44490173831 / 4000) := by
  exact
    thetaTile4096 11118848 11127040 7 6 474 3334 23 _ _ (811207 / 50000) (1622417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11127040 :
    ThetaLowerSegment 11127040 11135232 (44490173831 / 4000) (1113059099327 / 100000) := by
  exact
    thetaTile4096 11127040 11135232 7 6 496 3335 23 _ _ (1622487 / 100000) (162249 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11135232 :
    ThetaLowerSegment 11135232 11143424 (1113059099327 / 100000) (222776672063 / 20000) := by
  exact
    thetaTile4096 11135232 11143424 7 6 508 3336 23 _ _ (1622561 / 100000) (405641 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11143424 :
    ThetaLowerSegment 11143424 11151616 (222776672063 / 20000) (2786781317 / 250) := by
  exact
    thetaTile4096 11143424 11151616 7 6 511 3338 23 _ _ (324527 / 20000) (811319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11151616 :
    ThetaLowerSegment 11151616 11159808 (2786781317 / 250) (278881375877 / 25000) := by
  exact
    thetaTile4096 11151616 11159808 7 6 501 3339 23 _ _ (405677 / 25000) (1622711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11159808 :
    ThetaLowerSegment 11159808 11168000 (278881375877 / 25000) (1116374217971 / 100000) := by
  exact
    thetaTile4096 11159808 11168000 7 6 523 3340 23 _ _ (1622781 / 100000) (50712 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11168000 :
    ThetaLowerSegment 11168000 11176192 (1116374217971 / 100000) (139651248537 / 12500) := by
  exact
    thetaTile4096 11168000 11176192 7 6 515 3341 23 _ _ (324571 / 20000) (811429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11176192 :
    ThetaLowerSegment 11176192 11184384 (139651248537 / 12500) (223610133 / 20) := by
  exact
    thetaTile4096 11176192 11184384 7 6 518 3343 23 _ _ (101433 / 6250) (1622931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11184384 :
    ThetaLowerSegment 11184384 11192576 (223610133 / 20) (559432705751 / 50000) := by
  exact
    thetaTile4096 11184384 11192576 7 6 502 3344 23 _ _ (1623001 / 100000) (405751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11192576 :
    ThetaLowerSegment 11192576 11200768 (559432705751 / 50000) (139958401319 / 12500) := by
  exact
    thetaTile4096 11192576 11200768 7 6 494 3345 23 _ _ (64923 / 4000) (811539 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11200768 :
    ThetaLowerSegment 11200768 11208960 (139958401319 / 12500) (280122536647 / 25000) := by
  exact
    thetaTile4096 11200768 11208960 7 6 507 3346 23 _ _ (405787 / 25000) (1623151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11208960 :
    ThetaLowerSegment 11208960 11217152 (280122536647 / 25000) (44851875497 / 4000) := by
  exact
    thetaTile4096 11208960 11217152 7 6 497 3347 23 _ _ (1623221 / 100000) (202903 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11217152 :
    ThetaLowerSegment 11217152 11225344 (44851875497 / 4000) (1122113404307 / 100000) := by
  exact
    thetaTile4096 11217152 11225344 7 6 503 3349 23 _ _ (811647 / 50000) (1623297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11225344 :
    ThetaLowerSegment 11225344 11233536 (1122113404307 / 100000) (561460108853 / 50000) := by
  exact
    thetaTile4096 11225344 11233536 7 6 497 3350 23 _ _ (1623367 / 100000) (162337 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11233536 :
    ThetaLowerSegment 11233536 11241728 (561460108853 / 50000) (561867592293 / 50000) := by
  exact
    thetaTile4096 11233536 11241728 7 6 502 3351 23 _ _ (20293 / 1250) (1623443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11241728 :
    ThetaLowerSegment 11241728 11249920 (561867592293 / 50000) (562283211621 / 50000) := by
  exact
    thetaTile4096 11241728 11249920 7 6 512 3352 23 _ _ (1623513 / 100000) (405879 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11249920 :
    ThetaLowerSegment 11249920 11258112 (562283211621 / 50000) (35168424417 / 3125) := by
  exact
    thetaTile4096 11249920 11258112 7 6 507 3354 23 _ _ (811793 / 50000) (1623589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11258112 :
    ThetaLowerSegment 11258112 11266304 (35168424417 / 3125) (281554411731 / 25000) := by
  exact
    thetaTile4096 11258112 11266304 7 6 510 3355 23 _ _ (811829 / 50000) (1623661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11266304 :
    ThetaLowerSegment 11266304 11274496 (281554411731 / 25000) (1127005156459 / 100000) := by
  exact
    thetaTile4096 11266304 11274496 7 6 485 3356 23 _ _ (1623731 / 100000) (811867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11274496 :
    ThetaLowerSegment 11274496 11282688 (1127005156459 / 100000) (1127797572811 / 100000) := by
  exact
    thetaTile4096 11274496 11282688 7 6 488 3357 23 _ _ (405951 / 25000) (1623807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11282688 :
    ThetaLowerSegment 11282688 11290880 (1127797572811 / 100000) (564313686979 / 50000) := by
  exact
    thetaTile4096 11282688 11290880 7 6 511 3358 23 _ _ (1623877 / 100000) (40597 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11290880 :
    ThetaLowerSegment 11290880 11299072 (564313686979 / 50000) (1129457211897 / 100000) := by
  exact
    thetaTile4096 11290880 11299072 7 6 511 3360 23 _ _ (1623949 / 100000) (101497 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11299072 :
    ThetaLowerSegment 11299072 11307264 (1129457211897 / 100000) (1130256230721 / 100000) := by
  exact
    thetaTile4096 11299072 11307264 7 6 492 3361 23 _ _ (812011 / 50000) (64961 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11307264 :
    ThetaLowerSegment 11307264 11315456 (1130256230721 / 100000) (1131084518661 / 100000) := by
  exact
    thetaTile4096 11307264 11315456 7 6 510 3362 23 _ _ (812047 / 50000) (1624097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11315456 :
    ThetaLowerSegment 11315456 11323648 (1131084518661 / 100000) (226379970099 / 20000) := by
  exact
    thetaTile4096 11315456 11323648 7 6 502 3363 23 _ _ (1624167 / 100000) (162417 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11323648 :
    ThetaLowerSegment 11323648 11331840 (226379970099 / 20000) (70795614789 / 6250) := by
  exact
    thetaTile4096 11323648 11331840 7 6 511 3365 23 _ _ (1624239 / 100000) (812121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11331840 :
    ThetaLowerSegment 11331840 11340032 (70795614789 / 6250) (1133537119191 / 100000) := by
  exact
    thetaTile4096 11331840 11340032 7 6 497 3366 23 _ _ (1624311 / 100000) (812157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11340032 :
    ThetaLowerSegment 11340032 11348224 (1133537119191 / 100000) (45373842477 / 4000) := by
  exact
    thetaTile4096 11340032 11348224 7 6 498 3367 23 _ _ (1624383 / 100000) (812193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11348224 :
    ThetaLowerSegment 11348224 11356416 (45373842477 / 4000) (227033282441 / 20000) := by
  exact
    thetaTile4096 11348224 11356416 7 6 505 3368 23 _ _ (203057 / 12500) (1624459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11356416 :
    ThetaLowerSegment 11356416 11364608 (227033282441 / 20000) (1135996546013 / 100000) := by
  exact
    thetaTile4096 11356416 11364608 7 6 511 3369 23 _ _ (101533 / 6250) (1624531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11364608 :
    ThetaLowerSegment 11364608 11372800 (1135996546013 / 100000) (1136790975413 / 100000) := by
  exact
    thetaTile4096 11364608 11372800 7 6 489 3371 23 _ _ (8123 / 500) (1624603 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11372800 :
    ThetaLowerSegment 11372800 11380992 (1136790975413 / 100000) (1137600062069 / 100000) := by
  exact
    thetaTile4096 11372800 11380992 7 6 498 3372 23 _ _ (50771 / 3125) (64987 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11380992 :
    ThetaLowerSegment 11380992 11389184 (1137600062069 / 100000) (1138404310349 / 100000) := by
  exact
    thetaTile4096 11380992 11389184 7 6 495 3373 23 _ _ (203093 / 12500) (1624747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11389184 :
    ThetaLowerSegment 11389184 11397376 (1138404310349 / 100000) (227848543081 / 20000) := by
  exact
    thetaTile4096 11389184 11397376 7 6 516 3374 23 _ _ (101551 / 6250) (1624819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11397376 :
    ThetaLowerSegment 11397376 11405568 (227848543081 / 20000) (1140064908733 / 100000) := by
  exact
    thetaTile4096 11397376 11405568 7 6 506 3376 23 _ _ (203111 / 12500) (1624891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11405568 :
    ThetaLowerSegment 11405568 11413760 (1140064908733 / 100000) (1140861139133 / 100000) := by
  exact
    thetaTile4096 11405568 11413760 7 6 490 3377 23 _ _ (10156 / 625) (1624963 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11413760 :
    ThetaLowerSegment 11413760 11421952 (1140861139133 / 100000) (1141702905709 / 100000) := by
  exact
    thetaTile4096 11413760 11421952 7 6 518 3378 23 _ _ (203129 / 12500) (325007 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11421952 :
    ThetaLowerSegment 11421952 11430144 (1141702905709 / 100000) (571260166259 / 50000) := by
  exact
    thetaTile4096 11421952 11430144 7 6 503 3379 23 _ _ (1625103 / 100000) (812553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11430144 :
    ThetaLowerSegment 11430144 11438336 (571260166259 / 50000) (1143285789943 / 100000) := by
  exact
    thetaTile4096 11430144 11438336 7 6 471 3380 23 _ _ (65007 / 4000) (812589 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11438336 :
    ThetaLowerSegment 11438336 11446528 (1143285789943 / 100000) (1144134168877 / 100000) := by
  exact
    thetaTile4096 11438336 11446528 7 6 522 3382 23 _ _ (1625247 / 100000) (6501 / 400) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11446528 :
    ThetaLowerSegment 11446528 11454720 (1144134168877 / 100000) (228989690639 / 20000) := by
  exact
    thetaTile4096 11446528 11454720 7 6 501 3383 23 _ _ (812659 / 50000) (1625321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11454720 :
    ThetaLowerSegment 11454720 11462912 (228989690639 / 20000) (229161331823 / 20000) := by
  exact
    thetaTile4096 11454720 11462912 7 6 528 3384 23 _ _ (162539 / 10000) (1625393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11462912 :
    ThetaLowerSegment 11462912 11471104 (229161331823 / 20000) (573315383921 / 50000) := by
  exact
    thetaTile4096 11462912 11471104 7 6 507 3385 23 _ _ (1625461 / 100000) (203183 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11471104 :
    ThetaLowerSegment 11471104 11479296 (573315383921 / 50000) (1147464666271 / 100000) := by
  exact
    thetaTile4096 11471104 11479296 7 6 513 3386 23 _ _ (1625533 / 100000) (50798 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11479296 :
    ThetaLowerSegment 11479296 11487488 (1147464666271 / 100000) (1148272591459 / 100000) := by
  exact
    thetaTile4096 11479296 11487488 7 6 497 3388 23 _ _ (406401 / 25000) (1625607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11487488 :
    ThetaLowerSegment 11487488 11495680 (1148272591459 / 100000) (1149085428959 / 100000) := by
  exact
    thetaTile4096 11487488 11495680 7 6 500 3389 23 _ _ (65027 / 4000) (812839 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11495680 :
    ThetaLowerSegment 11495680 11503872 (1149085428959 / 100000) (229982261687 / 20000) := by
  exact
    thetaTile4096 11495680 11503872 7 6 508 3390 23 _ _ (1625747 / 100000) (6503 / 400) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11503872 :
    ThetaLowerSegment 11503872 11512064 (229982261687 / 20000) (1150704707619 / 100000) := by
  exact
    thetaTile4096 11503872 11512064 7 6 488 3391 23 _ _ (812909 / 50000) (1625821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11512064 :
    ThetaLowerSegment 11512064 11520256 (1150704707619 / 100000) (287871690057 / 25000) := by
  exact
    thetaTile4096 11512064 11520256 7 6 481 3392 23 _ _ (1625889 / 100000) (406473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11520256 :
    ThetaLowerSegment 11520256 11528448 (287871690057 / 25000) (288085503797 / 25000) := by
  exact
    thetaTile4096 11520256 11528448 7 6 526 3394 23 _ _ (40649 / 2500) (1625963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11528448 :
    ThetaLowerSegment 11528448 11536640 (288085503797 / 25000) (1153169664967 / 100000) := by
  exact
    thetaTile4096 11528448 11536640 7 6 509 3395 23 _ _ (1626031 / 100000) (813017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11536640 :
    ThetaLowerSegment 11536640 11544832 (1153169664967 / 100000) (1154044507843 / 100000) := by
  exact
    thetaTile4096 11536640 11544832 7 6 538 3396 23 _ _ (813051 / 50000) (325221 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11544832 :
    ThetaLowerSegment 11544832 11553024 (1154044507843 / 100000) (288714805129 / 25000) := by
  exact
    thetaTile4096 11544832 11553024 7 6 501 3397 23 _ _ (1626173 / 100000) (50818 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11553024 :
    ThetaLowerSegment 11553024 11561216 (288714805129 / 25000) (144458432973 / 12500) := by
  exact
    thetaTile4096 11553024 11561216 7 6 497 3398 23 _ _ (406561 / 25000) (1626247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11561216 :
    ThetaLowerSegment 11561216 11569408 (144458432973 / 12500) (1156495258119 / 100000) := by
  exact
    thetaTile4096 11561216 11569408 7 6 509 3400 23 _ _ (325263 / 20000) (813159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11569408 :
    ThetaLowerSegment 11569408 11577600 (1156495258119 / 100000) (1157287308101 / 100000) := by
  exact
    thetaTile4096 11569408 11577600 7 6 487 3401 23 _ _ (813193 / 50000) (1626389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11577600 :
    ThetaLowerSegment 11577600 11585792 (1157287308101 / 100000) (1158142824483 / 100000) := by
  exact
    thetaTile4096 11577600 11585792 7 6 526 3402 23 _ _ (1626457 / 100000) (81323 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11585792 :
    ThetaLowerSegment 11585792 11593984 (1158142824483 / 100000) (1158952835427 / 100000) := by
  exact
    thetaTile4096 11585792 11593984 7 6 498 3403 23 _ _ (50829 / 3125) (1626531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11593984 :
    ThetaLowerSegment 11593984 11602176 (1158952835427 / 100000) (1159756374839 / 100000) := by
  exact
    thetaTile4096 11593984 11602176 7 6 494 3404 23 _ _ (813299 / 50000) (1626601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11602176 :
    ThetaLowerSegment 11602176 11610368 (1159756374839 / 100000) (580313321377 / 50000) := by
  exact
    thetaTile4096 11602176 11610368 7 6 535 3406 23 _ _ (1626669 / 100000) (101667 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11610368 :
    ThetaLowerSegment 11610368 11618560 (580313321377 / 50000) (58074766069 / 5000) := by
  exact
    thetaTile4096 11610368 11618560 7 6 534 3407 23 _ _ (1626739 / 100000) (813371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11618560 :
    ThetaLowerSegment 11618560 11626752 (58074766069 / 5000) (11623282481 / 1000) := by
  exact
    thetaTile4096 11618560 11626752 7 6 512 3408 23 _ _ (162681 / 10000) (1626813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11626752 :
    ThetaLowerSegment 11626752 11634944 (11623282481 / 1000) (58155782901 / 5000) := by
  exact
    thetaTile4096 11626752 11634944 7 6 484 3409 23 _ _ (10168 / 625) (1626883 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11634944 :
    ThetaLowerSegment 11634944 11643136 (58155782901 / 5000) (1163878698039 / 100000) := by
  exact
    thetaTile4096 11634944 11643136 7 6 469 3411 23 _ _ (1626951 / 100000) (813477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11643136 :
    ThetaLowerSegment 11643136 11651328 (1163878698039 / 100000) (145589983487 / 12500) := by
  exact
    thetaTile4096 11643136 11651328 7 6 517 3412 23 _ _ (1627021 / 100000) (101689 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11651328 :
    ThetaLowerSegment 11651328 11659520 (145589983487 / 12500) (145695744467 / 12500) := by
  exact
    thetaTile4096 11651328 11659520 7 6 520 3413 23 _ _ (406773 / 25000) (325419 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11659520 :
    ThetaLowerSegment 11659520 11667712 (145695744467 / 12500) (583197090597 / 50000) := by
  exact
    thetaTile4096 11659520 11667712 7 6 509 3414 23 _ _ (813581 / 50000) (325433 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11667712 :
    ThetaLowerSegment 11667712 11675904 (583197090597 / 50000) (583594948821 / 50000) := by
  exact
    thetaTile4096 11667712 11675904 7 6 489 3415 23 _ _ (50851 / 3125) (325447 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11675904 :
    ThetaLowerSegment 11675904 11684096 (583594948821 / 50000) (11679693753 / 1000) := by
  exact
    thetaTile4096 11675904 11684096 7 6 479 3417 23 _ _ (813651 / 50000) (325461 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11684096 :
    ThetaLowerSegment 11684096 11692288 (11679693753 / 1000) (146102561357 / 12500) := by
  exact
    thetaTile4096 11684096 11692288 7 6 523 3418 23 _ _ (406843 / 25000) (13019 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11692288 :
    ThetaLowerSegment 11692288 11700480 (146102561357 / 12500) (233931073823 / 20000) := by
  exact
    thetaTile4096 11692288 11700480 7 6 513 3419 23 _ _ (1627443 / 100000) (813723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11700480 :
    ThetaLowerSegment 11700480 11708672 (233931073823 / 20000) (1170459360537 / 100000) := by
  exact
    thetaTile4096 11700480 11708672 7 6 494 3420 23 _ _ (1627513 / 100000) (406879 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11708672 :
    ThetaLowerSegment 11708672 11716864 (1170459360537 / 100000) (585632507061 / 50000) := by
  exact
    thetaTile4096 11708672 11716864 7 6 495 3421 23 _ _ (1627583 / 100000) (813793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11716864 :
    ThetaLowerSegment 11716864 11725056 (585632507061 / 50000) (586041047713 / 50000) := by
  exact
    thetaTile4096 11716864 11725056 7 6 502 3422 23 _ _ (406913 / 25000) (325531 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11725056 :
    ThetaLowerSegment 11725056 11733248 (586041047713 / 50000) (586447978213 / 50000) := by
  exact
    thetaTile4096 11725056 11733248 7 6 500 3424 23 _ _ (813861 / 50000) (65109 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11733248 :
    ThetaLowerSegment 11733248 11741440 (586447978213 / 50000) (586859809589 / 50000) := by
  exact
    thetaTile4096 11733248 11741440 7 6 506 3425 23 _ _ (101737 / 6250) (325559 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11741440 :
    ThetaLowerSegment 11741440 11749632 (586859809589 / 50000) (146818525117 / 12500) := by
  exact
    thetaTile4096 11741440 11749632 7 6 509 3426 23 _ _ (813931 / 50000) (325573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11749632 :
    ThetaLowerSegment 11749632 11757824 (146818525117 / 12500) (146920270867 / 12500) := by
  exact
    thetaTile4096 11749632 11757824 7 6 500 3427 23 _ _ (406983 / 25000) (325587 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11757824 :
    ThetaLowerSegment 11757824 11766016 (146920270867 / 12500) (1176138723413 / 100000) := by
  exact
    thetaTile4096 11757824 11766016 7 6 477 3428 23 _ _ (1628001 / 100000) (407001 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11766016 :
    ThetaLowerSegment 11766016 11774208 (1176138723413 / 100000) (36780231611 / 3125) := by
  exact
    thetaTile4096 11766016 11774208 7 6 509 3430 23 _ _ (1628071 / 100000) (814037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11774208 :
    ThetaLowerSegment 11774208 11782400 (36780231611 / 3125) (58889725359 / 5000) := by
  exact
    thetaTile4096 11774208 11782400 7 6 508 3431 23 _ _ (1628141 / 100000) (101759 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11782400 :
    ThetaLowerSegment 11782400 11790592 (58889725359 / 5000) (58932384461 / 5000) := by
  exact
    thetaTile4096 11782400 11790592 7 6 524 3432 23 _ _ (162821 / 10000) (1628213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11790592 :
    ThetaLowerSegment 11790592 11798784 (58932384461 / 5000) (58972684391 / 5000) := by
  exact
    thetaTile4096 11790592 11798784 7 6 495 3433 23 _ _ (40707 / 2500) (1628283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11798784 :
    ThetaLowerSegment 11798784 11806976 (58972684391 / 5000) (1180305314347 / 100000) := by
  exact
    thetaTile4096 11798784 11806976 7 6 523 3434 23 _ _ (1628349 / 100000) (50886 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11806976 :
    ThetaLowerSegment 11806976 11815168 (1180305314347 / 100000) (1181116267009 / 100000) := by
  exact
    thetaTile4096 11806976 11815168 7 6 498 3436 23 _ _ (1628419 / 100000) (814211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11815168 :
    ThetaLowerSegment 11815168 11823360 (1181116267009 / 100000) (236385125109 / 20000) := by
  exact
    thetaTile4096 11815168 11823360 7 6 497 3437 23 _ _ (203561 / 12500) (1628491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11823360 :
    ThetaLowerSegment 11823360 11831552 (236385125109 / 20000) (591367509187 / 50000) := by
  exact
    thetaTile4096 11823360 11831552 7 6 497 3438 23 _ _ (1628557 / 100000) (20357 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11831552 :
    ThetaLowerSegment 11831552 11839744 (591367509187 / 50000) (1183550960501 / 100000) := by
  exact
    thetaTile4096 11831552 11839744 7 6 501 3439 23 _ _ (1628627 / 100000) (162863 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11839744 :
    ThetaLowerSegment 11839744 11847936 (1183550960501 / 100000) (1184316447621 / 100000) := by
  exact
    thetaTile4096 11839744 11847936 7 6 470 3440 23 _ _ (203587 / 12500) (1628699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11847936 :
    ThetaLowerSegment 11847936 11856128 (1184316447621 / 100000) (1185134087651 / 100000) := by
  exact
    thetaTile4096 11847936 11856128 7 6 502 3442 23 _ _ (325753 / 20000) (50899 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11856128 :
    ThetaLowerSegment 11856128 11864320 (1185134087651 / 100000) (1185994112003 / 100000) := by
  exact
    thetaTile4096 11856128 11864320 7 6 528 3443 23 _ _ (814417 / 50000) (1628837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11864320 :
    ThetaLowerSegment 11864320 11872512 (1185994112003 / 100000) (237363015823 / 20000) := by
  exact
    thetaTile4096 11864320 11872512 7 6 504 3444 24 _ _ (1628903 / 100000) (814453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11872512 :
    ThetaLowerSegment 11872512 11880704 (237363015823 / 20000) (1187665402499 / 100000) := by
  exact
    thetaTile4096 11872512 11880704 7 6 522 3445 24 _ _ (407243 / 25000) (65159 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11880704 :
    ThetaLowerSegment 11880704 11888896 (1187665402499 / 100000) (1188460374507 / 100000) := by
  exact
    thetaTile4096 11880704 11888896 7 6 488 3446 24 _ _ (1629041 / 100000) (407261 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11888896 :
    ThetaLowerSegment 11888896 11897088 (1188460374507 / 100000) (1189273300397 / 100000) := by
  exact
    thetaTile4096 11888896 11897088 7 6 499 3448 24 _ _ (162911 / 10000) (1629113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11897088 :
    ThetaLowerSegment 11897088 11905280 (1189273300397 / 100000) (1190113956761 / 100000) := by
  exact
    thetaTile4096 11897088 11905280 7 6 516 3449 24 _ _ (1629179 / 100000) (814591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11905280 :
    ThetaLowerSegment 11905280 11913472 (1190113956761 / 100000) (1190918805273 / 100000) := by
  exact
    thetaTile4096 11905280 11913472 7 6 494 3450 24 _ _ (50914 / 3125) (1629251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11913472 :
    ThetaLowerSegment 11913472 11921664 (1190918805273 / 100000) (119173509309 / 10000) := by
  exact
    thetaTile4096 11913472 11921664 7 6 501 3451 24 _ _ (1629317 / 100000) (40733 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11921664 :
    ThetaLowerSegment 11921664 11929856 (119173509309 / 10000) (238522666321 / 20000) := by
  exact
    thetaTile4096 11921664 11929856 7 6 539 3452 24 _ _ (325877 / 20000) (407347 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11929856 :
    ThetaLowerSegment 11929856 11938048 (238522666321 / 20000) (1193388951709 / 100000) := by
  exact
    thetaTile4096 11929856 11938048 7 6 476 3453 24 _ _ (814727 / 50000) (1629457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11938048 :
    ThetaLowerSegment 11938048 11946240 (1193388951709 / 100000) (597110818981 / 50000) := by
  exact
    thetaTile4096 11938048 11946240 7 6 511 3455 24 _ _ (1629523 / 100000) (814763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11946240 :
    ThetaLowerSegment 11946240 11954432 (597110818981 / 50000) (74692017779 / 6250) := by
  exact
    thetaTile4096 11946240 11954432 7 6 522 3456 24 _ _ (1629591 / 100000) (814797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11954432 :
    ThetaLowerSegment 11954432 11962624 (74692017779 / 6250) (74744166899 / 6250) := by
  exact
    thetaTile4096 11954432 11962624 7 6 512 3457 24 _ _ (81483 / 5000) (1629663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11962624 :
    ThetaLowerSegment 11962624 11970816 (74744166899 / 6250) (74793466171 / 6250) := by
  exact
    thetaTile4096 11962624 11970816 7 6 484 3458 24 _ _ (50929 / 3125) (1629731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11970816 :
    ThetaLowerSegment 11970816 11979008 (74793466171 / 6250) (1197502208251 / 100000) := by
  exact
    thetaTile4096 11970816 11979008 7 6 495 3459 24 _ _ (1629797 / 100000) (8149 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11979008 :
    ThetaLowerSegment 11979008 11987200 (1197502208251 / 100000) (299584582249 / 25000) := by
  exact
    thetaTile4096 11979008 11987200 7 6 513 3461 24 _ _ (325973 / 20000) (407467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11987200 :
    ThetaLowerSegment 11987200 11995392 (299584582249 / 25000) (149894161937 / 12500) := by
  exact
    thetaTile4096 11987200 11995392 7 6 500 3462 24 _ _ (1629933 / 100000) (101871 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell11995392 :
    ThetaLowerSegment 11995392 12003584 (149894161937 / 12500) (119994710647 / 10000) := by
  exact
    thetaTile4096 11995392 12003584 7 6 487 3463 24 _ _ (815001 / 50000) (326001 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12003584 :
    ThetaLowerSegment 12003584 12011776 (119994710647 / 10000) (120076540161 / 10000) := by
  exact
    thetaTile4096 12003584 12011776 7 6 502 3464 24 _ _ (163007 / 10000) (1630073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12011776 :
    ThetaLowerSegment 12011776 12019968 (120076540161 / 10000) (150202245473 / 12500) := by
  exact
    thetaTile4096 12011776 12019968 7 6 523 3465 24 _ _ (815069 / 50000) (1630141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12019968 :
    ThetaLowerSegment 12019968 12028160 (150202245473 / 12500) (300599300563 / 25000) := by
  exact
    thetaTile4096 12019968 12028160 7 6 478 3466 24 _ _ (815103 / 50000) (1630209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12028160 :
    ThetaLowerSegment 12028160 12036352 (300599300563 / 25000) (1203217230577 / 100000) := by
  exact
    thetaTile4096 12028160 12036352 7 6 503 3468 24 _ _ (65211 / 4000) (815139 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12036352 :
    ThetaLowerSegment 12036352 12044544 (1203217230577 / 100000) (1204029141391 / 100000) := by
  exact
    thetaTile4096 12036352 12044544 7 6 498 3469 24 _ _ (1630343 / 100000) (815173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12044544 :
    ThetaLowerSegment 12044544 12052736 (1204029141391 / 100000) (1204831303603 / 100000) := by
  exact
    thetaTile4096 12044544 12052736 7 6 492 3470 24 _ _ (1630411 / 100000) (815207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12052736 :
    ThetaLowerSegment 12052736 12060928 (1204831303603 / 100000) (301425902467 / 25000) := by
  exact
    thetaTile4096 12052736 12060928 7 6 535 3471 24 _ _ (1630479 / 100000) (815241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12060928 :
    ThetaLowerSegment 12060928 12069120 (301425902467 / 25000) (1206507469539 / 100000) := by
  exact
    thetaTile4096 12060928 12069120 7 6 493 3472 24 _ _ (1630547 / 100000) (32611 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12069120 :
    ThetaLowerSegment 12069120 12077312 (1206507469539 / 100000) (1207329299499 / 100000) := by
  exact
    thetaTile4096 12069120 12077312 7 6 504 3474 24 _ _ (326123 / 20000) (815309 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12077312 :
    ThetaLowerSegment 12077312 12085504 (1207329299499 / 100000) (241623383781 / 20000) := by
  exact
    thetaTile4096 12077312 12085504 7 6 483 3475 24 _ _ (815341 / 50000) (326137 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12085504 :
    ThetaLowerSegment 12085504 12093696 (241623383781 / 20000) (241785154181 / 20000) := by
  exact
    thetaTile4096 12085504 12093696 7 6 496 3476 24 _ _ (6523 / 400) (1630753 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12093696 :
    ThetaLowerSegment 12093696 12101888 (241785154181 / 20000) (48388994869 / 4000) := by
  exact
    thetaTile4096 12093696 12101888 7 6 490 3477 24 _ _ (815409 / 50000) (1630821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12101888 :
    ThetaLowerSegment 12101888 12110080 (48388994869 / 4000) (1210551730927 / 100000) := by
  exact
    thetaTile4096 12101888 12110080 7 6 507 3478 24 _ _ (815443 / 50000) (1630889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12110080 :
    ThetaLowerSegment 12110080 12118272 (1210551730927 / 100000) (1211403088393 / 100000) := by
  exact
    thetaTile4096 12110080 12118272 7 6 522 3479 24 _ _ (1630953 / 100000) (407739 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12118272 :
    ThetaLowerSegment 12118272 12126464 (1211403088393 / 100000) (151525489963 / 12500) := by
  exact
    thetaTile4096 12118272 12126464 7 6 491 3481 24 _ _ (1631021 / 100000) (101939 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12126464 :
    ThetaLowerSegment 12126464 12134656 (151525489963 / 12500) (1213021095293 / 100000) := by
  exact
    thetaTile4096 12126464 12134656 7 6 501 3482 24 _ _ (1631089 / 100000) (407773 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12134656 :
    ThetaLowerSegment 12134656 12142848 (1213021095293 / 100000) (48554902349 / 4000) := by
  exact
    thetaTile4096 12134656 12142848 7 6 522 3483 24 _ _ (407789 / 25000) (1631159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12142848 :
    ThetaLowerSegment 12142848 12151040 (48554902349 / 4000) (1214711007861 / 100000) := by
  exact
    thetaTile4096 12142848 12151040 7 6 514 3484 24 _ _ (203903 / 12500) (1631227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12151040 :
    ThetaLowerSegment 12151040 12159232 (1214711007861 / 100000) (243100110541 / 20000) := by
  exact
    thetaTile4096 12151040 12159232 7 6 484 3485 24 _ _ (1631291 / 100000) (815647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12159232 :
    ThetaLowerSegment 12159232 12167424 (243100110541 / 20000) (1216317863063 / 100000) := by
  exact
    thetaTile4096 12159232 12167424 7 6 501 3487 24 _ _ (815679 / 50000) (1631361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12167424 :
    ThetaLowerSegment 12167424 12175616 (1216317863063 / 100000) (1217143364619 / 100000) := by
  exact
    thetaTile4096 12167424 12175616 7 6 506 3488 24 _ _ (815713 / 50000) (1631429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12175616 :
    ThetaLowerSegment 12175616 12183808 (1217143364619 / 100000) (1217926481259 / 100000) := by
  exact
    thetaTile4096 12175616 12183808 7 6 480 3489 24 _ _ (1631493 / 100000) (203937 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12183808 :
    ThetaLowerSegment 12183808 12192000 (1217926481259 / 100000) (1218753682179 / 100000) := by
  exact
    thetaTile4096 12183808 12192000 7 6 507 3490 24 _ _ (40789 / 2500) (1631563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12192000 :
    ThetaLowerSegment 12192000 12200192 (1218753682179 / 100000) (1219558074783 / 100000) := by
  exact
    thetaTile4096 12192000 12200192 7 6 493 3491 24 _ _ (407907 / 25000) (1631631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12200192 :
    ThetaLowerSegment 12200192 12208384 (1219558074783 / 100000) (1220377185673 / 100000) := by
  exact
    thetaTile4096 12200192 12208384 7 6 502 3492 24 _ _ (326339 / 20000) (815849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12208384 :
    ThetaLowerSegment 12208384 12216576 (1220377185673 / 100000) (1221228965437 / 100000) := by
  exact
    thetaTile4096 12208384 12216576 7 6 522 3494 24 _ _ (815881 / 50000) (326353 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12216576 :
    ThetaLowerSegment 12216576 12224768 (1221228965437 / 100000) (152754590099 / 12500) := by
  exact
    thetaTile4096 12216576 12224768 7 6 495 3495 24 _ _ (1631829 / 100000) (203979 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12224768 :
    ThetaLowerSegment 12224768 12232960 (152754590099 / 12500) (38215114838 / 3125) := by
  exact
    thetaTile4096 12224768 12232960 7 6 519 3496 24 _ _ (203987 / 12500) (1631899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12232960 :
    ThetaLowerSegment 12232960 12241152 (38215114838 / 3125) (611841668343 / 50000) := by
  exact
    thetaTile4096 12232960 12241152 7 6 490 3497 24 _ _ (1631963 / 100000) (815983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12241152 :
    ThetaLowerSegment 12241152 12249344 (611841668343 / 50000) (153058950897 / 12500) := by
  exact
    thetaTile4096 12241152 12249344 7 6 483 3498 24 _ _ (163203 / 10000) (1632033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12249344 :
    ThetaLowerSegment 12249344 12257536 (153058950897 / 12500) (1225292551967 / 100000) := by
  exact
    thetaTile4096 12249344 12257536 7 6 503 3499 24 _ _ (1632097 / 100000) (16321 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12257536 :
    ThetaLowerSegment 12257536 12265728 (1225292551967 / 100000) (245224011823 / 20000) := by
  exact
    thetaTile4096 12257536 12265728 7 6 507 3501 24 _ _ (408041 / 25000) (1632167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12265728 :
    ThetaLowerSegment 12265728 12273920 (245224011823 / 20000) (245390172837 / 20000) := by
  exact
    thetaTile4096 12265728 12273920 7 6 509 3502 24 _ _ (163223 / 10000) (1632233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12273920 :
    ThetaLowerSegment 12273920 12282112 (245390172837 / 20000) (613874528709 / 50000) := by
  exact
    thetaTile4096 12273920 12282112 7 6 489 3503 24 _ _ (1632297 / 100000) (16323 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12282112 :
    ThetaLowerSegment 12282112 12290304 (613874528709 / 50000) (614292413893 / 50000) := by
  exact
    thetaTile4096 12282112 12290304 7 6 512 3504 24 _ _ (408091 / 25000) (1632367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12290304 :
    ThetaLowerSegment 12290304 12298496 (614292413893 / 50000) (245883147033 / 20000) := by
  exact
    thetaTile4096 12290304 12298496 7 6 509 3505 24 _ _ (1632431 / 100000) (816217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12298496 :
    ThetaLowerSegment 12298496 12306688 (245883147033 / 20000) (1230258103617 / 100000) := by
  exact
    thetaTile4096 12298496 12306688 7 6 516 3506 24 _ _ (1632497 / 100000) (653 / 40) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12306688 :
    ThetaLowerSegment 12306688 12314880 (1230258103617 / 100000) (1231113567153 / 100000) := by
  exact
    thetaTile4096 12306688 12314880 7 6 524 3508 24 _ _ (408141 / 25000) (1632567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12314880 :
    ThetaLowerSegment 12314880 12323072 (1231113567153 / 100000) (1231938045303 / 100000) := by
  exact
    thetaTile4096 12314880 12323072 7 6 505 3509 24 _ _ (163263 / 10000) (1632633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12323072 :
    ThetaLowerSegment 12323072 12331264 (1231938045303 / 100000) (616360053583 / 50000) := by
  exact
    thetaTile4096 12323072 12331264 7 6 479 3510 24 _ _ (1632697 / 100000) (16327 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12331264 :
    ThetaLowerSegment 12331264 12339456 (616360053583 / 50000) (123351689551 / 10000) := by
  exact
    thetaTile4096 12331264 12339456 7 6 488 3511 24 _ _ (1632763 / 100000) (816383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12339456 :
    ThetaLowerSegment 12339456 12347648 (123351689551 / 10000) (123432024787 / 10000) := by
  exact
    thetaTile4096 12339456 12347648 7 6 492 3512 24 _ _ (163283 / 10000) (1632833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12347648 :
    ThetaLowerSegment 12347648 12355840 (123432024787 / 10000) (617579778207 / 50000) := by
  exact
    thetaTile4096 12347648 12355840 7 6 514 3513 24 _ _ (51028 / 3125) (1632899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12355840 :
    ThetaLowerSegment 12355840 12364032 (617579778207 / 50000) (30900748129 / 2500) := by
  exact
    thetaTile4096 12355840 12364032 7 6 533 3515 24 _ _ (816481 / 50000) (326593 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12364032 :
    ThetaLowerSegment 12364032 12372224 (30900748129 / 2500) (1236883999327 / 100000) := by
  exact
    thetaTile4096 12364032 12372224 7 6 523 3516 24 _ _ (1633029 / 100000) (204129 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12372224 :
    ThetaLowerSegment 12372224 12380416 (1236883999327 / 100000) (1237694014447 / 100000) := by
  exact
    thetaTile4096 12372224 12380416 7 6 496 3517 24 _ _ (326619 / 20000) (816549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12380416 :
    ThetaLowerSegment 12380416 12388608 (1237694014447 / 100000) (38702894693 / 3125) := by
  exact
    thetaTile4096 12380416 12388608 7 6 489 3518 24 _ _ (1633161 / 100000) (408291 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12388608 :
    ThetaLowerSegment 12388608 12396800 (38702894693 / 3125) (1239323942719 / 100000) := by
  exact
    thetaTile4096 12388608 12396800 7 6 509 3519 24 _ _ (1633227 / 100000) (163323 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12396800 :
    ThetaLowerSegment 12396800 12404992 (1239323942719 / 100000) (62006784467 / 5000) := by
  exact
    thetaTile4096 12396800 12404992 7 6 497 3520 24 _ _ (1633293 / 100000) (102081 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12404992 :
    ThetaLowerSegment 12404992 12413184 (62006784467 / 5000) (248198640563 / 20000) := by
  exact
    thetaTile4096 12404992 12413184 7 6 525 3522 24 _ _ (1633359 / 100000) (816681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12413184 :
    ThetaLowerSegment 12413184 12421376 (248198640563 / 20000) (15522889373 / 1250) := by
  exact
    thetaTile4096 12413184 12421376 7 6 513 3523 24 _ _ (65337 / 4000) (408357 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12421376 :
    ThetaLowerSegment 12421376 12429568 (15522889373 / 1250) (1242636460903 / 100000) := by
  exact
    thetaTile4096 12421376 12429568 7 6 493 3524 24 _ _ (1633491 / 100000) (816747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12429568 :
    ThetaLowerSegment 12429568 12437760 (1242636460903 / 100000) (124343853739 / 10000) := by
  exact
    thetaTile4096 12429568 12437760 7 6 491 3525 24 _ _ (1633557 / 100000) (40839 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12437760 :
    ThetaLowerSegment 12437760 12445952 (124343853739 / 10000) (311066287657 / 25000) := by
  exact
    thetaTile4096 12437760 12445952 7 6 506 3526 24 _ _ (1633623 / 100000) (816813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12445952 :
    ThetaLowerSegment 12445952 12454144 (311066287657 / 25000) (4980314911 / 400) := by
  exact
    thetaTile4096 12445952 12454144 7 6 498 3527 24 _ _ (1633689 / 100000) (408423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12454144 :
    ThetaLowerSegment 12454144 12462336 (4980314911 / 400) (249183368813 / 20000) := by
  exact
    thetaTile4096 12454144 12462336 7 6 513 3529 24 _ _ (326751 / 20000) (816879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12462336 :
    ThetaLowerSegment 12462336 12470528 (249183368813 / 20000) (623341553057 / 50000) := by
  exact
    thetaTile4096 12462336 12470528 7 6 469 3530 24 _ _ (1633821 / 100000) (51057 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12470528 :
    ThetaLowerSegment 12470528 12478720 (623341553057 / 50000) (623769631189 / 50000) := by
  exact
    thetaTile4096 12470528 12478720 7 6 524 3531 24 _ _ (816943 / 50000) (1633889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12478720 :
    ThetaLowerSegment 12478720 12486912 (623769631189 / 50000) (624177302213 / 50000) := by
  exact
    thetaTile4096 12478720 12486912 7 6 499 3532 24 _ _ (51061 / 3125) (326791 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12486912 :
    ThetaLowerSegment 12486912 12495104 (624177302213 / 50000) (312291677843 / 25000) := by
  exact
    thetaTile4096 12486912 12495104 7 6 497 3533 24 _ _ (817009 / 50000) (1634021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12495104 :
    ThetaLowerSegment 12495104 12503296 (312291677843 / 25000) (624957560693 / 50000) := by
  exact
    thetaTile4096 12495104 12503296 7 6 458 3534 24 _ _ (1634083 / 100000) (817043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12503296 :
    ThetaLowerSegment 12503296 12511488 (624957560693 / 50000) (78170149437 / 6250) := by
  exact
    thetaTile4096 12503296 12511488 7 6 494 3536 24 _ _ (1634149 / 100000) (204269 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12511488 :
    ThetaLowerSegment 12511488 12519680 (78170149437 / 6250) (312895496889 / 25000) := by
  exact
    thetaTile4096 12511488 12519680 7 6 526 3537 24 _ _ (817107 / 50000) (1634217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12519680 :
    ThetaLowerSegment 12519680 12527872 (312895496889 / 25000) (313107953289 / 25000) := by
  exact
    thetaTile4096 12519680 12527872 7 6 520 3538 24 _ _ (40857 / 2500) (1634283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12527872 :
    ThetaLowerSegment 12527872 12536064 (313107953289 / 25000) (313304074689 / 25000) := by
  exact
    thetaTile4096 12527872 12536064 7 6 480 3539 24 _ _ (326869 / 20000) (408587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12536064 :
    ThetaLowerSegment 12536064 12544256 (313304074689 / 25000) (12540400419 / 1000) := by
  exact
    thetaTile4096 12536064 12544256 7 6 504 3540 24 _ _ (1634411 / 100000) (817207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12544256 :
    ThetaLowerSegment 12544256 12552448 (12540400419 / 1000) (313711051023 / 25000) := by
  exact
    thetaTile4096 12544256 12552448 7 6 492 3541 24 _ _ (408619 / 25000) (1634479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12552448 :
    ThetaLowerSegment 12552448 12560640 (313711051023 / 25000) (313913734107 / 25000) := by
  exact
    thetaTile4096 12552448 12560640 7 6 496 3542 24 _ _ (1634541 / 100000) (102159 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12560640 :
    ThetaLowerSegment 12560640 12568832 (313913734107 / 25000) (628227129381 / 50000) := by
  exact
    thetaTile4096 12560640 12568832 7 6 489 3544 24 _ _ (817303 / 50000) (1634609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12568832 :
    ThetaLowerSegment 12568832 12577024 (628227129381 / 50000) (628632528037 / 50000) := by
  exact
    thetaTile4096 12568832 12577024 7 6 496 3545 24 _ _ (102167 / 6250) (65387 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12577024 :
    ThetaLowerSegment 12577024 12585216 (628632528037 / 50000) (629051020709 / 50000) := by
  exact
    thetaTile4096 12577024 12585216 7 6 512 3546 24 _ _ (1634737 / 100000) (81737 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12585216 :
    ThetaLowerSegment 12585216 12593408 (629051020709 / 50000) (629466260417 / 50000) := by
  exact
    thetaTile4096 12585216 12593408 7 6 508 3547 24 _ _ (817401 / 50000) (326961 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12593408 :
    ThetaLowerSegment 12593408 12601600 (629466260417 / 50000) (251950971787 / 20000) := by
  exact
    thetaTile4096 12593408 12601600 7 6 503 3548 24 _ _ (1634867 / 100000) (163487 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12601600 :
    ThetaLowerSegment 12601600 12609792 (251950971787 / 20000) (1260587039323 / 100000) := by
  exact
    thetaTile4096 12601600 12609792 7 6 509 3549 24 _ _ (408733 / 25000) (326987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12609792 :
    ThetaLowerSegment 12609792 12617984 (1260587039323 / 100000) (1261424157787 / 100000) := by
  exact
    thetaTile4096 12609792 12617984 7 6 512 3551 24 _ _ (1634997 / 100000) (327 / 20) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12617984 :
    ThetaLowerSegment 12617984 12626176 (1261424157787 / 100000) (1262222068043 / 100000) := by
  exact
    thetaTile4096 12617984 12626176 7 6 488 3552 24 _ _ (817531 / 50000) (327013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12626176 :
    ThetaLowerSegment 12626176 12634368 (1262222068043 / 100000) (157884654933 / 12500) := by
  exact
    thetaTile4096 12626176 12634368 7 6 523 3553 24 _ _ (1635127 / 100000) (163513 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12634368 :
    ThetaLowerSegment 12634368 12642560 (157884654933 / 12500) (78992916219 / 6250) := by
  exact
    thetaTile4096 12634368 12642560 7 6 495 3554 24 _ _ (204399 / 12500) (327039 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12642560 :
    ThetaLowerSegment 12642560 12650752 (78992916219 / 6250) (158085787461 / 12500) := by
  exact
    thetaTile4096 12642560 12650752 7 6 489 3555 24 _ _ (204407 / 12500) (1635259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12650752 :
    ThetaLowerSegment 12650752 12658944 (158085787461 / 12500) (1265489242299 / 100000) := by
  exact
    thetaTile4096 12650752 12658944 7 6 491 3556 24 _ _ (1635321 / 100000) (408831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12658944 :
    ThetaLowerSegment 12658944 12667136 (1265489242299 / 100000) (1266282404509 / 100000) := by
  exact
    thetaTile4096 12658944 12667136 7 6 485 3557 24 _ _ (817693 / 50000) (1635389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12667136 :
    ThetaLowerSegment 12667136 12675328 (1266282404509 / 100000) (253421988543 / 20000) := by
  exact
    thetaTile4096 12667136 12675328 7 6 506 3559 24 _ _ (1635451 / 100000) (817727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12675328 :
    ThetaLowerSegment 12675328 12683520 (253421988543 / 20000) (253591427897 / 20000) := by
  exact
    thetaTile4096 12675328 12683520 7 6 518 3560 24 _ _ (327103 / 20000) (817759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12683520 :
    ThetaLowerSegment 12683520 12691712 (253591427897 / 20000) (253754004549 / 20000) := by
  exact
    thetaTile4096 12683520 12691712 7 6 497 3561 24 _ _ (81779 / 5000) (1635583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12691712 :
    ThetaLowerSegment 12691712 12699904 (253754004549 / 20000) (253922475881 / 20000) := by
  exact
    thetaTile4096 12691712 12699904 7 6 515 3562 24 _ _ (408911 / 25000) (1635647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12699904 :
    ThetaLowerSegment 12699904 12708096 (253922475881 / 20000) (254076232527 / 20000) := by
  exact
    thetaTile4096 12699904 12708096 7 6 470 3563 24 _ _ (1635709 / 100000) (51116 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12708096 :
    ThetaLowerSegment 12708096 12716288 (254076232527 / 20000) (635621607503 / 50000) := by
  exact
    thetaTile4096 12708096 12716288 7 6 527 3564 24 _ _ (1635773 / 100000) (51118 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12716288 :
    ThetaLowerSegment 12716288 12724480 (635621607503 / 50000) (318018964137 / 25000) := by
  exact
    thetaTile4096 12716288 12724480 7 6 509 3565 24 _ _ (817919 / 50000) (1635841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12724480 :
    ThetaLowerSegment 12724480 12732672 (318018964137 / 25000) (159113770821 / 12500) := by
  exact
    thetaTile4096 12724480 12732672 7 6 510 3567 24 _ _ (817951 / 50000) (327181 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12732672 :
    ThetaLowerSegment 12732672 12740864 (159113770821 / 12500) (636875526803 / 50000) := by
  exact
    thetaTile4096 12732672 12740864 7 6 514 3568 24 _ _ (1635967 / 100000) (163597 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12740864 :
    ThetaLowerSegment 12740864 12749056 (636875526803 / 50000) (318644721323 / 25000) := by
  exact
    thetaTile4096 12740864 12749056 7 6 506 3569 24 _ _ (1636031 / 100000) (818017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12749056 :
    ThetaLowerSegment 12749056 12757248 (318644721323 / 25000) (318850869293 / 25000) := by
  exact
    thetaTile4096 12749056 12757248 7 6 504 3570 24 _ _ (327219 / 20000) (818049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12757248 :
    ThetaLowerSegment 12757248 12765440 (318850869293 / 25000) (319054571213 / 25000) := by
  exact
    thetaTile4096 12757248 12765440 7 6 498 3571 24 _ _ (10226 / 625) (1636163 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12765440 :
    ThetaLowerSegment 12765440 12773632 (319054571213 / 25000) (319262371661 / 25000) := by
  exact
    thetaTile4096 12765440 12773632 7 6 508 3572 24 _ _ (51132 / 3125) (1636227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12773632 :
    ThetaLowerSegment 12773632 12781824 (319262371661 / 25000) (319470589309 / 25000) := by
  exact
    thetaTile4096 12773632 12781824 7 6 509 3574 24 _ _ (51134 / 3125) (1636291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12781824 :
    ThetaLowerSegment 12781824 12790016 (319470589309 / 25000) (319672678781 / 25000) := by
  exact
    thetaTile4096 12781824 12790016 7 6 494 3575 24 _ _ (51136 / 3125) (327271 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12790016 :
    ThetaLowerSegment 12790016 12798208 (319672678781 / 25000) (319876821677 / 25000) := by
  exact
    thetaTile4096 12790016 12798208 7 6 499 3576 24 _ _ (51138 / 3125) (1636419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12798208 :
    ThetaLowerSegment 12798208 12806400 (319876821677 / 25000) (320086700237 / 25000) := by
  exact
    thetaTile4096 12798208 12806400 7 6 513 3577 24 _ _ (10228 / 625) (1636483 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12806400 :
    ThetaLowerSegment 12806400 12814592 (320086700237 / 25000) (320285540333 / 25000) := by
  exact
    thetaTile4096 12806400 12814592 7 6 486 3578 24 _ _ (51142 / 3125) (1636547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12814592 :
    ThetaLowerSegment 12814592 12822784 (320285540333 / 25000) (320485615661 / 25000) := by
  exact
    thetaTile4096 12814592 12822784 7 6 489 3579 24 _ _ (51144 / 3125) (1636611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12822784 :
    ThetaLowerSegment 12822784 12830976 (320485615661 / 25000) (320698383021 / 25000) := by
  exact
    thetaTile4096 12822784 12830976 7 6 520 3580 24 _ _ (51146 / 3125) (65467 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12830976 :
    ThetaLowerSegment 12830976 12839168 (320698383021 / 25000) (2567243441 / 200) := by
  exact
    thetaTile4096 12830976 12839168 7 6 506 3582 24 _ _ (51148 / 3125) (1636739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12839168 :
    ThetaLowerSegment 12839168 12847360 (2567243441 / 200) (12844384837 / 1000) := by
  exact
    thetaTile4096 12839168 12847360 7 6 499 3583 24 _ _ (2046 / 125) (1636803 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12847360 :
    ThetaLowerSegment 12847360 12855552 (12844384837 / 1000) (642633368189 / 50000) := by
  exact
    thetaTile4096 12847360 12855552 7 6 506 3584 24 _ _ (1636863 / 100000) (818433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12855552 :
    ThetaLowerSegment 12855552 12863744 (642633368189 / 50000) (321522118433 / 25000) := by
  exact
    thetaTile4096 12855552 12863744 7 6 502 3585 24 _ _ (1636927 / 100000) (163693 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12863744 :
    ThetaLowerSegment 12863744 12871936 (321522118433 / 25000) (321734927263 / 25000) := by
  exact
    thetaTile4096 12863744 12871936 7 6 520 3586 24 _ _ (1636991 / 100000) (818497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12871936 :
    ThetaLowerSegment 12871936 12880128 (321734927263 / 25000) (321929736689 / 25000) := by
  exact
    thetaTile4096 12871936 12880128 7 6 476 3587 24 _ _ (818527 / 50000) (1637057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12880128 :
    ThetaLowerSegment 12880128 12888320 (321929736689 / 25000) (644251563139 / 50000) := by
  exact
    thetaTile4096 12880128 12888320 7 6 479 3588 24 _ _ (818559 / 50000) (1637121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12888320 :
    ThetaLowerSegment 12888320 12896512 (644251563139 / 50000) (644669044549 / 50000) := by
  exact
    thetaTile4096 12888320 12896512 7 6 510 3590 24 _ _ (818591 / 50000) (327437 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12896512 :
    ThetaLowerSegment 12896512 12904704 (644669044549 / 50000) (1290135427413 / 100000) := by
  exact
    thetaTile4096 12896512 12904704 7 6 487 3591 24 _ _ (327449 / 20000) (51164 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12904704 :
    ThetaLowerSegment 12904704 12912896 (1290135427413 / 100000) (40341649903 / 3125) := by
  exact
    thetaTile4096 12904704 12912896 7 6 487 3592 24 _ _ (1637309 / 100000) (51166 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12912896 :
    ThetaLowerSegment 12912896 12921088 (40341649903 / 3125) (80734467681 / 6250) := by
  exact
    thetaTile4096 12912896 12921088 7 6 500 3593 24 _ _ (409343 / 25000) (13099 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12921088 :
    ThetaLowerSegment 12921088 12929280 (80734467681 / 6250) (12925521891 / 1000) := by
  exact
    thetaTile4096 12921088 12929280 7 6 489 3594 24 _ _ (409359 / 25000) (1637439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12929280 :
    ThetaLowerSegment 12929280 12937472 (12925521891 / 1000) (1293359476107 / 100000) := by
  exact
    thetaTile4096 12929280 12937472 7 6 493 3595 24 _ _ (1637499 / 100000) (818751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12937472 :
    ThetaLowerSegment 12937472 12945664 (1293359476107 / 100000) (1294166794173 / 100000) := by
  exact
    thetaTile4096 12937472 12945664 7 6 493 3596 24 _ _ (818781 / 50000) (327513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12945664 :
    ThetaLowerSegment 12945664 12953856 (1294166794173 / 100000) (1294992157677 / 100000) := by
  exact
    thetaTile4096 12945664 12953856 7 6 504 3598 24 _ _ (818813 / 50000) (1637629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12953856 :
    ThetaLowerSegment 12953856 12962048 (1294992157677 / 100000) (1295820828311 / 100000) := by
  exact
    thetaTile4096 12953856 12962048 7 6 506 3599 24 _ _ (1637689 / 100000) (409423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12962048 :
    ThetaLowerSegment 12962048 12970240 (1295820828311 / 100000) (259325320459 / 20000) := by
  exact
    thetaTile4096 12962048 12970240 7 6 492 3600 24 _ _ (204719 / 12500) (327551 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12970240 :
    ThetaLowerSegment 12970240 12978432 (259325320459 / 20000) (6487121091 / 500) := by
  exact
    thetaTile4096 12970240 12978432 7 6 487 3601 24 _ _ (327563 / 20000) (818909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12978432 :
    ThetaLowerSegment 12978432 12986624 (6487121091 / 500) (324555056727 / 25000) := by
  exact
    thetaTile4096 12978432 12986624 7 6 486 3602 24 _ _ (818939 / 50000) (1637881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12986624 :
    ThetaLowerSegment 12986624 12994816 (324555056727 / 25000) (162379490253 / 12500) := by
  exact
    thetaTile4096 12986624 12994816 7 6 498 3603 24 _ _ (818971 / 50000) (327589 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell12994816 :
    ThetaLowerSegment 12994816 13003008 (162379490253 / 12500) (1299889322629 / 100000) := by
  exact
    thetaTile4096 12994816 13003008 7 6 521 3604 24 _ _ (327601 / 20000) (204751 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13003008 :
    ThetaLowerSegment 13003008 13011200 (1299889322629 / 100000) (1300705080493 / 100000) := by
  exact
    thetaTile4096 13003008 13011200 7 6 498 3605 24 _ _ (409517 / 25000) (1638071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13011200 :
    ThetaLowerSegment 13011200 13019392 (1300705080493 / 100000) (65077599711 / 5000) := by
  exact
    thetaTile4096 13011200 13019392 7 6 517 3607 24 _ _ (1638131 / 100000) (819067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13019392 :
    ThetaLowerSegment 13019392 13027584 (65077599711 / 5000) (325587858223 / 25000) := by
  exact
    thetaTile4096 13019392 13027584 7 6 488 3608 24 _ _ (819097 / 50000) (1638197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13027584 :
    ThetaLowerSegment 13027584 13035776 (325587858223 / 25000) (325786087199 / 25000) := by
  exact
    thetaTile4096 13027584 13035776 7 6 484 3609 24 _ _ (102391 / 6250) (1638259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13035776 :
    ThetaLowerSegment 13035776 13043968 (325786087199 / 25000) (162995438537 / 12500) := by
  exact
    thetaTile4096 13035776 13043968 7 6 500 3610 24 _ _ (1638319 / 100000) (819161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13043968 :
    ThetaLowerSegment 13043968 13052160 (162995438537 / 12500) (652400360749 / 50000) := by
  exact
    thetaTile4096 13043968 13052160 7 6 511 3611 24 _ _ (819191 / 50000) (327677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13052160 :
    ThetaLowerSegment 13052160 13060352 (652400360749 / 50000) (40799496819 / 3125) := by
  exact
    thetaTile4096 13052160 13060352 7 6 478 3612 24 _ _ (327689 / 20000) (102403 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13060352 :
    ThetaLowerSegment 13060352 13068544 (40799496819 / 3125) (81647739251 / 6250) := by
  exact
    thetaTile4096 13060352 13068544 7 6 476 3613 24 _ _ (409627 / 25000) (1638511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13068544 :
    ThetaLowerSegment 13068544 13076736 (81647739251 / 6250) (40849677103 / 3125) := by
  exact
    thetaTile4096 13068544 13076736 7 6 504 3615 24 _ _ (163857 / 10000) (1638573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13076736 :
    ThetaLowerSegment 13076736 13084928 (40849677103 / 3125) (1307994236099 / 100000) := by
  exact
    thetaTile4096 13076736 13084928 7 6 491 3616 24 _ _ (1638633 / 100000) (409659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13084928 :
    ThetaLowerSegment 13084928 13093120 (1307994236099 / 100000) (10470259591 / 800) := by
  exact
    thetaTile4096 13084928 13093120 7 6 481 3617 24 _ _ (204837 / 12500) (1638699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13093120 :
    ThetaLowerSegment 13093120 13101312 (10470259591 / 800) (1309596911601 / 100000) := by
  exact
    thetaTile4096 13093120 13101312 7 6 497 3618 24 _ _ (819379 / 50000) (1638761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13101312 :
    ThetaLowerSegment 13101312 13109504 (1309596911601 / 100000) (40951278263 / 3125) := by
  exact
    thetaTile4096 13101312 13109504 7 6 515 3619 24 _ _ (1638821 / 100000) (204853 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13109504 :
    ThetaLowerSegment 13109504 13117696 (40951278263 / 3125) (655615423011 / 50000) := by
  exact
    thetaTile4096 13109504 13117696 7 6 482 3620 24 _ _ (1638883 / 100000) (819443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13117696 :
    ThetaLowerSegment 13117696 13125888 (655615423011 / 50000) (656030076349 / 50000) := by
  exact
    thetaTile4096 13117696 13125888 7 6 506 3621 24 _ _ (819473 / 50000) (1638949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13125888 :
    ThetaLowerSegment 13125888 13134080 (656030076349 / 50000) (131288621273 / 10000) := by
  exact
    thetaTile4096 13125888 13134080 7 6 504 3622 24 _ _ (51219 / 3125) (1639011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13134080 :
    ThetaLowerSegment 13134080 13142272 (131288621273 / 10000) (1313723778011 / 100000) := by
  exact
    thetaTile4096 13134080 13142272 7 6 511 3624 24 _ _ (1639071 / 100000) (819537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13142272 :
    ThetaLowerSegment 13142272 13150464 (1313723778011 / 100000) (1314517118383 / 100000) := by
  exact
    thetaTile4096 13142272 13150464 7 6 484 3625 24 _ _ (1639133 / 100000) (51223 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13150464 :
    ThetaLowerSegment 13150464 13158656 (1314517118383 / 100000) (1315349829443 / 100000) := by
  exact
    thetaTile4096 13150464 13158656 7 6 508 3626 24 _ _ (327839 / 20000) (819599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13158656 :
    ThetaLowerSegment 13158656 13166848 (1315349829443 / 100000) (1316139951799 / 100000) := by
  exact
    thetaTile4096 13158656 13166848 7 6 482 3627 24 _ _ (819629 / 50000) (1639261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13166848 :
    ThetaLowerSegment 13166848 13175040 (1316139951799 / 100000) (1316959611799 / 100000) := by
  exact
    thetaTile4096 13166848 13175040 7 6 500 3628 24 _ _ (40983 / 2500) (1639323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13175040 :
    ThetaLowerSegment 13175040 13183232 (1316959611799 / 100000) (1317797336001 / 100000) := by
  exact
    thetaTile4096 13175040 13183232 7 6 511 3629 24 _ _ (819691 / 50000) (327877 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13183232 :
    ThetaLowerSegment 13183232 13191424 (1317797336001 / 100000) (1318625255221 / 100000) := by
  exact
    thetaTile4096 13183232 13191424 7 6 505 3630 24 _ _ (409861 / 25000) (1639447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13191424 :
    ThetaLowerSegment 13191424 13199616 (1318625255221 / 100000) (1319461403281 / 100000) := by
  exact
    thetaTile4096 13191424 13199616 7 6 510 3632 24 _ _ (819753 / 50000) (1639509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13199616 :
    ThetaLowerSegment 13199616 13207808 (1319461403281 / 100000) (264057221197 / 20000) := by
  exact
    thetaTile4096 13199616 13207808 7 6 503 3633 24 _ _ (102473 / 6250) (1639571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13207808 :
    ThetaLowerSegment 13207808 13216000 (264057221197 / 20000) (264221512123 / 20000) := by
  exact
    thetaTile4096 13207808 13216000 7 6 501 3634 24 _ _ (163963 / 10000) (1639633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13216000 :
    ThetaLowerSegment 13216000 13224192 (264221512123 / 20000) (1321937244767 / 100000) := by
  exact
    thetaTile4096 13216000 13224192 7 6 506 3635 24 _ _ (409923 / 25000) (327939 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13224192 :
    ThetaLowerSegment 13224192 13232384 (1321937244767 / 100000) (1322750562751 / 100000) := by
  exact
    thetaTile4096 13224192 13232384 7 6 496 3636 24 _ _ (819877 / 50000) (1639757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13232384 :
    ThetaLowerSegment 13232384 13240576 (1322750562751 / 100000) (264712126371 / 20000) := by
  exact
    thetaTile4096 13232384 13240576 7 6 494 3637 24 _ _ (204977 / 12500) (1639819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13240576 :
    ThetaLowerSegment 13240576 13248768 (264712126371 / 20000) (1324378930977 / 100000) := by
  exact
    thetaTile4096 13240576 13248768 7 6 499 3638 24 _ _ (819939 / 50000) (1639881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13248768 :
    ThetaLowerSegment 13248768 13256960 (1324378930977 / 100000) (1325174301877 / 100000) := by
  exact
    thetaTile4096 13248768 13256960 7 6 485 3639 24 _ _ (81997 / 5000) (1639943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13256960 :
    ThetaLowerSegment 13256960 13265152 (1325174301877 / 100000) (1325982822863 / 100000) := by
  exact
    thetaTile4096 13256960 13265152 7 6 493 3641 24 _ _ (820001 / 50000) (328001 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13265152 :
    ThetaLowerSegment 13265152 13273344 (1325982822863 / 100000) (1326796294607 / 100000) := by
  exact
    thetaTile4096 13265152 13273344 7 6 496 3642 24 _ _ (51252 / 3125) (1640067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13273344 :
    ThetaLowerSegment 13273344 13281536 (1326796294607 / 100000) (1327649159607 / 100000) := by
  exact
    thetaTile4096 13273344 13281536 7 6 520 3643 24 _ _ (13121 / 800) (51254 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13281536 :
    ThetaLowerSegment 13281536 13289728 (1327649159607 / 100000) (265691882397 / 20000) := by
  exact
    thetaTile4096 13281536 13289728 7 6 494 3644 24 _ _ (1640187 / 100000) (164019 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13289728 :
    ThetaLowerSegment 13289728 13297920 (265691882397 / 20000) (332312913063 / 25000) := by
  exact
    thetaTile4096 13289728 13297920 7 6 483 3645 24 _ _ (1640249 / 100000) (410063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13297920 :
    ThetaLowerSegment 13297920 13306112 (332312913063 / 25000) (665041644711 / 50000) := by
  exact
    thetaTile4096 13297920 13306112 7 6 507 3646 24 _ _ (164031 / 10000) (1640313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13306112 :
    ThetaLowerSegment 13306112 13314304 (665041644711 / 50000) (665460759757 / 50000) := by
  exact
    thetaTile4096 13306112 13314304 7 6 511 3647 24 _ _ (410093 / 25000) (13123 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13314304 :
    ThetaLowerSegment 13314304 13322496 (665460759757 / 50000) (1331759780777 / 100000) := by
  exact
    thetaTile4096 13314304 13322496 7 6 511 3648 24 _ _ (1640433 / 100000) (410109 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13322496 :
    ThetaLowerSegment 13322496 13330688 (1331759780777 / 100000) (1332540656397 / 100000) := by
  exact
    thetaTile4096 13322496 13330688 7 6 476 3649 24 _ _ (328099 / 20000) (820249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13330688 :
    ThetaLowerSegment 13330688 13338880 (1332540656397 / 100000) (1333383902181 / 100000) := by
  exact
    thetaTile4096 13330688 13338880 7 6 514 3651 24 _ _ (410139 / 25000) (1640559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13338880 :
    ThetaLowerSegment 13338880 13347072 (1333383902181 / 100000) (1334182883147 / 100000) := by
  exact
    thetaTile4096 13338880 13347072 7 6 487 3652 24 _ _ (820309 / 50000) (1640621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13347072 :
    ThetaLowerSegment 13347072 13355264 (1334182883147 / 100000) (133499830061 / 10000) := by
  exact
    thetaTile4096 13347072 13355264 7 6 497 3653 24 _ _ (1640679 / 100000) (820341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13355264 :
    ThetaLowerSegment 13355264 13363456 (133499830061 / 10000) (133585148593 / 10000) := by
  exact
    thetaTile4096 13355264 13363456 7 6 520 3654 24 _ _ (1640741 / 100000) (205093 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13363456 :
    ThetaLowerSegment 13363456 13371648 (133585148593 / 10000) (334165100329 / 25000) := by
  exact
    thetaTile4096 13363456 13371648 7 6 493 3655 24 _ _ (820401 / 50000) (328161 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13371648 :
    ThetaLowerSegment 13371648 13379840 (334165100329 / 25000) (668748620723 / 50000) := by
  exact
    thetaTile4096 13371648 13379840 7 6 510 3656 24 _ _ (1640863 / 100000) (820433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13379840 :
    ThetaLowerSegment 13379840 13388032 (668748620723 / 50000) (669153928951 / 50000) := by
  exact
    thetaTile4096 13379840 13388032 7 6 494 3657 24 _ _ (410231 / 25000) (1640927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13388032 :
    ThetaLowerSegment 13388032 13396224 (669153928951 / 50000) (167392069479 / 12500) := by
  exact
    thetaTile4096 13388032 13396224 7 6 505 3658 24 _ _ (820493 / 50000) (1640989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13396224 :
    ThetaLowerSegment 13396224 13404416 (167392069479 / 12500) (26798944661 / 2000) := by
  exact
    thetaTile4096 13396224 13404416 7 6 494 3660 24 _ _ (1641047 / 100000) (32821 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13404416 :
    ThetaLowerSegment 13404416 13412608 (26798944661 / 2000) (670373226323 / 50000) := by
  exact
    thetaTile4096 13404416 13412608 7 6 487 3661 24 _ _ (410277 / 25000) (1641111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13412608 :
    ThetaLowerSegment 13412608 13420800 (670373226323 / 50000) (83846914091 / 6250) := by
  exact
    thetaTile4096 13412608 13420800 7 6 490 3662 24 _ _ (1641169 / 100000) (410293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13420800 :
    ThetaLowerSegment 13420800 13428992 (83846914091 / 6250) (671184799613 / 50000) := by
  exact
    thetaTile4096 13420800 13428992 7 6 499 3663 24 _ _ (164123 / 10000) (1641233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13428992 :
    ThetaLowerSegment 13428992 13437184 (671184799613 / 50000) (167900011559 / 12500) := by
  exact
    thetaTile4096 13428992 13437184 7 6 506 3664 24 _ _ (1641291 / 100000) (820647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13437184 :
    ThetaLowerSegment 13437184 13445376 (167900011559 / 12500) (1680003392 / 125) := by
  exact
    thetaTile4096 13437184 13445376 7 6 489 3665 24 _ _ (205169 / 12500) (328271 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13445376 :
    ThetaLowerSegment 13445376 13453568 (1680003392 / 125) (1344792233253 / 100000) := by
  exact
    thetaTile4096 13445376 13453568 7 6 481 3666 24 _ _ (1641413 / 100000) (205177 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13453568 :
    ThetaLowerSegment 13453568 13461760 (1344792233253 / 100000) (1345629384993 / 100000) := by
  exact
    thetaTile4096 13453568 13461760 7 6 510 3667 24 _ _ (820737 / 50000) (1641477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13461760 :
    ThetaLowerSegment 13461760 13469952 (1345629384993 / 100000) (1346414038723 / 100000) := by
  exact
    thetaTile4096 13461760 13469952 7 6 478 3669 24 _ _ (328307 / 20000) (820769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13469952 :
    ThetaLowerSegment 13469952 13478144 (1346414038723 / 100000) (1347256177471 / 100000) := by
  exact
    thetaTile4096 13469952 13478144 7 6 513 3670 24 _ _ (410399 / 25000) (1641599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13478144 :
    ThetaLowerSegment 13478144 13486336 (1347256177471 / 100000) (1348070438847 / 100000) := by
  exact
    thetaTile4096 13478144 13486336 7 6 496 3671 24 _ _ (205207 / 12500) (1641659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13486336 :
    ThetaLowerSegment 13486336 13494528 (1348070438847 / 100000) (337221593049 / 25000) := by
  exact
    thetaTile4096 13486336 13494528 7 6 497 3672 24 _ _ (1641717 / 100000) (41043 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13494528 :
    ThetaLowerSegment 13494528 13502720 (337221593049 / 25000) (674844600819 / 50000) := by
  exact
    thetaTile4096 13494528 13502720 7 6 489 3673 24 _ _ (820889 / 50000) (1641781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13502720 :
    ThetaLowerSegment 13502720 13510912 (674844600819 / 50000) (675241925857 / 50000) := by
  exact
    thetaTile4096 13502720 13510912 7 6 484 3674 24 _ _ (1641839 / 100000) (820921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13510912 :
    ThetaLowerSegment 13510912 13519104 (675241925857 / 50000) (42228582894 / 3125) := by
  exact
    thetaTile4096 13510912 13519104 7 6 506 3675 24 _ _ (1641899 / 100000) (820951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13519104 :
    ThetaLowerSegment 13519104 13527296 (42228582894 / 3125) (169015517361 / 12500) := by
  exact
    thetaTile4096 13519104 13527296 7 6 493 3676 24 _ _ (41049 / 2500) (1641963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13527296 :
    ThetaLowerSegment 13527296 13535488 (169015517361 / 12500) (1352936939283 / 100000) := by
  exact
    thetaTile4096 13527296 13535488 7 6 495 3677 24 _ _ (1642021 / 100000) (205253 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13535488 :
    ThetaLowerSegment 13535488 13543680 (1352936939283 / 100000) (270748968627 / 20000) := by
  exact
    thetaTile4096 13535488 13543680 7 6 492 3679 24 _ _ (1642081 / 100000) (410521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13543680 :
    ThetaLowerSegment 13543680 13551872 (270748968627 / 20000) (1354580693413 / 100000) := by
  exact
    thetaTile4096 13543680 13551872 7 6 509 3680 24 _ _ (821071 / 50000) (328429 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13551872 :
    ThetaLowerSegment 13551872 13560064 (1354580693413 / 100000) (1355382087989 / 100000) := by
  exact
    thetaTile4096 13551872 13560064 7 6 488 3681 24 _ _ (821101 / 50000) (328441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13560064 :
    ThetaLowerSegment 13560064 13568256 (1355382087989 / 100000) (271238344631 / 20000) := by
  exact
    thetaTile4096 13560064 13568256 7 6 493 3682 24 _ _ (821131 / 50000) (328453 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13568256 :
    ThetaLowerSegment 13568256 13576448 (271238344631 / 20000) (339256095229 / 25000) := by
  exact
    thetaTile4096 13568256 13576448 7 6 507 3683 24 _ _ (1642323 / 100000) (821163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13576448 :
    ThetaLowerSegment 13576448 13584640 (339256095229 / 25000) (1357847214799 / 100000) := by
  exact
    thetaTile4096 13576448 13584640 7 6 501 3684 24 _ _ (1642383 / 100000) (821193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13584640 :
    ThetaLowerSegment 13584640 13592832 (1357847214799 / 100000) (1358681576351 / 100000) := by
  exact
    thetaTile4096 13584640 13592832 7 6 508 3685 24 _ _ (410611 / 25000) (1642447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13592832 :
    ThetaLowerSegment 13592832 13601024 (1358681576351 / 100000) (1359478190791 / 100000) := by
  exact
    thetaTile4096 13592832 13601024 7 6 485 3686 24 _ _ (205313 / 12500) (1642507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13601024 :
    ThetaLowerSegment 13601024 13609216 (1359478190791 / 100000) (1360348749711 / 100000) := by
  exact
    thetaTile4096 13601024 13609216 7 6 530 3687 24 _ _ (410641 / 25000) (1642567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13609216 :
    ThetaLowerSegment 13609216 13617408 (1360348749711 / 100000) (1361178274831 / 100000) := by
  exact
    thetaTile4096 13609216 13617408 7 6 505 3689 24 _ _ (51332 / 3125) (1642627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13617408 :
    ThetaLowerSegment 13617408 13625600 (1361178274831 / 100000) (1361973333887 / 100000) := by
  exact
    thetaTile4096 13617408 13625600 7 6 484 3690 24 _ _ (410671 / 25000) (1642687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13625600 :
    ThetaLowerSegment 13625600 13633792 (1361973333887 / 100000) (340702372773 / 25000) := by
  exact
    thetaTile4096 13625600 13633792 7 6 509 3691 24 _ _ (328549 / 20000) (410687 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13633792 :
    ThetaLowerSegment 13633792 13641984 (340702372773 / 25000) (170453861699 / 12500) := by
  exact
    thetaTile4096 13633792 13641984 7 6 500 3692 24 _ _ (328561 / 20000) (205351 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13641984 :
    ThetaLowerSegment 13641984 13650176 (170453861699 / 12500) (1364430968847 / 100000) := by
  exact
    thetaTile4096 13641984 13650176 7 6 487 3693 24 _ _ (328573 / 20000) (410717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13650176 :
    ThetaLowerSegment 13650176 13658368 (1364430968847 / 100000) (1365268860597 / 100000) := by
  exact
    thetaTile4096 13650176 13658368 7 6 510 3694 24 _ _ (65717 / 4000) (102683 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13658368 :
    ThetaLowerSegment 13658368 13666560 (1365268860597 / 100000) (1366103496977 / 100000) := by
  exact
    thetaTile4096 13658368 13666560 7 6 508 3695 24 _ _ (328597 / 20000) (410747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13666560 :
    ThetaLowerSegment 13666560 13674752 (1366103496977 / 100000) (683479761711 / 50000) := by
  exact
    thetaTile4096 13666560 13674752 7 6 521 3696 24 _ _ (328609 / 20000) (205381 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13674752 :
    ThetaLowerSegment 13674752 13682944 (683479761711 / 50000) (85486111857 / 6250) := by
  exact
    thetaTile4096 13674752 13682944 7 6 498 3697 24 _ _ (328621 / 20000) (410777 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13682944 :
    ThetaLowerSegment 13682944 13691136 (85486111857 / 6250) (1368604301707 / 100000) := by
  exact
    thetaTile4096 13682944 13691136 7 6 503 3699 24 _ _ (328633 / 20000) (51349 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13691136 :
    ThetaLowerSegment 13691136 13699328 (1368604301707 / 100000) (1369394692451 / 100000) := by
  exact
    thetaTile4096 13691136 13699328 7 6 481 3700 24 _ _ (205403 / 12500) (1643227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13699328 :
    ThetaLowerSegment 13699328 13707520 (1369394692451 / 100000) (1370229480723 / 100000) := by
  exact
    thetaTile4096 13699328 13707520 7 6 508 3701 24 _ _ (410821 / 25000) (1643287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13707520 :
    ThetaLowerSegment 13707520 13715712 (1370229480723 / 100000) (274206286519 / 20000) := by
  exact
    thetaTile4096 13707520 13715712 7 6 488 3702 24 _ _ (102709 / 6250) (1643347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13715712 :
    ThetaLowerSegment 13715712 13723904 (274206286519 / 20000) (1371858064807 / 100000) := by
  exact
    thetaTile4096 13715712 13723904 7 6 503 3703 24 _ _ (410851 / 25000) (1643407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13723904 :
    ThetaLowerSegment 13723904 13732096 (1371858064807 / 100000) (343172825137 / 25000) := by
  exact
    thetaTile4096 13723904 13732096 7 6 507 3704 24 _ _ (1643463 / 100000) (821733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13732096 :
    ThetaLowerSegment 13732096 13740288 (343172825137 / 25000) (27469406609 / 2000) := by
  exact
    thetaTile4096 13732096 13740288 7 6 474 3705 24 _ _ (1643523 / 100000) (821763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13740288 :
    ThetaLowerSegment 13740288 13748480 (27469406609 / 2000) (343573852279 / 25000) := by
  exact
    thetaTile4096 13740288 13748480 7 6 502 3706 24 _ _ (1643583 / 100000) (821793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13748480 :
    ThetaLowerSegment 13748480 13756672 (343573852279 / 25000) (68758491333 / 5000) := by
  exact
    thetaTile4096 13748480 13756672 7 6 532 3707 24 _ _ (821821 / 50000) (328729 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13756672 :
    ThetaLowerSegment 13756672 13764864 (68758491333 / 5000) (85995986987 / 6250) := by
  exact
    thetaTile4096 13756672 13764864 7 6 466 3708 24 _ _ (821851 / 50000) (328741 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13764864 :
    ThetaLowerSegment 13764864 13773056 (85995986987 / 6250) (688367329819 / 50000) := by
  exact
    thetaTile4096 13764864 13773056 7 6 486 3710 24 _ _ (1643761 / 100000) (410941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13773056 :
    ThetaLowerSegment 13773056 13781248 (688367329819 / 50000) (172195804133 / 12500) := by
  exact
    thetaTile4096 13773056 13781248 7 6 506 3711 24 _ _ (1643821 / 100000) (102739 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13781248 :
    ThetaLowerSegment 13781248 13789440 (172195804133 / 12500) (86153074789 / 6250) := by
  exact
    thetaTile4096 13781248 13789440 7 6 537 3712 24 _ _ (41097 / 2500) (1643883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13789440 :
    ThetaLowerSegment 13789440 13797632 (86153074789 / 6250) (344819024611 / 25000) := by
  exact
    thetaTile4096 13789440 13797632 7 6 503 3713 24 _ _ (82197 / 5000) (1643943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13797632 :
    ThetaLowerSegment 13797632 13805824 (344819024611 / 25000) (690034252981 / 50000) := by
  exact
    thetaTile4096 13797632 13805824 7 6 482 3714 24 _ _ (1643999 / 100000) (822001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13805824 :
    ThetaLowerSegment 13805824 13814016 (690034252981 / 50000) (138087738299 / 10000) := by
  exact
    thetaTile4096 13805824 13814016 7 6 492 3715 24 _ _ (1644059 / 100000) (822031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13814016 :
    ThetaLowerSegment 13814016 13822208 (138087738299 / 10000) (138169944199 / 10000) := by
  exact
    thetaTile4096 13814016 13822208 7 6 500 3716 24 _ _ (822059 / 50000) (1644121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13822208 :
    ThetaLowerSegment 13822208 13830400 (138169944199 / 10000) (691257476891 / 50000) := by
  exact
    thetaTile4096 13822208 13830400 7 6 496 3717 24 _ _ (1644177 / 100000) (82209 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13830400 :
    ThetaLowerSegment 13830400 13838592 (691257476891 / 50000) (138330911977 / 10000) := by
  exact
    thetaTile4096 13830400 13838592 7 6 483 3718 24 _ _ (411059 / 25000) (1644239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13838592 :
    ThetaLowerSegment 13838592 13846784 (138330911977 / 10000) (692087009733 / 50000) := by
  exact
    thetaTile4096 13838592 13846784 7 6 526 3720 24 _ _ (205537 / 12500) (1644299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13846784 :
    ThetaLowerSegment 13846784 13854976 (692087009733 / 50000) (1385010996161 / 100000) := by
  exact
    thetaTile4096 13846784 13854976 7 6 509 3721 24 _ _ (328871 / 20000) (822179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13854976 :
    ThetaLowerSegment 13854976 13863168 (1385010996161 / 100000) (1385836491989 / 100000) := by
  exact
    thetaTile4096 13854976 13863168 7 6 502 3722 24 _ _ (822207 / 50000) (1644417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13863168 :
    ThetaLowerSegment 13863168 13871360 (1385836491989 / 100000) (693317030697 / 50000) := by
  exact
    thetaTile4096 13863168 13871360 7 6 485 3723 24 _ _ (1644473 / 100000) (411119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13871360 :
    ThetaLowerSegment 13871360 13879552 (693317030697 / 50000) (693735564091 / 50000) := by
  exact
    thetaTile4096 13871360 13879552 7 6 509 3724 24 _ _ (411133 / 25000) (328907 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13879552 :
    ThetaLowerSegment 13879552 13887744 (693735564091 / 50000) (1388311514183 / 100000) := by
  exact
    thetaTile4096 13879552 13887744 7 6 511 3725 24 _ _ (1644591 / 100000) (822297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13887744 :
    ThetaLowerSegment 13887744 13895936 (1388311514183 / 100000) (1389120681983 / 100000) := by
  exact
    thetaTile4096 13887744 13895936 7 6 492 3726 24 _ _ (32893 / 2000) (1644653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13895936 :
    ThetaLowerSegment 13895936 13904128 (1389120681983 / 100000) (1389985798917 / 100000) := by
  exact
    thetaTile4096 13895936 13904128 7 6 526 3727 24 _ _ (1644709 / 100000) (205589 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13904128 :
    ThetaLowerSegment 13904128 13912320 (1389985798917 / 100000) (1390808182917 / 100000) := by
  exact
    thetaTile4096 13904128 13912320 7 6 500 3728 24 _ _ (51399 / 3125) (1644771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13912320 :
    ThetaLowerSegment 13912320 13920512 (1390808182917 / 100000) (1391643755033 / 100000) := by
  exact
    thetaTile4096 13912320 13920512 7 6 508 3729 24 _ _ (1644827 / 100000) (164483 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell13920512 :
    ThetaLowerSegment 13920512 13922560 (1391643755033 / 100000) (1391841141353 / 100000) := by
  exact
    thetaTile4096 13920512 13922560 7 4 120 3731 24 _ _ (822443 / 50000) (1644889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_8096000_13922560 :
    ThetaLowerSegment 8096000 13922560 (404582206079 / 50000) (1391841141353 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8096000 cell8104192)
                      (ThetaLowerSegment.join cell8112384 cell8120576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8128768 cell8136960)
                      (ThetaLowerSegment.join cell8145152 cell8153344)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8161536 cell8169728)
                      (ThetaLowerSegment.join cell8177920 cell8186112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8194304 cell8202496)
                      (ThetaLowerSegment.join cell8210688 cell8218880))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8227072 cell8235264)
                      (ThetaLowerSegment.join cell8243456 cell8251648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8259840 cell8268032)
                      (ThetaLowerSegment.join cell8276224 cell8284416)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8292608 cell8300800)
                      (ThetaLowerSegment.join cell8308992 cell8317184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8325376 cell8333568)
                      (ThetaLowerSegment.join cell8341760 cell8349952)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8358144 cell8366336)
                      (ThetaLowerSegment.join cell8374528 cell8382720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8390912 cell8399104)
                      (ThetaLowerSegment.join cell8407296 cell8415488)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8423680 cell8431872)
                      (ThetaLowerSegment.join cell8440064 cell8448256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8456448 cell8464640)
                      (ThetaLowerSegment.join cell8472832 cell8481024))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8489216 cell8497408)
                      (ThetaLowerSegment.join cell8505600 cell8513792))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8521984 cell8530176)
                      (ThetaLowerSegment.join cell8538368 cell8546560)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8554752 cell8562944)
                      (ThetaLowerSegment.join cell8571136 cell8579328))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8587520 cell8595712)
                      (ThetaLowerSegment.join cell8603904 cell8612096))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8620288 cell8628480)
                      (ThetaLowerSegment.join cell8636672 cell8644864))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8653056 cell8661248)
                      (ThetaLowerSegment.join cell8669440 cell8677632)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8685824 cell8694016)
                      (ThetaLowerSegment.join cell8702208 cell8710400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8718592 cell8726784)
                      (ThetaLowerSegment.join cell8734976 cell8743168))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8751360 cell8759552)
                      (ThetaLowerSegment.join cell8767744 cell8775936))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8784128 cell8792320)
                      (ThetaLowerSegment.join cell8800512 cell8808704)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8816896 cell8825088)
                      (ThetaLowerSegment.join cell8833280 cell8841472))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8849664 cell8857856)
                      (ThetaLowerSegment.join cell8866048 cell8874240)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8882432 cell8890624)
                      (ThetaLowerSegment.join cell8898816 cell8907008))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8915200 cell8923392)
                      (ThetaLowerSegment.join cell8931584 cell8939776)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8947968 cell8956160)
                      (ThetaLowerSegment.join cell8964352 cell8972544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell8980736 cell8988928)
                      (ThetaLowerSegment.join cell8997120 cell9005312))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9013504 cell9021696)
                      (ThetaLowerSegment.join cell9029888 cell9038080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9046272 cell9054464)
                      (ThetaLowerSegment.join cell9062656 cell9070848)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9079040 cell9087232)
                      (ThetaLowerSegment.join cell9095424 cell9103616))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9111808 cell9120000)
                      (ThetaLowerSegment.join cell9128192 cell9136384)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9144576 cell9152768)
                      (ThetaLowerSegment.join cell9160960 cell9169152))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9177344 cell9185536)
                      (ThetaLowerSegment.join cell9193728 cell9201920)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9210112 cell9218304)
                      (ThetaLowerSegment.join cell9226496 cell9234688))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9242880 cell9251072)
                      (ThetaLowerSegment.join cell9259264 cell9267456))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9275648 cell9283840)
                      (ThetaLowerSegment.join cell9292032 cell9300224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9308416 cell9316608)
                      (ThetaLowerSegment.join cell9324800 cell9332992)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9341184 cell9349376)
                      (ThetaLowerSegment.join cell9357568 cell9365760))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9373952 cell9382144)
                      (ThetaLowerSegment.join cell9390336 cell9398528)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9406720 cell9414912)
                      (ThetaLowerSegment.join cell9423104 cell9431296))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9439488 cell9447680)
                      (ThetaLowerSegment.join cell9455872 cell9464064)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9472256 cell9480448)
                      (ThetaLowerSegment.join cell9488640 cell9496832))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9505024 cell9513216)
                      (ThetaLowerSegment.join cell9521408 cell9529600))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9537792 cell9545984)
                      (ThetaLowerSegment.join cell9554176 cell9562368))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9570560 cell9578752)
                      (ThetaLowerSegment.join cell9586944 cell9595136)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9603328 cell9611520)
                      (ThetaLowerSegment.join cell9619712 cell9627904))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9636096 cell9644288)
                      (ThetaLowerSegment.join cell9652480 cell9660672))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9668864 cell9677056)
                      (ThetaLowerSegment.join cell9685248 cell9693440))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9701632 cell9709824)
                      (ThetaLowerSegment.join cell9718016 cell9726208)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9734400 cell9742592)
                      (ThetaLowerSegment.join cell9750784 cell9758976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9767168 cell9775360)
                      (ThetaLowerSegment.join cell9783552 cell9791744))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9799936 cell9808128)
                      (ThetaLowerSegment.join cell9816320 cell9824512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9832704 cell9840896)
                      (ThetaLowerSegment.join cell9849088 cell9857280)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9865472 cell9873664)
                      (ThetaLowerSegment.join cell9881856 cell9890048))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9898240 cell9906432)
                      (ThetaLowerSegment.join cell9914624 cell9922816)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9931008 cell9939200)
                      (ThetaLowerSegment.join cell9947392 cell9955584))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9963776 cell9971968)
                      (ThetaLowerSegment.join cell9980160 cell9988352)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell9996544 cell10004736)
                      (ThetaLowerSegment.join cell10012928 cell10021120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10029312 cell10037504)
                      (ThetaLowerSegment.join cell10045696 cell10053888))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10062080 cell10070272)
                      (ThetaLowerSegment.join cell10078464 cell10086656))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10094848 cell10103040)
                      (ThetaLowerSegment.join cell10111232 cell10119424)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10127616 cell10135808)
                      (ThetaLowerSegment.join cell10144000 cell10152192))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10160384 cell10168576)
                      (ThetaLowerSegment.join cell10176768 cell10184960))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10193152 cell10201344)
                      (ThetaLowerSegment.join cell10209536 cell10217728))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10225920 cell10234112)
                      (ThetaLowerSegment.join cell10242304 cell10250496)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10258688 cell10266880)
                      (ThetaLowerSegment.join cell10275072 cell10283264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10291456 cell10299648)
                      (ThetaLowerSegment.join cell10307840 cell10316032))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10324224 cell10332416)
                      (ThetaLowerSegment.join cell10340608 cell10348800))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10356992 cell10365184)
                      (ThetaLowerSegment.join cell10373376 cell10381568)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10389760 cell10397952)
                      (ThetaLowerSegment.join cell10406144 cell10414336))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10422528 cell10430720)
                      (ThetaLowerSegment.join cell10438912 cell10447104)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10455296 cell10463488)
                      (ThetaLowerSegment.join cell10471680 cell10479872))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10488064 cell10496256)
                      (ThetaLowerSegment.join cell10504448 cell10512640)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10520832 cell10529024)
                      (ThetaLowerSegment.join cell10537216 cell10545408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10553600 cell10561792)
                      (ThetaLowerSegment.join cell10569984 cell10578176))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10586368 cell10594560)
                      (ThetaLowerSegment.join cell10602752 cell10610944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10619136 cell10627328)
                      (ThetaLowerSegment.join cell10635520 cell10643712)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10651904 cell10660096)
                      (ThetaLowerSegment.join cell10668288 cell10676480))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10684672 cell10692864)
                      (ThetaLowerSegment.join cell10701056 cell10709248))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10717440 cell10725632)
                      (ThetaLowerSegment.join cell10733824 cell10742016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10750208 cell10758400)
                      (ThetaLowerSegment.join cell10766592 cell10774784)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10782976 cell10791168)
                      (ThetaLowerSegment.join cell10799360 cell10807552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10815744 cell10823936)
                      (ThetaLowerSegment.join cell10832128 cell10840320))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10848512 cell10856704)
                      (ThetaLowerSegment.join cell10864896 cell10873088))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10881280 cell10889472)
                      (ThetaLowerSegment.join cell10897664 cell10905856)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10914048 cell10922240)
                      (ThetaLowerSegment.join cell10930432 cell10938624))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10946816 cell10955008)
                      (ThetaLowerSegment.join cell10963200 cell10971392)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell10979584 cell10987776)
                      (ThetaLowerSegment.join cell10995968 cell11004160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11012352 cell11020544)
                      (ThetaLowerSegment.join cell11028736 cell11036928)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11045120 cell11053312)
                      (ThetaLowerSegment.join cell11061504 cell11069696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11077888 cell11086080)
                      (ThetaLowerSegment.join cell11094272 cell11102464))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11110656 cell11118848)
                      (ThetaLowerSegment.join cell11127040 cell11135232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11143424 cell11151616)
                      (ThetaLowerSegment.join cell11159808 cell11168000)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11176192 cell11184384)
                      (ThetaLowerSegment.join cell11192576 cell11200768))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11208960 cell11217152)
                      (ThetaLowerSegment.join cell11225344 cell11233536)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11241728 cell11249920)
                      (ThetaLowerSegment.join cell11258112 cell11266304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11274496 cell11282688)
                      (ThetaLowerSegment.join cell11290880 cell11299072)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11307264 cell11315456)
                      (ThetaLowerSegment.join cell11323648 cell11331840))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11340032 cell11348224)
                      (ThetaLowerSegment.join cell11356416 cell11364608))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11372800 cell11380992)
                      (ThetaLowerSegment.join cell11389184 cell11397376))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11405568 cell11413760)
                      (ThetaLowerSegment.join cell11421952 cell11430144)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11438336 cell11446528)
                      (ThetaLowerSegment.join cell11454720 cell11462912))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11471104 cell11479296)
                      (ThetaLowerSegment.join cell11487488 cell11495680)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11503872 cell11512064)
                      (ThetaLowerSegment.join cell11520256 cell11528448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11536640 cell11544832)
                      (ThetaLowerSegment.join cell11553024 cell11561216)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11569408 cell11577600)
                      (ThetaLowerSegment.join cell11585792 cell11593984))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11602176 cell11610368)
                      (ThetaLowerSegment.join cell11618560 cell11626752))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11634944 cell11643136)
                      (ThetaLowerSegment.join cell11651328 cell11659520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11667712 cell11675904)
                      (ThetaLowerSegment.join cell11684096 cell11692288)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11700480 cell11708672)
                      (ThetaLowerSegment.join cell11716864 cell11725056))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11733248 cell11741440)
                      (ThetaLowerSegment.join cell11749632 cell11757824))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11766016 cell11774208)
                      (ThetaLowerSegment.join cell11782400 cell11790592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11798784 cell11806976)
                      (ThetaLowerSegment.join cell11815168 cell11823360)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11831552 cell11839744)
                      (ThetaLowerSegment.join cell11847936 cell11856128))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11864320 cell11872512)
                      (ThetaLowerSegment.join cell11880704 cell11888896))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11897088 cell11905280)
                      (ThetaLowerSegment.join cell11913472 cell11921664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11929856 cell11938048)
                      (ThetaLowerSegment.join cell11946240 cell11954432)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11962624 cell11970816)
                      (ThetaLowerSegment.join cell11979008 cell11987200))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell11995392 cell12003584)
                      (ThetaLowerSegment.join cell12011776 cell12019968)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell12028160 cell12036352)
                      (ThetaLowerSegment.join cell12044544 cell12052736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell12060928 cell12069120)
                      (ThetaLowerSegment.join cell12077312 cell12085504)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell12093696 cell12101888)
                      (ThetaLowerSegment.join cell12110080 cell12118272))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell12126464 cell12134656)
                      (ThetaLowerSegment.join cell12142848 cell12151040))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell12159232 cell12167424)
                      (ThetaLowerSegment.join cell12175616 cell12183808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell12192000 cell12200192)
                      (ThetaLowerSegment.join cell12208384 cell12216576)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell12224768 cell12232960)
                      (ThetaLowerSegment.join cell12241152 cell12249344))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell12257536 cell12265728)
                      (ThetaLowerSegment.join cell12273920 cell12282112)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12290304 cell12298496)
                    (ThetaLowerSegment.join cell12306688 cell12314880))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12323072 cell12331264)
                    (ThetaLowerSegment.join cell12339456 cell12347648)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12355840 cell12364032)
                    (ThetaLowerSegment.join cell12372224 cell12380416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12388608 cell12396800)
                    (ThetaLowerSegment.join cell12404992 cell12413184))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12421376 cell12429568)
                    (ThetaLowerSegment.join cell12437760 cell12445952))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12454144 cell12462336)
                    (ThetaLowerSegment.join cell12470528 cell12478720)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12486912 cell12495104)
                    (ThetaLowerSegment.join cell12503296 cell12511488))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12519680 cell12527872)
                    (ThetaLowerSegment.join cell12536064 cell12544256)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12552448 cell12560640)
                    (ThetaLowerSegment.join cell12568832 cell12577024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12585216 cell12593408)
                    (ThetaLowerSegment.join cell12601600 cell12609792)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12617984 cell12626176)
                    (ThetaLowerSegment.join cell12634368 cell12642560))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12650752 cell12658944)
                    (ThetaLowerSegment.join cell12667136 cell12675328))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12683520 cell12691712)
                    (ThetaLowerSegment.join cell12699904 cell12708096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12716288 cell12724480)
                    (ThetaLowerSegment.join cell12732672 cell12740864)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12749056 cell12757248)
                    (ThetaLowerSegment.join cell12765440 cell12773632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12781824 cell12790016)
                    (ThetaLowerSegment.join cell12798208 cell12806400))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12814592 cell12822784)
                    (ThetaLowerSegment.join cell12830976 cell12839168))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12847360 cell12855552)
                    (ThetaLowerSegment.join cell12863744 cell12871936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12880128 cell12888320)
                    (ThetaLowerSegment.join cell12896512 cell12904704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12912896 cell12921088)
                    (ThetaLowerSegment.join cell12929280 cell12937472))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12945664 cell12953856)
                    (ThetaLowerSegment.join cell12962048 cell12970240))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell12978432 cell12986624)
                    (ThetaLowerSegment.join cell12994816 cell13003008)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13011200 cell13019392)
                    (ThetaLowerSegment.join cell13027584 cell13035776))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13043968 cell13052160)
                    (ThetaLowerSegment.join cell13060352 cell13068544)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13076736 cell13084928)
                    (ThetaLowerSegment.join cell13093120 cell13101312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13109504 cell13117696)
                    (ThetaLowerSegment.join cell13125888 cell13134080)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13142272 cell13150464)
                    (ThetaLowerSegment.join cell13158656 cell13166848))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13175040 cell13183232)
                    (ThetaLowerSegment.join cell13191424 cell13199616))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13207808 cell13216000)
                    (ThetaLowerSegment.join cell13224192 cell13232384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13240576 cell13248768)
                    (ThetaLowerSegment.join cell13256960 cell13265152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13273344 cell13281536)
                    (ThetaLowerSegment.join cell13289728 cell13297920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13306112 cell13314304)
                    (ThetaLowerSegment.join cell13322496 cell13330688)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13338880 cell13347072)
                    (ThetaLowerSegment.join cell13355264 cell13363456))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13371648 cell13379840)
                    (ThetaLowerSegment.join cell13388032 cell13396224)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13404416 cell13412608)
                    (ThetaLowerSegment.join cell13420800 cell13428992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13437184 cell13445376)
                    (ThetaLowerSegment.join cell13453568 cell13461760))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13469952 cell13478144)
                    (ThetaLowerSegment.join cell13486336 cell13494528))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13502720 cell13510912)
                    (ThetaLowerSegment.join cell13519104 cell13527296)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13535488 cell13543680)
                    (ThetaLowerSegment.join cell13551872 cell13560064))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13568256 cell13576448)
                    (ThetaLowerSegment.join cell13584640 cell13592832)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13601024 cell13609216)
                    (ThetaLowerSegment.join cell13617408 cell13625600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13633792 cell13641984)
                    (ThetaLowerSegment.join cell13650176 cell13658368)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13666560 cell13674752)
                    (ThetaLowerSegment.join cell13682944 cell13691136))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13699328 cell13707520)
                    (ThetaLowerSegment.join cell13715712 cell13723904))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13732096 cell13740288)
                    (ThetaLowerSegment.join cell13748480 cell13756672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13764864 cell13773056)
                    (ThetaLowerSegment.join cell13781248 cell13789440)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13797632 cell13805824)
                    (ThetaLowerSegment.join cell13814016 cell13822208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell13830400 cell13838592)
                    (ThetaLowerSegment.join cell13846784 cell13854976))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell13863168 cell13871360)
              (ThetaLowerSegment.join cell13879552 cell13887744))
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell13895936 cell13904128)
              (ThetaLowerSegment.join cell13912320 cell13920512))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
