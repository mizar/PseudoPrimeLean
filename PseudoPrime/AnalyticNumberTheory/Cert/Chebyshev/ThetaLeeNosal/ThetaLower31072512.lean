/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis8192

/-! # Direct theta estimate up to 31072512 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell21563648 :
    ThetaLowerSegment 21563648 21580032 (107785947657 / 5000) (13483523114 / 625) := by
  exact
    packedTile8192 21563648 21580032 11 974 4643 24 _ _ (33773 / 2000) (1688653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21580032 :
    ThetaLowerSegment 21580032 21596416 (13483523114 / 625) (1079511857949 / 50000) := by
  exact
    packedTile8192 21580032 21596416 11 983 4645 24 _ _ (844363 / 50000) (1688729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21596416 :
    ThetaLowerSegment 21596416 21612800 (1079511857949 / 50000) (1080342748533 / 50000) := by
  exact
    packedTile8192 21596416 21612800 11 984 4647 24 _ _ (844401 / 50000) (337761 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21612800 :
    ThetaLowerSegment 21612800 21629184 (1080342748533 / 50000) (216230344219 / 10000) := by
  exact
    packedTile8192 21612800 21629184 11 958 4648 24 _ _ (844439 / 50000) (1688881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21629184 :
    ThetaLowerSegment 21629184 21645568 (216230344219 / 10000) (1081964107969 / 50000) := by
  exact
    packedTile8192 21629184 21645568 11 962 4650 24 _ _ (844477 / 50000) (1688957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21645568 :
    ThetaLowerSegment 21645568 21661952 (1081964107969 / 50000) (541388687957 / 25000) := by
  exact
    packedTile8192 21645568 21661952 11 963 4652 24 _ _ (168903 / 10000) (1689033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21661952 :
    ThetaLowerSegment 21661952 21678336 (541388687957 / 25000) (1083606726469 / 50000) := by
  exact
    packedTile8192 21661952 21678336 11 982 4654 24 _ _ (337821 / 20000) (422277 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21678336 :
    ThetaLowerSegment 21678336 21694720 (1083606726469 / 50000) (433769378193 / 20000) := by
  exact
    packedTile8192 21678336 21694720 11 967 4656 24 _ _ (1689181 / 100000) (52787 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21694720 :
    ThetaLowerSegment 21694720 21711104 (433769378193 / 20000) (2170520943661 / 100000) := by
  exact
    packedTile8192 21694720 21711104 11 991 4657 24 _ _ (211157 / 12500) (1689259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21711104 :
    ThetaLowerSegment 21711104 21727488 (2170520943661 / 100000) (2172130877057 / 100000) := by
  exact
    packedTile8192 21711104 21727488 11 953 4659 24 _ _ (422333 / 25000) (337867 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21727488 :
    ThetaLowerSegment 21727488 21743872 (2172130877057 / 100000) (1086902539697 / 50000) := by
  exact
    packedTile8192 21727488 21743872 11 991 4661 24 _ _ (1689407 / 100000) (168941 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21743872 :
    ThetaLowerSegment 21743872 21760256 (1086902539697 / 50000) (2175428672557 / 100000) := by
  exact
    packedTile8192 21743872 21760256 11 961 4663 24 _ _ (1689483 / 100000) (844743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21760256 :
    ThetaLowerSegment 21760256 21776640 (2175428672557 / 100000) (2177050648237 / 100000) := by
  exact
    packedTile8192 21760256 21776640 11 960 4664 24 _ _ (844779 / 50000) (1689561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21776640 :
    ThetaLowerSegment 21776640 21793024 (2177050648237 / 100000) (435750083807 / 20000) := by
  exact
    packedTile8192 21776640 21793024 11 1006 4666 24 _ _ (1689633 / 100000) (422409 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21793024 :
    ThetaLowerSegment 21793024 21809408 (435750083807 / 20000) (545088488219 / 25000) := by
  exact
    packedTile8192 21793024 21809408 11 949 4668 24 _ _ (1689709 / 100000) (105607 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21809408 :
    ThetaLowerSegment 21809408 21825792 (545088488219 / 25000) (545499950623 / 25000) := by
  exact
    packedTile8192 21809408 21825792 11 974 4670 24 _ _ (211223 / 12500) (1689787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21825792 :
    ThetaLowerSegment 21825792 21842176 (545499950623 / 25000) (1091819482861 / 50000) := by
  exact
    packedTile8192 21825792 21842176 11 970 4671 24 _ _ (1689859 / 100000) (844931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21842176 :
    ThetaLowerSegment 21842176 21858560 (1091819482861 / 50000) (273159563971 / 12500) := by
  exact
    packedTile8192 21842176 21858560 11 969 4673 24 _ _ (844967 / 50000) (1689937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21858560 :
    ThetaLowerSegment 21858560 21874944 (273159563971 / 12500) (546733180147 / 25000) := by
  exact
    packedTile8192 21858560 21874944 11 980 4675 24 _ _ (1690009 / 100000) (422503 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21874944 :
    ThetaLowerSegment 21874944 21891328 (546733180147 / 25000) (136787340833 / 6250) := by
  exact
    packedTile8192 21874944 21891328 11 985 4677 24 _ _ (422521 / 25000) (1690087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21891328 :
    ThetaLowerSegment 21891328 21907712 (136787340833 / 6250) (273775810587 / 12500) := by
  exact
    packedTile8192 21891328 21907712 11 952 4678 24 _ _ (1690159 / 100000) (845081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21907712 :
    ThetaLowerSegment 21907712 21924096 (273775810587 / 12500) (2191871364201 / 100000) := by
  exact
    packedTile8192 21907712 21924096 11 985 4680 24 _ _ (1690233 / 100000) (422559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21924096 :
    ThetaLowerSegment 21924096 21940480 (2191871364201 / 100000) (2193556601277 / 100000) := by
  exact
    packedTile8192 21924096 21940480 11 997 4682 24 _ _ (422577 / 25000) (1690311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21940480 :
    ThetaLowerSegment 21940480 21956864 (2193556601277 / 100000) (1097609123883 / 50000) := by
  exact
    packedTile8192 21940480 21956864 11 983 4684 24 _ _ (1690383 / 100000) (845193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21956864 :
    ThetaLowerSegment 21956864 21973248 (1097609123883 / 50000) (219685461111 / 10000) := by
  exact
    packedTile8192 21956864 21973248 11 968 4685 24 _ _ (845229 / 50000) (1690461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21973248 :
    ThetaLowerSegment 21973248 21989632 (219685461111 / 10000) (43969888543 / 2000) := by
  exact
    packedTile8192 21973248 21989632 11 970 4687 24 _ _ (422633 / 25000) (338107 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell21989632 :
    ThetaLowerSegment 21989632 22006016 (43969888543 / 2000) (2200115719263 / 100000) := by
  exact
    packedTile8192 21989632 22006016 11 959 4689 24 _ _ (1690607 / 100000) (169061 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22006016 :
    ThetaLowerSegment 22006016 22022400 (2200115719263 / 100000) (550440187969 / 25000) := by
  exact
    packedTile8192 22006016 22022400 11 973 4691 24 _ _ (1690681 / 100000) (422671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22022400 :
    ThetaLowerSegment 22022400 22038784 (550440187969 / 25000) (275430804451 / 12500) := by
  exact
    packedTile8192 22022400 22038784 11 997 4692 24 _ _ (422689 / 25000) (1690759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22038784 :
    ThetaLowerSegment 22038784 22055168 (275430804451 / 12500) (551276707667 / 25000) := by
  exact
    packedTile8192 22038784 22055168 11 982 4694 24 _ _ (169083 / 10000) (1690833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22055168 :
    ThetaLowerSegment 22055168 22071552 (551276707667 / 25000) (110335490383 / 5000) := by
  exact
    packedTile8192 22055168 22071552 11 948 4696 24 _ _ (211363 / 12500) (1690907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22071552 :
    ThetaLowerSegment 22071552 22087936 (110335490383 / 5000) (2208277345193 / 100000) := by
  exact
    packedTile8192 22071552 22087936 11 927 4698 24 _ _ (1690979 / 100000) (845491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22087936 :
    ThetaLowerSegment 22087936 22104320 (2208277345193 / 100000) (441978121951 / 20000) := by
  exact
    packedTile8192 22087936 22104320 11 954 4699 24 _ _ (1691053 / 100000) (105691 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22104320 :
    ThetaLowerSegment 22104320 22120704 (441978121951 / 20000) (2211507327167 / 100000) := by
  exact
    packedTile8192 22104320 22120704 11 956 4701 24 _ _ (1691127 / 100000) (169113 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22120704 :
    ThetaLowerSegment 22120704 22137088 (2211507327167 / 100000) (2213151174539 / 100000) := by
  exact
    packedTile8192 22120704 22137088 11 972 4703 24 _ _ (1691201 / 100000) (422801 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22137088 :
    ThetaLowerSegment 22137088 22153472 (2213151174539 / 100000) (1107388244907 / 50000) := by
  exact
    packedTile8192 22137088 22153472 11 961 4705 24 _ _ (67651 / 4000) (845639 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22153472 :
    ThetaLowerSegment 22153472 22169856 (1107388244907 / 50000) (1108206857823 / 50000) := by
  exact
    packedTile8192 22153472 22169856 11 968 4706 24 _ _ (1691349 / 100000) (211419 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22169856 :
    ThetaLowerSegment 22169856 22186240 (1108206857823 / 50000) (443615276891 / 20000) := by
  exact
    packedTile8192 22169856 22186240 11 983 4708 24 _ _ (1691423 / 100000) (845713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22186240 :
    ThetaLowerSegment 22186240 22202624 (443615276891 / 20000) (1109815435099 / 50000) := by
  exact
    packedTile8192 22186240 22202624 11 919 4710 24 _ _ (1691497 / 100000) (3383 / 200) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22202624 :
    ThetaLowerSegment 22202624 22219008 (1109815435099 / 50000) (1110617239753 / 50000) := by
  exact
    packedTile8192 22202624 22219008 11 948 4711 24 _ _ (1691571 / 100000) (845787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22219008 :
    ThetaLowerSegment 22219008 22235392 (1110617239753 / 50000) (222285169117 / 10000) := by
  exact
    packedTile8192 22219008 22235392 11 956 4713 24 _ _ (422911 / 25000) (1691647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22235392 :
    ThetaLowerSegment 22235392 22251776 (222285169117 / 10000) (278061370739 / 12500) := by
  exact
    packedTile8192 22235392 22251776 11 969 4715 24 _ _ (845859 / 50000) (1691721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22251776 :
    ThetaLowerSegment 22251776 22268160 (278061370739 / 12500) (55653257809 / 2500) := by
  exact
    packedTile8192 22251776 22268160 11 969 4717 24 _ _ (105737 / 6250) (338359 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22268160 :
    ThetaLowerSegment 22268160 22284544 (55653257809 / 2500) (17822049557 / 800) := by
  exact
    packedTile8192 22268160 22284544 11 961 4718 24 _ _ (338373 / 20000) (422967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22284544 :
    ThetaLowerSegment 22284544 22300928 (17822049557 / 800) (2229407527089 / 100000) := by
  exact
    packedTile8192 22284544 22300928 11 976 4720 24 _ _ (1691939 / 100000) (845971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22300928 :
    ThetaLowerSegment 22300928 22317312 (2229407527089 / 100000) (2231065698849 / 100000) := by
  exact
    packedTile8192 22300928 22317312 11 980 4722 24 _ _ (423003 / 25000) (338403 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22317312 :
    ThetaLowerSegment 22317312 22333696 (2231065698849 / 100000) (2232701946011 / 100000) := by
  exact
    packedTile8192 22317312 22333696 11 967 4724 24 _ _ (846043 / 50000) (1692089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22333696 :
    ThetaLowerSegment 22333696 22350080 (2232701946011 / 100000) (2234295959789 / 100000) := by
  exact
    packedTile8192 22333696 22350080 11 942 4725 24 _ _ (1692159 / 100000) (846081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22350080 :
    ThetaLowerSegment 22350080 22366464 (2234295959789 / 100000) (1117961097851 / 50000) := by
  exact
    packedTile8192 22350080 22366464 11 961 4727 24 _ _ (1692233 / 100000) (423059 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22366464 :
    ThetaLowerSegment 22366464 22382848 (1117961097851 / 50000) (1118781866261 / 50000) := by
  exact
    packedTile8192 22366464 22382848 11 970 4729 24 _ _ (846153 / 50000) (1692309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22382848 :
    ThetaLowerSegment 22382848 22399232 (1118781866261 / 50000) (279897282761 / 12500) := by
  exact
    packedTile8192 22382848 22399232 11 954 4731 24 _ _ (1692379 / 100000) (846191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22399232 :
    ThetaLowerSegment 22399232 22407424 (279897282761 / 12500) (279998829881 / 12500) := by
  exact
    packedTile8192 22399232 22407424 10 480 4732 24 _ _ (423113 / 25000) (338491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22407424 :
    ThetaLowerSegment 22407424 22415616 (279998829881 / 12500) (448158237269 / 20000) := by
  exact
    packedTile8192 22407424 22415616 10 473 4733 24 _ _ (1692489 / 100000) (423123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22415616 :
    ThetaLowerSegment 22415616 22423808 (448158237269 / 20000) (224163914137 / 10000) := by
  exact
    packedTile8192 22415616 22423808 10 501 4734 24 _ _ (67701 / 4000) (105783 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22423808 :
    ThetaLowerSegment 22423808 22432000 (224163914137 / 10000) (560608238237 / 25000) := by
  exact
    packedTile8192 22423808 22432000 10 469 4735 24 _ _ (846281 / 50000) (338513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22432000 :
    ThetaLowerSegment 22432000 22440192 (560608238237 / 25000) (70101524537 / 3125) := by
  exact
    packedTile8192 22432000 22440192 10 482 4736 24 _ _ (846299 / 50000) (1692601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22440192 :
    ThetaLowerSegment 22440192 22448384 (70101524537 / 3125) (1122025547087 / 50000) := by
  exact
    packedTile8192 22440192 22448384 10 474 4737 24 _ _ (338527 / 20000) (846319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22448384 :
    ThetaLowerSegment 22448384 22456576 (1122025547087 / 50000) (1122431788127 / 50000) := by
  exact
    packedTile8192 22448384 22456576 10 480 4737 24 _ _ (1692671 / 100000) (846337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22456576 :
    ThetaLowerSegment 22456576 22464768 (1122431788127 / 50000) (1122837191693 / 50000) := by
  exact
    packedTile8192 22456576 22464768 10 479 4738 24 _ _ (423177 / 25000) (1692711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22464768 :
    ThetaLowerSegment 22464768 22472960 (1122837191693 / 50000) (1123259531321 / 50000) := by
  exact
    packedTile8192 22464768 22472960 10 499 4739 24 _ _ (211593 / 12500) (1692747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22472960 :
    ThetaLowerSegment 22472960 22481152 (1123259531321 / 50000) (2247343446989 / 100000) := by
  exact
    packedTile8192 22472960 22481152 10 487 4740 24 _ _ (1692781 / 100000) (105799 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22481152 :
    ThetaLowerSegment 22481152 22489344 (2247343446989 / 100000) (562041962217 / 25000) := by
  exact
    packedTile8192 22481152 22489344 10 487 4741 24 _ _ (1692817 / 100000) (84641 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22489344 :
    ThetaLowerSegment 22489344 22497536 (562041962217 / 25000) (224896856881 / 10000) := by
  exact
    packedTile8192 22489344 22497536 10 473 4742 24 _ _ (846427 / 50000) (1692857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22497536 :
    ThetaLowerSegment 22497536 22505728 (224896856881 / 10000) (56244655867 / 2500) := by
  exact
    packedTile8192 22497536 22505728 10 483 4743 24 _ _ (169289 / 10000) (1692893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22505728 :
    ThetaLowerSegment 22505728 22513920 (56244655867 / 2500) (2250597146713 / 100000) := by
  exact
    packedTile8192 22505728 22513920 10 479 4744 24 _ _ (1692927 / 100000) (169293 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22513920 :
    ThetaLowerSegment 22513920 22522112 (2250597146713 / 100000) (2251436856361 / 100000) := by
  exact
    packedTile8192 22513920 22522112 10 496 4744 24 _ _ (1692963 / 100000) (846483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22522112 :
    ThetaLowerSegment 22522112 22530304 (2251436856361 / 100000) (1126130673437 / 50000) := by
  exact
    packedTile8192 22522112 22530304 10 487 4745 24 _ _ (1692999 / 100000) (846501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22530304 :
    ThetaLowerSegment 22530304 22538496 (1126130673437 / 50000) (1126555625473 / 50000) := by
  exact
    packedTile8192 22530304 22538496 10 502 4746 24 _ _ (423259 / 25000) (1693039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22538496 :
    ThetaLowerSegment 22538496 22546688 (1126555625473 / 50000) (1126969581577 / 50000) := by
  exact
    packedTile8192 22538496 22546688 10 489 4747 24 _ _ (105817 / 6250) (67723 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22546688 :
    ThetaLowerSegment 22546688 22563072 (1126969581577 / 50000) (1127789045849 / 50000) := by
  exact
    packedTile8192 22546688 22563072 11 968 4748 24 _ _ (423277 / 25000) (1693111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22563072 :
    ThetaLowerSegment 22563072 22579456 (1127789045849 / 50000) (1128618704539 / 50000) := by
  exact
    packedTile8192 22563072 22579456 11 980 4750 24 _ _ (1693181 / 100000) (52912 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22579456 :
    ThetaLowerSegment 22579456 22595840 (1128618704539 / 50000) (141180520733 / 6250) := by
  exact
    packedTile8192 22579456 22595840 11 975 4751 24 _ _ (846627 / 50000) (1693257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22595840 :
    ThetaLowerSegment 22595840 22612224 (141180520733 / 6250) (282563393923 / 12500) := by
  exact
    packedTile8192 22595840 22612224 11 956 4753 24 _ _ (846663 / 50000) (1693329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22612224 :
    ThetaLowerSegment 22612224 22628608 (282563393923 / 12500) (1131101968591 / 50000) := by
  exact
    packedTile8192 22612224 22628608 11 1002 4755 24 _ _ (1693399 / 100000) (846701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22628608 :
    ThetaLowerSegment 22628608 22644992 (1131101968591 / 50000) (2263794106451 / 100000) := by
  exact
    packedTile8192 22628608 22644992 11 939 4756 24 _ _ (1693471 / 100000) (846737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22644992 :
    ThetaLowerSegment 22644992 22661376 (2263794106451 / 100000) (2265409746473 / 100000) := by
  exact
    packedTile8192 22644992 22661376 11 954 4758 24 _ _ (1693543 / 100000) (846773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22661376 :
    ThetaLowerSegment 22661376 22677760 (2265409746473 / 100000) (2267057634841 / 100000) := by
  exact
    packedTile8192 22661376 22677760 11 973 4760 24 _ _ (105851 / 6250) (1693619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22677760 :
    ThetaLowerSegment 22677760 22694144 (2267057634841 / 100000) (2268727611209 / 100000) := by
  exact
    packedTile8192 22677760 22694144 11 986 4762 24 _ _ (211711 / 12500) (1693691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22694144 :
    ThetaLowerSegment 22694144 22710528 (2268727611209 / 100000) (2270397658569 / 100000) := by
  exact
    packedTile8192 22694144 22710528 11 986 4763 24 _ _ (10586 / 625) (1693763 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22710528 :
    ThetaLowerSegment 22710528 22726912 (2270397658569 / 100000) (454402376093 / 20000) := by
  exact
    packedTile8192 22710528 22726912 11 953 4765 24 _ _ (211729 / 12500) (338767 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22726912 :
    ThetaLowerSegment 22726912 22743296 (454402376093 / 20000) (22736837647 / 1000) := by
  exact
    packedTile8192 22726912 22743296 11 987 4767 24 _ _ (338781 / 20000) (423477 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22743296 :
    ThetaLowerSegment 22743296 22759680 (22736837647 / 1000) (2275325228413 / 100000) := by
  exact
    packedTile8192 22743296 22759680 11 969 4768 24 _ _ (1693977 / 100000) (84699 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22759680 :
    ThetaLowerSegment 22759680 22776064 (2275325228413 / 100000) (2276917634473 / 100000) := by
  exact
    packedTile8192 22759680 22776064 11 940 4770 24 _ _ (1694049 / 100000) (423513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22776064 :
    ThetaLowerSegment 22776064 22792448 (2276917634473 / 100000) (1139279618861 / 50000) := by
  exact
    packedTile8192 22776064 22792448 11 969 4772 24 _ _ (1694121 / 100000) (423531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22792448 :
    ThetaLowerSegment 22792448 22808832 (1139279618861 / 50000) (1140085207157 / 50000) := by
  exact
    packedTile8192 22792448 22808832 11 951 4774 24 _ _ (105887 / 6250) (338839 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22808832 :
    ThetaLowerSegment 22808832 22825216 (1140085207157 / 50000) (1140903536669 / 50000) := by
  exact
    packedTile8192 22808832 22825216 11 966 4775 24 _ _ (211783 / 12500) (1694267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22825216 :
    ThetaLowerSegment 22825216 22841600 (1140903536669 / 50000) (1141721900957 / 50000) := by
  exact
    packedTile8192 22825216 22841600 11 966 4777 24 _ _ (52948 / 3125) (1694339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22841600 :
    ThetaLowerSegment 22841600 22857984 (1141721900957 / 50000) (1142561480121 / 50000) := by
  exact
    packedTile8192 22841600 22857984 11 991 4779 24 _ _ (211801 / 12500) (1694411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22857984 :
    ThetaLowerSegment 22857984 22874368 (1142561480121 / 50000) (1143369747081 / 50000) := by
  exact
    packedTile8192 22857984 22874368 11 954 4781 24 _ _ (21181 / 1250) (1694483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22874368 :
    ThetaLowerSegment 22874368 22890752 (1143369747081 / 50000) (28604959563 / 1250) := by
  exact
    packedTile8192 22874368 22890752 11 978 4782 24 _ _ (1694551 / 100000) (847277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22890752 :
    ThetaLowerSegment 22890752 22907136 (28604959563 / 1250) (114502874779 / 5000) := by
  exact
    packedTile8192 22890752 22907136 11 980 4784 24 _ _ (1694623 / 100000) (847313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22907136 :
    ThetaLowerSegment 22907136 22923520 (114502874779 / 5000) (572926184537 / 25000) := by
  exact
    packedTile8192 22907136 22923520 11 972 4786 24 _ _ (847347 / 50000) (1694697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22923520 :
    ThetaLowerSegment 22923520 22939904 (572926184537 / 25000) (573331233611 / 25000) := by
  exact
    packedTile8192 22923520 22939904 11 956 4787 24 _ _ (847383 / 50000) (1694769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22939904 :
    ThetaLowerSegment 22939904 22956288 (573331233611 / 25000) (91798282499 / 4000) := by
  exact
    packedTile8192 22939904 22956288 11 963 4789 24 _ _ (1694837 / 100000) (42371 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22956288 :
    ThetaLowerSegment 22956288 22972672 (91798282499 / 4000) (2296607903841 / 100000) := by
  exact
    packedTile8192 22956288 22972672 11 974 4791 24 _ _ (1694909 / 100000) (52966 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22972672 :
    ThetaLowerSegment 22972672 22989056 (2296607903841 / 100000) (2298209659941 / 100000) := by
  exact
    packedTile8192 22972672 22989056 11 945 4792 24 _ _ (84749 / 5000) (1694983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell22989056 :
    ThetaLowerSegment 22989056 23005440 (2298209659941 / 100000) (1149948117843 / 50000) := by
  exact
    packedTile8192 22989056 23005440 11 995 4794 24 _ _ (1695051 / 100000) (847527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23005440 :
    ThetaLowerSegment 23005440 23021824 (1149948117843 / 50000) (71924200233 / 3125) := by
  exact
    packedTile8192 23005440 23021824 11 990 4796 24 _ _ (1695123 / 100000) (847563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23021824 :
    ThetaLowerSegment 23021824 23038208 (71924200233 / 3125) (287902767003 / 12500) := by
  exact
    packedTile8192 23021824 23038208 11 972 4798 24 _ _ (847597 / 50000) (1695197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23038208 :
    ThetaLowerSegment 23038208 23054592 (287902767003 / 12500) (72026973517 / 3125) := by
  exact
    packedTile8192 23038208 23054592 11 968 4799 24 _ _ (339053 / 20000) (423817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23054592 :
    ThetaLowerSegment 23054592 23070976 (72026973517 / 3125) (144154607609 / 6250) := by
  exact
    packedTile8192 23054592 23070976 11 950 4801 24 _ _ (211917 / 12500) (1695339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23070976 :
    ThetaLowerSegment 23070976 23087360 (144154607609 / 6250) (2308113180313 / 100000) := by
  exact
    packedTile8192 23070976 23087360 11 967 4803 24 _ _ (1695407 / 100000) (169541 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23087360 :
    ThetaLowerSegment 23087360 23103744 (2308113180313 / 100000) (2309740839193 / 100000) := by
  exact
    packedTile8192 23087360 23103744 11 960 4804 24 _ _ (847739 / 50000) (1695481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23103744 :
    ThetaLowerSegment 23103744 23120128 (2309740839193 / 100000) (1155681739793 / 50000) := by
  exact
    packedTile8192 23103744 23120128 11 957 4806 24 _ _ (1695549 / 100000) (52986 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23120128 :
    ThetaLowerSegment 23120128 23136512 (1155681739793 / 50000) (1156489702723 / 50000) := by
  exact
    packedTile8192 23120128 23136512 11 953 4808 24 _ _ (84781 / 5000) (1695623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23136512 :
    ThetaLowerSegment 23136512 23152896 (1156489702723 / 50000) (231461405157 / 10000) := by
  exact
    packedTile8192 23136512 23152896 11 964 4810 24 _ _ (1695691 / 100000) (847847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23152896 :
    ThetaLowerSegment 23152896 23169280 (231461405157 / 10000) (579086356143 / 25000) := by
  exact
    packedTile8192 23152896 23169280 11 1021 4811 24 _ _ (847881 / 50000) (339153 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23169280 :
    ThetaLowerSegment 23169280 23185664 (579086356143 / 25000) (579484876663 / 25000) := by
  exact
    packedTile8192 23169280 23185664 11 940 4813 24 _ _ (211979 / 12500) (339167 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23185664 :
    ThetaLowerSegment 23185664 23202048 (579484876663 / 25000) (579885109771 / 25000) := by
  exact
    packedTile8192 23185664 23202048 11 944 4815 24 _ _ (1695903 / 100000) (847953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23202048 :
    ThetaLowerSegment 23202048 23218432 (579885109771 / 25000) (580287055609 / 25000) := by
  exact
    packedTile8192 23202048 23218432 11 948 4816 24 _ _ (847987 / 50000) (1695977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23218432 :
    ThetaLowerSegment 23218432 23234816 (580287055609 / 25000) (58069877029 / 2500) := by
  exact
    packedTile8192 23218432 23234816 11 971 4818 24 _ _ (424011 / 25000) (1696047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23234816 :
    ThetaLowerSegment 23234816 23251200 (58069877029 / 2500) (232441995933 / 10000) := by
  exact
    packedTile8192 23234816 23251200 11 958 4820 24 _ _ (339223 / 20000) (848059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23251200 :
    ThetaLowerSegment 23251200 23267584 (232441995933 / 10000) (93043085283 / 4000) := by
  exact
    packedTile8192 23251200 23267584 11 977 4821 24 _ _ (339237 / 20000) (424047 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23267584 :
    ThetaLowerSegment 23267584 23283968 (93043085283 / 4000) (465556373871 / 20000) := by
  exact
    packedTile8192 23267584 23283968 11 1005 4823 24 _ _ (53008 / 3125) (1696259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23283968 :
    ThetaLowerSegment 23283968 23300352 (465556373871 / 20000) (465878675811 / 20000) := by
  exact
    packedTile8192 23283968 23300352 11 950 4825 24 _ _ (848163 / 50000) (1696329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23300352 :
    ThetaLowerSegment 23300352 23316736 (465878675811 / 20000) (2331059239927 / 100000) := by
  exact
    packedTile8192 23300352 23316736 11 982 4827 24 _ _ (424099 / 25000) (1696399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23316736 :
    ThetaLowerSegment 23316736 23333120 (2331059239927 / 100000) (2332687848247 / 100000) := by
  exact
    packedTile8192 23316736 23333120 11 960 4828 24 _ _ (1696467 / 100000) (169647 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23333120 :
    ThetaLowerSegment 23333120 23349504 (2332687848247 / 100000) (583577858539 / 25000) := by
  exact
    packedTile8192 23333120 23349504 11 957 4830 24 _ _ (1696537 / 100000) (84827 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23349504 :
    ThetaLowerSegment 23349504 23365888 (583577858539 / 25000) (2335989378479 / 100000) := by
  exact
    packedTile8192 23349504 23365888 11 989 4832 24 _ _ (1696607 / 100000) (169661 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23365888 :
    ThetaLowerSegment 23365888 23382272 (2335989378479 / 100000) (584408364623 / 25000) := by
  exact
    packedTile8192 23365888 23382272 11 969 4833 24 _ _ (1696677 / 100000) (42417 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23382272 :
    ThetaLowerSegment 23382272 23398656 (584408364623 / 25000) (584802009927 / 25000) := by
  exact
    packedTile8192 23382272 23398656 11 928 4835 24 _ _ (1696747 / 100000) (6787 / 400) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23398656 :
    ThetaLowerSegment 23398656 23415040 (584802009927 / 25000) (2340828499943 / 100000) := by
  exact
    packedTile8192 23398656 23415040 11 955 4837 24 _ _ (1696817 / 100000) (84841 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23415040 :
    ThetaLowerSegment 23415040 23431424 (2340828499943 / 100000) (468490144783 / 20000) := by
  exact
    packedTile8192 23415040 23431424 11 956 4838 24 _ _ (1696887 / 100000) (169689 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23431424 :
    ThetaLowerSegment 23431424 23447808 (468490144783 / 20000) (586032253597 / 25000) := by
  exact
    packedTile8192 23431424 23447808 11 989 4840 24 _ _ (1696957 / 100000) (10606 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23447808 :
    ThetaLowerSegment 23447808 23464192 (586032253597 / 25000) (1172887565289 / 50000) := by
  exact
    packedTile8192 23447808 23464192 11 970 4842 24 _ _ (1697027 / 100000) (169703 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23464192 :
    ThetaLowerSegment 23464192 23480576 (1172887565289 / 50000) (469487996547 / 20000) := by
  exact
    packedTile8192 23464192 23480576 11 981 4843 24 _ _ (1697097 / 100000) (16971 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23480576 :
    ThetaLowerSegment 23480576 23496960 (469487996547 / 20000) (2349076051723 / 100000) := by
  exact
    packedTile8192 23480576 23496960 11 964 4845 24 _ _ (1697167 / 100000) (169717 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23496960 :
    ThetaLowerSegment 23496960 23513344 (2349076051723 / 100000) (2350674848977 / 100000) := by
  exact
    packedTile8192 23496960 23513344 11 942 4847 24 _ _ (1697237 / 100000) (42431 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23513344 :
    ThetaLowerSegment 23513344 23529728 (2350674848977 / 100000) (2352314446573 / 100000) := by
  exact
    packedTile8192 23513344 23529728 11 966 4849 24 _ _ (848653 / 50000) (1697309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23529728 :
    ThetaLowerSegment 23529728 23546112 (2352314446573 / 100000) (470791161833 / 20000) := by
  exact
    packedTile8192 23529728 23546112 11 967 4850 24 _ _ (53043 / 3125) (1697379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23546112 :
    ThetaLowerSegment 23546112 23562496 (470791161833 / 20000) (2355609121569 / 100000) := by
  exact
    packedTile8192 23546112 23562496 11 974 4852 24 _ _ (848723 / 50000) (1697449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23562496 :
    ThetaLowerSegment 23562496 23578880 (2355609121569 / 100000) (1178625309287 / 50000) := by
  exact
    packedTile8192 23562496 23578880 11 967 4854 24 _ _ (339503 / 20000) (848759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23578880 :
    ThetaLowerSegment 23578880 23595264 (1178625309287 / 50000) (1179433359747 / 50000) := by
  exact
    packedTile8192 23578880 23595264 11 952 4855 24 _ _ (339517 / 20000) (424397 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23595264 :
    ThetaLowerSegment 23595264 23611648 (1179433359747 / 50000) (1180249931321 / 50000) := by
  exact
    packedTile8192 23595264 23611648 11 962 4857 24 _ _ (848827 / 50000) (1697657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23611648 :
    ThetaLowerSegment 23611648 23628032 (1180249931321 / 50000) (1181081816081 / 50000) := by
  exact
    packedTile8192 23611648 23628032 11 980 4859 24 _ _ (424431 / 25000) (1697727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23628032 :
    ThetaLowerSegment 23628032 23644416 (1181081816081 / 50000) (295472066939 / 12500) := by
  exact
    packedTile8192 23628032 23644416 11 950 4860 24 _ _ (1697793 / 100000) (424449 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23644416 :
    ThetaLowerSegment 23644416 23660800 (295472066939 / 12500) (236543874241 / 10000) := by
  exact
    packedTile8192 23644416 23660800 11 979 4862 24 _ _ (848931 / 50000) (339573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23660800 :
    ThetaLowerSegment 23660800 23677184 (236543874241 / 10000) (1183549659953 / 50000) := by
  exact
    packedTile8192 23660800 23677184 11 978 4864 24 _ _ (424483 / 25000) (339587 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23677184 :
    ThetaLowerSegment 23677184 23693568 (1183549659953 / 50000) (47374044657 / 2000) := by
  exact
    packedTile8192 23677184 23693568 11 944 4865 24 _ _ (1698001 / 100000) (424501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23693568 :
    ThetaLowerSegment 23693568 23709952 (47374044657 / 2000) (59258351953 / 2500) := by
  exact
    packedTile8192 23693568 23709952 11 961 4867 24 _ _ (169807 / 10000) (1698073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23709952 :
    ThetaLowerSegment 23709952 23726336 (59258351953 / 2500) (2371942215753 / 100000) := by
  exact
    packedTile8192 23709952 23726336 11 947 4869 24 _ _ (1698139 / 100000) (849071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23726336 :
    ThetaLowerSegment 23726336 23742720 (2371942215753 / 100000) (2373560607977 / 100000) := by
  exact
    packedTile8192 23726336 23742720 11 953 4870 24 _ _ (53069 / 3125) (1698211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23742720 :
    ThetaLowerSegment 23742720 23759104 (2373560607977 / 100000) (2375201143559 / 100000) := by
  exact
    packedTile8192 23742720 23759104 11 966 4872 25 _ _ (1698277 / 100000) (42457 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23759104 :
    ThetaLowerSegment 23759104 23775488 (2375201143559 / 100000) (2376848539179 / 100000) := by
  exact
    packedTile8192 23759104 23775488 11 970 4874 25 _ _ (849173 / 50000) (1698349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23775488 :
    ThetaLowerSegment 23775488 23791872 (2376848539179 / 100000) (594619329791 / 25000) := by
  exact
    packedTile8192 23775488 23791872 11 959 4876 25 _ _ (339683 / 20000) (849209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23791872 :
    ThetaLowerSegment 23791872 23808256 (594619329791 / 25000) (595029513677 / 25000) := by
  exact
    packedTile8192 23791872 23808256 11 966 4877 25 _ _ (424621 / 25000) (1698487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23808256 :
    ThetaLowerSegment 23808256 23824640 (595029513677 / 25000) (2381801320731 / 100000) := by
  exact
    packedTile8192 23808256 23824640 11 991 4879 25 _ _ (1698553 / 100000) (424639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23824640 :
    ThetaLowerSegment 23824640 23841024 (2381801320731 / 100000) (2383377641947 / 100000) := by
  exact
    packedTile8192 23824640 23841024 11 928 4881 25 _ _ (849311 / 50000) (13589 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23841024 :
    ThetaLowerSegment 23841024 23857408 (2383377641947 / 100000) (2384965917097 / 100000) := by
  exact
    packedTile8192 23841024 23857408 11 935 4882 25 _ _ (169869 / 10000) (1698693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23857408 :
    ThetaLowerSegment 23857408 23873792 (2384965917097 / 100000) (1193307706043 / 50000) := by
  exact
    packedTile8192 23857408 23873792 11 971 4884 25 _ _ (1698759 / 100000) (849381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23873792 :
    ThetaLowerSegment 23873792 23890176 (1193307706043 / 50000) (1194140131763 / 50000) := by
  exact
    packedTile8192 23873792 23890176 11 980 4886 25 _ _ (424707 / 25000) (1698831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23890176 :
    ThetaLowerSegment 23890176 23906560 (1194140131763 / 50000) (1194966644667 / 50000) := by
  exact
    packedTile8192 23890176 23906560 11 973 4887 25 _ _ (106181 / 6250) (1698899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23906560 :
    ThetaLowerSegment 23906560 23922944 (1194966644667 / 50000) (597897020311 / 25000) := by
  exact
    packedTile8192 23906560 23922944 11 974 4889 25 _ _ (339793 / 20000) (212371 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23922944 :
    ThetaLowerSegment 23922944 23939328 (597897020311 / 25000) (598308186297 / 25000) := by
  exact
    packedTile8192 23922944 23939328 11 968 4891 25 _ _ (1699033 / 100000) (424759 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23939328 :
    ThetaLowerSegment 23939328 23955712 (598308186297 / 25000) (598712572573 / 25000) := by
  exact
    packedTile8192 23939328 23955712 11 952 4892 25 _ _ (849551 / 50000) (339821 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23955712 :
    ThetaLowerSegment 23955712 23972096 (598712572573 / 25000) (1198241596331 / 50000) := by
  exact
    packedTile8192 23955712 23972096 11 961 4894 25 _ _ (169917 / 10000) (1699173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23972096 :
    ThetaLowerSegment 23972096 23988480 (1198241596331 / 50000) (1199047035617 / 50000) := by
  exact
    packedTile8192 23972096 23988480 11 948 4896 25 _ _ (1699239 / 100000) (849621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell23988480 :
    ThetaLowerSegment 23988480 24004864 (1199047035617 / 50000) (2399801874769 / 100000) := by
  exact
    packedTile8192 23988480 24004864 11 1005 4897 25 _ _ (1699307 / 100000) (169931 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24004864 :
    ThetaLowerSegment 24004864 24021248 (2399801874769 / 100000) (1200712388947 / 50000) := by
  exact
    packedTile8192 24004864 24021248 11 955 4899 25 _ _ (2719 / 160) (849689 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24021248 :
    ThetaLowerSegment 24021248 24037632 (1200712388947 / 50000) (2403047745959 / 100000) := by
  exact
    packedTile8192 24021248 24037632 11 955 4901 25 _ _ (1699443 / 100000) (849723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24037632 :
    ThetaLowerSegment 24037632 24054016 (2403047745959 / 100000) (2404714967231 / 100000) := by
  exact
    packedTile8192 24037632 24054016 11 981 4902 25 _ _ (212439 / 12500) (339903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24054016 :
    ThetaLowerSegment 24054016 24070400 (2404714967231 / 100000) (2406355061931 / 100000) := by
  exact
    packedTile8192 24054016 24070400 11 965 4904 25 _ _ (84979 / 5000) (1699583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24070400 :
    ThetaLowerSegment 24070400 24086784 (2406355061931 / 100000) (2408005420139 / 100000) := by
  exact
    packedTile8192 24070400 24086784 11 971 4906 25 _ _ (53114 / 3125) (1699651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24086784 :
    ThetaLowerSegment 24086784 24103168 (2408005420139 / 100000) (2409601453463 / 100000) := by
  exact
    packedTile8192 24086784 24103168 11 939 4907 25 _ _ (424929 / 25000) (1699719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24103168 :
    ThetaLowerSegment 24103168 24119552 (2409601453463 / 100000) (2411228146751 / 100000) := by
  exact
    packedTile8192 24103168 24119552 11 957 4909 25 _ _ (212473 / 12500) (1699787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24119552 :
    ThetaLowerSegment 24119552 24135936 (2411228146751 / 100000) (2412822607927 / 100000) := by
  exact
    packedTile8192 24119552 24135936 11 938 4911 25 _ _ (424963 / 25000) (339971 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24135936 :
    ThetaLowerSegment 24135936 24152320 (2412822607927 / 100000) (2414493629287 / 100000) := by
  exact
    packedTile8192 24135936 24152320 11 983 4912 25 _ _ (21249 / 1250) (1699923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24152320 :
    ThetaLowerSegment 24152320 24168704 (2414493629287 / 100000) (2416190217311 / 100000) := by
  exact
    packedTile8192 24152320 24168704 11 998 4914 25 _ _ (424997 / 25000) (1699991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24168704 :
    ThetaLowerSegment 24168704 24185088 (2416190217311 / 100000) (604450042349 / 25000) := by
  exact
    packedTile8192 24168704 24185088 11 947 4916 25 _ _ (340011 / 20000) (850029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24185088 :
    ThetaLowerSegment 24185088 24201472 (604450042349 / 25000) (2419450988829 / 100000) := by
  exact
    packedTile8192 24185088 24201472 11 971 4917 25 _ _ (1700123 / 100000) (850063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24201472 :
    ThetaLowerSegment 24201472 24217856 (2419450988829 / 100000) (2421096773717 / 100000) := by
  exact
    packedTile8192 24201472 24217856 11 968 4919 25 _ _ (1700191 / 100000) (850097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24217856 :
    ThetaLowerSegment 24217856 24234240 (2421096773717 / 100000) (302848141363 / 12500) := by
  exact
    packedTile8192 24217856 24234240 11 993 4921 25 _ _ (1700259 / 100000) (850131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24234240 :
    ThetaLowerSegment 24234240 24250624 (302848141363 / 12500) (1212202770791 / 50000) := by
  exact
    packedTile8192 24234240 24250624 11 953 4922 25 _ _ (850163 / 50000) (1700329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24250624 :
    ThetaLowerSegment 24250624 24267008 (1212202770791 / 50000) (303253252133 / 12500) := by
  exact
    packedTile8192 24250624 24267008 11 953 4924 25 _ _ (850197 / 50000) (1700397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24267008 :
    ThetaLowerSegment 24267008 24283392 (303253252133 / 12500) (1213858137649 / 50000) := by
  exact
    packedTile8192 24267008 24283392 11 994 4926 25 _ _ (1700461 / 100000) (106279 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24283392 :
    ThetaLowerSegment 24283392 24299776 (1213858137649 / 50000) (1214684594743 / 50000) := by
  exact
    packedTile8192 24283392 24299776 11 972 4927 25 _ _ (1700529 / 100000) (425133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24299776 :
    ThetaLowerSegment 24299776 24316160 (1214684594743 / 50000) (1215511084399 / 50000) := by
  exact
    packedTile8192 24299776 24316160 11 972 4929 25 _ _ (425149 / 25000) (1700599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24316160 :
    ThetaLowerSegment 24316160 24332544 (1215511084399 / 50000) (1216326552787 / 50000) := by
  exact
    packedTile8192 24316160 24332544 11 959 4931 25 _ _ (212583 / 12500) (1700667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24332544 :
    ThetaLowerSegment 24332544 24348928 (1216326552787 / 50000) (304283600003 / 12500) := by
  exact
    packedTile8192 24332544 24348928 11 950 4932 25 _ _ (1700731 / 100000) (850367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24348928 :
    ThetaLowerSegment 24348928 24365312 (304283600003 / 12500) (1217970342229 / 50000) := by
  exact
    packedTile8192 24348928 24365312 11 983 4934 25 _ _ (850399 / 50000) (1700801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24365312 :
    ThetaLowerSegment 24365312 24381696 (1217970342229 / 50000) (1218785057043 / 50000) := by
  exact
    packedTile8192 24365312 24381696 11 958 4936 25 _ _ (850433 / 50000) (1700869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24381696 :
    ThetaLowerSegment 24381696 24398080 (1218785057043 / 50000) (1219611710481 / 50000) := by
  exact
    packedTile8192 24381696 24398080 11 972 4937 25 _ _ (1700933 / 100000) (212617 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24398080 :
    ThetaLowerSegment 24398080 24414464 (1219611710481 / 50000) (1220446050981 / 50000) := by
  exact
    packedTile8192 24398080 24414464 11 981 4939 25 _ _ (1701 / 100) (1701003 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24414464 :
    ThetaLowerSegment 24414464 24430848 (1220446050981 / 50000) (2442509816679 / 100000) := by
  exact
    packedTile8192 24414464 24430848 11 951 4941 25 _ _ (1701067 / 100000) (170107 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24430848 :
    ThetaLowerSegment 24430848 24447232 (2442509816679 / 100000) (2444117388309 / 100000) := by
  exact
    packedTile8192 24430848 24447232 11 945 4942 25 _ _ (850567 / 50000) (1701137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24447232 :
    ThetaLowerSegment 24447232 24463616 (2444117388309 / 100000) (2445713114847 / 100000) := by
  exact
    packedTile8192 24447232 24463616 11 938 4944 25 _ _ (1701201 / 100000) (425301 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24463616 :
    ThetaLowerSegment 24463616 24480000 (2445713114847 / 100000) (2447366747343 / 100000) := by
  exact
    packedTile8192 24463616 24480000 11 972 4946 25 _ _ (425317 / 25000) (1701271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24480000 :
    ThetaLowerSegment 24480000 24496384 (2447366747343 / 100000) (612251283237 / 25000) := by
  exact
    packedTile8192 24480000 24496384 11 963 4947 25 _ _ (340267 / 20000) (850669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24496384 :
    ThetaLowerSegment 24496384 24512768 (612251283237 / 25000) (612664723923 / 25000) := by
  exact
    packedTile8192 24496384 24512768 11 972 4949 25 _ _ (850701 / 50000) (340281 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24512768 :
    ThetaLowerSegment 24512768 24529152 (612664723923 / 25000) (613073076483 / 25000) := by
  exact
    packedTile8192 24512768 24529152 11 960 4951 25 _ _ (1701469 / 100000) (53171 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24529152 :
    ThetaLowerSegment 24529152 24545536 (613073076483 / 25000) (613487400499 / 25000) := by
  exact
    packedTile8192 24529152 24545536 11 974 4952 25 _ _ (53173 / 3125) (1701539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24545536 :
    ThetaLowerSegment 24545536 24561920 (613487400499 / 25000) (613895785219 / 25000) := by
  exact
    packedTile8192 24545536 24561920 11 960 4954 25 _ _ (1701603 / 100000) (850803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24561920 :
    ThetaLowerSegment 24561920 24578304 (613895785219 / 25000) (1228627089917 / 50000) := by
  exact
    packedTile8192 24561920 24578304 11 982 4955 25 _ _ (1701669 / 100000) (212709 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24578304 :
    ThetaLowerSegment 24578304 24594688 (1228627089917 / 50000) (1229426905837 / 50000) := by
  exact
    packedTile8192 24578304 24594688 11 940 4957 25 _ _ (212717 / 12500) (1701739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24594688 :
    ThetaLowerSegment 24594688 24611072 (1229426905837 / 50000) (2460468822721 / 100000) := by
  exact
    packedTile8192 24594688 24611072 11 949 4959 25 _ _ (1701803 / 100000) (850903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24611072 :
    ThetaLowerSegment 24611072 24627456 (2460468822721 / 100000) (615528632511 / 25000) := by
  exact
    packedTile8192 24611072 24627456 11 967 4960 25 _ _ (1701869 / 100000) (106367 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24627456 :
    ThetaLowerSegment 24627456 24643840 (615528632511 / 25000) (615936671667 / 25000) := by
  exact
    packedTile8192 24627456 24643840 11 959 4962 25 _ _ (106371 / 6250) (1701939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24643840 :
    ThetaLowerSegment 24643840 24660224 (615936671667 / 25000) (77042824893 / 3125) := by
  exact
    packedTile8192 24643840 24660224 11 954 4964 25 _ _ (851001 / 50000) (340401 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24660224 :
    ThetaLowerSegment 24660224 24676608 (77042824893 / 3125) (2467046934541 / 100000) := by
  exact
    packedTile8192 24660224 24676608 11 985 4965 25 _ _ (1702069 / 100000) (212759 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24676608 :
    ThetaLowerSegment 24676608 24692992 (2467046934541 / 100000) (2468735452461 / 100000) := by
  exact
    packedTile8192 24676608 24692992 11 992 4967 25 _ _ (340427 / 20000) (851069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24692992 :
    ThetaLowerSegment 24692992 24709376 (2468735452461 / 100000) (494077998561 / 20000) := by
  exact
    packedTile8192 24692992 24709376 11 972 4969 25 _ _ (851101 / 50000) (340441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24709376 :
    ThetaLowerSegment 24709376 24725760 (494077998561 / 20000) (494409940821 / 20000) := by
  exact
    packedTile8192 24709376 24725760 11 975 4970 25 _ _ (425567 / 25000) (1702271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24725760 :
    ThetaLowerSegment 24725760 24742144 (494409940821 / 20000) (494728277279 / 20000) := by
  exact
    packedTile8192 24725760 24742144 11 935 4972 25 _ _ (851167 / 50000) (1702337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24742144 :
    ThetaLowerSegment 24742144 24758528 (494728277279 / 20000) (495059564319 / 20000) := by
  exact
    packedTile8192 24742144 24758528 11 973 4974 25 _ _ (2128 / 125) (1702403 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24758528 :
    ThetaLowerSegment 24758528 24774912 (495059564319 / 20000) (619244539131 / 25000) := by
  exact
    packedTile8192 24758528 24774912 11 987 4975 25 _ _ (1702467 / 100000) (170247 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24774912 :
    ThetaLowerSegment 24774912 24791296 (619244539131 / 25000) (1239301186503 / 50000) := by
  exact
    packedTile8192 24774912 24791296 11 954 4977 25 _ _ (1702533 / 100000) (212817 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24791296 :
    ThetaLowerSegment 24791296 24807680 (1239301186503 / 50000) (310024075059 / 12500) := by
  exact
    packedTile8192 24791296 24807680 11 934 4979 25 _ _ (1702599 / 100000) (851301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24807680 :
    ThetaLowerSegment 24807680 24824064 (310024075059 / 12500) (2481818645547 / 100000) := by
  exact
    packedTile8192 24807680 24824064 11 955 4980 25 _ _ (340533 / 20000) (425667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24824064 :
    ThetaLowerSegment 24824064 24840448 (2481818645547 / 100000) (2483429429073 / 100000) := by
  exact
    packedTile8192 24824064 24840448 11 946 4982 25 _ _ (1702731 / 100000) (851367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24840448 :
    ThetaLowerSegment 24840448 24856832 (2483429429073 / 100000) (99402973239 / 4000) := by
  exact
    packedTile8192 24840448 24856832 11 966 4984 25 _ _ (1702797 / 100000) (4257 / 250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24856832 :
    ThetaLowerSegment 24856832 24873216 (99402973239 / 4000) (621685358463 / 25000) := by
  exact
    packedTile8192 24856832 24873216 11 979 4985 25 _ _ (1702863 / 100000) (851433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24873216 :
    ThetaLowerSegment 24873216 24889600 (621685358463 / 25000) (2488367731047 / 100000) := by
  exact
    packedTile8192 24873216 24889600 11 955 4987 25 _ _ (1702929 / 100000) (425733 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24889600 :
    ThetaLowerSegment 24889600 24905984 (2488367731047 / 100000) (1244998748631 / 50000) := by
  exact
    packedTile8192 24889600 24905984 11 957 4988 25 _ _ (340599 / 20000) (851499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24905984 :
    ThetaLowerSegment 24905984 24922368 (1244998748631 / 50000) (1245794929181 / 50000) := by
  exact
    packedTile8192 24905984 24922368 11 935 4990 25 _ _ (85153 / 5000) (1703063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24922368 :
    ThetaLowerSegment 24922368 24938752 (1245794929181 / 50000) (249320442181 / 10000) := by
  exact
    packedTile8192 24922368 24938752 11 948 4992 25 _ _ (851563 / 50000) (1703129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24938752 :
    ThetaLowerSegment 24938752 24955136 (249320442181 / 10000) (1247420594661 / 50000) := by
  exact
    packedTile8192 24938752 24955136 11 961 4993 25 _ _ (212899 / 12500) (340639 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24955136 :
    ThetaLowerSegment 24955136 24971520 (1247420594661 / 50000) (124825604271 / 5000) := by
  exact
    packedTile8192 24955136 24971520 11 981 4995 25 _ _ (851629 / 50000) (1703261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24971520 :
    ThetaLowerSegment 24971520 24987904 (124825604271 / 5000) (2498159198761 / 100000) := by
  exact
    packedTile8192 24971520 24987904 11 967 4997 25 _ _ (1703323 / 100000) (851663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell24987904 :
    ThetaLowerSegment 24987904 25004288 (2498159198761 / 100000) (1249894671017 / 50000) := by
  exact
    packedTile8192 24987904 25004288 11 957 4998 25 _ _ (1703389 / 100000) (53231 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25004288 :
    ThetaLowerSegment 25004288 25020672 (1249894671017 / 50000) (625365959329 / 25000) := by
  exact
    packedTile8192 25004288 25020672 11 983 5000 25 _ _ (851727 / 50000) (1703457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25020672 :
    ThetaLowerSegment 25020672 25037056 (625365959329 / 25000) (625764157129 / 25000) := by
  exact
    packedTile8192 25020672 25037056 11 935 5002 25 _ _ (10647 / 625) (1703523 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25037056 :
    ThetaLowerSegment 25037056 25053440 (625764157129 / 25000) (2504663109171 / 100000) := by
  exact
    packedTile8192 25037056 25053440 11 943 5003 25 _ _ (340717 / 20000) (425897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25053440 :
    ThetaLowerSegment 25053440 25069824 (2504663109171 / 100000) (2506336094453 / 100000) := by
  exact
    packedTile8192 25053440 25069824 11 982 5005 25 _ _ (1703651 / 100000) (851827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25069824 :
    ThetaLowerSegment 25069824 25086208 (2506336094453 / 100000) (2507997217553 / 100000) := by
  exact
    packedTile8192 25069824 25086208 11 975 5006 25 _ _ (425929 / 25000) (1703719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25086208 :
    ThetaLowerSegment 25086208 25102592 (2507997217553 / 100000) (20077090039 / 800) := by
  exact
    packedTile8192 25086208 25102592 11 962 5008 25 _ _ (1703781 / 100000) (212973 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25102592 :
    ThetaLowerSegment 25102592 25118976 (20077090039 / 800) (2511336694181 / 100000) := by
  exact
    packedTile8192 25102592 25118976 11 998 5010 25 _ _ (1703847 / 100000) (34077 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25118976 :
    ThetaLowerSegment 25118976 25135360 (2511336694181 / 100000) (2512963930141 / 100000) := by
  exact
    packedTile8192 25118976 25135360 11 955 5011 25 _ _ (212989 / 12500) (340783 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25135360 :
    ThetaLowerSegment 25135360 25151744 (2512963930141 / 100000) (2514514549211 / 100000) := by
  exact
    packedTile8192 25135360 25151744 11 910 5013 25 _ _ (1703977 / 100000) (85199 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25151744 :
    ThetaLowerSegment 25151744 25168128 (2514514549211 / 100000) (2516129981027 / 100000) := by
  exact
    packedTile8192 25151744 25168128 11 948 5015 25 _ _ (852021 / 50000) (340809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25168128 :
    ThetaLowerSegment 25168128 25184512 (2516129981027 / 100000) (2517776148389 / 100000) := by
  exact
    packedTile8192 25168128 25184512 11 966 5016 25 _ _ (1704107 / 100000) (170411 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25184512 :
    ThetaLowerSegment 25184512 25200896 (2517776148389 / 100000) (2519410449337 / 100000) := by
  exact
    packedTile8192 25184512 25200896 11 959 5018 25 _ _ (426043 / 25000) (68167 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25200896 :
    ThetaLowerSegment 25200896 25217280 (2519410449337 / 100000) (504199418983 / 20000) := by
  exact
    packedTile8192 25200896 25217280 11 931 5020 25 _ _ (852119 / 50000) (1704241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25217280 :
    ThetaLowerSegment 25217280 25233664 (504199418983 / 20000) (315324679429 / 12500) := by
  exact
    packedTile8192 25217280 25233664 11 939 5021 25 _ _ (1704303 / 100000) (852153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25233664 :
    ThetaLowerSegment 25233664 25250048 (315324679429 / 12500) (252418931421 / 10000) := by
  exact
    packedTile8192 25233664 25250048 11 934 5023 25 _ _ (1704367 / 100000) (170437 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25250048 :
    ThetaLowerSegment 25250048 25266432 (252418931421 / 10000) (1262915341113 / 50000) := by
  exact
    packedTile8192 25250048 25266432 11 963 5024 25 _ _ (106527 / 6250) (340887 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25266432 :
    ThetaLowerSegment 25266432 25282816 (1262915341113 / 50000) (2527485748813 / 100000) := by
  exact
    packedTile8192 25266432 25282816 11 971 5026 25 _ _ (1704497 / 100000) (3409 / 200) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25282816 :
    ThetaLowerSegment 25282816 25299200 (2527485748813 / 100000) (2529094855341 / 100000) := by
  exact
    packedTile8192 25282816 25299200 11 944 5028 25 _ _ (852281 / 50000) (340913 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25299200 :
    ThetaLowerSegment 25299200 25315584 (2529094855341 / 100000) (1265385251841 / 50000) := by
  exact
    packedTile8192 25299200 25315584 11 983 5029 25 _ _ (1704627 / 100000) (170463 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25315584 :
    ThetaLowerSegment 25315584 25331968 (1265385251841 / 50000) (1266204356347 / 50000) := by
  exact
    packedTile8192 25315584 25331968 11 961 5031 25 _ _ (426173 / 25000) (340939 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25331968 :
    ThetaLowerSegment 25331968 25348352 (1266204356347 / 50000) (253403845943 / 10000) := by
  exact
    packedTile8192 25331968 25348352 11 956 5033 25 _ _ (426189 / 25000) (1704759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25348352 :
    ThetaLowerSegment 25348352 25364736 (253403845943 / 10000) (1267823905227 / 50000) := by
  exact
    packedTile8192 25348352 25364736 11 944 5034 25 _ _ (1704821 / 100000) (213103 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25364736 :
    ThetaLowerSegment 25364736 25381120 (1267823905227 / 50000) (317159497073 / 12500) := by
  exact
    packedTile8192 25364736 25381120 11 955 5036 25 _ _ (852443 / 50000) (1704889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25381120 :
    ThetaLowerSegment 25381120 25397504 (317159497073 / 12500) (1269477676167 / 50000) := by
  exact
    packedTile8192 25381120 25397504 11 985 5037 25 _ _ (34099 / 2000) (1704953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25397504 :
    ThetaLowerSegment 25397504 25413888 (1269477676167 / 50000) (2540559771449 / 100000) := by
  exact
    packedTile8192 25397504 25413888 11 941 5039 25 _ _ (341003 / 20000) (852509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25413888 :
    ThetaLowerSegment 25413888 25430272 (2540559771449 / 100000) (2542155725393 / 100000) := by
  exact
    packedTile8192 25413888 25430272 11 936 5041 25 _ _ (1705079 / 100000) (852541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25430272 :
    ThetaLowerSegment 25430272 25446656 (2542155725393 / 100000) (2543813125361 / 100000) := by
  exact
    packedTile8192 25430272 25446656 11 972 5042 25 _ _ (213143 / 12500) (1705147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25446656 :
    ThetaLowerSegment 25446656 25463040 (2543813125361 / 100000) (2545492755241 / 100000) := by
  exact
    packedTile8192 25446656 25463040 11 985 5044 25 _ _ (213151 / 12500) (1705211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25463040 :
    ThetaLowerSegment 25463040 25479424 (2545492755241 / 100000) (2547187795609 / 100000) := by
  exact
    packedTile8192 25463040 25479424 11 994 5046 25 _ _ (213159 / 12500) (68211 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25479424 :
    ThetaLowerSegment 25479424 25495808 (2547187795609 / 100000) (637197276763 / 25000) := by
  exact
    packedTile8192 25479424 25495808 11 939 5047 25 _ _ (1705337 / 100000) (85267 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25495808 :
    ThetaLowerSegment 25495808 25512192 (637197276763 / 25000) (2550370013779 / 100000) := by
  exact
    packedTile8192 25495808 25512192 11 927 5049 25 _ _ (1705401 / 100000) (426351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25512192 :
    ThetaLowerSegment 25512192 25528576 (2550370013779 / 100000) (319003678903 / 12500) := by
  exact
    packedTile8192 25512192 25528576 11 973 5050 25 _ _ (341093 / 20000) (426367 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25528576 :
    ThetaLowerSegment 25528576 25544960 (319003678903 / 12500) (1276848719293 / 50000) := by
  exact
    packedTile8192 25528576 25544960 11 978 5052 25 _ _ (1705529 / 100000) (426383 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25544960 :
    ThetaLowerSegment 25544960 25561344 (1276848719293 / 50000) (51106559729 / 2000) := by
  exact
    packedTile8192 25544960 25561344 11 956 5054 25 _ _ (852797 / 50000) (1705597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25561344 :
    ThetaLowerSegment 25561344 25577728 (51106559729 / 2000) (79905329222 / 3125) := by
  exact
    packedTile8192 25561344 25577728 11 963 5055 25 _ _ (852829 / 50000) (1705661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25577728 :
    ThetaLowerSegment 25577728 25594112 (79905329222 / 3125) (639652859917 / 25000) := by
  exact
    packedTile8192 25577728 25594112 11 962 5057 25 _ _ (852861 / 50000) (68229 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25594112 :
    ThetaLowerSegment 25594112 25610496 (639652859917 / 25000) (320028139153 / 12500) := by
  exact
    packedTile8192 25594112 25610496 11 946 5059 25 _ _ (852893 / 50000) (1705789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25610496 :
    ThetaLowerSegment 25610496 25626880 (320028139153 / 12500) (1280935629237 / 50000) := by
  exact
    packedTile8192 25610496 25626880 11 965 5060 25 _ _ (34117 / 2000) (1705853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25626880 :
    ThetaLowerSegment 25626880 25643264 (1280935629237 / 50000) (80110880373 / 3125) := by
  exact
    packedTile8192 25626880 25643264 11 983 5062 25 _ _ (852957 / 50000) (1705917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25643264 :
    ThetaLowerSegment 25643264 25659648 (80110880373 / 3125) (1282580160573 / 50000) := by
  exact
    packedTile8192 25643264 25659648 11 945 5063 25 _ _ (852989 / 50000) (1705981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25659648 :
    ThetaLowerSegment 25659648 25676032 (1282580160573 / 50000) (1283363233851 / 50000) := by
  exact
    packedTile8192 25659648 25676032 11 918 5065 25 _ _ (853021 / 50000) (341209 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25676032 :
    ThetaLowerSegment 25676032 25692416 (1283363233851 / 50000) (2568383095657 / 100000) := by
  exact
    packedTile8192 25676032 25692416 11 971 5067 25 _ _ (341221 / 20000) (426527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25692416 :
    ThetaLowerSegment 25692416 25708800 (2568383095657 / 100000) (1285021599047 / 50000) := by
  exact
    packedTile8192 25692416 25708800 11 973 5068 25 _ _ (1706169 / 100000) (426543 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25708800 :
    ThetaLowerSegment 25708800 25725184 (1285021599047 / 50000) (2571713600201 / 100000) := by
  exact
    packedTile8192 25708800 25725184 11 979 5070 25 _ _ (1706233 / 100000) (426559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25725184 :
    ThetaLowerSegment 25725184 25741568 (2571713600201 / 100000) (128666473173 / 5000) := by
  exact
    packedTile8192 25725184 25741568 11 947 5072 25 _ _ (1706297 / 100000) (17063 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25741568 :
    ThetaLowerSegment 25741568 25757952 (128666473173 / 5000) (25749999899 / 1000) := by
  exact
    packedTile8192 25741568 25757952 11 979 5073 25 _ _ (42659 / 2500) (1706363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25757952 :
    ThetaLowerSegment 25757952 25774336 (25749999899 / 1000) (644159965841 / 25000) := by
  exact
    packedTile8192 25757952 25774336 11 961 5075 25 _ _ (213303 / 12500) (1706427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25774336 :
    ThetaLowerSegment 25774336 25790720 (644159965841 / 25000) (515656642069 / 20000) := by
  exact
    packedTile8192 25774336 25790720 11 963 5076 25 _ _ (1706487 / 100000) (170649 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25790720 :
    ThetaLowerSegment 25790720 25807104 (515656642069 / 20000) (1289970135683 / 50000) := by
  exact
    packedTile8192 25790720 25807104 11 971 5078 25 _ _ (1706551 / 100000) (853277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25807104 :
    ThetaLowerSegment 25807104 25823488 (1289970135683 / 50000) (2581570088691 / 100000) := by
  exact
    packedTile8192 25807104 25823488 11 955 5080 25 _ _ (341323 / 20000) (853309 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25823488 :
    ThetaLowerSegment 25823488 25839872 (2581570088691 / 100000) (2583266526623 / 100000) := by
  exact
    packedTile8192 25823488 25839872 11 994 5081 25 _ _ (853339 / 50000) (1706681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25839872 :
    ThetaLowerSegment 25839872 25856256 (2583266526623 / 100000) (16155624236 / 625) := by
  exact
    packedTile8192 25839872 25856256 11 957 5083 25 _ _ (1706741 / 100000) (213343 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25856256 :
    ThetaLowerSegment 25856256 25872640 (16155624236 / 625) (51730699939 / 2000) := by
  exact
    packedTile8192 25856256 25872640 11 958 5084 25 _ _ (341361 / 20000) (213351 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25872640 :
    ThetaLowerSegment 25872640 25889024 (51730699939 / 2000) (1294097889757 / 50000) := by
  exact
    packedTile8192 25872640 25889024 11 973 5086 25 _ _ (426717 / 25000) (1706871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25889024 :
    ThetaLowerSegment 25889024 25905408 (1294097889757 / 50000) (323724610099 / 12500) := by
  exact
    packedTile8192 25889024 25905408 11 938 5088 25 _ _ (1706931 / 100000) (853467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25905408 :
    ThetaLowerSegment 25905408 25921792 (323724610099 / 12500) (2591430475007 / 100000) := by
  exact
    packedTile8192 25905408 25921792 11 957 5089 25 _ _ (341399 / 20000) (853499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25921792 :
    ThetaLowerSegment 25921792 25938176 (2591430475007 / 100000) (2593111927137 / 100000) := by
  exact
    packedTile8192 25921792 25938176 11 985 5091 25 _ _ (853529 / 50000) (1707061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25938176 :
    ThetaLowerSegment 25938176 25954560 (2593111927137 / 100000) (2594709792393 / 100000) := by
  exact
    packedTile8192 25938176 25954560 11 936 5092 25 _ _ (1707121 / 100000) (426781 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25954560 :
    ThetaLowerSegment 25954560 25970944 (2594709792393 / 100000) (103853128113 / 4000) := by
  exact
    packedTile8192 25954560 25970944 11 948 5094 25 _ _ (106699 / 6250) (1707187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25970944 :
    ThetaLowerSegment 25970944 25987328 (103853128113 / 4000) (519596846483 / 20000) := by
  exact
    packedTile8192 25970944 25987328 11 970 5096 25 _ _ (1707247 / 100000) (6829 / 400) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell25987328 :
    ThetaLowerSegment 25987328 26003712 (519596846483 / 20000) (519931479243 / 20000) := by
  exact
    packedTile8192 25987328 26003712 11 980 5097 25 _ _ (170731 / 10000) (1707313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26003712 :
    ThetaLowerSegment 26003712 26020096 (519931479243 / 20000) (650314301179 / 25000) := by
  exact
    packedTile8192 26003712 26020096 11 937 5099 25 _ _ (1707373 / 100000) (106711 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26020096 :
    ThetaLowerSegment 26020096 26036480 (650314301179 / 25000) (650724939537 / 25000) := by
  exact
    packedTile8192 26020096 26036480 11 962 5100 25 _ _ (426859 / 25000) (1707439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26036480 :
    ThetaLowerSegment 26036480 26052864 (650724939537 / 25000) (1302271186093 / 50000) := by
  exact
    packedTile8192 26036480 26052864 11 962 5102 25 _ _ (1707499 / 100000) (853751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26052864 :
    ThetaLowerSegment 26052864 26069248 (1302271186093 / 50000) (325773344299 / 12500) := by
  exact
    packedTile8192 26052864 26069248 11 963 5104 25 _ _ (853781 / 50000) (341513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26069248 :
    ThetaLowerSegment 26069248 26085632 (325773344299 / 12500) (2607786799017 / 100000) := by
  exact
    packedTile8192 26069248 26085632 11 937 5105 25 _ _ (13661 / 800) (426907 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26085632 :
    ThetaLowerSegment 26085632 26102016 (2607786799017 / 100000) (521897531253 / 20000) := by
  exact
    packedTile8192 26085632 26102016 11 996 5107 25 _ _ (213461 / 12500) (1707691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26102016 :
    ThetaLowerSegment 26102016 26118400 (521897531253 / 20000) (652770246987 / 25000) := by
  exact
    packedTile8192 26102016 26118400 11 933 5109 25 _ _ (1707751 / 100000) (853877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26118400 :
    ThetaLowerSegment 26118400 26134784 (652770246987 / 25000) (81649116369 / 3125) := by
  exact
    packedTile8192 26118400 26134784 11 990 5110 25 _ _ (853907 / 50000) (1707817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26134784 :
    ThetaLowerSegment 26134784 26151168 (81649116369 / 3125) (326798421813 / 12500) := by
  exact
    packedTile8192 26134784 26151168 11 946 5112 25 _ _ (426969 / 25000) (1707879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26151168 :
    ThetaLowerSegment 26151168 26167552 (326798421813 / 12500) (26160338277 / 1000) := by
  exact
    packedTile8192 26151168 26167552 11 964 5113 25 _ _ (1707939 / 100000) (853971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26167552 :
    ThetaLowerSegment 26167552 26183936 (26160338277 / 1000) (1308820528791 / 50000) := by
  exact
    packedTile8192 26167552 26183936 11 941 5115 25 _ _ (854001 / 50000) (341601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26183936 :
    ThetaLowerSegment 26183936 26200320 (1308820528791 / 50000) (1309619048711 / 50000) := by
  exact
    packedTile8192 26183936 26200320 11 935 5117 25 _ _ (53377 / 3125) (1708067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26200320 :
    ThetaLowerSegment 26200320 26216704 (1309619048711 / 50000) (1310452614687 / 50000) := by
  exact
    packedTile8192 26200320 26216704 11 976 5118 25 _ _ (1708127 / 100000) (170813 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26216704 :
    ThetaLowerSegment 26216704 26233088 (1310452614687 / 50000) (2622553631759 / 100000) := by
  exact
    packedTile8192 26216704 26233088 11 965 5120 25 _ _ (1708189 / 100000) (53381 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26233088 :
    ThetaLowerSegment 26233088 26249472 (2622553631759 / 100000) (104964188983 / 4000) := by
  exact
    packedTile8192 26233088 26249472 11 908 5121 25 _ _ (427063 / 25000) (341651 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26249472 :
    ThetaLowerSegment 26249472 26265856 (104964188983 / 4000) (2625742997701 / 100000) := by
  exact
    packedTile8192 26249472 26265856 11 959 5123 25 _ _ (854157 / 50000) (1708317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26265856 :
    ThetaLowerSegment 26265856 26282240 (2625742997701 / 100000) (2627396706637 / 100000) := by
  exact
    packedTile8192 26265856 26282240 11 968 5125 25 _ _ (1708377 / 100000) (85419 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26282240 :
    ThetaLowerSegment 26282240 26298624 (2627396706637 / 100000) (82157667196 / 3125) := by
  exact
    packedTile8192 26282240 26298624 11 965 5126 25 _ _ (1708439 / 100000) (854221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26298624 :
    ThetaLowerSegment 26298624 26315008 (82157667196 / 3125) (2630670134723 / 100000) := by
  exact
    packedTile8192 26298624 26315008 11 951 5128 25 _ _ (1708501 / 100000) (213563 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26315008 :
    ThetaLowerSegment 26315008 26331392 (2630670134723 / 100000) (263235990353 / 10000) := by
  exact
    packedTile8192 26315008 26331392 11 989 5129 25 _ _ (1708563 / 100000) (854283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26331392 :
    ThetaLowerSegment 26331392 26347776 (263235990353 / 10000) (82310957323 / 3125) := by
  exact
    packedTile8192 26331392 26347776 11 931 5131 25 _ _ (854313 / 50000) (1708629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26347776 :
    ThetaLowerSegment 26347776 26364160 (82310957323 / 3125) (164725397063 / 6250) := by
  exact
    packedTile8192 26347776 26364160 11 969 5133 25 _ _ (106793 / 6250) (1708691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26364160 :
    ThetaLowerSegment 26364160 26380544 (164725397063 / 6250) (1318627648379 / 50000) := by
  exact
    packedTile8192 26364160 26380544 11 965 5134 25 _ _ (1367 / 80) (1708753 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26380544 :
    ThetaLowerSegment 26380544 26396928 (1318627648379 / 50000) (263888037697 / 10000) := by
  exact
    packedTile8192 26380544 26396928 11 951 5136 25 _ _ (427203 / 25000) (341763 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26396928 :
    ThetaLowerSegment 26396928 26413312 (263888037697 / 10000) (264060633971 / 10000) := by
  exact
    packedTile8192 26396928 26413312 11 1010 5137 25 _ _ (854437 / 50000) (1708877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26413312 :
    ThetaLowerSegment 26413312 26429696 (264060633971 / 10000) (1321137130623 / 50000) := by
  exact
    packedTile8192 26413312 26429696 11 976 5139 25 _ _ (213617 / 12500) (1708939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26429696 :
    ThetaLowerSegment 26429696 26446080 (1321137130623 / 50000) (82619510076 / 3125) := by
  exact
    packedTile8192 26429696 26446080 11 907 5140 25 _ _ (854499 / 50000) (1709001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26446080 :
    ThetaLowerSegment 26446080 26462464 (82619510076 / 3125) (330686118359 / 12500) := by
  exact
    packedTile8192 26446080 26462464 11 974 5142 25 _ _ (85453 / 5000) (1709063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26462464 :
    ThetaLowerSegment 26462464 26478848 (330686118359 / 12500) (1323575961289 / 50000) := by
  exact
    packedTile8192 26462464 26478848 11 973 5144 25 _ _ (854561 / 50000) (13673 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26478848 :
    ThetaLowerSegment 26478848 26495232 (1323575961289 / 50000) (264878077493 / 10000) := by
  exact
    packedTile8192 26478848 26495232 11 953 5145 25 _ _ (53412 / 3125) (1709187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26495232 :
    ThetaLowerSegment 26495232 26511616 (264878077493 / 10000) (1325239882727 / 50000) := by
  exact
    packedTile8192 26495232 26511616 11 994 5147 25 _ _ (854623 / 50000) (1709249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26511616 :
    ThetaLowerSegment 26511616 26528000 (1325239882727 / 50000) (1326039838871 / 50000) := by
  exact
    packedTile8192 26511616 26528000 11 936 5148 25 _ _ (427327 / 25000) (1709311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26528000 :
    ThetaLowerSegment 26528000 26544384 (1326039838871 / 50000) (331718716529 / 12500) := by
  exact
    packedTile8192 26528000 26544384 11 977 5150 25 _ _ (170937 / 10000) (1709373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26544384 :
    ThetaLowerSegment 26544384 26560768 (331718716529 / 12500) (132771932503 / 5000) := by
  exact
    packedTile8192 26544384 26560768 11 988 5152 25 _ _ (1709431 / 100000) (854717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26560768 :
    ThetaLowerSegment 26560768 26577152 (132771932503 / 5000) (664259683877 / 25000) := by
  exact
    packedTile8192 26560768 26577152 11 936 5153 25 _ _ (1709493 / 100000) (213687 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26577152 :
    ThetaLowerSegment 26577152 26593536 (664259683877 / 25000) (2658708970743 / 100000) := by
  exact
    packedTile8192 26577152 26593536 11 977 5155 25 _ _ (341911 / 20000) (854779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26593536 :
    ThetaLowerSegment 26593536 26609920 (2658708970743 / 100000) (2660292075159 / 100000) := by
  exact
    packedTile8192 26593536 26609920 11 926 5156 25 _ _ (106851 / 6250) (1709619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26609920 :
    ThetaLowerSegment 26609920 26626304 (2660292075159 / 100000) (2661943624107 / 100000) := by
  exact
    packedTile8192 26609920 26626304 11 966 5158 25 _ _ (854839 / 50000) (1709681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26626304 :
    ThetaLowerSegment 26626304 26642688 (2661943624107 / 100000) (2663602071907 / 100000) := by
  exact
    packedTile8192 26626304 26642688 11 970 5160 25 _ _ (85487 / 5000) (1709743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26642688 :
    ThetaLowerSegment 26642688 26659072 (2663602071907 / 100000) (2665243480867 / 100000) := by
  exact
    packedTile8192 26642688 26659072 11 960 5161 25 _ _ (1709801 / 100000) (427451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26659072 :
    ThetaLowerSegment 26659072 26675456 (2665243480867 / 100000) (2666867850717 / 100000) := by
  exact
    packedTile8192 26659072 26675456 11 950 5163 25 _ _ (1709863 / 100000) (854933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26675456 :
    ThetaLowerSegment 26675456 26691840 (2666867850717 / 100000) (2668500828137 / 100000) := by
  exact
    packedTile8192 26675456 26691840 11 955 5164 25 _ _ (427481 / 25000) (1709927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26691840 :
    ThetaLowerSegment 26691840 26708224 (2668500828137 / 100000) (333767587969 / 12500) := by
  exact
    packedTile8192 26691840 26708224 11 959 5166 25 _ _ (341997 / 20000) (427497 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26708224 :
    ThetaLowerSegment 26708224 26724608 (333767587969 / 12500) (1335892884483 / 50000) := by
  exact
    packedTile8192 26708224 26724608 11 962 5168 25 _ _ (1710047 / 100000) (34201 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26724608 :
    ThetaLowerSegment 26724608 26740992 (1335892884483 / 50000) (1336704330729 / 50000) := by
  exact
    packedTile8192 26724608 26740992 11 949 5169 25 _ _ (427527 / 25000) (1710111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26740992 :
    ThetaLowerSegment 26740992 26757376 (1336704330729 / 50000) (534997429489 / 20000) := by
  exact
    packedTile8192 26740992 26757376 11 923 5171 25 _ _ (1710169 / 100000) (427543 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26757376 :
    ThetaLowerSegment 26757376 26773760 (534997429489 / 20000) (535329214303 / 20000) := by
  exact
    packedTile8192 26757376 26773760 11 970 5172 25 _ _ (1710231 / 100000) (855117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26773760 :
    ThetaLowerSegment 26773760 26790144 (535329214303 / 20000) (2678258876871 / 100000) := by
  exact
    packedTile8192 26773760 26790144 11 943 5174 25 _ _ (427573 / 25000) (342059 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26790144 :
    ThetaLowerSegment 26790144 26806528 (2678258876871 / 100000) (334987815763 / 12500) := by
  exact
    packedTile8192 26790144 26806528 11 961 5175 25 _ _ (1710353 / 100000) (427589 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26806528 :
    ThetaLowerSegment 26806528 26822912 (334987815763 / 12500) (6703878413 / 250) := by
  exact
    packedTile8192 26806528 26822912 11 964 5177 25 _ _ (855207 / 50000) (1710417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26822912 :
    ThetaLowerSegment 26822912 26839296 (6703878413 / 250) (5366345791 / 200) := by
  exact
    packedTile8192 26822912 26839296 11 948 5179 25 _ _ (68419 / 4000) (855239 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26839296 :
    ThetaLowerSegment 26839296 26855680 (5366345791 / 200) (671202041979 / 25000) := by
  exact
    packedTile8192 26839296 26855680 11 956 5180 25 _ _ (213817 / 12500) (1710539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26855680 :
    ThetaLowerSegment 26855680 26872064 (671202041979 / 25000) (1343233723503 / 50000) := by
  exact
    packedTile8192 26855680 26872064 11 970 5182 25 _ _ (1710597 / 100000) (8553 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26872064 :
    ThetaLowerSegment 26872064 26888448 (1343233723503 / 50000) (672030413323 / 25000) := by
  exact
    packedTile8192 26872064 26888448 11 967 5183 25 _ _ (855329 / 50000) (1710661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26888448 :
    ThetaLowerSegment 26888448 26904832 (672030413323 / 25000) (2689751968499 / 100000) := by
  exact
    packedTile8192 26888448 26904832 11 953 5185 25 _ _ (1710719 / 100000) (855361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26904832 :
    ThetaLowerSegment 26904832 26921216 (2689751968499 / 100000) (2691421689779 / 100000) := by
  exact
    packedTile8192 26904832 26921216 11 976 5186 25 _ _ (85539 / 5000) (1710783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26921216 :
    ThetaLowerSegment 26921216 26937600 (2691421689779 / 100000) (1346531193149 / 50000) := by
  exact
    packedTile8192 26921216 26937600 11 959 5188 25 _ _ (1710841 / 100000) (427711 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26937600 :
    ThetaLowerSegment 26937600 26953984 (1346531193149 / 50000) (1347342160697 / 50000) := by
  exact
    packedTile8192 26937600 26953984 11 948 5190 25 _ _ (855451 / 50000) (342181 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26953984 :
    ThetaLowerSegment 26953984 26970368 (1347342160697 / 50000) (134818224353 / 5000) := by
  exact
    packedTile8192 26953984 26970368 11 982 5191 25 _ _ (1710963 / 100000) (855483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26970368 :
    ThetaLowerSegment 26970368 26986752 (134818224353 / 5000) (674494923193 / 25000) := by
  exact
    packedTile8192 26970368 26986752 11 944 5193 25 _ _ (1711023 / 100000) (855513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell26986752 :
    ThetaLowerSegment 26986752 27003136 (674494923193 / 25000) (84363465276 / 3125) := by
  exact
    packedTile8192 26986752 27003136 11 965 5194 25 _ _ (427771 / 25000) (1711087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27003136 :
    ThetaLowerSegment 27003136 27019520 (84363465276 / 3125) (1350638505161 / 50000) := by
  exact
    packedTile8192 27003136 27019520 11 962 5196 25 _ _ (342229 / 20000) (427787 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27019520 :
    ThetaLowerSegment 27019520 27035904 (1350638505161 / 50000) (1351453039217 / 50000) := by
  exact
    packedTile8192 27019520 27035904 11 952 5198 25 _ _ (855603 / 50000) (1711209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27035904 :
    ThetaLowerSegment 27035904 27052288 (1351453039217 / 50000) (338064119651 / 12500) := by
  exact
    packedTile8192 27035904 27052288 11 939 5199 25 _ _ (855633 / 50000) (1711269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27052288 :
    ThetaLowerSegment 27052288 27068672 (338064119651 / 12500) (2706167810417 / 100000) := by
  exact
    packedTile8192 27052288 27068672 11 967 5201 25 _ _ (1711327 / 100000) (171133 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27068672 :
    ThetaLowerSegment 27068672 27085056 (2706167810417 / 100000) (676963381653 / 25000) := by
  exact
    packedTile8192 27068672 27085056 11 985 5202 25 _ _ (1711387 / 100000) (171139 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27085056 :
    ThetaLowerSegment 27085056 27101440 (676963381653 / 25000) (677385681447 / 25000) := by
  exact
    packedTile8192 27085056 27101440 11 987 5204 25 _ _ (213931 / 12500) (1711451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27101440 :
    ThetaLowerSegment 27101440 27117824 (677385681447 / 25000) (677786174319 / 25000) := by
  exact
    packedTile8192 27101440 27117824 11 936 5205 25 _ _ (427877 / 25000) (1711511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27117824 :
    ThetaLowerSegment 27117824 27134208 (677786174319 / 25000) (271279807293 / 10000) := by
  exact
    packedTile8192 27117824 27134208 11 966 5207 25 _ _ (1711569 / 100000) (427893 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27134208 :
    ThetaLowerSegment 27134208 27150592 (271279807293 / 10000) (2714460064689 / 100000) := by
  exact
    packedTile8192 27134208 27150592 11 971 5209 25 _ _ (1711629 / 100000) (106977 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27150592 :
    ThetaLowerSegment 27150592 27166976 (2714460064689 / 100000) (2716103286129 / 100000) := by
  exact
    packedTile8192 27150592 27166976 11 960 5210 25 _ _ (1711689 / 100000) (427923 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27166976 :
    ThetaLowerSegment 27166976 27183360 (2716103286129 / 100000) (2717751701379 / 100000) := by
  exact
    packedTile8192 27166976 27183360 11 963 5212 25 _ _ (6847 / 400) (1711753 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27183360 :
    ThetaLowerSegment 27183360 27199744 (2717751701379 / 100000) (2719316295719 / 100000) := by
  exact
    packedTile8192 27183360 27199744 11 914 5213 25 _ _ (171181 / 10000) (1711813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27199744 :
    ThetaLowerSegment 27199744 27216128 (2719316295719 / 100000) (2720961402789 / 100000) := by
  exact
    packedTile8192 27199744 27216128 11 961 5215 25 _ _ (171187 / 10000) (1711873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27216128 :
    ThetaLowerSegment 27216128 27232512 (2720961402789 / 100000) (340327532991 / 12500) := by
  exact
    packedTile8192 27216128 27232512 11 969 5216 25 _ _ (1711931 / 100000) (855967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27232512 :
    ThetaLowerSegment 27232512 27248896 (340327532991 / 12500) (1362102783797 / 50000) := by
  exact
    packedTile8192 27232512 27248896 11 926 5218 25 _ _ (1711991 / 100000) (855997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27248896 :
    ThetaLowerSegment 27248896 27265280 (1362102783797 / 50000) (136292970443 / 5000) := by
  exact
    packedTile8192 27248896 27265280 11 966 5220 25 _ _ (1712051 / 100000) (856027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27265280 :
    ThetaLowerSegment 27265280 27281664 (136292970443 / 5000) (340928462817 / 12500) := by
  exact
    packedTile8192 27265280 27281664 11 916 5221 25 _ _ (1712111 / 100000) (856057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27281664 :
    ThetaLowerSegment 27281664 27298048 (340928462817 / 12500) (545817359247 / 20000) := by
  exact
    packedTile8192 27281664 27298048 11 969 5223 25 _ _ (1712171 / 100000) (856087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27298048 :
    ThetaLowerSegment 27298048 27314432 (545817359247 / 20000) (21845570347 / 800) := by
  exact
    packedTile8192 27298048 27314432 11 940 5224 25 _ _ (1712231 / 100000) (856117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27314432 :
    ThetaLowerSegment 27314432 27330816 (21845570347 / 800) (2732329818989 / 100000) := by
  exact
    packedTile8192 27314432 27330816 11 954 5226 25 _ _ (1712291 / 100000) (856147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27330816 :
    ThetaLowerSegment 27330816 27347200 (2732329818989 / 100000) (170873033681 / 6250) := by
  exact
    packedTile8192 27330816 27347200 11 957 5227 25 _ _ (1712351 / 100000) (856177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27347200 :
    ThetaLowerSegment 27347200 27363584 (170873033681 / 6250) (547125573031 / 20000) := by
  exact
    packedTile8192 27347200 27363584 11 969 5229 25 _ _ (1712411 / 100000) (856207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27363584 :
    ThetaLowerSegment 27363584 27379968 (547125573031 / 20000) (136861451277 / 5000) := by
  exact
    packedTile8192 27363584 27379968 11 935 5231 25 _ _ (1712471 / 100000) (856237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27379968 :
    ThetaLowerSegment 27379968 27396352 (136861451277 / 5000) (2738885043017 / 100000) := by
  exact
    packedTile8192 27379968 27396352 11 967 5232 25 _ _ (1712531 / 100000) (856267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27396352 :
    ThetaLowerSegment 27396352 27412736 (2738885043017 / 100000) (548105141039 / 20000) := by
  exact
    packedTile8192 27396352 27412736 11 958 5234 25 _ _ (1712591 / 100000) (856297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27412736 :
    ThetaLowerSegment 27412736 27429120 (548105141039 / 20000) (548436710079 / 20000) := by
  exact
    packedTile8192 27412736 27429120 11 968 5235 25 _ _ (34253 / 2000) (1712653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27429120 :
    ThetaLowerSegment 27429120 27445504 (548436710079 / 20000) (21951005663 / 800) := by
  exact
    packedTile8192 27429120 27445504 11 988 5237 25 _ _ (171271 / 10000) (1712713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27445504 :
    ThetaLowerSegment 27445504 27461888 (21951005663 / 800) (21963680161 / 800) := by
  exact
    packedTile8192 27445504 27461888 11 925 5238 25 _ _ (171277 / 10000) (1712773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27461888 :
    ThetaLowerSegment 27461888 27478272 (21963680161 / 800) (549420867193 / 20000) := by
  exact
    packedTile8192 27461888 27478272 11 960 5240 25 _ _ (1712829 / 100000) (53526 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27478272 :
    ThetaLowerSegment 27478272 27494656 (549420867193 / 20000) (21989715613 / 800) := by
  exact
    packedTile8192 27478272 27494656 11 940 5241 25 _ _ (1712889 / 100000) (428223 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27494656 :
    ThetaLowerSegment 27494656 27511040 (21989715613 / 800) (2750348604971 / 100000) := by
  exact
    packedTile8192 27494656 27511040 11 954 5243 25 _ _ (1712949 / 100000) (214119 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27511040 :
    ThetaLowerSegment 27511040 27527424 (2750348604971 / 100000) (2752011935739 / 100000) := by
  exact
    packedTile8192 27511040 27527424 11 971 5245 25 _ _ (107063 / 6250) (1713011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27527424 :
    ThetaLowerSegment 27527424 27543808 (2752011935739 / 100000) (2753658194087 / 100000) := by
  exact
    packedTile8192 27527424 27543808 11 961 5246 25 _ _ (428267 / 25000) (1713071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27543808 :
    ThetaLowerSegment 27543808 27560192 (2753658194087 / 100000) (275528395161 / 10000) := by
  exact
    packedTile8192 27543808 27560192 11 949 5248 25 _ _ (1713127 / 100000) (171313 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27560192 :
    ThetaLowerSegment 27560192 27576576 (275528395161 / 10000) (2756923471569 / 100000) := by
  exact
    packedTile8192 27560192 27576576 11 957 5249 25 _ _ (1713187 / 100000) (171319 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27576576 :
    ThetaLowerSegment 27576576 27592960 (2756923471569 / 100000) (2758607592387 / 100000) := by
  exact
    packedTile8192 27576576 27592960 11 983 5251 25 _ _ (856623 / 50000) (1713249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27592960 :
    ThetaLowerSegment 27592960 27609344 (2758607592387 / 100000) (2760320898387 / 100000) := by
  exact
    packedTile8192 27592960 27609344 11 1000 5252 25 _ _ (856653 / 50000) (1713309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27609344 :
    ThetaLowerSegment 27609344 27625728 (2760320898387 / 100000) (86309340861 / 3125) := by
  exact
    packedTile8192 27609344 27625728 11 921 5254 25 _ _ (342673 / 20000) (214171 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27625728 :
    ThetaLowerSegment 27625728 27642112 (86309340861 / 3125) (6908932307 / 250) := by
  exact
    packedTile8192 27625728 27642112 11 977 5256 25 _ _ (107089 / 6250) (1713427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27642112 :
    ThetaLowerSegment 27642112 27658496 (6908932307 / 250) (345648378091 / 12500) := by
  exact
    packedTile8192 27642112 27658496 11 942 5257 25 _ _ (428371 / 25000) (1713487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27658496 :
    ThetaLowerSegment 27658496 27674880 (345648378091 / 12500) (2766789187433 / 100000) := by
  exact
    packedTile8192 27658496 27674880 11 935 5259 25 _ _ (1713543 / 100000) (856773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27674880 :
    ThetaLowerSegment 27674880 27691264 (2766789187433 / 100000) (2768391405303 / 100000) := by
  exact
    packedTile8192 27674880 27691264 11 935 5260 25 _ _ (856801 / 50000) (342721 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27691264 :
    ThetaLowerSegment 27691264 27707648 (2768391405303 / 100000) (346259063343 / 12500) := by
  exact
    packedTile8192 27691264 27707648 11 981 5262 25 _ _ (1713661 / 100000) (53552 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27707648 :
    ThetaLowerSegment 27707648 27724032 (346259063343 / 12500) (86614624377 / 3125) := by
  exact
    packedTile8192 27707648 27724032 11 931 5263 25 _ _ (42843 / 2500) (1713723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27724032 :
    ThetaLowerSegment 27724032 27740416 (86614624377 / 3125) (693357008031 / 25000) := by
  exact
    packedTile8192 27724032 27740416 11 1027 5265 25 _ _ (85689 / 5000) (1713783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27740416 :
    ThetaLowerSegment 27740416 27756800 (693357008031 / 25000) (138752294807 / 5000) := by
  exact
    packedTile8192 27740416 27756800 11 944 5266 25 _ _ (1713839 / 100000) (856921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27756800 :
    ThetaLowerSegment 27756800 27773184 (138752294807 / 5000) (1388327623181 / 50000) := by
  exact
    packedTile8192 27756800 27773184 11 939 5268 25 _ _ (856949 / 50000) (1713901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27773184 :
    ThetaLowerSegment 27773184 27789568 (1388327623181 / 50000) (347285438189 / 12500) := by
  exact
    packedTile8192 27773184 27789568 11 950 5270 25 _ _ (1713957 / 100000) (42849 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27789568 :
    ThetaLowerSegment 27789568 27805952 (347285438189 / 12500) (347488334833 / 12500) := by
  exact
    packedTile8192 27789568 27805952 11 947 5271 25 _ _ (53563 / 3125) (1714019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27805952 :
    ThetaLowerSegment 27805952 27822336 (347488334833 / 12500) (2781547048439 / 100000) := by
  exact
    packedTile8192 27805952 27822336 11 957 5273 25 _ _ (68563 / 4000) (857039 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27822336 :
    ThetaLowerSegment 27822336 27838720 (2781547048439 / 100000) (86973322954 / 3125) := by
  exact
    packedTile8192 27822336 27838720 11 933 5274 25 _ _ (1714133 / 100000) (214267 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27838720 :
    ThetaLowerSegment 27838720 27855104 (86973322954 / 3125) (17404585477 / 625) := by
  exact
    packedTile8192 27838720 27855104 11 926 5276 25 _ _ (107137 / 6250) (342839 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27855104 :
    ThetaLowerSegment 27855104 27871488 (17404585477 / 625) (2786398214041 / 100000) := by
  exact
    packedTile8192 27855104 27871488 11 971 5277 25 _ _ (1714251 / 100000) (857127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27871488 :
    ThetaLowerSegment 27871488 27887872 (2786398214041 / 100000) (2788050808881 / 100000) := by
  exact
    packedTile8192 27871488 27887872 11 964 5279 25 _ _ (171431 / 10000) (1714313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27887872 :
    ThetaLowerSegment 27887872 27904256 (2788050808881 / 100000) (2789717175549 / 100000) := by
  exact
    packedTile8192 27887872 27904256 11 972 5280 25 _ _ (1714369 / 100000) (428593 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27904256 :
    ThetaLowerSegment 27904256 27920640 (2789717175549 / 100000) (1395697799791 / 50000) := by
  exact
    packedTile8192 27904256 27920640 11 979 5282 25 _ _ (1714427 / 100000) (171443 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27920640 :
    ThetaLowerSegment 27920640 27937024 (1395697799791 / 50000) (1396515609613 / 50000) := by
  exact
    packedTile8192 27920640 27937024 11 954 5283 25 _ _ (857243 / 50000) (1714489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27937024 :
    ThetaLowerSegment 27937024 27953408 (1396515609613 / 50000) (2794658322431 / 100000) := by
  exact
    packedTile8192 27937024 27953408 11 949 5285 25 _ _ (342909 / 20000) (428637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27953408 :
    ThetaLowerSegment 27953408 27969792 (2794658322431 / 100000) (174771057423 / 6250) := by
  exact
    packedTile8192 27953408 27969792 11 979 5287 25 _ _ (1714603 / 100000) (857303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27969792 :
    ThetaLowerSegment 27969792 27986176 (174771057423 / 6250) (1398982066503 / 50000) := by
  exact
    packedTile8192 27969792 27986176 11 949 5288 25 _ _ (857331 / 50000) (342933 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell27986176 :
    ThetaLowerSegment 27986176 28002560 (1398982066503 / 50000) (559911421763 / 20000) := by
  exact
    packedTile8192 27986176 28002560 11 929 5290 25 _ _ (1714721 / 100000) (428681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28002560 :
    ThetaLowerSegment 28002560 28018944 (559911421763 / 20000) (140061450917 / 5000) := by
  exact
    packedTile8192 28002560 28018944 11 975 5291 25 _ _ (1714779 / 100000) (857391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28018944 :
    ThetaLowerSegment 28018944 28035328 (140061450917 / 5000) (70073167699 / 2500) := by
  exact
    packedTile8192 28018944 28035328 11 990 5293 25 _ _ (857419 / 50000) (1714841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28035328 :
    ThetaLowerSegment 28035328 28051712 (70073167699 / 2500) (350568839309 / 12500) := by
  exact
    packedTile8192 28035328 28051712 11 947 5294 25 _ _ (107181 / 6250) (1714899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28051712 :
    ThetaLowerSegment 28051712 28068096 (350568839309 / 12500) (1403055661761 / 50000) := by
  exact
    packedTile8192 28051712 28068096 11 910 5296 25 _ _ (342991 / 20000) (857479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28068096 :
    ThetaLowerSegment 28068096 28084480 (1403055661761 / 50000) (701947151559 / 25000) := by
  exact
    packedTile8192 28068096 28084480 11 978 5297 25 _ _ (1715013 / 100000) (214377 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28084480 :
    ThetaLowerSegment 28084480 28100864 (701947151559 / 25000) (561890102007 / 20000) := by
  exact
    packedTile8192 28084480 28100864 11 969 5299 25 _ _ (1715071 / 100000) (857537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28100864 :
    ThetaLowerSegment 28100864 28117248 (561890102007 / 20000) (562207058031 / 20000) := by
  exact
    packedTile8192 28100864 28117248 11 924 5301 25 _ _ (171513 / 10000) (1715133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28117248 :
    ThetaLowerSegment 28117248 28133632 (562207058031 / 20000) (2812663003567 / 100000) := by
  exact
    packedTile8192 28117248 28133632 11 949 5302 25 _ _ (428797 / 25000) (1715191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28133632 :
    ThetaLowerSegment 28133632 28150016 (2812663003567 / 100000) (2814350805631 / 100000) := by
  exact
    packedTile8192 28133632 28150016 11 984 5304 25 _ _ (857623 / 50000) (1715249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28150016 :
    ThetaLowerSegment 28150016 28166400 (2814350805631 / 100000) (2815951184263 / 100000) := by
  exact
    packedTile8192 28150016 28166400 11 933 5305 25 _ _ (214413 / 12500) (1715307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28166400 :
    ThetaLowerSegment 28166400 28182784 (2815951184263 / 100000) (704392192893 / 25000) := by
  exact
    packedTile8192 28166400 28182784 11 943 5307 25 _ _ (1715363 / 100000) (857683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28182784 :
    ThetaLowerSegment 28182784 28199168 (704392192893 / 25000) (2819155535997 / 100000) := by
  exact
    packedTile8192 28182784 28199168 11 925 5308 25 _ _ (1715421 / 100000) (53607 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28199168 :
    ThetaLowerSegment 28199168 28215552 (2819155535997 / 100000) (2820846998291 / 100000) := by
  exact
    packedTile8192 28199168 28215552 11 986 5310 25 _ _ (1715479 / 100000) (857741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28215552 :
    ThetaLowerSegment 28215552 28231936 (2820846998291 / 100000) (2822517931329 / 100000) := by
  exact
    packedTile8192 28215552 28231936 11 974 5311 25 _ _ (1715537 / 100000) (85777 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28231936 :
    ThetaLowerSegment 28231936 28248320 (2822517931329 / 100000) (2824168333719 / 100000) := by
  exact
    packedTile8192 28231936 28248320 11 962 5313 25 _ _ (343119 / 20000) (857799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28248320 :
    ThetaLowerSegment 28248320 28264704 (2824168333719 / 100000) (88306140263 / 3125) := by
  exact
    packedTile8192 28248320 28264704 11 949 5314 25 _ _ (1715653 / 100000) (214457 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28264704 :
    ThetaLowerSegment 28264704 28281088 (88306140263 / 3125) (2827465875219 / 100000) := by
  exact
    packedTile8192 28264704 28281088 11 973 5316 25 _ _ (1715711 / 100000) (857857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28281088 :
    ThetaLowerSegment 28281088 28297472 (2827465875219 / 100000) (113165481369 / 4000) := by
  exact
    packedTile8192 28281088 28297472 11 974 5317 25 _ _ (1715769 / 100000) (428943 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28297472 :
    ThetaLowerSegment 28297472 28313856 (113165481369 / 4000) (566156845629 / 20000) := by
  exact
    packedTile8192 28297472 28313856 11 960 5319 25 _ _ (1715827 / 100000) (171583 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28313856 :
    ThetaLowerSegment 28313856 28330240 (566156845629 / 20000) (56648389331 / 2000) := by
  exact
    packedTile8192 28313856 28330240 11 953 5321 25 _ _ (343177 / 20000) (107243 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28330240 :
    ThetaLowerSegment 28330240 28346624 (56648389331 / 2000) (2834047896457 / 100000) := by
  exact
    packedTile8192 28330240 28346624 11 949 5322 25 _ _ (1715943 / 100000) (857973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28346624 :
    ThetaLowerSegment 28346624 28363008 (2834047896457 / 100000) (2835643776457 / 100000) := by
  exact
    packedTile8192 28346624 28363008 11 930 5324 25 _ _ (429 / 25) (1716003 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28363008 :
    ThetaLowerSegment 28363008 28379392 (2835643776457 / 100000) (2837274031557 / 100000) := by
  exact
    packedTile8192 28363008 28379392 11 950 5325 25 _ _ (858029 / 50000) (1716061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28379392 :
    ThetaLowerSegment 28379392 28395776 (2837274031557 / 100000) (2838919786801 / 100000) := by
  exact
    packedTile8192 28379392 28395776 11 959 5327 25 _ _ (429029 / 25000) (1716119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28395776 :
    ThetaLowerSegment 28395776 28412160 (2838919786801 / 100000) (2840527841839 / 100000) := by
  exact
    packedTile8192 28395776 28412160 11 937 5328 25 _ _ (858087 / 50000) (1716177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28412160 :
    ThetaLowerSegment 28412160 28428544 (2840527841839 / 100000) (113686742347 / 4000) := by
  exact
    packedTile8192 28412160 28428544 11 956 5330 25 _ _ (1716231 / 100000) (858117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28428544 :
    ThetaLowerSegment 28428544 28444928 (113686742347 / 4000) (1421924402803 / 50000) := by
  exact
    packedTile8192 28428544 28444928 11 979 5331 25 _ _ (1716289 / 100000) (429073 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28444928 :
    ThetaLowerSegment 28444928 28461312 (1421924402803 / 50000) (2845467320827 / 100000) := by
  exact
    packedTile8192 28444928 28461312 11 943 5333 25 _ _ (1716347 / 100000) (34327 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28461312 :
    ThetaLowerSegment 28461312 28477696 (2845467320827 / 100000) (2847060143739 / 100000) := by
  exact
    packedTile8192 28461312 28477696 11 928 5334 25 _ _ (429101 / 25000) (1716407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28477696 :
    ThetaLowerSegment 28477696 28494080 (2847060143739 / 100000) (2848718246031 / 100000) := by
  exact
    packedTile8192 28477696 28494080 11 966 5336 25 _ _ (858231 / 50000) (343293 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28494080 :
    ThetaLowerSegment 28494080 28510464 (2848718246031 / 100000) (57008729631 / 2000) := by
  exact
    packedTile8192 28494080 28510464 11 1001 5337 25 _ _ (1716519 / 100000) (858261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28510464 :
    ThetaLowerSegment 28510464 28526848 (57008729631 / 2000) (356509262001 / 12500) := by
  exact
    packedTile8192 28510464 28526848 11 954 5339 25 _ _ (1716577 / 100000) (85829 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28526848 :
    ThetaLowerSegment 28526848 28543232 (356509262001 / 12500) (1426841291033 / 50000) := by
  exact
    packedTile8192 28526848 28543232 11 937 5341 25 _ _ (858317 / 50000) (1716637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28543232 :
    ThetaLowerSegment 28543232 28559616 (1426841291033 / 50000) (1427672169961 / 50000) := by
  exact
    packedTile8192 28543232 28559616 11 968 5342 25 _ _ (429173 / 25000) (343339 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28559616 :
    ThetaLowerSegment 28559616 28576000 (1427672169961 / 50000) (89279618234 / 3125) := by
  exact
    packedTile8192 28559616 28576000 11 934 5344 25 _ _ (1716749 / 100000) (107297 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28576000 :
    ThetaLowerSegment 28576000 28592384 (89279618234 / 3125) (1429314268281 / 50000) := by
  exact
    packedTile8192 28576000 28592384 11 979 5345 25 _ _ (858403 / 50000) (1716809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28592384 :
    ThetaLowerSegment 28592384 28608768 (1429314268281 / 50000) (1430113468473 / 50000) := by
  exact
    packedTile8192 28592384 28608768 11 931 5347 25 _ _ (53652 / 3125) (1716867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28608768 :
    ThetaLowerSegment 28608768 28625152 (1430113468473 / 50000) (2861883765711 / 100000) := by
  exact
    packedTile8192 28608768 28625152 11 965 5348 25 _ _ (1716921 / 100000) (429231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28625152 :
    ThetaLowerSegment 28625152 28641536 (2861883765711 / 100000) (2863525196679 / 100000) := by
  exact
    packedTile8192 28625152 28641536 11 956 5350 25 _ _ (858489 / 50000) (1716981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28641536 :
    ThetaLowerSegment 28641536 28657920 (2863525196679 / 100000) (2865173550279 / 100000) := by
  exact
    packedTile8192 28641536 28657920 11 960 5351 25 _ _ (343407 / 20000) (858519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28657920 :
    ThetaLowerSegment 28657920 28674304 (2865173550279 / 100000) (2866828827931 / 100000) := by
  exact
    packedTile8192 28657920 28674304 11 964 5353 25 _ _ (1717093 / 100000) (214637 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28674304 :
    ThetaLowerSegment 28674304 28690688 (2866828827931 / 100000) (2868484160531 / 100000) := by
  exact
    packedTile8192 28674304 28690688 11 964 5354 25 _ _ (34343 / 2000) (1717153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28690688 :
    ThetaLowerSegment 28690688 28707072 (2868484160531 / 100000) (2870039950073 / 100000) := by
  exact
    packedTile8192 28690688 28707072 11 906 5356 25 _ _ (1717207 / 100000) (171721 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28707072 :
    ThetaLowerSegment 28707072 28723456 (2870039950073 / 100000) (574335300533 / 20000) := by
  exact
    packedTile8192 28707072 28723456 11 953 5357 25 _ _ (107329 / 6250) (1717267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28723456 :
    ThetaLowerSegment 28723456 28739840 (574335300533 / 20000) (2873352607961 / 100000) := by
  exact
    packedTile8192 28723456 28739840 11 976 5359 25 _ _ (1717321 / 100000) (429331 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28739840 :
    ThetaLowerSegment 28739840 28756224 (2873352607961 / 100000) (2874987551817 / 100000) := by
  exact
    packedTile8192 28739840 28756224 11 952 5360 25 _ _ (858689 / 50000) (1717381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28756224 :
    ThetaLowerSegment 28756224 28772608 (2874987551817 / 100000) (1438279502421 / 50000) := by
  exact
    packedTile8192 28756224 28772608 11 915 5362 25 _ _ (343487 / 20000) (858719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28772608 :
    ThetaLowerSegment 28772608 28788992 (1438279502421 / 50000) (1439099604851 / 50000) := by
  exact
    packedTile8192 28772608 28788992 11 955 5364 25 _ _ (429373 / 25000) (343499 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28788992 :
    ThetaLowerSegment 28788992 28805376 (1439099604851 / 50000) (575968580819 / 20000) := by
  exact
    packedTile8192 28788992 28805376 11 957 5365 25 _ _ (1717549 / 100000) (107347 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28805376 :
    ThetaLowerSegment 28805376 28821760 (575968580819 / 20000) (2881407643161 / 100000) := by
  exact
    packedTile8192 28805376 28821760 11 911 5367 25 _ _ (858803 / 50000) (1717609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28821760 :
    ThetaLowerSegment 28821760 28838144 (2881407643161 / 100000) (115323500703 / 4000) := by
  exact
    packedTile8192 28821760 28838144 11 978 5368 25 _ _ (1717663 / 100000) (858833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28838144 :
    ThetaLowerSegment 28838144 28854528 (115323500703 / 4000) (576947305563 / 20000) := by
  exact
    packedTile8192 28838144 28854528 11 960 5370 25 _ _ (1717719 / 100000) (858861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28854528 :
    ThetaLowerSegment 28854528 28870912 (576947305563 / 20000) (2886371850567 / 100000) := by
  exact
    packedTile8192 28854528 28870912 11 952 5371 25 _ _ (107361 / 6250) (1717779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28870912 :
    ThetaLowerSegment 28870912 28887296 (2886371850567 / 100000) (577602819783 / 20000) := by
  exact
    packedTile8192 28870912 28887296 11 956 5373 25 _ _ (1717833 / 100000) (429459 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28887296 :
    ThetaLowerSegment 28887296 28903680 (577602819783 / 20000) (577933685397 / 20000) := by
  exact
    packedTile8192 28887296 28903680 11 963 5374 25 _ _ (171789 / 10000) (1717893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28903680 :
    ThetaLowerSegment 28903680 28920064 (577933685397 / 20000) (2891322808983 / 100000) := by
  exact
    packedTile8192 28903680 28920064 11 963 5376 25 _ _ (858973 / 50000) (1717949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28920064 :
    ThetaLowerSegment 28920064 28936448 (2891322808983 / 100000) (723246029471 / 25000) := by
  exact
    packedTile8192 28920064 28936448 11 967 5377 25 _ _ (1718003 / 100000) (859003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28936448 :
    ThetaLowerSegment 28936448 28952832 (723246029471 / 25000) (361820806393 / 12500) := by
  exact
    packedTile8192 28936448 28952832 11 921 5379 25 _ _ (85903 / 5000) (1718063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28952832 :
    ThetaLowerSegment 28952832 28969216 (361820806393 / 12500) (724043222401 / 25000) := by
  exact
    packedTile8192 28952832 28969216 11 935 5380 25 _ _ (429529 / 25000) (1718119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28969216 :
    ThetaLowerSegment 28969216 28985600 (724043222401 / 25000) (1448916322361 / 50000) := by
  exact
    packedTile8192 28969216 28985600 11 966 5382 25 _ _ (1718173 / 100000) (53693 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell28985600 :
    ThetaLowerSegment 28985600 29001984 (1448916322361 / 50000) (2899466680501 / 100000) := by
  exact
    packedTile8192 28985600 29001984 11 951 5383 25 _ _ (1718229 / 100000) (214779 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29001984 :
    ThetaLowerSegment 29001984 29018368 (2899466680501 / 100000) (2901119671633 / 100000) := by
  exact
    packedTile8192 29001984 29018368 11 962 5385 25 _ _ (859143 / 50000) (1718289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29018368 :
    ThetaLowerSegment 29018368 29034752 (2901119671633 / 100000) (2902750378191 / 100000) := by
  exact
    packedTile8192 29018368 29034752 11 949 5386 25 _ _ (859171 / 50000) (343669 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29034752 :
    ThetaLowerSegment 29034752 29051136 (2902750378191 / 100000) (2904396604433 / 100000) := by
  exact
    packedTile8192 29034752 29051136 11 958 5388 25 _ _ (1718399 / 100000) (859201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29051136 :
    ThetaLowerSegment 29051136 29067520 (2904396604433 / 100000) (2905998204493 / 100000) := by
  exact
    packedTile8192 29051136 29067520 11 932 5389 25 _ _ (343691 / 20000) (859229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29067520 :
    ThetaLowerSegment 29067520 29083904 (2905998204493 / 100000) (116305987781 / 4000) := by
  exact
    packedTile8192 29067520 29083904 11 961 5391 25 _ _ (107407 / 6250) (343703 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29083904 :
    ThetaLowerSegment 29083904 29100288 (116305987781 / 4000) (2909272022717 / 100000) := by
  exact
    packedTile8192 29083904 29100288 11 944 5392 25 _ _ (214821 / 12500) (1718571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29100288 :
    ThetaLowerSegment 29100288 29116672 (2909272022717 / 100000) (2910932213501 / 100000) := by
  exact
    packedTile8192 29100288 29116672 11 966 5394 25 _ _ (53707 / 3125) (1718627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29116672 :
    ThetaLowerSegment 29116672 29133056 (2910932213501 / 100000) (1456271308799 / 50000) := by
  exact
    packedTile8192 29116672 29133056 11 937 5395 25 _ _ (1718681 / 100000) (429671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29133056 :
    ThetaLowerSegment 29133056 29149440 (1456271308799 / 50000) (7285421357 / 250) := by
  exact
    packedTile8192 29133056 29149440 11 946 5397 25 _ _ (1718737 / 100000) (85937 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29149440 :
    ThetaLowerSegment 29149440 29165824 (7285421357 / 250) (1457890385317 / 50000) := by
  exact
    packedTile8192 29149440 29165824 11 938 5399 25 _ _ (1718793 / 100000) (429699 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29165824 :
    ThetaLowerSegment 29165824 29182208 (1457890385317 / 50000) (291740336409 / 10000) := by
  exact
    packedTile8192 29165824 29182208 11 944 5400 25 _ _ (1718849 / 100000) (429713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29182208 :
    ThetaLowerSegment 29182208 29198592 (291740336409 / 10000) (116762621809 / 4000) := by
  exact
    packedTile8192 29182208 29198592 11 967 5402 25 _ _ (343781 / 20000) (429727 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29198592 :
    ThetaLowerSegment 29198592 29214976 (116762621809 / 4000) (2920731219403 / 100000) := by
  exact
    packedTile8192 29198592 29214976 11 969 5403 25 _ _ (859481 / 50000) (343793 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29214976 :
    ThetaLowerSegment 29214976 29231360 (2920731219403 / 100000) (2922298963819 / 100000) := by
  exact
    packedTile8192 29214976 29231360 11 912 5405 25 _ _ (859509 / 50000) (1719021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29231360 :
    ThetaLowerSegment 29231360 29247744 (2922298963819 / 100000) (2923894264491 / 100000) := by
  exact
    packedTile8192 29231360 29247744 11 928 5406 25 _ _ (859537 / 50000) (1719077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29247744 :
    ThetaLowerSegment 29247744 29264128 (2923894264491 / 100000) (2925546348421 / 100000) := by
  exact
    packedTile8192 29247744 29264128 11 961 5408 25 _ _ (171913 / 10000) (1719133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29264128 :
    ThetaLowerSegment 29264128 29280512 (2925546348421 / 100000) (2927198486167 / 100000) := by
  exact
    packedTile8192 29264128 29280512 11 961 5409 25 _ _ (859593 / 50000) (1719189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29280512 :
    ThetaLowerSegment 29280512 29296896 (2927198486167 / 100000) (2928895378021 / 100000) := by
  exact
    packedTile8192 29280512 29296896 11 987 5411 25 _ _ (859621 / 50000) (343849 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29296896 :
    ThetaLowerSegment 29296896 29313280 (2928895378021 / 100000) (2930554500591 / 100000) := by
  exact
    packedTile8192 29296896 29313280 11 965 5412 25 _ _ (859649 / 50000) (1719301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29313280 :
    ThetaLowerSegment 29313280 29329664 (2930554500591 / 100000) (2932187886891 / 100000) := by
  exact
    packedTile8192 29313280 29329664 11 950 5414 25 _ _ (859677 / 50000) (1719357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29329664 :
    ThetaLowerSegment 29329664 29346048 (2932187886891 / 100000) (293385743303 / 10000) := by
  exact
    packedTile8192 29329664 29346048 11 971 5415 25 _ _ (1719409 / 100000) (429853 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29346048 :
    ThetaLowerSegment 29346048 29362432 (293385743303 / 10000) (36694410319 / 1250) := by
  exact
    packedTile8192 29346048 29362432 11 986 5417 25 _ _ (343893 / 20000) (429867 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29362432 :
    ThetaLowerSegment 29362432 29378816 (36694410319 / 1250) (2937215602327 / 100000) := by
  exact
    packedTile8192 29362432 29378816 11 967 5418 25 _ _ (1719521 / 100000) (429881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29378816 :
    ThetaLowerSegment 29378816 29395200 (2937215602327 / 100000) (2938794174013 / 100000) := by
  exact
    packedTile8192 29378816 29395200 11 918 5420 25 _ _ (1719577 / 100000) (85979 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29395200 :
    ThetaLowerSegment 29395200 29411584 (2938794174013 / 100000) (2940445021693 / 100000) := by
  exact
    packedTile8192 29395200 29411584 11 960 5421 25 _ _ (1719633 / 100000) (429909 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29411584 :
    ThetaLowerSegment 29411584 29427968 (2940445021693 / 100000) (2941985862141 / 100000) := by
  exact
    packedTile8192 29411584 29427968 11 896 5423 25 _ _ (214961 / 12500) (1719691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29427968 :
    ThetaLowerSegment 29427968 29444352 (2941985862141 / 100000) (2943614459709 / 100000) := by
  exact
    packedTile8192 29427968 29444352 11 947 5424 25 _ _ (53742 / 3125) (1719747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29444352 :
    ThetaLowerSegment 29444352 29460736 (2943614459709 / 100000) (2945236231109 / 100000) := by
  exact
    packedTile8192 29444352 29460736 11 943 5426 25 _ _ (8599 / 500) (1719803 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29460736 :
    ThetaLowerSegment 29460736 29477120 (2945236231109 / 100000) (2946883852199 / 100000) := by
  exact
    packedTile8192 29460736 29477120 11 958 5427 25 _ _ (343971 / 20000) (859929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29477120 :
    ThetaLowerSegment 29477120 29493504 (2946883852199 / 100000) (92141663964 / 3125) := by
  exact
    packedTile8192 29477120 29493504 11 959 5429 25 _ _ (1719911 / 100000) (859957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29493504 :
    ThetaLowerSegment 29493504 29509888 (92141663964 / 3125) (2950141415993 / 100000) := by
  exact
    packedTile8192 29493504 29509888 11 935 5430 25 _ _ (1719967 / 100000) (171997 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29509888 :
    ThetaLowerSegment 29509888 29526272 (2950141415993 / 100000) (590362311471 / 20000) := by
  exact
    packedTile8192 29509888 29526272 11 971 5432 25 _ _ (860011 / 50000) (68801 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29526272 :
    ThetaLowerSegment 29526272 29542656 (590362311471 / 20000) (2953464552313 / 100000) := by
  exact
    packedTile8192 29526272 29542656 11 961 5433 25 _ _ (860039 / 50000) (1720081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29542656 :
    ThetaLowerSegment 29542656 29559040 (2953464552313 / 100000) (591017671573 / 20000) := by
  exact
    packedTile8192 29542656 29559040 11 944 5435 25 _ _ (1720133 / 100000) (215017 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29559040 :
    ThetaLowerSegment 29559040 29575424 (591017671573 / 20000) (2956701895147 / 100000) := by
  exact
    packedTile8192 29559040 29575424 11 938 5436 25 _ _ (1720189 / 100000) (53756 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29575424 :
    ThetaLowerSegment 29575424 29591808 (2956701895147 / 100000) (2958344728167 / 100000) := by
  exact
    packedTile8192 29575424 29591808 11 955 5438 25 _ _ (430061 / 25000) (1720247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29591808 :
    ThetaLowerSegment 29591808 29608192 (2958344728167 / 100000) (2959996215207 / 100000) := by
  exact
    packedTile8192 29591808 29608192 11 960 5439 25 _ _ (1720299 / 100000) (860151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29608192 :
    ThetaLowerSegment 29608192 29624576 (2959996215207 / 100000) (92552513836 / 3125) := by
  exact
    packedTile8192 29608192 29624576 11 979 5441 25 _ _ (344071 / 20000) (860179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29624576 :
    ThetaLowerSegment 29624576 29640960 (92552513836 / 3125) (1481637631411 / 50000) := by
  exact
    packedTile8192 29624576 29640960 11 927 5442 25 _ _ (172041 / 10000) (1720413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29640960 :
    ThetaLowerSegment 29640960 29657344 (1481637631411 / 50000) (1482463454611 / 50000) := by
  exact
    packedTile8192 29640960 29657344 11 960 5444 25 _ _ (344093 / 20000) (430117 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29657344 :
    ThetaLowerSegment 29657344 29673728 (1482463454611 / 50000) (1483292745733 / 50000) := by
  exact
    packedTile8192 29657344 29673728 11 964 5445 25 _ _ (1720521 / 100000) (430131 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29673728 :
    ThetaLowerSegment 29673728 29690112 (1483292745733 / 50000) (1484099695877 / 50000) := by
  exact
    packedTile8192 29673728 29690112 11 938 5447 25 _ _ (53768 / 3125) (1720579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29690112 :
    ThetaLowerSegment 29690112 29706496 (1484099695877 / 50000) (2969873565717 / 100000) := by
  exact
    packedTile8192 29690112 29706496 11 973 5448 25 _ _ (1720631 / 100000) (860317 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29706496 :
    ThetaLowerSegment 29706496 29722880 (2969873565717 / 100000) (2971577044857 / 100000) := by
  exact
    packedTile8192 29706496 29722880 11 990 5450 25 _ _ (860343 / 50000) (1720689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29722880 :
    ThetaLowerSegment 29722880 29739264 (2971577044857 / 100000) (92913136016 / 3125) := by
  exact
    packedTile8192 29722880 29739264 11 955 5451 25 _ _ (1720741 / 100000) (215093 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29739264 :
    ThetaLowerSegment 29739264 29755648 (92913136016 / 3125) (92962178702 / 3125) := by
  exact
    packedTile8192 29739264 29755648 11 912 5453 25 _ _ (430199 / 25000) (1720799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29755648 :
    ThetaLowerSegment 29755648 29772032 (92962178702 / 3125) (372046612673 / 12500) := by
  exact
    packedTile8192 29755648 29772032 11 920 5454 25 _ _ (1720851 / 100000) (860427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29772032 :
    ThetaLowerSegment 29772032 29788416 (372046612673 / 12500) (297800948299 / 10000) := by
  exact
    packedTile8192 29772032 29788416 11 951 5456 25 _ _ (860453 / 50000) (1720909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29788416 :
    ThetaLowerSegment 29788416 29804800 (297800948299 / 10000) (744911529463 / 25000) := by
  exact
    packedTile8192 29788416 29804800 11 951 5457 25 _ _ (860481 / 50000) (344193 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29804800 :
    ThetaLowerSegment 29804800 29821184 (744911529463 / 25000) (2981251826713 / 100000) := by
  exact
    packedTile8192 29804800 29821184 11 933 5459 25 _ _ (1721017 / 100000) (86051 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29821184 :
    ThetaLowerSegment 29821184 29837568 (2981251826713 / 100000) (1491444282617 / 50000) := by
  exact
    packedTile8192 29821184 29837568 11 951 5460 25 _ _ (1721071 / 100000) (860537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29837568 :
    ThetaLowerSegment 29837568 29853952 (1491444282617 / 50000) (298456838421 / 10000) := by
  exact
    packedTile8192 29837568 29853952 11 976 5462 25 _ _ (860563 / 50000) (1721129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29853952 :
    ThetaLowerSegment 29853952 29870336 (298456838421 / 10000) (2986277516943 / 100000) := by
  exact
    packedTile8192 29853952 29870336 11 993 5463 25 _ _ (1721181 / 100000) (53787 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29870336 :
    ThetaLowerSegment 29870336 29886720 (2986277516943 / 100000) (2987938509683 / 100000) := by
  exact
    packedTile8192 29870336 29886720 11 965 5465 25 _ _ (430309 / 25000) (1721239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29886720 :
    ThetaLowerSegment 29886720 29903104 (2987938509683 / 100000) (597915435743 / 20000) := by
  exact
    packedTile8192 29886720 29903104 11 952 5466 25 _ _ (1721291 / 100000) (860647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29903104 :
    ThetaLowerSegment 29903104 29919488 (597915435743 / 20000) (2991200407993 / 100000) := by
  exact
    packedTile8192 29903104 29919488 11 943 5468 25 _ _ (860673 / 50000) (1721349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29919488 :
    ThetaLowerSegment 29919488 29935872 (2991200407993 / 100000) (1496430779979 / 50000) := by
  exact
    packedTile8192 29919488 29935872 11 965 5469 25 _ _ (1721401 / 100000) (430351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29935872 :
    ThetaLowerSegment 29935872 29952256 (1496430779979 / 50000) (1497288064569 / 50000) := by
  exact
    packedTile8192 29935872 29952256 11 996 5471 25 _ _ (344291 / 20000) (860729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29952256 :
    ThetaLowerSegment 29952256 29968640 (1497288064569 / 50000) (1498090288229 / 50000) := by
  exact
    packedTile8192 29952256 29968640 11 932 5472 25 _ _ (172151 / 10000) (1721513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29968640 :
    ThetaLowerSegment 29968640 29985024 (1498090288229 / 50000) (1498916639429 / 50000) := by
  exact
    packedTile8192 29968640 29985024 11 960 5474 25 _ _ (344313 / 20000) (53799 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell29985024 :
    ThetaLowerSegment 29985024 30001408 (1498916639429 / 50000) (2999498084431 / 100000) := by
  exact
    packedTile8192 29985024 30001408 11 967 5475 25 _ _ (1721619 / 100000) (860811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30001408 :
    ThetaLowerSegment 30001408 30017792 (2999498084431 / 100000) (3001192211647 / 100000) := by
  exact
    packedTile8192 30001408 30017792 11 984 5477 25 _ _ (860837 / 50000) (1721677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30017792 :
    ThetaLowerSegment 30017792 30034176 (3001192211647 / 100000) (1501407901047 / 50000) := by
  exact
    packedTile8192 30017792 30034176 11 943 5478 25 _ _ (1721729 / 100000) (430433 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30034176 :
    ThetaLowerSegment 30034176 30050560 (1501407901047 / 50000) (751111152203 / 25000) := by
  exact
    packedTile8192 30034176 30050560 11 946 5480 25 _ _ (1721783 / 100000) (860893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30050560 :
    ThetaLowerSegment 30050560 30066944 (751111152203 / 25000) (375762627121 / 12500) := by
  exact
    packedTile8192 30050560 30066944 11 962 5481 25 _ _ (860919 / 50000) (1721841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30066944 :
    ThetaLowerSegment 30066944 30083328 (375762627121 / 12500) (187986564209 / 6250) := by
  exact
    packedTile8192 30066944 30083328 11 978 5483 25 _ _ (430473 / 25000) (344379 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30083328 :
    ThetaLowerSegment 30083328 30099712 (187986564209 / 6250) (3009415711153 / 100000) := by
  exact
    packedTile8192 30083328 30099712 11 947 5484 25 _ _ (1721947 / 100000) (34439 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30099712 :
    ThetaLowerSegment 30099712 30116096 (3009415711153 / 100000) (1505504281039 / 50000) := by
  exact
    packedTile8192 30099712 30116096 11 925 5486 25 _ _ (1722001 / 100000) (430501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30116096 :
    ThetaLowerSegment 30116096 30132480 (1505504281039 / 50000) (301269101079 / 10000) := by
  exact
    packedTile8192 30116096 30132480 11 977 5487 25 _ _ (215257 / 12500) (1722059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30132480 :
    ThetaLowerSegment 30132480 30148864 (301269101079 / 10000) (150719364457 / 5000) := by
  exact
    packedTile8192 30132480 30148864 11 985 5489 25 _ _ (172211 / 10000) (1722113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30148864 :
    ThetaLowerSegment 30148864 30165248 (150719364457 / 5000) (94248630642 / 3125) := by
  exact
    packedTile8192 30148864 30165248 11 911 5490 25 _ _ (430541 / 25000) (1722167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30165248 :
    ThetaLowerSegment 30165248 30181632 (94248630642 / 3125) (3017597455251 / 100000) := by
  exact
    packedTile8192 30165248 30181632 11 953 5492 25 _ _ (1722219 / 100000) (861111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30181632 :
    ThetaLowerSegment 30181632 30198016 (3017597455251 / 100000) (754813139901 / 25000) := by
  exact
    packedTile8192 30181632 30198016 11 961 5493 25 _ _ (1722273 / 100000) (430569 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30198016 :
    ThetaLowerSegment 30198016 30214400 (754813139901 / 25000) (1510440940473 / 50000) := by
  exact
    packedTile8192 30198016 30214400 11 946 5495 25 _ _ (1722327 / 100000) (172233 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30214400 :
    ThetaLowerSegment 30214400 30230784 (1510440940473 / 50000) (1511284907163 / 50000) := by
  exact
    packedTile8192 30214400 30230784 11 980 5496 25 _ _ (1722381 / 100000) (107649 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30230784 :
    ThetaLowerSegment 30230784 30247168 (1511284907163 / 50000) (302420440609 / 10000) := by
  exact
    packedTile8192 30230784 30247168 11 949 5498 25 _ _ (430609 / 25000) (1722439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30247168 :
    ThetaLowerSegment 30247168 30263552 (302420440609 / 10000) (15129109121 / 500) := by
  exact
    packedTile8192 30247168 30263552 11 939 5499 25 _ _ (172249 / 10000) (1722493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30263552 :
    ThetaLowerSegment 30263552 30279936 (15129109121 / 500) (378430988217 / 12500) := by
  exact
    packedTile8192 30263552 30279936 11 944 5501 25 _ _ (107659 / 6250) (1722547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30279936 :
    ThetaLowerSegment 30279936 30296320 (378430988217 / 12500) (189320141937 / 6250) := by
  exact
    packedTile8192 30279936 30296320 11 972 5502 25 _ _ (861299 / 50000) (1722601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30296320 :
    ThetaLowerSegment 30296320 30312704 (189320141937 / 6250) (37884355681 / 1250) := by
  exact
    packedTile8192 30296320 30312704 11 944 5504 25 _ _ (430663 / 25000) (344531 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30312704 :
    ThetaLowerSegment 30312704 30329088 (37884355681 / 1250) (758108315237 / 25000) := by
  exact
    packedTile8192 30312704 30329088 11 978 5505 25 _ _ (861353 / 50000) (1722709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30329088 :
    ThetaLowerSegment 30329088 30345472 (758108315237 / 25000) (758523500397 / 25000) := by
  exact
    packedTile8192 30329088 30345472 11 964 5507 25 _ _ (43069 / 2500) (1722763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30345472 :
    ThetaLowerSegment 30345472 30361856 (758523500397 / 25000) (151786361463 / 5000) := by
  exact
    packedTile8192 30345472 30361856 11 948 5508 25 _ _ (861407 / 50000) (1722817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30361856 :
    ThetaLowerSegment 30361856 30378240 (151786361463 / 5000) (759330651257 / 25000) := by
  exact
    packedTile8192 30361856 30378240 11 926 5510 25 _ _ (430717 / 25000) (1722871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30378240 :
    ThetaLowerSegment 30378240 30394624 (759330651257 / 25000) (1519494335301 / 50000) := by
  exact
    packedTile8192 30378240 30394624 11 967 5511 25 _ _ (861461 / 50000) (68917 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30394624 :
    ThetaLowerSegment 30394624 30411008 (1519494335301 / 50000) (1520339455029 / 50000) := by
  exact
    packedTile8192 30394624 30411008 11 981 5513 25 _ _ (53843 / 3125) (1722979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30411008 :
    ThetaLowerSegment 30411008 30427392 (1520339455029 / 50000) (1521130325799 / 50000) := by
  exact
    packedTile8192 30411008 30427392 11 918 5514 25 _ _ (172303 / 10000) (1723033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30427392 :
    ThetaLowerSegment 30427392 30443776 (1521130325799 / 50000) (1521898821263 / 50000) := by
  exact
    packedTile8192 30427392 30443776 11 892 5516 25 _ _ (430771 / 25000) (1723087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30443776 :
    ThetaLowerSegment 30443776 30460160 (1521898821263 / 50000) (380680835699 / 12500) := by
  exact
    packedTile8192 30443776 30460160 11 957 5517 25 _ _ (861569 / 50000) (1723141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30460160 :
    ThetaLowerSegment 30460160 30476544 (380680835699 / 12500) (95220989239 / 3125) := by
  exact
    packedTile8192 30460160 30476544 11 943 5519 25 _ _ (215399 / 12500) (344639 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30476544 :
    ThetaLowerSegment 30476544 30492928 (95220989239 / 3125) (95272686589 / 3125) := by
  exact
    packedTile8192 30476544 30492928 11 960 5520 25 _ _ (344649 / 20000) (107703 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30492928 :
    ThetaLowerSegment 30492928 30509312 (95272686589 / 3125) (19064532452 / 625) := by
  exact
    packedTile8192 30492928 30509312 11 928 5522 25 _ _ (1723299 / 100000) (861651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30509312 :
    ThetaLowerSegment 30509312 30525696 (19064532452 / 625) (3051991674671 / 100000) := by
  exact
    packedTile8192 30509312 30525696 11 967 5523 25 _ _ (1723353 / 100000) (430839 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30525696 :
    ThetaLowerSegment 30525696 30542080 (3051991674671 / 100000) (3053685782769 / 100000) := by
  exact
    packedTile8192 30525696 30542080 11 983 5525 25 _ _ (861703 / 50000) (1723409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30542080 :
    ThetaLowerSegment 30542080 30558464 (3053685782769 / 100000) (3055274812889 / 100000) := by
  exact
    packedTile8192 30542080 30558464 11 922 5526 25 _ _ (86173 / 5000) (1723463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30558464 :
    ThetaLowerSegment 30558464 30574848 (3055274812889 / 100000) (3056955239039 / 100000) := by
  exact
    packedTile8192 30558464 30574848 11 975 5527 25 _ _ (861757 / 50000) (1723517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30574848 :
    ThetaLowerSegment 30574848 30591232 (3056955239039 / 100000) (1529302346329 / 50000) := by
  exact
    packedTile8192 30574848 30591232 11 957 5529 25 _ _ (1723567 / 100000) (172357 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30591232 :
    ThetaLowerSegment 30591232 30607616 (1529302346329 / 50000) (1530136578893 / 50000) := by
  exact
    packedTile8192 30591232 30607616 11 968 5530 25 _ _ (1723621 / 100000) (215453 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30607616 :
    ThetaLowerSegment 30607616 30624000 (1530136578893 / 50000) (306192099013 / 10000) := by
  exact
    packedTile8192 30607616 30624000 11 956 5532 25 _ _ (861837 / 50000) (1723677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30624000 :
    ThetaLowerSegment 30624000 30640384 (306192099013 / 10000) (1531774094681 / 50000) := by
  exact
    packedTile8192 30624000 30640384 11 944 5533 25 _ _ (107733 / 6250) (1723731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30640384 :
    ThetaLowerSegment 30640384 30656768 (1531774094681 / 50000) (766315406919 / 25000) := by
  exact
    packedTile8192 30640384 30656768 11 994 5535 25 _ _ (1723781 / 100000) (215473 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30656768 :
    ThetaLowerSegment 30656768 30673152 (766315406919 / 25000) (766736022659 / 25000) := by
  exact
    packedTile8192 30656768 30673152 11 976 5536 25 _ _ (344767 / 20000) (861919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30673152 :
    ThetaLowerSegment 30673152 30689536 (766736022659 / 25000) (767140705367 / 25000) := by
  exact
    packedTile8192 30673152 30689536 11 939 5538 25 _ _ (107743 / 6250) (1723891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30689536 :
    ThetaLowerSegment 30689536 30705920 (767140705367 / 25000) (1535099421213 / 50000) := by
  exact
    packedTile8192 30689536 30705920 11 949 5539 25 _ _ (861971 / 50000) (344789 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30705920 :
    ThetaLowerSegment 30705920 30722304 (1535099421213 / 50000) (3071817673731 / 100000) := by
  exact
    packedTile8192 30705920 30722304 11 939 5541 25 _ _ (344799 / 20000) (861999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30722304 :
    ThetaLowerSegment 30722304 30738688 (3071817673731 / 100000) (3073483104099 / 100000) := by
  exact
    packedTile8192 30722304 30738688 11 966 5542 25 _ _ (107753 / 6250) (1724051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30738688 :
    ThetaLowerSegment 30738688 30755072 (3073483104099 / 100000) (3075086518959 / 100000) := by
  exact
    packedTile8192 30738688 30755072 11 930 5544 25 _ _ (862051 / 50000) (344821 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30755072 :
    ThetaLowerSegment 30755072 30771456 (3075086518959 / 100000) (3076707224659 / 100000) := by
  exact
    packedTile8192 30755072 30771456 11 940 5545 25 _ _ (344831 / 20000) (862079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30771456 :
    ThetaLowerSegment 30771456 30787840 (3076707224659 / 100000) (615668009927 / 20000) := by
  exact
    packedTile8192 30771456 30787840 11 947 5547 25 _ _ (107763 / 6250) (1724211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30787840 :
    ThetaLowerSegment 30787840 30804224 (615668009927 / 20000) (3079959131653 / 100000) := by
  exact
    packedTile8192 30787840 30804224 11 939 5548 25 _ _ (862131 / 50000) (344853 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30804224 :
    ThetaLowerSegment 30804224 30820608 (3079959131653 / 100000) (3081604128163 / 100000) := by
  exact
    packedTile8192 30804224 30820608 11 954 5550 25 _ _ (344863 / 20000) (862159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30820608 :
    ThetaLowerSegment 30820608 30836992 (3081604128163 / 100000) (3083285386963 / 100000) := by
  exact
    packedTile8192 30820608 30836992 11 975 5551 25 _ _ (107773 / 6250) (1724371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30836992 :
    ThetaLowerSegment 30836992 30853376 (3083285386963 / 100000) (3084902893861 / 100000) := by
  exact
    packedTile8192 30836992 30853376 11 938 5553 25 _ _ (1724421 / 100000) (215553 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30853376 :
    ThetaLowerSegment 30853376 30869760 (3084902893861 / 100000) (3086567011271 / 100000) := by
  exact
    packedTile8192 30853376 30869760 11 965 5554 25 _ _ (862237 / 50000) (1724477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30869760 :
    ThetaLowerSegment 30869760 30886144 (3086567011271 / 100000) (3088232904353 / 100000) := by
  exact
    packedTile8192 30869760 30886144 11 966 5556 25 _ _ (1724527 / 100000) (172453 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30886144 :
    ThetaLowerSegment 30886144 30902528 (3088232904353 / 100000) (3089895399473 / 100000) := by
  exact
    packedTile8192 30886144 30902528 11 964 5557 25 _ _ (86229 / 5000) (1724583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30902528 :
    ThetaLowerSegment 30902528 30918912 (3089895399473 / 100000) (3091544148621 / 100000) := by
  exact
    packedTile8192 30902528 30918912 11 956 5559 25 _ _ (1724633 / 100000) (431159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30918912 :
    ThetaLowerSegment 30918912 30935296 (3091544148621 / 100000) (618627551697 / 20000) := by
  exact
    packedTile8192 30918912 30935296 11 924 5560 25 _ _ (862343 / 50000) (1724689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30935296 :
    ThetaLowerSegment 30935296 30951680 (618627551697 / 20000) (1547378644203 / 50000) := by
  exact
    packedTile8192 30935296 30951680 11 939 5561 25 _ _ (1724739 / 100000) (862371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30951680 :
    ThetaLowerSegment 30951680 30968064 (1547378644203 / 50000) (309639929039 / 10000) := by
  exact
    packedTile8192 30951680 30968064 11 952 5563 25 _ _ (215599 / 12500) (344959 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30968064 :
    ThetaLowerSegment 30968064 30984448 (309639929039 / 10000) (619595504713 / 20000) := by
  exact
    packedTile8192 30968064 30984448 11 915 5564 25 _ _ (344969 / 20000) (107803 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell30984448 :
    ThetaLowerSegment 30984448 31000832 (619595504713 / 20000) (619918060639 / 20000) := by
  exact
    packedTile8192 30984448 31000832 11 935 5566 25 _ _ (862449 / 50000) (1724901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31000832 :
    ThetaLowerSegment 31000832 31017216 (619918060639 / 20000) (310125488091 / 10000) := by
  exact
    packedTile8192 31000832 31017216 11 965 5567 25 _ _ (1724951 / 100000) (862477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31017216 :
    ThetaLowerSegment 31017216 31033600 (310125488091 / 10000) (1551449404861 / 50000) := by
  exact
    packedTile8192 31017216 31033600 11 953 5569 25 _ _ (431251 / 25000) (1725007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31033600 :
    ThetaLowerSegment 31033600 31049984 (1551449404861 / 50000) (3104477236877 / 100000) := by
  exact
    packedTile8192 31033600 31049984 11 915 5570 25 _ _ (1725057 / 100000) (86253 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31049984 :
    ThetaLowerSegment 31049984 31066368 (3104477236877 / 100000) (97065319181 / 3125) := by
  exact
    packedTile8192 31049984 31066368 11 935 5572 25 _ _ (1725109 / 100000) (215639 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31066368 :
    ThetaLowerSegment 31066368 31070464 (97065319181 / 3125) (1553235737297 / 50000) := by
  exact
    packedTile8192 31066368 31070464 9 221 5573 25 _ _ (862581 / 50000) (345033 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31070464 :
    ThetaLowerSegment 31070464 31072512 (1553235737297 / 50000) (3106694022169 / 100000) := by
  exact
    packedTile8192 31070464 31072512 8 129 5574 25 _ _ (69007 / 4000) (862589 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_21563648_31072512 :
    ThetaLowerSegment 21563648 31072512 (107785947657 / 5000) (3106694022169 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell21563648 cell21580032)
                      (ThetaLowerSegment.join cell21596416 cell21612800))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell21629184 cell21645568)
                      (ThetaLowerSegment.join cell21661952 cell21678336)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell21694720 cell21711104)
                      (ThetaLowerSegment.join cell21727488 cell21743872))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell21760256 cell21776640)
                      (ThetaLowerSegment.join cell21793024 cell21809408))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell21825792 cell21842176)
                      (ThetaLowerSegment.join cell21858560 cell21874944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell21891328 cell21907712)
                      (ThetaLowerSegment.join cell21924096 cell21940480)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell21956864 cell21973248)
                      (ThetaLowerSegment.join cell21989632 cell22006016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22022400 cell22038784)
                      (ThetaLowerSegment.join cell22055168 cell22071552)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22087936 cell22104320)
                      (ThetaLowerSegment.join cell22120704 cell22137088))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22153472 cell22169856)
                      (ThetaLowerSegment.join cell22186240 cell22202624)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22219008 cell22235392)
                      (ThetaLowerSegment.join cell22251776 cell22268160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22284544 cell22300928)
                      (ThetaLowerSegment.join cell22317312 cell22333696))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22350080 cell22366464)
                      (ThetaLowerSegment.join cell22382848 cell22399232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22407424 cell22415616)
                      (ThetaLowerSegment.join cell22423808 cell22432000)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22440192 cell22448384)
                      (ThetaLowerSegment.join cell22456576 cell22464768))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22472960 cell22481152)
                      (ThetaLowerSegment.join cell22489344 cell22497536))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22505728 cell22513920)
                      (ThetaLowerSegment.join cell22522112 cell22530304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22538496 cell22546688)
                      (ThetaLowerSegment.join cell22563072 cell22579456)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22595840 cell22612224)
                      (ThetaLowerSegment.join cell22628608 cell22644992))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22661376 cell22677760)
                      (ThetaLowerSegment.join cell22694144 cell22710528))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22726912 cell22743296)
                      (ThetaLowerSegment.join cell22759680 cell22776064))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22792448 cell22808832)
                      (ThetaLowerSegment.join cell22825216 cell22841600)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22857984 cell22874368)
                      (ThetaLowerSegment.join cell22890752 cell22907136))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22923520 cell22939904)
                      (ThetaLowerSegment.join cell22956288 cell22972672)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell22989056 cell23005440)
                      (ThetaLowerSegment.join cell23021824 cell23038208))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23054592 cell23070976)
                      (ThetaLowerSegment.join cell23087360 cell23103744)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23120128 cell23136512)
                      (ThetaLowerSegment.join cell23152896 cell23169280))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23185664 cell23202048)
                      (ThetaLowerSegment.join cell23218432 cell23234816))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23251200 cell23267584)
                      (ThetaLowerSegment.join cell23283968 cell23300352))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23316736 cell23333120)
                      (ThetaLowerSegment.join cell23349504 cell23365888)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23382272 cell23398656)
                      (ThetaLowerSegment.join cell23415040 cell23431424))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23447808 cell23464192)
                      (ThetaLowerSegment.join cell23480576 cell23496960)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23513344 cell23529728)
                      (ThetaLowerSegment.join cell23546112 cell23562496))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23578880 cell23595264)
                      (ThetaLowerSegment.join cell23611648 cell23628032)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23644416 cell23660800)
                      (ThetaLowerSegment.join cell23677184 cell23693568))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23709952 cell23726336)
                      (ThetaLowerSegment.join cell23742720 cell23759104))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23775488 cell23791872)
                      (ThetaLowerSegment.join cell23808256 cell23824640))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23841024 cell23857408)
                      (ThetaLowerSegment.join cell23873792 cell23890176)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23906560 cell23922944)
                      (ThetaLowerSegment.join cell23939328 cell23955712))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell23972096 cell23988480)
                      (ThetaLowerSegment.join cell24004864 cell24021248)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24037632 cell24054016)
                      (ThetaLowerSegment.join cell24070400 cell24086784))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24103168 cell24119552)
                      (ThetaLowerSegment.join cell24135936 cell24152320)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24168704 cell24185088)
                      (ThetaLowerSegment.join cell24201472 cell24217856))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24234240 cell24250624)
                      (ThetaLowerSegment.join cell24267008 cell24283392))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24299776 cell24316160)
                      (ThetaLowerSegment.join cell24332544 cell24348928))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24365312 cell24381696)
                      (ThetaLowerSegment.join cell24398080 cell24414464)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24430848 cell24447232)
                      (ThetaLowerSegment.join cell24463616 cell24480000))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24496384 cell24512768)
                      (ThetaLowerSegment.join cell24529152 cell24545536))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24561920 cell24578304)
                      (ThetaLowerSegment.join cell24594688 cell24611072))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24627456 cell24643840)
                      (ThetaLowerSegment.join cell24660224 cell24676608)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24692992 cell24709376)
                      (ThetaLowerSegment.join cell24725760 cell24742144))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24758528 cell24774912)
                      (ThetaLowerSegment.join cell24791296 cell24807680))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24824064 cell24840448)
                      (ThetaLowerSegment.join cell24856832 cell24873216))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24889600 cell24905984)
                      (ThetaLowerSegment.join cell24922368 cell24938752)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell24955136 cell24971520)
                      (ThetaLowerSegment.join cell24987904 cell25004288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25020672 cell25037056)
                      (ThetaLowerSegment.join cell25053440 cell25069824)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25086208 cell25102592)
                      (ThetaLowerSegment.join cell25118976 cell25135360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25151744 cell25168128)
                      (ThetaLowerSegment.join cell25184512 cell25200896)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25217280 cell25233664)
                      (ThetaLowerSegment.join cell25250048 cell25266432))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25282816 cell25299200)
                      (ThetaLowerSegment.join cell25315584 cell25331968))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25348352 cell25364736)
                      (ThetaLowerSegment.join cell25381120 cell25397504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25413888 cell25430272)
                      (ThetaLowerSegment.join cell25446656 cell25463040)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25479424 cell25495808)
                      (ThetaLowerSegment.join cell25512192 cell25528576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25544960 cell25561344)
                      (ThetaLowerSegment.join cell25577728 cell25594112))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25610496 cell25626880)
                      (ThetaLowerSegment.join cell25643264 cell25659648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25676032 cell25692416)
                      (ThetaLowerSegment.join cell25708800 cell25725184)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25741568 cell25757952)
                      (ThetaLowerSegment.join cell25774336 cell25790720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25807104 cell25823488)
                      (ThetaLowerSegment.join cell25839872 cell25856256))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25872640 cell25889024)
                      (ThetaLowerSegment.join cell25905408 cell25921792))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell25938176 cell25954560)
                      (ThetaLowerSegment.join cell25970944 cell25987328)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26003712 cell26020096)
                      (ThetaLowerSegment.join cell26036480 cell26052864))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26069248 cell26085632)
                      (ThetaLowerSegment.join cell26102016 cell26118400)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26134784 cell26151168)
                      (ThetaLowerSegment.join cell26167552 cell26183936))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26200320 cell26216704)
                      (ThetaLowerSegment.join cell26233088 cell26249472)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26265856 cell26282240)
                      (ThetaLowerSegment.join cell26298624 cell26315008))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26331392 cell26347776)
                      (ThetaLowerSegment.join cell26364160 cell26380544))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26396928 cell26413312)
                      (ThetaLowerSegment.join cell26429696 cell26446080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26462464 cell26478848)
                      (ThetaLowerSegment.join cell26495232 cell26511616)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26528000 cell26544384)
                      (ThetaLowerSegment.join cell26560768 cell26577152))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26593536 cell26609920)
                      (ThetaLowerSegment.join cell26626304 cell26642688))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26659072 cell26675456)
                      (ThetaLowerSegment.join cell26691840 cell26708224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26724608 cell26740992)
                      (ThetaLowerSegment.join cell26757376 cell26773760)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26790144 cell26806528)
                      (ThetaLowerSegment.join cell26822912 cell26839296))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26855680 cell26872064)
                      (ThetaLowerSegment.join cell26888448 cell26904832))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26921216 cell26937600)
                      (ThetaLowerSegment.join cell26953984 cell26970368))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell26986752 cell27003136)
                      (ThetaLowerSegment.join cell27019520 cell27035904)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27052288 cell27068672)
                      (ThetaLowerSegment.join cell27085056 cell27101440))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27117824 cell27134208)
                      (ThetaLowerSegment.join cell27150592 cell27166976)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27183360 cell27199744)
                      (ThetaLowerSegment.join cell27216128 cell27232512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27248896 cell27265280)
                      (ThetaLowerSegment.join cell27281664 cell27298048)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27314432 cell27330816)
                      (ThetaLowerSegment.join cell27347200 cell27363584))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27379968 cell27396352)
                      (ThetaLowerSegment.join cell27412736 cell27429120))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27445504 cell27461888)
                      (ThetaLowerSegment.join cell27478272 cell27494656))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27511040 cell27527424)
                      (ThetaLowerSegment.join cell27543808 cell27560192)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27576576 cell27592960)
                      (ThetaLowerSegment.join cell27609344 cell27625728))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27642112 cell27658496)
                      (ThetaLowerSegment.join cell27674880 cell27691264)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27707648 cell27724032)
                      (ThetaLowerSegment.join cell27740416 cell27756800))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27773184 cell27789568)
                      (ThetaLowerSegment.join cell27805952 cell27822336)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27838720 cell27855104)
                      (ThetaLowerSegment.join cell27871488 cell27887872))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27904256 cell27920640)
                      (ThetaLowerSegment.join cell27937024 cell27953408))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell27969792 cell27986176)
                      (ThetaLowerSegment.join cell28002560 cell28018944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28035328 cell28051712)
                      (ThetaLowerSegment.join cell28068096 cell28084480)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28100864 cell28117248)
                      (ThetaLowerSegment.join cell28133632 cell28150016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28166400 cell28182784)
                      (ThetaLowerSegment.join cell28199168 cell28215552)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28231936 cell28248320)
                      (ThetaLowerSegment.join cell28264704 cell28281088))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28297472 cell28313856)
                      (ThetaLowerSegment.join cell28330240 cell28346624)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28363008 cell28379392)
                      (ThetaLowerSegment.join cell28395776 cell28412160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28428544 cell28444928)
                      (ThetaLowerSegment.join cell28461312 cell28477696))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28494080 cell28510464)
                      (ThetaLowerSegment.join cell28526848 cell28543232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28559616 cell28576000)
                      (ThetaLowerSegment.join cell28592384 cell28608768)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28625152 cell28641536)
                      (ThetaLowerSegment.join cell28657920 cell28674304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28690688 cell28707072)
                      (ThetaLowerSegment.join cell28723456 cell28739840))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28756224 cell28772608)
                      (ThetaLowerSegment.join cell28788992 cell28805376))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28821760 cell28838144)
                      (ThetaLowerSegment.join cell28854528 cell28870912)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28887296 cell28903680)
                      (ThetaLowerSegment.join cell28920064 cell28936448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell28952832 cell28969216)
                      (ThetaLowerSegment.join cell28985600 cell29001984))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell29018368 cell29034752)
                      (ThetaLowerSegment.join cell29051136 cell29067520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell29083904 cell29100288)
                      (ThetaLowerSegment.join cell29116672 cell29133056)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell29149440 cell29165824)
                      (ThetaLowerSegment.join cell29182208 cell29198592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell29214976 cell29231360)
                      (ThetaLowerSegment.join cell29247744 cell29264128)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell29280512 cell29296896)
                      (ThetaLowerSegment.join cell29313280 cell29329664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell29346048 cell29362432)
                      (ThetaLowerSegment.join cell29378816 cell29395200)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell29411584 cell29427968)
                      (ThetaLowerSegment.join cell29444352 cell29460736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell29477120 cell29493504)
                      (ThetaLowerSegment.join cell29509888 cell29526272))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell29542656 cell29559040)
                      (ThetaLowerSegment.join cell29575424 cell29591808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell29608192 cell29624576)
                      (ThetaLowerSegment.join cell29640960 cell29657344)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell29673728 cell29690112)
                      (ThetaLowerSegment.join cell29706496 cell29722880))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell29739264 cell29755648)
                      (ThetaLowerSegment.join cell29772032 cell29788416)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell29804800 cell29821184)
                  (ThetaLowerSegment.join cell29837568 cell29853952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell29870336 cell29886720)
                  (ThetaLowerSegment.join cell29903104 cell29919488)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell29935872 cell29952256)
                  (ThetaLowerSegment.join cell29968640 cell29985024))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30001408 cell30017792)
                  (ThetaLowerSegment.join cell30034176 cell30050560))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30066944 cell30083328)
                  (ThetaLowerSegment.join cell30099712 cell30116096))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30132480 cell30148864)
                  (ThetaLowerSegment.join cell30165248 cell30181632)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30198016 cell30214400)
                  (ThetaLowerSegment.join cell30230784 cell30247168))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30263552 cell30279936)
                  (ThetaLowerSegment.join cell30296320 cell30312704)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30329088 cell30345472)
                  (ThetaLowerSegment.join cell30361856 cell30378240))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30394624 cell30411008)
                  (ThetaLowerSegment.join cell30427392 cell30443776)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30460160 cell30476544)
                  (ThetaLowerSegment.join cell30492928 cell30509312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30525696 cell30542080)
                  (ThetaLowerSegment.join cell30558464 cell30574848))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30591232 cell30607616)
                  (ThetaLowerSegment.join cell30624000 cell30640384))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30656768 cell30673152)
                  (ThetaLowerSegment.join cell30689536 cell30705920)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30722304 cell30738688)
                  (ThetaLowerSegment.join cell30755072 cell30771456))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell30787840 cell30804224)
                  (ThetaLowerSegment.join cell30820608 cell30836992))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell30853376 cell30869760)
              (ThetaLowerSegment.join cell30886144 cell30902528))
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell30918912 cell30935296)
              (ThetaLowerSegment.join cell30951680 cell30968064)))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell30984448 cell31000832)
              (ThetaLowerSegment.join cell31017216 cell31033600))
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell31049984 cell31066368)
              cell31070464)))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
