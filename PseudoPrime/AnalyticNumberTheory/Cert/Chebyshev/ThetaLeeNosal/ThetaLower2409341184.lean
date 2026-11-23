/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2409341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2377341184 :
    ThetaLowerSegment 2377341184 2377472256 (237728310708963 / 100000)
      (118870633202943 / 50000) := by
  exact
    packedTile65536 2377341184 2377472256 14 6001 48757 31 _ _ (2158923 / 100000) (1079463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2377472256 :
    ThetaLowerSegment 2377472256 2377603328 (118870633202943 / 50000) (59438592776229 / 25000) := by
  exact
    packedTile65536 2377472256 2377603328 14 6070 48759 31 _ _ (2158929 / 100000) (539733 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2377603328 :
    ThetaLowerSegment 2377603328 2377734400 (59438592776229 / 25000) (118883762744889 / 50000) := by
  exact
    packedTile65536 2377603328 2377734400 14 6093 48760 31 _ _ (1079467 / 50000) (2158937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2377734400 :
    ThetaLowerSegment 2377734400 2377865472 (118883762744889 / 50000)
      (118890339955599 / 50000) := by
  exact
    packedTile65536 2377734400 2377865472 14 6093 48762 31 _ _ (107947 / 5000) (2158943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2377865472 :
    ThetaLowerSegment 2377865472 2377996544 (118890339955599 / 50000) (59448437541057 / 25000) := by
  exact
    packedTile65536 2377865472 2377996544 14 6054 48763 31 _ _ (431789 / 20000) (539737 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2377996544 :
    ThetaLowerSegment 2377996544 2378127616 (59448437541057 / 25000) (118903496584831 / 50000) := by
  exact
    packedTile65536 2377996544 2378127616 14 6134 48764 31 _ _ (2158951 / 100000) (1079477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2378127616 :
    ThetaLowerSegment 2378127616 2378258688 (118903496584831 / 50000)
      (118909970214397 / 50000) := by
  exact
    packedTile65536 2378127616 2378258688 14 5997 48766 31 _ _ (539739 / 25000) (2158959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2378258688 :
    ThetaLowerSegment 2378258688 2378389760 (118909970214397 / 50000)
      (118916619817357 / 50000) := by
  exact
    packedTile65536 2378258688 2378389760 14 6160 48767 31 _ _ (1079481 / 50000) (431793 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2378389760 :
    ThetaLowerSegment 2378389760 2378520832 (118916619817357 / 50000) (9513841951437 / 4000) := by
  exact
    packedTile65536 2378389760 2378520832 14 5933 48768 31 _ _ (2158967 / 100000) (215897 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2378520832 :
    ThetaLowerSegment 2378520832 2378651904 (9513841951437 / 4000) (237859084664899 / 100000) := by
  exact
    packedTile65536 2378520832 2378651904 14 6038 48770 31 _ _ (2158973 / 100000) (67468 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2378651904 :
    ThetaLowerSegment 2378651904 2378782976 (237859084664899 / 100000)
      (237872081712459 / 100000) := by
  exact
    packedTile65536 2378651904 2378782976 14 6020 48771 31 _ _ (1079489 / 50000) (2158981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2378782976 :
    ThetaLowerSegment 2378782976 2378914048 (237872081712459 / 100000)
      (237885063683251 / 100000) := by
  exact
    packedTile65536 2378782976 2378914048 14 6013 48772 31 _ _ (269873 / 12500) (2158987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2378914048 :
    ThetaLowerSegment 2378914048 2379045120 (237885063683251 / 100000) (14868639189949 / 6250) := by
  exact
    packedTile65536 2378914048 2379045120 14 6097 48774 31 _ _ (2158989 / 100000) (134937 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2379045120 :
    ThetaLowerSegment 2379045120 2379176192 (14868639189949 / 6250) (237911334297829 / 100000) := by
  exact
    packedTile65536 2379045120 2379176192 14 6071 48775 31 _ _ (431799 / 20000) (1079499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2379176192 :
    ThetaLowerSegment 2379176192 2379307264 (237911334297829 / 100000)
      (59481097444219 / 25000) := by
  exact
    packedTile65536 2379176192 2379307264 14 6047 48776 31 _ _ (2159001 / 100000) (539751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2379307264 :
    ThetaLowerSegment 2379307264 2379438336 (59481097444219 / 25000) (118968802526301 / 50000) := by
  exact
    packedTile65536 2379307264 2379438336 14 6121 48778 31 _ _ (1079503 / 50000) (2159009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2379438336 :
    ThetaLowerSegment 2379438336 2379569408 (118968802526301 / 50000) (23795080525197 / 10000) := by
  exact
    packedTile65536 2379438336 2379569408 14 6114 48779 31 _ _ (539753 / 25000) (431803 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2379569408 :
    ThetaLowerSegment 2379569408 2379700480 (23795080525197 / 10000)
      (237963916962211 / 100000) := by
  exact
    packedTile65536 2379569408 2379700480 14 6073 48780 31 _ _ (2159017 / 100000) (107951 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2379700480 :
    ThetaLowerSegment 2379700480 2379831552 (237963916962211 / 100000) (11898850355933 / 5000) := by
  exact
    packedTile65536 2379700480 2379831552 14 6063 48782 31 _ _ (2159023 / 100000) (1079513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2379831552 :
    ThetaLowerSegment 2379831552 2379962624 (11898850355933 / 5000) (59497537820281 / 25000) := by
  exact
    packedTile65536 2379831552 2379962624 14 6088 48783 31 _ _ (539757 / 25000) (2159031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2379962624 :
    ThetaLowerSegment 2379962624 2380093696 (59497537820281 / 25000) (119001763248377 / 50000) := by
  exact
    packedTile65536 2379962624 2380093696 14 6195 48784 31 _ _ (1079517 / 50000) (2159037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2380093696 :
    ThetaLowerSegment 2380093696 2380224768 (119001763248377 / 50000)
      (119008171276129 / 50000) := by
  exact
    packedTile65536 2380093696 2380224768 14 5936 48786 31 _ _ (2159039 / 100000) (1079521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2380224768 :
    ThetaLowerSegment 2380224768 2380355840 (119008171276129 / 50000)
      (119014618184499 / 50000) := by
  exact
    packedTile65536 2380224768 2380355840 14 5972 48787 31 _ _ (431809 / 20000) (269881 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2380355840 :
    ThetaLowerSegment 2380355840 2380486912 (119014618184499 / 50000) (29755301091631 / 12500) := by
  exact
    packedTile65536 2380355840 2380486912 14 6101 48788 31 _ _ (43181 / 2000) (2159053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2380486912 :
    ThetaLowerSegment 2380486912 2380617984 (29755301091631 / 12500) (5951389312437 / 2500) := by
  exact
    packedTile65536 2380486912 2380617984 14 6097 48790 31 _ _ (134941 / 6250) (2159059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2380617984 :
    ThetaLowerSegment 2380617984 2380749056 (5951389312437 / 2500) (119034304453899 / 50000) := by
  exact
    packedTile65536 2380617984 2380749056 14 6038 48791 31 _ _ (2159061 / 100000) (269883 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2380749056 :
    ThetaLowerSegment 2380749056 2380880128 (119034304453899 / 50000)
      (119040937107723 / 50000) := by
  exact
    packedTile65536 2380749056 2380880128 14 6144 48792 31 _ _ (2159067 / 100000) (215907 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2380880128 :
    ThetaLowerSegment 2380880128 2381011200 (119040937107723 / 50000)
      (119047490970779 / 50000) := by
  exact
    packedTile65536 2380880128 2381011200 14 6071 48794 31 _ _ (67471 / 3125) (86363 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2381011200 :
    ThetaLowerSegment 2381011200 2381142272 (119047490970779 / 50000) (29763495019927 / 12500) := by
  exact
    packedTile65536 2381011200 2381142272 14 6011 48795 31 _ _ (1079539 / 50000) (2159081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2381142272 :
    ThetaLowerSegment 2381142272 2381273344 (29763495019927 / 12500) (47624223090427 / 20000) := by
  exact
    packedTile65536 2381142272 2381273344 14 6093 48796 31 _ _ (2159083 / 100000) (1079543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2381273344 :
    ThetaLowerSegment 2381273344 2381404416 (47624223090427 / 20000)
      (238134255667789 / 100000) := by
  exact
    packedTile65536 2381273344 2381404416 14 6086 48798 31 _ _ (2159089 / 100000) (539773 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2381404416 :
    ThetaLowerSegment 2381404416 2381535488 (238134255667789 / 100000)
      (238147287959173 / 100000) := by
  exact
    packedTile65536 2381404416 2381535488 14 6036 48799 31 _ _ (1079547 / 50000) (2159097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2381535488 :
    ThetaLowerSegment 2381535488 2381666560 (238147287959173 / 100000)
      (238160249036473 / 100000) := by
  exact
    packedTile65536 2381535488 2381666560 14 6003 48800 31 _ _ (21591 / 1000) (2159103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2381666560 :
    ThetaLowerSegment 2381666560 2381797632 (238160249036473 / 100000)
      (119086741095509 / 50000) := by
  exact
    packedTile65536 2381666560 2381797632 14 6129 48802 31 _ _ (431821 / 20000) (539777 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2381797632 :
    ThetaLowerSegment 2381797632 2381928704 (119086741095509 / 50000)
      (119093270247173 / 50000) := by
  exact
    packedTile65536 2381797632 2381928704 14 6048 48803 31 _ _ (2159111 / 100000) (1079557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2381928704 :
    ThetaLowerSegment 2381928704 2382059776 (119093270247173 / 50000)
      (119099801573073 / 50000) := by
  exact
    packedTile65536 2381928704 2382059776 14 6050 48805 31 _ _ (539779 / 25000) (2159119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2382059776 :
    ThetaLowerSegment 2382059776 2382190848 (119099801573073 / 50000)
      (119106328598879 / 50000) := by
  exact
    packedTile65536 2382059776 2382190848 14 6046 48806 31 _ _ (1079561 / 50000) (17273 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2382190848 :
    ThetaLowerSegment 2382190848 2382321920 (119106328598879 / 50000)
      (119112935527499 / 50000) := by
  exact
    packedTile65536 2382190848 2382321920 14 6120 48807 31 _ _ (2159127 / 100000) (215913 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2382321920 :
    ThetaLowerSegment 2382321920 2382452992 (119112935527499 / 50000) (23823900722017 / 10000) := by
  exact
    packedTile65536 2382321920 2382452992 14 6084 48809 31 _ _ (2159133 / 100000) (67473 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2382452992 :
    ThetaLowerSegment 2382452992 2382584064 (23823900722017 / 10000) (119126063071329 / 50000) := by
  exact
    packedTile65536 2382452992 2382584064 14 6076 48810 31 _ _ (1079569 / 50000) (2159141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2382584064 :
    ThetaLowerSegment 2382584064 2382715136 (119126063071329 / 50000)
      (119132683006833 / 50000) := by
  exact
    packedTile65536 2382584064 2382715136 14 6132 48811 31 _ _ (269893 / 12500) (2159147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2382715136 :
    ThetaLowerSegment 2382715136 2382846208 (119132683006833 / 50000) (47655690523151 / 20000) := by
  exact
    packedTile65536 2382715136 2382846208 14 6061 48813 31 _ _ (2159149 / 100000) (134947 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2382846208 :
    ThetaLowerSegment 2382846208 2382977280 (47655690523151 / 20000) (47658297918729 / 20000) := by
  exact
    packedTile65536 2382846208 2382977280 14 6038 48814 31 _ _ (431831 / 20000) (1079579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2382977280 :
    ThetaLowerSegment 2382977280 2383108352 (47658297918729 / 20000) (47660926480113 / 20000) := by
  exact
    packedTile65536 2382977280 2383108352 14 6087 48815 31 _ _ (53979 / 2500) (2159163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2383108352 :
    ThetaLowerSegment 2383108352 2383239424 (47660926480113 / 20000)
      (238317660808209 / 100000) := by
  exact
    packedTile65536 2383108352 2383239424 14 6034 48817 31 _ _ (1079583 / 50000) (2159169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2383239424 :
    ThetaLowerSegment 2383239424 2383370496 (238317660808209 / 100000)
      (23833085550219 / 10000) := by
  exact
    packedTile65536 2383239424 2383370496 14 6111 48818 31 _ _ (2159171 / 100000) (1079587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2383370496 :
    ThetaLowerSegment 2383370496 2383501568 (23833085550219 / 10000) (59586007700061 / 25000) := by
  exact
    packedTile65536 2383370496 2383501568 14 6102 48819 31 _ _ (2159177 / 100000) (107959 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2383501568 :
    ThetaLowerSegment 2383501568 2383632640 (59586007700061 / 25000) (29794650766101 / 12500) := by
  exact
    packedTile65536 2383501568 2383632640 14 6102 48821 31 _ _ (1079591 / 50000) (431837 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2383632640 :
    ThetaLowerSegment 2383632640 2383763712 (29794650766101 / 12500) (5959260724903 / 2500) := by
  exact
    packedTile65536 2383632640 2383763712 14 6124 48822 31 _ _ (539797 / 25000) (2159191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2383763712 :
    ThetaLowerSegment 2383763712 2383894784 (5959260724903 / 2500) (14898975544387 / 6250) := by
  exact
    packedTile65536 2383763712 2383894784 14 6104 48823 31 _ _ (2159193 / 100000) (539799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2383894784 :
    ThetaLowerSegment 2383894784 2384025856 (14898975544387 / 6250) (59599207911217 / 25000) := by
  exact
    packedTile65536 2383894784 2384025856 14 6124 48825 31 _ _ (2159199 / 100000) (1079601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2384025856 :
    ThetaLowerSegment 2384025856 2384156928 (59599207911217 / 25000) (59602471548063 / 25000) := by
  exact
    packedTile65536 2384025856 2384156928 14 6046 48826 31 _ _ (539801 / 25000) (2159207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2384156928 :
    ThetaLowerSegment 2384156928 2384288000 (59602471548063 / 25000) (59605775139363 / 25000) := by
  exact
    packedTile65536 2384156928 2384288000 14 6120 48827 31 _ _ (215921 / 10000) (2159213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2384288000 :
    ThetaLowerSegment 2384288000 2384419072 (59605775139363 / 25000)
      (238436157330557 / 100000) := by
  exact
    packedTile65536 2384288000 2384419072 14 6047 48829 31 _ _ (431843 / 20000) (1079609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2384419072 :
    ThetaLowerSegment 2384419072 2384550144 (238436157330557 / 100000)
      (59612297057323 / 25000) := by
  exact
    packedTile65536 2384419072 2384550144 14 6035 48830 31 _ _ (2159221 / 100000) (269903 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2384550144 :
    ThetaLowerSegment 2384550144 2384681216 (59612297057323 / 25000) (119231133330587 / 50000) := by
  exact
    packedTile65536 2384550144 2384681216 14 6057 48831 31 _ _ (1079613 / 50000) (2159229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2384681216 :
    ThetaLowerSegment 2384681216 2384812288 (119231133330587 / 50000)
      (119237735182427 / 50000) := by
  exact
    packedTile65536 2384681216 2384812288 14 6115 48833 31 _ _ (67476 / 3125) (431847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2384812288 :
    ThetaLowerSegment 2384812288 2384943360 (119237735182427 / 50000) (14905531200057 / 6250) := by
  exact
    packedTile65536 2384812288 2384943360 14 6034 48834 31 _ _ (2159237 / 100000) (53981 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2384943360 :
    ThetaLowerSegment 2384943360 2385074432 (14905531200057 / 6250) (14906347393911 / 6250) := by
  exact
    packedTile65536 2384943360 2385074432 14 6048 48835 31 _ _ (2159243 / 100000) (1079623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2385074432 :
    ThetaLowerSegment 2385074432 2385205504 (14906347393911 / 6250) (7453582402116 / 3125) := by
  exact
    packedTile65536 2385074432 2385205504 14 6057 48837 31 _ _ (134953 / 6250) (2159251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2385205504 :
    ThetaLowerSegment 2385205504 2385336576 (7453582402116 / 3125) (119263795116229 / 50000) := by
  exact
    packedTile65536 2385205504 2385336576 14 5999 48838 31 _ _ (1079627 / 50000) (2159257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2385336576 :
    ThetaLowerSegment 2385336576 2385467648 (119263795116229 / 50000)
      (119270359263589 / 50000) := by
  exact
    packedTile65536 2385336576 2385467648 14 6080 48839 31 _ _ (2159259 / 100000) (1079631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2385467648 :
    ThetaLowerSegment 2385467648 2385598720 (119270359263589 / 50000)
      (238553892202943 / 100000) := by
  exact
    packedTile65536 2385467648 2385598720 14 6101 48841 31 _ _ (431853 / 20000) (539817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2385598720 :
    ThetaLowerSegment 2385598720 2385729792 (238553892202943 / 100000)
      (238566903963963 / 100000) := by
  exact
    packedTile65536 2385598720 2385729792 14 6026 48842 31 _ _ (215927 / 10000) (2159273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2385729792 :
    ThetaLowerSegment 2385729792 2385860864 (238566903963963 / 100000)
      (238580062591907 / 100000) := by
  exact
    packedTile65536 2385729792 2385860864 14 6094 48843 31 _ _ (539819 / 25000) (2159279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2385860864 :
    ThetaLowerSegment 2385860864 2385991936 (238580062591907 / 100000)
      (23859332705509 / 10000) := by
  exact
    packedTile65536 2385860864 2385991936 14 6143 48845 31 _ _ (2159281 / 100000) (539821 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2385991936 :
    ThetaLowerSegment 2385991936 2386123008 (23859332705509 / 10000) (119303240715747 / 50000) := by
  exact
    packedTile65536 2385991936 2386123008 14 6092 48846 31 _ _ (2159287 / 100000) (215929 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2386123008 :
    ThetaLowerSegment 2386123008 2386254080 (119303240715747 / 50000)
      (119309861105019 / 50000) := by
  exact
    packedTile65536 2386123008 2386254080 14 6132 48847 31 _ _ (539823 / 25000) (431859 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2386254080 :
    ThetaLowerSegment 2386254080 2386385152 (119309861105019 / 50000) (11931633791937 / 5000) := by
  exact
    packedTile65536 2386254080 2386385152 14 5999 48849 31 _ _ (1079649 / 50000) (2159301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2386385152 :
    ThetaLowerSegment 2386385152 2386516224 (11931633791937 / 5000) (119322874129551 / 50000) := by
  exact
    packedTile65536 2386385152 2386516224 14 6054 48850 31 _ _ (2159303 / 100000) (1079653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2386516224 :
    ThetaLowerSegment 2386516224 2386647296 (119322874129551 / 50000) (47731774075979 / 20000) := by
  exact
    packedTile65536 2386516224 2386647296 14 6077 48851 31 _ _ (2159309 / 100000) (134957 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2386647296 :
    ThetaLowerSegment 2386647296 2386778368 (47731774075979 / 20000)
      (238671936388909 / 100000) := by
  exact
    packedTile65536 2386647296 2386778368 14 6051 48853 31 _ _ (1079657 / 50000) (2159317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2386778368 :
    ThetaLowerSegment 2386778368 2386909440 (238671936388909 / 100000)
      (238684954929189 / 100000) := by
  exact
    packedTile65536 2386778368 2386909440 14 6029 48854 31 _ _ (53983 / 2500) (2159323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2386909440 :
    ThetaLowerSegment 2386909440 2387040512 (238684954929189 / 100000)
      (238698109537089 / 100000) := by
  exact
    packedTile65536 2386909440 2387040512 14 6092 48856 31 _ _ (86373 / 4000) (67479 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2387040512 :
    ThetaLowerSegment 2387040512 2387171584 (238698109537089 / 100000)
      (238711389422739 / 100000) := by
  exact
    packedTile65536 2387040512 2387171584 14 6150 48857 31 _ _ (2159331 / 100000) (1079667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2387171584 :
    ThetaLowerSegment 2387171584 2387302656 (238711389422739 / 100000)
      (238724533300971 / 100000) := by
  exact
    packedTile65536 2387171584 2387302656 14 6087 48858 31 _ _ (269917 / 12500) (2159339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2387302656 :
    ThetaLowerSegment 2387302656 2387433728 (238724533300971 / 100000)
      (119368752231179 / 50000) := by
  exact
    packedTile65536 2387302656 2387433728 14 6007 48860 31 _ _ (2159341 / 100000) (134959 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2387433728 :
    ThetaLowerSegment 2387433728 2387564800 (119368752231179 / 50000)
      (238750596583219 / 100000) := by
  exact
    packedTile65536 2387433728 2387564800 14 6063 48861 31 _ _ (2159347 / 100000) (43187 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2387564800 :
    ThetaLowerSegment 2387564800 2387695872 (238750596583219 / 100000)
      (238763874438667 / 100000) := by
  exact
    packedTile65536 2387564800 2387695872 14 6149 48862 31 _ _ (269919 / 12500) (431871 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2387695872 :
    ThetaLowerSegment 2387695872 2387826944 (238763874438667 / 100000)
      (238776934235851 / 100000) := by
  exact
    packedTile65536 2387695872 2387826944 14 6048 48864 31 _ _ (1079679 / 50000) (2159361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2387826944 :
    ThetaLowerSegment 2387826944 2387958016 (238776934235851 / 100000) (7462192105564 / 3125) := by
  exact
    packedTile65536 2387826944 2387958016 14 6119 48865 31 _ _ (2159363 / 100000) (1079683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2387958016 :
    ThetaLowerSegment 2387958016 2388089088 (7462192105564 / 3125) (47760639288983 / 20000) := by
  exact
    packedTile65536 2387958016 2388089088 14 6043 48866 31 _ _ (2159369 / 100000) (539843 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2388089088 :
    ThetaLowerSegment 2388089088 2388220160 (47760639288983 / 20000)
      (238816100863939 / 100000) := by
  exact
    packedTile65536 2388089088 2388220160 14 5976 48868 31 _ _ (1079687 / 50000) (2159377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2388220160 :
    ThetaLowerSegment 2388220160 2388351232 (238816100863939 / 100000)
      (238829193184879 / 100000) := by
  exact
    packedTile65536 2388220160 2388351232 14 6063 48869 31 _ _ (107969 / 5000) (2159383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2388351232 :
    ThetaLowerSegment 2388351232 2388482304 (238829193184879 / 100000)
      (238842248826589 / 100000) := by
  exact
    packedTile65536 2388351232 2388482304 14 6046 48870 31 _ _ (431877 / 20000) (539847 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2388482304 :
    ThetaLowerSegment 2388482304 2388613376 (238842248826589 / 100000) (11942769004163 / 5000) := by
  exact
    packedTile65536 2388482304 2388613376 14 6081 48872 31 _ _ (2159391 / 100000) (1079697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2388613376 :
    ThetaLowerSegment 2388613376 2388744448 (11942769004163 / 5000) (14929267384723 / 6250) := by
  exact
    packedTile65536 2388613376 2388744448 14 5973 48873 31 _ _ (539849 / 25000) (2159399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2388744448 :
    ThetaLowerSegment 2388744448 2388875520 (14929267384723 / 6250) (119440765202821 / 50000) := by
  exact
    packedTile65536 2388744448 2388875520 14 6137 48874 31 _ _ (1079701 / 50000) (431881 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2388875520 :
    ThetaLowerSegment 2388875520 2389006592 (119440765202821 / 50000)
      (238894596977399 / 100000) := by
  exact
    packedTile65536 2388875520 2389006592 14 6051 48876 31 _ _ (2159407 / 100000) (215941 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2389006592 :
    ThetaLowerSegment 2389006592 2389137664 (238894596977399 / 100000)
      (119453874980991 / 50000) := by
  exact
    packedTile65536 2389006592 2389137664 14 6091 48877 31 _ _ (2159413 / 100000) (269927 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2389137664 :
    ThetaLowerSegment 2389137664 2389268736 (119453874980991 / 50000)
      (119460472002981 / 50000) := by
  exact
    packedTile65536 2389137664 2389268736 14 6110 48878 31 _ _ (1079709 / 50000) (2159421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2389268736 :
    ThetaLowerSegment 2389268736 2389399808 (119460472002981 / 50000)
      (119467035572229 / 50000) := by
  exact
    packedTile65536 2389268736 2389399808 14 6079 48880 31 _ _ (67482 / 3125) (2159427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2389399808 :
    ThetaLowerSegment 2389399808 2389530880 (119467035572229 / 50000) (59736805516767 / 25000) := by
  exact
    packedTile65536 2389399808 2389530880 14 6090 48881 31 _ _ (2159429 / 100000) (269929 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2389530880 :
    ThetaLowerSegment 2389530880 2389661952 (59736805516767 / 25000) (119480164918759 / 50000) := by
  exact
    packedTile65536 2389530880 2389661952 14 6070 48882 31 _ _ (431887 / 20000) (1079719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2389661952 :
    ThetaLowerSegment 2389661952 2389793024 (119480164918759 / 50000)
      (119486751210759 / 50000) := by
  exact
    packedTile65536 2389661952 2389793024 14 6100 48884 31 _ _ (26993 / 1250) (2159443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2389793024 :
    ThetaLowerSegment 2389793024 2389924096 (119486751210759 / 50000) (59746621792579 / 25000) := by
  exact
    packedTile65536 2389793024 2389924096 14 6013 48885 31 _ _ (1079723 / 50000) (2159449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2389924096 :
    ThetaLowerSegment 2389924096 2390055168 (59746621792579 / 25000)
      (238999709488789 / 100000) := by
  exact
    packedTile65536 2389924096 2390055168 14 6123 48886 31 _ _ (2159451 / 100000) (1079727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2390055168 :
    ThetaLowerSegment 2390055168 2390186240 (238999709488789 / 100000)
      (23901273749287 / 10000) := by
  exact
    packedTile65536 2390055168 2390186240 14 6033 48888 31 _ _ (2159457 / 100000) (107973 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2390186240 :
    ThetaLowerSegment 2390186240 2390317312 (23901273749287 / 10000) (11951289572033 / 5000) := by
  exact
    packedTile65536 2390186240 2390317312 14 6045 48889 31 _ _ (1079731 / 50000) (431893 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2390317312 :
    ThetaLowerSegment 2390317312 2390448384 (11951289572033 / 5000) (7469972287461 / 3125) := by
  exact
    packedTile65536 2390317312 2390448384 14 6169 48890 31 _ _ (539867 / 25000) (2159471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2390448384 :
    ThetaLowerSegment 2390448384 2390579456 (7469972287461 / 3125) (239052124023577 / 100000) := by
  exact
    packedTile65536 2390448384 2390579456 14 6025 48892 31 _ _ (2159473 / 100000) (539869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2390579456 :
    ThetaLowerSegment 2390579456 2390710528 (239052124023577 / 100000)
      (239065115449241 / 100000) := by
  exact
    packedTile65536 2390579456 2390710528 14 6016 48893 31 _ _ (2159479 / 100000) (1079741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2390710528 :
    ThetaLowerSegment 2390710528 2390841600 (239065115449241 / 100000)
      (47815653773257 / 20000) := by
  exact
    packedTile65536 2390710528 2390841600 14 6091 48894 31 _ _ (539871 / 25000) (2159487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2390841600 :
    ThetaLowerSegment 2390841600 2390972672 (47815653773257 / 20000) (47818281872587 / 20000) := by
  exact
    packedTile65536 2390841600 2390972672 14 6085 48896 31 _ _ (215949 / 10000) (2159493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2390972672 :
    ThetaLowerSegment 2390972672 2391103744 (47818281872587 / 20000) (47820932004851 / 20000) := by
  exact
    packedTile65536 2390972672 2391103744 14 6136 48897 31 _ _ (431899 / 20000) (1079749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2391103744 :
    ThetaLowerSegment 2391103744 2391234816 (47820932004851 / 20000)
      (239117720686303 / 100000) := by
  exact
    packedTile65536 2391103744 2391234816 14 6048 48898 31 _ _ (2159501 / 100000) (134969 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2391234816 :
    ThetaLowerSegment 2391234816 2391365888 (239117720686303 / 100000)
      (239130934703517 / 100000) := by
  exact
    packedTile65536 2391234816 2391365888 14 6119 48900 31 _ _ (1079753 / 50000) (2159509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2391365888 :
    ThetaLowerSegment 2391365888 2391496960 (239130934703517 / 100000)
      (239144185469149 / 100000) := by
  exact
    packedTile65536 2391365888 2391496960 14 6136 48901 31 _ _ (269939 / 12500) (431903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2391496960 :
    ThetaLowerSegment 2391496960 2391628032 (239144185469149 / 100000)
      (239157082104673 / 100000) := by
  exact
    packedTile65536 2391496960 2391628032 14 5972 48902 31 _ _ (2159517 / 100000) (13497 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2391628032 :
    ThetaLowerSegment 2391628032 2391759104 (239157082104673 / 100000)
      (119585152432001 / 50000) := by
  exact
    packedTile65536 2391628032 2391759104 14 6123 48904 31 _ _ (2159523 / 100000) (1079763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2391759104 :
    ThetaLowerSegment 2391759104 2391890176 (119585152432001 / 50000)
      (119591550033701 / 50000) := by
  exact
    packedTile65536 2391759104 2391890176 14 5925 48905 31 _ _ (269941 / 12500) (2159531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2391890176 :
    ThetaLowerSegment 2391890176 2392021248 (119591550033701 / 50000)
      (239196193315981 / 100000) := by
  exact
    packedTile65536 2391890176 2392021248 14 6063 48906 31 _ _ (2159533 / 100000) (134971 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2392021248 :
    ThetaLowerSegment 2392021248 2392152320 (239196193315981 / 100000)
      (239209327632179 / 100000) := by
  exact
    packedTile65536 2392021248 2392152320 14 6082 48908 31 _ _ (2159539 / 100000) (1079771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2392152320 :
    ThetaLowerSegment 2392152320 2392283392 (239209327632179 / 100000)
      (239222548360547 / 100000) := by
  exact
    packedTile65536 2392152320 2392283392 14 6122 48909 31 _ _ (269943 / 12500) (2159547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2392283392 :
    ThetaLowerSegment 2392283392 2392414464 (239222548360547 / 100000)
      (239235576925697 / 100000) := by
  exact
    packedTile65536 2392283392 2392414464 14 6033 48910 31 _ _ (43191 / 2000) (2159553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2392414464 :
    ThetaLowerSegment 2392414464 2392545536 (239235576925697 / 100000)
      (59812177294913 / 25000) := by
  exact
    packedTile65536 2392414464 2392545536 14 6081 48912 31 _ _ (431911 / 20000) (1079779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2392545536 :
    ThetaLowerSegment 2392545536 2392676608 (59812177294913 / 25000)
      (239261828512727 / 100000) := by
  exact
    packedTile65536 2392545536 2392676608 14 6075 48913 31 _ _ (2159561 / 100000) (539891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2392676608 :
    ThetaLowerSegment 2392676608 2392807680 (239261828512727 / 100000)
      (239274939237913 / 100000) := by
  exact
    packedTile65536 2392676608 2392807680 14 6071 48914 31 _ _ (1079783 / 50000) (2159569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2392807680 :
    ThetaLowerSegment 2392807680 2392938752 (239274939237913 / 100000)
      (239288002488941 / 100000) := by
  exact
    packedTile65536 2392807680 2392938752 14 6049 48916 31 _ _ (539893 / 25000) (86383 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2392938752 :
    ThetaLowerSegment 2392938752 2393069824 (239288002488941 / 100000)
      (23930125581299 / 10000) := by
  exact
    packedTile65536 2392938752 2393069824 14 6137 48917 31 _ _ (2159577 / 100000) (107979 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2393069824 :
    ThetaLowerSegment 2393069824 2393200896 (23930125581299 / 10000) (14957146700321 / 6250) := by
  exact
    packedTile65536 2393069824 2393200896 14 6062 48919 31 _ _ (2159583 / 100000) (1079793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2393200896 :
    ThetaLowerSegment 2393200896 2393331968 (14957146700321 / 6250) (59831901228967 / 25000) := by
  exact
    packedTile65536 2393200896 2393331968 14 6139 48920 31 _ _ (539897 / 25000) (2159591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2393331968 :
    ThetaLowerSegment 2393331968 2393463040 (59831901228967 / 25000) (29917574089273 / 12500) := by
  exact
    packedTile65536 2393331968 2393463040 14 6014 48921 31 _ _ (1079797 / 50000) (2159597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2393463040 :
    ThetaLowerSegment 2393463040 2393594112 (29917574089273 / 12500) (1495960013366 / 625) := by
  exact
    packedTile65536 2393463040 2393594112 14 6024 48923 31 _ _ (2159599 / 100000) (1079801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2393594112 :
    ThetaLowerSegment 2393594112 2393725184 (1495960013366 / 625) (23936659000303 / 10000) := by
  exact
    packedTile65536 2393594112 2393725184 14 6014 48924 31 _ _ (431921 / 20000) (269951 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2393725184 :
    ThetaLowerSegment 2393725184 2393856256 (23936659000303 / 10000) (23937976362403 / 10000) := by
  exact
    packedTile65536 2393725184 2393856256 14 6100 48925 31 _ _ (215961 / 10000) (2159613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2393856256 :
    ThetaLowerSegment 2393856256 2393987328 (23937976362403 / 10000) (119696399533103 / 50000) := by
  exact
    packedTile65536 2393856256 2393987328 14 6036 48927 31 _ _ (67488 / 3125) (2159619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2393987328 :
    ThetaLowerSegment 2393987328 2394118400 (119696399533103 / 50000)
      (239405875571361 / 100000) := by
  exact
    packedTile65536 2393987328 2394118400 14 6055 48928 31 _ _ (2159621 / 100000) (269953 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2394118400 :
    ThetaLowerSegment 2394118400 2394249472 (239405875571361 / 100000)
      (239419252300999 / 100000) := by
  exact
    packedTile65536 2394118400 2394249472 14 6194 48929 31 _ _ (2159627 / 100000) (215963 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2394249472 :
    ThetaLowerSegment 2394249472 2394380544 (239419252300999 / 100000)
      (239432348309447 / 100000) := by
  exact
    packedTile65536 2394249472 2394380544 14 6064 48931 31 _ _ (134977 / 6250) (431927 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2394380544 :
    ThetaLowerSegment 2394380544 2394511616 (239432348309447 / 100000)
      (239445420598261 / 100000) := by
  exact
    packedTile65536 2394380544 2394511616 14 6053 48932 31 _ _ (1079819 / 50000) (2159641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2394511616 :
    ThetaLowerSegment 2394511616 2394642688 (239445420598261 / 100000)
      (239458529631271 / 100000) := by
  exact
    packedTile65536 2394511616 2394642688 14 6070 48933 31 _ _ (2159643 / 100000) (1079823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2394642688 :
    ThetaLowerSegment 2394642688 2394773760 (239458529631271 / 100000)
      (47894320396123 / 20000) := by
  exact
    packedTile65536 2394642688 2394773760 14 6053 48935 31 _ _ (67489 / 3125) (2159651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2394773760 :
    ThetaLowerSegment 2394773760 2394904832 (47894320396123 / 20000) (47896922779193 / 20000) := by
  exact
    packedTile65536 2394773760 2394904832 14 6025 48936 31 _ _ (1079827 / 50000) (2159657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2394904832 :
    ThetaLowerSegment 2394904832 2395035904 (47896922779193 / 20000) (119748836676969 / 50000) := by
  exact
    packedTile65536 2394904832 2395035904 14 6047 48937 31 _ _ (2159659 / 100000) (1079831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2395035904 :
    ThetaLowerSegment 2395035904 2395166976 (119748836676969 / 50000)
      (119755427974549 / 50000) := by
  exact
    packedTile65536 2395035904 2395166976 14 6104 48939 31 _ _ (431933 / 20000) (539917 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2395166976 :
    ThetaLowerSegment 2395166976 2395298048 (119755427974549 / 50000) (29940497532961 / 12500) := by
  exact
    packedTile65536 2395166976 2395298048 14 6077 48940 31 _ _ (215967 / 10000) (2159673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2395298048 :
    ThetaLowerSegment 2395298048 2395429120 (29940497532961 / 12500) (14971069173401 / 6250) := by
  exact
    packedTile65536 2395298048 2395429120 14 6078 48941 31 _ _ (539919 / 25000) (2159679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2395429120 :
    ThetaLowerSegment 2395429120 2395560192 (14971069173401 / 6250) (239550248433301 / 100000) := by
  exact
    packedTile65536 2395429120 2395560192 14 6085 48943 31 _ _ (2159681 / 100000) (539921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2395560192 :
    ThetaLowerSegment 2395560192 2395691264 (239550248433301 / 100000) (4791265297337 / 2000) := by
  exact
    packedTile65536 2395560192 2395691264 14 6027 48944 31 _ _ (2159687 / 100000) (215969 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2395691264 :
    ThetaLowerSegment 2395691264 2395822336 (4791265297337 / 2000) (119788175220339 / 50000) := by
  exact
    packedTile65536 2395691264 2395822336 14 6059 48945 31 _ _ (539923 / 25000) (431939 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2395822336 :
    ThetaLowerSegment 2395822336 2395953408 (119788175220339 / 50000)
      (119794729903769 / 50000) := by
  exact
    packedTile65536 2395822336 2395953408 14 6070 48947 31 _ _ (1079849 / 50000) (2159701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2395953408 :
    ThetaLowerSegment 2395953408 2396084480 (119794729903769 / 50000)
      (239602497934549 / 100000) := by
  exact
    packedTile65536 2395953408 2396084480 14 6037 48948 31 _ _ (2159703 / 100000) (1079853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2396084480 :
    ThetaLowerSegment 2396084480 2396215552 (239602497934549 / 100000)
      (239615460507967 / 100000) := by
  exact
    packedTile65536 2396084480 2396215552 14 6002 48949 31 _ _ (2159709 / 100000) (67491 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2396215552 :
    ThetaLowerSegment 2396215552 2396346624 (239615460507967 / 100000)
      (47925701899991 / 20000) := by
  exact
    packedTile65536 2396215552 2396346624 14 6042 48951 31 _ _ (1079857 / 50000) (2159717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2396346624 :
    ThetaLowerSegment 2396346624 2396477696 (47925701899991 / 20000) (47928306090367 / 20000) := by
  exact
    packedTile65536 2396346624 2396477696 14 6029 48952 31 _ _ (53993 / 2500) (2159723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2396477696 :
    ThetaLowerSegment 2396477696 2396608768 (47928306090367 / 20000) (47930896896477 / 20000) := by
  exact
    packedTile65536 2396477696 2396608768 14 5998 48953 31 _ _ (86389 / 4000) (134983 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2396608768 :
    ThetaLowerSegment 2396608768 2396739840 (47930896896477 / 20000) (59916926048959 / 25000) := by
  exact
    packedTile65536 2396608768 2396739840 14 6121 48955 31 _ _ (2159731 / 100000) (1079867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2396739840 :
    ThetaLowerSegment 2396739840 2396870912 (59916926048959 / 25000) (59920198588933 / 25000) := by
  exact
    packedTile65536 2396739840 2396870912 14 6061 48956 31 _ _ (269967 / 12500) (2159739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2396870912 :
    ThetaLowerSegment 2396870912 2397001984 (59920198588933 / 25000) (119846904477499 / 50000) := by
  exact
    packedTile65536 2396870912 2397001984 14 6026 48957 31 _ _ (2159741 / 100000) (67492 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2397001984 :
    ThetaLowerSegment 2397001984 2397133056 (119846904477499 / 50000) (59926731814569 / 25000) := by
  exact
    packedTile65536 2397001984 2397133056 14 6074 48959 31 _ _ (2159747 / 100000) (8639 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2397133056 :
    ThetaLowerSegment 2397133056 2397264128 (59926731814569 / 25000) (59930024356493 / 25000) := by
  exact
    packedTile65536 2397133056 2397264128 14 6098 48960 31 _ _ (269969 / 12500) (431951 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2397264128 :
    ThetaLowerSegment 2397264128 2397395200 (59930024356493 / 25000) (14983320587859 / 6250) := by
  exact
    packedTile65536 2397264128 2397395200 14 6034 48961 31 _ _ (1079879 / 50000) (2159761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2397395200 :
    ThetaLowerSegment 2397395200 2397526272 (14983320587859 / 6250) (23974630827957 / 10000) := by
  exact
    packedTile65536 2397395200 2397526272 14 6102 48963 31 _ _ (2159763 / 100000) (1079883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2397526272 :
    ThetaLowerSegment 2397526272 2397657344 (23974630827957 / 10000) (47951846899407 / 20000) := by
  exact
    packedTile65536 2397526272 2397657344 14 5985 48964 31 _ _ (2159769 / 100000) (539943 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2397657344 :
    ThetaLowerSegment 2397657344 2397788416 (47951846899407 / 20000)
      (239772357283859 / 100000) := by
  exact
    packedTile65536 2397657344 2397788416 14 6076 48965 31 _ _ (1079887 / 50000) (2159777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2397788416 :
    ThetaLowerSegment 2397788416 2397919488 (239772357283859 / 100000)
      (239785555699439 / 100000) := by
  exact
    packedTile65536 2397788416 2397919488 14 6111 48967 31 _ _ (107989 / 5000) (2159783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2397919488 :
    ThetaLowerSegment 2397919488 2398050560 (239785555699439 / 100000)
      (239798618079119 / 100000) := by
  exact
    packedTile65536 2397919488 2398050560 14 6048 48968 31 _ _ (431957 / 20000) (539947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2398050560 :
    ThetaLowerSegment 2398050560 2398181632 (239798618079119 / 100000)
      (239811788484637 / 100000) := by
  exact
    packedTile65536 2398050560 2398181632 14 6098 48969 31 _ _ (2159791 / 100000) (1079897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2398181632 :
    ThetaLowerSegment 2398181632 2398312704 (239811788484637 / 100000)
      (239825038833097 / 100000) := by
  exact
    packedTile65536 2398181632 2398312704 14 6135 48971 31 _ _ (539949 / 25000) (2159799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2398312704 :
    ThetaLowerSegment 2398312704 2398443776 (239825038833097 / 100000)
      (47967614215673 / 20000) := by
  exact
    packedTile65536 2398312704 2398443776 14 6034 48972 31 _ _ (1079901 / 50000) (431961 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2398443776 :
    ThetaLowerSegment 2398443776 2398574848 (47967614215673 / 20000)
      (239850952167313 / 100000) := by
  exact
    packedTile65536 2398443776 2398574848 14 5964 48973 31 _ _ (2159807 / 100000) (215981 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2398574848 :
    ThetaLowerSegment 2398574848 2398705920 (239850952167313 / 100000)
      (239864226378011 / 100000) := by
  exact
    packedTile65536 2398574848 2398705920 14 6146 48975 31 _ _ (2159813 / 100000) (269977 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2398705920 :
    ThetaLowerSegment 2398705920 2398836992 (239864226378011 / 100000)
      (239877243601097 / 100000) := by
  exact
    packedTile65536 2398705920 2398836992 14 6027 48976 31 _ _ (1079909 / 50000) (2159821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2398836992 :
    ThetaLowerSegment 2398836992 2398968064 (239877243601097 / 100000) (9595611211709 / 4000) := by
  exact
    packedTile65536 2398836992 2398968064 14 6036 48977 31 _ _ (2159823 / 100000) (1079913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2398968064 :
    ThetaLowerSegment 2398968064 2399099136 (9595611211709 / 4000) (7496981559163 / 3125) := by
  exact
    packedTile65536 2398968064 2399099136 14 6079 48979 31 _ _ (2159829 / 100000) (269979 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2399099136 :
    ThetaLowerSegment 2399099136 2399230208 (7496981559163 / 3125) (119958246003877 / 50000) := by
  exact
    packedTile65536 2399099136 2399230208 14 6057 48980 31 _ _ (1079917 / 50000) (2159837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2399230208 :
    ThetaLowerSegment 2399230208 2399361280 (119958246003877 / 50000)
      (119964794638757 / 50000) := by
  exact
    packedTile65536 2399230208 2399361280 14 6064 48981 31 _ _ (13499 / 625) (2159843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2399361280 :
    ThetaLowerSegment 2399361280 2399492352 (119964794638757 / 50000)
      (119971403764457 / 50000) := by
  exact
    packedTile65536 2399361280 2399492352 14 6120 48983 31 _ _ (431969 / 20000) (269981 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2399492352 :
    ThetaLowerSegment 2399492352 2399623424 (119971403764457 / 50000)
      (239955997738971 / 100000) := by
  exact
    packedTile65536 2399492352 2399623424 14 6107 48984 31 _ _ (2159851 / 100000) (1079927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2399623424 :
    ThetaLowerSegment 2399623424 2399754496 (239955997738971 / 100000)
      (239969248455531 / 100000) := by
  exact
    packedTile65536 2399623424 2399754496 14 6135 48985 31 _ _ (134991 / 6250) (2159859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2399754496 :
    ThetaLowerSegment 2399754496 2399885568 (239969248455531 / 100000)
      (239982494889177 / 100000) := by
  exact
    packedTile65536 2399754496 2399885568 14 6133 48987 31 _ _ (1079931 / 50000) (431973 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2399885568 :
    ThetaLowerSegment 2399885568 2400016640 (239982494889177 / 100000)
      (239995618241069 / 100000) := by
  exact
    packedTile65536 2399885568 2400016640 14 6076 48988 31 _ _ (2159867 / 100000) (215987 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2400016640 :
    ThetaLowerSegment 2400016640 2400147712 (239995618241069 / 100000)
      (240008599077799 / 100000) := by
  exact
    packedTile65536 2400016640 2400147712 14 6010 48989 31 _ _ (2159873 / 100000) (539969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2400147712 :
    ThetaLowerSegment 2400147712 2400278784 (240008599077799 / 100000)
      (240021612342749 / 100000) := by
  exact
    packedTile65536 2400147712 2400278784 14 6025 48991 31 _ _ (1079939 / 50000) (2159881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2400278784 :
    ThetaLowerSegment 2400278784 2400409856 (240021612342749 / 100000)
      (48006933336329 / 20000) := by
  exact
    packedTile65536 2400278784 2400409856 14 6044 48992 31 _ _ (539971 / 25000) (2159887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2400409856 :
    ThetaLowerSegment 2400409856 2400540928 (48006933336329 / 20000)
      (240047785847431 / 100000) := by
  exact
    packedTile65536 2400409856 2400540928 14 6074 48993 31 _ _ (2159889 / 100000) (539973 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2400540928 :
    ThetaLowerSegment 2400540928 2400672000 (240047785847431 / 100000)
      (240060797048887 / 100000) := by
  exact
    packedTile65536 2400540928 2400672000 14 6024 48995 31 _ _ (1079947 / 50000) (2159897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2400672000 :
    ThetaLowerSegment 2400672000 2400803072 (240060797048887 / 100000)
      (240073944360187 / 100000) := by
  exact
    packedTile65536 2400672000 2400803072 14 6087 48996 31 _ _ (21599 / 1000) (2159903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2400803072 :
    ThetaLowerSegment 2400803072 2400934144 (240073944360187 / 100000)
      (240087033384487 / 100000) := by
  exact
    packedTile65536 2400803072 2400934144 14 6060 48997 31 _ _ (431981 / 20000) (539977 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2400934144 :
    ThetaLowerSegment 2400934144 2401065216 (240087033384487 / 100000)
      (240099997170309 / 100000) := by
  exact
    packedTile65536 2400934144 2401065216 14 6002 48999 31 _ _ (2159911 / 100000) (1079957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2401065216 :
    ThetaLowerSegment 2401065216 2401196288 (240099997170309 / 100000)
      (240113073301773 / 100000) := by
  exact
    packedTile65536 2401065216 2401196288 14 6054 49000 31 _ _ (539979 / 25000) (2159919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2401196288 :
    ThetaLowerSegment 2401196288 2401327360 (240113073301773 / 100000)
      (240126095471511 / 100000) := by
  exact
    packedTile65536 2401196288 2401327360 14 6029 49002 31 _ _ (1079961 / 50000) (86397 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2401327360 :
    ThetaLowerSegment 2401327360 2401458432 (240126095471511 / 100000)
      (240139283985773 / 100000) := by
  exact
    packedTile65536 2401327360 2401458432 14 6106 49003 31 _ _ (2159927 / 100000) (215993 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2401458432 :
    ThetaLowerSegment 2401458432 2401589504 (240139283985773 / 100000)
      (120076183349977 / 50000) := by
  exact
    packedTile65536 2401458432 2401589504 14 6057 49004 31 _ _ (2159933 / 100000) (67498 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2401589504 :
    ThetaLowerSegment 2401589504 2401720576 (120076183349977 / 50000) (60041420679431 / 25000) := by
  exact
    packedTile65536 2401589504 2401720576 14 6165 49006 31 _ _ (1079969 / 50000) (2159941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2401720576 :
    ThetaLowerSegment 2401720576 2401851648 (60041420679431 / 25000) (60044680574913 / 25000) := by
  exact
    packedTile65536 2401720576 2401851648 14 6037 49007 31 _ _ (269993 / 12500) (2159947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2401851648 :
    ThetaLowerSegment 2401851648 2401982720 (60044680574913 / 25000) (24019172951253 / 10000) := by
  exact
    packedTile65536 2401851648 2401982720 14 6022 49008 31 _ _ (2159949 / 100000) (134997 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2401982720 :
    ThetaLowerSegment 2401982720 2402113792 (24019172951253 / 10000) (1921638533439 / 800) := by
  exact
    packedTile65536 2401982720 2402113792 14 6059 49010 31 _ _ (431991 / 20000) (1079979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2402113792 :
    ThetaLowerSegment 2402113792 2402244864 (1921638533439 / 800) (48043547944111 / 20000) := by
  exact
    packedTile65536 2402113792 2402244864 14 5983 49011 31 _ _ (53999 / 2500) (2159963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2402244864 :
    ThetaLowerSegment 2402244864 2402375936 (48043547944111 / 20000) (48046162365747 / 20000) := by
  exact
    packedTile65536 2402244864 2402375936 14 6052 49012 31 _ _ (431993 / 20000) (67499 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2402375936 :
    ThetaLowerSegment 2402375936 2402507008 (48046162365747 / 20000) (120121904187121 / 50000) := by
  exact
    packedTile65536 2402375936 2402507008 14 6017 49014 31 _ _ (2159971 / 100000) (1079987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2402507008 :
    ThetaLowerSegment 2402507008 2402638080 (120121904187121 / 50000) (24025690430873 / 10000) := by
  exact
    packedTile65536 2402507008 2402638080 14 6063 49015 31 _ _ (269997 / 12500) (2159979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2402638080 :
    ThetaLowerSegment 2402638080 2402769152 (24025690430873 / 10000) (120135055219339 / 50000) := by
  exact
    packedTile65536 2402638080 2402769152 14 6114 49016 31 _ _ (1079991 / 50000) (431997 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2402769152 :
    ThetaLowerSegment 2402769152 2402900224 (120135055219339 / 50000) (24028332091917 / 10000) := by
  exact
    packedTile65536 2402769152 2402900224 14 6116 49018 31 _ _ (2159987 / 100000) (215999 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2402900224 :
    ThetaLowerSegment 2402900224 2403031296 (24028332091917 / 10000)
      (240296499036463 / 100000) := by
  exact
    packedTile65536 2402900224 2403031296 14 6101 49019 31 _ _ (2159993 / 100000) (539999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2403031296 :
    ThetaLowerSegment 2403031296 2403162368 (240296499036463 / 100000)
      (240309560544369 / 100000) := by
  exact
    packedTile65536 2403031296 2403162368 14 6047 49020 31 _ _ (1079999 / 50000) (2160001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2403162368 :
    ThetaLowerSegment 2403162368 2403293440 (240309560544369 / 100000)
      (240322794888877 / 100000) := by
  exact
    packedTile65536 2403162368 2403293440 14 6127 49022 31 _ _ (540001 / 25000) (2160007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2403293440 :
    ThetaLowerSegment 2403293440 2403424512 (240322794888877 / 100000)
      (240335720382733 / 100000) := by
  exact
    packedTile65536 2403293440 2403424512 14 5984 49023 31 _ _ (2160009 / 100000) (540003 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2403424512 :
    ThetaLowerSegment 2403424512 2403555584 (240335720382733 / 100000)
      (120174486037379 / 50000) := by
  exact
    packedTile65536 2403424512 2403555584 14 6135 49024 31 _ _ (432003 / 20000) (1080009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2403555584 :
    ThetaLowerSegment 2403555584 2403686656 (120174486037379 / 50000)
      (120181098938609 / 50000) := by
  exact
    packedTile65536 2403555584 2403686656 14 6123 49026 31 _ _ (108001 / 5000) (2160023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2403686656 :
    ThetaLowerSegment 2403686656 2403817728 (120181098938609 / 50000) (7511723553349 / 3125) := by
  exact
    packedTile65536 2403686656 2403817728 14 5998 49027 31 _ _ (86401 / 4000) (540007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2403817728 :
    ThetaLowerSegment 2403817728 2403948800 (7511723553349 / 3125) (240388185174191 / 100000) := by
  exact
    packedTile65536 2403817728 2403948800 14 6033 49028 31 _ _ (2160031 / 100000) (1080017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2403948800 :
    ThetaLowerSegment 2403948800 2404079872 (240388185174191 / 100000)
      (240401238271739 / 100000) := by
  exact
    packedTile65536 2403948800 2404079872 14 6043 49030 31 _ _ (540009 / 25000) (2160039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2404079872 :
    ThetaLowerSegment 2404079872 2404210944 (240401238271739 / 100000)
      (240414462048863 / 100000) := by
  exact
    packedTile65536 2404079872 2404210944 14 6122 49031 31 _ _ (1080021 / 50000) (432009 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2404210944 :
    ThetaLowerSegment 2404210944 2404342016 (240414462048863 / 100000)
      (240427465531803 / 100000) := by
  exact
    packedTile65536 2404210944 2404342016 14 6020 49032 31 _ _ (2160047 / 100000) (43201 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2404342016 :
    ThetaLowerSegment 2404342016 2404473088 (240427465531803 / 100000)
      (240440572733407 / 100000) := by
  exact
    packedTile65536 2404342016 2404473088 14 6068 49034 31 _ _ (2160053 / 100000) (270007 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2404473088 :
    ThetaLowerSegment 2404473088 2404604160 (240440572733407 / 100000)
      (48090722168699 / 20000) := by
  exact
    packedTile65536 2404473088 2404604160 14 6036 49035 31 _ _ (1080029 / 50000) (2160061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2404604160 :
    ThetaLowerSegment 2404604160 2404735232 (48090722168699 / 20000)
      (240466564747303 / 100000) := by
  exact
    packedTile65536 2404604160 2404735232 14 5997 49036 31 _ _ (67502 / 3125) (2160067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2404735232 :
    ThetaLowerSegment 2404735232 2404866304 (240466564747303 / 100000) (4809593224913 / 2000) := by
  exact
    packedTile65536 2404735232 2404866304 14 6063 49038 31 _ _ (2160069 / 100000) (270009 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2404866304 :
    ThetaLowerSegment 2404866304 2404997376 (4809593224913 / 2000) (1202463821303 / 500) := by
  exact
    packedTile65536 2404866304 2404997376 14 6066 49039 31 _ _ (86403 / 4000) (1080039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2404997376 :
    ThetaLowerSegment 2404997376 2405128448 (1202463821303 / 500) (6012646682647 / 2500) := by
  exact
    packedTile65536 2404997376 2405128448 14 6066 49040 31 _ _ (27001 / 1250) (2160083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2405128448 :
    ThetaLowerSegment 2405128448 2405259520 (6012646682647 / 2500) (48103813517063 / 20000) := by
  exact
    packedTile65536 2405128448 2405259520 14 6111 49042 31 _ _ (432017 / 20000) (270011 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2405259520 :
    ThetaLowerSegment 2405259520 2405390592 (48103813517063 / 20000)
      (240532257100961 / 100000) := by
  exact
    packedTile65536 2405259520 2405390592 14 6106 49043 31 _ _ (2160091 / 100000) (1080047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2405390592 :
    ThetaLowerSegment 2405390592 2405521664 (240532257100961 / 100000)
      (48109086305293 / 20000) := by
  exact
    packedTile65536 2405390592 2405521664 14 6099 49044 31 _ _ (67503 / 3125) (2160099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2405521664 :
    ThetaLowerSegment 2405521664 2405652736 (48109086305293 / 20000)
      (240558653510807 / 100000) := by
  exact
    packedTile65536 2405521664 2405652736 14 6121 49046 31 _ _ (1080051 / 50000) (432021 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2405652736 :
    ThetaLowerSegment 2405652736 2405783808 (240558653510807 / 100000)
      (240571627113449 / 100000) := by
  exact
    packedTile65536 2405652736 2405783808 14 6006 49047 31 _ _ (2160107 / 100000) (216011 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2405783808 :
    ThetaLowerSegment 2405783808 2405914880 (240571627113449 / 100000)
      (240584769240941 / 100000) := by
  exact
    packedTile65536 2405783808 2405914880 14 6084 49048 31 _ _ (2160113 / 100000) (540029 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2405914880 :
    ThetaLowerSegment 2405914880 2406045952 (240584769240941 / 100000)
      (240597738589413 / 100000) := by
  exact
    packedTile65536 2405914880 2406045952 14 6004 49050 31 _ _ (1080059 / 50000) (2160121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2406045952 :
    ThetaLowerSegment 2406045952 2406177024 (240597738589413 / 100000)
      (48122197325981 / 20000) := by
  exact
    packedTile65536 2406045952 2406177024 14 6133 49051 31 _ _ (540031 / 25000) (2160127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2406177024 :
    ThetaLowerSegment 2406177024 2406308096 (48122197325981 / 20000)
      (240623951724163 / 100000) := by
  exact
    packedTile65536 2406177024 2406308096 14 6002 49052 31 _ _ (2160129 / 100000) (540033 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2406308096 :
    ThetaLowerSegment 2406308096 2406439168 (240623951724163 / 100000)
      (48127392442249 / 20000) := by
  exact
    packedTile65536 2406308096 2406439168 14 6023 49054 31 _ _ (1080067 / 50000) (2160137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2406439168 :
    ThetaLowerSegment 2406439168 2406570240 (48127392442249 / 20000) (48130034725497 / 20000) := by
  exact
    packedTile65536 2406439168 2406570240 14 6116 49055 31 _ _ (108007 / 5000) (2160143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2406570240 :
    ThetaLowerSegment 2406570240 2406701312 (48130034725497 / 20000) (12033160073099 / 5000) := by
  exact
    packedTile65536 2406570240 2406701312 14 6031 49056 31 _ _ (432029 / 20000) (540037 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2406701312 :
    ThetaLowerSegment 2406701312 2406832384 (12033160073099 / 5000) (120338104945651 / 50000) := by
  exact
    packedTile65536 2406701312 2406832384 14 6022 49058 31 _ _ (2160151 / 100000) (1080077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2406832384 :
    ThetaLowerSegment 2406832384 2406963456 (120338104945651 / 50000)
      (120344749585507 / 50000) := by
  exact
    packedTile65536 2406832384 2406963456 14 6152 49059 31 _ _ (540039 / 25000) (2160159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2406963456 :
    ThetaLowerSegment 2406963456 2407094528 (120344749585507 / 50000) (24070269344051 / 10000) := by
  exact
    packedTile65536 2406963456 2407094528 14 6108 49060 31 _ _ (1080081 / 50000) (432033 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2407094528 :
    ThetaLowerSegment 2407094528 2407225600 (24070269344051 / 10000) (120357818580587 / 50000) := by
  exact
    packedTile65536 2407094528 2407225600 14 5992 49062 31 _ _ (2160167 / 100000) (216017 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2407225600 :
    ThetaLowerSegment 2407225600 2407356672 (120357818580587 / 50000) (9629147125023 / 4000) := by
  exact
    packedTile65536 2407225600 2407356672 14 6037 49063 31 _ _ (2160173 / 100000) (135011 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2407356672 :
    ThetaLowerSegment 2407356672 2407487744 (9629147125023 / 4000) (48148358081207 / 20000) := by
  exact
    packedTile65536 2407356672 2407487744 14 6070 49064 31 _ _ (1080089 / 50000) (2160181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2407487744 :
    ThetaLowerSegment 2407487744 2407618816 (48148358081207 / 20000)
      (240755045288923 / 100000) := by
  exact
    packedTile65536 2407487744 2407618816 14 6136 49066 31 _ _ (2160183 / 100000) (1080093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2407618816 :
    ThetaLowerSegment 2407618816 2407749888 (240755045288923 / 100000) (9630730453009 / 4000) := by
  exact
    packedTile65536 2407618816 2407749888 14 6118 49067 31 _ _ (2160189 / 100000) (67506 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2407749888 :
    ThetaLowerSegment 2407749888 2407880960 (9630730453009 / 4000) (240781263532911 / 100000) := by
  exact
    packedTile65536 2407749888 2407880960 14 6019 49068 31 _ _ (1080097 / 50000) (2160197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2407880960 :
    ThetaLowerSegment 2407880960 2408012032 (240781263532911 / 100000)
      (240794494757911 / 100000) := by
  exact
    packedTile65536 2407880960 2408012032 14 6125 49070 31 _ _ (10801 / 500) (2160203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2408012032 :
    ThetaLowerSegment 2408012032 2408143104 (240794494757911 / 100000)
      (240807585600211 / 100000) := by
  exact
    packedTile65536 2408012032 2408143104 14 6060 49071 31 _ _ (432041 / 20000) (135013 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2408143104 :
    ThetaLowerSegment 2408143104 2408274176 (240807585600211 / 100000)
      (60205164259243 / 25000) := by
  exact
    packedTile65536 2408143104 2408274176 14 6051 49072 31 _ _ (2160211 / 100000) (1080107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2408274176 :
    ThetaLowerSegment 2408274176 2408405248 (60205164259243 / 25000) (60208506653449 / 25000) := by
  exact
    packedTile65536 2408274176 2408405248 14 6189 49074 31 _ _ (270027 / 12500) (2160219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2408405248 :
    ThetaLowerSegment 2408405248 2408536320 (60208506653449 / 25000) (120423536097227 / 50000) := by
  exact
    packedTile65536 2408405248 2408536320 14 6039 49075 31 _ _ (1080111 / 50000) (86409 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2408536320 :
    ThetaLowerSegment 2408536320 2408667392 (120423536097227 / 50000)
      (240860100523491 / 100000) := by
  exact
    packedTile65536 2408536320 2408667392 14 6031 49076 31 _ _ (2160227 / 100000) (216023 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2408667392 :
    ThetaLowerSegment 2408667392 2408798464 (240860100523491 / 100000)
      (240873154805467 / 100000) := by
  exact
    packedTile65536 2408667392 2408798464 14 6043 49078 31 _ _ (270029 / 12500) (432047 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2408798464 :
    ThetaLowerSegment 2408798464 2408929536 (240873154805467 / 100000)
      (240886232886319 / 100000) := by
  exact
    packedTile65536 2408798464 2408929536 14 6054 49079 31 _ _ (1080119 / 50000) (2160241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2408929536 :
    ThetaLowerSegment 2408929536 2409060608 (240886232886319 / 100000)
      (120449654418599 / 50000) := by
  exact
    packedTile65536 2408929536 2409060608 14 6053 49080 31 _ _ (2160243 / 100000) (1080123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2409060608 :
    ThetaLowerSegment 2409060608 2409191680 (120449654418599 / 50000) (60228096746161 / 25000) := by
  exact
    packedTile65536 2409060608 2409191680 14 6054 49082 31 _ _ (2160249 / 100000) (540063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2409191680 :
    ThetaLowerSegment 2409191680 2409322752 (60228096746161 / 25000) (120462707738259 / 50000) := by
  exact
    packedTile65536 2409191680 2409322752 14 6031 49083 31 _ _ (1080127 / 50000) (2160257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2409322752 :
    ThetaLowerSegment 2409322752 2409339136 (120462707738259 / 50000)
      (120463511354979 / 50000) := by
  exact
    packedTile65536 2409322752 2409339136 11 744 49084 31 _ _ (108013 / 5000) (2160263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2409339136 :
    ThetaLowerSegment 2409339136 2409341184 (120463511354979 / 50000)
      (120463607486549 / 50000) := by
  exact
    packedTile65536 2409339136 2409341184 8 89 49085 31 _ _ (108013 / 5000) (2160263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2377341184_2409341184 :
    ThetaLowerSegment 2377341184 2409341184 (237728310708963 / 100000)
      (120463607486549 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2377341184 cell2377472256)
                  (ThetaLowerSegment.join cell2377603328 cell2377734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2377865472 cell2377996544)
                  (ThetaLowerSegment.join cell2378127616 cell2378258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2378389760 cell2378520832)
                  (ThetaLowerSegment.join cell2378651904 cell2378782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2378914048 cell2379045120)
                  (ThetaLowerSegment.join cell2379176192 cell2379307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2379438336 cell2379569408)
                  (ThetaLowerSegment.join cell2379700480 cell2379831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2379962624 cell2380093696)
                  (ThetaLowerSegment.join cell2380224768 cell2380355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2380486912 cell2380617984)
                  (ThetaLowerSegment.join cell2380749056 cell2380880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2381011200 cell2381142272)
                  (ThetaLowerSegment.join cell2381273344 cell2381404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2381535488 cell2381666560)
                  (ThetaLowerSegment.join cell2381797632 cell2381928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2382059776 cell2382190848)
                  (ThetaLowerSegment.join cell2382321920 cell2382452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2382584064 cell2382715136)
                  (ThetaLowerSegment.join cell2382846208 cell2382977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2383108352 cell2383239424)
                  (ThetaLowerSegment.join cell2383370496 cell2383501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2383632640 cell2383763712)
                  (ThetaLowerSegment.join cell2383894784 cell2384025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2384156928 cell2384288000)
                  (ThetaLowerSegment.join cell2384419072 cell2384550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2384681216 cell2384812288)
                  (ThetaLowerSegment.join cell2384943360 cell2385074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2385205504 cell2385336576)
                  (ThetaLowerSegment.join cell2385467648 cell2385598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2385729792 cell2385860864)
                  (ThetaLowerSegment.join cell2385991936 cell2386123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2386254080 cell2386385152)
                  (ThetaLowerSegment.join cell2386516224 cell2386647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2386778368 cell2386909440)
                  (ThetaLowerSegment.join cell2387040512 cell2387171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2387302656 cell2387433728)
                  (ThetaLowerSegment.join cell2387564800 cell2387695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2387826944 cell2387958016)
                  (ThetaLowerSegment.join cell2388089088 cell2388220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2388351232 cell2388482304)
                  (ThetaLowerSegment.join cell2388613376 cell2388744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2388875520 cell2389006592)
                  (ThetaLowerSegment.join cell2389137664 cell2389268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2389399808 cell2389530880)
                  (ThetaLowerSegment.join cell2389661952 cell2389793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2389924096 cell2390055168)
                  (ThetaLowerSegment.join cell2390186240 cell2390317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2390448384 cell2390579456)
                  (ThetaLowerSegment.join cell2390710528 cell2390841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2390972672 cell2391103744)
                  (ThetaLowerSegment.join cell2391234816 cell2391365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2391496960 cell2391628032)
                  (ThetaLowerSegment.join cell2391759104 cell2391890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2392021248 cell2392152320)
                  (ThetaLowerSegment.join cell2392283392 cell2392414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2392545536 cell2392676608)
                  (ThetaLowerSegment.join cell2392807680 cell2392938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2393069824 cell2393200896)
                  (ThetaLowerSegment.join cell2393331968 cell2393463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2393594112 cell2393725184)
                  (ThetaLowerSegment.join cell2393856256 cell2393987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2394118400 cell2394249472)
                  (ThetaLowerSegment.join cell2394380544 cell2394511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2394642688 cell2394773760)
                  (ThetaLowerSegment.join cell2394904832 cell2395035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2395166976 cell2395298048)
                  (ThetaLowerSegment.join cell2395429120 cell2395560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2395691264 cell2395822336)
                  (ThetaLowerSegment.join cell2395953408 cell2396084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2396215552 cell2396346624)
                  (ThetaLowerSegment.join cell2396477696 cell2396608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2396739840 cell2396870912)
                  (ThetaLowerSegment.join cell2397001984 cell2397133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2397264128 cell2397395200)
                  (ThetaLowerSegment.join cell2397526272 cell2397657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2397788416 cell2397919488)
                  (ThetaLowerSegment.join cell2398050560 cell2398181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2398312704 cell2398443776)
                  (ThetaLowerSegment.join cell2398574848 cell2398705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2398836992 cell2398968064)
                  (ThetaLowerSegment.join cell2399099136 cell2399230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2399361280 cell2399492352)
                  (ThetaLowerSegment.join cell2399623424 cell2399754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2399885568 cell2400016640)
                  (ThetaLowerSegment.join cell2400147712 cell2400278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2400409856 cell2400540928)
                  (ThetaLowerSegment.join cell2400672000 cell2400803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2400934144 cell2401065216)
                  (ThetaLowerSegment.join cell2401196288 cell2401327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2401458432 cell2401589504)
                  (ThetaLowerSegment.join cell2401720576 cell2401851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2401982720 cell2402113792)
                  (ThetaLowerSegment.join cell2402244864 cell2402375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2402507008 cell2402638080)
                  (ThetaLowerSegment.join cell2402769152 cell2402900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2403031296 cell2403162368)
                  (ThetaLowerSegment.join cell2403293440 cell2403424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2403555584 cell2403686656)
                  (ThetaLowerSegment.join cell2403817728 cell2403948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2404079872 cell2404210944)
                  (ThetaLowerSegment.join cell2404342016 cell2404473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2404604160 cell2404735232)
                  (ThetaLowerSegment.join cell2404866304 cell2404997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2405128448 cell2405259520)
                  (ThetaLowerSegment.join cell2405390592 cell2405521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2405652736 cell2405783808)
                  (ThetaLowerSegment.join cell2405914880 cell2406045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2406177024 cell2406308096)
                  (ThetaLowerSegment.join cell2406439168 cell2406570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2406701312 cell2406832384)
                  (ThetaLowerSegment.join cell2406963456 cell2407094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2407225600 cell2407356672)
                  (ThetaLowerSegment.join cell2407487744 cell2407618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2407749888 cell2407880960)
                  (ThetaLowerSegment.join cell2408012032 cell2408143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2408274176 cell2408405248)
                  (ThetaLowerSegment.join cell2408536320 cell2408667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2408798464 cell2408929536)
                (ThetaLowerSegment.join cell2409060608 cell2409191680))
              (ThetaLowerSegment.join cell2409322752 cell2409339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
