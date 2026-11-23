/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1321341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1289341184 :
    ThetaLowerSegment 1289341184 1289472256 (1611616691067 / 1250) (64471226220537 / 50000) := by
  exact
    packedTile65536 1289341184 1289472256 14 6253 35907 30 _ _ (1048869 / 50000) (2097741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1289472256 :
    ThetaLowerSegment 1289472256 1289603328 (64471226220537 / 50000) (64477861397461 / 50000) := by
  exact
    packedTile65536 1289472256 1289603328 14 6326 35909 30 _ _ (524437 / 25000) (2097751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1289603328 :
    ThetaLowerSegment 1289603328 1289734400 (64477861397461 / 50000)
      (128968676456747 / 100000) := by
  exact
    packedTile65536 1289603328 1289734400 14 6175 35911 30 _ _ (2097759 / 100000) (1048881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1289734400 :
    ThetaLowerSegment 1289734400 1289865472 (128968676456747 / 100000)
      (64490936760763 / 50000) := by
  exact
    packedTile65536 1289734400 1289865472 14 6291 35912 30 _ _ (2097769 / 100000) (524443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1289865472 :
    ThetaLowerSegment 1289865472 1289996544 (64490936760763 / 50000)
      (128994894435779 / 100000) := by
  exact
    packedTile65536 1289865472 1289996544 14 6207 35914 30 _ _ (2097779 / 100000) (1048891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1289996544 :
    ThetaLowerSegment 1289996544 1290127616 (128994894435779 / 100000)
      (129008009812607 / 100000) := by
  exact
    packedTile65536 1289996544 1290127616 14 6252 35916 30 _ _ (2097789 / 100000) (65556 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1290127616 :
    ThetaLowerSegment 1290127616 1290258688 (129008009812607 / 100000)
      (64510601435259 / 50000) := by
  exact
    packedTile65536 1290127616 1290258688 14 6289 35918 30 _ _ (2097799 / 100000) (1048901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1290258688 :
    ThetaLowerSegment 1290258688 1290389760 (64510601435259 / 50000) (25806885072129 / 20000) := by
  exact
    packedTile65536 1290258688 1290389760 14 6303 35920 30 _ _ (2097809 / 100000) (524453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1290389760 :
    ThetaLowerSegment 1290389760 1290520832 (25806885072129 / 20000) (25809520353613 / 20000) := by
  exact
    packedTile65536 1290389760 1290520832 14 6281 35921 30 _ _ (104891 / 5000) (2097823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1290520832 :
    ThetaLowerSegment 1290520832 1290651904 (25809520353613 / 20000) (25812146836773 / 20000) := by
  exact
    packedTile65536 1290520832 1290651904 14 6260 35923 30 _ _ (209783 / 10000) (2097833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1290651904 :
    ThetaLowerSegment 1290651904 1290782976 (25812146836773 / 20000) (25814754451893 / 20000) := by
  exact
    packedTile65536 1290651904 1290782976 14 6215 35925 30 _ _ (26223 / 1250) (2097843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1290782976 :
    ThetaLowerSegment 1290782976 1290914048 (25814754451893 / 20000) (25817370470843 / 20000) := by
  exact
    packedTile65536 1290782976 1290914048 14 6235 35927 30 _ _ (41957 / 2000) (2097853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1290914048 :
    ThetaLowerSegment 1290914048 1291045120 (25817370470843 / 20000) (5164001999659 / 4000) := by
  exact
    packedTile65536 1290914048 1291045120 14 6291 35929 30 _ _ (104893 / 5000) (2097863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1291045120 :
    ThetaLowerSegment 1291045120 1291176192 (5164001999659 / 4000) (5164530662899 / 4000) := by
  exact
    packedTile65536 1291045120 1291176192 14 6300 35931 30 _ _ (209787 / 10000) (2097873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1291176192 :
    ThetaLowerSegment 1291176192 1291307264 (5164530662899 / 4000) (25825250070359 / 20000) := by
  exact
    packedTile65536 1291176192 1291307264 14 6189 35932 30 _ _ (52447 / 2500) (2097883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1291307264 :
    ThetaLowerSegment 1291307264 1291438336 (25825250070359 / 20000) (64569772343531 / 50000) := by
  exact
    packedTile65536 1291307264 1291438336 14 6337 35934 30 _ _ (2097891 / 100000) (1048947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1291438336 :
    ThetaLowerSegment 1291438336 1291569408 (64569772343531 / 50000)
      (129152717407441 / 100000) := by
  exact
    packedTile65536 1291438336 1291569408 14 6279 35936 30 _ _ (2097901 / 100000) (131119 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1291569408 :
    ThetaLowerSegment 1291569408 1291700480 (129152717407441 / 100000)
      (129165745434751 / 100000) := by
  exact
    packedTile65536 1291569408 1291700480 14 6210 35938 30 _ _ (2097911 / 100000) (1048957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1291700480 :
    ThetaLowerSegment 1291700480 1291831552 (129165745434751 / 100000)
      (64589446552829 / 50000) := by
  exact
    packedTile65536 1291700480 1291831552 14 6267 35940 30 _ _ (2097921 / 100000) (524481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1291831552 :
    ThetaLowerSegment 1291831552 1291962624 (64589446552829 / 50000)
      (129192074406131 / 100000) := by
  exact
    packedTile65536 1291831552 1291962624 14 6283 35942 30 _ _ (2097931 / 100000) (1048967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1291962624 :
    ThetaLowerSegment 1291962624 1292093696 (129192074406131 / 100000)
      (129205178145617 / 100000) := by
  exact
    packedTile65536 1291962624 1292093696 14 6246 35943 30 _ _ (2097941 / 100000) (262243 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1292093696 :
    ThetaLowerSegment 1292093696 1292224768 (129205178145617 / 100000)
      (64609167198169 / 50000) := by
  exact
    packedTile65536 1292093696 1292224768 14 6271 35945 30 _ _ (2097951 / 100000) (1048977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1292224768 :
    ThetaLowerSegment 1292224768 1292355840 (64609167198169 / 50000) (32307865336143 / 25000) := by
  exact
    packedTile65536 1292224768 1292355840 14 6257 35947 30 _ _ (1048981 / 50000) (419593 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1292355840 :
    ThetaLowerSegment 1292355840 1292486912 (32307865336143 / 25000) (6462230152059 / 5000) := by
  exact
    packedTile65536 1292355840 1292486912 14 6264 35949 30 _ _ (524493 / 25000) (83919 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1292486912 :
    ThetaLowerSegment 1292486912 1292617984 (6462230152059 / 5000) (32314404730377 / 25000) := by
  exact
    packedTile65536 1292486912 1292617984 14 6204 35951 30 _ _ (1048991 / 50000) (419597 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1292617984 :
    ThetaLowerSegment 1292617984 1292749056 (32314404730377 / 25000) (32317698053319 / 25000) := by
  exact
    packedTile65536 1292617984 1292749056 14 6279 35952 30 _ _ (262249 / 12500) (419599 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1292749056 :
    ThetaLowerSegment 1292749056 1292880128 (32317698053319 / 25000) (64641888373827 / 50000) := by
  exact
    packedTile65536 1292749056 1292880128 14 6189 35954 30 _ _ (1049001 / 50000) (419601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1292880128 :
    ThetaLowerSegment 1292880128 1293011200 (64641888373827 / 50000) (12929676973597 / 10000) := by
  exact
    packedTile65536 1292880128 1293011200 14 6193 35956 30 _ _ (524503 / 25000) (419603 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1293011200 :
    ThetaLowerSegment 1293011200 1293142272 (12929676973597 / 10000) (32327395589081 / 25000) := by
  exact
    packedTile65536 1293011200 1293142272 14 6107 35958 30 _ _ (1049011 / 50000) (83921 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1293142272 :
    ThetaLowerSegment 1293142272 1293273344 (32327395589081 / 25000) (64661246825703 / 50000) := by
  exact
    packedTile65536 1293142272 1293273344 14 6154 35960 30 _ _ (2098033 / 100000) (524509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1293273344 :
    ThetaLowerSegment 1293273344 1293404416 (64661246825703 / 50000) (64667855661153 / 50000) := by
  exact
    packedTile65536 1293273344 1293404416 14 6300 35962 30 _ _ (2098043 / 100000) (1049023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1293404416 :
    ThetaLowerSegment 1293404416 1293535488 (64667855661153 / 50000) (32337180861753 / 25000) := by
  exact
    packedTile65536 1293404416 1293535488 14 6202 35963 30 _ _ (2098053 / 100000) (262257 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1293535488 :
    ThetaLowerSegment 1293535488 1293666560 (32337180861753 / 25000) (161702363613 / 125) := by
  exact
    packedTile65536 1293535488 1293666560 14 6276 35965 30 _ _ (2098063 / 100000) (1049033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1293666560 :
    ThetaLowerSegment 1293666560 1293797632 (161702363613 / 125) (129375106652227 / 100000) := by
  exact
    packedTile65536 1293666560 1293797632 14 6299 35967 30 _ _ (2098073 / 100000) (524519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1293797632 :
    ThetaLowerSegment 1293797632 1293928704 (129375106652227 / 100000)
      (129388261632637 / 100000) := by
  exact
    packedTile65536 1293797632 1293928704 14 6270 35969 30 _ _ (2098083 / 100000) (1049043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1293928704 :
    ThetaLowerSegment 1293928704 1294059776 (129388261632637 / 100000)
      (32350356791553 / 25000) := by
  exact
    packedTile65536 1293928704 1294059776 14 6275 35971 30 _ _ (2098093 / 100000) (131131 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1294059776 :
    ThetaLowerSegment 1294059776 1294190848 (32350356791553 / 25000) (6470728799199 / 5000) := by
  exact
    packedTile65536 1294059776 1294190848 14 6267 35973 30 _ _ (262263 / 12500) (2098107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1294190848 :
    ThetaLowerSegment 1294190848 1294321920 (6470728799199 / 5000) (64713801586903 / 50000) := by
  exact
    packedTile65536 1294190848 1294321920 14 6209 35974 30 _ _ (1049057 / 50000) (2098117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1294321920 :
    ThetaLowerSegment 1294321920 1294452992 (64713801586903 / 50000) (64720341439411 / 50000) := by
  exact
    packedTile65536 1294321920 1294452992 14 6234 35976 30 _ _ (524531 / 25000) (2098127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1294452992 :
    ThetaLowerSegment 1294452992 1294584064 (64720341439411 / 50000) (8090852428517 / 6250) := by
  exact
    packedTile65536 1294452992 1294584064 14 6175 35978 30 _ _ (1049067 / 50000) (2098137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1294584064 :
    ThetaLowerSegment 1294584064 1294715136 (8090852428517 / 6250) (8091671229213 / 6250) := by
  exact
    packedTile65536 1294584064 1294715136 14 6244 35980 30 _ _ (65567 / 3125) (2098147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1294715136 :
    ThetaLowerSegment 1294715136 1294846208 (8091671229213 / 6250) (16184980067623 / 12500) := by
  exact
    packedTile65536 1294715136 1294846208 14 6244 35982 30 _ _ (1049077 / 50000) (2098157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1294846208 :
    ThetaLowerSegment 1294846208 1294977280 (16184980067623 / 12500) (16186631322691 / 12500) := by
  exact
    packedTile65536 1294846208 1294977280 14 6296 35983 30 _ _ (524541 / 25000) (2098167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1294977280 :
    ThetaLowerSegment 1294977280 1295108352 (16186631322691 / 12500) (64753045366469 / 50000) := by
  exact
    packedTile65536 1294977280 1295108352 14 6215 35985 30 _ _ (1049087 / 50000) (2098177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1295108352 :
    ThetaLowerSegment 1295108352 1295239424 (64753045366469 / 50000) (64759474205309 / 50000) := by
  exact
    packedTile65536 1295108352 1295239424 14 6128 35987 30 _ _ (419637 / 20000) (524547 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1295239424 :
    ThetaLowerSegment 1295239424 1295304960 (64759474205309 / 50000) (4047672892079 / 3125) := by
  exact
    packedTile65536 1295239424 1295304960 13 3138 35989 30 _ _ (419639 / 20000) (1049099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1295304960 :
    ThetaLowerSegment 1295304960 1295370496 (4047672892079 / 3125) (16191525340541 / 12500) := by
  exact
    packedTile65536 1295304960 1295370496 13 3179 35990 30 _ _ (10491 / 500) (2098203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1295370496 :
    ThetaLowerSegment 1295370496 1295501568 (16191525340541 / 12500)
      (129545259854043 / 100000) := by
  exact
    packedTile65536 1295370496 1295501568 14 6223 35991 30 _ _ (419641 / 20000) (65569 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1295501568 :
    ThetaLowerSegment 1295501568 1295567104 (129545259854043 / 100000)
      (16193978670651 / 12500) := by
  exact
    packedTile65536 1295501568 1295567104 13 3131 35993 30 _ _ (419643 / 20000) (1049109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1295567104 :
    ThetaLowerSegment 1295567104 1295698176 (16193978670651 / 12500) (32391240531047 / 25000) := by
  exact
    packedTile65536 1295567104 1295698176 14 6259 35993 30 _ _ (104911 / 5000) (2098223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1295698176 :
    ThetaLowerSegment 1295698176 1295829248 (32391240531047 / 25000) (64788999213589 / 50000) := by
  exact
    packedTile65536 1295698176 1295829248 14 6213 35995 30 _ _ (209823 / 10000) (2098233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1295829248 :
    ThetaLowerSegment 1295829248 1295894784 (64788999213589 / 50000) (64792266173269 / 50000) := by
  exact
    packedTile65536 1295829248 1295894784 13 3114 35997 30 _ _ (13114 / 625) (2098243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1295894784 :
    ThetaLowerSegment 1295894784 1295960320 (64792266173269 / 50000)
      (129591013825343 / 100000) := by
  exact
    packedTile65536 1295894784 1295960320 13 3089 35998 30 _ _ (419649 / 20000) (262281 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1295960320 :
    ThetaLowerSegment 1295960320 1296025856 (129591013825343 / 100000)
      (129597449158093 / 100000) := by
  exact
    packedTile65536 1295960320 1296025856 13 3067 35999 30 _ _ (8393 / 400) (2098253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296025856 :
    ThetaLowerSegment 1296025856 1296091392 (129597449158093 / 100000)
      (32401024632047 / 25000) := by
  exact
    packedTile65536 1296025856 1296091392 13 3169 36000 30 _ _ (419651 / 20000) (1049129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296091392 :
    ThetaLowerSegment 1296091392 1296156928 (32401024632047 / 25000) (16201325129491 / 12500) := by
  exact
    packedTile65536 1296091392 1296156928 13 3099 36001 30 _ _ (104913 / 5000) (2098263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296156928 :
    ThetaLowerSegment 1296156928 1296222464 (16201325129491 / 12500)
      (129616994449383 / 100000) := by
  exact
    packedTile65536 1296156928 1296222464 13 3047 36002 30 _ _ (419653 / 20000) (524567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296222464 :
    ThetaLowerSegment 1296222464 1296288000 (129616994449383 / 100000)
      (64811784166213 / 50000) := by
  exact
    packedTile65536 1296222464 1296288000 13 3133 36003 30 _ _ (2098271 / 100000) (1049137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296288000 :
    ThetaLowerSegment 1296288000 1296353536 (64811784166213 / 50000) (64815092098327 / 50000) := by
  exact
    packedTile65536 1296288000 1296353536 13 3153 36003 30 _ _ (524569 / 25000) (2098279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296353536 :
    ThetaLowerSegment 1296353536 1296419072 (64815092098327 / 50000)
      (129636737128217 / 100000) := by
  exact
    packedTile65536 1296353536 1296419072 13 3123 36004 30 _ _ (2098281 / 100000) (524571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296419072 :
    ThetaLowerSegment 1296419072 1296484608 (129636737128217 / 100000)
      (129643323647971 / 100000) := by
  exact
    packedTile65536 1296419072 1296484608 13 3139 36005 30 _ _ (1049143 / 50000) (2098289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296484608 :
    ThetaLowerSegment 1296484608 1296550144 (129643323647971 / 100000)
      (12964993116633 / 10000) := by
  exact
    packedTile65536 1296484608 1296550144 13 3149 36006 30 _ _ (2098291 / 100000) (1049147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296550144 :
    ThetaLowerSegment 1296550144 1296615680 (12964993116633 / 10000) (12965639391801 / 10000) := by
  exact
    packedTile65536 1296550144 1296615680 13 3080 36007 30 _ _ (262287 / 12500) (2098299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296615680 :
    ThetaLowerSegment 1296615680 1296681216 (12965639391801 / 10000)
      (129662896552809 / 100000) := by
  exact
    packedTile65536 1296615680 1296681216 13 3099 36008 30 _ _ (2098301 / 100000) (65572 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296681216 :
    ThetaLowerSegment 1296681216 1296746752 (129662896552809 / 100000)
      (25933893269779 / 20000) := by
  exact
    packedTile65536 1296681216 1296746752 13 3131 36009 30 _ _ (1049153 / 50000) (2098309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296746752 :
    ThetaLowerSegment 1296746752 1296812288 (25933893269779 / 20000) (64837994998897 / 50000) := by
  exact
    packedTile65536 1296746752 1296812288 13 3109 36010 30 _ _ (2098311 / 100000) (1049157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296812288 :
    ThetaLowerSegment 1296812288 1296877824 (64837994998897 / 50000) (64841250536171 / 50000) := by
  exact
    packedTile65536 1296812288 1296877824 13 3103 36011 30 _ _ (524579 / 25000) (2098319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296877824 :
    ThetaLowerSegment 1296877824 1296943360 (64841250536171 / 50000)
      (129689142258307 / 100000) := by
  exact
    packedTile65536 1296877824 1296943360 13 3165 36012 30 _ _ (2098321 / 100000) (524581 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296943360 :
    ThetaLowerSegment 1296943360 1297008896 (129689142258307 / 100000)
      (129695749886881 / 100000) := by
  exact
    packedTile65536 1296943360 1297008896 13 3149 36013 30 _ _ (1049163 / 50000) (2098329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297008896 :
    ThetaLowerSegment 1297008896 1297074432 (129695749886881 / 100000)
      (64851117914001 / 50000) := by
  exact
    packedTile65536 1297008896 1297074432 13 3091 36014 30 _ _ (2098331 / 100000) (1049167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297074432 :
    ThetaLowerSegment 1297074432 1297139968 (64851117914001 / 50000) (64854367187297 / 50000) := by
  exact
    packedTile65536 1297074432 1297139968 13 3097 36014 30 _ _ (65573 / 3125) (2098339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297139968 :
    ThetaLowerSegment 1297139968 1297205504 (64854367187297 / 50000) (64857690959441 / 50000) := by
  exact
    packedTile65536 1297139968 1297205504 13 3168 36015 30 _ _ (2098341 / 100000) (262293 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297205504 :
    ThetaLowerSegment 1297205504 1297271040 (64857690959441 / 50000) (6486099900191 / 5000) := by
  exact
    packedTile65536 1297205504 1297271040 13 3153 36016 30 _ _ (1049173 / 50000) (2098349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297271040 :
    ThetaLowerSegment 1297271040 1297336576 (6486099900191 / 5000) (129728404269423 / 100000) := by
  exact
    packedTile65536 1297271040 1297336576 13 3053 36017 30 _ _ (2098351 / 100000) (1049177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297336576 :
    ThetaLowerSegment 1297336576 1297402112 (129728404269423 / 100000)
      (129734972123703 / 100000) := by
  exact
    packedTile65536 1297336576 1297402112 13 3130 36018 30 _ _ (524589 / 25000) (2098359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297402112 :
    ThetaLowerSegment 1297402112 1297467648 (129734972123703 / 100000)
      (64870687111557 / 50000) := by
  exact
    packedTile65536 1297402112 1297467648 13 3051 36019 30 _ _ (2098361 / 100000) (524591 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297467648 :
    ThetaLowerSegment 1297467648 1297533184 (64870687111557 / 50000)
      (129747931619989 / 100000) := by
  exact
    packedTile65536 1297467648 1297533184 13 3125 36020 30 _ _ (2098367 / 100000) (209837 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297533184 :
    ThetaLowerSegment 1297533184 1297598720 (129747931619989 / 100000)
      (129754428179701 / 100000) := by
  exact
    packedTile65536 1297533184 1297598720 13 3096 36021 30 _ _ (524593 / 25000) (16787 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297598720 :
    ThetaLowerSegment 1297598720 1297664256 (129754428179701 / 100000)
      (129761033870497 / 100000) := by
  exact
    packedTile65536 1297598720 1297664256 13 3148 36022 30 _ _ (2098377 / 100000) (104919 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297664256 :
    ThetaLowerSegment 1297664256 1297729792 (129761033870497 / 100000)
      (129767561936899 / 100000) := by
  exact
    packedTile65536 1297664256 1297729792 13 3111 36023 30 _ _ (1049191 / 50000) (419677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297729792 :
    ThetaLowerSegment 1297729792 1297795328 (129767561936899 / 100000)
      (32443495225683 / 25000) := by
  exact
    packedTile65536 1297729792 1297795328 13 3059 36024 30 _ _ (2098387 / 100000) (209839 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297795328 :
    ThetaLowerSegment 1297795328 1297860864 (32443495225683 / 25000) (32445151381569 / 25000) := by
  exact
    packedTile65536 1297795328 1297860864 13 3157 36024 30 _ _ (262299 / 12500) (419679 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297860864 :
    ThetaLowerSegment 1297860864 1297926400 (32445151381569 / 25000) (16223390918019 / 12500) := by
  exact
    packedTile65536 1297860864 1297926400 13 3108 36025 30 _ _ (2098397 / 100000) (2623 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297926400 :
    ThetaLowerSegment 1297926400 1297991936 (16223390918019 / 12500) (16224211393201 / 12500) := by
  exact
    packedTile65536 1297926400 1297991936 13 3128 36026 30 _ _ (1049201 / 50000) (419681 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1297991936 :
    ThetaLowerSegment 1297991936 1298057472 (16224211393201 / 12500) (16225038165559 / 12500) := by
  exact
    packedTile65536 1297991936 1298057472 13 3152 36027 30 _ _ (2098407 / 100000) (209841 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298057472 :
    ThetaLowerSegment 1298057472 1298123008 (16225038165559 / 12500) (32451741945643 / 25000) := by
  exact
    packedTile65536 1298057472 1298123008 13 3175 36028 30 _ _ (524603 / 25000) (419683 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298123008 :
    ThetaLowerSegment 1298123008 1298188544 (32451741945643 / 25000) (32453382907737 / 25000) := by
  exact
    packedTile65536 1298123008 1298188544 13 3128 36029 30 _ _ (2098417 / 100000) (104921 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298188544 :
    ThetaLowerSegment 1298188544 1298254080 (32453382907737 / 25000) (64910000532987 / 50000) := by
  exact
    packedTile65536 1298188544 1298254080 13 3083 36030 30 _ _ (1049211 / 50000) (83937 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298254080 :
    ThetaLowerSegment 1298254080 1298319616 (64910000532987 / 50000)
      (129826319429671 / 100000) := by
  exact
    packedTile65536 1298254080 1298319616 13 3011 36031 30 _ _ (2098427 / 100000) (209843 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298319616 :
    ThetaLowerSegment 1298319616 1298385152 (129826319429671 / 100000)
      (129832992443431 / 100000) := by
  exact
    packedTile65536 1298319616 1298385152 13 3180 36032 30 _ _ (65576 / 3125) (419687 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298385152 :
    ThetaLowerSegment 1298385152 1298450688 (129832992443431 / 100000)
      (64919802309209 / 50000) := by
  exact
    packedTile65536 1298385152 1298450688 13 3151 36033 30 _ _ (2098437 / 100000) (52461 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298450688 :
    ThetaLowerSegment 1298450688 1298516224 (64919802309209 / 50000) (8115389075183 / 6250) := by
  exact
    packedTile65536 1298450688 1298516224 13 3155 36034 30 _ _ (1049221 / 50000) (419689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298516224 :
    ThetaLowerSegment 1298516224 1298581760 (8115389075183 / 6250) (64926388277231 / 50000) := by
  exact
    packedTile65536 1298516224 1298581760 13 3122 36034 30 _ _ (2098447 / 100000) (41969 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298581760 :
    ThetaLowerSegment 1298581760 1298647296 (64926388277231 / 50000) (12985930064173 / 10000) := by
  exact
    packedTile65536 1298581760 1298647296 13 3109 36035 30 _ _ (524613 / 25000) (419691 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298647296 :
    ThetaLowerSegment 1298647296 1298712832 (12985930064173 / 10000) (64932949095269 / 50000) := by
  exact
    packedTile65536 1298647296 1298712832 13 3144 36036 30 _ _ (2098457 / 100000) (104923 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298712832 :
    ThetaLowerSegment 1298712832 1298778368 (64932949095269 / 50000) (1298725104443 / 1000) := by
  exact
    packedTile65536 1298712832 1298778368 13 3151 36037 30 _ _ (1049231 / 50000) (419693 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298778368 :
    ThetaLowerSegment 1298778368 1298843904 (1298725104443 / 1000) (8117440579217 / 6250) := by
  exact
    packedTile65536 1298778368 1298843904 13 3116 36038 30 _ _ (2098467 / 100000) (209847 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298843904 :
    ThetaLowerSegment 1298843904 1298909440 (8117440579217 / 6250) (25977132311179 / 20000) := by
  exact
    packedTile65536 1298843904 1298909440 13 3151 36039 30 _ _ (2098473 / 100000) (524619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298909440 :
    ThetaLowerSegment 1298909440 1298974976 (25977132311179 / 20000)
      (129892120671179 / 100000) := by
  exact
    packedTile65536 1298909440 1298974976 13 3078 36040 30 _ _ (1049239 / 50000) (2098481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1298974976 :
    ThetaLowerSegment 1298974976 1299040512 (129892120671179 / 100000)
      (25979738623987 / 20000) := by
  exact
    packedTile65536 1298974976 1299040512 13 3132 36041 30 _ _ (2098483 / 100000) (1049243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299040512 :
    ThetaLowerSegment 1299040512 1299106048 (25979738623987 / 20000)
      (129905232008543 / 100000) := by
  exact
    packedTile65536 1299040512 1299106048 13 3116 36042 30 _ _ (262311 / 12500) (2098491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299106048 :
    ThetaLowerSegment 1299106048 1299171584 (129905232008543 / 100000)
      (64955880210133 / 50000) := by
  exact
    packedTile65536 1299106048 1299171584 13 3111 36043 30 _ _ (2098493 / 100000) (65578 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299171584 :
    ThetaLowerSegment 1299171584 1299237120 (64955880210133 / 50000) (64959072025591 / 50000) := by
  exact
    packedTile65536 1299171584 1299237120 13 3042 36044 30 _ _ (1049249 / 50000) (2098501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299237120 :
    ThetaLowerSegment 1299237120 1299302656 (64959072025591 / 50000) (2598495338533 / 2000) := by
  exact
    packedTile65536 1299237120 1299302656 13 3156 36044 30 _ _ (2098503 / 100000) (1049253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299302656 :
    ThetaLowerSegment 1299302656 1299368192 (2598495338533 / 2000) (2598628593791 / 2000) := by
  exact
    packedTile65536 1299302656 1299368192 13 3175 36045 30 _ _ (524627 / 25000) (2098511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299368192 :
    ThetaLowerSegment 1299368192 1299433728 (2598628593791 / 2000) (32484497410297 / 25000) := by
  exact
    packedTile65536 1299368192 1299433728 13 3126 36046 30 _ _ (2098513 / 100000) (524629 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299433728 :
    ThetaLowerSegment 1299433728 1299499264 (32484497410297 / 25000) (64972286346077 / 50000) := by
  exact
    packedTile65536 1299433728 1299499264 13 3137 36047 30 _ _ (1049259 / 50000) (2098521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299499264 :
    ThetaLowerSegment 1299499264 1299564800 (64972286346077 / 50000)
      (129951097000161 / 100000) := by
  exact
    packedTile65536 1299499264 1299564800 13 3109 36048 30 _ _ (2098523 / 100000) (1049263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299564800 :
    ThetaLowerSegment 1299564800 1299630336 (129951097000161 / 100000)
      (129957736742753 / 100000) := by
  exact
    packedTile65536 1299564800 1299630336 13 3164 36049 30 _ _ (65579 / 3125) (2098531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299630336 :
    ThetaLowerSegment 1299630336 1299695872 (129957736742753 / 100000)
      (64982138935057 / 50000) := by
  exact
    packedTile65536 1299630336 1299695872 13 3117 36050 30 _ _ (2098533 / 100000) (262317 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299695872 :
    ThetaLowerSegment 1299695872 1299761408 (64982138935057 / 50000) (16246348704191 / 12500) := by
  exact
    packedTile65536 1299695872 1299761408 13 3103 36051 30 _ _ (1049269 / 50000) (2098541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299761408 :
    ThetaLowerSegment 1299761408 1299826944 (16246348704191 / 12500) (25995433421141 / 20000) := by
  exact
    packedTile65536 1299761408 1299826944 13 3039 36052 30 _ _ (2098543 / 100000) (1049273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299826944 :
    ThetaLowerSegment 1299826944 1299892480 (25995433421141 / 20000)
      (129983645323381 / 100000) := by
  exact
    packedTile65536 1299826944 1299892480 13 3087 36053 30 _ _ (524637 / 25000) (2098551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299892480 :
    ThetaLowerSegment 1299892480 1299958016 (129983645323381 / 100000)
      (64995093256541 / 50000) := by
  exact
    packedTile65536 1299892480 1299958016 13 3117 36054 30 _ _ (2098553 / 100000) (524639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1299958016 :
    ThetaLowerSegment 1299958016 1300023552 (64995093256541 / 50000) (64998423668087 / 50000) := by
  exact
    packedTile65536 1299958016 1300023552 13 3174 36054 30 _ _ (1049279 / 50000) (2098561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300023552 :
    ThetaLowerSegment 1300023552 1300089088 (64998423668087 / 50000) (8125200373879 / 6250) := by
  exact
    packedTile65536 1300023552 1300089088 13 3030 36055 30 _ _ (2098563 / 100000) (1049283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300089088 :
    ThetaLowerSegment 1300089088 1300154624 (8125200373879 / 6250) (4062808600974 / 3125) := by
  exact
    packedTile65536 1300089088 1300154624 13 3178 36056 30 _ _ (262321 / 12500) (2098571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300154624 :
    ThetaLowerSegment 1300154624 1300220160 (4062808600974 / 3125) (130016550791881 / 100000) := by
  exact
    packedTile65536 1300154624 1300220160 13 3181 36057 30 _ _ (2098573 / 100000) (131161 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300220160 :
    ThetaLowerSegment 1300220160 1300285696 (130016550791881 / 100000)
      (130023127735333 / 100000) := by
  exact
    packedTile65536 1300220160 1300285696 13 3134 36058 30 _ _ (1049289 / 50000) (2098581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300285696 :
    ThetaLowerSegment 1300285696 1300351232 (130023127735333 / 100000)
      (65014853396519 / 50000) := by
  exact
    packedTile65536 1300285696 1300351232 13 3135 36059 30 _ _ (2098583 / 100000) (1049293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300351232 :
    ThetaLowerSegment 1300351232 1300416768 (65014853396519 / 50000)
      (130036252292129 / 100000) := by
  exact
    packedTile65536 1300351232 1300416768 13 3119 36060 30 _ _ (2098589 / 100000) (65581 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300416768 :
    ThetaLowerSegment 1300416768 1300482304 (130036252292129 / 100000)
      (130042877553387 / 100000) := by
  exact
    packedTile65536 1300416768 1300482304 13 3157 36061 30 _ _ (1049297 / 50000) (2098597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300482304 :
    ThetaLowerSegment 1300482304 1300547840 (130042877553387 / 100000)
      (130049475548643 / 100000) := by
  exact
    packedTile65536 1300482304 1300547840 13 3144 36062 30 _ _ (2098599 / 100000) (1049301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300547840 :
    ThetaLowerSegment 1300547840 1300613376 (130049475548643 / 100000)
      (130055895178279 / 100000) := by
  exact
    packedTile65536 1300547840 1300613376 13 3059 36063 30 _ _ (524651 / 25000) (2098607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300613376 :
    ThetaLowerSegment 1300613376 1300678912 (130055895178279 / 100000)
      (65031253947619 / 50000) := by
  exact
    packedTile65536 1300613376 1300678912 13 3151 36064 30 _ _ (2098609 / 100000) (524653 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300678912 :
    ThetaLowerSegment 1300678912 1300744448 (65031253947619 / 50000) (520276541273 / 400) := by
  exact
    packedTile65536 1300678912 1300744448 13 3158 36064 30 _ _ (1049307 / 50000) (2098617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300744448 :
    ThetaLowerSegment 1300744448 1300809984 (520276541273 / 400) (65037837307527 / 50000) := by
  exact
    packedTile65536 1300744448 1300809984 13 3116 36065 30 _ _ (2098619 / 100000) (1049311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300809984 :
    ThetaLowerSegment 1300809984 1300875520 (65037837307527 / 50000) (65041117456839 / 50000) := by
  exact
    packedTile65536 1300809984 1300875520 13 3126 36066 30 _ _ (65582 / 3125) (2098627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300875520 :
    ThetaLowerSegment 1300875520 1300941056 (65041117456839 / 50000) (13008875745261 / 10000) := by
  exact
    packedTile65536 1300875520 1300941056 13 3108 36067 30 _ _ (2098629 / 100000) (262329 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300941056 :
    ThetaLowerSegment 1300941056 1301006592 (13008875745261 / 10000) (65047686173489 / 50000) := by
  exact
    packedTile65536 1300941056 1301006592 13 3152 36068 30 _ _ (1049317 / 50000) (2098637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301006592 :
    ThetaLowerSegment 1301006592 1301072128 (65047686173489 / 50000) (13010181097143 / 10000) := by
  exact
    packedTile65536 1301006592 1301072128 13 3068 36069 30 _ _ (2098639 / 100000) (1049321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301072128 :
    ThetaLowerSegment 1301072128 1301137664 (13010181097143 / 10000) (65054211899337 / 50000) := by
  exact
    packedTile65536 1301072128 1301137664 13 3151 36070 30 _ _ (524661 / 25000) (2098647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301137664 :
    ThetaLowerSegment 1301137664 1301203200 (65054211899337 / 50000)
      (130115028247077 / 100000) := by
  exact
    packedTile65536 1301137664 1301203200 13 3147 36071 30 _ _ (2098649 / 100000) (524663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301203200 :
    ThetaLowerSegment 1301203200 1301268736 (130115028247077 / 100000)
      (130121510989283 / 100000) := by
  exact
    packedTile65536 1301203200 1301268736 13 3089 36072 30 _ _ (1049327 / 50000) (2098657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301268736 :
    ThetaLowerSegment 1301268736 1301334272 (130121510989283 / 100000) (3253202676863 / 2500) := by
  exact
    packedTile65536 1301268736 1301334272 13 3143 36073 30 _ _ (2098659 / 100000) (1049331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301334272 :
    ThetaLowerSegment 1301334272 1301399808 (3253202676863 / 2500) (8133413177141 / 6250) := by
  exact
    packedTile65536 1301334272 1301399808 13 3099 36074 30 _ _ (262333 / 12500) (2098667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301399808 :
    ThetaLowerSegment 1301399808 1301465344 (8133413177141 / 6250) (26028240550717 / 20000) := by
  exact
    packedTile65536 1301399808 1301465344 13 3141 36074 30 _ _ (2098669 / 100000) (131167 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301465344 :
    ThetaLowerSegment 1301465344 1301530880 (26028240550717 / 20000)
      (130147832464751 / 100000) := by
  exact
    packedTile65536 1301465344 1301530880 13 3159 36075 30 _ _ (1049337 / 50000) (2098677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301530880 :
    ThetaLowerSegment 1301530880 1301596416 (130147832464751 / 100000) (4067326943491 / 3125) := by
  exact
    packedTile65536 1301530880 1301596416 13 3159 36076 30 _ _ (2098679 / 100000) (1049341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301596416 :
    ThetaLowerSegment 1301596416 1301661952 (4067326943491 / 3125) (8135062605691 / 6250) := by
  exact
    packedTile65536 1301596416 1301661952 13 3116 36077 30 _ _ (524671 / 25000) (2098687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301661952 :
    ThetaLowerSegment 1301661952 1301727488 (8135062605691 / 6250) (130167576883693 / 100000) := by
  exact
    packedTile65536 1301661952 1301727488 13 3133 36078 30 _ _ (2098689 / 100000) (524673 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301727488 :
    ThetaLowerSegment 1301727488 1301793024 (130167576883693 / 100000)
      (130174133203749 / 100000) := by
  exact
    packedTile65536 1301727488 1301793024 13 3124 36079 30 _ _ (1049347 / 50000) (2098697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301793024 :
    ThetaLowerSegment 1301793024 1301858560 (130174133203749 / 100000) (8136290604009 / 6250) := by
  exact
    packedTile65536 1301793024 1301858560 13 3105 36080 30 _ _ (2098699 / 100000) (1049351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301858560 :
    ThetaLowerSegment 1301858560 1301924096 (8136290604009 / 6250) (325467962571 / 250) := by
  exact
    packedTile65536 1301858560 1301924096 13 3114 36081 30 _ _ (131169 / 6250) (2098707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301924096 :
    ThetaLowerSegment 1301924096 1301989632 (325467962571 / 250) (4068556254974 / 3125) := by
  exact
    packedTile65536 1301924096 1301989632 13 3152 36082 30 _ _ (2098709 / 100000) (262339 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1301989632 :
    ThetaLowerSegment 1301989632 1302055168 (4068556254974 / 3125) (32550092283497 / 25000) := by
  exact
    packedTile65536 1301989632 1302055168 13 3130 36083 30 _ _ (1049357 / 50000) (2098717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302055168 :
    ThetaLowerSegment 1302055168 1302120704 (32550092283497 / 25000) (5208276937337 / 4000) := by
  exact
    packedTile65536 1302055168 1302120704 13 3123 36084 30 _ _ (2098719 / 100000) (1049361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302120704 :
    ThetaLowerSegment 1302120704 1302186240 (5208276937337 / 4000) (520853860637 / 400) := by
  exact
    packedTile65536 1302120704 1302186240 13 3117 36084 30 _ _ (83949 / 4000) (262341 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302186240 :
    ThetaLowerSegment 1302186240 1302251776 (520853860637 / 400) (13022006356637 / 10000) := by
  exact
    packedTile65536 1302186240 1302251776 13 3144 36085 30 _ _ (209873 / 10000) (2098733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302251776 :
    ThetaLowerSegment 1302251776 1302317312 (13022006356637 / 10000) (3255663296691 / 2500) := by
  exact
    packedTile65536 1302251776 1302317312 13 3082 36086 30 _ _ (419747 / 20000) (1049369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302317312 :
    ThetaLowerSegment 1302317312 1302382848 (3255663296691 / 2500) (3255827837907 / 2500) := by
  exact
    packedTile65536 1302317312 1302382848 13 3136 36087 30 _ _ (104937 / 5000) (2098743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302382848 :
    ThetaLowerSegment 1302382848 1302448384 (3255827837907 / 2500) (6511980981289 / 5000) := by
  exact
    packedTile65536 1302382848 1302448384 13 3100 36088 30 _ _ (419749 / 20000) (524687 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302448384 :
    ThetaLowerSegment 1302448384 1302513920 (6511980981289 / 5000) (3256150730207 / 2500) := by
  exact
    packedTile65536 1302448384 1302513920 13 3054 36089 30 _ _ (1679 / 80) (2098753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302513920 :
    ThetaLowerSegment 1302513920 1302579456 (3256150730207 / 2500) (1042021441303 / 800) := by
  exact
    packedTile65536 1302513920 1302579456 13 3169 36090 30 _ _ (419751 / 20000) (1049379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302579456 :
    ThetaLowerSegment 1302579456 1302644992 (1042021441303 / 800) (26051829708239 / 20000) := by
  exact
    packedTile65536 1302579456 1302644992 13 3082 36091 30 _ _ (52469 / 2500) (2098763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302644992 :
    ThetaLowerSegment 1302644992 1302710528 (26051829708239 / 20000) (13026564421887 / 10000) := by
  exact
    packedTile65536 1302644992 1302710528 13 3095 36092 30 _ _ (419753 / 20000) (131173 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302710528 :
    ThetaLowerSegment 1302710528 1302776064 (13026564421887 / 10000) (13027232250501 / 10000) := by
  exact
    packedTile65536 1302710528 1302776064 13 3182 36093 30 _ _ (209877 / 10000) (2098773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302776064 :
    ThetaLowerSegment 1302776064 1302841600 (13027232250501 / 10000) (13027883710261 / 10000) := by
  exact
    packedTile65536 1302776064 1302841600 13 3104 36093 30 _ _ (83951 / 4000) (1049389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302841600 :
    ThetaLowerSegment 1302841600 1302907136 (13027883710261 / 10000) (13028535381451 / 10000) := by
  exact
    packedTile65536 1302841600 1302907136 13 3105 36094 30 _ _ (104939 / 5000) (2098783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302907136 :
    ThetaLowerSegment 1302907136 1302972672 (13028535381451 / 10000) (26058389219639 / 20000) := by
  exact
    packedTile65536 1302907136 1302972672 13 3141 36095 30 _ _ (419757 / 20000) (524697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1302972672 :
    ThetaLowerSegment 1302972672 1303038208 (26058389219639 / 20000) (26059695926293 / 20000) := by
  exact
    packedTile65536 1302972672 1303038208 13 3113 36096 30 _ _ (209879 / 10000) (2098793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303038208 :
    ThetaLowerSegment 1303038208 1303103744 (26059695926293 / 20000) (5212205144561 / 4000) := by
  exact
    packedTile65536 1303038208 1303103744 13 3168 36097 30 _ _ (419759 / 20000) (1049399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303103744 :
    ThetaLowerSegment 1303103744 1303169280 (5212205144561 / 4000) (5212468585937 / 4000) := by
  exact
    packedTile65536 1303103744 1303169280 13 3138 36098 30 _ _ (5247 / 250) (2098803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303169280 :
    ThetaLowerSegment 1303169280 1303234816 (5212468585937 / 4000) (26063624879779 / 20000) := by
  exact
    packedTile65536 1303169280 1303234816 13 3054 36099 30 _ _ (419761 / 20000) (262351 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303234816 :
    ThetaLowerSegment 1303234816 1303300352 (26063624879779 / 20000) (26064930759361 / 20000) := by
  exact
    packedTile65536 1303234816 1303300352 13 3111 36100 30 _ _ (209881 / 10000) (2098813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303300352 :
    ThetaLowerSegment 1303300352 1303365888 (26064930759361 / 20000) (521324665679 / 400) := by
  exact
    packedTile65536 1303300352 1303365888 13 3103 36101 30 _ _ (419763 / 20000) (1049409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303365888 :
    ThetaLowerSegment 1303365888 1303431424 (521324665679 / 400) (13033786375437 / 10000) := by
  exact
    packedTile65536 1303365888 1303431424 13 3191 36102 30 _ _ (104941 / 5000) (2098823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303431424 :
    ThetaLowerSegment 1303431424 1303496960 (13033786375437 / 10000) (6517220814301 / 5000) := by
  exact
    packedTile65536 1303431424 1303496960 13 3122 36103 30 _ _ (83953 / 4000) (524707 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303496960 :
    ThetaLowerSegment 1303496960 1303562496 (6517220814301 / 5000) (6517543194589 / 5000) := by
  exact
    packedTile65536 1303496960 1303562496 13 3072 36103 30 _ _ (209883 / 10000) (2098833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303562496 :
    ThetaLowerSegment 1303562496 1303628032 (6517543194589 / 5000) (26071473636289 / 20000) := by
  exact
    packedTile65536 1303562496 1303628032 13 3099 36104 30 _ _ (419767 / 20000) (1049419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303628032 :
    ThetaLowerSegment 1303628032 1303693568 (26071473636289 / 20000) (5214560608309 / 4000) := by
  exact
    packedTile65536 1303628032 1303693568 13 3167 36105 30 _ _ (52471 / 2500) (2098843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303693568 :
    ThetaLowerSegment 1303693568 1303759104 (5214560608309 / 4000) (26074110202211 / 20000) := by
  exact
    packedTile65536 1303693568 1303759104 13 3114 36106 30 _ _ (419769 / 20000) (65589 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303759104 :
    ThetaLowerSegment 1303759104 1303824640 (26074110202211 / 20000) (26075418205531 / 20000) := by
  exact
    packedTile65536 1303759104 1303824640 13 3116 36107 30 _ _ (41977 / 2000) (2098853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303824640 :
    ThetaLowerSegment 1303824640 1303890176 (26075418205531 / 20000) (13038359118159 / 10000) := by
  exact
    packedTile65536 1303824640 1303890176 13 3097 36108 30 _ _ (419771 / 20000) (1049429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303890176 :
    ThetaLowerSegment 1303890176 1303955712 (13038359118159 / 10000) (13039004517609 / 10000) := by
  exact
    packedTile65536 1303890176 1303955712 13 3075 36109 30 _ _ (104943 / 5000) (2098863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1303955712 :
    ThetaLowerSegment 1303955712 1304021248 (13039004517609 / 10000) (26079329221303 / 20000) := by
  exact
    packedTile65536 1303955712 1304021248 13 3145 36110 30 _ _ (419773 / 20000) (524717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304021248 :
    ThetaLowerSegment 1304021248 1304086784 (26079329221303 / 20000) (26080657386239 / 20000) := by
  exact
    packedTile65536 1304021248 1304086784 13 3164 36111 30 _ _ (209887 / 10000) (2098873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304086784 :
    ThetaLowerSegment 1304086784 1304152320 (26080657386239 / 20000) (26081959528289 / 20000) := by
  exact
    packedTile65536 1304086784 1304152320 13 3102 36112 30 _ _ (16791 / 800) (1049439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304152320 :
    ThetaLowerSegment 1304152320 1304217856 (26081959528289 / 20000) (1043331457609 / 800) := by
  exact
    packedTile65536 1304152320 1304217856 13 3161 36113 30 _ _ (13118 / 625) (2098883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304217856 :
    ThetaLowerSegment 1304217856 1304283392 (1043331457609 / 800) (5216919228893 / 4000) := by
  exact
    packedTile65536 1304217856 1304283392 13 3120 36113 30 _ _ (419777 / 20000) (262361 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304283392 :
    ThetaLowerSegment 1304283392 1304348928 (5216919228893 / 4000) (5217182849477 / 4000) := by
  exact
    packedTile65536 1304283392 1304348928 13 3140 36114 30 _ _ (209889 / 10000) (2098893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304348928 :
    ThetaLowerSegment 1304348928 1304414464 (5217182849477 / 4000) (26087196252451 / 20000) := by
  exact
    packedTile65536 1304348928 1304414464 13 3054 36115 30 _ _ (419779 / 20000) (1049449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304414464 :
    ThetaLowerSegment 1304414464 1304480000 (26087196252451 / 20000) (65221247076029 / 50000) := by
  exact
    packedTile65536 1304414464 1304480000 13 3103 36116 30 _ _ (2098901 / 100000) (262363 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304480000 :
    ThetaLowerSegment 1304480000 1304545536 (65221247076029 / 50000) (6522451822103 / 5000) := by
  exact
    packedTile65536 1304480000 1304545536 13 3117 36117 30 _ _ (1049453 / 50000) (2098909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304545536 :
    ThetaLowerSegment 1304545536 1304611072 (6522451822103 / 5000) (4076738869184 / 3125) := by
  exact
    packedTile65536 1304545536 1304611072 13 3148 36118 30 _ _ (2098911 / 100000) (1049457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304611072 :
    ThetaLowerSegment 1304611072 1304676608 (4076738869184 / 3125) (16307782974369 / 12500) := by
  exact
    packedTile65536 1304611072 1304676608 13 3154 36119 30 _ _ (524729 / 25000) (2098919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304676608 :
    ThetaLowerSegment 1304676608 1304742144 (16307782974369 / 12500) (65234458687261 / 50000) := by
  exact
    packedTile65536 1304676608 1304742144 13 3170 36120 30 _ _ (2098921 / 100000) (524731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304742144 :
    ThetaLowerSegment 1304742144 1304807680 (65234458687261 / 50000) (32618828200511 / 25000) := by
  exact
    packedTile65536 1304742144 1304807680 13 3047 36121 30 _ _ (1049463 / 50000) (2098929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304807680 :
    ThetaLowerSegment 1304807680 1304873216 (32618828200511 / 25000)
      (130482002095141 / 100000) := by
  exact
    packedTile65536 1304807680 1304873216 13 3187 36122 30 _ _ (2098931 / 100000) (1049467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304873216 :
    ThetaLowerSegment 1304873216 1304938752 (130482002095141 / 100000)
      (130488603248861 / 100000) := by
  exact
    packedTile65536 1304873216 1304938752 13 3145 36123 30 _ _ (262367 / 12500) (2098939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1304938752 :
    ThetaLowerSegment 1304938752 1305004288 (130488603248861 / 100000) (8155942667483 / 6250) := by
  exact
    packedTile65536 1304938752 1305004288 13 3087 36123 30 _ _ (2098941 / 100000) (65592 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305004288 :
    ThetaLowerSegment 1305004288 1305069824 (8155942667483 / 6250) (65250774766177 / 50000) := by
  exact
    packedTile65536 1305004288 1305069824 13 3081 36124 30 _ _ (1049473 / 50000) (2098949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305069824 :
    ThetaLowerSegment 1305069824 1305135360 (65250774766177 / 50000)
      (130508146535347 / 100000) := by
  exact
    packedTile65536 1305069824 1305135360 13 3143 36125 30 _ _ (2098951 / 100000) (1049477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305135360 :
    ThetaLowerSegment 1305135360 1305200896 (130508146535347 / 100000)
      (130514653298947 / 100000) := by
  exact
    packedTile65536 1305135360 1305200896 13 3100 36126 30 _ _ (524739 / 25000) (2098959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305200896 :
    ThetaLowerSegment 1305200896 1305266432 (130514653298947 / 100000)
      (16315159964853 / 12500) := by
  exact
    packedTile65536 1305200896 1305266432 13 3157 36127 30 _ _ (2098961 / 100000) (524741 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305266432 :
    ThetaLowerSegment 1305266432 1305331968 (16315159964853 / 12500) (32631968667499 / 25000) := by
  exact
    packedTile65536 1305266432 1305331968 13 3142 36128 30 _ _ (1049483 / 50000) (2098969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305331968 :
    ThetaLowerSegment 1305331968 1305397504 (32631968667499 / 25000)
      (130534534704979 / 100000) := by
  exact
    packedTile65536 1305331968 1305397504 13 3173 36129 30 _ _ (2098971 / 100000) (1049487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305397504 :
    ThetaLowerSegment 1305397504 1305463040 (130534534704979 / 100000)
      (130541045728531 / 100000) := by
  exact
    packedTile65536 1305397504 1305463040 13 3102 36130 30 _ _ (65593 / 3125) (2098979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305463040 :
    ThetaLowerSegment 1305463040 1305528576 (130541045728531 / 100000)
      (130547661716643 / 100000) := by
  exact
    packedTile65536 1305463040 1305528576 13 3152 36131 30 _ _ (2098981 / 100000) (262373 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305528576 :
    ThetaLowerSegment 1305528576 1305594112 (130547661716643 / 100000)
      (130554176969187 / 100000) := by
  exact
    packedTile65536 1305528576 1305594112 13 3104 36132 30 _ _ (1049493 / 50000) (2098989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305594112 :
    ThetaLowerSegment 1305594112 1305659648 (130554176969187 / 100000)
      (130560801384783 / 100000) := by
  exact
    packedTile65536 1305594112 1305659648 13 3156 36133 30 _ _ (2098991 / 100000) (1049497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305659648 :
    ThetaLowerSegment 1305659648 1305725184 (130560801384783 / 100000)
      (130567381737243 / 100000) := by
  exact
    packedTile65536 1305659648 1305725184 13 3135 36133 30 _ _ (524749 / 25000) (2098999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305725184 :
    ThetaLowerSegment 1305725184 1305790720 (130567381737243 / 100000)
      (65286976854687 / 50000) := by
  exact
    packedTile65536 1305725184 1305790720 13 3131 36134 30 _ _ (2099001 / 100000) (524751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305790720 :
    ThetaLowerSegment 1305790720 1305856256 (65286976854687 / 50000) (32645172354907 / 25000) := by
  exact
    packedTile65536 1305790720 1305856256 13 3209 36135 30 _ _ (1049503 / 50000) (2099009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305856256 :
    ThetaLowerSegment 1305856256 1305987328 (32645172354907 / 25000)
      (130593839723543 / 100000) := by
  exact
    packedTile65536 1305856256 1305987328 14 6265 36136 30 _ _ (2099011 / 100000) (1049507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1305987328 :
    ThetaLowerSegment 1305987328 1306118400 (130593839723543 / 100000)
      (32651739126443 / 25000) := by
  exact
    packedTile65536 1305987328 1306118400 14 6249 36138 30 _ _ (2099021 / 100000) (131189 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306118400 :
    ThetaLowerSegment 1306118400 1306249472 (32651739126443 / 25000) (13062000828053 / 10000) := by
  exact
    packedTile65536 1306118400 1306249472 14 6218 36140 30 _ _ (2099031 / 100000) (1049517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306249472 :
    ThetaLowerSegment 1306249472 1306380544 (13062000828053 / 10000)
      (130633087405001 / 100000) := by
  exact
    packedTile65536 1306249472 1306380544 14 6231 36142 30 _ _ (2099041 / 100000) (524761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306380544 :
    ThetaLowerSegment 1306380544 1306446080 (130633087405001 / 100000)
      (65319783587719 / 50000) := by
  exact
    packedTile65536 1306380544 1306446080 13 3087 36143 30 _ _ (2099051 / 100000) (1049527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306446080 :
    ThetaLowerSegment 1306446080 1306511616 (65319783587719 / 50000) (65323066511303 / 50000) := by
  exact
    packedTile65536 1306446080 1306511616 13 3128 36144 30 _ _ (131191 / 6250) (2099059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306511616 :
    ThetaLowerSegment 1306511616 1306577152 (65323066511303 / 50000)
      (130652684191987 / 100000) := by
  exact
    packedTile65536 1306511616 1306577152 13 3121 36145 30 _ _ (2099061 / 100000) (262383 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306577152 :
    ThetaLowerSegment 1306577152 1306642688 (130652684191987 / 100000)
      (130659195494719 / 100000) := by
  exact
    packedTile65536 1306577152 1306642688 13 3102 36146 30 _ _ (1049533 / 50000) (2099069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306642688 :
    ThetaLowerSegment 1306642688 1306708224 (130659195494719 / 100000)
      (130665748794381 / 100000) := by
  exact
    packedTile65536 1306642688 1306708224 13 3122 36147 30 _ _ (2099071 / 100000) (1049537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306708224 :
    ThetaLowerSegment 1306708224 1306773760 (130665748794381 / 100000) (5226893931573 / 4000) := by
  exact
    packedTile65536 1306708224 1306773760 13 3144 36148 30 _ _ (524769 / 25000) (2099079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306773760 :
    ThetaLowerSegment 1306773760 1306839296 (5226893931573 / 4000) (130678754684537 / 100000) := by
  exact
    packedTile65536 1306773760 1306839296 13 3052 36149 30 _ _ (2099081 / 100000) (524771 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306839296 :
    ThetaLowerSegment 1306839296 1306904832 (130678754684537 / 100000)
      (130685337418233 / 100000) := by
  exact
    packedTile65536 1306839296 1306904832 13 3136 36150 30 _ _ (1049543 / 50000) (2099089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306904832 :
    ThetaLowerSegment 1306904832 1306970368 (130685337418233 / 100000)
      (130691886582153 / 100000) := by
  exact
    packedTile65536 1306904832 1306970368 13 3120 36151 30 _ _ (2099091 / 100000) (1049547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306970368 :
    ThetaLowerSegment 1306970368 1307035904 (130691886582153 / 100000)
      (26139685892877 / 20000) := by
  exact
    packedTile65536 1306970368 1307035904 13 3117 36152 30 _ _ (262387 / 12500) (2099099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307035904 :
    ThetaLowerSegment 1307035904 1307101440 (26139685892877 / 20000) (65352498775707 / 50000) := by
  exact
    packedTile65536 1307035904 1307101440 13 3129 36152 30 _ _ (2099101 / 100000) (65597 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307101440 :
    ThetaLowerSegment 1307101440 1307166976 (65352498775707 / 50000) (816946393218 / 625) := by
  exact
    packedTile65536 1307101440 1307166976 13 3061 36153 30 _ _ (1049553 / 50000) (2099109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307166976 :
    ThetaLowerSegment 1307166976 1307232512 (816946393218 / 625) (130718016222531 / 100000) := by
  exact
    packedTile65536 1307166976 1307232512 13 3141 36154 30 _ _ (2099111 / 100000) (1049557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307232512 :
    ThetaLowerSegment 1307232512 1307298048 (130718016222531 / 100000)
      (130724596951191 / 100000) := by
  exact
    packedTile65536 1307232512 1307298048 13 3135 36155 30 _ _ (524779 / 25000) (2099119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307298048 :
    ThetaLowerSegment 1307298048 1307363584 (130724596951191 / 100000)
      (130731293147181 / 100000) := by
  exact
    packedTile65536 1307298048 1307363584 13 3190 36156 30 _ _ (2099121 / 100000) (524781 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307363584 :
    ThetaLowerSegment 1307363584 1307429120 (130731293147181 / 100000)
      (26147570163361 / 20000) := by
  exact
    packedTile65536 1307363584 1307429120 13 3124 36157 30 _ _ (1049563 / 50000) (2099129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307429120 :
    ThetaLowerSegment 1307429120 1307494656 (26147570163361 / 20000) (6537224728321 / 5000) := by
  exact
    packedTile65536 1307429120 1307494656 13 3165 36158 30 _ _ (2099131 / 100000) (1049567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307494656 :
    ThetaLowerSegment 1307494656 1307625728 (6537224728321 / 5000) (32689345290581 / 25000) := by
  exact
    packedTile65536 1307494656 1307625728 14 6139 36159 30 _ _ (65598 / 3125) (2099139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307625728 :
    ThetaLowerSegment 1307625728 1307691264 (32689345290581 / 25000) (32690988921899 / 25000) := by
  exact
    packedTile65536 1307625728 1307691264 13 3132 36161 30 _ _ (1049573 / 50000) (2099149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307691264 :
    ThetaLowerSegment 1307691264 1307756800 (32690988921899 / 25000)
      (130770616293719 / 100000) := by
  exact
    packedTile65536 1307691264 1307756800 13 3173 36162 30 _ _ (2099151 / 100000) (1049577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307756800 :
    ThetaLowerSegment 1307756800 1307822336 (130770616293719 / 100000)
      (130777176156219 / 100000) := by
  exact
    packedTile65536 1307756800 1307822336 13 3125 36162 30 _ _ (524789 / 25000) (2099159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307822336 :
    ThetaLowerSegment 1307822336 1307887872 (130777176156219 / 100000)
      (16347962805971 / 12500) := by
  exact
    packedTile65536 1307822336 1307887872 13 3109 36163 30 _ _ (2099161 / 100000) (524791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307887872 :
    ThetaLowerSegment 1307887872 1307953408 (16347962805971 / 12500) (32697570308503 / 25000) := by
  exact
    packedTile65536 1307887872 1307953408 13 3134 36164 30 _ _ (1049583 / 50000) (2099169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1307953408 :
    ThetaLowerSegment 1307953408 1308018944 (32697570308503 / 25000)
      (130796958696963 / 100000) := by
  exact
    packedTile65536 1307953408 1308018944 13 3181 36165 30 _ _ (2099171 / 100000) (1049587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1308018944 :
    ThetaLowerSegment 1308018944 1308150016 (130796958696963 / 100000)
      (26162045937527 / 20000) := by
  exact
    packedTile65536 1308018944 1308150016 14 6322 36166 30 _ _ (262397 / 12500) (2099179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1308150016 :
    ThetaLowerSegment 1308150016 1308281088 (26162045937527 / 20000)
      (130823452460249 / 100000) := by
  exact
    packedTile65536 1308150016 1308281088 14 6299 36168 30 _ _ (1049593 / 50000) (2099189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1308281088 :
    ThetaLowerSegment 1308281088 1308412160 (130823452460249 / 100000)
      (130836603923189 / 100000) := by
  exact
    packedTile65536 1308281088 1308412160 14 6265 36170 30 _ _ (524799 / 25000) (2099199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1308412160 :
    ThetaLowerSegment 1308412160 1308543232 (130836603923189 / 100000)
      (130849711371697 / 100000) := by
  exact
    packedTile65536 1308412160 1308543232 14 6244 36171 30 _ _ (2099207 / 100000) (209921 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1308543232 :
    ThetaLowerSegment 1308543232 1308674304 (130849711371697 / 100000)
      (130862873462287 / 100000) := by
  exact
    packedTile65536 1308543232 1308674304 14 6270 36173 30 _ _ (2099217 / 100000) (104961 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1308674304 :
    ThetaLowerSegment 1308674304 1308805376 (130862873462287 / 100000) (4089872242537 / 3125) := by
  exact
    packedTile65536 1308674304 1308805376 14 6211 36175 30 _ _ (2099227 / 100000) (209923 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1308805376 :
    ThetaLowerSegment 1308805376 1308936448 (4089872242537 / 3125) (130889071877937 / 100000) := by
  exact
    packedTile65536 1308805376 1308936448 14 6269 36177 30 _ _ (2099237 / 100000) (52481 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1308936448 :
    ThetaLowerSegment 1308936448 1309067520 (130889071877937 / 100000)
      (130902112400301 / 100000) := by
  exact
    packedTile65536 1308936448 1309067520 14 6212 36179 30 _ _ (2099247 / 100000) (8397 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1309067520 :
    ThetaLowerSegment 1309067520 1309198592 (130902112400301 / 100000)
      (130915354513457 / 100000) := by
  exact
    packedTile65536 1309067520 1309198592 14 6308 36181 30 _ _ (2099257 / 100000) (104963 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1309198592 :
    ThetaLowerSegment 1309198592 1309329664 (130915354513457 / 100000)
      (130928458138071 / 100000) := by
  exact
    packedTile65536 1309198592 1309329664 14 6242 36182 30 _ _ (2099267 / 100000) (209927 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1309329664 :
    ThetaLowerSegment 1309329664 1309460736 (130928458138071 / 100000)
      (65470760969421 / 50000) := by
  exact
    packedTile65536 1309329664 1309460736 14 6223 36184 30 _ _ (2099277 / 100000) (26241 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1309460736 :
    ThetaLowerSegment 1309460736 1309591808 (65470760969421 / 50000)
      (130954623589009 / 100000) := by
  exact
    packedTile65536 1309460736 1309591808 14 6241 36186 30 _ _ (2099287 / 100000) (209929 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1309591808 :
    ThetaLowerSegment 1309591808 1309722880 (130954623589009 / 100000)
      (13096770850721 / 10000) := by
  exact
    packedTile65536 1309591808 1309722880 14 6233 36188 30 _ _ (2099297 / 100000) (20993 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1309722880 :
    ThetaLowerSegment 1309722880 1309853952 (13096770850721 / 10000) (65490454474813 / 50000) := by
  exact
    packedTile65536 1309722880 1309853952 14 6288 36190 30 _ _ (2099307 / 100000) (209931 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1309853952 :
    ThetaLowerSegment 1309853952 1309985024 (65490454474813 / 50000) (4093567888576 / 3125) := by
  exact
    packedTile65536 1309853952 1309985024 14 6318 36191 30 _ _ (2099317 / 100000) (52483 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1309985024 :
    ThetaLowerSegment 1309985024 1310116096 (4093567888576 / 3125) (4093975158014 / 3125) := by
  exact
    packedTile65536 1309985024 1310116096 14 6208 36193 30 _ _ (2099327 / 100000) (209933 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1310116096 :
    ThetaLowerSegment 1310116096 1310247168 (4093975158014 / 3125) (131020290223969 / 100000) := by
  exact
    packedTile65536 1310116096 1310247168 14 6233 36195 30 _ _ (2099337 / 100000) (104967 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1310247168 :
    ThetaLowerSegment 1310247168 1310378240 (131020290223969 / 100000)
      (26206685587499 / 20000) := by
  exact
    packedTile65536 1310247168 1310378240 14 6258 36197 30 _ _ (2099347 / 100000) (41987 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1310378240 :
    ThetaLowerSegment 1310378240 1310509312 (26206685587499 / 20000) (6552320623027 / 5000) := by
  exact
    packedTile65536 1310378240 1310509312 14 6185 36199 30 _ _ (2099357 / 100000) (13121 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1310509312 :
    ThetaLowerSegment 1310509312 1310640384 (6552320623027 / 5000) (32764890723857 / 25000) := by
  exact
    packedTile65536 1310509312 1310640384 14 6264 36200 30 _ _ (2099367 / 100000) (209937 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1310640384 :
    ThetaLowerSegment 1310640384 1310771456 (32764890723857 / 25000) (32768203540763 / 25000) := by
  exact
    packedTile65536 1310640384 1310771456 14 6312 36202 30 _ _ (2099377 / 100000) (104969 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1310771456 :
    ThetaLowerSegment 1310771456 1310902528 (32768203540763 / 25000) (26217203441579 / 20000) := by
  exact
    packedTile65536 1310771456 1310902528 14 6289 36204 30 _ _ (2099387 / 100000) (209939 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1310902528 :
    ThetaLowerSegment 1310902528 1311033600 (26217203441579 / 20000)
      (131099088053617 / 100000) := by
  exact
    packedTile65536 1310902528 1311033600 14 6226 36206 30 _ _ (2099397 / 100000) (10497 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1311033600 :
    ThetaLowerSegment 1311033600 1311164672 (131099088053617 / 100000)
      (131112158961599 / 100000) := by
  exact
    packedTile65536 1311033600 1311164672 14 6226 36208 30 _ _ (2099407 / 100000) (209941 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1311164672 :
    ThetaLowerSegment 1311164672 1311295744 (131112158961599 / 100000)
      (26225059422637 / 20000) := by
  exact
    packedTile65536 1311164672 1311295744 14 6258 36210 30 _ _ (2099417 / 100000) (104971 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1311295744 :
    ThetaLowerSegment 1311295744 1311426816 (26225059422637 / 20000) (16392298904923 / 12500) := by
  exact
    packedTile65536 1311295744 1311426816 14 6237 36211 30 _ _ (2099427 / 100000) (209943 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1311426816 :
    ThetaLowerSegment 1311426816 1311557888 (16392298904923 / 12500) (26230295406041 / 20000) := by
  exact
    packedTile65536 1311426816 1311557888 14 6233 36213 30 _ _ (2099437 / 100000) (26243 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1311557888 :
    ThetaLowerSegment 1311557888 1311688960 (26230295406041 / 20000) (16395571410143 / 12500) := by
  exact
    packedTile65536 1311557888 1311688960 14 6237 36215 30 _ _ (2099447 / 100000) (41989 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1311688960 :
    ThetaLowerSegment 1311688960 1311820032 (16395571410143 / 12500)
      (131177707583593 / 100000) := by
  exact
    packedTile65536 1311688960 1311820032 14 6257 36217 30 _ _ (2099457 / 100000) (104973 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1311820032 :
    ThetaLowerSegment 1311820032 1311951104 (131177707583593 / 100000)
      (16398854443843 / 12500) := by
  exact
    packedTile65536 1311820032 1311951104 14 6253 36219 30 _ _ (2099467 / 100000) (209947 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1311951104 :
    ThetaLowerSegment 1311951104 1312082176 (16398854443843 / 12500) (26240759124453 / 20000) := by
  exact
    packedTile65536 1311951104 1312082176 14 6173 36220 30 _ _ (2099477 / 100000) (52487 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1312082176 :
    ThetaLowerSegment 1312082176 1312213248 (26240759124453 / 20000) (32804222530671 / 25000) := by
  exact
    packedTile65536 1312082176 1312213248 14 6237 36222 30 _ _ (2099487 / 100000) (209949 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1312213248 :
    ThetaLowerSegment 1312213248 1312344320 (32804222530671 / 25000)
      (131229917501569 / 100000) := by
  exact
    packedTile65536 1312213248 1312344320 14 6205 36224 30 _ _ (2099497 / 100000) (4199 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1312344320 :
    ThetaLowerSegment 1312344320 1312475392 (131229917501569 / 100000)
      (32810721539077 / 25000) := by
  exact
    packedTile65536 1312344320 1312475392 14 6177 36226 30 _ _ (2099507 / 100000) (209951 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1312475392 :
    ThetaLowerSegment 1312475392 1312606464 (32810721539077 / 25000) (16407016238693 / 12500) := by
  exact
    packedTile65536 1312475392 1312606464 14 6308 36228 30 _ _ (2099517 / 100000) (13122 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1312606464 :
    ThetaLowerSegment 1312606464 1312737536 (16407016238693 / 12500) (32817351829573 / 25000) := by
  exact
    packedTile65536 1312606464 1312737536 14 6324 36229 30 _ _ (2099527 / 100000) (209953 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1312737536 :
    ThetaLowerSegment 1312737536 1312868608 (32817351829573 / 25000) (1312823908551 / 1000) := by
  exact
    packedTile65536 1312737536 1312868608 14 6184 36231 30 _ _ (2099537 / 100000) (104977 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1312868608 :
    ThetaLowerSegment 1312868608 1312999680 (1312823908551 / 1000) (65647748113737 / 50000) := by
  exact
    packedTile65536 1312868608 1312999680 14 6242 36233 30 _ _ (2099547 / 100000) (41991 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1312999680 :
    ThetaLowerSegment 1312999680 1313130752 (65647748113737 / 50000)
      (131308528177773 / 100000) := by
  exact
    packedTile65536 1312999680 1313130752 14 6207 36235 30 _ _ (2099557 / 100000) (52489 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1313130752 :
    ThetaLowerSegment 1313130752 1313261824 (131308528177773 / 100000) (8207595149871 / 6250) := by
  exact
    packedTile65536 1313130752 1313261824 14 6189 36237 30 _ _ (2099567 / 100000) (209957 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1313261824 :
    ThetaLowerSegment 1313261824 1313392896 (8207595149871 / 6250) (8208407160889 / 6250) := by
  exact
    packedTile65536 1313261824 1313392896 14 6188 36238 30 _ _ (262447 / 12500) (2099579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1313392896 :
    ThetaLowerSegment 1313392896 1313523968 (8208407160889 / 6250) (65673771252677 / 50000) := by
  exact
    packedTile65536 1313392896 1313523968 14 6205 36240 30 _ _ (1049793 / 50000) (2099589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1313523968 :
    ThetaLowerSegment 1313523968 1313655040 (65673771252677 / 50000) (65680368183309 / 50000) := by
  exact
    packedTile65536 1313523968 1313655040 14 6284 36242 30 _ _ (524899 / 25000) (2099599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1313655040 :
    ThetaLowerSegment 1313655040 1313786112 (65680368183309 / 50000) (32843458952113 / 25000) := by
  exact
    packedTile65536 1313655040 1313786112 14 6239 36244 30 _ _ (1049803 / 50000) (2099609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1313786112 :
    ThetaLowerSegment 1313786112 1313917184 (32843458952113 / 25000) (32846748525481 / 25000) := by
  exact
    packedTile65536 1313786112 1313917184 14 6267 36246 30 _ _ (65613 / 3125) (2099619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1313917184 :
    ThetaLowerSegment 1313917184 1314048256 (32846748525481 / 25000) (13140030783039 / 10000) := by
  exact
    packedTile65536 1313917184 1314048256 14 6341 36247 30 _ _ (1049813 / 50000) (2099629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1314048256 :
    ThetaLowerSegment 1314048256 1314179328 (13140030783039 / 10000) (65706639690799 / 50000) := by
  exact
    packedTile65536 1314048256 1314179328 14 6178 36249 30 _ _ (524909 / 25000) (2099639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1314179328 :
    ThetaLowerSegment 1314179328 1314310400 (65706639690799 / 50000) (32856595818071 / 25000) := by
  exact
    packedTile65536 1314179328 1314310400 14 6241 36251 30 _ _ (1049823 / 50000) (2099649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1314310400 :
    ThetaLowerSegment 1314310400 1314441472 (32856595818071 / 25000) (32859889653421 / 25000) := by
  exact
    packedTile65536 1314310400 1314441472 14 6275 36253 30 _ _ (262457 / 12500) (2099659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1314441472 :
    ThetaLowerSegment 1314441472 1314572544 (32859889653421 / 25000) (32863192428039 / 25000) := by
  exact
    packedTile65536 1314441472 1314572544 14 6292 36255 30 _ _ (1049833 / 50000) (2099669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1314572544 :
    ThetaLowerSegment 1314572544 1314703616 (32863192428039 / 25000) (8216610025473 / 6250) := by
  exact
    packedTile65536 1314572544 1314703616 14 6187 36257 30 _ _ (524919 / 25000) (2099679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1314703616 :
    ThetaLowerSegment 1314703616 1314834688 (8216610025473 / 6250) (32869741858127 / 25000) := by
  exact
    packedTile65536 1314703616 1314834688 14 6290 36258 30 _ _ (1049843 / 50000) (2099689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1314834688 :
    ThetaLowerSegment 1314834688 1314965760 (32869741858127 / 25000) (32872979589359 / 25000) := by
  exact
    packedTile65536 1314834688 1314965760 14 6168 36260 30 _ _ (131231 / 6250) (2099699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1314965760 :
    ThetaLowerSegment 1314965760 1315096832 (32872979589359 / 25000) (65752521809821 / 50000) := by
  exact
    packedTile65536 1314965760 1315096832 14 6251 36262 30 _ _ (1049853 / 50000) (2099709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1315096832 :
    ThetaLowerSegment 1315096832 1315227904 (65752521809821 / 50000) (65759061375303 / 50000) := by
  exact
    packedTile65536 1315096832 1315227904 14 6229 36264 30 _ _ (524929 / 25000) (2099719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1315227904 :
    ThetaLowerSegment 1315227904 1315358976 (65759061375303 / 50000) (13153114945071 / 10000) := by
  exact
    packedTile65536 1315227904 1315358976 14 6204 36266 30 _ _ (1049863 / 50000) (2099729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1315358976 :
    ThetaLowerSegment 1315358976 1315490048 (13153114945071 / 10000) (13154402083239 / 10000) := by
  exact
    packedTile65536 1315358976 1315490048 14 6130 36267 30 _ _ (262467 / 12500) (2099739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1315490048 :
    ThetaLowerSegment 1315490048 1315621120 (13154402083239 / 10000) (8222325058627 / 6250) := by
  exact
    packedTile65536 1315490048 1315621120 14 6277 36269 30 _ _ (1049873 / 50000) (2099749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1315621120 :
    ThetaLowerSegment 1315621120 1315752192 (8222325058627 / 6250) (8223131364931 / 6250) := by
  exact
    packedTile65536 1315621120 1315752192 14 6144 36271 30 _ _ (524939 / 25000) (2099759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1315752192 :
    ThetaLowerSegment 1315752192 1315817728 (8223131364931 / 6250) (6578832025511 / 5000) := by
  exact
    packedTile65536 1315752192 1315817728 13 3114 36273 30 _ _ (1049883 / 50000) (2099769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1315817728 :
    ThetaLowerSegment 1315817728 1315883264 (6578832025511 / 5000) (26316644658461 / 20000) := by
  exact
    packedTile65536 1315817728 1315883264 13 3135 36274 30 _ _ (2099771 / 100000) (1049887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1315883264 :
    ThetaLowerSegment 1315883264 1315948800 (26316644658461 / 20000)
      (131589665405073 / 100000) := by
  exact
    packedTile65536 1315883264 1315948800 13 3068 36275 30 _ _ (65618 / 3125) (2099779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1315948800 :
    ThetaLowerSegment 1315948800 1316014336 (131589665405073 / 100000) (3289906835397 / 2500) := by
  exact
    packedTile65536 1315948800 1316014336 13 3147 36276 30 _ _ (2099781 / 100000) (262473 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316014336 :
    ThetaLowerSegment 1316014336 1316079872 (3289906835397 / 2500) (3290068518919 / 2500) := by
  exact
    packedTile65536 1316014336 1316079872 13 3080 36276 30 _ _ (1049893 / 50000) (2099789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316079872 :
    ThetaLowerSegment 1316079872 1316145408 (3290068518919 / 2500) (65804639752967 / 50000) := by
  exact
    packedTile65536 1316079872 1316145408 13 3114 36277 30 _ _ (2099791 / 100000) (1049897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316145408 :
    ThetaLowerSegment 1316145408 1316210944 (65804639752967 / 50000) (65807928033503 / 50000) := by
  exact
    packedTile65536 1316145408 1316210944 13 3132 36278 30 _ _ (524949 / 25000) (2099799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316210944 :
    ThetaLowerSegment 1316210944 1316276480 (65807928033503 / 50000) (65811220521471 / 50000) := by
  exact
    packedTile65536 1316210944 1316276480 13 3136 36279 30 _ _ (2099801 / 100000) (524951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316276480 :
    ThetaLowerSegment 1316276480 1316342016 (65811220521471 / 50000) (65814569712041 / 50000) := by
  exact
    packedTile65536 1316276480 1316342016 13 3190 36280 30 _ _ (1049903 / 50000) (2099809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316342016 :
    ThetaLowerSegment 1316342016 1316407552 (65814569712041 / 50000)
      (131635642538749 / 100000) := by
  exact
    packedTile65536 1316342016 1316407552 13 3097 36281 30 _ _ (2099811 / 100000) (1049907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316407552 :
    ThetaLowerSegment 1316407552 1316473088 (131635642538749 / 100000)
      (131642172966509 / 100000) := by
  exact
    packedTile65536 1316407552 1316473088 13 3110 36282 30 _ _ (262477 / 12500) (2099819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316473088 :
    ThetaLowerSegment 1316473088 1316538624 (131642172966509 / 100000)
      (131648753805523 / 100000) := by
  exact
    packedTile65536 1316473088 1316538624 13 3134 36283 30 _ _ (2099821 / 100000) (131239 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316538624 :
    ThetaLowerSegment 1316538624 1316604160 (131648753805523 / 100000)
      (131655273765253 / 100000) := by
  exact
    packedTile65536 1316538624 1316604160 13 3105 36284 30 _ _ (1049913 / 50000) (2099829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316604160 :
    ThetaLowerSegment 1316604160 1316669696 (131655273765253 / 100000)
      (65830907369409 / 50000) := by
  exact
    packedTile65536 1316604160 1316669696 13 3115 36285 30 _ _ (2099831 / 100000) (1049917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316669696 :
    ThetaLowerSegment 1316669696 1316735232 (65830907369409 / 50000) (13166835992763 / 10000) := by
  exact
    packedTile65536 1316669696 1316735232 13 3117 36285 30 _ _ (524959 / 25000) (2099839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316735232 :
    ThetaLowerSegment 1316735232 1316800768 (13166835992763 / 10000)
      (131674917731073 / 100000) := by
  exact
    packedTile65536 1316735232 1316800768 13 3123 36286 30 _ _ (2099841 / 100000) (524961 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316800768 :
    ThetaLowerSegment 1316800768 1316866304 (131674917731073 / 100000)
      (131681433553211 / 100000) := by
  exact
    packedTile65536 1316800768 1316866304 13 3103 36287 30 _ _ (1049923 / 50000) (2099849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316866304 :
    ThetaLowerSegment 1316866304 1316931840 (131681433553211 / 100000)
      (26337590298143 / 20000) := by
  exact
    packedTile65536 1316866304 1316931840 13 3104 36288 30 _ _ (2099851 / 100000) (1049927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316931840 :
    ThetaLowerSegment 1316931840 1316997376 (26337590298143 / 20000)
      (131694559737547 / 100000) := by
  exact
    packedTile65536 1316931840 1316997376 13 3147 36289 30 _ _ (131241 / 6250) (2099859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1316997376 :
    ThetaLowerSegment 1316997376 1317062912 (131694559737547 / 100000)
      (131701207897473 / 100000) := by
  exact
    packedTile65536 1316997376 1317062912 13 3166 36290 30 _ _ (2099861 / 100000) (262483 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317062912 :
    ThetaLowerSegment 1317062912 1317128448 (131701207897473 / 100000)
      (131707725881537 / 100000) := by
  exact
    packedTile65536 1317062912 1317128448 13 3104 36291 30 _ _ (1049933 / 50000) (2099869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317128448 :
    ThetaLowerSegment 1317128448 1317193984 (131707725881537 / 100000)
      (131714279575807 / 100000) := by
  exact
    packedTile65536 1317128448 1317193984 13 3121 36292 30 _ _ (209987 / 10000) (2099873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317193984 :
    ThetaLowerSegment 1317193984 1317259520 (131714279575807 / 100000)
      (16465100485929 / 12500) := by
  exact
    packedTile65536 1317193984 1317259520 13 3107 36293 30 _ _ (16799 / 800) (1049939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317259520 :
    ThetaLowerSegment 1317259520 1317325056 (16465100485929 / 12500) (8232958800867 / 6250) := by
  exact
    packedTile65536 1317259520 1317325056 13 3113 36294 30 _ _ (52497 / 2500) (2099883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317325056 :
    ThetaLowerSegment 1317325056 1317390592 (8232958800867 / 6250) (65866965126501 / 50000) := by
  exact
    packedTile65536 1317325056 1317390592 13 3138 36294 30 _ _ (419977 / 20000) (131243 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317390592 :
    ThetaLowerSegment 1317390592 1317456128 (65866965126501 / 50000) (32935123102313 / 25000) := by
  exact
    packedTile65536 1317390592 1317456128 13 3125 36295 30 _ _ (209989 / 10000) (2099893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317456128 :
    ThetaLowerSegment 1317456128 1317521664 (32935123102313 / 25000) (65873528340511 / 50000) := by
  exact
    packedTile65536 1317456128 1317521664 13 3126 36296 30 _ _ (419979 / 20000) (1049949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317521664 :
    ThetaLowerSegment 1317521664 1317587200 (65873528340511 / 50000) (65876812584111 / 50000) := by
  exact
    packedTile65536 1317521664 1317587200 13 3128 36297 30 _ _ (20999 / 1000) (2099903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317587200 :
    ThetaLowerSegment 1317587200 1317652736 (65876812584111 / 50000)
      (131760191571157 / 100000) := by
  exact
    packedTile65536 1317587200 1317652736 13 3127 36298 30 _ _ (419981 / 20000) (524977 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317652736 :
    ThetaLowerSegment 1317652736 1317718272 (131760191571157 / 100000)
      (131766823086937 / 100000) := by
  exact
    packedTile65536 1317652736 1317718272 13 3158 36299 30 _ _ (209991 / 10000) (2099913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317718272 :
    ThetaLowerSegment 1317718272 1317849344 (131766823086937 / 100000)
      (65889941229161 / 50000) := by
  exact
    packedTile65536 1317718272 1317849344 14 6219 36300 30 _ _ (419983 / 20000) (1049959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317849344 :
    ThetaLowerSegment 1317849344 1317914880 (65889941229161 / 50000) (65893242311261 / 50000) := by
  exact
    packedTile65536 1317849344 1317914880 13 3144 36302 30 _ _ (83997 / 4000) (262491 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317914880 :
    ThetaLowerSegment 1317914880 1318045952 (65893242311261 / 50000) (32949884971833 / 25000) := by
  exact
    packedTile65536 1317914880 1318045952 14 6217 36303 30 _ _ (209993 / 10000) (2099933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318045952 :
    ThetaLowerSegment 1318045952 1318111488 (32949884971833 / 25000) (32951535524673 / 25000) := by
  exact
    packedTile65536 1318045952 1318111488 13 3144 36304 30 _ _ (104997 / 5000) (2099943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318111488 :
    ThetaLowerSegment 1318111488 1318242560 (32951535524673 / 25000) (16477398369629 / 12500) := by
  exact
    packedTile65536 1318111488 1318242560 14 6212 36305 30 _ _ (419989 / 20000) (524987 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318242560 :
    ThetaLowerSegment 1318242560 1318308096 (16477398369629 / 12500)
      (131825572920187 / 100000) := by
  exact
    packedTile65536 1318242560 1318308096 13 3041 36307 30 _ _ (419991 / 20000) (1049979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318308096 :
    ThetaLowerSegment 1318308096 1318373632 (131825572920187 / 100000)
      (131831996697827 / 100000) := by
  exact
    packedTile65536 1318308096 1318373632 13 3059 36308 30 _ _ (52499 / 2500) (2099963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318373632 :
    ThetaLowerSegment 1318373632 1318439168 (131831996697827 / 100000)
      (131838640987087 / 100000) := by
  exact
    packedTile65536 1318373632 1318439168 13 3164 36309 30 _ _ (419993 / 20000) (65624 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318439168 :
    ThetaLowerSegment 1318439168 1318504704 (131838640987087 / 100000)
      (131845117294567 / 100000) := by
  exact
    packedTile65536 1318439168 1318504704 13 3084 36310 30 _ _ (209997 / 10000) (2099973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318504704 :
    ThetaLowerSegment 1318504704 1318570240 (131845117294567 / 100000)
      (16481447889699 / 12500) := by
  exact
    packedTile65536 1318504704 1318570240 13 3079 36311 30 _ _ (83999 / 4000) (1049989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318570240 :
    ThetaLowerSegment 1318570240 1318635776 (16481447889699 / 12500) (32964552138623 / 25000) := by
  exact
    packedTile65536 1318570240 1318635776 13 3155 36312 30 _ _ (104999 / 5000) (2099983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318635776 :
    ThetaLowerSegment 1318635776 1318701312 (32964552138623 / 25000)
      (131864829807197 / 100000) := by
  exact
    packedTile65536 1318635776 1318701312 13 3153 36313 30 _ _ (419997 / 20000) (524997 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318701312 :
    ThetaLowerSegment 1318701312 1318766848 (131864829807197 / 100000)
      (131871446875687 / 100000) := by
  exact
    packedTile65536 1318701312 1318766848 13 3151 36313 30 _ _ (209999 / 10000) (2099993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318766848 :
    ThetaLowerSegment 1318766848 1318832384 (131871446875687 / 100000)
      (131878032460007 / 100000) := by
  exact
    packedTile65536 1318766848 1318832384 13 3136 36314 30 _ _ (419999 / 20000) (1049999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318832384 :
    ThetaLowerSegment 1318832384 1318897920 (131878032460007 / 100000)
      (131884620160007 / 100000) := by
  exact
    packedTile65536 1318832384 1318897920 13 3137 36315 30 _ _ 21 (2100003 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318897920 :
    ThetaLowerSegment 1318897920 1318963456 (131884620160007 / 100000)
      (131891188975647 / 100000) := by
  exact
    packedTile65536 1318897920 1318963456 13 3128 36316 30 _ _ (420001 / 20000) (262501 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1318963456 :
    ThetaLowerSegment 1318963456 1319028992 (131891188975647 / 100000)
      (131897741006847 / 100000) := by
  exact
    packedTile65536 1318963456 1319028992 13 3120 36317 30 _ _ (210001 / 10000) (2100013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319028992 :
    ThetaLowerSegment 1319028992 1319094528 (131897741006847 / 100000)
      (131904293053647 / 100000) := by
  exact
    packedTile65536 1319028992 1319094528 13 3120 36318 30 _ _ (420003 / 20000) (1050009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319094528 :
    ThetaLowerSegment 1319094528 1319160064 (131904293053647 / 100000)
      (131910855616147 / 100000) := by
  exact
    packedTile65536 1319094528 1319160064 13 3125 36319 30 _ _ (105001 / 5000) (2100023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319160064 :
    ThetaLowerSegment 1319160064 1319225600 (131910855616147 / 100000)
      (131917361493597 / 100000) := by
  exact
    packedTile65536 1319160064 1319225600 13 3098 36320 30 _ _ (84001 / 4000) (525007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319225600 :
    ThetaLowerSegment 1319225600 1319291136 (131917361493597 / 100000)
      (131923760285007 / 100000) := by
  exact
    packedTile65536 1319225600 1319291136 13 3047 36321 30 _ _ (210003 / 10000) (2100033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319291136 :
    ThetaLowerSegment 1319291136 1319356672 (131923760285007 / 100000)
      (65965249648661 / 50000) := by
  exact
    packedTile65536 1319291136 1319356672 13 3209 36322 30 _ _ (420007 / 20000) (1050019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319356672 :
    ThetaLowerSegment 1319356672 1319422208 (65965249648661 / 50000) (65968494210461 / 50000) := by
  exact
    packedTile65536 1319356672 1319422208 13 3090 36322 30 _ _ (52501 / 2500) (2100043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319422208 :
    ThetaLowerSegment 1319422208 1319487744 (65968494210461 / 50000) (13194345025631 / 10000) := by
  exact
    packedTile65536 1319422208 1319487744 13 3077 36323 30 _ _ (525011 / 25000) (2100047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319487744 :
    ThetaLowerSegment 1319487744 1319553280 (13194345025631 / 10000)
      (131950017109533 / 100000) := by
  exact
    packedTile65536 1319487744 1319553280 13 3127 36324 30 _ _ (2100049 / 100000) (525013 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319553280 :
    ThetaLowerSegment 1319553280 1319618816 (131950017109533 / 100000)
      (131956541977311 / 100000) := by
  exact
    packedTile65536 1319553280 1319618816 13 3107 36325 30 _ _ (1050027 / 50000) (2100057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319618816 :
    ThetaLowerSegment 1319618816 1319684352 (131956541977311 / 100000)
      (32990764615097 / 25000) := by
  exact
    packedTile65536 1319618816 1319684352 13 3103 36326 30 _ _ (2100059 / 100000) (1050031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319684352 :
    ThetaLowerSegment 1319684352 1319749888 (32990764615097 / 25000) (32992419465529 / 25000) := by
  exact
    packedTile65536 1319684352 1319749888 13 3152 36327 30 _ _ (65627 / 3125) (2100067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319749888 :
    ThetaLowerSegment 1319749888 1319815424 (32992419465529 / 25000)
      (131976282579121 / 100000) := by
  exact
    packedTile65536 1319749888 1319815424 13 3145 36328 30 _ _ (2100069 / 100000) (262509 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319815424 :
    ThetaLowerSegment 1319815424 1319880960 (131976282579121 / 100000)
      (131982918812961 / 100000) := by
  exact
    packedTile65536 1319815424 1319880960 13 3160 36329 30 _ _ (1050037 / 50000) (2100077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319880960 :
    ThetaLowerSegment 1319880960 1319946496 (131982918812961 / 100000)
      (65994835283473 / 50000) := by
  exact
    packedTile65536 1319880960 1319946496 13 3215 36330 30 _ _ (2100079 / 100000) (1050041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319946496 :
    ThetaLowerSegment 1319946496 1320077568 (65994835283473 / 50000) (66001303542193 / 50000) := by
  exact
    packedTile65536 1319946496 1320077568 14 6160 36331 30 _ _ (525021 / 25000) (2100087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320077568 :
    ThetaLowerSegment 1320077568 1320143104 (66001303542193 / 50000) (66004525086389 / 50000) := by
  exact
    packedTile65536 1320077568 1320143104 13 3068 36332 30 _ _ (1050047 / 50000) (2100097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320143104 :
    ThetaLowerSegment 1320143104 1320208640 (66004525086389 / 50000)
      (132015646583737 / 100000) := by
  exact
    packedTile65536 1320143104 1320208640 13 3141 36333 30 _ _ (2100099 / 100000) (1050051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320208640 :
    ThetaLowerSegment 1320208640 1320274176 (132015646583737 / 100000)
      (132022285012481 / 100000) := by
  exact
    packedTile65536 1320208640 1320274176 13 3161 36334 30 _ _ (262513 / 12500) (2100107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320274176 :
    ThetaLowerSegment 1320274176 1320339712 (132022285012481 / 100000)
      (33007171011151 / 25000) := by
  exact
    packedTile65536 1320274176 1320339712 13 3047 36335 30 _ _ (2100109 / 100000) (131257 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320339712 :
    ThetaLowerSegment 1320339712 1320405248 (33007171011151 / 25000) (33008813300299 / 25000) := by
  exact
    packedTile65536 1320339712 1320405248 13 3128 36336 30 _ _ (1050057 / 50000) (2100117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320405248 :
    ThetaLowerSegment 1320405248 1320470784 (33008813300299 / 25000)
      (132041795071881 / 100000) := by
  exact
    packedTile65536 1320405248 1320470784 13 3115 36337 30 _ _ (2100119 / 100000) (1050061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320470784 :
    ThetaLowerSegment 1320470784 1320536320 (132041795071881 / 100000)
      (132048280254793 / 100000) := by
  exact
    packedTile65536 1320470784 1320536320 13 3088 36338 30 _ _ (525031 / 25000) (2100127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320536320 :
    ThetaLowerSegment 1320536320 1320601856 (132048280254793 / 100000)
      (26410990892951 / 20000) := by
  exact
    packedTile65536 1320536320 1320601856 13 3178 36339 30 _ _ (2100129 / 100000) (525033 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320601856 :
    ThetaLowerSegment 1320601856 1320667392 (26410990892951 / 20000)
      (132061544685247 / 100000) := by
  exact
    packedTile65536 1320601856 1320667392 13 3138 36340 30 _ _ (1050067 / 50000) (2100137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320667392 :
    ThetaLowerSegment 1320667392 1320732928 (132061544685247 / 100000)
      (132068202125877 / 100000) := by
  exact
    packedTile65536 1320667392 1320732928 13 3170 36340 30 _ _ (2100139 / 100000) (1050071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320732928 :
    ThetaLowerSegment 1320732928 1320798464 (132068202125877 / 100000)
      (132074754575157 / 100000) := by
  exact
    packedTile65536 1320732928 1320798464 13 3120 36341 30 _ _ (131259 / 6250) (2100147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320798464 :
    ThetaLowerSegment 1320798464 1320864000 (132074754575157 / 100000)
      (132081336442123 / 100000) := by
  exact
    packedTile65536 1320798464 1320864000 13 3134 36342 30 _ _ (2100149 / 100000) (262519 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320864000 :
    ThetaLowerSegment 1320864000 1320995072 (132081336442123 / 100000)
      (132094466604931 / 100000) := by
  exact
    packedTile65536 1320864000 1320995072 14 6252 36343 30 _ _ (1050077 / 50000) (2100157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1320995072 :
    ThetaLowerSegment 1320995072 1321126144 (132094466604931 / 100000)
      (132107674536327 / 100000) := by
  exact
    packedTile65536 1320995072 1321126144 14 6289 36345 30 _ _ (525041 / 25000) (2100167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1321126144 :
    ThetaLowerSegment 1321126144 1321257216 (132107674536327 / 100000)
      (132120714516693 / 100000) := by
  exact
    packedTile65536 1321126144 1321257216 14 6209 36347 30 _ _ (1050087 / 50000) (2100177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1321257216 :
    ThetaLowerSegment 1321257216 1321322752 (132120714516693 / 100000)
      (132127288089483 / 100000) := by
  exact
    packedTile65536 1321257216 1321322752 13 3130 36349 30 _ _ (2100183 / 100000) (1050093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1321322752 :
    ThetaLowerSegment 1321322752 1321339136 (132127288089483 / 100000) (211406295419 / 160) := by
  exact
    packedTile65536 1321322752 1321339136 11 784 36350 30 _ _ (525047 / 25000) (2100191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1321339136 :
    ThetaLowerSegment 1321339136 1321341184 (211406295419 / 160) (26425827251023 / 20000) := by
  exact
    packedTile65536 1321339136 1321341184 8 96 36350 30 _ _ (210019 / 10000) (2100193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1289341184_1321341184 :
    ThetaLowerSegment 1289341184 1321341184 (1611616691067 / 1250) (26425827251023 / 20000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1289341184 cell1289472256)
                    (ThetaLowerSegment.join cell1289603328 cell1289734400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1289865472 cell1289996544)
                    (ThetaLowerSegment.join cell1290127616 cell1290258688)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1290389760 cell1290520832)
                    (ThetaLowerSegment.join cell1290651904 cell1290782976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1290914048 cell1291045120)
                    (ThetaLowerSegment.join cell1291176192 cell1291307264))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1291438336 cell1291569408)
                    (ThetaLowerSegment.join cell1291700480 cell1291831552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1291962624 cell1292093696)
                    (ThetaLowerSegment.join cell1292224768 cell1292355840)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1292486912 cell1292617984)
                    (ThetaLowerSegment.join cell1292749056 cell1292880128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1293011200 cell1293142272)
                    (ThetaLowerSegment.join cell1293273344 cell1293404416)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1293535488 cell1293666560)
                    (ThetaLowerSegment.join cell1293797632 cell1293928704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1294059776 cell1294190848)
                    (ThetaLowerSegment.join cell1294321920 cell1294452992)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1294584064 cell1294715136)
                    (ThetaLowerSegment.join cell1294846208 cell1294977280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1295108352 cell1295239424)
                    (ThetaLowerSegment.join cell1295304960 cell1295370496))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1295501568 cell1295567104)
                    (ThetaLowerSegment.join cell1295698176 cell1295829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1295894784 cell1295960320)
                    (ThetaLowerSegment.join cell1296025856 cell1296091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1296156928 cell1296222464)
                    (ThetaLowerSegment.join cell1296288000 cell1296353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1296419072 cell1296484608)
                    (ThetaLowerSegment.join cell1296550144 cell1296615680))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1296681216 cell1296746752)
                    (ThetaLowerSegment.join cell1296812288 cell1296877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1296943360 cell1297008896)
                    (ThetaLowerSegment.join cell1297074432 cell1297139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1297205504 cell1297271040)
                    (ThetaLowerSegment.join cell1297336576 cell1297402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1297467648 cell1297533184)
                    (ThetaLowerSegment.join cell1297598720 cell1297664256))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1297729792 cell1297795328)
                    (ThetaLowerSegment.join cell1297860864 cell1297926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1297991936 cell1298057472)
                    (ThetaLowerSegment.join cell1298123008 cell1298188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1298254080 cell1298319616)
                    (ThetaLowerSegment.join cell1298385152 cell1298450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1298516224 cell1298581760)
                    (ThetaLowerSegment.join cell1298647296 cell1298712832)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1298778368 cell1298843904)
                    (ThetaLowerSegment.join cell1298909440 cell1298974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1299040512 cell1299106048)
                    (ThetaLowerSegment.join cell1299171584 cell1299237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1299302656 cell1299368192)
                    (ThetaLowerSegment.join cell1299433728 cell1299499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1299564800 cell1299630336)
                    (ThetaLowerSegment.join cell1299695872 cell1299761408))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1299826944 cell1299892480)
                    (ThetaLowerSegment.join cell1299958016 cell1300023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1300089088 cell1300154624)
                    (ThetaLowerSegment.join cell1300220160 cell1300285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1300351232 cell1300416768)
                    (ThetaLowerSegment.join cell1300482304 cell1300547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1300613376 cell1300678912)
                    (ThetaLowerSegment.join cell1300744448 cell1300809984)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1300875520 cell1300941056)
                    (ThetaLowerSegment.join cell1301006592 cell1301072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1301137664 cell1301203200)
                    (ThetaLowerSegment.join cell1301268736 cell1301334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1301399808 cell1301465344)
                    (ThetaLowerSegment.join cell1301530880 cell1301596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1301661952 cell1301727488)
                    (ThetaLowerSegment.join cell1301793024 cell1301858560))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1301924096 cell1301989632)
                    (ThetaLowerSegment.join cell1302055168 cell1302120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1302186240 cell1302251776)
                    (ThetaLowerSegment.join cell1302317312 cell1302382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1302448384 cell1302513920)
                    (ThetaLowerSegment.join cell1302579456 cell1302644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1302710528 cell1302776064)
                    (ThetaLowerSegment.join cell1302841600 cell1302907136)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1302972672 cell1303038208)
                    (ThetaLowerSegment.join cell1303103744 cell1303169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1303234816 cell1303300352)
                    (ThetaLowerSegment.join cell1303365888 cell1303431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1303496960 cell1303562496)
                    (ThetaLowerSegment.join cell1303628032 cell1303693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1303759104 cell1303824640)
                    (ThetaLowerSegment.join cell1303890176 cell1303955712))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1304021248 cell1304086784)
                    (ThetaLowerSegment.join cell1304152320 cell1304217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1304283392 cell1304348928)
                    (ThetaLowerSegment.join cell1304414464 cell1304480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1304545536 cell1304611072)
                    (ThetaLowerSegment.join cell1304676608 cell1304742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1304807680 cell1304873216)
                    (ThetaLowerSegment.join cell1304938752 cell1305004288))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1305069824 cell1305135360)
                    (ThetaLowerSegment.join cell1305200896 cell1305266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1305331968 cell1305397504)
                    (ThetaLowerSegment.join cell1305463040 cell1305528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1305594112 cell1305659648)
                    (ThetaLowerSegment.join cell1305725184 cell1305790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1305856256 cell1305987328)
                    (ThetaLowerSegment.join cell1306118400 cell1306249472))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1306380544 cell1306446080)
                    (ThetaLowerSegment.join cell1306511616 cell1306577152))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1306642688 cell1306708224)
                    (ThetaLowerSegment.join cell1306773760 cell1306839296)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1306904832 cell1306970368)
                    (ThetaLowerSegment.join cell1307035904 cell1307101440))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1307166976 cell1307232512)
                    (ThetaLowerSegment.join cell1307298048 cell1307363584)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1307429120 cell1307494656)
                    (ThetaLowerSegment.join cell1307625728 cell1307691264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1307756800 cell1307822336)
                    (ThetaLowerSegment.join cell1307887872 cell1307953408)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1308018944 cell1308150016)
                    (ThetaLowerSegment.join cell1308281088 cell1308412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1308543232 cell1308674304)
                    (ThetaLowerSegment.join cell1308805376 cell1308936448))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1309067520 cell1309198592)
                    (ThetaLowerSegment.join cell1309329664 cell1309460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1309591808 cell1309722880)
                    (ThetaLowerSegment.join cell1309853952 cell1309985024)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1310116096 cell1310247168)
                    (ThetaLowerSegment.join cell1310378240 cell1310509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1310640384 cell1310771456)
                    (ThetaLowerSegment.join cell1310902528 cell1311033600))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1311164672 cell1311295744)
                  (ThetaLowerSegment.join cell1311426816 cell1311557888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1311688960 cell1311820032)
                  (ThetaLowerSegment.join cell1311951104 cell1312082176)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1312213248 cell1312344320)
                  (ThetaLowerSegment.join cell1312475392 cell1312606464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1312737536 cell1312868608)
                  (ThetaLowerSegment.join cell1312999680 cell1313130752))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1313261824 cell1313392896)
                  (ThetaLowerSegment.join cell1313523968 cell1313655040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1313786112 cell1313917184)
                  (ThetaLowerSegment.join cell1314048256 cell1314179328)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1314310400 cell1314441472)
                  (ThetaLowerSegment.join cell1314572544 cell1314703616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1314834688 cell1314965760)
                  (ThetaLowerSegment.join cell1315096832 cell1315227904)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1315358976 cell1315490048)
                  (ThetaLowerSegment.join cell1315621120 cell1315752192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1315817728 cell1315883264)
                  (ThetaLowerSegment.join cell1315948800 cell1316014336)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1316079872 cell1316145408)
                  (ThetaLowerSegment.join cell1316210944 cell1316276480))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1316342016 cell1316407552)
                  (ThetaLowerSegment.join cell1316473088 cell1316538624))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1316604160 cell1316669696)
                  (ThetaLowerSegment.join cell1316735232 cell1316800768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1316866304 cell1316931840)
                  (ThetaLowerSegment.join cell1316997376 cell1317062912)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1317128448 cell1317193984)
                  (ThetaLowerSegment.join cell1317259520 cell1317325056))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1317390592 cell1317456128)
                  (ThetaLowerSegment.join cell1317521664 cell1317587200))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1317652736 cell1317718272)
                  (ThetaLowerSegment.join cell1317849344 cell1317914880))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1318045952 cell1318111488)
                  (ThetaLowerSegment.join cell1318242560 cell1318308096)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1318373632 cell1318439168)
                  (ThetaLowerSegment.join cell1318504704 cell1318570240))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1318635776 cell1318701312)
                  (ThetaLowerSegment.join cell1318766848 cell1318832384))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1318897920 cell1318963456)
                  (ThetaLowerSegment.join cell1319028992 cell1319094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1319160064 cell1319225600)
                  (ThetaLowerSegment.join cell1319291136 cell1319356672)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1319422208 cell1319487744)
                  (ThetaLowerSegment.join cell1319553280 cell1319618816))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1319684352 cell1319749888)
                  (ThetaLowerSegment.join cell1319815424 cell1319880960)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1319946496 cell1320077568)
                  (ThetaLowerSegment.join cell1320143104 cell1320208640))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1320274176 cell1320339712)
                  (ThetaLowerSegment.join cell1320405248 cell1320470784)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1320536320 cell1320601856)
                  (ThetaLowerSegment.join cell1320667392 cell1320732928))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1320798464 cell1320864000)
                  (ThetaLowerSegment.join cell1320995072 cell1321126144))))
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell1321257216 cell1321322752)
              cell1321339136)))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
