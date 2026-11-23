/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis16384
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 297341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell265341184 :
    ThetaLowerSegment 265341184 265373952 (6633105923007 / 25000) (13267893523431 / 50000) := by
  exact
    packedTile16384 265341184 265373952 12 1734 16289 28 _ _ (1939651 / 100000) (969827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265373952 :
    ThetaLowerSegment 265373952 265406720 (13267893523431 / 50000) (13269546117159 / 50000) := by
  exact
    packedTile16384 265373952 265406720 12 1704 16290 28 _ _ (121229 / 6250) (1939667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265406720 :
    ThetaLowerSegment 265406720 265472256 (13269546117159 / 50000) (13272848415549 / 50000) := by
  exact
    packedTile16384 265406720 265472256 13 3405 16291 28 _ _ (484919 / 25000) (1939679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265472256 :
    ThetaLowerSegment 265472256 265537792 (13272848415549 / 50000) (13276165304259 / 50000) := by
  exact
    packedTile16384 265472256 265537792 13 3420 16293 28 _ _ (1939701 / 100000) (242463 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265537792 :
    ThetaLowerSegment 265537792 265603328 (13276165304259 / 50000) (13279443439509 / 50000) := by
  exact
    packedTile16384 265537792 265603328 13 3380 16295 28 _ _ (77589 / 4000) (121233 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265603328 :
    ThetaLowerSegment 265603328 265668864 (13279443439509 / 50000) (6641368082567 / 25000) := by
  exact
    packedTile16384 265603328 265668864 13 3395 16297 28 _ _ (7759 / 400) (1939753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265668864 :
    ThetaLowerSegment 265668864 265734400 (6641368082567 / 25000) (6642997493567 / 25000) := by
  exact
    packedTile16384 265668864 265734400 13 3360 16299 28 _ _ (77591 / 4000) (969889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265734400 :
    ThetaLowerSegment 265734400 265799936 (6642997493567 / 25000) (830582002714 / 3125) := by
  exact
    packedTile16384 265734400 265799936 13 3420 16301 28 _ _ (1939799 / 100000) (969901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265799936 :
    ThetaLowerSegment 265799936 265865472 (830582002714 / 3125) (1661572702097 / 6250) := by
  exact
    packedTile16384 265799936 265865472 13 3371 16303 28 _ _ (121239 / 6250) (1939827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265865472 :
    ThetaLowerSegment 265865472 265931008 (1661572702097 / 6250) (212733712829 / 800) := by
  exact
    packedTile16384 265865472 265931008 13 3377 16305 28 _ _ (1939849 / 100000) (484963 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265931008 :
    ThetaLowerSegment 265931008 265996544 (212733712829 / 800) (1329914998623 / 5000) := by
  exact
    packedTile16384 265931008 265996544 13 3395 16307 28 _ _ (1939873 / 100000) (484969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265996544 :
    ThetaLowerSegment 265996544 266062080 (1329914998623 / 5000) (266048568277 / 1000) := by
  exact
    packedTile16384 265996544 266062080 13 3380 16309 28 _ _ (969949 / 50000) (1939901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266062080 :
    ThetaLowerSegment 266062080 266127616 (266048568277 / 1000) (6652847622091 / 25000) := by
  exact
    packedTile16384 266062080 266127616 13 3368 16311 28 _ _ (1939923 / 100000) (969963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266127616 :
    ThetaLowerSegment 266127616 266193152 (6652847622091 / 25000) (2661790483039 / 10000) := by
  exact
    packedTile16384 266127616 266193152 13 3358 16313 28 _ _ (1939947 / 100000) (38799 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266193152 :
    ThetaLowerSegment 266193152 266258688 (2661790483039 / 10000) (13312217388071 / 50000) := by
  exact
    packedTile16384 266193152 266258688 13 3366 16315 28 _ _ (484993 / 25000) (77599 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266258688 :
    ThetaLowerSegment 266258688 266324224 (13312217388071 / 50000) (13315495011313 / 50000) := by
  exact
    packedTile16384 266258688 266324224 13 3379 16317 28 _ _ (484999 / 25000) (1939999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266324224 :
    ThetaLowerSegment 266324224 266389760 (13315495011313 / 50000) (1331870962611 / 5000) := by
  exact
    packedTile16384 266324224 266389760 13 3314 16319 28 _ _ (1940021 / 100000) (242503 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266389760 :
    ThetaLowerSegment 266389760 266455296 (1331870962611 / 5000) (3330492710859 / 12500) := by
  exact
    packedTile16384 266389760 266455296 13 3362 16321 28 _ _ (970023 / 50000) (1940049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266455296 :
    ThetaLowerSegment 266455296 266520832 (3330492710859 / 12500) (6662577249153 / 25000) := by
  exact
    packedTile16384 266455296 266520832 13 3282 16323 28 _ _ (194007 / 10000) (1940073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266520832 :
    ThetaLowerSegment 266520832 266553600 (6662577249153 / 25000) (26653640139727 / 100000) := by
  exact
    packedTile16384 266520832 266553600 12 1717 16325 28 _ _ (388019 / 20000) (970049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266553600 :
    ThetaLowerSegment 266553600 266586368 (26653640139727 / 100000) (26656903399701 / 100000) := by
  exact
    packedTile16384 266553600 266586368 12 1682 16326 28 _ _ (1940107 / 100000) (194011 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266586368 :
    ThetaLowerSegment 266586368 266619136 (26656903399701 / 100000) (13330022226181 / 50000) := by
  exact
    packedTile16384 266586368 266619136 12 1619 16327 28 _ _ (1940119 / 100000) (970061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266619136 :
    ThetaLowerSegment 266619136 266651904 (13330022226181 / 50000) (13331697530163 / 50000) := by
  exact
    packedTile16384 266619136 266651904 12 1727 16328 28 _ _ (485033 / 25000) (388027 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266651904 :
    ThetaLowerSegment 266651904 266684672 (13331697530163 / 50000) (13333355383211 / 50000) := by
  exact
    packedTile16384 266651904 266684672 12 1709 16329 28 _ _ (121259 / 6250) (1940147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266684672 :
    ThetaLowerSegment 266684672 266717440 (13333355383211 / 50000) (13334991904797 / 50000) := by
  exact
    packedTile16384 266684672 266717440 12 1687 16330 28 _ _ (485039 / 25000) (1940159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266717440 :
    ThetaLowerSegment 266717440 266750208 (13334991904797 / 50000) (533466573219 / 2000) := by
  exact
    packedTile16384 266717440 266750208 12 1724 16331 28 _ _ (1940169 / 100000) (485043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266750208 :
    ThetaLowerSegment 266750208 266782976 (533466573219 / 2000) (5335304051739 / 20000) := by
  exact
    packedTile16384 266750208 266782976 12 1645 16332 28 _ _ (1940181 / 100000) (242523 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266782976 :
    ThetaLowerSegment 266782976 266815744 (5335304051739 / 20000) (1667485387599 / 6250) := by
  exact
    packedTile16384 266782976 266815744 12 1673 16333 28 _ _ (1940193 / 100000) (485049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266815744 :
    ThetaLowerSegment 266815744 266848512 (1667485387599 / 6250) (26683016044959 / 100000) := by
  exact
    packedTile16384 266815744 266848512 12 1675 16334 28 _ _ (388041 / 20000) (121263 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266848512 :
    ThetaLowerSegment 266848512 266881280 (26683016044959 / 100000) (26686368741663 / 100000) := by
  exact
    packedTile16384 266848512 266881280 12 1728 16335 28 _ _ (970109 / 50000) (1940221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266881280 :
    ThetaLowerSegment 266881280 266914048 (26686368741663 / 100000) (26689715638413 / 100000) := by
  exact
    packedTile16384 266881280 266914048 12 1725 16336 28 _ _ (194023 / 10000) (1940233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266914048 :
    ThetaLowerSegment 266914048 266946816 (26689715638413 / 100000) (213543507043 / 800) := by
  exact
    packedTile16384 266914048 266946816 12 1661 16337 28 _ _ (970121 / 50000) (388049 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266946816 :
    ThetaLowerSegment 266946816 266979584 (213543507043 / 800) (5339234169041 / 20000) := by
  exact
    packedTile16384 266946816 266979584 12 1666 16338 28 _ _ (388051 / 20000) (970129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell266979584 :
    ThetaLowerSegment 266979584 267012352 (5339234169041 / 20000) (26699442135367 / 100000) := by
  exact
    packedTile16384 266979584 267012352 12 1686 16339 28 _ _ (1940267 / 100000) (194027 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267012352 :
    ThetaLowerSegment 267012352 267045120 (26699442135367 / 100000) (1335137709581 / 5000) := by
  exact
    packedTile16384 267012352 267045120 12 1707 16340 28 _ _ (1940279 / 100000) (970141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267045120 :
    ThetaLowerSegment 267045120 267077888 (1335137709581 / 5000) (13353020522287 / 50000) := by
  exact
    packedTile16384 267045120 267077888 12 1694 16341 28 _ _ (1940291 / 100000) (970147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267077888 :
    ThetaLowerSegment 267077888 267110656 (13353020522287 / 50000) (13354661049319 / 50000) := by
  exact
    packedTile16384 267077888 267110656 12 1691 16342 28 _ _ (121269 / 6250) (1940307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267110656 :
    ThetaLowerSegment 267110656 267143424 (13354661049319 / 50000) (106850148809 / 400) := by
  exact
    packedTile16384 267110656 267143424 12 1657 16343 28 _ _ (485079 / 25000) (1940319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267143424 :
    ThetaLowerSegment 267143424 267176192 (106850148809 / 400) (13357889745169 / 50000) := by
  exact
    packedTile16384 267143424 267176192 12 1671 16344 28 _ _ (242541 / 12500) (1940331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267176192 :
    ThetaLowerSegment 267176192 267208960 (13357889745169 / 50000) (13359522541279 / 50000) := by
  exact
    packedTile16384 267176192 267208960 12 1683 16345 28 _ _ (97017 / 5000) (1940343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267208960 :
    ThetaLowerSegment 267208960 267241728 (13359522541279 / 50000) (1068892893551 / 4000) := by
  exact
    packedTile16384 267208960 267241728 12 1689 16346 28 _ _ (1940353 / 100000) (485089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267241728 :
    ThetaLowerSegment 267241728 267274496 (1068892893551 / 4000) (2672560349599 / 10000) := by
  exact
    packedTile16384 267241728 267274496 12 1691 16347 28 _ _ (388073 / 20000) (121273 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267274496 :
    ThetaLowerSegment 267274496 267307264 (2672560349599 / 10000) (3341112282017 / 12500) := by
  exact
    packedTile16384 267274496 267307264 12 1698 16348 28 _ _ (1940377 / 100000) (97019 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267307264 :
    ThetaLowerSegment 267307264 267340032 (3341112282017 / 12500) (13366057710549 / 50000) := by
  exact
    packedTile16384 267307264 267340032 12 1658 16349 28 _ _ (1940389 / 100000) (242549 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267340032 :
    ThetaLowerSegment 267340032 267372800 (13366057710549 / 50000) (267354160449 / 1000) := by
  exact
    packedTile16384 267340032 267372800 12 1701 16350 28 _ _ (970201 / 50000) (388081 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267372800 :
    ThetaLowerSegment 267372800 267405568 (267354160449 / 1000) (13369325357519 / 50000) := by
  exact
    packedTile16384 267372800 267405568 12 1667 16351 28 _ _ (970207 / 50000) (1940417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267405568 :
    ThetaLowerSegment 267405568 267438336 (13369325357519 / 50000) (6685492695981 / 25000) := by
  exact
    packedTile16384 267405568 267438336 12 1711 16352 28 _ _ (970213 / 50000) (1940429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267438336 :
    ThetaLowerSegment 267438336 267471104 (6685492695981 / 25000) (2674518608969 / 10000) := by
  exact
    packedTile16384 267438336 267471104 12 1657 16353 28 _ _ (970219 / 50000) (1940441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267471104 :
    ThetaLowerSegment 267471104 267503872 (2674518608969 / 10000) (6687110541617 / 25000) := by
  exact
    packedTile16384 267471104 267503872 12 1678 16354 28 _ _ (1940451 / 100000) (970227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267503872 :
    ThetaLowerSegment 267503872 267536640 (6687110541617 / 25000) (214014533053 / 800) := by
  exact
    packedTile16384 267503872 267536640 12 1739 16355 28 _ _ (1940463 / 100000) (970233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267536640 :
    ThetaLowerSegment 267536640 267569408 (214014533053 / 800) (1070205238517 / 4000) := by
  exact
    packedTile16384 267536640 267569408 12 1708 16356 28 _ _ (77619 / 4000) (970239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267569408 :
    ThetaLowerSegment 267569408 267602176 (1070205238517 / 4000) (3344802025927 / 12500) := by
  exact
    packedTile16384 267569408 267602176 12 1693 16357 28 _ _ (1940487 / 100000) (194049 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267602176 :
    ThetaLowerSegment 267602176 267634944 (3344802025927 / 12500) (6690400141979 / 25000) := by
  exact
    packedTile16384 267602176 267634944 12 1641 16358 28 _ _ (3881 / 200) (1940503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267634944 :
    ThetaLowerSegment 267634944 267667712 (6690400141979 / 25000) (6691222433939 / 25000) := by
  exact
    packedTile16384 267634944 267667712 12 1695 16359 28 _ _ (60641 / 3125) (388103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267667712 :
    ThetaLowerSegment 267667712 267700480 (6691222433939 / 25000) (669204764177 / 2500) := by
  exact
    packedTile16384 267667712 267700480 12 1701 16360 28 _ _ (485131 / 25000) (1940527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267700480 :
    ThetaLowerSegment 267700480 267733248 (669204764177 / 2500) (836606681168 / 3125) := by
  exact
    packedTile16384 267700480 267733248 12 1661 16361 28 _ _ (242567 / 12500) (1940539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267733248 :
    ThetaLowerSegment 267733248 267766016 (836606681168 / 3125) (836707589716 / 3125) := by
  exact
    packedTile16384 267733248 267766016 12 1664 16362 28 _ _ (1940549 / 100000) (242569 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267766016 :
    ThetaLowerSegment 267766016 267798784 (836707589716 / 3125) (26777974814149 / 100000) := by
  exact
    packedTile16384 267766016 267798784 12 1717 16363 28 _ _ (1940561 / 100000) (485141 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267798784 :
    ThetaLowerSegment 267798784 267831552 (26777974814149 / 100000) (13390661151287 / 50000) := by
  exact
    packedTile16384 267798784 267831552 12 1725 16364 28 _ _ (1940573 / 100000) (60643 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267831552 :
    ThetaLowerSegment 267831552 267864320 (13390661151287 / 50000) (13392287361517 / 50000) := by
  exact
    packedTile16384 267831552 267864320 12 1676 16365 28 _ _ (388117 / 20000) (485147 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267864320 :
    ThetaLowerSegment 267864320 267897088 (13392287361517 / 50000) (1339394366191 / 5000) := by
  exact
    packedTile16384 267864320 267897088 12 1707 16366 28 _ _ (970299 / 50000) (1940601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267897088 :
    ThetaLowerSegment 267897088 267929856 (1339394366191 / 5000) (2679119994509 / 10000) := by
  exact
    packedTile16384 267897088 267929856 12 1707 16367 28 _ _ (194061 / 10000) (1940613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267929856 :
    ThetaLowerSegment 267929856 267962624 (2679119994509 / 10000) (669861747329 / 2500) := by
  exact
    packedTile16384 267929856 267962624 12 1685 16368 28 _ _ (970311 / 50000) (621 / 32) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267962624 :
    ThetaLowerSegment 267962624 267995392 (669861747329 / 2500) (1339887478231 / 5000) := by
  exact
    packedTile16384 267962624 267995392 12 1690 16369 28 _ _ (970317 / 50000) (1940637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell267995392 :
    ThetaLowerSegment 267995392 268028160 (1339887478231 / 5000) (13400526272907 / 50000) := by
  exact
    packedTile16384 267995392 268028160 12 1702 16370 28 _ _ (1940647 / 100000) (38813 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268028160 :
    ThetaLowerSegment 268028160 268060928 (13400526272907 / 50000) (26804260455141 / 100000) := by
  exact
    packedTile16384 268028160 268060928 12 1653 16371 28 _ _ (1940659 / 100000) (970331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268060928 :
    ThetaLowerSegment 268060928 268093696 (26804260455141 / 100000) (13403790471611 / 50000) := by
  exact
    packedTile16384 268060928 268093696 12 1711 16372 28 _ _ (1940671 / 100000) (970337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268093696 :
    ThetaLowerSegment 268093696 268126464 (13403790471611 / 50000) (26810796654953 / 100000) := by
  exact
    packedTile16384 268093696 268126464 12 1657 16373 28 _ _ (1940683 / 100000) (970343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268126464 :
    ThetaLowerSegment 268126464 268159232 (26810796654953 / 100000) (26814045378383 / 100000) := by
  exact
    packedTile16384 268126464 268159232 12 1674 16374 28 _ _ (388139 / 20000) (970349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268159232 :
    ThetaLowerSegment 268159232 268192000 (26814045378383 / 100000) (26817292182867 / 100000) := by
  exact
    packedTile16384 268159232 268192000 12 1673 16375 28 _ _ (485177 / 25000) (1940711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268192000 :
    ThetaLowerSegment 268192000 268224768 (26817292182867 / 100000) (26820550651747 / 100000) := by
  exact
    packedTile16384 268192000 268224768 12 1679 16376 28 _ _ (24259 / 1250) (1940723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268224768 :
    ThetaLowerSegment 268224768 268257536 (26820550651747 / 100000) (26823774207599 / 100000) := by
  exact
    packedTile16384 268224768 268257536 12 1661 16377 28 _ _ (485183 / 25000) (388147 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268257536 :
    ThetaLowerSegment 268257536 268290304 (26823774207599 / 100000) (26827054064959 / 100000) := by
  exact
    packedTile16384 268257536 268290304 12 1690 16378 28 _ _ (242593 / 12500) (1940747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268290304 :
    ThetaLowerSegment 268290304 268323072 (26827054064959 / 100000) (1676898176167 / 6250) := by
  exact
    packedTile16384 268290304 268323072 12 1709 16379 28 _ _ (1940757 / 100000) (48519 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268323072 :
    ThetaLowerSegment 268323072 268355840 (1676898176167 / 6250) (13416813714527 / 50000) := by
  exact
    packedTile16384 268323072 268355840 12 1678 16380 28 _ _ (1940769 / 100000) (485193 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268355840 :
    ThetaLowerSegment 268355840 268388608 (13416813714527 / 50000) (6709228778017 / 25000) := by
  exact
    packedTile16384 268355840 268388608 12 1694 16381 28 _ _ (1940781 / 100000) (121299 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268388608 :
    ThetaLowerSegment 268388608 268421376 (6709228778017 / 25000) (3355026807521 / 12500) := by
  exact
    packedTile16384 268388608 268421376 12 1700 16382 28 _ _ (1940793 / 100000) (485199 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268421376 :
    ThetaLowerSegment 268421376 268454144 (3355026807521 / 12500) (26843523532693 / 100000) := by
  exact
    packedTile32768 268421376 268454144 12 1705 16383 28 _ _ (388161 / 20000) (242601 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268454144 :
    ThetaLowerSegment 268454144 268486912 (26843523532693 / 100000) (26846817100839 / 100000) := by
  exact
    packedTile32768 268454144 268486912 12 1697 16384 28 _ _ (970409 / 50000) (1940821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268486912 :
    ThetaLowerSegment 268486912 268519680 (26846817100839 / 100000) (26850135920139 / 100000) := by
  exact
    packedTile32768 268486912 268519680 12 1710 16385 28 _ _ (194083 / 10000) (1940833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268519680 :
    ThetaLowerSegment 268519680 268552448 (26850135920139 / 100000) (26853410120593 / 100000) := by
  exact
    packedTile32768 268519680 268552448 12 1687 16386 28 _ _ (970421 / 50000) (388169 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268552448 :
    ThetaLowerSegment 268552448 268585216 (26853410120593 / 100000) (214853412623 / 800) := by
  exact
    packedTile32768 268552448 268585216 12 1683 16387 28 _ _ (970427 / 50000) (1940857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268585216 :
    ThetaLowerSegment 268585216 268617984 (214853412623 / 800) (26860026512591 / 100000) := by
  exact
    packedTile32768 268585216 268617984 12 1726 16388 28 _ _ (970433 / 50000) (1940869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268617984 :
    ThetaLowerSegment 268617984 268650752 (26860026512591 / 100000) (26863310479859 / 100000) := by
  exact
    packedTile32768 268617984 268650752 12 1692 16389 28 _ _ (1940879 / 100000) (970441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268650752 :
    ThetaLowerSegment 268650752 268683520 (26863310479859 / 100000) (26866575058521 / 100000) := by
  exact
    packedTile32768 268650752 268683520 12 1682 16390 28 _ _ (1940891 / 100000) (970447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268683520 :
    ThetaLowerSegment 268683520 268716288 (26866575058521 / 100000) (6717473015437 / 25000) := by
  exact
    packedTile32768 268683520 268716288 12 1709 16391 28 _ _ (1940903 / 100000) (970453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268716288 :
    ThetaLowerSegment 268716288 268749056 (6717473015437 / 25000) (26873131448883 / 100000) := by
  exact
    packedTile32768 268716288 268749056 12 1669 16392 28 _ _ (388183 / 20000) (970459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268749056 :
    ThetaLowerSegment 268749056 268781824 (26873131448883 / 100000) (26876376678827 / 100000) := by
  exact
    packedTile32768 268749056 268781824 12 1672 16393 28 _ _ (1940927 / 100000) (194093 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268781824 :
    ThetaLowerSegment 268781824 268814592 (26876376678827 / 100000) (26879573407007 / 100000) := by
  exact
    packedTile32768 268781824 268814592 12 1647 16394 28 _ _ (97047 / 5000) (1940943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268814592 :
    ThetaLowerSegment 268814592 268847360 (26879573407007 / 100000) (26882940958727 / 100000) := by
  exact
    packedTile32768 268814592 268847360 12 1735 16395 28 _ _ (242619 / 12500) (388191 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268847360 :
    ThetaLowerSegment 268847360 268880128 (26882940958727 / 100000) (26886217305959 / 100000) := by
  exact
    packedTile32768 268847360 268880128 12 1688 16396 28 _ _ (485241 / 25000) (1940967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268880128 :
    ThetaLowerSegment 268880128 268912896 (26886217305959 / 100000) (26889544138823 / 100000) := by
  exact
    packedTile32768 268880128 268912896 12 1714 16397 28 _ _ (121311 / 6250) (1940979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268912896 :
    ThetaLowerSegment 268912896 268945664 (26889544138823 / 100000) (26892830231507 / 100000) := by
  exact
    packedTile32768 268912896 268945664 12 1693 16398 28 _ _ (485247 / 25000) (1940991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268945664 :
    ThetaLowerSegment 268945664 268978432 (26892830231507 / 100000) (26896151282507 / 100000) := by
  exact
    packedTile32768 268945664 268978432 12 1711 16399 28 _ _ (1941 / 100) (1941003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell268978432 :
    ThetaLowerSegment 268978432 269011200 (26896151282507 / 100000) (26899493706893 / 100000) := by
  exact
    packedTile32768 268978432 269011200 12 1722 16400 28 _ _ (1941013 / 100000) (242627 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269011200 :
    ThetaLowerSegment 269011200 269076736 (26899493706893 / 100000) (26905957320143 / 100000) := by
  exact
    packedTile32768 269011200 269076736 13 3330 16401 28 _ _ (77641 / 4000) (485257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269076736 :
    ThetaLowerSegment 269076736 269109504 (26905957320143 / 100000) (26909148404699 / 100000) := by
  exact
    packedTile32768 269076736 269109504 12 1644 16403 28 _ _ (1941049 / 100000) (485263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269109504 :
    ThetaLowerSegment 269109504 269142272 (26909148404699 / 100000) (13456246426401 / 50000) := by
  exact
    packedTile32768 269109504 269142272 12 1723 16404 28 _ _ (1941061 / 100000) (242633 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269142272 :
    ThetaLowerSegment 269142272 269175040 (13456246426401 / 50000) (6728940890623 / 25000) := by
  exact
    packedTile32768 269142272 269175040 12 1685 16405 28 _ _ (970537 / 50000) (1941077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269175040 :
    ThetaLowerSegment 269175040 269207808 (6728940890623 / 25000) (3364890205159 / 12500) := by
  exact
    packedTile32768 269175040 269207808 12 1730 16406 28 _ _ (970543 / 50000) (1941089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269207808 :
    ThetaLowerSegment 269207808 269240576 (3364890205159 / 12500) (6730606347517 / 25000) := by
  exact
    packedTile32768 269207808 269240576 12 1702 16407 28 _ _ (970549 / 50000) (1941101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269240576 :
    ThetaLowerSegment 269240576 269306112 (6730606347517 / 25000) (6732252408797 / 25000) := by
  exact
    packedTile32768 269240576 269306112 13 3392 16408 28 _ _ (194111 / 10000) (1941113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269306112 :
    ThetaLowerSegment 269306112 269371648 (6732252408797 / 25000) (2693561531419 / 10000) := by
  exact
    packedTile32768 269306112 269371648 13 3403 16410 28 _ _ (970567 / 50000) (1941137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269371648 :
    ThetaLowerSegment 269371648 269437184 (2693561531419 / 10000) (13471053274943 / 50000) := by
  exact
    packedTile32768 269371648 269437184 13 3344 16412 28 _ _ (1941159 / 100000) (970581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269437184 :
    ThetaLowerSegment 269437184 269502720 (13471053274943 / 50000) (3368576189117 / 12500) := by
  exact
    packedTile32768 269437184 269502720 13 3350 16414 28 _ _ (1941183 / 100000) (970593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269502720 :
    ThetaLowerSegment 269502720 269535488 (3368576189117 / 12500) (5390380748243 / 20000) := by
  exact
    packedTile32768 269502720 269535488 12 1697 16416 28 _ _ (1941207 / 100000) (194121 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269535488 :
    ThetaLowerSegment 269535488 269601024 (5390380748243 / 20000) (5391671271299 / 20000) := by
  exact
    packedTile32768 269535488 269601024 13 3324 16417 28 _ _ (97061 / 5000) (1941223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269601024 :
    ThetaLowerSegment 269601024 269633792 (5391671271299 / 20000) (26961538055411 / 100000) := by
  exact
    packedTile32768 269601024 269633792 12 1639 16419 28 _ _ (485311 / 25000) (1941247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269633792 :
    ThetaLowerSegment 269633792 269666560 (26961538055411 / 100000) (5392969191127 / 20000) := by
  exact
    packedTile32768 269633792 269666560 12 1704 16420 28 _ _ (242657 / 12500) (1941259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269666560 :
    ThetaLowerSegment 269666560 269699328 (5392969191127 / 20000) (26968066519247 / 100000) := by
  exact
    packedTile32768 269666560 269699328 12 1659 16421 28 _ _ (485317 / 25000) (1941271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269699328 :
    ThetaLowerSegment 269699328 269732096 (26968066519247 / 100000) (26971353106287 / 100000) := by
  exact
    packedTile32768 269699328 269732096 12 1693 16422 28 _ _ (12133 / 625) (1941283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269732096 :
    ThetaLowerSegment 269732096 269764864 (26971353106287 / 100000) (26974569827131 / 100000) := by
  exact
    packedTile32768 269732096 269764864 12 1657 16423 28 _ _ (485323 / 25000) (388259 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269764864 :
    ThetaLowerSegment 269764864 269797632 (26974569827131 / 100000) (13488914639113 / 50000) := by
  exact
    packedTile32768 269764864 269797632 12 1679 16424 28 _ _ (388261 / 20000) (485327 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269797632 :
    ThetaLowerSegment 269797632 269830400 (13488914639113 / 50000) (26981042157861 / 100000) := by
  exact
    packedTile32768 269797632 269830400 12 1655 16425 28 _ _ (1941317 / 100000) (48533 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269830400 :
    ThetaLowerSegment 269830400 269863168 (26981042157861 / 100000) (13492117822033 / 50000) := by
  exact
    packedTile32768 269830400 269863168 12 1645 16426 28 _ _ (1941329 / 100000) (485333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269863168 :
    ThetaLowerSegment 269863168 269895936 (13492117822033 / 50000) (13493787375293 / 50000) := by
  exact
    packedTile32768 269863168 269895936 12 1720 16427 28 _ _ (1941341 / 100000) (60667 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269895936 :
    ThetaLowerSegment 269895936 269928704 (13493787375293 / 50000) (26990814868743 / 100000) := by
  exact
    packedTile32768 269895936 269928704 12 1669 16428 28 _ _ (1941353 / 100000) (485339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269928704 :
    ThetaLowerSegment 269928704 269961472 (26990814868743 / 100000) (13497060506669 / 50000) := by
  exact
    packedTile32768 269928704 269961472 12 1703 16429 28 _ _ (388273 / 20000) (242671 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269961472 :
    ThetaLowerSegment 269961472 269994240 (13497060506669 / 50000) (6749354367871 / 25000) := by
  exact
    packedTile32768 269961472 269994240 12 1698 16430 28 _ _ (1941377 / 100000) (97069 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell269994240 :
    ThetaLowerSegment 269994240 270027008 (6749354367871 / 25000) (843773039012 / 3125) := by
  exact
    packedTile32768 269994240 270027008 12 1710 16431 28 _ _ (194139 / 10000) (1941393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270027008 :
    ThetaLowerSegment 270027008 270059776 (843773039012 / 3125) (13501979017151 / 50000) := by
  exact
    packedTile32768 270027008 270059776 12 1659 16432 28 _ _ (970701 / 50000) (388281 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270059776 :
    ThetaLowerSegment 270059776 270092544 (13501979017151 / 50000) (2700714583609 / 10000) := by
  exact
    packedTile32768 270059776 270092544 12 1642 16433 28 _ _ (970707 / 50000) (1941417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270092544 :
    ThetaLowerSegment 270092544 270125312 (2700714583609 / 10000) (3376308451997 / 12500) := by
  exact
    packedTile32768 270092544 270125312 12 1711 16434 28 _ _ (970713 / 50000) (1941429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270125312 :
    ThetaLowerSegment 270125312 270158080 (3376308451997 / 12500) (270137641777 / 1000) := by
  exact
    packedTile32768 270125312 270158080 12 1698 16435 28 _ _ (970719 / 50000) (1941441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270158080 :
    ThetaLowerSegment 270158080 270190848 (270137641777 / 1000) (33771296828 / 125) := by
  exact
    packedTile32768 270158080 270190848 12 1686 16436 28 _ _ (38829 / 2000) (1941453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270190848 :
    ThetaLowerSegment 270190848 270223616 (33771296828 / 125) (6755071867447 / 25000) := by
  exact
    packedTile32768 270190848 270223616 12 1674 16437 28 _ _ (970731 / 50000) (388293 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270223616 :
    ThetaLowerSegment 270223616 270256384 (6755071867447 / 25000) (13511792047169 / 50000) := by
  exact
    packedTile32768 270223616 270256384 12 1698 16438 28 _ _ (77659 / 4000) (970739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270256384 :
    ThetaLowerSegment 270256384 270289152 (13511792047169 / 50000) (13513442311119 / 50000) := by
  exact
    packedTile32768 270256384 270289152 12 1700 16439 28 _ _ (1941487 / 100000) (194149 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270289152 :
    ThetaLowerSegment 270289152 270321920 (13513442311119 / 50000) (27030124984069 / 100000) := by
  exact
    packedTile32768 270289152 270321920 12 1669 16440 28 _ _ (1941499 / 100000) (970751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270321920 :
    ThetaLowerSegment 270321920 270354688 (27030124984069 / 100000) (3379166787719 / 12500) := by
  exact
    packedTile32768 270321920 270354688 12 1653 16441 28 _ _ (1941511 / 100000) (970757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270354688 :
    ThetaLowerSegment 270354688 270387456 (3379166787719 / 12500) (13518307737811 / 50000) := by
  exact
    packedTile32768 270354688 270387456 12 1690 16442 28 _ _ (1941523 / 100000) (970763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270387456 :
    ThetaLowerSegment 270387456 270420224 (13518307737811 / 50000) (27039867546747 / 100000) := by
  exact
    packedTile32768 270387456 270420224 12 1675 16443 28 _ _ (388307 / 20000) (970769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270420224 :
    ThetaLowerSegment 270420224 270452992 (27039867546747 / 100000) (27043203124493 / 100000) := by
  exact
    packedTile32768 270420224 270452992 12 1718 16444 28 _ _ (1941547 / 100000) (38831 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270452992 :
    ThetaLowerSegment 270452992 270485760 (27043203124493 / 100000) (27046534839737 / 100000) := by
  exact
    packedTile32768 270452992 270485760 12 1716 16445 28 _ _ (1941559 / 100000) (970781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270485760 :
    ThetaLowerSegment 270485760 270518528 (27046534839737 / 100000) (27049800563841 / 100000) := by
  exact
    packedTile32768 270485760 270518528 12 1682 16446 28 _ _ (485393 / 25000) (77663 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270518528 :
    ThetaLowerSegment 270518528 270551296 (27049800563841 / 100000) (27053107081393 / 100000) := by
  exact
    packedTile32768 270518528 270551296 12 1703 16447 28 _ _ (121349 / 6250) (1941587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270551296 :
    ThetaLowerSegment 270551296 270584064 (27053107081393 / 100000) (1082257632069 / 4000) := by
  exact
    packedTile32768 270551296 270584064 12 1717 16448 28 _ _ (485399 / 25000) (1941599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270584064 :
    ThetaLowerSegment 270584064 270616832 (1082257632069 / 4000) (27059753184973 / 100000) := by
  exact
    packedTile32768 270584064 270616832 12 1706 16449 28 _ _ (242701 / 12500) (1941611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270616832 :
    ThetaLowerSegment 270616832 270649600 (27059753184973 / 100000) (27063051997353 / 100000) := by
  exact
    packedTile32768 270616832 270649600 12 1699 16450 28 _ _ (97081 / 5000) (1941623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270649600 :
    ThetaLowerSegment 270649600 270682368 (27063051997353 / 100000) (27066339180329 / 100000) := by
  exact
    packedTile32768 270649600 270682368 12 1693 16451 28 _ _ (60676 / 3125) (388327 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270682368 :
    ThetaLowerSegment 270682368 270715136 (27066339180329 / 100000) (27069517651557 / 100000) := by
  exact
    packedTile32768 270682368 270715136 12 1637 16452 28 _ _ (485411 / 25000) (1941647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270715136 :
    ThetaLowerSegment 270715136 270747904 (27069517651557 / 100000) (5414559033377 / 20000) := by
  exact
    packedTile32768 270715136 270747904 12 1688 16453 28 _ _ (242707 / 12500) (1941659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270747904 :
    ThetaLowerSegment 270747904 270780672 (5414559033377 / 20000) (27076039694113 / 100000) := by
  exact
    packedTile32768 270747904 270780672 12 1671 16454 28 _ _ (485417 / 25000) (1941671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270780672 :
    ThetaLowerSegment 270780672 270813440 (27076039694113 / 100000) (27079363850273 / 100000) := by
  exact
    packedTile32768 270780672 270813440 12 1712 16455 28 _ _ (24271 / 1250) (1941683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270813440 :
    ThetaLowerSegment 270813440 270846208 (27079363850273 / 100000) (27082618127741 / 100000) := by
  exact
    packedTile32768 270813440 270846208 12 1676 16456 28 _ _ (1941693 / 100000) (60678 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270846208 :
    ThetaLowerSegment 270846208 270878976 (27082618127741 / 100000) (13542944950333 / 50000) := by
  exact
    packedTile32768 270846208 270878976 12 1685 16457 28 _ _ (388341 / 20000) (485427 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270878976 :
    ThetaLowerSegment 270878976 270911744 (13542944950333 / 50000) (3386145454441 / 12500) := by
  exact
    packedTile32768 270878976 270911744 12 1686 16458 28 _ _ (1941717 / 100000) (48543 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270911744 :
    ThetaLowerSegment 270911744 270944512 (3386145454441 / 12500) (27092447099267 / 100000) := by
  exact
    packedTile32768 270911744 270944512 12 1691 16459 28 _ _ (1941729 / 100000) (485433 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270944512 :
    ThetaLowerSegment 270944512 270977280 (27092447099267 / 100000) (5419148835097 / 20000) := by
  exact
    packedTile32768 270944512 270977280 12 1698 16460 28 _ _ (1941741 / 100000) (121359 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell270977280 :
    ThetaLowerSegment 270977280 271010048 (5419148835097 / 20000) (27098924766899 / 100000) := by
  exact
    packedTile32768 270977280 271010048 12 1638 16461 28 _ _ (1941753 / 100000) (485439 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271010048 :
    ThetaLowerSegment 271010048 271042816 (27098924766899 / 100000) (13551065310457 / 50000) := by
  exact
    packedTile32768 271010048 271042816 12 1651 16462 28 _ _ (388353 / 20000) (242721 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271042816 :
    ThetaLowerSegment 271042816 271075584 (13551065310457 / 50000) (6776325871133 / 25000) := by
  exact
    packedTile32768 271042816 271075584 12 1634 16463 28 _ _ (1941777 / 100000) (97089 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271075584 :
    ThetaLowerSegment 271075584 271108352 (6776325871133 / 25000) (6777141422513 / 25000) := by
  exact
    packedTile32768 271075584 271108352 12 1680 16464 28 _ _ (1941789 / 100000) (60681 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271108352 :
    ThetaLowerSegment 271108352 271141120 (6777141422513 / 25000) (13555904248861 / 50000) := by
  exact
    packedTile32768 271108352 271141120 12 1670 16465 28 _ _ (1941801 / 100000) (485451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271141120 :
    ThetaLowerSegment 271141120 271173888 (13555904248861 / 50000) (13557547022659 / 50000) := by
  exact
    packedTile32768 271141120 271173888 12 1692 16466 28 _ _ (1941813 / 100000) (242727 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271173888 :
    ThetaLowerSegment 271173888 271206656 (13557547022659 / 50000) (6779567232707 / 25000) := by
  exact
    packedTile32768 271173888 271206656 12 1635 16467 28 _ _ (970913 / 50000) (1941829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271206656 :
    ThetaLowerSegment 271206656 271239424 (6779567232707 / 25000) (13560778231281 / 50000) := by
  exact
    packedTile32768 271206656 271239424 12 1693 16468 28 _ _ (970919 / 50000) (1941841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271239424 :
    ThetaLowerSegment 271239424 271272192 (13560778231281 / 50000) (847652225016 / 3125) := by
  exact
    packedTile32768 271239424 271272192 12 1707 16469 28 _ _ (38837 / 2000) (1941853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271272192 :
    ThetaLowerSegment 271272192 271304960 (847652225016 / 3125) (13564042491061 / 50000) := by
  exact
    packedTile32768 271272192 271304960 12 1655 16470 28 _ _ (970931 / 50000) (388373 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271304960 :
    ThetaLowerSegment 271304960 271337728 (13564042491061 / 50000) (6782850911197 / 25000) := by
  exact
    packedTile32768 271304960 271337728 12 1709 16471 28 _ _ (970937 / 50000) (1941877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271337728 :
    ThetaLowerSegment 271337728 271370496 (6782850911197 / 25000) (3391836649959 / 12500) := by
  exact
    packedTile32768 271337728 271370496 12 1694 16472 28 _ _ (970943 / 50000) (1941889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271370496 :
    ThetaLowerSegment 271370496 271403264 (3391836649959 / 12500) (3392246390437 / 12500) := by
  exact
    packedTile32768 271370496 271403264 12 1688 16473 28 _ _ (970949 / 50000) (1941901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271403264 :
    ThetaLowerSegment 271403264 271436032 (3392246390437 / 12500) (6785303528299 / 25000) := by
  exact
    packedTile32768 271403264 271436032 12 1670 16474 28 _ _ (194191 / 10000) (1941913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271436032 :
    ThetaLowerSegment 271436032 271468800 (6785303528299 / 25000) (13572252835493 / 50000) := by
  exact
    packedTile32768 271436032 271468800 12 1695 16475 28 _ _ (970961 / 50000) (77677 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271468800 :
    ThetaLowerSegment 271468800 271501568 (13572252835493 / 50000) (3393469315821 / 12500) := by
  exact
    packedTile32768 271468800 271501568 12 1673 16476 28 _ _ (970967 / 50000) (1941937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271501568 :
    ThetaLowerSegment 271501568 271534336 (3393469315821 / 12500) (2715093349217 / 10000) := by
  exact
    packedTile32768 271501568 271534336 12 1637 16477 28 _ _ (970973 / 50000) (1941949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271534336 :
    ThetaLowerSegment 271534336 271567104 (2715093349217 / 10000) (13577103816679 / 50000) := by
  exact
    packedTile32768 271534336 271567104 12 1686 16478 28 _ _ (970979 / 50000) (1941961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271567104 :
    ThetaLowerSegment 271567104 271599872 (13577103816679 / 50000) (13578760317089 / 50000) := by
  exact
    packedTile32768 271567104 271599872 12 1706 16479 28 _ _ (194197 / 10000) (1941973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271599872 :
    ThetaLowerSegment 271599872 271632640 (13578760317089 / 50000) (27160889974683 / 100000) := by
  exact
    packedTile32768 271599872 271632640 12 1735 16480 28 _ _ (1941983 / 100000) (970993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271632640 :
    ThetaLowerSegment 271632640 271665408 (27160889974683 / 100000) (27164133106333 / 100000) := by
  exact
    packedTile32768 271632640 271665408 12 1670 16481 28 _ _ (388399 / 20000) (970999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271665408 :
    ThetaLowerSegment 271665408 271698176 (27164133106333 / 100000) (27167469474359 / 100000) := by
  exact
    packedTile32768 271665408 271698176 12 1718 16482 28 _ _ (1942007 / 100000) (194201 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271698176 :
    ThetaLowerSegment 271698176 271730944 (27167469474359 / 100000) (13585398076453 / 50000) := by
  exact
    packedTile32768 271698176 271730944 12 1713 16483 28 _ _ (1942019 / 100000) (971011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271730944 :
    ThetaLowerSegment 271730944 271763712 (13585398076453 / 50000) (5434811364591 / 20000) := by
  exact
    packedTile32768 271730944 271763712 12 1679 16484 28 _ _ (1942031 / 100000) (971017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271763712 :
    ThetaLowerSegment 271763712 271796480 (5434811364591 / 20000) (271773874267 / 1000) := by
  exact
    packedTile32768 271763712 271796480 12 1715 16485 28 _ _ (1942043 / 100000) (971023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271796480 :
    ThetaLowerSegment 271796480 271829248 (271773874267 / 1000) (5436122636011 / 20000) := by
  exact
    packedTile32768 271796480 271829248 12 1661 16486 28 _ _ (388411 / 20000) (971029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271829248 :
    ThetaLowerSegment 271829248 271862016 (5436122636011 / 20000) (2718392440429 / 10000) := by
  exact
    packedTile32768 271829248 271862016 12 1705 16487 28 _ _ (1942067 / 100000) (194207 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271862016 :
    ThetaLowerSegment 271862016 271894784 (2718392440429 / 10000) (13593628505927 / 50000) := by
  exact
    packedTile32768 271862016 271894784 12 1716 16488 28 _ _ (1942079 / 100000) (971041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271894784 :
    ThetaLowerSegment 271894784 271927552 (13593628505927 / 50000) (27190537203553 / 100000) := by
  exact
    packedTile32768 271894784 271927552 12 1689 16489 28 _ _ (1942091 / 100000) (971047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271927552 :
    ThetaLowerSegment 271927552 271960320 (27190537203553 / 100000) (27193733905091 / 100000) := by
  exact
    packedTile32768 271927552 271960320 12 1646 16490 28 _ _ (1942103 / 100000) (971053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271960320 :
    ThetaLowerSegment 271960320 271993088 (27193733905091 / 100000) (3399630165867 / 12500) := by
  exact
    packedTile32768 271960320 271993088 12 1703 16491 28 _ _ (388423 / 20000) (971059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell271993088 :
    ThetaLowerSegment 271993088 272025856 (3399630165867 / 12500) (27200255547121 / 100000) := by
  exact
    packedTile32768 271993088 272025856 12 1655 16492 28 _ _ (1942127 / 100000) (194213 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272025856 :
    ThetaLowerSegment 272025856 272058624 (27200255547121 / 100000) (27203506687807 / 100000) := by
  exact
    packedTile32768 272025856 272058624 12 1674 16493 28 _ _ (1942139 / 100000) (971071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272058624 :
    ThetaLowerSegment 272058624 272091392 (27203506687807 / 100000) (27206711236957 / 100000) := by
  exact
    packedTile32768 272058624 272091392 12 1650 16494 28 _ _ (1942151 / 100000) (971077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272091392 :
    ThetaLowerSegment 272091392 272124160 (27206711236957 / 100000) (27210020682709 / 100000) := by
  exact
    packedTile32768 272091392 272124160 12 1704 16495 28 _ _ (1942163 / 100000) (971083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272124160 :
    ThetaLowerSegment 272124160 272156928 (27210020682709 / 100000) (27213260230609 / 100000) := by
  exact
    packedTile32768 272124160 272156928 12 1668 16496 28 _ _ (77687 / 4000) (971089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272156928 :
    ThetaLowerSegment 272156928 272189696 (27213260230609 / 100000) (27216546411013 / 100000) := by
  exact
    packedTile32768 272156928 272189696 12 1692 16497 28 _ _ (1942187 / 100000) (194219 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272189696 :
    ThetaLowerSegment 272189696 272222464 (27216546411013 / 100000) (27219871455701 / 100000) := by
  exact
    packedTile32768 272189696 272222464 12 1712 16498 28 _ _ (1942199 / 100000) (971101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272222464 :
    ThetaLowerSegment 272222464 272255232 (27219871455701 / 100000) (27223159620617 / 100000) := by
  exact
    packedTile32768 272222464 272255232 12 1693 16499 28 _ _ (485553 / 25000) (388443 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272255232 :
    ThetaLowerSegment 272255232 272288000 (27223159620617 / 100000) (27226440036953 / 100000) := by
  exact
    packedTile32768 272255232 272288000 12 1689 16500 28 _ _ (121389 / 6250) (1942227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272288000 :
    ThetaLowerSegment 272288000 272320768 (27226440036953 / 100000) (27229704935669 / 100000) := by
  exact
    packedTile32768 272288000 272320768 12 1681 16501 28 _ _ (485559 / 25000) (1942239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272320768 :
    ThetaLowerSegment 272320768 272353536 (27229704935669 / 100000) (27232983450293 / 100000) := by
  exact
    packedTile32768 272320768 272353536 12 1688 16502 28 _ _ (242781 / 12500) (1942251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272353536 :
    ThetaLowerSegment 272353536 272386304 (27232983450293 / 100000) (27236289176813 / 100000) := by
  exact
    packedTile32768 272353536 272386304 12 1702 16503 28 _ _ (97113 / 5000) (1942263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272386304 :
    ThetaLowerSegment 272386304 272419072 (27236289176813 / 100000) (27239589096941 / 100000) := by
  exact
    packedTile32768 272386304 272419072 12 1699 16504 28 _ _ (60696 / 3125) (77691 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272419072 :
    ThetaLowerSegment 272419072 272451840 (27239589096941 / 100000) (27242894864309 / 100000) := by
  exact
    packedTile32768 272419072 272451840 12 1702 16505 28 _ _ (485571 / 25000) (1942287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272451840 :
    ThetaLowerSegment 272451840 272484608 (27242894864309 / 100000) (27246132671741 / 100000) := by
  exact
    packedTile32768 272451840 272484608 12 1667 16506 28 _ _ (242787 / 12500) (1942299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272484608 :
    ThetaLowerSegment 272484608 272517376 (27246132671741 / 100000) (27249473441501 / 100000) := by
  exact
    packedTile32768 272484608 272517376 12 1720 16507 28 _ _ (485577 / 25000) (1942311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272517376 :
    ThetaLowerSegment 272517376 272550144 (27249473441501 / 100000) (27252740423741 / 100000) := by
  exact
    packedTile32768 272517376 272550144 12 1682 16508 28 _ _ (24279 / 1250) (1942323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272550144 :
    ThetaLowerSegment 272550144 272582912 (27252740423741 / 100000) (27256044330473 / 100000) := by
  exact
    packedTile32768 272550144 272582912 12 1701 16509 28 _ _ (485583 / 25000) (388467 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272582912 :
    ThetaLowerSegment 272582912 272615680 (27256044330473 / 100000) (27259422066689 / 100000) := by
  exact
    packedTile32768 272582912 272615680 12 1739 16510 28 _ _ (242793 / 12500) (1942347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272615680 :
    ThetaLowerSegment 272615680 272648448 (27259422066689 / 100000) (27262714360109 / 100000) := by
  exact
    packedTile32768 272615680 272648448 12 1695 16511 28 _ _ (485589 / 25000) (1942359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272648448 :
    ThetaLowerSegment 272648448 272681216 (27262714360109 / 100000) (27265938690989 / 100000) := by
  exact
    packedTile32768 272648448 272681216 12 1660 16512 28 _ _ (60699 / 3125) (1942371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272681216 :
    ThetaLowerSegment 272681216 272713984 (27265938690989 / 100000) (27269190235109 / 100000) := by
  exact
    packedTile32768 272681216 272713984 12 1674 16513 28 _ _ (97119 / 5000) (1942383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272713984 :
    ThetaLowerSegment 272713984 272746752 (27269190235109 / 100000) (5454491856169 / 20000) := by
  exact
    packedTile32768 272713984 272746752 12 1683 16514 28 _ _ (242799 / 12500) (388479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272746752 :
    ThetaLowerSegment 272746752 272779520 (5454491856169 / 20000) (27275689498697 / 100000) := by
  exact
    packedTile32768 272746752 272779520 12 1663 16515 28 _ _ (485601 / 25000) (1942407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272779520 :
    ThetaLowerSegment 272779520 272812288 (27275689498697 / 100000) (27278908082009 / 100000) := by
  exact
    packedTile32768 272779520 272812288 12 1657 16516 28 _ _ (121401 / 6250) (1942419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272812288 :
    ThetaLowerSegment 272812288 272845056 (27278908082009 / 100000) (5456442818893 / 20000) := by
  exact
    packedTile32768 272812288 272845056 12 1702 16517 28 _ _ (485607 / 25000) (1942431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272845056 :
    ThetaLowerSegment 272845056 272877824 (5456442818893 / 20000) (5457101306053 / 20000) := by
  exact
    packedTile32768 272845056 272877824 12 1695 16518 28 _ _ (48561 / 2500) (1942443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272877824 :
    ThetaLowerSegment 272877824 272910592 (5457101306053 / 20000) (27288787331693 / 100000) := by
  exact
    packedTile32768 272877824 272910592 12 1689 16519 28 _ _ (485613 / 25000) (388491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272910592 :
    ThetaLowerSegment 272910592 272943360 (27288787331693 / 100000) (27292019591789 / 100000) := by
  exact
    packedTile32768 272910592 272943360 12 1664 16520 28 _ _ (60702 / 3125) (1942467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272943360 :
    ThetaLowerSegment 272943360 272976128 (27292019591789 / 100000) (27295271296613 / 100000) := by
  exact
    packedTile32768 272943360 272976128 12 1674 16520 28 _ _ (485619 / 25000) (1942479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell272976128 :
    ThetaLowerSegment 272976128 273008896 (27295271296613 / 100000) (5459708489281 / 20000) := by
  exact
    packedTile32768 272976128 273008896 12 1684 16521 28 _ _ (242811 / 12500) (1942491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273008896 :
    ThetaLowerSegment 273008896 273041664 (5459708489281 / 20000) (5460361946281 / 20000) := by
  exact
    packedTile32768 273008896 273041664 12 1682 16522 28 _ _ (777 / 40) (1942503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273041664 :
    ThetaLowerSegment 273041664 273074432 (5460361946281 / 20000) (27305166392141 / 100000) := by
  exact
    packedTile32768 273041664 273074432 12 1728 16523 28 _ _ (121407 / 6250) (388503 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273074432 :
    ThetaLowerSegment 273074432 273107200 (27305166392141 / 100000) (1092338048009 / 4000) := by
  exact
    packedTile32768 273074432 273107200 12 1691 16524 28 _ _ (485631 / 25000) (1942527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273107200 :
    ThetaLowerSegment 273107200 273139968 (1092338048009 / 4000) (27311669982377 / 100000) := by
  exact
    packedTile32768 273107200 273139968 12 1657 16525 28 _ _ (242817 / 12500) (1942539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273139968 :
    ThetaLowerSegment 273139968 273172736 (27311669982377 / 100000) (27314923750277 / 100000) := by
  exact
    packedTile32768 273139968 273172736 12 1675 16526 28 _ _ (485637 / 25000) (1942551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273172736 :
    ThetaLowerSegment 273172736 273205504 (27314923750277 / 100000) (27318132859397 / 100000) := by
  exact
    packedTile32768 273172736 273205504 12 1652 16527 28 _ _ (12141 / 625) (1942563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273205504 :
    ThetaLowerSegment 273205504 273238272 (27318132859397 / 100000) (27321382782353 / 100000) := by
  exact
    packedTile32768 273205504 273238272 12 1673 16528 28 _ _ (485643 / 25000) (77703 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273238272 :
    ThetaLowerSegment 273238272 273271040 (27321382782353 / 100000) (27324702658409 / 100000) := by
  exact
    packedTile32768 273238272 273271040 12 1709 16529 28 _ _ (242823 / 12500) (1942587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273271040 :
    ThetaLowerSegment 273271040 273303808 (27324702658409 / 100000) (5465587804669 / 20000) := by
  exact
    packedTile32768 273271040 273303808 12 1666 16530 28 _ _ (485649 / 25000) (1942599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273303808 :
    ThetaLowerSegment 273303808 273336576 (5465587804669 / 20000) (1093250435321 / 4000) := by
  exact
    packedTile32768 273303808 273336576 12 1710 16531 28 _ _ (121413 / 6250) (1942611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273336576 :
    ThetaLowerSegment 273336576 273369344 (1093250435321 / 4000) (5466911890357 / 20000) := by
  exact
    packedTile32768 273336576 273369344 12 1698 16532 28 _ _ (97131 / 5000) (1942623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273369344 :
    ThetaLowerSegment 273369344 273402112 (5466911890357 / 20000) (27337879409873 / 100000) := by
  exact
    packedTile32768 273369344 273402112 12 1709 16533 28 _ _ (242829 / 12500) (388527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273402112 :
    ThetaLowerSegment 273402112 273434880 (27337879409873 / 100000) (27341214929621 / 100000) := by
  exact
    packedTile32768 273402112 273434880 12 1717 16534 28 _ _ (485661 / 25000) (1942647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273434880 :
    ThetaLowerSegment 273434880 273467648 (27341214929621 / 100000) (27344490247637 / 100000) := by
  exact
    packedTile32768 273434880 273467648 12 1686 16535 28 _ _ (60708 / 3125) (1942659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273467648 :
    ThetaLowerSegment 273467648 273500416 (27344490247637 / 100000) (5469549231841 / 20000) := by
  exact
    packedTile32768 273467648 273500416 12 1676 16536 28 _ _ (485667 / 25000) (1942671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273500416 :
    ThetaLowerSegment 273500416 273533184 (5469549231841 / 20000) (5470213628401 / 20000) := by
  exact
    packedTile32768 273500416 273533184 12 1710 16537 28 _ _ (48567 / 2500) (1942683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273533184 :
    ThetaLowerSegment 273533184 273565952 (5470213628401 / 20000) (27354246386117 / 100000) := by
  exact
    packedTile32768 273533184 273565952 12 1636 16538 28 _ _ (485673 / 25000) (388539 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273565952 :
    ThetaLowerSegment 273565952 273598720 (27354246386117 / 100000) (5471508630961 / 20000) := by
  exact
    packedTile32768 273565952 273598720 12 1697 16539 28 _ _ (121419 / 6250) (1942707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273598720 :
    ThetaLowerSegment 273598720 273631488 (5471508630961 / 20000) (27360824402129 / 100000) := by
  exact
    packedTile32768 273598720 273631488 12 1689 16540 28 _ _ (485679 / 25000) (1942719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273631488 :
    ThetaLowerSegment 273631488 273664256 (27360824402129 / 100000) (27364037674241 / 100000) := by
  exact
    packedTile32768 273631488 273664256 12 1654 16541 28 _ _ (242841 / 12500) (1942731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273664256 :
    ThetaLowerSegment 273664256 273697024 (27364037674241 / 100000) (27367377244301 / 100000) := by
  exact
    packedTile32768 273664256 273697024 12 1719 16542 28 _ _ (97137 / 5000) (1942743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273697024 :
    ThetaLowerSegment 273697024 273729792 (27367377244301 / 100000) (27370666323437 / 100000) := by
  exact
    packedTile32768 273697024 273729792 12 1693 16543 28 _ _ (60711 / 3125) (388551 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273729792 :
    ThetaLowerSegment 273729792 273762560 (27370666323437 / 100000) (27373951537361 / 100000) := by
  exact
    packedTile32768 273729792 273762560 12 1691 16544 28 _ _ (485691 / 25000) (1942767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273762560 :
    ThetaLowerSegment 273762560 273795328 (27373951537361 / 100000) (27377295054857 / 100000) := by
  exact
    packedTile32768 273762560 273795328 12 1721 16545 28 _ _ (242847 / 12500) (1942779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273795328 :
    ThetaLowerSegment 273795328 273828096 (27377295054857 / 100000) (1095220881029 / 4000) := by
  exact
    packedTile32768 273795328 273828096 12 1661 16546 28 _ _ (485697 / 25000) (1942791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273828096 :
    ThetaLowerSegment 273828096 273860864 (1095220881029 / 4000) (1095352136597 / 4000) := by
  exact
    packedTile32768 273828096 273860864 12 1689 16547 28 _ _ (4857 / 250) (1942803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273860864 :
    ThetaLowerSegment 273860864 273893632 (1095352136597 / 4000) (27387104252513 / 100000) := by
  exact
    packedTile32768 273860864 273893632 12 1699 16548 28 _ _ (485703 / 25000) (388563 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273893632 :
    ThetaLowerSegment 273893632 273926400 (27387104252513 / 100000) (27390309912113 / 100000) := by
  exact
    packedTile32768 273893632 273926400 12 1650 16549 28 _ _ (242853 / 12500) (1942827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273926400 :
    ThetaLowerSegment 273926400 273959168 (27390309912113 / 100000) (27393682675409 / 100000) := by
  exact
    packedTile32768 273926400 273959168 12 1736 16550 28 _ _ (485709 / 25000) (1942839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273959168 :
    ThetaLowerSegment 273959168 273991936 (27393682675409 / 100000) (136985442431 / 500) := by
  exact
    packedTile32768 273959168 273991936 12 1753 16551 28 _ _ (1942847 / 100000) (38857 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell273991936 :
    ThetaLowerSegment 273991936 274024704 (136985442431 / 500) (27400354432179 / 100000) := by
  exact
    packedTile32768 273991936 274024704 12 1681 16552 28 _ _ (1942859 / 100000) (971431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274024704 :
    ThetaLowerSegment 274024704 274057472 (27400354432179 / 100000) (13701817970649 / 50000) := by
  exact
    packedTile32768 274024704 274057472 12 1689 16553 28 _ _ (1942871 / 100000) (971437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274057472 :
    ThetaLowerSegment 274057472 274090240 (13701817970649 / 50000) (6851724024743 / 25000) := by
  exact
    packedTile32768 274057472 274090240 12 1678 16554 28 _ _ (1942883 / 100000) (971443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274090240 :
    ThetaLowerSegment 274090240 274123008 (6851724024743 / 25000) (13705058709441 / 50000) := by
  exact
    packedTile32768 274090240 274123008 12 1658 16555 28 _ _ (388579 / 20000) (971449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274123008 :
    ThetaLowerSegment 274123008 274155776 (13705058709441 / 50000) (1713339501139 / 6250) := by
  exact
    packedTile32768 274123008 274155776 12 1706 16556 28 _ _ (1942907 / 100000) (194291 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274155776 :
    ThetaLowerSegment 274155776 274188544 (1713339501139 / 6250) (3427088958187 / 12500) := by
  exact
    packedTile32768 274155776 274188544 12 1688 16557 28 _ _ (1942919 / 100000) (971461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274188544 :
    ThetaLowerSegment 274188544 274221312 (3427088958187 / 12500) (5483998655191 / 20000) := by
  exact
    packedTile32768 274188544 274221312 12 1689 16558 28 _ _ (1942931 / 100000) (971467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274221312 :
    ThetaLowerSegment 274221312 274254080 (5483998655191 / 20000) (27423358453231 / 100000) := by
  exact
    packedTile32768 274221312 274254080 12 1732 16559 28 _ _ (1942943 / 100000) (971473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274254080 :
    ThetaLowerSegment 274254080 274286848 (27423358453231 / 100000) (1714166220861 / 6250) := by
  exact
    packedTile32768 274254080 274286848 12 1699 16560 28 _ _ (388591 / 20000) (971479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274286848 :
    ThetaLowerSegment 274286848 274319616 (1714166220861 / 6250) (27429960634709 / 100000) := by
  exact
    packedTile32768 274286848 274319616 12 1699 16561 28 _ _ (1942967 / 100000) (194297 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274319616 :
    ThetaLowerSegment 274319616 274352384 (27429960634709 / 100000) (27433217067513 / 100000) := by
  exact
    packedTile32768 274319616 274352384 12 1676 16562 28 _ _ (1942979 / 100000) (971491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274352384 :
    ThetaLowerSegment 274352384 274385152 (27433217067513 / 100000) (27436442432573 / 100000) := by
  exact
    packedTile32768 274352384 274385152 12 1660 16563 28 _ _ (1942991 / 100000) (971497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274385152 :
    ThetaLowerSegment 274385152 274417920 (27436442432573 / 100000) (1097592463991 / 4000) := by
  exact
    packedTile32768 274385152 274417920 12 1734 16564 28 _ _ (1943003 / 100000) (971503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274417920 :
    ThetaLowerSegment 274417920 274450688 (1097592463991 / 4000) (5488613618583 / 20000) := by
  exact
    packedTile32768 274417920 274450688 12 1676 16565 28 _ _ (388603 / 20000) (971509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274450688 :
    ThetaLowerSegment 274450688 274483456 (5488613618583 / 20000) (27446382896977 / 100000) := by
  exact
    packedTile32768 274450688 274483456 12 1706 16566 28 _ _ (1943027 / 100000) (194303 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274483456 :
    ThetaLowerSegment 274483456 274516224 (27446382896977 / 100000) (548993993291 / 2000) := by
  exact
    packedTile32768 274483456 274516224 12 1707 16567 28 _ _ (1943039 / 100000) (971521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274516224 :
    ThetaLowerSegment 274516224 274548992 (548993993291 / 2000) (3431621956067 / 12500) := by
  exact
    packedTile32768 274516224 274548992 12 1686 16568 28 _ _ (1943051 / 100000) (971527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274548992 :
    ThetaLowerSegment 274548992 274581760 (3431621956067 / 12500) (6864081372287 / 25000) := by
  exact
    packedTile32768 274548992 274581760 12 1724 16569 28 _ _ (1943063 / 100000) (971533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274581760 :
    ThetaLowerSegment 274581760 274614528 (6864081372287 / 25000) (858109389752 / 3125) := by
  exact
    packedTile32768 274581760 274614528 12 1634 16570 28 _ _ (971537 / 50000) (1943077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274614528 :
    ThetaLowerSegment 274614528 274647296 (858109389752 / 3125) (13731418375363 / 50000) := by
  exact
    packedTile32768 274614528 274647296 12 1717 16571 28 _ _ (971543 / 50000) (1943089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274647296 :
    ThetaLowerSegment 274647296 274680064 (13731418375363 / 50000) (13733050577683 / 50000) := by
  exact
    packedTile32768 274647296 274680064 12 1680 16572 28 _ _ (971549 / 50000) (1943101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274680064 :
    ThetaLowerSegment 274680064 274712832 (13733050577683 / 50000) (13734692505633 / 50000) := by
  exact
    packedTile32768 274680064 274712832 12 1690 16573 28 _ _ (194311 / 10000) (1943113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274712832 :
    ThetaLowerSegment 274712832 274745600 (13734692505633 / 50000) (1717042412691 / 6250) := by
  exact
    packedTile32768 274712832 274745600 12 1695 16574 28 _ _ (971561 / 50000) (3109 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274745600 :
    ThetaLowerSegment 274745600 274778368 (1717042412691 / 6250) (549517345719 / 2000) := by
  exact
    packedTile32768 274745600 274778368 12 1641 16575 28 _ _ (971567 / 50000) (1943137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274778368 :
    ThetaLowerSegment 274778368 274811136 (549517345719 / 2000) (13739563942469 / 50000) := by
  exact
    packedTile32768 274778368 274811136 12 1678 16576 28 _ _ (971573 / 50000) (1943149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274811136 :
    ThetaLowerSegment 274811136 274843904 (13739563942469 / 50000) (13741192308873 / 50000) := by
  exact
    packedTile32768 274811136 274843904 12 1676 16577 28 _ _ (971579 / 50000) (1943161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274843904 :
    ThetaLowerSegment 274843904 274876672 (13741192308873 / 50000) (6871395283099 / 25000) := by
  exact
    packedTile32768 274843904 274876672 12 1645 16578 28 _ _ (194317 / 10000) (1943173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274876672 :
    ThetaLowerSegment 274876672 274909440 (6871395283099 / 25000) (13744431583397 / 50000) := by
  exact
    packedTile32768 274876672 274909440 12 1689 16579 28 _ _ (971591 / 50000) (388637 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274909440 :
    ThetaLowerSegment 274909440 274942208 (13744431583397 / 50000) (3436524468063 / 12500) := by
  exact
    packedTile32768 274909440 274942208 12 1715 16580 28 _ _ (971597 / 50000) (1943197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274942208 :
    ThetaLowerSegment 274942208 274974976 (3436524468063 / 12500) (13747744739337 / 50000) := by
  exact
    packedTile32768 274942208 274974976 12 1695 16581 28 _ _ (971603 / 50000) (1943209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell274974976 :
    ThetaLowerSegment 274974976 275007744 (13747744739337 / 50000) (1718678810119 / 6250) := by
  exact
    packedTile32768 274974976 275007744 12 1735 16582 28 _ _ (971609 / 50000) (1943221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275007744 :
    ThetaLowerSegment 275007744 275040512 (1718678810119 / 6250) (2750207506267 / 10000) := by
  exact
    packedTile32768 275007744 275040512 12 1654 16583 28 _ _ (1943229 / 100000) (60726 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275040512 :
    ThetaLowerSegment 275040512 275073280 (2750207506267 / 10000) (27505275580597 / 100000) := by
  exact
    packedTile32768 275040512 275073280 12 1647 16584 28 _ _ (1943241 / 100000) (485811 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275073280 :
    ThetaLowerSegment 275073280 275106048 (27505275580597 / 100000) (27508478061541 / 100000) := by
  exact
    packedTile32768 275073280 275106048 12 1648 16585 28 _ _ (1943253 / 100000) (242907 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275106048 :
    ThetaLowerSegment 275106048 275138816 (27508478061541 / 100000) (27511859342641 / 100000) := by
  exact
    packedTile32768 275106048 275138816 12 1740 16586 28 _ _ (388653 / 20000) (485817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275138816 :
    ThetaLowerSegment 275138816 275171584 (27511859342641 / 100000) (27515077409353 / 100000) := by
  exact
    packedTile32768 275138816 275171584 12 1656 16587 28 _ _ (1943277 / 100000) (24291 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275171584 :
    ThetaLowerSegment 275171584 275204352 (27515077409353 / 100000) (6879583104607 / 25000) := by
  exact
    packedTile32768 275171584 275204352 12 1675 16588 28 _ _ (1943289 / 100000) (485823 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275204352 :
    ThetaLowerSegment 275204352 275237120 (6879583104607 / 25000) (27521731251877 / 100000) := by
  exact
    packedTile32768 275204352 275237120 12 1749 16589 28 _ _ (1943301 / 100000) (242913 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275237120 :
    ThetaLowerSegment 275237120 275269888 (27521731251877 / 100000) (13762502867141 / 50000) := by
  exact
    packedTile32768 275237120 275269888 12 1685 16590 28 _ _ (1943313 / 100000) (485829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275269888 :
    ThetaLowerSegment 275269888 275302656 (13762502867141 / 50000) (1720518607927 / 6250) := by
  exact
    packedTile32768 275269888 275302656 12 1694 16591 28 _ _ (77733 / 4000) (60729 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275302656 :
    ThetaLowerSegment 275302656 275335424 (1720518607927 / 6250) (13765783209833 / 50000) := by
  exact
    packedTile32768 275302656 275335424 12 1682 16592 28 _ _ (1943337 / 100000) (97167 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275335424 :
    ThetaLowerSegment 275335424 275368192 (13765783209833 / 50000) (27534883716409 / 100000) := by
  exact
    packedTile32768 275335424 275368192 12 1707 16593 28 _ _ (1943349 / 100000) (242919 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275368192 :
    ThetaLowerSegment 275368192 275400960 (27534883716409 / 100000) (27538169938169 / 100000) := by
  exact
    packedTile32768 275368192 275400960 12 1691 16594 28 _ _ (12146 / 625) (1943363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275400960 :
    ThetaLowerSegment 275400960 275433728 (27538169938169 / 100000) (27541395935689 / 100000) := by
  exact
    packedTile32768 275400960 275433728 12 1660 16595 28 _ _ (485843 / 25000) (15547 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275433728 :
    ThetaLowerSegment 275433728 275466496 (27541395935689 / 100000) (27544693858337 / 100000) := by
  exact
    packedTile32768 275433728 275466496 12 1697 16596 28 _ _ (242923 / 12500) (1943387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275466496 :
    ThetaLowerSegment 275466496 275499264 (27544693858337 / 100000) (5509592918761 / 20000) := by
  exact
    packedTile32768 275466496 275499264 12 1683 16597 28 _ _ (485849 / 25000) (1943399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275499264 :
    ThetaLowerSegment 275499264 275532032 (5509592918761 / 20000) (27551272274221 / 100000) := by
  exact
    packedTile32768 275499264 275532032 12 1702 16598 28 _ _ (121463 / 6250) (1943411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275532032 :
    ThetaLowerSegment 275532032 275564800 (27551272274221 / 100000) (27554649938181 / 100000) := by
  exact
    packedTile32768 275532032 275564800 12 1738 16599 28 _ _ (97171 / 5000) (1943423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275564800 :
    ThetaLowerSegment 275564800 275597568 (27554649938181 / 100000) (27557944055421 / 100000) := by
  exact
    packedTile32768 275564800 275597568 12 1695 16600 28 _ _ (242929 / 12500) (388687 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275597568 :
    ThetaLowerSegment 275597568 275630336 (27557944055421 / 100000) (27561174059349 / 100000) := by
  exact
    packedTile32768 275597568 275630336 12 1662 16601 28 _ _ (485861 / 25000) (1943447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275630336 :
    ThetaLowerSegment 275630336 275663104 (27561174059349 / 100000) (27564425461237 / 100000) := by
  exact
    packedTile32768 275630336 275663104 12 1673 16602 28 _ _ (60733 / 3125) (1943459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275663104 :
    ThetaLowerSegment 275663104 275695872 (27564425461237 / 100000) (27567774056601 / 100000) := by
  exact
    packedTile32768 275663104 275695872 12 1723 16603 28 _ _ (485867 / 25000) (1943471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275695872 :
    ThetaLowerSegment 275695872 275728640 (27567774056601 / 100000) (27570996344783 / 100000) := by
  exact
    packedTile32768 275695872 275728640 12 1658 16604 28 _ _ (1943479 / 100000) (971741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275728640 :
    ThetaLowerSegment 275728640 275761408 (27570996344783 / 100000) (3446791178981 / 12500) := by
  exact
    packedTile32768 275728640 275761408 12 1715 16605 28 _ _ (1943491 / 100000) (971747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275761408 :
    ThetaLowerSegment 275761408 275794176 (3446791178981 / 12500) (6894392798713 / 25000) := by
  exact
    packedTile32768 275761408 275794176 12 1668 16606 28 _ _ (1943503 / 100000) (971753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275794176 :
    ThetaLowerSegment 275794176 275826944 (6894392798713 / 25000) (27580807147327 / 100000) := by
  exact
    packedTile32768 275794176 275826944 12 1665 16607 28 _ _ (388703 / 20000) (971759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275826944 :
    ThetaLowerSegment 275826944 275859712 (27580807147327 / 100000) (13792060430431 / 50000) := by
  exact
    packedTile32768 275826944 275859712 12 1705 16608 28 _ _ (1943527 / 100000) (194353 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275859712 :
    ThetaLowerSegment 275859712 275892480 (13792060430431 / 50000) (6896851360443 / 25000) := by
  exact
    packedTile32768 275859712 275892480 12 1690 16609 28 _ _ (1943539 / 100000) (971771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275892480 :
    ThetaLowerSegment 275892480 275925248 (6896851360443 / 25000) (13795317811767 / 50000) := by
  exact
    packedTile32768 275892480 275925248 12 1662 16610 28 _ _ (1943551 / 100000) (971777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275925248 :
    ThetaLowerSegment 275925248 275958016 (13795317811767 / 50000) (27593968834079 / 100000) := by
  exact
    packedTile32768 275925248 275958016 12 1715 16610 28 _ _ (1943563 / 100000) (971783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275958016 :
    ThetaLowerSegment 275958016 275990784 (27593968834079 / 100000) (27597259304861 / 100000) := by
  exact
    packedTile32768 275958016 275990784 12 1693 16611 28 _ _ (971787 / 50000) (1943577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell275990784 :
    ThetaLowerSegment 275990784 276023552 (27597259304861 / 100000) (27600477883277 / 100000) := by
  exact
    packedTile32768 275990784 276023552 12 1656 16612 28 _ _ (971793 / 50000) (1943589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276023552 :
    ThetaLowerSegment 276023552 276056320 (27600477883277 / 100000) (5520743183509 / 20000) := by
  exact
    packedTile32768 276023552 276056320 12 1666 16613 28 _ _ (971799 / 50000) (1943601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276056320 :
    ThetaLowerSegment 276056320 276089088 (5520743183509 / 20000) (1104280646693 / 4000) := by
  exact
    packedTile32768 276056320 276089088 12 1698 16614 28 _ _ (194361 / 10000) (1943613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276089088 :
    ThetaLowerSegment 276089088 276121856 (1104280646693 / 4000) (27610221200003 / 100000) := by
  exact
    packedTile32768 276089088 276121856 12 1649 16615 28 _ _ (971811 / 50000) (15549 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276121856 :
    ThetaLowerSegment 276121856 276154624 (27610221200003 / 100000) (27613469012417 / 100000) := by
  exact
    packedTile32768 276121856 276154624 12 1671 16616 28 _ _ (971817 / 50000) (1943637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276154624 :
    ThetaLowerSegment 276154624 276187392 (27613469012417 / 100000) (27616747943219 / 100000) := by
  exact
    packedTile32768 276154624 276187392 12 1687 16617 28 _ _ (971823 / 50000) (1943649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276187392 :
    ThetaLowerSegment 276187392 276220160 (27616747943219 / 100000) (27620083260347 / 100000) := by
  exact
    packedTile32768 276187392 276220160 12 1716 16618 28 _ _ (971829 / 50000) (1943661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276220160 :
    ThetaLowerSegment 276220160 276252928 (27620083260347 / 100000) (27623403046999 / 100000) := by
  exact
    packedTile32768 276220160 276252928 12 1708 16619 28 _ _ (1943669 / 100000) (242959 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276252928 :
    ThetaLowerSegment 276252928 276285696 (27623403046999 / 100000) (5525328243909 / 20000) := by
  exact
    packedTile32768 276252928 276285696 12 1666 16620 28 _ _ (1943681 / 100000) (485921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276285696 :
    ThetaLowerSegment 276285696 276318464 (5525328243909 / 20000) (27629836650837 / 100000) := by
  exact
    packedTile32768 276285696 276318464 12 1644 16621 28 _ _ (1943693 / 100000) (121481 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276318464 :
    ThetaLowerSegment 276318464 276351232 (27629836650837 / 100000) (6908290582523 / 25000) := by
  exact
    packedTile32768 276318464 276351232 12 1711 16622 28 _ _ (388741 / 20000) (485927 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276351232 :
    ThetaLowerSegment 276351232 276384000 (6908290582523 / 25000) (13818231380779 / 50000) := by
  exact
    packedTile32768 276351232 276384000 12 1698 16623 28 _ _ (1943717 / 100000) (48593 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276384000 :
    ThetaLowerSegment 276384000 276416768 (13818231380779 / 50000) (863739198893 / 3125) := by
  exact
    packedTile32768 276384000 276416768 12 1642 16624 28 _ _ (1943729 / 100000) (485933 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276416768 :
    ThetaLowerSegment 276416768 276449536 (863739198893 / 3125) (3455363037441 / 12500) := by
  exact
    packedTile32768 276416768 276449536 12 1672 16625 28 _ _ (1943741 / 100000) (60742 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276449536 :
    ThetaLowerSegment 276449536 276482304 (3455363037441 / 12500) (691152592883 / 2500) := by
  exact
    packedTile32768 276449536 276482304 12 1646 16626 28 _ _ (242969 / 12500) (388751 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276482304 :
    ThetaLowerSegment 276482304 276515072 (691152592883 / 2500) (3456179901793 / 12500) := by
  exact
    packedTile32768 276482304 276515072 12 1716 16627 28 _ _ (485941 / 25000) (1943767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276515072 :
    ThetaLowerSegment 276515072 276547840 (3456179901793 / 12500) (3456593926081 / 12500) := by
  exact
    packedTile32768 276515072 276547840 12 1704 16628 28 _ _ (60743 / 3125) (1943779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276547840 :
    ThetaLowerSegment 276547840 276580608 (3456593926081 / 12500) (6913982375507 / 25000) := by
  exact
    packedTile32768 276547840 276580608 12 1635 16629 28 _ _ (485947 / 25000) (1943791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276580608 :
    ThetaLowerSegment 276580608 276613376 (6913982375507 / 25000) (6914796827707 / 25000) := by
  exact
    packedTile32768 276580608 276613376 12 1676 16630 28 _ _ (9719 / 500) (1943803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276613376 :
    ThetaLowerSegment 276613376 276646144 (6914796827707 / 25000) (6915605453499 / 25000) := by
  exact
    packedTile32768 276613376 276646144 12 1664 16631 28 _ _ (485953 / 25000) (388763 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276646144 :
    ThetaLowerSegment 276646144 276678912 (6915605453499 / 25000) (3458215789137 / 12500) := by
  exact
    packedTile32768 276646144 276678912 12 1700 16632 28 _ _ (1943823 / 100000) (971913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276678912 :
    ThetaLowerSegment 276678912 276711680 (3458215789137 / 12500) (13834556236833 / 50000) := by
  exact
    packedTile32768 276678912 276711680 12 1742 16633 28 _ _ (388767 / 20000) (971919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276711680 :
    ThetaLowerSegment 276711680 276744448 (13834556236833 / 50000) (13836255159111 / 50000) := by
  exact
    packedTile32768 276711680 276744448 12 1748 16634 28 _ _ (1943847 / 100000) (38877 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276744448 :
    ThetaLowerSegment 276744448 276777216 (13836255159111 / 50000) (13837915214697 / 50000) := by
  exact
    packedTile32768 276744448 276777216 12 1708 16635 28 _ _ (1943859 / 100000) (971931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276777216 :
    ThetaLowerSegment 276777216 276809984 (13837915214697 / 50000) (27679105852029 / 100000) := by
  exact
    packedTile32768 276777216 276809984 12 1685 16636 28 _ _ (1943871 / 100000) (971937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276809984 :
    ThetaLowerSegment 276809984 276842752 (27679105852029 / 100000) (1384122174957 / 5000) := by
  exact
    packedTile32768 276809984 276842752 12 1717 16637 28 _ _ (1943883 / 100000) (971943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276842752 :
    ThetaLowerSegment 276842752 276875520 (1384122174957 / 5000) (553714884657 / 2000) := by
  exact
    packedTile32768 276842752 276875520 12 1698 16638 28 _ _ (388779 / 20000) (971949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276875520 :
    ThetaLowerSegment 276875520 276908288 (553714884657 / 2000) (6922258816427 / 25000) := by
  exact
    packedTile32768 276875520 276908288 12 1693 16639 28 _ _ (971953 / 50000) (1943909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276908288 :
    ThetaLowerSegment 276908288 276941056 (6922258816427 / 25000) (13846147608097 / 50000) := by
  exact
    packedTile32768 276908288 276941056 12 1677 16640 28 _ _ (971959 / 50000) (1943921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276941056 :
    ThetaLowerSegment 276941056 276973824 (13846147608097 / 50000) (13847778565367 / 50000) := by
  exact
    packedTile32768 276941056 276973824 12 1678 16641 28 _ _ (194393 / 10000) (1943933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell276973824 :
    ThetaLowerSegment 276973824 277006592 (13847778565367 / 50000) (13849427028183 / 50000) := by
  exact
    packedTile32768 276973824 277006592 12 1696 16642 28 _ _ (971971 / 50000) (388789 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277006592 :
    ThetaLowerSegment 277006592 277039360 (13849427028183 / 50000) (6925527544829 / 25000) := by
  exact
    packedTile32768 277006592 277039360 12 1675 16643 28 _ _ (971977 / 50000) (1943957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277039360 :
    ThetaLowerSegment 277039360 277072128 (6925527544829 / 25000) (13852704544809 / 50000) := by
  exact
    packedTile32768 277039360 277072128 12 1697 16644 28 _ _ (971983 / 50000) (1943969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277072128 :
    ThetaLowerSegment 277072128 277104896 (13852704544809 / 50000) (6927169714733 / 25000) := by
  exact
    packedTile32768 277072128 277104896 12 1682 16645 28 _ _ (1943977 / 100000) (97199 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277104896 :
    ThetaLowerSegment 277104896 277137664 (6927169714733 / 25000) (221695666947 / 800) := by
  exact
    packedTile32768 277104896 277137664 12 1687 16646 28 _ _ (1943989 / 100000) (242999 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277137664 :
    ThetaLowerSegment 277137664 277170432 (221695666947 / 800) (13857564517003 / 50000) := by
  exact
    packedTile32768 277137664 277170432 12 1631 16647 28 _ _ (1944001 / 100000) (486001 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277170432 :
    ThetaLowerSegment 277170432 277203200 (13857564517003 / 50000) (5543684049603 / 20000) := by
  exact
    packedTile32768 277170432 277203200 12 1693 16648 28 _ _ (1944013 / 100000) (121501 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277203200 :
    ThetaLowerSegment 277203200 277235968 (5543684049603 / 20000) (5544335686783 / 20000) := by
  exact
    packedTile32768 277203200 277235968 12 1676 16649 28 _ _ (77761 / 4000) (486007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277235968 :
    ThetaLowerSegment 277235968 277268736 (5544335686783 / 20000) (27725020231799 / 100000) := by
  exact
    packedTile32768 277235968 277268736 12 1719 16650 28 _ _ (486009 / 25000) (1944039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277268736 :
    ThetaLowerSegment 277268736 277301504 (27725020231799 / 100000) (5545667744347 / 20000) := by
  exact
    packedTile32768 277268736 277301504 12 1707 16651 28 _ _ (121503 / 6250) (1944051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277301504 :
    ThetaLowerSegment 277301504 277334272 (5545667744347 / 20000) (5546301507907 / 20000) := by
  exact
    packedTile32768 277301504 277334272 12 1630 16652 28 _ _ (97203 / 5000) (1944063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277334272 :
    ThetaLowerSegment 277334272 277367040 (5546301507907 / 20000) (27734814406007 / 100000) := by
  exact
    packedTile32768 277334272 277367040 12 1701 16653 28 _ _ (243009 / 12500) (77763 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277367040 :
    ThetaLowerSegment 277367040 277399808 (27734814406007 / 100000) (27738115460639 / 100000) := by
  exact
    packedTile32768 277367040 277399808 12 1698 16654 28 _ _ (486021 / 25000) (1944087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277399808 :
    ThetaLowerSegment 277399808 277432576 (27738115460639 / 100000) (27741365989151 / 100000) := by
  exact
    packedTile32768 277399808 277432576 12 1672 16655 28 _ _ (60753 / 3125) (1944099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277432576 :
    ThetaLowerSegment 277432576 277465344 (27741365989151 / 100000) (5548931083639 / 20000) := by
  exact
    packedTile32768 277432576 277465344 12 1692 16656 28 _ _ (1944107 / 100000) (194411 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277465344 :
    ThetaLowerSegment 277465344 277498112 (5548931083639 / 20000) (6937003227927 / 25000) := by
  exact
    packedTile32768 277465344 277498112 12 1727 16657 28 _ _ (1944119 / 100000) (972061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277498112 :
    ThetaLowerSegment 277498112 277530880 (6937003227927 / 25000) (13875645358287 / 50000) := by
  exact
    packedTile32768 277498112 277530880 12 1686 16658 28 _ _ (1944131 / 100000) (972067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277530880 :
    ThetaLowerSegment 277530880 277563648 (13875645358287 / 50000) (5550925762021 / 20000) := by
  exact
    packedTile32768 277530880 277563648 12 1717 16659 28 _ _ (1944143 / 100000) (972073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277563648 :
    ThetaLowerSegment 277563648 277629184 (5550925762021 / 20000) (55522512869 / 200) := by
  exact
    packedTile32768 277563648 277629184 13 3409 16660 28 _ _ (388831 / 20000) (972079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277629184 :
    ThetaLowerSegment 277629184 277694720 (55522512869 / 200) (13883930403583 / 50000) := by
  exact
    packedTile32768 277629184 277694720 13 3397 16662 28 _ _ (972089 / 50000) (1944181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277694720 :
    ThetaLowerSegment 277694720 277760256 (13883930403583 / 50000) (13887194718741 / 50000) := by
  exact
    packedTile32768 277694720 277760256 13 3358 16664 28 _ _ (972101 / 50000) (388841 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277760256 :
    ThetaLowerSegment 277760256 277825792 (13887194718741 / 50000) (27780896758557 / 100000) := by
  exact
    packedTile32768 277760256 277825792 13 3347 16666 28 _ _ (77769 / 4000) (486057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277825792 :
    ThetaLowerSegment 277825792 277891328 (27780896758557 / 100000) (27787406104209 / 100000) := by
  exact
    packedTile32768 277825792 277891328 13 3348 16668 28 _ _ (1944249 / 100000) (486063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277891328 :
    ThetaLowerSegment 277891328 277956864 (27787406104209 / 100000) (13896982068519 / 50000) := by
  exact
    packedTile32768 277891328 277956864 13 3373 16670 28 _ _ (1944273 / 100000) (486069 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell277956864 :
    ThetaLowerSegment 277956864 278022400 (13896982068519 / 50000) (13900242652911 / 50000) := by
  exact
    packedTile32768 277956864 278022400 13 3354 16672 28 _ _ (243037 / 12500) (1944299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278022400 :
    ThetaLowerSegment 278022400 278087936 (13900242652911 / 50000) (13903518832111 / 50000) := by
  exact
    packedTile32768 278022400 278087936 13 3370 16674 28 _ _ (12152 / 625) (1944323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278087936 :
    ThetaLowerSegment 278087936 278153472 (13903518832111 / 50000) (27813607599219 / 100000) := by
  exact
    packedTile32768 278087936 278153472 13 3379 16675 28 _ _ (1944343 / 100000) (972173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278153472 :
    ThetaLowerSegment 278153472 278219008 (27813607599219 / 100000) (6955038570727 / 25000) := by
  exact
    packedTile32768 278153472 278219008 13 3367 16677 28 _ _ (1944367 / 100000) (194437 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278219008 :
    ThetaLowerSegment 278219008 278284544 (6955038570727 / 25000) (13913401076159 / 50000) := by
  exact
    packedTile32768 278219008 278284544 13 3419 16679 28 _ _ (194439 / 10000) (1944393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278284544 :
    ThetaLowerSegment 278284544 278350080 (13913401076159 / 50000) (2783331205039 / 10000) := by
  exact
    packedTile32768 278284544 278350080 13 3348 16681 28 _ _ (972207 / 50000) (1944417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278350080 :
    ThetaLowerSegment 278350080 278415616 (2783331205039 / 10000) (13919895458903 / 50000) := by
  exact
    packedTile32768 278350080 278415616 13 3332 16683 28 _ _ (972219 / 50000) (1944441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278415616 :
    ThetaLowerSegment 278415616 278481152 (13919895458903 / 50000) (27846229028177 / 100000) := by
  exact
    packedTile32768 278415616 278481152 13 3311 16685 28 _ _ (1944461 / 100000) (121529 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278481152 :
    ThetaLowerSegment 278481152 278513920 (27846229028177 / 100000) (27849507429887 / 100000) := by
  exact
    packedTile32768 278481152 278513920 12 1686 16687 28 _ _ (388897 / 20000) (243061 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278513920 :
    ThetaLowerSegment 278513920 278546688 (27849507429887 / 100000) (27852805295103 / 100000) := by
  exact
    packedTile32768 278513920 278546688 12 1696 16688 28 _ _ (121531 / 6250) (1944499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278546688 :
    ThetaLowerSegment 278546688 278579456 (27852805295103 / 100000) (5571217913823 / 20000) := by
  exact
    packedTile32768 278546688 278579456 12 1689 16689 28 _ _ (486127 / 25000) (1944511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278579456 :
    ThetaLowerSegment 278579456 278612224 (5571217913823 / 20000) (5571870105831 / 20000) := by
  exact
    packedTile32768 278579456 278612224 12 1677 16690 28 _ _ (48613 / 2500) (1944523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278612224 :
    ThetaLowerSegment 278612224 278644992 (5571870105831 / 20000) (5572523468583 / 20000) := by
  exact
    packedTile32768 278612224 278644992 12 1680 16691 28 _ _ (486133 / 25000) (388907 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278644992 :
    ThetaLowerSegment 278644992 278677760 (5572523468583 / 20000) (6966474446739 / 25000) := by
  exact
    packedTile32768 278644992 278677760 12 1687 16692 28 _ _ (1944543 / 100000) (972273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278677760 :
    ThetaLowerSegment 278677760 278710528 (6966474446739 / 25000) (27869143249251 / 100000) := by
  exact
    packedTile32768 278677760 278710528 12 1669 16693 28 _ _ (388911 / 20000) (972279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278710528 :
    ThetaLowerSegment 278710528 278743296 (27869143249251 / 100000) (27872417900079 / 100000) := by
  exact
    packedTile32768 278710528 278743296 12 1684 16694 28 _ _ (1944567 / 100000) (194457 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278743296 :
    ThetaLowerSegment 278743296 278776064 (27872417900079 / 100000) (27875610898797 / 100000) := by
  exact
    packedTile32768 278743296 278776064 12 1642 16695 28 _ _ (1944579 / 100000) (972291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278776064 :
    ThetaLowerSegment 278776064 278808832 (27875610898797 / 100000) (27878910868027 / 100000) := by
  exact
    packedTile32768 278776064 278808832 12 1697 16696 28 _ _ (194459 / 10000) (1944593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278808832 :
    ThetaLowerSegment 278808832 278841600 (27878910868027 / 100000) (27882191411601 / 100000) := by
  exact
    packedTile32768 278808832 278841600 12 1687 16697 28 _ _ (972301 / 50000) (388921 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278841600 :
    ThetaLowerSegment 278841600 278874368 (27882191411601 / 100000) (27885403913929 / 100000) := by
  exact
    packedTile32768 278841600 278874368 12 1652 16698 28 _ _ (972307 / 50000) (1944617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278874368 :
    ThetaLowerSegment 278874368 278907136 (27885403913929 / 100000) (27888626159211 / 100000) := by
  exact
    packedTile32768 278874368 278907136 12 1657 16699 28 _ _ (972313 / 50000) (1944629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278907136 :
    ThetaLowerSegment 278907136 278939904 (27888626159211 / 100000) (6973002943057 / 25000) := by
  exact
    packedTile32768 278907136 278939904 12 1741 16700 28 _ _ (1944637 / 100000) (12154 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278939904 :
    ThetaLowerSegment 278939904 278972672 (6973002943057 / 25000) (6973831363531 / 25000) := by
  exact
    packedTile32768 278939904 278972672 12 1704 16701 28 _ _ (1944649 / 100000) (486163 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell278972672 :
    ThetaLowerSegment 278972672 279005440 (6973831363531 / 25000) (2789852636613 / 10000) := by
  exact
    packedTile32768 278972672 279005440 12 1646 16702 28 _ _ (1944661 / 100000) (243083 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279005440 :
    ThetaLowerSegment 279005440 279038208 (2789852636613 / 10000) (27901775914713 / 100000) := by
  exact
    packedTile32768 279005440 279038208 12 1671 16703 28 _ _ (1944673 / 100000) (486169 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279038208 :
    ThetaLowerSegment 279038208 279070976 (27901775914713 / 100000) (27905093545617 / 100000) := by
  exact
    packedTile32768 279038208 279070976 12 1706 16704 28 _ _ (486171 / 25000) (1944687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279070976 :
    ThetaLowerSegment 279070976 279103744 (27905093545617 / 100000) (5581663570317 / 20000) := by
  exact
    packedTile32768 279070976 279103744 12 1658 16705 28 _ _ (243087 / 12500) (1944699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279103744 :
    ThetaLowerSegment 279103744 279136512 (5581663570317 / 20000) (27911579126901 / 100000) := by
  exact
    packedTile32768 279103744 279136512 12 1677 16706 28 _ _ (486177 / 25000) (1944711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279136512 :
    ThetaLowerSegment 279136512 279169280 (27911579126901 / 100000) (27914838477621 / 100000) := by
  exact
    packedTile32768 279136512 279169280 12 1676 16707 28 _ _ (24309 / 1250) (1944723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279169280 :
    ThetaLowerSegment 279169280 279202048 (27914838477621 / 100000) (1744879778421 / 6250) := by
  exact
    packedTile32768 279169280 279202048 12 1665 16708 28 _ _ (1944731 / 100000) (972367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279202048 :
    ThetaLowerSegment 279202048 279234816 (1744879778421 / 6250) (13960700982633 / 50000) := by
  exact
    packedTile32768 279202048 279234816 12 1710 16709 28 _ _ (1944743 / 100000) (972373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279234816 :
    ThetaLowerSegment 279234816 279267584 (13960700982633 / 50000) (6981162426529 / 25000) := by
  exact
    packedTile32768 279234816 279267584 12 1670 16710 28 _ _ (388951 / 20000) (972379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279267584 :
    ThetaLowerSegment 279267584 279300352 (6981162426529 / 25000) (6981979228669 / 25000) := by
  exact
    packedTile32768 279267584 279300352 12 1680 16711 28 _ _ (1944767 / 100000) (194477 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279300352 :
    ThetaLowerSegment 279300352 279333120 (6981979228669 / 25000) (13965618325361 / 50000) := by
  exact
    packedTile32768 279300352 279333120 12 1707 16712 28 _ _ (972389 / 50000) (1944781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279333120 :
    ThetaLowerSegment 279333120 279365888 (13965618325361 / 50000) (13967269452071 / 50000) := by
  exact
    packedTile32768 279333120 279365888 12 1698 16713 28 _ _ (194479 / 10000) (1944793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279365888 :
    ThetaLowerSegment 279365888 279398656 (13967269452071 / 50000) (13968885582533 / 50000) := by
  exact
    packedTile32768 279365888 279398656 12 1662 16714 28 _ _ (972401 / 50000) (388961 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279398656 :
    ThetaLowerSegment 279398656 279431424 (13968885582533 / 50000) (6985288299153 / 25000) := by
  exact
    packedTile32768 279398656 279431424 12 1739 16715 28 _ _ (972407 / 50000) (1944817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279431424 :
    ThetaLowerSegment 279431424 279464192 (6985288299153 / 25000) (27944336875137 / 100000) := by
  exact
    packedTile32768 279431424 279464192 12 1637 16716 28 _ _ (77793 / 4000) (486207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279464192 :
    ThetaLowerSegment 279464192 279496960 (27944336875137 / 100000) (13973795293719 / 50000) := by
  exact
    packedTile32768 279464192 279496960 12 1673 16717 28 _ _ (1944837 / 100000) (48621 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279496960 :
    ThetaLowerSegment 279496960 279529728 (13973795293719 / 50000) (27950910444681 / 100000) := by
  exact
    packedTile32768 279496960 279529728 12 1707 16718 28 _ _ (1944849 / 100000) (486213 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279529728 :
    ThetaLowerSegment 279529728 279562496 (27950910444681 / 100000) (27954119463681 / 100000) := by
  exact
    packedTile32768 279529728 279562496 12 1650 16719 28 _ _ (97243 / 5000) (1944863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279562496 :
    ThetaLowerSegment 279562496 279595264 (27954119463681 / 100000) (5591507320757 / 20000) := by
  exact
    packedTile32768 279562496 279595264 12 1757 16720 28 _ _ (243109 / 12500) (15559 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279595264 :
    ThetaLowerSegment 279595264 279628032 (5591507320757 / 20000) (1118434494217 / 4000) := by
  exact
    packedTile32768 279595264 279628032 12 1710 16721 28 _ _ (486221 / 25000) (1944887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279628032 :
    ThetaLowerSegment 279628032 279660800 (1118434494217 / 4000) (27964192017377 / 100000) := by
  exact
    packedTile32768 279628032 279660800 12 1712 16722 28 _ _ (60778 / 3125) (1944899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279660800 :
    ThetaLowerSegment 279660800 279693568 (27964192017377 / 100000) (13983724868301 / 50000) := by
  exact
    packedTile32768 279660800 279693568 12 1675 16723 28 _ _ (1944907 / 100000) (194491 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279693568 :
    ThetaLowerSegment 279693568 279726336 (13983724868301 / 50000) (27970812501553 / 100000) := by
  exact
    packedTile32768 279693568 279726336 12 1729 16724 28 _ _ (1944919 / 100000) (972461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279726336 :
    ThetaLowerSegment 279726336 279759104 (27970812501553 / 100000) (27974134443701 / 100000) := by
  exact
    packedTile32768 279726336 279759104 12 1708 16725 28 _ _ (1944931 / 100000) (972467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279759104 :
    ThetaLowerSegment 279759104 279824640 (27974134443701 / 100000) (44769108461 / 160) := by
  exact
    packedTile32768 279759104 279824640 13 3372 16726 28 _ _ (972471 / 50000) (388989 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279824640 :
    ThetaLowerSegment 279824640 279890176 (44769108461 / 160) (27987099506129 / 100000) := by
  exact
    packedTile32768 279824640 279890176 13 3294 16727 28 _ _ (972483 / 50000) (1944969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279890176 :
    ThetaLowerSegment 279890176 279922944 (27987099506129 / 100000) (27990367087649 / 100000) := by
  exact
    packedTile32768 279890176 279922944 12 1680 16729 28 _ _ (1944989 / 100000) (60781 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279922944 :
    ThetaLowerSegment 279922944 279955712 (27990367087649 / 100000) (6998421801089 / 25000) := by
  exact
    packedTile32768 279922944 279955712 12 1707 16730 28 _ _ (1945001 / 100000) (486251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279955712 :
    ThetaLowerSegment 279955712 279988480 (6998421801089 / 25000) (6999246486601 / 25000) := by
  exact
    packedTile32768 279955712 279988480 12 1696 16731 28 _ _ (1945013 / 100000) (243127 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell279988480 :
    ThetaLowerSegment 279988480 280021248 (6999246486601 / 25000) (7000064369193 / 25000) := by
  exact
    packedTile32768 279988480 280021248 12 1682 16732 28 _ _ (60782 / 3125) (1945027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280021248 :
    ThetaLowerSegment 280021248 280054016 (7000064369193 / 25000) (7000883229349 / 25000) := by
  exact
    packedTile32768 280021248 280054016 12 1684 16733 28 _ _ (486259 / 25000) (1945039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280054016 :
    ThetaLowerSegment 280054016 280086784 (7000883229349 / 25000) (1400341294183 / 5000) := by
  exact
    packedTile32768 280054016 280086784 12 1693 16734 28 _ _ (243131 / 12500) (1945051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280086784 :
    ThetaLowerSegment 280086784 280119552 (1400341294183 / 5000) (1400503512187 / 5000) := by
  exact
    packedTile32768 280086784 280119552 12 1668 16735 28 _ _ (97253 / 5000) (1945063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280119552 :
    ThetaLowerSegment 280119552 280152320 (1400503512187 / 5000) (28013351578517 / 100000) := by
  exact
    packedTile32768 280119552 280152320 12 1687 16736 28 _ _ (1945071 / 100000) (972537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280152320 :
    ThetaLowerSegment 280152320 280185088 (28013351578517 / 100000) (28016701011443 / 100000) := by
  exact
    packedTile32768 280152320 280185088 12 1722 16737 28 _ _ (1945083 / 100000) (972543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280185088 :
    ThetaLowerSegment 280185088 280250624 (28016701011443 / 100000) (14011677590719 / 50000) := by
  exact
    packedTile32768 280185088 280250624 13 3421 16738 28 _ _ (389019 / 20000) (972549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280250624 :
    ThetaLowerSegment 280250624 280316160 (14011677590719 / 50000) (14014943443841 / 50000) := by
  exact
    packedTile32768 280250624 280316160 13 3358 16740 28 _ _ (972559 / 50000) (1945121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280316160 :
    ThetaLowerSegment 280316160 280381696 (14014943443841 / 50000) (280363019627 / 1000) := by
  exact
    packedTile32768 280316160 280381696 13 3298 16742 28 _ _ (1945141 / 100000) (243143 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280381696 :
    ThetaLowerSegment 280381696 280414464 (280363019627 / 1000) (5607902686023 / 20000) := by
  exact
    packedTile32768 280381696 280414464 12 1651 16744 28 _ _ (389033 / 20000) (121573 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280414464 :
    ThetaLowerSegment 280414464 280447232 (5607902686023 / 20000) (5608569881391 / 20000) := by
  exact
    packedTile32768 280414464 280447232 12 1715 16745 28 _ _ (243147 / 12500) (1945179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280447232 :
    ThetaLowerSegment 280447232 280480000 (5608569881391 / 20000) (28046181513999 / 100000) := by
  exact
    packedTile32768 280447232 280480000 12 1713 16746 28 _ _ (486297 / 25000) (1945191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280480000 :
    ThetaLowerSegment 280480000 280545536 (28046181513999 / 100000) (28052832152799 / 100000) := by
  exact
    packedTile32768 280480000 280545536 13 3419 16747 28 _ _ (4863 / 250) (1945203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280545536 :
    ThetaLowerSegment 280545536 280611072 (28052832152799 / 100000) (28059461472783 / 100000) := by
  exact
    packedTile32768 280545536 280611072 13 3408 16749 28 _ _ (1945223 / 100000) (972613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280611072 :
    ThetaLowerSegment 280611072 280676608 (28059461472783 / 100000) (5613201834837 / 20000) := by
  exact
    packedTile32768 280611072 280676608 13 3366 16751 28 _ _ (1945247 / 100000) (7781 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280676608 :
    ThetaLowerSegment 280676608 280742144 (5613201834837 / 20000) (5614488825469 / 20000) := by
  exact
    packedTile32768 280676608 280742144 13 3308 16753 28 _ _ (194527 / 10000) (1945273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280742144 :
    ThetaLowerSegment 280742144 280807680 (5614488825469 / 20000) (28079034780029 / 100000) := by
  exact
    packedTile32768 280742144 280807680 13 3388 16755 28 _ _ (1945293 / 100000) (121581 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280807680 :
    ThetaLowerSegment 280807680 280873216 (28079034780029 / 100000) (14042763151429 / 50000) := by
  exact
    packedTile32768 280807680 280873216 13 3337 16757 28 _ _ (1945317 / 100000) (48633 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280873216 :
    ThetaLowerSegment 280873216 280938752 (14042763151429 / 50000) (14046032295299 / 50000) := by
  exact
    packedTile32768 280873216 280938752 13 3361 16759 28 _ _ (97267 / 5000) (1945343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell280938752 :
    ThetaLowerSegment 280938752 281004288 (14046032295299 / 50000) (28098556266929 / 100000) := by
  exact
    packedTile32768 280938752 281004288 13 3337 16761 28 _ _ (1945363 / 100000) (972683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281004288 :
    ThetaLowerSegment 281004288 281037056 (28098556266929 / 100000) (28101871206377 / 100000) := by
  exact
    packedTile32768 281004288 281037056 12 1704 16763 28 _ _ (1945387 / 100000) (194539 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281037056 :
    ThetaLowerSegment 281037056 281069824 (28101871206377 / 100000) (28105149202007 / 100000) := by
  exact
    packedTile32768 281037056 281069824 12 1685 16764 28 _ _ (972699 / 50000) (1945401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281069824 :
    ThetaLowerSegment 281069824 281102592 (28105149202007 / 100000) (28108423327037 / 100000) := by
  exact
    packedTile32768 281069824 281102592 12 1683 16765 28 _ _ (194541 / 10000) (1945413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281102592 :
    ThetaLowerSegment 281102592 281135360 (28108423327037 / 100000) (28111730544437 / 100000) := by
  exact
    packedTile32768 281102592 281135360 12 1700 16766 28 _ _ (972711 / 50000) (77817 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281135360 :
    ThetaLowerSegment 281135360 281200896 (28111730544437 / 100000) (28118282762781 / 100000) := by
  exact
    packedTile32768 281135360 281200896 13 3368 16767 28 _ _ (1945433 / 100000) (486359 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281200896 :
    ThetaLowerSegment 281200896 281266432 (28118282762781 / 100000) (28124920658653 / 100000) := by
  exact
    packedTile32768 281200896 281266432 13 3412 16769 28 _ _ (121591 / 6250) (1945459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281266432 :
    ThetaLowerSegment 281266432 281331968 (28124920658653 / 100000) (28131486653653 / 100000) := by
  exact
    packedTile32768 281266432 281331968 13 3375 16770 28 _ _ (48637 / 2500) (1945483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281331968 :
    ThetaLowerSegment 281331968 281397504 (28131486653653 / 100000) (28138023543733 / 100000) := by
  exact
    packedTile32768 281331968 281397504 13 3360 16772 28 _ _ (1945503 / 100000) (972753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281397504 :
    ThetaLowerSegment 281397504 281463040 (28138023543733 / 100000) (5628928444637 / 20000) := by
  exact
    packedTile32768 281397504 281463040 13 3402 16774 28 _ _ (972763 / 50000) (1945529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281463040 :
    ThetaLowerSegment 281463040 281528576 (5628928444637 / 20000) (5630243636437 / 20000) := by
  exact
    packedTile32768 281463040 281528576 13 3380 16776 28 _ _ (38911 / 2000) (1945553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281528576 :
    ThetaLowerSegment 281528576 281594112 (5630243636437 / 20000) (7039418884743 / 25000) := by
  exact
    packedTile32768 281528576 281594112 13 3319 16778 28 _ _ (1945573 / 100000) (243197 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281594112 :
    ThetaLowerSegment 281594112 281659648 (7039418884743 / 25000) (3520528781487 / 12500) := by
  exact
    packedTile32768 281594112 281659648 13 3369 16780 28 _ _ (486399 / 25000) (1945599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281659648 :
    ThetaLowerSegment 281659648 281725184 (3520528781487 / 12500) (14085444080057 / 50000) := by
  exact
    packedTile32768 281659648 281725184 13 3422 16782 28 _ _ (1945619 / 100000) (972811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281725184 :
    ThetaLowerSegment 281725184 281790720 (14085444080057 / 50000) (14088712760297 / 50000) := by
  exact
    packedTile32768 281725184 281790720 13 3360 16784 28 _ _ (1945643 / 100000) (972823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281790720 :
    ThetaLowerSegment 281790720 281856256 (14088712760297 / 50000) (3522996099419 / 12500) := by
  exact
    packedTile32768 281790720 281856256 13 3363 16786 28 _ _ (972833 / 50000) (1945669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281856256 :
    ThetaLowerSegment 281856256 281921792 (3522996099419 / 12500) (14095266775019 / 50000) := by
  exact
    packedTile32768 281856256 281921792 13 3374 16788 28 _ _ (1945689 / 100000) (486423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281921792 :
    ThetaLowerSegment 281921792 281987328 (14095266775019 / 50000) (2819711784283 / 10000) := by
  exact
    packedTile32768 281921792 281987328 13 3384 16790 28 _ _ (1945713 / 100000) (486429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell281987328 :
    ThetaLowerSegment 281987328 282052864 (2819711784283 / 10000) (14101796626119 / 50000) := by
  exact
    packedTile32768 281987328 282052864 13 3328 16792 28 _ _ (243217 / 12500) (1945739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282052864 :
    ThetaLowerSegment 282052864 282118400 (14101796626119 / 50000) (14105026586059 / 50000) := by
  exact
    packedTile32768 282052864 282118400 13 3320 16794 28 _ _ (1945759 / 100000) (972881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282118400 :
    ThetaLowerSegment 282118400 282183936 (14105026586059 / 50000) (14108307174511 / 50000) := by
  exact
    packedTile32768 282118400 282183936 13 3372 16796 28 _ _ (972891 / 50000) (389157 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282183936 :
    ThetaLowerSegment 282183936 282249472 (14108307174511 / 50000) (28223049126157 / 100000) := by
  exact
    packedTile32768 282183936 282249472 13 3307 16798 28 _ _ (389161 / 20000) (121613 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282249472 :
    ThetaLowerSegment 282249472 282282240 (28223049126157 / 100000) (5645279968739 / 20000) := by
  exact
    packedTile32768 282249472 282282240 12 1722 16800 28 _ _ (1945829 / 100000) (243229 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282282240 :
    ThetaLowerSegment 282282240 282347776 (5645279968739 / 20000) (5646588740723 / 20000) := by
  exact
    packedTile32768 282282240 282347776 13 3363 16801 28 _ _ (24323 / 1250) (1945843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282347776 :
    ThetaLowerSegment 282347776 282413312 (5646588740723 / 20000) (28239512940479 / 100000) := by
  exact
    packedTile32768 282347776 282413312 13 3376 16803 28 _ _ (243233 / 12500) (1945867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282413312 :
    ThetaLowerSegment 282413312 282478848 (28239512940479 / 100000) (28246082254991 / 100000) := by
  exact
    packedTile32768 282413312 282478848 13 3376 16805 28 _ _ (1945887 / 100000) (194589 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282478848 :
    ThetaLowerSegment 282478848 282544384 (28246082254991 / 100000) (28252649701241 / 100000) := by
  exact
    packedTile32768 282478848 282544384 13 3375 16807 28 _ _ (194591 / 10000) (1945913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282544384 :
    ThetaLowerSegment 282544384 282609920 (28252649701241 / 100000) (28259332035163 / 100000) := by
  exact
    packedTile32768 282544384 282609920 13 3434 16809 28 _ _ (1945933 / 100000) (121621 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282609920 :
    ThetaLowerSegment 282609920 282675456 (28259332035163 / 100000) (28265812068643 / 100000) := by
  exact
    packedTile32768 282609920 282675456 13 3330 16811 28 _ _ (486489 / 25000) (1945959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282675456 :
    ThetaLowerSegment 282675456 282740992 (28265812068643 / 100000) (2827241477539 / 10000) := by
  exact
    packedTile32768 282675456 282740992 13 3393 16812 28 _ _ (1945979 / 100000) (972991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282740992 :
    ThetaLowerSegment 282740992 282806528 (2827241477539 / 10000) (7069727633351 / 25000) := by
  exact
    packedTile32768 282740992 282806528 13 3338 16814 28 _ _ (1946003 / 100000) (973003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282806528 :
    ThetaLowerSegment 282806528 282872064 (7069727633351 / 25000) (7071358403139 / 25000) := by
  exact
    packedTile32768 282806528 282872064 13 3352 16816 28 _ _ (973013 / 50000) (1946029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282872064 :
    ThetaLowerSegment 282872064 282937600 (7071358403139 / 25000) (28291865304501 / 100000) := by
  exact
    packedTile32768 282872064 282937600 13 3305 16818 28 _ _ (1946049 / 100000) (486513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282937600 :
    ThetaLowerSegment 282937600 282970368 (28291865304501 / 100000) (28295189195477 / 100000) := by
  exact
    packedTile32768 282937600 282970368 12 1708 16820 28 _ _ (243259 / 12500) (77843 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell282970368 :
    ThetaLowerSegment 282970368 283035904 (28295189195477 / 100000) (5660356116397 / 20000) := by
  exact
    packedTile32768 282970368 283035904 13 3387 16821 28 _ _ (486521 / 25000) (1946087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283035904 :
    ThetaLowerSegment 283035904 283101440 (5660356116397 / 20000) (28308331178147 / 100000) := by
  exact
    packedTile32768 283035904 283101440 13 3366 16823 28 _ _ (1946107 / 100000) (194611 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283101440 :
    ThetaLowerSegment 283101440 283166976 (28308331178147 / 100000) (28314796222007 / 100000) := by
  exact
    packedTile32768 283101440 283166976 13 3322 16825 28 _ _ (194613 / 10000) (1946133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283166976 :
    ThetaLowerSegment 283166976 283199744 (28314796222007 / 100000) (7079511087841 / 25000) := by
  exact
    packedTile32768 283166976 283199744 12 1669 16827 28 _ _ (1946153 / 100000) (486539 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283199744 :
    ThetaLowerSegment 283199744 283232512 (7079511087841 / 25000) (28321257469779 / 100000) := by
  exact
    packedTile32768 283199744 283232512 12 1651 16828 28 _ _ (389233 / 20000) (243271 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283232512 :
    ThetaLowerSegment 283232512 283265280 (28321257469779 / 100000) (28324511476051 / 100000) := by
  exact
    packedTile32768 283232512 283265280 12 1672 16829 28 _ _ (60818 / 3125) (1946179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283265280 :
    ThetaLowerSegment 283265280 283298048 (28324511476051 / 100000) (5665565166843 / 20000) := by
  exact
    packedTile32768 283265280 283298048 12 1703 16830 28 _ _ (486547 / 25000) (1946191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283298048 :
    ThetaLowerSegment 283298048 283330816 (5665565166843 / 20000) (5666231545723 / 20000) := by
  exact
    packedTile32768 283298048 283330816 12 1712 16831 28 _ _ (9731 / 500) (1946203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283330816 :
    ThetaLowerSegment 283330816 283363584 (5666231545723 / 20000) (3541809988849 / 12500) := by
  exact
    packedTile32768 283330816 283363584 12 1707 16832 28 _ _ (1946211 / 100000) (973107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283363584 :
    ThetaLowerSegment 283363584 283396352 (3541809988849 / 12500) (354221285701 / 1250) := by
  exact
    packedTile32768 283363584 283396352 12 1656 16833 28 _ _ (1946223 / 100000) (973113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283396352 :
    ThetaLowerSegment 283396352 283429120 (354221285701 / 1250) (14170502807589 / 50000) := by
  exact
    packedTile32768 283396352 283429120 12 1697 16834 28 _ _ (973117 / 50000) (1946237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283429120 :
    ThetaLowerSegment 283429120 283461888 (14170502807589 / 50000) (1417210554117 / 5000) := by
  exact
    packedTile32768 283429120 283461888 12 1647 16835 28 _ _ (973123 / 50000) (1946249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283461888 :
    ThetaLowerSegment 283461888 283494656 (1417210554117 / 5000) (14173718988223 / 50000) := by
  exact
    packedTile32768 283461888 283494656 12 1658 16836 28 _ _ (1946257 / 100000) (97313 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283494656 :
    ThetaLowerSegment 283494656 283527424 (14173718988223 / 50000) (14175373316873 / 50000) := by
  exact
    packedTile32768 283494656 283527424 12 1700 16837 28 _ _ (1946269 / 100000) (60821 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283527424 :
    ThetaLowerSegment 283527424 283560192 (14175373316873 / 50000) (14177014030913 / 50000) := by
  exact
    packedTile32768 283527424 283560192 12 1686 16838 28 _ _ (48657 / 2500) (1946283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283560192 :
    ThetaLowerSegment 283560192 283592960 (14177014030913 / 50000) (14178707304953 / 50000) := by
  exact
    packedTile32768 283560192 283592960 12 1740 16839 28 _ _ (486573 / 25000) (389259 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283592960 :
    ThetaLowerSegment 283592960 283625728 (14178707304953 / 50000) (14180365555961 / 50000) := by
  exact
    packedTile32768 283592960 283625728 12 1704 16840 28 _ _ (60822 / 3125) (1946307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283625728 :
    ThetaLowerSegment 283625728 283691264 (14180365555961 / 50000) (28367373885017 / 100000) := by
  exact
    packedTile32768 283625728 283691264 13 3413 16841 28 _ _ (389263 / 20000) (973159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283691264 :
    ThetaLowerSegment 283691264 283756800 (28367373885017 / 100000) (28373975863513 / 100000) := by
  exact
    packedTile32768 283691264 283756800 13 3392 16843 28 _ _ (973169 / 50000) (1946341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283756800 :
    ThetaLowerSegment 283756800 283822336 (28373975863513 / 100000) (5676103905839 / 20000) := by
  exact
    packedTile32768 283756800 283822336 13 3362 16845 28 _ _ (1946361 / 100000) (486591 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283822336 :
    ThetaLowerSegment 283822336 283887872 (5676103905839 / 20000) (28387082736043 / 100000) := by
  exact
    packedTile32768 283822336 283887872 13 3372 16847 28 _ _ (121649 / 6250) (1946387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283887872 :
    ThetaLowerSegment 283887872 283953408 (28387082736043 / 100000) (7098393500847 / 25000) := by
  exact
    packedTile32768 283887872 283953408 13 3335 16848 28 _ _ (1946407 / 100000) (194641 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell283953408 :
    ThetaLowerSegment 283953408 284018944 (7098393500847 / 25000) (3550011331797 / 12500) := by
  exact
    packedTile32768 283953408 284018944 13 3348 16850 28 _ _ (1946431 / 100000) (973217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284018944 :
    ThetaLowerSegment 284018944 284084480 (3550011331797 / 12500) (1775410041717 / 6250) := by
  exact
    packedTile32768 284018944 284084480 13 3324 16852 28 _ _ (973227 / 50000) (1946457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284084480 :
    ThetaLowerSegment 284084480 284117248 (1775410041717 / 6250) (1775616368279 / 6250) := by
  exact
    packedTile32768 284084480 284117248 12 1696 16854 28 _ _ (1946477 / 100000) (24331 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284117248 :
    ThetaLowerSegment 284117248 284182784 (1775616368279 / 6250) (355205804747 / 1250) := by
  exact
    packedTile32768 284117248 284182784 13 3392 16855 28 _ _ (243311 / 12500) (1946491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284182784 :
    ThetaLowerSegment 284182784 284248320 (355205804747 / 1250) (14211461451629 / 50000) := by
  exact
    packedTile32768 284182784 284248320 13 3318 16857 28 _ _ (1946511 / 100000) (973257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284248320 :
    ThetaLowerSegment 284248320 284281088 (14211461451629 / 50000) (710655459633 / 2500) := by
  exact
    packedTile32768 284248320 284281088 12 1693 16859 28 _ _ (973267 / 50000) (1946537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284281088 :
    ThetaLowerSegment 284281088 284313856 (710655459633 / 2500) (3553684126279 / 12500) := by
  exact
    packedTile32768 284281088 284313856 12 1672 16860 28 _ _ (973273 / 50000) (1946549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284313856 :
    ThetaLowerSegment 284313856 284346624 (3553684126279 / 12500) (28432725706979 / 100000) := by
  exact
    packedTile32768 284313856 284346624 12 1671 16861 28 _ _ (1946557 / 100000) (12166 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284346624 :
    ThetaLowerSegment 284346624 284379392 (28432725706979 / 100000) (14218032036407 / 50000) := by
  exact
    packedTile32768 284346624 284379392 12 1715 16862 28 _ _ (1946569 / 100000) (486643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284379392 :
    ThetaLowerSegment 284379392 284444928 (14218032036407 / 50000) (14221311050417 / 50000) := by
  exact
    packedTile32768 284379392 284444928 13 3369 16863 28 _ _ (97329 / 5000) (1946583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284444928 :
    ThetaLowerSegment 284444928 284510464 (14221311050417 / 50000) (2844897581629 / 10000) := by
  exact
    packedTile32768 284444928 284510464 13 3264 16865 28 _ _ (486651 / 25000) (1946607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284510464 :
    ThetaLowerSegment 284510464 284543232 (2844897581629 / 10000) (7113064457353 / 25000) := by
  exact
    packedTile32768 284510464 284543232 12 1686 16867 28 _ _ (1946627 / 100000) (194663 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284543232 :
    ThetaLowerSegment 284543232 284576000 (7113064457353 / 25000) (7113883991951 / 25000) := by
  exact
    packedTile32768 284543232 284576000 12 1684 16868 28 _ _ (973319 / 50000) (1946641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284576000 :
    ThetaLowerSegment 284576000 284608768 (7113883991951 / 25000) (14229423609727 / 50000) := by
  exact
    packedTile32768 284576000 284608768 12 1701 16869 28 _ _ (38933 / 2000) (1946653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284608768 :
    ThetaLowerSegment 284608768 284641536 (14229423609727 / 50000) (28462068943409 / 100000) := by
  exact
    packedTile32768 284608768 284641536 12 1655 16870 28 _ _ (1946661 / 100000) (243333 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284641536 :
    ThetaLowerSegment 284641536 284674304 (28462068943409 / 100000) (28465405540931 / 100000) := by
  exact
    packedTile32768 284641536 284674304 12 1714 16871 28 _ _ (1946673 / 100000) (486669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284674304 :
    ThetaLowerSegment 284674304 284707072 (28465405540931 / 100000) (28468675970051 / 100000) := by
  exact
    packedTile32768 284674304 284707072 12 1680 16872 28 _ _ (486671 / 25000) (1946687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284707072 :
    ThetaLowerSegment 284707072 284739840 (28468675970051 / 100000) (28471932792459 / 100000) := by
  exact
    packedTile32768 284707072 284739840 12 1673 16873 28 _ _ (243337 / 12500) (1946699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284739840 :
    ThetaLowerSegment 284739840 284772608 (28471932792459 / 100000) (28475246087773 / 100000) := by
  exact
    packedTile32768 284739840 284772608 12 1702 16874 28 _ _ (1946707 / 100000) (194671 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284772608 :
    ThetaLowerSegment 284772608 284805376 (28475246087773 / 100000) (14239245634173 / 50000) := by
  exact
    packedTile32768 284772608 284805376 12 1667 16875 28 _ _ (1946719 / 100000) (973361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284805376 :
    ThetaLowerSegment 284805376 284838144 (14239245634173 / 50000) (14240917875243 / 50000) := by
  exact
    packedTile32768 284805376 284838144 12 1718 16876 28 _ _ (194673 / 10000) (1946733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284838144 :
    ThetaLowerSegment 284838144 284870912 (14240917875243 / 50000) (1424255021841 / 5000) := by
  exact
    packedTile32768 284838144 284870912 12 1677 16877 28 _ _ (973371 / 50000) (389349 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284870912 :
    ThetaLowerSegment 284870912 284903680 (1424255021841 / 5000) (3561043452603 / 12500) := by
  exact
    packedTile32768 284870912 284903680 12 1668 16878 28 _ _ (1946753 / 100000) (486689 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284903680 :
    ThetaLowerSegment 284903680 284936448 (3561043452603 / 12500) (3561448379723 / 12500) := by
  exact
    packedTile32768 284903680 284936448 12 1664 16879 28 _ _ (389353 / 20000) (121673 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284936448 :
    ThetaLowerSegment 284936448 284969216 (3561448379723 / 12500) (178092507281 / 625) := by
  exact
    packedTile32768 284936448 284969216 12 1651 16880 28 _ _ (243347 / 12500) (1946779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell284969216 :
    ThetaLowerSegment 284969216 285001984 (178092507281 / 625) (7124517455503 / 25000) := by
  exact
    packedTile32768 284969216 285001984 12 1679 16881 28 _ _ (486697 / 25000) (1946791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285001984 :
    ThetaLowerSegment 285001984 285034752 (7124517455503 / 25000) (28501319029543 / 100000) := by
  exact
    packedTile32768 285001984 285034752 12 1669 16882 28 _ _ (1946799 / 100000) (973401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285034752 :
    ThetaLowerSegment 285034752 285067520 (28501319029543 / 100000) (2850458383159 / 10000) := by
  exact
    packedTile32768 285034752 285067520 12 1677 16882 28 _ _ (1946811 / 100000) (973407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285067520 :
    ThetaLowerSegment 285067520 285100288 (2850458383159 / 10000) (1781735917053 / 6250) := by
  exact
    packedTile32768 285067520 285100288 12 1639 16883 28 _ _ (973411 / 50000) (77873 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285100288 :
    ThetaLowerSegment 285100288 285133056 (1781735917053 / 6250) (2851105119447 / 10000) := by
  exact
    packedTile32768 285100288 285133056 12 1683 16884 28 _ _ (973417 / 50000) (1946837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285133056 :
    ThetaLowerSegment 285133056 285165824 (2851105119447 / 10000) (712856976587 / 2500) := by
  exact
    packedTile32768 285133056 285165824 12 1658 16885 28 _ _ (389369 / 20000) (60839 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285165824 :
    ThetaLowerSegment 285165824 285198592 (712856976587 / 2500) (14258761263621 / 50000) := by
  exact
    packedTile32768 285165824 285198592 12 1666 16886 28 _ _ (1946857 / 100000) (97343 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285198592 :
    ThetaLowerSegment 285198592 285231360 (14258761263621 / 50000) (14260381057797 / 50000) := by
  exact
    packedTile32768 285198592 285231360 12 1664 16887 28 _ _ (486717 / 25000) (1946871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285231360 :
    ThetaLowerSegment 285231360 285264128 (14260381057797 / 50000) (14262013516677 / 50000) := by
  exact
    packedTile32768 285231360 285264128 12 1677 16888 28 _ _ (12168 / 625) (1946883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285264128 :
    ThetaLowerSegment 285264128 285296896 (14262013516677 / 50000) (14263621648643 / 50000) := by
  exact
    packedTile32768 285264128 285296896 12 1652 16889 28 _ _ (1946891 / 100000) (973447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285296896 :
    ThetaLowerSegment 285296896 285329664 (14263621648643 / 50000) (14265315454253 / 50000) := by
  exact
    packedTile32768 285296896 285329664 12 1740 16890 28 _ _ (1946903 / 100000) (973453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285329664 :
    ThetaLowerSegment 285329664 285362432 (14265315454253 / 50000) (7133481758477 / 25000) := by
  exact
    packedTile32768 285329664 285362432 12 1693 16891 28 _ _ (973457 / 50000) (1946917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285362432 :
    ThetaLowerSegment 285362432 285395200 (7133481758477 / 25000) (178357997753 / 625) := by
  exact
    packedTile32768 285362432 285395200 12 1722 16892 28 _ _ (973463 / 50000) (1946929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285395200 :
    ThetaLowerSegment 285395200 285427968 (178357997753 / 625) (5708104258117 / 20000) := by
  exact
    packedTile32768 285395200 285427968 12 1665 16893 28 _ _ (1946937 / 100000) (97347 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285427968 :
    ThetaLowerSegment 285427968 285460736 (5708104258117 / 20000) (5708746751287 / 20000) := by
  exact
    packedTile32768 285427968 285460736 12 1650 16894 28 _ _ (1946949 / 100000) (243369 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285460736 :
    ThetaLowerSegment 285460736 285493504 (5708746751287 / 20000) (5709403266199 / 20000) := by
  exact
    packedTile32768 285460736 285493504 12 1686 16895 28 _ _ (24337 / 1250) (1946963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285493504 :
    ThetaLowerSegment 285493504 285526272 (5709403266199 / 20000) (713757911171 / 2500) := by
  exact
    packedTile32768 285493504 285526272 12 1695 16896 28 _ _ (1946971 / 100000) (973487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285526272 :
    ThetaLowerSegment 285526272 285559040 (713757911171 / 2500) (28553550385603 / 100000) := by
  exact
    packedTile32768 285526272 285559040 12 1661 16897 28 _ _ (1946983 / 100000) (973493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285559040 :
    ThetaLowerSegment 285559040 285591808 (28553550385603 / 100000) (5711375170271 / 20000) := by
  exact
    packedTile32768 285559040 285591808 12 1708 16898 28 _ _ (973497 / 50000) (1946997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285591808 :
    ThetaLowerSegment 285591808 285624576 (5711375170271 / 20000) (28560129298381 / 100000) := by
  exact
    packedTile32768 285591808 285624576 12 1671 16899 28 _ _ (973503 / 50000) (1947009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285624576 :
    ThetaLowerSegment 285624576 285657344 (28560129298381 / 100000) (28563454803417 / 100000) := by
  exact
    packedTile32768 285624576 285657344 12 1708 16900 28 _ _ (1947017 / 100000) (97351 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285657344 :
    ThetaLowerSegment 285657344 285690112 (28563454803417 / 100000) (28566640142861 / 100000) := by
  exact
    packedTile32768 285657344 285690112 12 1636 16901 28 _ _ (1947029 / 100000) (243379 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285690112 :
    ThetaLowerSegment 285690112 285722880 (28566640142861 / 100000) (28570027992461 / 100000) := by
  exact
    packedTile32768 285690112 285722880 12 1740 16902 28 _ _ (12169 / 625) (1947043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285722880 :
    ThetaLowerSegment 285722880 285755648 (28570027992461 / 100000) (28573297092769 / 100000) := by
  exact
    packedTile32768 285722880 285755648 12 1679 16903 28 _ _ (486763 / 25000) (389411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285755648 :
    ThetaLowerSegment 285755648 285788416 (28573297092769 / 100000) (28576529217349 / 100000) := by
  exact
    packedTile32768 285755648 285788416 12 1660 16904 28 _ _ (1947063 / 100000) (973533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285788416 :
    ThetaLowerSegment 285788416 285821184 (28576529217349 / 100000) (893118333557 / 3125) := by
  exact
    packedTile32768 285788416 285821184 12 1673 16905 28 _ _ (77883 / 4000) (973539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285821184 :
    ThetaLowerSegment 285821184 285853952 (893118333557 / 3125) (3572883195831 / 12500) := by
  exact
    packedTile32768 285821184 285853952 12 1684 16906 28 _ _ (973543 / 50000) (1947089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285853952 :
    ThetaLowerSegment 285853952 285886720 (3572883195831 / 12500) (7146585146371 / 25000) := by
  exact
    packedTile32768 285853952 285886720 12 1682 16907 28 _ _ (973549 / 50000) (1947101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285886720 :
    ThetaLowerSegment 285886720 285919488 (7146585146371 / 25000) (28589644829457 / 100000) := by
  exact
    packedTile32768 285886720 285919488 12 1697 16908 28 _ _ (1947109 / 100000) (243389 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285919488 :
    ThetaLowerSegment 285919488 285952256 (28589644829457 / 100000) (7148222670041 / 25000) := by
  exact
    packedTile32768 285919488 285952256 12 1667 16909 28 _ _ (1947121 / 100000) (486781 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285952256 :
    ThetaLowerSegment 285952256 285985024 (7148222670041 / 25000) (1787265592679 / 6250) := by
  exact
    packedTile32768 285952256 285985024 12 1725 16910 28 _ _ (486783 / 25000) (389427 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell285985024 :
    ThetaLowerSegment 285985024 286017792 (1787265592679 / 6250) (3574944223279 / 12500) := by
  exact
    packedTile32768 285985024 286017792 12 1697 16911 28 _ _ (243393 / 12500) (1947147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286017792 :
    ThetaLowerSegment 286017792 286050560 (3574944223279 / 12500) (28602858108267 / 100000) := by
  exact
    packedTile32768 286017792 286050560 12 1697 16912 28 _ _ (389431 / 20000) (973579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286050560 :
    ThetaLowerSegment 286050560 286083328 (28602858108267 / 100000) (5721230932061 / 20000) := by
  exact
    packedTile32768 286050560 286083328 12 1693 16913 28 _ _ (973583 / 50000) (1947169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286083328 :
    ThetaLowerSegment 286083328 286116096 (5721230932061 / 20000) (28609423972167 / 100000) := by
  exact
    packedTile32768 286083328 286116096 12 1679 16913 28 _ _ (973589 / 50000) (1947181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286116096 :
    ThetaLowerSegment 286116096 286148864 (28609423972167 / 100000) (1144503292509 / 4000) := by
  exact
    packedTile32768 286116096 286148864 12 1622 16914 28 _ _ (1947189 / 100000) (243399 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286148864 :
    ThetaLowerSegment 286148864 286181632 (1144503292509 / 4000) (28615830243993 / 100000) := by
  exact
    packedTile32768 286148864 286181632 12 1668 16915 28 _ _ (1947201 / 100000) (486801 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286181632 :
    ThetaLowerSegment 286181632 286214400 (28615830243993 / 100000) (28619136609969 / 100000) := by
  exact
    packedTile32768 286181632 286214400 12 1698 16916 28 _ _ (486803 / 25000) (389443 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286214400 :
    ThetaLowerSegment 286214400 286247168 (28619136609969 / 100000) (28622353424017 / 100000) := by
  exact
    packedTile32768 286214400 286247168 12 1652 16917 28 _ _ (243403 / 12500) (1947227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286247168 :
    ThetaLowerSegment 286247168 286279936 (28622353424017 / 100000) (7156414470453 / 25000) := by
  exact
    packedTile32768 286247168 286279936 12 1697 16918 28 _ _ (389447 / 20000) (973619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286279936 :
    ThetaLowerSegment 286279936 286312704 (7156414470453 / 25000) (1789306618113 / 6250) := by
  exact
    packedTile32768 286279936 286312704 12 1668 16919 28 _ _ (1947247 / 100000) (7789 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286312704 :
    ThetaLowerSegment 286312704 286345472 (1789306618113 / 6250) (14316099351543 / 50000) := by
  exact
    packedTile32768 286312704 286345472 12 1691 16920 28 _ _ (973629 / 50000) (1947261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286345472 :
    ThetaLowerSegment 286345472 286378240 (14316099351543 / 50000) (14317715584813 / 50000) := by
  exact
    packedTile32768 286345472 286378240 12 1660 16921 28 _ _ (1947269 / 100000) (243409 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286378240 :
    ThetaLowerSegment 286378240 286411008 (14317715584813 / 50000) (5727744025447 / 20000) := by
  exact
    packedTile32768 286378240 286411008 12 1689 16922 28 _ _ (1947281 / 100000) (486821 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286411008 :
    ThetaLowerSegment 286411008 286443776 (5727744025447 / 20000) (5728386631807 / 20000) := by
  exact
    packedTile32768 286411008 286443776 12 1650 16923 28 _ _ (486823 / 25000) (389459 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286443776 :
    ThetaLowerSegment 286443776 286476544 (5728386631807 / 20000) (28645220208187 / 100000) := by
  exact
    packedTile32768 286443776 286476544 12 1688 16924 28 _ _ (243413 / 12500) (1947307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286476544 :
    ThetaLowerSegment 286476544 286509312 (28645220208187 / 100000) (28648546222207 / 100000) := by
  exact
    packedTile32768 286476544 286509312 12 1708 16925 28 _ _ (389463 / 20000) (973659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286509312 :
    ThetaLowerSegment 286509312 286542080 (28648546222207 / 100000) (14325913734101 / 50000) := by
  exact
    packedTile32768 286509312 286542080 12 1685 16926 28 _ _ (1947327 / 100000) (194733 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286542080 :
    ThetaLowerSegment 286542080 286574848 (14325913734101 / 50000) (2865514962683 / 10000) := by
  exact
    packedTile32768 286542080 286574848 12 1706 16927 28 _ _ (973669 / 50000) (1947341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286574848 :
    ThetaLowerSegment 286574848 286607616 (2865514962683 / 10000) (2865838612253 / 10000) := by
  exact
    packedTile32768 286574848 286607616 12 1662 16928 28 _ _ (38947 / 2000) (1947353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286607616 :
    ThetaLowerSegment 286607616 286640384 (2865838612253 / 10000) (28661644057483 / 100000) := by
  exact
    packedTile32768 286607616 286640384 12 1673 16929 28 _ _ (1947361 / 100000) (486841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286640384 :
    ThetaLowerSegment 286640384 286673152 (28661644057483 / 100000) (1146597093067 / 4000) := by
  exact
    packedTile32768 286640384 286673152 12 1686 16930 28 _ _ (486843 / 25000) (15579 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286673152 :
    ThetaLowerSegment 286673152 286705920 (1146597093067 / 4000) (5733633944207 / 20000) := by
  exact
    packedTile32768 286673152 286705920 12 1665 16931 28 _ _ (243423 / 12500) (1947387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286705920 :
    ThetaLowerSegment 286705920 286738688 (5733633944207 / 20000) (5734280479347 / 20000) := by
  exact
    packedTile32768 286705920 286738688 12 1660 16932 28 _ _ (389479 / 20000) (973699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286738688 :
    ThetaLowerSegment 286738688 286771456 (5734280479347 / 20000) (716865633883 / 2500) := by
  exact
    packedTile32768 286738688 286771456 12 1655 16933 28 _ _ (1947407 / 100000) (194741 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286771456 :
    ThetaLowerSegment 286771456 286804224 (716865633883 / 2500) (286779554401 / 1000) := by
  exact
    packedTile32768 286771456 286804224 12 1710 16934 28 _ _ (973709 / 50000) (1947421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286804224 :
    ThetaLowerSegment 286804224 286836992 (286779554401 / 1000) (717031749149 / 2500) := by
  exact
    packedTile32768 286804224 286836992 12 1702 16935 28 _ _ (194743 / 10000) (1947433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286836992 :
    ThetaLowerSegment 286836992 286869760 (717031749149 / 2500) (14342249411569 / 50000) := by
  exact
    packedTile32768 286836992 286869760 12 1658 16936 28 _ _ (1947441 / 100000) (486861 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286869760 :
    ThetaLowerSegment 286869760 286902528 (14342249411569 / 50000) (14343924220289 / 50000) := by
  exact
    packedTile32768 286869760 286902528 12 1720 16937 28 _ _ (486863 / 25000) (389491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286902528 :
    ThetaLowerSegment 286902528 286935296 (14343924220289 / 50000) (14345527956893 / 50000) := by
  exact
    packedTile32768 286902528 286935296 12 1647 16938 28 _ _ (243433 / 12500) (1947467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286935296 :
    ThetaLowerSegment 286935296 286968064 (14345527956893 / 50000) (14347140466193 / 50000) := by
  exact
    packedTile32768 286935296 286968064 12 1656 16939 28 _ _ (77899 / 4000) (973739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell286968064 :
    ThetaLowerSegment 286968064 287000832 (14347140466193 / 50000) (1434879777763 / 5000) := by
  exact
    packedTile32768 286968064 287000832 12 1702 16940 28 _ _ (1947487 / 100000) (194749 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287000832 :
    ThetaLowerSegment 287000832 287033600 (1434879777763 / 5000) (14350465809667 / 50000) := by
  exact
    packedTile32768 287000832 287033600 12 1713 16941 28 _ _ (973749 / 50000) (1947501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287033600 :
    ThetaLowerSegment 287033600 287066368 (14350465809667 / 50000) (28704252122179 / 100000) := by
  exact
    packedTile32768 287033600 287066368 12 1705 16942 28 _ _ (1947509 / 100000) (243439 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287066368 :
    ThetaLowerSegment 287066368 287099136 (28704252122179 / 100000) (28707590173173 / 100000) := by
  exact
    packedTile32768 287066368 287099136 12 1714 16943 28 _ _ (1947521 / 100000) (486881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287099136 :
    ThetaLowerSegment 287099136 287131904 (28707590173173 / 100000) (5742176689957 / 20000) := by
  exact
    packedTile32768 287099136 287131904 12 1691 16944 28 _ _ (486883 / 25000) (389507 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287131904 :
    ThetaLowerSegment 287131904 287164672 (5742176689957 / 20000) (5742850540181 / 20000) := by
  exact
    packedTile32768 287131904 287164672 12 1730 16944 28 _ _ (243443 / 12500) (1947547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287164672 :
    ThetaLowerSegment 287164672 287197440 (5742850540181 / 20000) (7179356317 / 25) := by
  exact
    packedTile32768 287164672 287197440 12 1629 16945 28 _ _ (389511 / 20000) (973779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287197440 :
    ThetaLowerSegment 287197440 287230208 (7179356317 / 25) (3590085200003 / 12500) := by
  exact
    packedTile32768 287197440 287230208 12 1672 16946 28 _ _ (1947567 / 100000) (194757 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287230208 :
    ThetaLowerSegment 287230208 287262976 (3590085200003 / 12500) (897625738871 / 3125) := by
  exact
    packedTile32768 287230208 287262976 12 1716 16947 28 _ _ (973789 / 50000) (1947581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287262976 :
    ThetaLowerSegment 287262976 287295744 (897625738871 / 3125) (897728961088 / 3125) := by
  exact
    packedTile32768 287262976 287295744 12 1696 16948 28 _ _ (1947589 / 100000) (243449 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287295744 :
    ThetaLowerSegment 287295744 287328512 (897728961088 / 3125) (28730651309723 / 100000) := by
  exact
    packedTile32768 287295744 287328512 12 1707 16949 28 _ _ (1947601 / 100000) (486901 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287328512 :
    ThetaLowerSegment 287328512 287361280 (28730651309723 / 100000) (28733933035943 / 100000) := by
  exact
    packedTile32768 287328512 287361280 12 1685 16950 28 _ _ (486903 / 25000) (389523 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287361280 :
    ThetaLowerSegment 287361280 287394048 (28733933035943 / 100000) (1149487266911 / 4000) := by
  exact
    packedTile32768 287361280 287394048 12 1668 16951 28 _ _ (243453 / 12500) (1947627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287394048 :
    ThetaLowerSegment 287394048 287426816 (1149487266911 / 4000) (2874045564721 / 10000) := by
  exact
    packedTile32768 287394048 287426816 12 1681 16952 28 _ _ (389527 / 20000) (973819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287426816 :
    ThetaLowerSegment 287426816 287459584 (2874045564721 / 10000) (7185913907397 / 25000) := by
  exact
    packedTile32768 287426816 287459584 12 1643 16953 28 _ _ (973823 / 50000) (1947649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287459584 :
    ThetaLowerSegment 287459584 287492352 (7185913907397 / 25000) (7186755295653 / 25000) := by
  exact
    packedTile32768 287459584 287492352 12 1728 16954 28 _ _ (973829 / 50000) (1947661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287492352 :
    ThetaLowerSegment 287492352 287525120 (7186755295653 / 25000) (1150011496941 / 4000) := by
  exact
    packedTile32768 287492352 287525120 12 1677 16955 28 _ _ (1947669 / 100000) (243459 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287525120 :
    ThetaLowerSegment 287525120 287557888 (1150011496941 / 4000) (7188393290343 / 25000) := by
  exact
    packedTile32768 287525120 287557888 12 1687 16956 28 _ _ (1947681 / 100000) (486921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287557888 :
    ThetaLowerSegment 287557888 287590656 (7188393290343 / 25000) (3594604930107 / 12500) := by
  exact
    packedTile32768 287557888 287590656 12 1677 16957 28 _ _ (486923 / 25000) (389539 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287590656 :
    ThetaLowerSegment 287590656 287623424 (3594604930107 / 12500) (28760027830667 / 100000) := by
  exact
    packedTile32768 287590656 287623424 12 1637 16958 28 _ _ (1947703 / 100000) (973853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287623424 :
    ThetaLowerSegment 287623424 287656192 (28760027830667 / 100000) (14381650969791 / 50000) := by
  exact
    packedTile32768 287623424 287656192 12 1681 16959 28 _ _ (389543 / 20000) (973859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287656192 :
    ThetaLowerSegment 287656192 287688960 (14381650969791 / 50000) (14383277321001 / 50000) := by
  exact
    packedTile32768 287656192 287688960 12 1670 16960 28 _ _ (973863 / 50000) (1947729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287688960 :
    ThetaLowerSegment 287688960 287721728 (14383277321001 / 50000) (359623103337 / 1250) := by
  exact
    packedTile32768 287688960 287721728 12 1691 16961 28 _ _ (973869 / 50000) (1947741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287721728 :
    ThetaLowerSegment 287721728 287754496 (359623103337 / 1250) (28773122433029 / 100000) := by
  exact
    packedTile32768 287721728 287754496 12 1681 16962 28 _ _ (1947749 / 100000) (243469 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287754496 :
    ThetaLowerSegment 287754496 287787264 (28773122433029 / 100000) (28776419990709 / 100000) := by
  exact
    packedTile32768 287754496 287787264 12 1693 16963 28 _ _ (24347 / 1250) (1947763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287787264 :
    ThetaLowerSegment 287787264 287820032 (28776419990709 / 100000) (28779641605597 / 100000) := by
  exact
    packedTile32768 287787264 287820032 12 1654 16964 28 _ _ (486943 / 25000) (77911 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287820032 :
    ThetaLowerSegment 287820032 287852800 (28779641605597 / 100000) (14391518295683 / 50000) := by
  exact
    packedTile32768 287820032 287852800 12 1743 16965 28 _ _ (1947783 / 100000) (973893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287852800 :
    ThetaLowerSegment 287852800 287885568 (14391518295683 / 50000) (1799140044531 / 6250) := by
  exact
    packedTile32768 287852800 287885568 12 1645 16966 28 _ _ (973897 / 50000) (1947797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287885568 :
    ThetaLowerSegment 287885568 287918336 (1799140044531 / 6250) (14394767226221 / 50000) := by
  exact
    packedTile32768 287885568 287918336 12 1691 16967 28 _ _ (973903 / 50000) (1947809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287918336 :
    ThetaLowerSegment 287918336 287951104 (14394767226221 / 50000) (28792820419721 / 100000) := by
  exact
    packedTile32768 287918336 287951104 12 1687 16968 28 _ _ (1947817 / 100000) (97391 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287951104 :
    ThetaLowerSegment 287951104 287983872 (28792820419721 / 100000) (28795995380991 / 100000) := by
  exact
    packedTile32768 287951104 287983872 12 1630 16969 28 _ _ (1947829 / 100000) (243479 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell287983872 :
    ThetaLowerSegment 287983872 288016640 (28795995380991 / 100000) (28799374883391 / 100000) := by
  exact
    packedTile32768 287983872 288016640 12 1735 16970 28 _ _ (12174 / 625) (1947843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288016640 :
    ThetaLowerSegment 288016640 288049408 (28799374883391 / 100000) (5760534908597 / 20000) := by
  exact
    packedTile32768 288016640 288049408 12 1694 16971 28 _ _ (1947851 / 100000) (973927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288049408 :
    ThetaLowerSegment 288049408 288082176 (5760534908597 / 20000) (900186877078 / 3125) := by
  exact
    packedTile32768 288049408 288082176 12 1697 16972 28 _ _ (1947863 / 100000) (973933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288082176 :
    ThetaLowerSegment 288082176 288114944 (900186877078 / 3125) (14404633064967 / 50000) := by
  exact
    packedTile32768 288082176 288114944 12 1687 16972 28 _ _ (973937 / 50000) (1947877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288114944 :
    ThetaLowerSegment 288114944 288147712 (14404633064967 / 50000) (14406243966689 / 50000) := by
  exact
    packedTile32768 288114944 288147712 12 1654 16973 28 _ _ (973943 / 50000) (1947889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288147712 :
    ThetaLowerSegment 288147712 288180480 (14406243966689 / 50000) (7203917699269 / 25000) := by
  exact
    packedTile32768 288147712 288180480 12 1634 16974 28 _ _ (1947897 / 100000) (19479 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288180480 :
    ThetaLowerSegment 288180480 288213248 (7203917699269 / 25000) (7204748482031 / 25000) := by
  exact
    packedTile32768 288180480 288213248 12 1706 16975 28 _ _ (486977 / 25000) (1947911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288213248 :
    ThetaLowerSegment 288213248 288246016 (7204748482031 / 25000) (7205561738631 / 25000) := by
  exact
    packedTile32768 288213248 288246016 12 1670 16976 28 _ _ (24349 / 1250) (1947923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288246016 :
    ThetaLowerSegment 288246016 288278784 (7205561738631 / 25000) (28825447405157 / 100000) := by
  exact
    packedTile32768 288246016 288278784 12 1643 16977 28 _ _ (1947931 / 100000) (973967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288278784 :
    ThetaLowerSegment 288278784 288311552 (28825447405157 / 100000) (28828733583311 / 100000) := by
  exact
    packedTile32768 288278784 288311552 12 1687 16978 28 _ _ (973971 / 50000) (389589 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288311552 :
    ThetaLowerSegment 288311552 288344320 (28828733583311 / 100000) (28831973030813 / 100000) := by
  exact
    packedTile32768 288311552 288344320 12 1663 16979 28 _ _ (973977 / 50000) (1947957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288344320 :
    ThetaLowerSegment 288344320 288377088 (28831973030813 / 100000) (1802206624933 / 6250) := by
  exact
    packedTile32768 288344320 288377088 12 1711 16980 28 _ _ (389593 / 20000) (60874 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288377088 :
    ThetaLowerSegment 288377088 288409856 (1802206624933 / 6250) (180241140591 / 625) := by
  exact
    packedTile32768 288377088 288409856 12 1682 16981 28 _ _ (243497 / 12500) (1947979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288409856 :
    ThetaLowerSegment 288409856 288442624 (180241140591 / 625) (7210479849501 / 25000) := by
  exact
    packedTile32768 288409856 288442624 12 1713 16982 28 _ _ (486997 / 25000) (1947991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288442624 :
    ThetaLowerSegment 288442624 288475392 (7210479849501 / 25000) (28845178400331 / 100000) := by
  exact
    packedTile32768 288442624 288475392 12 1673 16983 28 _ _ (1947999 / 100000) (974001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288475392 :
    ThetaLowerSegment 288475392 288508160 (28845178400331 / 100000) (28848513395163 / 100000) := by
  exact
    packedTile32768 288475392 288508160 12 1712 16984 28 _ _ (1948011 / 100000) (974007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288508160 :
    ThetaLowerSegment 288508160 288540928 (28848513395163 / 100000) (28851848408827 / 100000) := by
  exact
    packedTile32768 288508160 288540928 12 1712 16985 28 _ _ (974011 / 50000) (77921 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288540928 :
    ThetaLowerSegment 288540928 288573696 (28851848408827 / 100000) (28855097727871 / 100000) := by
  exact
    packedTile32768 288540928 288573696 12 1668 16986 28 _ _ (1948033 / 100000) (487009 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288573696 :
    ThetaLowerSegment 288573696 288606464 (28855097727871 / 100000) (14429176455533 / 50000) := by
  exact
    packedTile32768 288573696 288606464 12 1671 16987 28 _ _ (389609 / 20000) (121753 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288606464 :
    ThetaLowerSegment 288606464 288639232 (14429176455533 / 50000) (14430857627861 / 50000) := by
  exact
    packedTile32768 288606464 288639232 12 1726 16988 28 _ _ (243507 / 12500) (1948059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288639232 :
    ThetaLowerSegment 288639232 288672000 (14430857627861 / 50000) (14432532965481 / 50000) := by
  exact
    packedTile32768 288639232 288672000 12 1720 16989 28 _ _ (1948067 / 100000) (194807 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288672000 :
    ThetaLowerSegment 288672000 288704768 (14432532965481 / 50000) (28868301690181 / 100000) := by
  exact
    packedTile32768 288672000 288704768 12 1661 16990 28 _ _ (1948079 / 100000) (974041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288704768 :
    ThetaLowerSegment 288704768 288737536 (28868301690181 / 100000) (28871553052391 / 100000) := by
  exact
    packedTile32768 288704768 288737536 12 1669 16991 28 _ _ (194809 / 10000) (1948093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288737536 :
    ThetaLowerSegment 288737536 288770304 (28871553052391 / 100000) (28874837550677 / 100000) := by
  exact
    packedTile32768 288737536 288770304 12 1686 16992 28 _ _ (1948101 / 100000) (243513 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288770304 :
    ThetaLowerSegment 288770304 288803072 (28874837550677 / 100000) (28878087003161 / 100000) := by
  exact
    packedTile32768 288770304 288803072 12 1668 16993 28 _ _ (1948113 / 100000) (487029 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288803072 :
    ThetaLowerSegment 288803072 288835840 (28878087003161 / 100000) (28881359851481 / 100000) := by
  exact
    packedTile32768 288803072 288835840 12 1680 16994 28 _ _ (487031 / 25000) (1948127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288835840 :
    ThetaLowerSegment 288835840 288868608 (28881359851481 / 100000) (28884702851141 / 100000) := by
  exact
    packedTile32768 288835840 288868608 12 1716 16995 28 _ _ (389627 / 20000) (974069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288868608 :
    ThetaLowerSegment 288868608 288901376 (28884702851141 / 100000) (7221984680827 / 25000) := by
  exact
    packedTile32768 288868608 288901376 12 1661 16996 28 _ _ (1948147 / 100000) (38963 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288901376 :
    ThetaLowerSegment 288901376 288934144 (7221984680827 / 25000) (288912973477 / 1000) := by
  exact
    packedTile32768 288901376 288934144 12 1724 16997 28 _ _ (974079 / 50000) (1948161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288934144 :
    ThetaLowerSegment 288934144 288966912 (288912973477 / 1000) (1444724617243 / 5000) := by
  exact
    packedTile32768 288934144 288966912 12 1640 16998 28 _ _ (1948169 / 100000) (487043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288966912 :
    ThetaLowerSegment 288966912 288999680 (1444724617243 / 5000) (3612219687027 / 12500) := by
  exact
    packedTile32768 288966912 288999680 12 1676 16999 28 _ _ (1948181 / 100000) (243523 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell288999680 :
    ThetaLowerSegment 288999680 289032448 (3612219687027 / 12500) (722527320023 / 2500) := by
  exact
    packedTile32768 288999680 289032448 12 1712 16999 28 _ _ (60881 / 3125) (389639 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289032448 :
    ThetaLowerSegment 289032448 289065216 (722527320023 / 2500) (3613053515557 / 12500) := by
  exact
    packedTile32768 289032448 289065216 12 1712 17000 28 _ _ (1948203 / 100000) (974103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289065216 :
    ThetaLowerSegment 289065216 289097984 (3613053515557 / 12500) (7226903851049 / 25000) := by
  exact
    packedTile32768 289065216 289097984 12 1636 17001 28 _ _ (389643 / 20000) (974109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289097984 :
    ThetaLowerSegment 289097984 289130752 (7226903851049 / 25000) (14455412066209 / 50000) := by
  exact
    packedTile32768 289097984 289130752 12 1647 17002 28 _ _ (974113 / 50000) (1948229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289130752 :
    ThetaLowerSegment 289130752 289163520 (14455412066209 / 50000) (28914048464653 / 100000) := by
  exact
    packedTile32768 289130752 289163520 12 1655 17003 28 _ _ (1948237 / 100000) (24353 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289163520 :
    ThetaLowerSegment 289163520 289196288 (28914048464653 / 100000) (5783459628797 / 20000) := by
  exact
    packedTile32768 289163520 289196288 12 1668 17004 28 _ _ (1948249 / 100000) (487063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289196288 :
    ThetaLowerSegment 289196288 289229056 (5783459628797 / 20000) (5784122037197 / 20000) := by
  exact
    packedTile32768 289196288 289229056 12 1700 17005 28 _ _ (97413 / 5000) (1948263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289229056 :
    ThetaLowerSegment 289229056 289261824 (5784122037197 / 20000) (7230981048739 / 25000) := by
  exact
    packedTile32768 289229056 289261824 12 1701 17006 28 _ _ (1948271 / 100000) (974137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289261824 :
    ThetaLowerSegment 289261824 289294592 (7230981048739 / 25000) (28927097947963 / 100000) := by
  exact
    packedTile32768 289261824 289294592 12 1629 17007 28 _ _ (1948283 / 100000) (974143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289294592 :
    ThetaLowerSegment 289294592 289327360 (28927097947963 / 100000) (28930447065349 / 100000) := by
  exact
    packedTile32768 289294592 289327360 12 1719 17008 28 _ _ (974147 / 50000) (1948297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289327360 :
    ThetaLowerSegment 289327360 289360128 (28930447065349 / 100000) (28933728010969 / 100000) := by
  exact
    packedTile32768 289327360 289360128 12 1684 17009 28 _ _ (389661 / 20000) (487077 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289360128 :
    ThetaLowerSegment 289360128 289392896 (28933728010969 / 100000) (28936989493627 / 100000) := by
  exact
    packedTile32768 289360128 289392896 12 1674 17010 28 _ _ (1948317 / 100000) (12177 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289392896 :
    ThetaLowerSegment 289392896 289425664 (28936989493627 / 100000) (28940297754571 / 100000) := by
  exact
    packedTile32768 289392896 289425664 12 1698 17011 28 _ _ (243541 / 12500) (1948331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289425664 :
    ThetaLowerSegment 289425664 289458432 (28940297754571 / 100000) (28943617724227 / 100000) := by
  exact
    packedTile32768 289425664 289458432 12 1704 17012 28 _ _ (1948339 / 100000) (974171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289458432 :
    ThetaLowerSegment 289458432 289491200 (28943617724227 / 100000) (28946894850609 / 100000) := by
  exact
    packedTile32768 289458432 289491200 12 1682 17013 28 _ _ (1948351 / 100000) (974177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289491200 :
    ThetaLowerSegment 289491200 289523968 (28946894850609 / 100000) (28950109647909 / 100000) := by
  exact
    packedTile32768 289491200 289523968 12 1650 17014 28 _ _ (974181 / 50000) (389673 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289523968 :
    ThetaLowerSegment 289523968 289556736 (28950109647909 / 100000) (28953453055977 / 100000) := by
  exact
    packedTile32768 289523968 289556736 12 1716 17015 28 _ _ (1948373 / 100000) (243547 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289556736 :
    ThetaLowerSegment 289556736 289589504 (28953453055977 / 100000) (28956710755697 / 100000) := by
  exact
    packedTile32768 289556736 289589504 12 1672 17016 28 _ _ (389677 / 20000) (487097 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289589504 :
    ThetaLowerSegment 289589504 289622272 (28956710755697 / 100000) (5791999929629 / 20000) := by
  exact
    packedTile32768 289589504 289622272 12 1688 17017 28 _ _ (487099 / 25000) (1948399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289622272 :
    ThetaLowerSegment 289622272 289655040 (5791999929629 / 20000) (14481666686261 / 50000) := by
  exact
    packedTile32768 289622272 289655040 12 1711 17018 28 _ _ (1948407 / 100000) (194841 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289655040 :
    ThetaLowerSegment 289655040 289687808 (14481666686261 / 50000) (28966608664861 / 100000) := by
  exact
    packedTile32768 289655040 289687808 12 1681 17019 28 _ _ (1948419 / 100000) (974211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289687808 :
    ThetaLowerSegment 289687808 289720576 (28966608664861 / 100000) (28969989190911 / 100000) := by
  exact
    packedTile32768 289687808 289720576 12 1735 17020 28 _ _ (194843 / 10000) (1948433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289720576 :
    ThetaLowerSegment 289720576 289753344 (28969989190911 / 100000) (14486673177377 / 50000) := by
  exact
    packedTile32768 289720576 289753344 12 1723 17021 28 _ _ (1948441 / 100000) (487111 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289753344 :
    ThetaLowerSegment 289753344 289786112 (14486673177377 / 50000) (14488305980991 / 50000) := by
  exact
    packedTile32768 289753344 289786112 12 1676 17022 28 _ _ (1948453 / 100000) (243557 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289786112 :
    ThetaLowerSegment 289786112 289818880 (14488305980991 / 50000) (2897987953611 / 10000) := by
  exact
    packedTile32768 289786112 289818880 12 1677 17023 28 _ _ (121779 / 6250) (1948467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289818880 :
    ThetaLowerSegment 289818880 289851648 (2897987953611 / 10000) (5796635660857 / 20000) := by
  exact
    packedTile32768 289818880 289851648 12 1693 17024 28 _ _ (77939 / 4000) (974239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289851648 :
    ThetaLowerSegment 289851648 289884416 (5796635660857 / 20000) (28986447863793 / 100000) := by
  exact
    packedTile32768 289851648 289884416 12 1678 17025 28 _ _ (974243 / 50000) (1948489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289884416 :
    ThetaLowerSegment 289884416 289917184 (28986447863793 / 100000) (28989746670907 / 100000) := by
  exact
    packedTile32768 289884416 289917184 12 1693 17025 28 _ _ (974249 / 50000) (1948501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289917184 :
    ThetaLowerSegment 289917184 289949952 (28989746670907 / 100000) (14496513005777 / 50000) := by
  exact
    packedTile32768 289917184 289949952 12 1683 17026 28 _ _ (1948509 / 100000) (60891 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289949952 :
    ThetaLowerSegment 289949952 289982720 (14496513005777 / 50000) (14498139045717 / 50000) := by
  exact
    packedTile32768 289949952 289982720 12 1669 17027 28 _ _ (48713 / 2500) (1948523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell289982720 :
    ThetaLowerSegment 289982720 290015488 (14498139045717 / 50000) (14499784580991 / 50000) := by
  exact
    packedTile32768 289982720 290015488 12 1689 17028 28 _ _ (487133 / 25000) (389707 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290015488 :
    ThetaLowerSegment 290015488 290048256 (14499784580991 / 50000) (7250692167397 / 25000) := by
  exact
    packedTile32768 290015488 290048256 12 1642 17029 28 _ _ (1948543 / 100000) (974273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290048256 :
    ThetaLowerSegment 290048256 290081024 (7250692167397 / 25000) (14503006505999 / 50000) := by
  exact
    packedTile32768 290048256 290081024 12 1665 17030 28 _ _ (974277 / 50000) (1948557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290081024 :
    ThetaLowerSegment 290081024 290113792 (14503006505999 / 50000) (14504643301439 / 50000) := by
  exact
    packedTile32768 290081024 290113792 12 1680 17031 28 _ _ (974283 / 50000) (1948569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290113792 :
    ThetaLowerSegment 290113792 290146560 (14504643301439 / 50000) (7253100107231 / 25000) := by
  exact
    packedTile32768 290113792 290146560 12 1598 17032 28 _ _ (1948577 / 100000) (97429 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290146560 :
    ThetaLowerSegment 290146560 290179328 (7253100107231 / 25000) (362696096211 / 1250) := by
  exact
    packedTile32768 290146560 290179328 12 1687 17033 28 _ _ (487147 / 25000) (1948591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290179328 :
    ThetaLowerSegment 290179328 290212096 (362696096211 / 1250) (2901898082919 / 10000) := by
  exact
    packedTile32768 290179328 290212096 12 1690 17034 28 _ _ (1948599 / 100000) (974301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290212096 :
    ThetaLowerSegment 290212096 290244864 (2901898082919 / 10000) (29022174602619 / 100000) := by
  exact
    packedTile32768 290212096 290244864 12 1639 17035 28 _ _ (1948611 / 100000) (974307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290244864 :
    ThetaLowerSegment 290244864 290277632 (29022174602619 / 100000) (29025461927933 / 100000) := by
  exact
    packedTile32768 290244864 290277632 12 1687 17036 28 _ _ (974311 / 50000) (15589 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290277632 :
    ThetaLowerSegment 290277632 290310400 (29025461927933 / 100000) (2902871419641 / 10000) := by
  exact
    packedTile32768 290277632 290310400 12 1669 17037 28 _ _ (1948633 / 100000) (487159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290310400 :
    ThetaLowerSegment 290310400 290343168 (2902871419641 / 10000) (1161281621337 / 4000) := by
  exact
    packedTile32768 290310400 290343168 12 1707 17038 28 _ _ (389729 / 20000) (243581 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290343168 :
    ThetaLowerSegment 290343168 290375936 (1161281621337 / 4000) (29035325967441 / 100000) := by
  exact
    packedTile32768 290343168 290375936 12 1686 17039 28 _ _ (121791 / 6250) (1948659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290375936 :
    ThetaLowerSegment 290375936 290408704 (29035325967441 / 100000) (5807720725067 / 20000) := by
  exact
    packedTile32768 290375936 290408704 12 1682 17040 28 _ _ (1948667 / 100000) (194867 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290408704 :
    ThetaLowerSegment 290408704 290441472 (5807720725067 / 20000) (29041852071561 / 100000) := by
  exact
    packedTile32768 290408704 290441472 12 1667 17041 28 _ _ (974339 / 50000) (1948681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290441472 :
    ThetaLowerSegment 290441472 290474240 (29041852071561 / 100000) (29045153152421 / 100000) := by
  exact
    packedTile32768 290441472 290474240 12 1694 17042 28 _ _ (194869 / 10000) (1948693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290474240 :
    ThetaLowerSegment 290474240 290507008 (29045153152421 / 100000) (29048352919463 / 100000) := by
  exact
    packedTile32768 290474240 290507008 12 1642 17043 28 _ _ (1948701 / 100000) (60897 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290507008 :
    ThetaLowerSegment 290507008 290539776 (29048352919463 / 100000) (5810319894731 / 20000) := by
  exact
    packedTile32768 290507008 290539776 12 1666 17044 28 _ _ (243589 / 12500) (389743 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290539776 :
    ThetaLowerSegment 290539776 290572544 (5810319894731 / 20000) (29054888919767 / 100000) := by
  exact
    packedTile32768 290539776 290572544 12 1688 17045 28 _ _ (487181 / 25000) (1948727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290572544 :
    ThetaLowerSegment 290572544 290605312 (29054888919767 / 100000) (29058116024927 / 100000) := by
  exact
    packedTile32768 290572544 290605312 12 1656 17046 28 _ _ (389747 / 20000) (974369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290605312 :
    ThetaLowerSegment 290605312 290638080 (29058116024927 / 100000) (5812265511667 / 20000) := by
  exact
    packedTile32768 290605312 290638080 12 1648 17047 28 _ _ (974373 / 50000) (1948749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290638080 :
    ThetaLowerSegment 290638080 290670848 (5812265511667 / 20000) (29064519622301 / 100000) := by
  exact
    packedTile32768 290638080 290670848 12 1638 17048 28 _ _ (1948757 / 100000) (48719 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290670848 :
    ThetaLowerSegment 290670848 290703616 (29064519622301 / 100000) (29067809144373 / 100000) := by
  exact
    packedTile32768 290670848 290703616 12 1688 17049 28 _ _ (1948769 / 100000) (487193 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290703616 :
    ThetaLowerSegment 290703616 290736384 (29067809144373 / 100000) (29071176636213 / 100000) := by
  exact
    packedTile32768 290703616 290736384 12 1728 17050 28 _ _ (97439 / 5000) (1948783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290736384 :
    ThetaLowerSegment 290736384 290769152 (29071176636213 / 100000) (14537228225733 / 50000) := by
  exact
    packedTile32768 290736384 290769152 12 1683 17050 28 _ _ (1948791 / 100000) (974397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290769152 :
    ThetaLowerSegment 290769152 290801920 (14537228225733 / 50000) (29077705106067 / 100000) := by
  exact
    packedTile32768 290769152 290801920 12 1667 17051 28 _ _ (1948803 / 100000) (974403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290801920 :
    ThetaLowerSegment 290801920 290834688 (29077705106067 / 100000) (29081027833937 / 100000) := by
  exact
    packedTile32768 290801920 290834688 12 1705 17052 28 _ _ (974407 / 50000) (1948817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290834688 :
    ThetaLowerSegment 290834688 290867456 (29081027833937 / 100000) (14542155802031 / 50000) := by
  exact
    packedTile32768 290834688 290867456 12 1685 17053 28 _ _ (77953 / 4000) (487207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290867456 :
    ThetaLowerSegment 290867456 290900224 (14542155802031 / 50000) (14543823031229 / 50000) := by
  exact
    packedTile32768 290867456 290900224 12 1711 17054 28 _ _ (487209 / 25000) (1948839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290900224 :
    ThetaLowerSegment 290900224 290932992 (14543823031229 / 50000) (14545465910093 / 50000) := by
  exact
    packedTile32768 290900224 290932992 12 1686 17055 28 _ _ (121803 / 6250) (1948851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290932992 :
    ThetaLowerSegment 290932992 290965760 (14545465910093 / 50000) (29094250727063 / 100000) := by
  exact
    packedTile32768 290932992 290965760 12 1703 17056 28 _ _ (1948859 / 100000) (974431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290965760 :
    ThetaLowerSegment 290965760 290998528 (29094250727063 / 100000) (29097569652673 / 100000) := by
  exact
    packedTile32768 290965760 290998528 12 1703 17057 28 _ _ (194887 / 10000) (1948873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell290998528 :
    ThetaLowerSegment 290998528 291031296 (29097569652673 / 100000) (14550411167531 / 50000) := by
  exact
    packedTile32768 290998528 291031296 12 1669 17058 28 _ _ (1948881 / 100000) (487221 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291031296 :
    ThetaLowerSegment 291031296 291064064 (14550411167531 / 50000) (29104172482129 / 100000) := by
  exact
    packedTile32768 291031296 291064064 12 1719 17059 28 _ _ (1948893 / 100000) (60903 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291064064 :
    ThetaLowerSegment 291064064 291096832 (29104172482129 / 100000) (5821483091677 / 20000) := by
  exact
    packedTile32768 291064064 291096832 12 1664 17060 28 _ _ (243613 / 12500) (1948907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291096832 :
    ThetaLowerSegment 291096832 291129600 (5821483091677 / 20000) (5822137927117 / 20000) := by
  exact
    packedTile32768 291096832 291129600 12 1680 17061 28 _ _ (389783 / 20000) (974459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291129600 :
    ThetaLowerSegment 291129600 291162368 (5822137927117 / 20000) (29113965780191 / 100000) := by
  exact
    packedTile32768 291129600 291162368 12 1681 17062 28 _ _ (974463 / 50000) (1948929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291162368 :
    ThetaLowerSegment 291162368 291195136 (29113965780191 / 100000) (29117300413109 / 100000) := by
  exact
    packedTile32768 291162368 291195136 12 1711 17063 28 _ _ (974469 / 50000) (1948941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291195136 :
    ThetaLowerSegment 291195136 291227904 (29117300413109 / 100000) (1164823297729 / 4000) := by
  exact
    packedTile32768 291195136 291227904 12 1684 17064 28 _ _ (1948949 / 100000) (243619 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291227904 :
    ThetaLowerSegment 291227904 291260672 (1164823297729 / 4000) (5824782253381 / 20000) := by
  exact
    packedTile32768 291227904 291260672 12 1708 17065 28 _ _ (12181 / 625) (1948963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291260672 :
    ThetaLowerSegment 291260672 291293440 (5824782253381 / 20000) (7281804667673 / 25000) := by
  exact
    packedTile32768 291260672 291293440 12 1697 17066 28 _ _ (1948971 / 100000) (974487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291293440 :
    ThetaLowerSegment 291293440 291326208 (7281804667673 / 25000) (29130413053829 / 100000) := by
  exact
    packedTile32768 291293440 291326208 12 1639 17067 28 _ _ (1948983 / 100000) (974493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291326208 :
    ThetaLowerSegment 291326208 291358976 (29130413053829 / 100000) (29133699057713 / 100000) := by
  exact
    packedTile32768 291326208 291358976 12 1686 17068 28 _ _ (974497 / 50000) (1948997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291358976 :
    ThetaLowerSegment 291358976 291391744 (29133699057713 / 100000) (14568475973529 / 50000) := by
  exact
    packedTile32768 291358976 291391744 12 1669 17069 28 _ _ (389801 / 20000) (121813 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291391744 :
    ThetaLowerSegment 291391744 291424512 (14568475973529 / 50000) (14570127764589 / 50000) := by
  exact
    packedTile32768 291391744 291424512 12 1695 17070 28 _ _ (243627 / 12500) (1949019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291424512 :
    ThetaLowerSegment 291424512 291457280 (14570127764589 / 50000) (14571750330399 / 50000) := by
  exact
    packedTile32768 291424512 291457280 12 1665 17071 28 _ _ (487257 / 25000) (1949031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291457280 :
    ThetaLowerSegment 291457280 291490048 (14571750330399 / 50000) (14573368032769 / 50000) := by
  exact
    packedTile32768 291457280 291490048 12 1660 17072 28 _ _ (1949039 / 100000) (974521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291490048 :
    ThetaLowerSegment 291490048 291522816 (14573368032769 / 50000) (14574983795219 / 50000) := by
  exact
    packedTile32768 291490048 291522816 12 1658 17073 28 _ _ (38981 / 2000) (1949053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291522816 :
    ThetaLowerSegment 291522816 291555584 (14574983795219 / 50000) (14576605413971 / 50000) := by
  exact
    packedTile32768 291522816 291555584 12 1664 17074 28 _ _ (1949061 / 100000) (243633 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291555584 :
    ThetaLowerSegment 291555584 291588352 (14576605413971 / 50000) (29156491117801 / 100000) := by
  exact
    packedTile32768 291555584 291588352 12 1683 17074 28 _ _ (1949073 / 100000) (487269 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291588352 :
    ThetaLowerSegment 291588352 291621120 (29156491117801 / 100000) (29159765578921 / 100000) := by
  exact
    packedTile32768 291588352 291621120 12 1680 17075 28 _ _ (487271 / 25000) (1949087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291621120 :
    ThetaLowerSegment 291621120 291653888 (29159765578921 / 100000) (911345062738 / 3125) := by
  exact
    packedTile32768 291621120 291653888 12 1681 17076 28 _ _ (389819 / 20000) (974549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291653888 :
    ThetaLowerSegment 291653888 291686656 (911345062738 / 3125) (1458313291447 / 5000) := by
  exact
    packedTile32768 291653888 291686656 12 1654 17077 28 _ _ (974553 / 50000) (1949109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291686656 :
    ThetaLowerSegment 291686656 291719424 (1458313291447 / 5000) (14584767249913 / 50000) := by
  exact
    packedTile32768 291686656 291719424 12 1677 17078 28 _ _ (974559 / 50000) (1949121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291719424 :
    ThetaLowerSegment 291719424 291752192 (14584767249913 / 50000) (29172842171739 / 100000) := by
  exact
    packedTile32768 291719424 291752192 12 1697 17079 28 _ _ (1949129 / 100000) (487283 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291752192 :
    ThetaLowerSegment 291752192 291784960 (29172842171739 / 100000) (29176173251999 / 100000) := by
  exact
    packedTile32768 291752192 291784960 12 1709 17080 28 _ _ (97457 / 5000) (1949143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291784960 :
    ThetaLowerSegment 291784960 291817728 (29176173251999 / 100000) (29179525791719 / 100000) := by
  exact
    packedTile32768 291784960 291817728 12 1720 17081 28 _ _ (1949151 / 100000) (974577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291817728 :
    ThetaLowerSegment 291817728 291850496 (29179525791719 / 100000) (29182817926337 / 100000) := by
  exact
    packedTile32768 291817728 291850496 12 1689 17082 28 _ _ (974581 / 50000) (389833 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291850496 :
    ThetaLowerSegment 291850496 291883264 (29182817926337 / 100000) (29186102284527 / 100000) := by
  exact
    packedTile32768 291850496 291883264 12 1685 17083 28 _ _ (974587 / 50000) (1949177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291883264 :
    ThetaLowerSegment 291883264 291916032 (29186102284527 / 100000) (7297331071833 / 25000) := by
  exact
    packedTile32768 291883264 291916032 12 1653 17084 28 _ _ (389837 / 20000) (487297 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291916032 :
    ThetaLowerSegment 291916032 291948800 (7297331071833 / 25000) (7298161429329 / 25000) := by
  exact
    packedTile32768 291916032 291948800 12 1704 17085 28 _ _ (487299 / 25000) (1949199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291948800 :
    ThetaLowerSegment 291948800 291981568 (7298161429329 / 25000) (29195937927939 / 100000) := by
  exact
    packedTile32768 291948800 291981568 12 1689 17086 28 _ _ (1949207 / 100000) (194921 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell291981568 :
    ThetaLowerSegment 291981568 292014336 (29195937927939 / 100000) (29199310076809 / 100000) := by
  exact
    packedTile32768 291981568 292014336 12 1730 17087 28 _ _ (1949219 / 100000) (974611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292014336 :
    ThetaLowerSegment 292014336 292047104 (29199310076809 / 100000) (29202635463189 / 100000) := by
  exact
    packedTile32768 292014336 292047104 12 1706 17088 28 _ _ (194923 / 10000) (1949233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292047104 :
    ThetaLowerSegment 292047104 292079872 (29202635463189 / 100000) (29205828319947 / 100000) := by
  exact
    packedTile32768 292047104 292079872 12 1638 17089 28 _ _ (1949241 / 100000) (487311 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292079872 :
    ThetaLowerSegment 292079872 292112640 (29205828319947 / 100000) (29209155693111 / 100000) := by
  exact
    packedTile32768 292079872 292112640 12 1707 17090 28 _ _ (487313 / 25000) (389851 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292112640 :
    ThetaLowerSegment 292112640 292145408 (29209155693111 / 100000) (29212586397751 / 100000) := by
  exact
    packedTile32768 292112640 292145408 12 1760 17091 28 _ _ (121829 / 6250) (1949267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292145408 :
    ThetaLowerSegment 292145408 292210944 (29212586397751 / 100000) (14609522172913 / 50000) := by
  exact
    packedTile32768 292145408 292210944 13 3313 17092 28 _ _ (77971 / 4000) (974639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292210944 :
    ThetaLowerSegment 292210944 292243712 (14609522172913 / 50000) (3652791357571 / 12500) := by
  exact
    packedTile32768 292210944 292243712 12 1686 17094 28 _ _ (1949297 / 100000) (19493 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292243712 :
    ThetaLowerSegment 292243712 292276480 (3652791357571 / 12500) (7306411658369 / 25000) := by
  exact
    packedTile32768 292243712 292276480 12 1701 17095 28 _ _ (487327 / 25000) (1949311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292276480 :
    ThetaLowerSegment 292276480 292309248 (7306411658369 / 25000) (7307216727529 / 25000) := by
  exact
    packedTile32768 292276480 292309248 12 1652 17096 28 _ _ (48733 / 2500) (1949323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292309248 :
    ThetaLowerSegment 292309248 292342016 (7307216727529 / 25000) (1827011298301 / 6250) := by
  exact
    packedTile32768 292309248 292342016 12 1700 17097 28 _ _ (1949331 / 100000) (974667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292342016 :
    ThetaLowerSegment 292342016 292374784 (1827011298301 / 6250) (14617721010991 / 50000) := by
  exact
    packedTile32768 292342016 292374784 12 1673 17098 28 _ _ (974671 / 50000) (389869 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292374784 :
    ThetaLowerSegment 292374784 292407552 (14617721010991 / 50000) (29238812453319 / 100000) := by
  exact
    packedTile32768 292374784 292407552 12 1729 17098 28 _ _ (1949353 / 100000) (487339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292407552 :
    ThetaLowerSegment 292407552 292473088 (29238812453319 / 100000) (29245274594979 / 100000) := by
  exact
    packedTile32768 292407552 292473088 13 3315 17099 28 _ _ (487341 / 25000) (1949367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292473088 :
    ThetaLowerSegment 292473088 292505856 (29245274594979 / 100000) (14624283554811 / 50000) := by
  exact
    packedTile32768 292473088 292505856 12 1689 17101 28 _ _ (1949387 / 100000) (194939 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292505856 :
    ThetaLowerSegment 292505856 292538624 (14624283554811 / 50000) (2925183430067 / 10000) := by
  exact
    packedTile32768 292505856 292538624 12 1676 17102 28 _ _ (974699 / 50000) (1949401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292538624 :
    ThetaLowerSegment 292538624 292571392 (2925183430067 / 10000) (29255103459563 / 100000) := by
  exact
    packedTile32768 292538624 292571392 12 1677 17103 28 _ _ (1949409 / 100000) (487353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292571392 :
    ThetaLowerSegment 292571392 292604160 (29255103459563 / 100000) (29258390181683 / 100000) := by
  exact
    packedTile32768 292571392 292604160 12 1686 17104 28 _ _ (97471 / 5000) (1949423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292604160 :
    ThetaLowerSegment 292604160 292636928 (29258390181683 / 100000) (29261602845619 / 100000) := by
  exact
    packedTile32768 292604160 292636928 12 1648 17105 28 _ _ (243679 / 12500) (389887 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292636928 :
    ThetaLowerSegment 292636928 292669696 (29261602845619 / 100000) (29264916898719 / 100000) := by
  exact
    packedTile32768 292636928 292669696 12 1700 17106 28 _ _ (1949443 / 100000) (974723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292669696 :
    ThetaLowerSegment 292669696 292702464 (29264916898719 / 100000) (29268186133077 / 100000) := by
  exact
    packedTile32768 292669696 292702464 12 1677 17107 28 _ _ (974727 / 50000) (1949457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292702464 :
    ThetaLowerSegment 292702464 292735232 (29268186133077 / 100000) (29271426143907 / 100000) := by
  exact
    packedTile32768 292702464 292735232 12 1662 17108 28 _ _ (389893 / 20000) (487367 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292735232 :
    ThetaLowerSegment 292735232 292768000 (29271426143907 / 100000) (29274748051011 / 100000) := by
  exact
    packedTile32768 292735232 292768000 12 1704 17109 28 _ _ (487369 / 25000) (1949479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292768000 :
    ThetaLowerSegment 292768000 292800768 (29274748051011 / 100000) (29277988100067 / 100000) := by
  exact
    packedTile32768 292768000 292800768 12 1662 17110 28 _ _ (121843 / 6250) (1949491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292800768 :
    ThetaLowerSegment 292800768 292833536 (29277988100067 / 100000) (14640632603943 / 50000) := by
  exact
    packedTile32768 292800768 292833536 12 1681 17111 28 _ _ (1949499 / 100000) (974751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292833536 :
    ThetaLowerSegment 292833536 292866304 (14640632603943 / 50000) (7321129735019 / 25000) := by
  exact
    packedTile32768 292833536 292866304 12 1669 17112 28 _ _ (194951 / 10000) (1949513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292866304 :
    ThetaLowerSegment 292866304 292899072 (7321129735019 / 25000) (14643879521989 / 50000) := by
  exact
    packedTile32768 292866304 292899072 12 1662 17113 28 _ _ (1949521 / 100000) (487381 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292899072 :
    ThetaLowerSegment 292899072 292931840 (14643879521989 / 50000) (14645535649423 / 50000) := by
  exact
    packedTile32768 292899072 292931840 12 1699 17114 28 _ _ (487383 / 25000) (389907 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292931840 :
    ThetaLowerSegment 292931840 292964608 (14645535649423 / 50000) (14647172291611 / 50000) := by
  exact
    packedTile32768 292931840 292964608 12 1679 17115 28 _ _ (243693 / 12500) (1949547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292964608 :
    ThetaLowerSegment 292964608 292997376 (14647172291611 / 50000) (14648759229381 / 50000) := by
  exact
    packedTile32768 292964608 292997376 12 1628 17116 28 _ _ (389911 / 20000) (974779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell292997376 :
    ThetaLowerSegment 292997376 293030144 (14648759229381 / 50000) (14650420259613 / 50000) := by
  exact
    packedTile32768 292997376 293030144 12 1704 17117 28 _ _ (974783 / 50000) (1949569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293030144 :
    ThetaLowerSegment 293030144 293062912 (14650420259613 / 50000) (29304195741243 / 100000) := by
  exact
    packedTile32768 293030144 293062912 12 1721 17118 28 _ _ (1949577 / 100000) (97479 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293062912 :
    ThetaLowerSegment 293062912 293095680 (29304195741243 / 100000) (29307531486311 / 100000) := by
  exact
    packedTile32768 293062912 293095680 12 1711 17119 28 _ _ (487397 / 25000) (1949591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293095680 :
    ThetaLowerSegment 293095680 293128448 (29307531486311 / 100000) (29310763921453 / 100000) := by
  exact
    packedTile32768 293095680 293128448 12 1658 17120 28 _ _ (1949599 / 100000) (974801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293128448 :
    ThetaLowerSegment 293128448 293161216 (29310763921453 / 100000) (14657014759939 / 50000) := by
  exact
    packedTile32768 293128448 293161216 12 1675 17120 28 _ _ (1949611 / 100000) (974807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293161216 :
    ThetaLowerSegment 293161216 293193984 (14657014759939 / 50000) (14658664140151 / 50000) := by
  exact
    packedTile32768 293161216 293193984 12 1692 17121 28 _ _ (974811 / 50000) (15597 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293193984 :
    ThetaLowerSegment 293193984 293226752 (14658664140151 / 50000) (916267036711 / 3125) := by
  exact
    packedTile32768 293193984 293226752 12 1650 17122 28 _ _ (1949633 / 100000) (487409 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293226752 :
    ThetaLowerSegment 293226752 293259520 (916267036711 / 3125) (7330965379799 / 25000) := by
  exact
    packedTile32768 293226752 293259520 12 1701 17123 28 _ _ (487411 / 25000) (1949647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293259520 :
    ThetaLowerSegment 293259520 293292288 (7330965379799 / 25000) (29327119392701 / 100000) := by
  exact
    packedTile32768 293259520 293292288 12 1671 17124 28 _ _ (389931 / 20000) (974829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293292288 :
    ThetaLowerSegment 293292288 293325056 (29327119392701 / 100000) (29330394833261 / 100000) := by
  exact
    packedTile32768 293292288 293325056 12 1680 17125 28 _ _ (1949667 / 100000) (194967 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293325056 :
    ThetaLowerSegment 293325056 293357824 (29330394833261 / 100000) (29333586456147 / 100000) := by
  exact
    packedTile32768 293325056 293357824 12 1637 17126 28 _ _ (974839 / 50000) (1949681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293357824 :
    ThetaLowerSegment 293357824 293390592 (29333586456147 / 100000) (29336842436777 / 100000) := by
  exact
    packedTile32768 293357824 293390592 12 1670 17127 28 _ _ (1949689 / 100000) (487423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293390592 :
    ThetaLowerSegment 293390592 293423360 (29336842436777 / 100000) (29340168624977 / 100000) := by
  exact
    packedTile32768 293390592 293423360 12 1706 17128 28 _ _ (19497 / 1000) (1949703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293423360 :
    ThetaLowerSegment 293423360 293456128 (29340168624977 / 100000) (29343416843503 / 100000) := by
  exact
    packedTile32768 293423360 293456128 12 1666 17129 28 _ _ (1949711 / 100000) (974857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293456128 :
    ThetaLowerSegment 293456128 293488896 (29343416843503 / 100000) (29346631935081 / 100000) := by
  exact
    packedTile32768 293456128 293488896 12 1649 17130 28 _ _ (974861 / 50000) (77989 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293488896 :
    ThetaLowerSegment 293488896 293521664 (29346631935081 / 100000) (5869993585991 / 20000) := by
  exact
    packedTile32768 293488896 293521664 12 1711 17131 28 _ _ (974867 / 50000) (1949737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293521664 :
    ThetaLowerSegment 293521664 293554432 (5869993585991 / 20000) (234825729641 / 800) := by
  exact
    packedTile32768 293521664 293554432 12 1666 17132 28 _ _ (389949 / 20000) (487437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293554432 :
    ThetaLowerSegment 293554432 293587200 (234825729641 / 800) (29356536639593 / 100000) := by
  exact
    packedTile32768 293554432 293587200 12 1703 17133 28 _ _ (487439 / 25000) (1949759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293587200 :
    ThetaLowerSegment 293587200 293619968 (29356536639593 / 100000) (117439178801 / 400) := by
  exact
    packedTile32768 293587200 293619968 12 1671 17134 28 _ _ (1949767 / 100000) (194977 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293619968 :
    ThetaLowerSegment 293619968 293652736 (117439178801 / 400) (3670389396523 / 12500) := by
  exact
    packedTile32768 293619968 293652736 12 1703 17135 28 _ _ (974889 / 50000) (1949781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293652736 :
    ThetaLowerSegment 293652736 293685504 (3670389396523 / 12500) (29366462959897 / 100000) := by
  exact
    packedTile32768 293652736 293685504 12 1717 17136 28 _ _ (1949789 / 100000) (60931 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293685504 :
    ThetaLowerSegment 293685504 293718272 (29366462959897 / 100000) (7342428319541 / 25000) := by
  exact
    packedTile32768 293685504 293718272 12 1667 17137 28 _ _ (1949801 / 100000) (487451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293718272 :
    ThetaLowerSegment 293718272 293751040 (7342428319541 / 25000) (1468647303323 / 5000) := by
  exact
    packedTile32768 293718272 293751040 12 1658 17138 28 _ _ (487453 / 25000) (389963 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293751040 :
    ThetaLowerSegment 293751040 293783808 (1468647303323 / 5000) (7344059341921 / 25000) := by
  exact
    packedTile32768 293751040 293783808 12 1688 17139 28 _ _ (1949823 / 100000) (974913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293783808 :
    ThetaLowerSegment 293783808 293816576 (7344059341921 / 25000) (1468977994241 / 5000) := by
  exact
    packedTile32768 293783808 293816576 12 1704 17140 28 _ _ (974917 / 50000) (1949837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293816576 :
    ThetaLowerSegment 293816576 293849344 (1468977994241 / 5000) (5876573754357 / 20000) := by
  exact
    packedTile32768 293816576 293849344 12 1697 17141 28 _ _ (389969 / 20000) (243731 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293849344 :
    ThetaLowerSegment 293849344 293882112 (5876573754357 / 20000) (29386160128713 / 100000) := by
  exact
    packedTile32768 293849344 293882112 12 1688 17142 28 _ _ (60933 / 3125) (1949859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293882112 :
    ThetaLowerSegment 293882112 293914880 (29386160128713 / 100000) (29389478802347 / 100000) := by
  exact
    packedTile32768 293882112 293914880 12 1702 17142 28 _ _ (1949867 / 100000) (194987 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293914880 :
    ThetaLowerSegment 293914880 293980416 (29389478802347 / 100000) (14698062969929 / 50000) := by
  exact
    packedTile32768 293914880 293980416 13 3409 17143 28 _ _ (1949879 / 100000) (974941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell293980416 :
    ThetaLowerSegment 293980416 294045952 (14698062969929 / 50000) (14701362202421 / 50000) := by
  exact
    packedTile32768 293980416 294045952 13 3384 17145 28 _ _ (1949901 / 100000) (121869 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294045952 :
    ThetaLowerSegment 294045952 294111488 (14701362202421 / 50000) (919035126629 / 3125) := by
  exact
    packedTile32768 294045952 294111488 13 3282 17147 28 _ _ (1949923 / 100000) (974963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294111488 :
    ThetaLowerSegment 294111488 294144256 (919035126629 / 3125) (14706194130029 / 50000) := by
  exact
    packedTile32768 294111488 294144256 12 1674 17149 28 _ _ (389989 / 20000) (487487 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294144256 :
    ThetaLowerSegment 294144256 294177024 (14706194130029 / 50000) (1176626645511 / 4000) := by
  exact
    packedTile32768 294144256 294177024 12 1681 17150 28 _ _ (1949957 / 100000) (48749 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294177024 :
    ThetaLowerSegment 294177024 294209792 (1176626645511 / 4000) (29418957683759 / 100000) := by
  exact
    packedTile32768 294177024 294209792 12 1688 17151 28 _ _ (121873 / 6250) (1949971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294209792 :
    ThetaLowerSegment 294209792 294275328 (29418957683759 / 100000) (29425579812443 / 100000) := by
  exact
    packedTile32768 294209792 294275328 13 3396 17152 28 _ _ (1949979 / 100000) (974991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294275328 :
    ThetaLowerSegment 294275328 294340864 (29425579812443 / 100000) (2943214546581 / 10000) := by
  exact
    packedTile32768 294275328 294340864 13 3367 17154 28 _ _ (1950001 / 100000) (487501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294340864 :
    ThetaLowerSegment 294340864 294406400 (2943214546581 / 10000) (1471937802189 / 5000) := by
  exact
    packedTile32768 294340864 294406400 13 3390 17156 28 _ _ (1950023 / 100000) (975013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294406400 :
    ThetaLowerSegment 294406400 294471936 (1471937802189 / 5000) (3680666937373 / 12500) := by
  exact
    packedTile32768 294406400 294471936 13 3374 17158 28 _ _ (975023 / 50000) (1950049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294471936 :
    ThetaLowerSegment 294471936 294537472 (3680666937373 / 12500) (7362958768907 / 25000) := by
  exact
    packedTile32768 294471936 294537472 13 3333 17160 28 _ _ (487517 / 25000) (1950071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294537472 :
    ThetaLowerSegment 294537472 294603008 (7362958768907 / 25000) (7364606594957 / 25000) := by
  exact
    packedTile32768 294537472 294603008 13 3380 17162 28 _ _ (195009 / 10000) (1950093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294603008 :
    ThetaLowerSegment 294603008 294668544 (7364606594957 / 25000) (7366248589261 / 25000) := by
  exact
    packedTile32768 294603008 294668544 13 3368 17164 28 _ _ (60941 / 3125) (390023 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294668544 :
    ThetaLowerSegment 294668544 294734080 (7366248589261 / 25000) (29471455154299 / 100000) := by
  exact
    packedTile32768 294668544 294734080 13 3313 17165 28 _ _ (390027 / 20000) (975069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294734080 :
    ThetaLowerSegment 294734080 294799616 (29471455154299 / 100000) (14739061370541 / 50000) := by
  exact
    packedTile32768 294734080 294799616 13 3419 17167 28 _ _ (1950157 / 100000) (24377 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294799616 :
    ThetaLowerSegment 294799616 294865152 (14739061370541 / 50000) (5896941699113 / 20000) := by
  exact
    packedTile32768 294799616 294865152 13 3377 17169 28 _ _ (1950179 / 100000) (975091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294865152 :
    ThetaLowerSegment 294865152 294930688 (5896941699113 / 20000) (7372810904779 / 25000) := by
  exact
    packedTile32768 294865152 294930688 13 3351 17171 28 _ _ (1950201 / 100000) (487551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294930688 :
    ThetaLowerSegment 294930688 294996224 (7372810904779 / 25000) (7374427152919 / 25000) := by
  exact
    packedTile32768 294930688 294996224 13 3315 17173 28 _ _ (121889 / 6250) (1950227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell294996224 :
    ThetaLowerSegment 294996224 295061760 (7374427152919 / 25000) (14752075137107 / 50000) := by
  exact
    packedTile32768 294996224 295061760 13 3303 17175 28 _ _ (975123 / 50000) (1950249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295061760 :
    ThetaLowerSegment 295061760 295127296 (14752075137107 / 50000) (2951065831853 / 10000) := by
  exact
    packedTile32768 295061760 295127296 13 3337 17177 28 _ _ (487567 / 25000) (1950271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295127296 :
    ThetaLowerSegment 295127296 295160064 (2951065831853 / 10000) (2951388019761 / 10000) := by
  exact
    packedTile32768 295127296 295160064 12 1652 17179 28 _ _ (195029 / 10000) (1950293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295160064 :
    ThetaLowerSegment 295160064 295192832 (2951388019761 / 10000) (14758574451043 / 50000) := by
  exact
    packedTile32768 295160064 295192832 12 1676 17180 28 _ _ (1950301 / 100000) (60947 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295192832 :
    ThetaLowerSegment 295192832 295225600 (14758574451043 / 50000) (14760181508131 / 50000) := by
  exact
    packedTile32768 295192832 295225600 12 1648 17181 28 _ _ (243789 / 12500) (390063 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295225600 :
    ThetaLowerSegment 295225600 295258368 (14760181508131 / 50000) (14761800277051 / 50000) := by
  exact
    packedTile32768 295225600 295258368 12 1660 17182 28 _ _ (487581 / 25000) (1950327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295258368 :
    ThetaLowerSegment 295258368 295291136 (14761800277051 / 50000) (14763454161131 / 50000) := by
  exact
    packedTile32768 295258368 295291136 12 1696 17183 28 _ _ (390067 / 20000) (975169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295291136 :
    ThetaLowerSegment 295291136 295323904 (14763454161131 / 50000) (14765106104193 / 50000) := by
  exact
    packedTile32768 295291136 295323904 12 1694 17184 28 _ _ (975173 / 50000) (1950349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295323904 :
    ThetaLowerSegment 295323904 295356672 (14765106104193 / 50000) (29533486857789 / 100000) := by
  exact
    packedTile32768 295323904 295356672 12 1679 17184 28 _ _ (1950357 / 100000) (48759 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295356672 :
    ThetaLowerSegment 295356672 295389440 (29533486857789 / 100000) (29536808334493 / 100000) := by
  exact
    packedTile32768 295356672 295389440 12 1703 17185 28 _ _ (60949 / 3125) (1950371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295389440 :
    ThetaLowerSegment 295389440 295422208 (29536808334493 / 100000) (7385011978503 / 25000) := by
  exact
    packedTile32768 295389440 295422208 12 1661 17186 28 _ _ (1950379 / 100000) (975191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295422208 :
    ThetaLowerSegment 295422208 295454976 (7385011978503 / 25000) (14771637904731 / 50000) := by
  exact
    packedTile32768 295422208 295454976 12 1655 17187 28 _ _ (195039 / 10000) (1950393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295454976 :
    ThetaLowerSegment 295454976 295487744 (14771637904731 / 50000) (29546515425523 / 100000) := by
  exact
    packedTile32768 295454976 295487744 12 1661 17188 28 _ _ (1950401 / 100000) (487601 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295487744 :
    ThetaLowerSegment 295487744 295520512 (29546515425523 / 100000) (29549897439931 / 100000) := by
  exact
    packedTile32768 295487744 295520512 12 1734 17189 28 _ _ (487603 / 25000) (390083 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295520512 :
    ThetaLowerSegment 295520512 295553280 (29549897439931 / 100000) (14776545141191 / 50000) := by
  exact
    packedTile32768 295520512 295553280 12 1637 17190 28 _ _ (1950423 / 100000) (975213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295553280 :
    ThetaLowerSegment 295553280 295586048 (14776545141191 / 50000) (14778203010091 / 50000) := by
  exact
    packedTile32768 295553280 295586048 12 1700 17191 28 _ _ (975217 / 50000) (1950437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295586048 :
    ThetaLowerSegment 295586048 295618816 (14778203010091 / 50000) (14779827731609 / 50000) := by
  exact
    packedTile32768 295586048 295618816 12 1666 17192 28 _ _ (975223 / 50000) (1950449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295618816 :
    ThetaLowerSegment 295618816 295651584 (14779827731609 / 50000) (29563074614339 / 100000) := by
  exact
    packedTile32768 295618816 295651584 12 1753 17193 28 _ _ (1950457 / 100000) (97523 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295651584 :
    ThetaLowerSegment 295651584 295684352 (29563074614339 / 100000) (29566279233263 / 100000) := by
  exact
    packedTile32768 295651584 295684352 12 1643 17194 28 _ _ (487617 / 25000) (1950471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295684352 :
    ThetaLowerSegment 295684352 295717120 (29566279233263 / 100000) (14784743885609 / 50000) := by
  exact
    packedTile32768 295684352 295717120 12 1645 17195 28 _ _ (1950479 / 100000) (975241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295717120 :
    ThetaLowerSegment 295717120 295749888 (14784743885609 / 50000) (14786362792309 / 50000) := by
  exact
    packedTile32768 295717120 295749888 12 1660 17196 28 _ _ (195049 / 10000) (1950493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295749888 :
    ThetaLowerSegment 295749888 295782656 (14786362792309 / 50000) (29576078495837 / 100000) := by
  exact
    packedTile32768 295749888 295782656 12 1719 17197 28 _ _ (1950501 / 100000) (243813 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295782656 :
    ThetaLowerSegment 295782656 295815424 (29576078495837 / 100000) (5915880433657 / 20000) := by
  exact
    packedTile32768 295782656 295815424 12 1704 17198 28 _ _ (121907 / 6250) (390103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295815424 :
    ThetaLowerSegment 295815424 295848192 (5915880433657 / 20000) (1848916587079 / 6250) := by
  exact
    packedTile32768 295815424 295848192 12 1673 17199 28 _ _ (1950523 / 100000) (975263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295848192 :
    ThetaLowerSegment 295848192 295880960 (1848916587079 / 6250) (369823888523 / 1250) := by
  exact
    packedTile32768 295848192 295880960 12 1664 17200 28 _ _ (975267 / 50000) (1950537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295880960 :
    ThetaLowerSegment 295880960 295913728 (369823888523 / 1250) (5917833308289 / 20000) := by
  exact
    packedTile32768 295880960 295913728 12 1669 17201 28 _ _ (390109 / 20000) (487637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295913728 :
    ThetaLowerSegment 295913728 295946496 (5917833308289 / 20000) (5918476991769 / 20000) := by
  exact
    packedTile32768 295913728 295946496 12 1650 17202 28 _ _ (487639 / 25000) (1950559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295946496 :
    ThetaLowerSegment 295946496 295979264 (5918476991769 / 20000) (29595669713673 / 100000) := by
  exact
    packedTile32768 295946496 295979264 12 1684 17203 28 _ _ (1950567 / 100000) (195057 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell295979264 :
    ThetaLowerSegment 295979264 296012032 (29595669713673 / 100000) (5919804551451 / 20000) := by
  exact
    packedTile32768 295979264 296012032 12 1719 17204 28 _ _ (975289 / 50000) (1950581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296012032 :
    ThetaLowerSegment 296012032 296044800 (5919804551451 / 20000) (5920466191579 / 20000) := by
  exact
    packedTile32768 296012032 296044800 12 1696 17205 28 _ _ (195059 / 10000) (1950593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296044800 :
    ThetaLowerSegment 296044800 296077568 (5920466191579 / 20000) (2960563722659 / 10000) := by
  exact
    packedTile32768 296044800 296077568 12 1695 17205 28 _ _ (1950601 / 100000) (487651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296077568 :
    ThetaLowerSegment 296077568 296110336 (2960563722659 / 10000) (14804425917583 / 50000) := by
  exact
    packedTile32768 296077568 296110336 12 1648 17206 28 _ _ (487653 / 25000) (390123 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296110336 :
    ThetaLowerSegment 296110336 296143104 (14804425917583 / 50000) (3701513671947 / 12500) := by
  exact
    packedTile32768 296110336 296143104 12 1670 17207 28 _ _ (1950623 / 100000) (975313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296143104 :
    ThetaLowerSegment 296143104 296175872 (3701513671947 / 12500) (740385441271 / 2500) := by
  exact
    packedTile32768 296143104 296175872 12 1696 17208 28 _ _ (975317 / 50000) (1950637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296175872 :
    ThetaLowerSegment 296175872 296208640 (740385441271 / 2500) (1480936687367 / 5000) := by
  exact
    packedTile32768 296175872 296208640 12 1700 17209 28 _ _ (390129 / 20000) (243831 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296208640 :
    ThetaLowerSegment 296208640 296241408 (1480936687367 / 5000) (7405492471411 / 25000) := by
  exact
    packedTile32768 296208640 296241408 12 1659 17210 28 _ _ (60958 / 3125) (1950659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296241408 :
    ThetaLowerSegment 296241408 296274176 (7405492471411 / 25000) (2962524310487 / 10000) := by
  exact
    packedTile32768 296241408 296274176 12 1678 17211 28 _ _ (1950667 / 100000) (195067 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296274176 :
    ThetaLowerSegment 296274176 296306944 (2962524310487 / 10000) (740712762263 / 2500) := by
  exact
    packedTile32768 296274176 296306944 12 1675 17212 28 _ _ (975339 / 50000) (1950681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296306944 :
    ThetaLowerSegment 296306944 296339712 (740712762263 / 2500) (14815950394001 / 50000) := by
  exact
    packedTile32768 296306944 296339712 12 1738 17213 28 _ _ (1950689 / 100000) (487673 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296339712 :
    ThetaLowerSegment 296339712 296372480 (14815950394001 / 50000) (14817568499651 / 50000) := by
  exact
    packedTile32768 296339712 296372480 12 1659 17214 28 _ _ (19507 / 1000) (1950703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296372480 :
    ThetaLowerSegment 296372480 296405248 (14817568499651 / 50000) (29638427848759 / 100000) := by
  exact
    packedTile32768 296372480 296405248 12 1687 17215 28 _ _ (1950711 / 100000) (975357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296405248 :
    ThetaLowerSegment 296405248 296438016 (29638427848759 / 100000) (5928351936387 / 20000) := by
  exact
    packedTile32768 296405248 296438016 12 1708 17216 28 _ _ (975361 / 50000) (78029 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296438016 :
    ThetaLowerSegment 296438016 296503552 (5928351936387 / 20000) (3706034635111 / 12500) := by
  exact
    packedTile32768 296438016 296503552 13 3341 17217 28 _ _ (1950733 / 100000) (121921 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296503552 :
    ThetaLowerSegment 296503552 296536320 (3706034635111 / 12500) (29651548497023 / 100000) := by
  exact
    packedTile32768 296503552 296536320 12 1677 17219 28 _ _ (390151 / 20000) (975379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296536320 :
    ThetaLowerSegment 296536320 296569088 (29651548497023 / 100000) (29654810179447 / 100000) := by
  exact
    packedTile32768 296536320 296569088 12 1672 17220 28 _ _ (1950767 / 100000) (195077 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296569088 :
    ThetaLowerSegment 296569088 296601856 (29654810179447 / 100000) (1186325138113 / 4000) := by
  exact
    packedTile32768 296569088 296601856 12 1701 17221 28 _ _ (975389 / 50000) (1950781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296601856 :
    ThetaLowerSegment 296601856 296667392 (1186325138113 / 4000) (29664710414911 / 100000) := by
  exact
    packedTile32768 296601856 296667392 13 3374 17222 28 _ _ (1950789 / 100000) (243849 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296667392 :
    ThetaLowerSegment 296667392 296732928 (29664710414911 / 100000) (29671191009053 / 100000) := by
  exact
    packedTile32768 296667392 296732928 13 3322 17224 28 _ _ (1950811 / 100000) (975407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296732928 :
    ThetaLowerSegment 296732928 296765696 (29671191009053 / 100000) (1186979048473 / 4000) := by
  exact
    packedTile32768 296732928 296765696 12 1684 17225 28 _ _ (1950833 / 100000) (487709 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296765696 :
    ThetaLowerSegment 296765696 296798464 (1186979048473 / 4000) (5935550725949 / 20000) := by
  exact
    packedTile32768 296765696 296798464 12 1680 17226 28 _ _ (487711 / 25000) (1950847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296798464 :
    ThetaLowerSegment 296798464 296831232 (5935550725949 / 20000) (2968099009819 / 10000) := by
  exact
    packedTile32768 296798464 296831232 12 1659 17227 28 _ _ (390171 / 20000) (975429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296831232 :
    ThetaLowerSegment 296831232 296864000 (2968099009819 / 10000) (14842110366143 / 50000) := by
  exact
    packedTile32768 296831232 296864000 12 1656 17228 28 _ _ (975433 / 50000) (1950869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296864000 :
    ThetaLowerSegment 296864000 296896768 (14842110366143 / 50000) (29687504058277 / 100000) := by
  exact
    packedTile32768 296864000 296896768 12 1683 17229 28 _ _ (1950877 / 100000) (12193 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296896768 :
    ThetaLowerSegment 296896768 296929536 (29687504058277 / 100000) (29690828371429 / 100000) := by
  exact
    packedTile32768 296896768 296929536 12 1704 17230 28 _ _ (243861 / 12500) (1950891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296929536 :
    ThetaLowerSegment 296929536 296962304 (29690828371429 / 100000) (7423509400071 / 25000) := by
  exact
    packedTile32768 296929536 296962304 12 1645 17231 28 _ _ (1950899 / 100000) (975451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296962304 :
    ThetaLowerSegment 296962304 296995072 (7423509400071 / 25000) (14848668294547 / 50000) := by
  exact
    packedTile32768 296962304 296995072 12 1691 17232 28 _ _ (195091 / 10000) (1950913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell296995072 :
    ThetaLowerSegment 296995072 297027840 (14848668294547 / 50000) (29700619989137 / 100000) := by
  exact
    packedTile32768 296995072 297027840 12 1683 17233 28 _ _ (1950921 / 100000) (487731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297027840 :
    ThetaLowerSegment 297027840 297060608 (29700619989137 / 100000) (29703881947441 / 100000) := by
  exact
    packedTile32768 297027840 297060608 12 1672 17234 28 _ _ (487733 / 25000) (390187 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297060608 :
    ThetaLowerSegment 297060608 297093376 (29703881947441 / 100000) (29707186844883 / 100000) := by
  exact
    packedTile32768 297060608 297093376 12 1694 17235 28 _ _ (1950943 / 100000) (975473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297093376 :
    ThetaLowerSegment 297093376 297126144 (29707186844883 / 100000) (29710446889017 / 100000) := by
  exact
    packedTile32768 297093376 297126144 12 1671 17236 28 _ _ (975477 / 50000) (1950957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297126144 :
    ThetaLowerSegment 297126144 297158912 (29710446889017 / 100000) (14856855426731 / 50000) := by
  exact
    packedTile32768 297126144 297158912 12 1673 17237 28 _ _ (390193 / 20000) (243871 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297158912 :
    ThetaLowerSegment 297158912 297191680 (14856855426731 / 50000) (14858484491691 / 50000) := by
  exact
    packedTile32768 297158912 297191680 12 1670 17238 28 _ _ (60968 / 3125) (1950979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297191680 :
    ThetaLowerSegment 297191680 297224448 (14858484491691 / 50000) (2972033248497 / 10000) := by
  exact
    packedTile32768 297191680 297224448 12 1724 17239 28 _ _ (1950987 / 100000) (195099 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297224448 :
    ThetaLowerSegment 297224448 297257216 (2972033248497 / 10000) (371545736707 / 1250) := by
  exact
    packedTile32768 297224448 297257216 12 1705 17240 28 _ _ (975499 / 50000) (1951001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297257216 :
    ThetaLowerSegment 297257216 297322752 (371545736707 / 1250) (7432571140781 / 25000) := by
  exact
    packedTile32768 297257216 297322752 13 3396 17241 28 _ _ (1951009 / 100000) (487753 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297322752 :
    ThetaLowerSegment 297322752 297339136 (7432571140781 / 25000) (2973189611473 / 10000) := by
  exact
    packedTile32768 297322752 297339136 11 826 17243 28 _ _ (1951031 / 100000) (975517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell297339136 :
    ThetaLowerSegment 297339136 297341184 (2973189611473 / 10000) (7433021829089 / 25000) := by
  exact
    packedTile32768 297339136 297341184 8 98 17243 28 _ _ (1951037 / 100000) (12194 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_265341184_297341184 :
    ThetaLowerSegment 265341184 297341184 (6633105923007 / 25000) (7433021829089 / 25000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell265341184 cell265373952)
                      (ThetaLowerSegment.join cell265406720 cell265472256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell265537792 cell265603328)
                      (ThetaLowerSegment.join cell265668864 cell265734400)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell265799936 cell265865472)
                      (ThetaLowerSegment.join cell265931008 cell265996544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell266062080 cell266127616)
                      (ThetaLowerSegment.join cell266193152 cell266258688))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell266324224 cell266389760)
                      (ThetaLowerSegment.join cell266455296 cell266520832))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell266553600 cell266586368)
                      (ThetaLowerSegment.join cell266619136 cell266651904)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell266684672 cell266717440)
                      (ThetaLowerSegment.join cell266750208 cell266782976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell266815744 cell266848512)
                      (ThetaLowerSegment.join cell266881280 cell266914048)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell266946816 cell266979584)
                      (ThetaLowerSegment.join cell267012352 cell267045120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell267077888 cell267110656)
                      (ThetaLowerSegment.join cell267143424 cell267176192)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell267208960 cell267241728)
                      (ThetaLowerSegment.join cell267274496 cell267307264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell267340032 cell267372800)
                      (ThetaLowerSegment.join cell267405568 cell267438336))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell267471104 cell267503872)
                      (ThetaLowerSegment.join cell267536640 cell267569408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell267602176 cell267634944)
                      (ThetaLowerSegment.join cell267667712 cell267700480)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell267733248 cell267766016)
                      (ThetaLowerSegment.join cell267798784 cell267831552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell267864320 cell267897088)
                      (ThetaLowerSegment.join cell267929856 cell267962624))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell267995392 cell268028160)
                      (ThetaLowerSegment.join cell268060928 cell268093696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell268126464 cell268159232)
                      (ThetaLowerSegment.join cell268192000 cell268224768)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell268257536 cell268290304)
                      (ThetaLowerSegment.join cell268323072 cell268355840))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell268388608 cell268421376)
                      (ThetaLowerSegment.join cell268454144 cell268486912))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell268519680 cell268552448)
                      (ThetaLowerSegment.join cell268585216 cell268617984))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell268650752 cell268683520)
                      (ThetaLowerSegment.join cell268716288 cell268749056)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell268781824 cell268814592)
                      (ThetaLowerSegment.join cell268847360 cell268880128))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell268912896 cell268945664)
                      (ThetaLowerSegment.join cell268978432 cell269011200)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell269076736 cell269109504)
                      (ThetaLowerSegment.join cell269142272 cell269175040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell269207808 cell269240576)
                      (ThetaLowerSegment.join cell269306112 cell269371648)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell269437184 cell269502720)
                      (ThetaLowerSegment.join cell269535488 cell269601024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell269633792 cell269666560)
                      (ThetaLowerSegment.join cell269699328 cell269732096))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell269764864 cell269797632)
                      (ThetaLowerSegment.join cell269830400 cell269863168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell269895936 cell269928704)
                      (ThetaLowerSegment.join cell269961472 cell269994240)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell270027008 cell270059776)
                      (ThetaLowerSegment.join cell270092544 cell270125312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell270158080 cell270190848)
                      (ThetaLowerSegment.join cell270223616 cell270256384)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell270289152 cell270321920)
                      (ThetaLowerSegment.join cell270354688 cell270387456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell270420224 cell270452992)
                      (ThetaLowerSegment.join cell270485760 cell270518528)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell270551296 cell270584064)
                      (ThetaLowerSegment.join cell270616832 cell270649600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell270682368 cell270715136)
                      (ThetaLowerSegment.join cell270747904 cell270780672))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell270813440 cell270846208)
                      (ThetaLowerSegment.join cell270878976 cell270911744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell270944512 cell270977280)
                      (ThetaLowerSegment.join cell271010048 cell271042816)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell271075584 cell271108352)
                      (ThetaLowerSegment.join cell271141120 cell271173888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell271206656 cell271239424)
                      (ThetaLowerSegment.join cell271272192 cell271304960)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell271337728 cell271370496)
                      (ThetaLowerSegment.join cell271403264 cell271436032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell271468800 cell271501568)
                      (ThetaLowerSegment.join cell271534336 cell271567104)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell271599872 cell271632640)
                      (ThetaLowerSegment.join cell271665408 cell271698176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell271730944 cell271763712)
                      (ThetaLowerSegment.join cell271796480 cell271829248))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell271862016 cell271894784)
                      (ThetaLowerSegment.join cell271927552 cell271960320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell271993088 cell272025856)
                      (ThetaLowerSegment.join cell272058624 cell272091392)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell272124160 cell272156928)
                      (ThetaLowerSegment.join cell272189696 cell272222464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell272255232 cell272288000)
                      (ThetaLowerSegment.join cell272320768 cell272353536))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell272386304 cell272419072)
                      (ThetaLowerSegment.join cell272451840 cell272484608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell272517376 cell272550144)
                      (ThetaLowerSegment.join cell272582912 cell272615680)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell272648448 cell272681216)
                      (ThetaLowerSegment.join cell272713984 cell272746752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell272779520 cell272812288)
                      (ThetaLowerSegment.join cell272845056 cell272877824))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell272910592 cell272943360)
                      (ThetaLowerSegment.join cell272976128 cell273008896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell273041664 cell273074432)
                      (ThetaLowerSegment.join cell273107200 cell273139968)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell273172736 cell273205504)
                      (ThetaLowerSegment.join cell273238272 cell273271040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell273303808 cell273336576)
                      (ThetaLowerSegment.join cell273369344 cell273402112)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell273434880 cell273467648)
                      (ThetaLowerSegment.join cell273500416 cell273533184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell273565952 cell273598720)
                      (ThetaLowerSegment.join cell273631488 cell273664256)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell273697024 cell273729792)
                      (ThetaLowerSegment.join cell273762560 cell273795328))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell273828096 cell273860864)
                      (ThetaLowerSegment.join cell273893632 cell273926400))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell273959168 cell273991936)
                      (ThetaLowerSegment.join cell274024704 cell274057472))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell274090240 cell274123008)
                      (ThetaLowerSegment.join cell274155776 cell274188544)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell274221312 cell274254080)
                      (ThetaLowerSegment.join cell274286848 cell274319616))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell274352384 cell274385152)
                      (ThetaLowerSegment.join cell274417920 cell274450688))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell274483456 cell274516224)
                      (ThetaLowerSegment.join cell274548992 cell274581760))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell274614528 cell274647296)
                      (ThetaLowerSegment.join cell274680064 cell274712832)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell274745600 cell274778368)
                      (ThetaLowerSegment.join cell274811136 cell274843904))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell274876672 cell274909440)
                      (ThetaLowerSegment.join cell274942208 cell274974976))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell275007744 cell275040512)
                      (ThetaLowerSegment.join cell275073280 cell275106048))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell275138816 cell275171584)
                      (ThetaLowerSegment.join cell275204352 cell275237120)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell275269888 cell275302656)
                      (ThetaLowerSegment.join cell275335424 cell275368192))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell275400960 cell275433728)
                      (ThetaLowerSegment.join cell275466496 cell275499264)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell275532032 cell275564800)
                      (ThetaLowerSegment.join cell275597568 cell275630336))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell275663104 cell275695872)
                      (ThetaLowerSegment.join cell275728640 cell275761408)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell275794176 cell275826944)
                      (ThetaLowerSegment.join cell275859712 cell275892480))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell275925248 cell275958016)
                      (ThetaLowerSegment.join cell275990784 cell276023552))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell276056320 cell276089088)
                      (ThetaLowerSegment.join cell276121856 cell276154624))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell276187392 cell276220160)
                      (ThetaLowerSegment.join cell276252928 cell276285696)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell276318464 cell276351232)
                      (ThetaLowerSegment.join cell276384000 cell276416768))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell276449536 cell276482304)
                      (ThetaLowerSegment.join cell276515072 cell276547840))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell276580608 cell276613376)
                      (ThetaLowerSegment.join cell276646144 cell276678912))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell276711680 cell276744448)
                      (ThetaLowerSegment.join cell276777216 cell276809984)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell276842752 cell276875520)
                      (ThetaLowerSegment.join cell276908288 cell276941056))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell276973824 cell277006592)
                      (ThetaLowerSegment.join cell277039360 cell277072128))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell277104896 cell277137664)
                      (ThetaLowerSegment.join cell277170432 cell277203200))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell277235968 cell277268736)
                      (ThetaLowerSegment.join cell277301504 cell277334272)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell277367040 cell277399808)
                      (ThetaLowerSegment.join cell277432576 cell277465344))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell277498112 cell277530880)
                      (ThetaLowerSegment.join cell277563648 cell277629184)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell277694720 cell277760256)
                      (ThetaLowerSegment.join cell277825792 cell277891328))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell277956864 cell278022400)
                      (ThetaLowerSegment.join cell278087936 cell278153472)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell278219008 cell278284544)
                      (ThetaLowerSegment.join cell278350080 cell278415616))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell278481152 cell278513920)
                      (ThetaLowerSegment.join cell278546688 cell278579456))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell278612224 cell278644992)
                      (ThetaLowerSegment.join cell278677760 cell278710528))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell278743296 cell278776064)
                      (ThetaLowerSegment.join cell278808832 cell278841600)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell278874368 cell278907136)
                      (ThetaLowerSegment.join cell278939904 cell278972672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell279005440 cell279038208)
                      (ThetaLowerSegment.join cell279070976 cell279103744)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell279136512 cell279169280)
                      (ThetaLowerSegment.join cell279202048 cell279234816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell279267584 cell279300352)
                      (ThetaLowerSegment.join cell279333120 cell279365888)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell279398656 cell279431424)
                      (ThetaLowerSegment.join cell279464192 cell279496960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell279529728 cell279562496)
                      (ThetaLowerSegment.join cell279595264 cell279628032))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell279660800 cell279693568)
                      (ThetaLowerSegment.join cell279726336 cell279759104))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell279824640 cell279890176)
                      (ThetaLowerSegment.join cell279922944 cell279955712)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell279988480 cell280021248)
                      (ThetaLowerSegment.join cell280054016 cell280086784))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell280119552 cell280152320)
                      (ThetaLowerSegment.join cell280185088 cell280250624)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell280316160 cell280381696)
                      (ThetaLowerSegment.join cell280414464 cell280447232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell280480000 cell280545536)
                      (ThetaLowerSegment.join cell280611072 cell280676608)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell280742144 cell280807680)
                      (ThetaLowerSegment.join cell280873216 cell280938752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell281004288 cell281037056)
                      (ThetaLowerSegment.join cell281069824 cell281102592))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell281135360 cell281200896)
                      (ThetaLowerSegment.join cell281266432 cell281331968))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell281397504 cell281463040)
                      (ThetaLowerSegment.join cell281528576 cell281594112)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell281659648 cell281725184)
                      (ThetaLowerSegment.join cell281790720 cell281856256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell281921792 cell281987328)
                      (ThetaLowerSegment.join cell282052864 cell282118400))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell282183936 cell282249472)
                      (ThetaLowerSegment.join cell282282240 cell282347776))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell282413312 cell282478848)
                      (ThetaLowerSegment.join cell282544384 cell282609920)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell282675456 cell282740992)
                      (ThetaLowerSegment.join cell282806528 cell282872064))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell282937600 cell282970368)
                      (ThetaLowerSegment.join cell283035904 cell283101440))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell283166976 cell283199744)
                      (ThetaLowerSegment.join cell283232512 cell283265280))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell283298048 cell283330816)
                      (ThetaLowerSegment.join cell283363584 cell283396352)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell283429120 cell283461888)
                      (ThetaLowerSegment.join cell283494656 cell283527424))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell283560192 cell283592960)
                      (ThetaLowerSegment.join cell283625728 cell283691264)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell283756800 cell283822336)
                      (ThetaLowerSegment.join cell283887872 cell283953408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell284018944 cell284084480)
                      (ThetaLowerSegment.join cell284117248 cell284182784)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell284248320 cell284281088)
                      (ThetaLowerSegment.join cell284313856 cell284346624))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell284379392 cell284444928)
                      (ThetaLowerSegment.join cell284510464 cell284543232))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell284576000 cell284608768)
                      (ThetaLowerSegment.join cell284641536 cell284674304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell284707072 cell284739840)
                      (ThetaLowerSegment.join cell284772608 cell284805376)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell284838144 cell284870912)
                      (ThetaLowerSegment.join cell284903680 cell284936448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell284969216 cell285001984)
                      (ThetaLowerSegment.join cell285034752 cell285067520)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell285100288 cell285133056)
                      (ThetaLowerSegment.join cell285165824 cell285198592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell285231360 cell285264128)
                      (ThetaLowerSegment.join cell285296896 cell285329664)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell285362432 cell285395200)
                      (ThetaLowerSegment.join cell285427968 cell285460736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell285493504 cell285526272)
                      (ThetaLowerSegment.join cell285559040 cell285591808))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell285624576 cell285657344)
                      (ThetaLowerSegment.join cell285690112 cell285722880))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell285755648 cell285788416)
                      (ThetaLowerSegment.join cell285821184 cell285853952)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell285886720 cell285919488)
                      (ThetaLowerSegment.join cell285952256 cell285985024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell286017792 cell286050560)
                      (ThetaLowerSegment.join cell286083328 cell286116096)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell286148864 cell286181632)
                      (ThetaLowerSegment.join cell286214400 cell286247168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell286279936 cell286312704)
                      (ThetaLowerSegment.join cell286345472 cell286378240)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell286411008 cell286443776)
                      (ThetaLowerSegment.join cell286476544 cell286509312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell286542080 cell286574848)
                      (ThetaLowerSegment.join cell286607616 cell286640384))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell286673152 cell286705920)
                      (ThetaLowerSegment.join cell286738688 cell286771456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell286804224 cell286836992)
                      (ThetaLowerSegment.join cell286869760 cell286902528)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell286935296 cell286968064)
                      (ThetaLowerSegment.join cell287000832 cell287033600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell287066368 cell287099136)
                      (ThetaLowerSegment.join cell287131904 cell287164672))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell287197440 cell287230208)
                      (ThetaLowerSegment.join cell287262976 cell287295744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell287328512 cell287361280)
                      (ThetaLowerSegment.join cell287394048 cell287426816)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell287459584 cell287492352)
                      (ThetaLowerSegment.join cell287525120 cell287557888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell287590656 cell287623424)
                      (ThetaLowerSegment.join cell287656192 cell287688960))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell287721728 cell287754496)
                      (ThetaLowerSegment.join cell287787264 cell287820032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell287852800 cell287885568)
                      (ThetaLowerSegment.join cell287918336 cell287951104)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell287983872 cell288016640)
                      (ThetaLowerSegment.join cell288049408 cell288082176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell288114944 cell288147712)
                      (ThetaLowerSegment.join cell288180480 cell288213248)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell288246016 cell288278784)
                      (ThetaLowerSegment.join cell288311552 cell288344320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell288377088 cell288409856)
                      (ThetaLowerSegment.join cell288442624 cell288475392)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell288508160 cell288540928)
                      (ThetaLowerSegment.join cell288573696 cell288606464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell288639232 cell288672000)
                      (ThetaLowerSegment.join cell288704768 cell288737536))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell288770304 cell288803072)
                      (ThetaLowerSegment.join cell288835840 cell288868608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell288901376 cell288934144)
                      (ThetaLowerSegment.join cell288966912 cell288999680)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell289032448 cell289065216)
                      (ThetaLowerSegment.join cell289097984 cell289130752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell289163520 cell289196288)
                      (ThetaLowerSegment.join cell289229056 cell289261824)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell289294592 cell289327360)
                      (ThetaLowerSegment.join cell289360128 cell289392896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell289425664 cell289458432)
                      (ThetaLowerSegment.join cell289491200 cell289523968)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell289556736 cell289589504)
                      (ThetaLowerSegment.join cell289622272 cell289655040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell289687808 cell289720576)
                      (ThetaLowerSegment.join cell289753344 cell289786112))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell289818880 cell289851648)
                      (ThetaLowerSegment.join cell289884416 cell289917184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell289949952 cell289982720)
                      (ThetaLowerSegment.join cell290015488 cell290048256)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell290081024 cell290113792)
                      (ThetaLowerSegment.join cell290146560 cell290179328))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell290212096 cell290244864)
                      (ThetaLowerSegment.join cell290277632 cell290310400)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell290343168 cell290375936)
                      (ThetaLowerSegment.join cell290408704 cell290441472))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell290474240 cell290507008)
                      (ThetaLowerSegment.join cell290539776 cell290572544)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell290605312 cell290638080)
                      (ThetaLowerSegment.join cell290670848 cell290703616))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell290736384 cell290769152)
                      (ThetaLowerSegment.join cell290801920 cell290834688))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell290867456 cell290900224)
                      (ThetaLowerSegment.join cell290932992 cell290965760))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell290998528 cell291031296)
                      (ThetaLowerSegment.join cell291064064 cell291096832)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell291129600 cell291162368)
                      (ThetaLowerSegment.join cell291195136 cell291227904))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell291260672 cell291293440)
                      (ThetaLowerSegment.join cell291326208 cell291358976))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell291391744 cell291424512)
                      (ThetaLowerSegment.join cell291457280 cell291490048))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell291522816 cell291555584)
                      (ThetaLowerSegment.join cell291588352 cell291621120)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell291653888 cell291686656)
                      (ThetaLowerSegment.join cell291719424 cell291752192))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell291784960 cell291817728)
                      (ThetaLowerSegment.join cell291850496 cell291883264))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell291916032 cell291948800)
                      (ThetaLowerSegment.join cell291981568 cell292014336))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell292047104 cell292079872)
                      (ThetaLowerSegment.join cell292112640 cell292145408)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell292210944 cell292243712)
                      (ThetaLowerSegment.join cell292276480 cell292309248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell292342016 cell292374784)
                      (ThetaLowerSegment.join cell292407552 cell292473088)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell292505856 cell292538624)
                      (ThetaLowerSegment.join cell292571392 cell292604160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell292636928 cell292669696)
                      (ThetaLowerSegment.join cell292702464 cell292735232)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell292768000 cell292800768)
                      (ThetaLowerSegment.join cell292833536 cell292866304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell292899072 cell292931840)
                      (ThetaLowerSegment.join cell292964608 cell292997376))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell293030144 cell293062912)
                      (ThetaLowerSegment.join cell293095680 cell293128448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell293161216 cell293193984)
                      (ThetaLowerSegment.join cell293226752 cell293259520)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell293292288 cell293325056)
                      (ThetaLowerSegment.join cell293357824 cell293390592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell293423360 cell293456128)
                      (ThetaLowerSegment.join cell293488896 cell293521664))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell293554432 cell293587200)
                    (ThetaLowerSegment.join cell293619968 cell293652736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell293685504 cell293718272)
                    (ThetaLowerSegment.join cell293751040 cell293783808)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell293816576 cell293849344)
                    (ThetaLowerSegment.join cell293882112 cell293914880))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell293980416 cell294045952)
                    (ThetaLowerSegment.join cell294111488 cell294144256))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell294177024 cell294209792)
                    (ThetaLowerSegment.join cell294275328 cell294340864))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell294406400 cell294471936)
                    (ThetaLowerSegment.join cell294537472 cell294603008)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell294668544 cell294734080)
                    (ThetaLowerSegment.join cell294799616 cell294865152))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell294930688 cell294996224)
                    (ThetaLowerSegment.join cell295061760 cell295127296)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell295160064 cell295192832)
                    (ThetaLowerSegment.join cell295225600 cell295258368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell295291136 cell295323904)
                    (ThetaLowerSegment.join cell295356672 cell295389440)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell295422208 cell295454976)
                    (ThetaLowerSegment.join cell295487744 cell295520512))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell295553280 cell295586048)
                    (ThetaLowerSegment.join cell295618816 cell295651584))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell295684352 cell295717120)
                    (ThetaLowerSegment.join cell295749888 cell295782656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell295815424 cell295848192)
                    (ThetaLowerSegment.join cell295880960 cell295913728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell295946496 cell295979264)
                    (ThetaLowerSegment.join cell296012032 cell296044800))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell296077568 cell296110336)
                    (ThetaLowerSegment.join cell296143104 cell296175872))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell296208640 cell296241408)
                  (ThetaLowerSegment.join cell296274176 cell296306944))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell296339712 cell296372480)
                  (ThetaLowerSegment.join cell296405248 cell296438016)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell296503552 cell296536320)
                  (ThetaLowerSegment.join cell296569088 cell296601856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell296667392 cell296732928)
                  (ThetaLowerSegment.join cell296765696 cell296798464))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell296831232 cell296864000)
                  (ThetaLowerSegment.join cell296896768 cell296929536))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell296962304 cell296995072)
                  (ThetaLowerSegment.join cell297027840 cell297060608)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell297093376 cell297126144)
                  (ThetaLowerSegment.join cell297158912 cell297191680))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell297224448 cell297257216)
                  (ThetaLowerSegment.join cell297322752 cell297339136))))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
