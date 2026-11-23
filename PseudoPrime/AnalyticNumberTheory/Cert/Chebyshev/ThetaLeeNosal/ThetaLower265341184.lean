/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis16384

/-! # Direct theta estimate up to 265341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell234012928 :
    ThetaLowerSegment 234012928 234045696 (5849673503353 / 25000) (11700975395221 / 50000) := by
  exact
    packedTile16384 234012928 234045696 12 1690 15297 28 _ _ (1927087 / 100000) (192709 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234045696 :
    ThetaLowerSegment 234045696 234078464 (11700975395221 / 50000) (23405263477061 / 100000) := by
  exact
    packedTile16384 234045696 234078464 12 1719 15298 28 _ _ (1927101 / 100000) (60222 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234078464 :
    ThetaLowerSegment 234078464 234111232 (23405263477061 / 100000) (11704257260033 / 50000) := by
  exact
    packedTile16384 234078464 234111232 12 1687 15299 28 _ _ (385423 / 20000) (963559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234111232 :
    ThetaLowerSegment 234111232 234144000 (11704257260033 / 50000) (23411781003721 / 100000) := by
  exact
    packedTile16384 234111232 234144000 12 1695 15300 28 _ _ (1927129 / 100000) (481783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234144000 :
    ThetaLowerSegment 234144000 234176768 (23411781003721 / 100000) (11707535318411 / 50000) := by
  exact
    packedTile16384 234144000 234176768 12 1707 15301 28 _ _ (1927143 / 100000) (963573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234176768 :
    ThetaLowerSegment 234176768 234209536 (11707535318411 / 50000) (23418418108531 / 100000) := by
  exact
    packedTile16384 234176768 234209536 12 1737 15302 28 _ _ (1927157 / 100000) (48179 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234209536 :
    ThetaLowerSegment 234209536 234242304 (23418418108531 / 100000) (731928609316 / 3125) := by
  exact
    packedTile16384 234209536 234242304 12 1711 15303 28 _ _ (1927171 / 100000) (963587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234242304 :
    ThetaLowerSegment 234242304 234275072 (731928609316 / 3125) (23424962804837 / 100000) := by
  exact
    packedTile16384 234242304 234275072 12 1685 15304 28 _ _ (385437 / 20000) (481797 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234275072 :
    ThetaLowerSegment 234275072 234307840 (23424962804837 / 100000) (23428173518371 / 100000) := by
  exact
    packedTile16384 234275072 234307840 12 1666 15306 28 _ _ (1927199 / 100000) (963601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234307840 :
    ThetaLowerSegment 234307840 234340608 (23428173518371 / 100000) (23431449780471 / 100000) := by
  exact
    packedTile16384 234307840 234340608 12 1700 15307 28 _ _ (1927213 / 100000) (120451 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234340608 :
    ThetaLowerSegment 234340608 234373376 (23431449780471 / 100000) (11717329306713 / 50000) := by
  exact
    packedTile16384 234340608 234373376 12 1665 15308 28 _ _ (1927227 / 100000) (192723 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234373376 :
    ThetaLowerSegment 234373376 234406144 (11717329306713 / 50000) (11718982879491 / 50000) := by
  exact
    packedTile16384 234373376 234406144 12 1716 15309 28 _ _ (1927241 / 100000) (481811 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234406144 :
    ThetaLowerSegment 234406144 234438912 (11718982879491 / 50000) (23441274855817 / 100000) := by
  exact
    packedTile16384 234406144 234438912 12 1717 15310 28 _ _ (385451 / 20000) (963629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234438912 :
    ThetaLowerSegment 234438912 234471680 (23441274855817 / 100000) (732640719731 / 3125) := by
  exact
    packedTile16384 234438912 234471680 12 1675 15311 28 _ _ (1927269 / 100000) (240909 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234471680 :
    ThetaLowerSegment 234471680 234504448 (732640719731 / 3125) (23447792903473 / 100000) := by
  exact
    packedTile16384 234471680 234504448 12 1707 15312 28 _ _ (1927283 / 100000) (963643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234504448 :
    ThetaLowerSegment 234504448 234537216 (23447792903473 / 100000) (23451038471621 / 100000) := by
  exact
    packedTile16384 234504448 234537216 12 1684 15313 28 _ _ (1927297 / 100000) (19273 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234537216 :
    ThetaLowerSegment 234537216 234569984 (23451038471621 / 100000) (4690864521913 / 20000) := by
  exact
    packedTile16384 234537216 234569984 12 1704 15314 28 _ _ (1927311 / 100000) (963657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234569984 :
    ThetaLowerSegment 234569984 234602752 (4690864521913 / 20000) (1172882940457 / 5000) := by
  exact
    packedTile16384 234569984 234602752 12 1731 15315 28 _ _ (77093 / 4000) (60229 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234602752 :
    ThetaLowerSegment 234602752 234635520 (1172882940457 / 5000) (11730469570059 / 50000) := by
  exact
    packedTile16384 234602752 234635520 12 1702 15316 28 _ _ (1927339 / 100000) (963671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234635520 :
    ThetaLowerSegment 234635520 234668288 (11730469570059 / 50000) (2346414625551 / 10000) := by
  exact
    packedTile16384 234635520 234668288 12 1664 15317 28 _ _ (1927353 / 100000) (481839 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234668288 :
    ThetaLowerSegment 234668288 234701056 (2346414625551 / 10000) (23467497946723 / 100000) := by
  exact
    packedTile16384 234668288 234701056 12 1739 15318 28 _ _ (1927367 / 100000) (192737 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234701056 :
    ThetaLowerSegment 234701056 234733824 (23467497946723 / 100000) (23470824606329 / 100000) := by
  exact
    packedTile16384 234701056 234733824 12 1726 15319 28 _ _ (1927381 / 100000) (240923 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234733824 :
    ThetaLowerSegment 234733824 234766592 (23470824606329 / 100000) (11737068899167 / 50000) := by
  exact
    packedTile16384 234733824 234766592 12 1719 15321 28 _ _ (385479 / 20000) (963699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234766592 :
    ThetaLowerSegment 234766592 234799360 (11737068899167 / 50000) (23477416321043 / 100000) := by
  exact
    packedTile16384 234766592 234799360 12 1701 15322 28 _ _ (1927409 / 100000) (481853 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234799360 :
    ThetaLowerSegment 234799360 234832128 (23477416321043 / 100000) (23480750762833 / 100000) := by
  exact
    packedTile16384 234799360 234832128 12 1730 15323 28 _ _ (1927423 / 100000) (963713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234832128 :
    ThetaLowerSegment 234832128 234864896 (23480750762833 / 100000) (23484181600693 / 100000) := by
  exact
    packedTile16384 234832128 234864896 12 1780 15324 28 _ _ (1927437 / 100000) (24093 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234864896 :
    ThetaLowerSegment 234864896 234897664 (23484181600693 / 100000) (23487388879157 / 100000) := by
  exact
    packedTile16384 234864896 234897664 12 1664 15325 28 _ _ (1927451 / 100000) (963727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234897664 :
    ThetaLowerSegment 234897664 234930432 (23487388879157 / 100000) (5872660128153 / 25000) := by
  exact
    packedTile16384 234897664 234930432 12 1687 15326 28 _ _ (385493 / 20000) (481867 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234930432 :
    ThetaLowerSegment 234930432 234963200 (5872660128153 / 25000) (11746957648867 / 50000) := by
  exact
    packedTile16384 234930432 234963200 12 1699 15327 28 _ _ (963739 / 50000) (1927481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234963200 :
    ThetaLowerSegment 234963200 234995968 (11746957648867 / 50000) (11748620110717 / 50000) := by
  exact
    packedTile16384 234963200 234995968 12 1725 15328 28 _ _ (481873 / 25000) (385499 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell234995968 :
    ThetaLowerSegment 234995968 235028736 (11748620110717 / 50000) (2937555707989 / 12500) := by
  exact
    packedTile16384 234995968 235028736 12 1663 15329 28 _ _ (963753 / 50000) (1927509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235028736 :
    ThetaLowerSegment 235028736 235061504 (2937555707989 / 12500) (2937973738889 / 12500) := by
  exact
    packedTile16384 235028736 235061504 12 1735 15330 28 _ _ (12047 / 625) (1927523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235061504 :
    ThetaLowerSegment 235061504 235094272 (2937973738889 / 12500) (1175355456233 / 5000) := by
  exact
    packedTile16384 235061504 235094272 12 1722 15331 28 _ _ (963767 / 50000) (1927537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235094272 :
    ThetaLowerSegment 235094272 235127040 (1175355456233 / 5000) (2938796076041 / 12500) := by
  exact
    packedTile16384 235094272 235127040 12 1691 15332 28 _ _ (481887 / 25000) (1927551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235127040 :
    ThetaLowerSegment 235127040 235159808 (2938796076041 / 12500) (5878400764341 / 25000) := by
  exact
    packedTile16384 235127040 235159808 12 1678 15333 28 _ _ (963781 / 50000) (385513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235159808 :
    ThetaLowerSegment 235159808 235192576 (5878400764341 / 25000) (1175840719949 / 5000) := by
  exact
    packedTile16384 235159808 235192576 12 1666 15334 28 _ _ (240947 / 12500) (1927579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235192576 :
    ThetaLowerSegment 235192576 235225344 (1175840719949 / 5000) (2352013949173 / 10000) := by
  exact
    packedTile16384 235192576 235225344 12 1725 15335 28 _ _ (192759 / 10000) (1927593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235225344 :
    ThetaLowerSegment 235225344 235258112 (2352013949173 / 10000) (11761724593899 / 50000) := by
  exact
    packedTile16384 235225344 235258112 12 1717 15337 28 _ _ (481901 / 25000) (1927607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235258112 :
    ThetaLowerSegment 235258112 235290880 (11761724593899 / 50000) (2352681095359 / 10000) := by
  exact
    packedTile16384 235258112 235290880 12 1744 15338 28 _ _ (963809 / 50000) (1927621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235290880 :
    ThetaLowerSegment 235290880 235323648 (2352681095359 / 10000) (11765071914659 / 50000) := by
  exact
    packedTile16384 235290880 235323648 12 1729 15339 28 _ _ (120477 / 6250) (385527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235323648 :
    ThetaLowerSegment 235323648 235356416 (11765071914659 / 50000) (11766716196697 / 50000) := by
  exact
    packedTile16384 235323648 235356416 12 1706 15340 28 _ _ (963823 / 50000) (1927649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235356416 :
    ThetaLowerSegment 235356416 235389184 (11766716196697 / 50000) (11768360490677 / 50000) := by
  exact
    packedTile16384 235356416 235389184 12 1706 15341 28 _ _ (96383 / 5000) (1927663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235389184 :
    ThetaLowerSegment 235389184 235421952 (11768360490677 / 50000) (11769975881489 / 50000) := by
  exact
    packedTile16384 235389184 235421952 12 1676 15342 28 _ _ (963837 / 50000) (1927677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235421952 :
    ThetaLowerSegment 235421952 235454720 (11769975881489 / 50000) (11771619235509 / 50000) := by
  exact
    packedTile16384 235421952 235454720 12 1705 15343 28 _ _ (240961 / 12500) (1927691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235454720 :
    ThetaLowerSegment 235454720 235487488 (11771619235509 / 50000) (23546552189037 / 100000) := by
  exact
    packedTile16384 235454720 235487488 12 1719 15344 28 _ _ (1927701 / 100000) (240963 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235487488 :
    ThetaLowerSegment 235487488 235520256 (23546552189037 / 100000) (11774898266691 / 50000) := by
  exact
    packedTile16384 235487488 235520256 12 1683 15345 28 _ _ (385543 / 20000) (963859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235520256 :
    ThetaLowerSegment 235520256 235553024 (11774898266691 / 50000) (11776583101837 / 50000) := by
  exact
    packedTile16384 235520256 235553024 12 1748 15346 28 _ _ (1927729 / 100000) (481933 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235553024 :
    ThetaLowerSegment 235553024 235585792 (11776583101837 / 50000) (11778202405957 / 50000) := by
  exact
    packedTile16384 235553024 235585792 12 1680 15347 28 _ _ (1927743 / 100000) (963873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235585792 :
    ThetaLowerSegment 235585792 235618560 (11778202405957 / 50000) (588992917461 / 2500) := by
  exact
    packedTile16384 235585792 235618560 12 1718 15348 28 _ _ (1927757 / 100000) (24097 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235618560 :
    ThetaLowerSegment 235618560 235651328 (588992917461 / 2500) (4712585287431 / 20000) := by
  exact
    packedTile16384 235618560 235651328 12 1665 15349 28 _ _ (1927771 / 100000) (963887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235651328 :
    ThetaLowerSegment 235651328 235684096 (4712585287431 / 20000) (4713224540937 / 20000) := by
  exact
    packedTile16384 235651328 235684096 12 1658 15350 28 _ _ (385557 / 20000) (481947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235684096 :
    ThetaLowerSegment 235684096 235716864 (4713224540937 / 20000) (23569372973799 / 100000) := by
  exact
    packedTile16384 235684096 235716864 12 1686 15352 28 _ _ (1927799 / 100000) (963901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235716864 :
    ThetaLowerSegment 235716864 235749632 (23569372973799 / 100000) (2357258663807 / 10000) := by
  exact
    packedTile16384 235716864 235749632 12 1667 15353 28 _ _ (1927813 / 100000) (240977 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235749632 :
    ThetaLowerSegment 235749632 235782400 (2357258663807 / 10000) (23575939129223 / 100000) := by
  exact
    packedTile16384 235749632 235782400 12 1739 15354 28 _ _ (1927827 / 100000) (192783 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235782400 :
    ThetaLowerSegment 235782400 235815168 (23575939129223 / 100000) (23579098858983 / 100000) := by
  exact
    packedTile16384 235782400 235815168 12 1639 15355 28 _ _ (12049 / 625) (1927843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235815168 :
    ThetaLowerSegment 235815168 235847936 (23579098858983 / 100000) (23582416695717 / 100000) := by
  exact
    packedTile16384 235815168 235847936 12 1721 15356 28 _ _ (963927 / 50000) (1927857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235847936 :
    ThetaLowerSegment 235847936 235880704 (23582416695717 / 100000) (943428225541 / 4000) := by
  exact
    packedTile16384 235847936 235880704 12 1706 15357 28 _ _ (481967 / 25000) (1927871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235880704 :
    ThetaLowerSegment 235880704 235913472 (943428225541 / 4000) (23588942552403 / 100000) := by
  exact
    packedTile16384 235880704 235913472 12 1679 15358 28 _ _ (963941 / 50000) (385577 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235913472 :
    ThetaLowerSegment 235913472 235946240 (23588942552403 / 100000) (23592260461419 / 100000) := by
  exact
    packedTile16384 235913472 235946240 12 1721 15359 28 _ _ (240987 / 12500) (1927899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235946240 :
    ThetaLowerSegment 235946240 235979008 (23592260461419 / 100000) (23595541764239 / 100000) := by
  exact
    packedTile16384 235946240 235979008 12 1702 15360 28 _ _ (192791 / 10000) (1927913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell235979008 :
    ThetaLowerSegment 235979008 236011776 (23595541764239 / 100000) (23598852009747 / 100000) := by
  exact
    packedTile16384 235979008 236011776 12 1717 15361 28 _ _ (481981 / 25000) (1927927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236011776 :
    ThetaLowerSegment 236011776 236044544 (23598852009747 / 100000) (23602123720533 / 100000) := by
  exact
    packedTile16384 236011776 236044544 12 1697 15362 28 _ _ (963969 / 50000) (1927941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236044544 :
    ThetaLowerSegment 236044544 236077312 (23602123720533 / 100000) (4721084489281 / 20000) := by
  exact
    packedTile16384 236044544 236077312 12 1711 15363 28 _ _ (120497 / 6250) (385591 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236077312 :
    ThetaLowerSegment 236077312 236110080 (4721084489281 / 20000) (188868952099 / 800) := by
  exact
    packedTile16384 236077312 236110080 12 1658 15364 28 _ _ (385593 / 20000) (60249 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236110080 :
    ThetaLowerSegment 236110080 236142848 (188868952099 / 800) (5902987158027 / 25000) := by
  exact
    packedTile16384 236110080 236142848 12 1727 15365 28 _ _ (1927979 / 100000) (963991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236142848 :
    ThetaLowerSegment 236142848 236175616 (5902987158027 / 25000) (23615270564047 / 100000) := by
  exact
    packedTile16384 236142848 236175616 12 1723 15366 28 _ _ (1927993 / 100000) (481999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236175616 :
    ThetaLowerSegment 236175616 236208384 (23615270564047 / 100000) (5904663554083 / 25000) := by
  exact
    packedTile16384 236175616 236208384 12 1755 15368 28 _ _ (1928007 / 100000) (192801 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236208384 :
    ThetaLowerSegment 236208384 236241152 (5904663554083 / 25000) (23621960772347 / 100000) := by
  exact
    packedTile16384 236208384 236241152 12 1715 15369 28 _ _ (1928021 / 100000) (241003 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236241152 :
    ThetaLowerSegment 236241152 236273920 (23621960772347 / 100000) (23625196015077 / 100000) := by
  exact
    packedTile16384 236241152 236273920 12 1678 15370 28 _ _ (385607 / 20000) (964019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236273920 :
    ThetaLowerSegment 236273920 236306688 (23625196015077 / 100000) (23628485266671 / 100000) := by
  exact
    packedTile16384 236273920 236306688 12 1706 15371 28 _ _ (1928049 / 100000) (482013 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236306688 :
    ThetaLowerSegment 236306688 236339456 (23628485266671 / 100000) (23631755261519 / 100000) := by
  exact
    packedTile16384 236306688 236339456 12 1696 15372 28 _ _ (1928063 / 100000) (964033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236339456 :
    ThetaLowerSegment 236339456 236372224 (23631755261519 / 100000) (4727005055683 / 20000) := by
  exact
    packedTile16384 236339456 236372224 12 1696 15373 28 _ _ (482019 / 25000) (1928079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236372224 :
    ThetaLowerSegment 236372224 236404992 (4727005055683 / 20000) (4727649808979 / 20000) := by
  exact
    packedTile16384 236372224 236404992 12 1672 15374 28 _ _ (192809 / 10000) (1928093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236404992 :
    ThetaLowerSegment 236404992 236437760 (4727649808979 / 20000) (4728299580027 / 20000) := by
  exact
    packedTile16384 236404992 236437760 12 1685 15375 28 _ _ (241013 / 12500) (1928107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236437760 :
    ThetaLowerSegment 236437760 236470528 (4728299580027 / 20000) (23644771844499 / 100000) := by
  exact
    packedTile16384 236437760 236470528 12 1698 15376 28 _ _ (964059 / 50000) (1928121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236470528 :
    ThetaLowerSegment 236470528 236503296 (23644771844499 / 100000) (4729595665603 / 20000) := by
  exact
    packedTile16384 236470528 236503296 12 1663 15377 28 _ _ (482033 / 25000) (385627 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236503296 :
    ThetaLowerSegment 236503296 236536064 (4729595665603 / 20000) (23651267745091 / 100000) := by
  exact
    packedTile16384 236503296 236536064 12 1706 15378 28 _ _ (964073 / 50000) (1928149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236536064 :
    ThetaLowerSegment 236536064 236568832 (23651267745091 / 100000) (23654611174531 / 100000) := by
  exact
    packedTile16384 236536064 236568832 12 1734 15379 28 _ _ (12051 / 625) (1928163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236568832 :
    ThetaLowerSegment 236568832 236601600 (23654611174531 / 100000) (23657881355939 / 100000) := by
  exact
    packedTile16384 236568832 236601600 12 1696 15380 28 _ _ (1928173 / 100000) (120511 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236601600 :
    ThetaLowerSegment 236601600 236634368 (23657881355939 / 100000) (23661205550327 / 100000) := by
  exact
    packedTile16384 236601600 236634368 12 1724 15381 28 _ _ (1928187 / 100000) (192819 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236634368 :
    ThetaLowerSegment 236634368 236667136 (23661205550327 / 100000) (5916125211459 / 25000) := by
  exact
    packedTile16384 236634368 236667136 12 1709 15382 28 _ _ (1928201 / 100000) (482051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236667136 :
    ThetaLowerSegment 236667136 236699904 (5916125211459 / 25000) (23667680472371 / 100000) := by
  exact
    packedTile16384 236667136 236699904 12 1649 15383 28 _ _ (385643 / 20000) (964109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236699904 :
    ThetaLowerSegment 236699904 236732672 (23667680472371 / 100000) (4734190149751 / 20000) := by
  exact
    packedTile16384 236699904 236732672 12 1696 15385 28 _ _ (1928229 / 100000) (241029 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236732672 :
    ThetaLowerSegment 236732672 236765440 (4734190149751 / 20000) (4734845752371 / 20000) := by
  exact
    packedTile16384 236732672 236765440 12 1700 15386 28 _ _ (1928243 / 100000) (964123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236765440 :
    ThetaLowerSegment 236765440 236798208 (4734845752371 / 20000) (23677549220409 / 100000) := by
  exact
    packedTile16384 236765440 236798208 12 1722 15387 28 _ _ (1928257 / 100000) (96413 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236798208 :
    ThetaLowerSegment 236798208 236830976 (23677549220409 / 100000) (23680858131729 / 100000) := by
  exact
    packedTile16384 236798208 236830976 12 1716 15388 28 _ _ (192827 / 10000) (1928273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236830976 :
    ThetaLowerSegment 236830976 236863744 (23680858131729 / 100000) (947364985793 / 4000) := by
  exact
    packedTile16384 236830976 236863744 12 1694 15389 28 _ _ (482071 / 25000) (1928287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236863744 :
    ThetaLowerSegment 236863744 236896512 (947364985793 / 4000) (23687443245683 / 100000) := by
  exact
    packedTile16384 236863744 236896512 12 1721 15390 28 _ _ (964149 / 50000) (1928301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236896512 :
    ThetaLowerSegment 236896512 236929280 (23687443245683 / 100000) (23690721376083 / 100000) := by
  exact
    packedTile16384 236896512 236929280 12 1700 15391 28 _ _ (241039 / 12500) (385663 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236929280 :
    ThetaLowerSegment 236929280 236962048 (23690721376083 / 100000) (23694117158169 / 100000) := by
  exact
    packedTile16384 236929280 236962048 12 1761 15392 28 _ _ (964163 / 50000) (1928329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236962048 :
    ThetaLowerSegment 236962048 236994816 (23694117158169 / 100000) (23697335557629 / 100000) := by
  exact
    packedTile16384 236962048 236994816 12 1669 15393 28 _ _ (96417 / 5000) (1928343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell236994816 :
    ThetaLowerSegment 236994816 237027584 (23697335557629 / 100000) (23700652324789 / 100000) := by
  exact
    packedTile16384 236994816 237027584 12 1720 15394 28 _ _ (1928353 / 100000) (482089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237027584 :
    ThetaLowerSegment 237027584 237060352 (23700652324789 / 100000) (23703957545827 / 100000) := by
  exact
    packedTile16384 237027584 237060352 12 1714 15395 28 _ _ (1928367 / 100000) (192837 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237060352 :
    ThetaLowerSegment 237060352 237093120 (23703957545827 / 100000) (4741434817067 / 20000) := by
  exact
    packedTile16384 237060352 237093120 12 1668 15396 28 _ _ (1928381 / 100000) (60262 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237093120 :
    ThetaLowerSegment 237093120 237125888 (4741434817067 / 20000) (4742085071861 / 20000) := by
  exact
    packedTile16384 237093120 237125888 12 1686 15397 28 _ _ (385679 / 20000) (964199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237125888 :
    ThetaLowerSegment 237125888 237158656 (4742085071861 / 20000) (23713796218237 / 100000) := by
  exact
    packedTile16384 237125888 237158656 12 1748 15398 28 _ _ (1928409 / 100000) (482103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237158656 :
    ThetaLowerSegment 237158656 237191424 (23713796218237 / 100000) (23717037895619 / 100000) := by
  exact
    packedTile16384 237158656 237191424 12 1681 15399 28 _ _ (964211 / 50000) (77137 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237191424 :
    ThetaLowerSegment 237191424 237224192 (23717037895619 / 100000) (23720352877103 / 100000) := by
  exact
    packedTile16384 237191424 237224192 12 1719 15401 28 _ _ (482109 / 25000) (1928439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237224192 :
    ThetaLowerSegment 237224192 237256960 (23720352877103 / 100000) (23723679453353 / 100000) := by
  exact
    packedTile16384 237224192 237256960 12 1725 15402 28 _ _ (38569 / 2000) (1928453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237256960 :
    ThetaLowerSegment 237256960 237289728 (23723679453353 / 100000) (23726903845161 / 100000) := by
  exact
    packedTile16384 237256960 237289728 12 1672 15403 28 _ _ (120529 / 6250) (1928467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237289728 :
    ThetaLowerSegment 237289728 237322496 (23726903845161 / 100000) (23730191900151 / 100000) := by
  exact
    packedTile16384 237289728 237322496 12 1705 15404 28 _ _ (964239 / 50000) (1928481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237322496 :
    ThetaLowerSegment 237322496 237355264 (23730191900151 / 100000) (23733485764487 / 100000) := by
  exact
    packedTile16384 237322496 237355264 12 1708 15405 28 _ _ (482123 / 25000) (385699 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237355264 :
    ThetaLowerSegment 237355264 237388032 (23733485764487 / 100000) (23736714081857 / 100000) := by
  exact
    packedTile16384 237355264 237388032 12 1674 15406 28 _ _ (385701 / 20000) (482127 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237388032 :
    ThetaLowerSegment 237388032 237420800 (23736714081857 / 100000) (1483752066441 / 6250) := by
  exact
    packedTile16384 237388032 237420800 12 1721 15407 28 _ _ (1928519 / 100000) (964261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237420800 :
    ThetaLowerSegment 237420800 237453568 (1483752066441 / 6250) (741977281203 / 3125) := by
  exact
    packedTile16384 237420800 237453568 12 1680 15408 28 _ _ (1928533 / 100000) (241067 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237453568 :
    ThetaLowerSegment 237453568 237486336 (741977281203 / 3125) (23746518743097 / 100000) := by
  exact
    packedTile16384 237453568 237486336 12 1683 15409 28 _ _ (1928547 / 100000) (38571 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237486336 :
    ThetaLowerSegment 237486336 237519104 (23746518743097 / 100000) (23749859010749 / 100000) := by
  exact
    packedTile16384 237486336 237519104 12 1732 15410 28 _ _ (1928561 / 100000) (482141 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237519104 :
    ThetaLowerSegment 237519104 237551872 (23749859010749 / 100000) (23753195443769 / 100000) := by
  exact
    packedTile16384 237519104 237551872 12 1730 15411 28 _ _ (964287 / 50000) (1928577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237551872 :
    ThetaLowerSegment 237551872 237584640 (23753195443769 / 100000) (23756460543253 / 100000) := by
  exact
    packedTile16384 237551872 237584640 12 1693 15412 28 _ _ (482147 / 25000) (1928591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237584640 :
    ThetaLowerSegment 237584640 237617408 (23756460543253 / 100000) (23759841382559 / 100000) := by
  exact
    packedTile16384 237584640 237617408 12 1753 15413 28 _ _ (964301 / 50000) (385721 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237617408 :
    ThetaLowerSegment 237617408 237650176 (23759841382559 / 100000) (23763158602079 / 100000) := by
  exact
    packedTile16384 237617408 237650176 12 1720 15414 28 _ _ (241077 / 12500) (1928619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237650176 :
    ThetaLowerSegment 237650176 237682944 (23763158602079 / 100000) (23766367842399 / 100000) := by
  exact
    packedTile16384 237650176 237682944 12 1664 15415 28 _ _ (192863 / 10000) (1928633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237682944 :
    ThetaLowerSegment 237682944 237715712 (23766367842399 / 100000) (11884835803929 / 50000) := by
  exact
    packedTile16384 237682944 237715712 12 1713 15416 28 _ _ (1928643 / 100000) (964323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237715712 :
    ThetaLowerSegment 237715712 237748480 (11884835803929 / 50000) (23772921394903 / 100000) := by
  exact
    packedTile16384 237715712 237748480 12 1685 15418 28 _ _ (1928657 / 100000) (96433 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237748480 :
    ThetaLowerSegment 237748480 237781248 (23772921394903 / 100000) (11888062458717 / 50000) := by
  exact
    packedTile16384 237748480 237781248 12 1661 15419 28 _ _ (1928671 / 100000) (964337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237781248 :
    ThetaLowerSegment 237781248 237814016 (11888062458717 / 50000) (23779363179549 / 100000) := by
  exact
    packedTile16384 237781248 237814016 12 1679 15420 28 _ _ (385737 / 20000) (120543 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237814016 :
    ThetaLowerSegment 237814016 237846784 (23779363179549 / 100000) (23782697898391 / 100000) := by
  exact
    packedTile16384 237814016 237846784 12 1729 15421 28 _ _ (964349 / 50000) (1928701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237846784 :
    ThetaLowerSegment 237846784 237879552 (23782697898391 / 100000) (23786024926591 / 100000) := by
  exact
    packedTile16384 237846784 237879552 12 1725 15422 28 _ _ (241089 / 12500) (385743 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237879552 :
    ThetaLowerSegment 237879552 237912320 (23786024926591 / 100000) (23789309546969 / 100000) := by
  exact
    packedTile16384 237879552 237912320 12 1703 15423 28 _ _ (964363 / 50000) (1928729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237912320 :
    ThetaLowerSegment 237912320 237945088 (23789309546969 / 100000) (23792590333709 / 100000) := by
  exact
    packedTile16384 237912320 237945088 12 1701 15424 28 _ _ (96437 / 5000) (1928743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237945088 :
    ThetaLowerSegment 237945088 237977856 (23792590333709 / 100000) (23795927078129 / 100000) := by
  exact
    packedTile16384 237945088 237977856 12 1730 15425 28 _ _ (964377 / 50000) (1928757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell237977856 :
    ThetaLowerSegment 237977856 238010624 (23795927078129 / 100000) (2379925034367 / 10000) := by
  exact
    packedTile16384 237977856 238010624 12 1723 15426 28 _ _ (1928767 / 100000) (192877 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238010624 :
    ThetaLowerSegment 238010624 238043392 (2379925034367 / 10000) (23802523485027 / 100000) := by
  exact
    packedTile16384 238010624 238043392 12 1697 15427 28 _ _ (1928781 / 100000) (120549 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238043392 :
    ThetaLowerSegment 238043392 238076160 (23802523485027 / 100000) (5951465557293 / 25000) := by
  exact
    packedTile16384 238043392 238076160 12 1731 15428 28 _ _ (385759 / 20000) (964399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238076160 :
    ThetaLowerSegment 238076160 238108928 (5951465557293 / 25000) (11904568673427 / 50000) := by
  exact
    packedTile16384 238076160 238108928 12 1698 15429 28 _ _ (1928809 / 100000) (482203 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238108928 :
    ThetaLowerSegment 238108928 238141696 (11904568673427 / 50000) (11906192741551 / 50000) := by
  exact
    packedTile16384 238108928 238141696 12 1684 15430 28 _ _ (964411 / 50000) (77153 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238141696 :
    ThetaLowerSegment 238141696 238174464 (11906192741551 / 50000) (11907856362601 / 50000) := by
  exact
    packedTile16384 238141696 238174464 12 1725 15431 28 _ _ (482209 / 25000) (1928839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238174464 :
    ThetaLowerSegment 238174464 238207232 (11907856362601 / 50000) (744344155861 / 3125) := by
  exact
    packedTile16384 238174464 238207232 12 1711 15432 28 _ _ (38577 / 2000) (1928853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238207232 :
    ThetaLowerSegment 238207232 238240000 (744344155861 / 3125) (744446023991 / 3125) := by
  exact
    packedTile16384 238207232 238240000 12 1690 15433 28 _ _ (60277 / 3125) (1928867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238240000 :
    ThetaLowerSegment 238240000 238272768 (744446023991 / 3125) (23825553787489 / 100000) := by
  exact
    packedTile16384 238240000 238272768 12 1701 15435 28 _ _ (1928877 / 100000) (24111 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238272768 :
    ThetaLowerSegment 238272768 238305536 (23825553787489 / 100000) (23828856048881 / 100000) := by
  exact
    packedTile16384 238272768 238305536 12 1712 15436 28 _ _ (1928891 / 100000) (964447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238305536 :
    ThetaLowerSegment 238305536 238338304 (23828856048881 / 100000) (23832173765481 / 100000) := by
  exact
    packedTile16384 238305536 238338304 12 1720 15437 28 _ _ (385781 / 20000) (482227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238338304 :
    ThetaLowerSegment 238338304 238371072 (23832173765481 / 100000) (5958859856337 / 25000) := by
  exact
    packedTile16384 238338304 238371072 12 1693 15438 28 _ _ (1928919 / 100000) (964461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238371072 :
    ThetaLowerSegment 238371072 238403840 (5958859856337 / 25000) (1191935544701 / 5000) := by
  exact
    packedTile16384 238371072 238403840 12 1696 15439 28 _ _ (482233 / 25000) (385787 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238403840 :
    ThetaLowerSegment 238403840 238436608 (1191935544701 / 5000) (1192099505111 / 5000) := by
  exact
    packedTile16384 238403840 238436608 12 1700 15440 28 _ _ (964473 / 50000) (1928949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238436608 :
    ThetaLowerSegment 238436608 238469376 (1192099505111 / 5000) (238452172523 / 1000) := by
  exact
    packedTile16384 238436608 238469376 12 1673 15441 28 _ _ (12056 / 625) (1928963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238469376 :
    ThetaLowerSegment 238469376 238502144 (238452172523 / 1000) (11924255005459 / 50000) := by
  exact
    packedTile16384 238469376 238502144 12 1707 15442 28 _ _ (964487 / 50000) (1928977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238502144 :
    ThetaLowerSegment 238502144 238534912 (11924255005459 / 50000) (23851725632247 / 100000) := by
  exact
    packedTile16384 238502144 238534912 12 1667 15443 28 _ _ (1928987 / 100000) (192899 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238534912 :
    ThetaLowerSegment 238534912 238567680 (23851725632247 / 100000) (23855107171 / 100) := by
  exact
    packedTile16384 238534912 238567680 12 1753 15444 28 _ _ (1929001 / 100000) (482251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238567680 :
    ThetaLowerSegment 238567680 238600448 (23855107171 / 100) (954332759239 / 4000) := by
  exact
    packedTile16384 238567680 238600448 12 1665 15445 28 _ _ (385803 / 20000) (964509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238600448 :
    ThetaLowerSegment 238600448 238633216 (954332759239 / 4000) (23861602188333 / 100000) := by
  exact
    packedTile16384 238600448 238633216 12 1702 15446 28 _ _ (1929029 / 100000) (241129 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238633216 :
    ThetaLowerSegment 238633216 238665984 (23861602188333 / 100000) (23864929785783 / 100000) := by
  exact
    packedTile16384 238633216 238665984 12 1725 15447 28 _ _ (964521 / 50000) (385809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238665984 :
    ThetaLowerSegment 238665984 238698752 (23864929785783 / 100000) (23868240045879 / 100000) := by
  exact
    packedTile16384 238665984 238698752 12 1716 15448 28 _ _ (60283 / 3125) (1929059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238698752 :
    ThetaLowerSegment 238698752 238731520 (23868240045879 / 100000) (23871558046279 / 100000) := by
  exact
    packedTile16384 238698752 238731520 12 1720 15449 28 _ _ (192907 / 10000) (1929073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238731520 :
    ThetaLowerSegment 238731520 238764288 (23871558046279 / 100000) (23874769971139 / 100000) := by
  exact
    packedTile16384 238731520 238764288 12 1665 15450 28 _ _ (482271 / 25000) (1929087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238764288 :
    ThetaLowerSegment 238764288 238797056 (23874769971139 / 100000) (23878080301591 / 100000) := by
  exact
    packedTile16384 238764288 238797056 12 1716 15451 28 _ _ (1929097 / 100000) (19291 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238797056 :
    ThetaLowerSegment 238797056 238829824 (23878080301591 / 100000) (746294121134 / 3125) := by
  exact
    packedTile16384 238797056 238829824 12 1727 15453 28 _ _ (1929111 / 100000) (964557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238829824 :
    ThetaLowerSegment 238829824 238862592 (746294121134 / 3125) (11942328332269 / 50000) := by
  exact
    packedTile16384 238829824 238862592 12 1682 15454 28 _ _ (15433 / 800) (241141 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238862592 :
    ThetaLowerSegment 238862592 238895360 (11942328332269 / 50000) (11943939162499 / 50000) := by
  exact
    packedTile16384 238862592 238895360 12 1670 15455 28 _ _ (964569 / 50000) (1929141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238895360 :
    ThetaLowerSegment 238895360 238928128 (11943939162499 / 50000) (11945554827299 / 50000) := by
  exact
    packedTile16384 238895360 238928128 12 1675 15456 28 _ _ (60286 / 3125) (385831 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238928128 :
    ThetaLowerSegment 238928128 238960896 (11945554827299 / 50000) (5973601649823 / 25000) := by
  exact
    packedTile16384 238928128 238960896 12 1709 15457 28 _ _ (964583 / 50000) (1929169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238960896 :
    ThetaLowerSegment 238960896 238993664 (5973601649823 / 25000) (1493609125617 / 6250) := by
  exact
    packedTile16384 238960896 238993664 12 1731 15458 28 _ _ (96459 / 5000) (1929183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell238993664 :
    ThetaLowerSegment 238993664 239026432 (1493609125617 / 6250) (11950445297231 / 50000) := by
  exact
    packedTile16384 238993664 239026432 12 1630 15459 28 _ _ (1929193 / 100000) (482299 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239026432 :
    ThetaLowerSegment 239026432 239059200 (11950445297231 / 50000) (11952077406353 / 50000) := by
  exact
    packedTile16384 239026432 239059200 12 1692 15460 28 _ _ (1929207 / 100000) (192921 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239059200 :
    ThetaLowerSegment 239059200 239091968 (11952077406353 / 50000) (23907409408533 / 100000) := by
  exact
    packedTile16384 239059200 239091968 12 1687 15461 28 _ _ (1929221 / 100000) (241153 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239091968 :
    ThetaLowerSegment 239091968 239124736 (23907409408533 / 100000) (23910638946249 / 100000) := by
  exact
    packedTile16384 239091968 239124736 12 1674 15462 28 _ _ (964617 / 50000) (1929237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239124736 :
    ThetaLowerSegment 239124736 239157504 (23910638946249 / 100000) (23913901304617 / 100000) := by
  exact
    packedTile16384 239124736 239157504 12 1691 15463 28 _ _ (60289 / 3125) (1929251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239157504 :
    ThetaLowerSegment 239157504 239190272 (23913901304617 / 100000) (191337587307 / 800) := by
  exact
    packedTile16384 239157504 239190272 12 1709 15464 28 _ _ (964631 / 50000) (385853 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239190272 :
    ThetaLowerSegment 239190272 239223040 (191337587307 / 800) (956821288023 / 4000) := by
  exact
    packedTile16384 239190272 239223040 12 1728 15465 28 _ _ (77171 / 4000) (964639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239223040 :
    ThetaLowerSegment 239223040 239255808 (956821288023 / 4000) (23923742537471 / 100000) := by
  exact
    packedTile16384 239223040 239255808 12 1664 15466 28 _ _ (1929289 / 100000) (482323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239255808 :
    ThetaLowerSegment 239255808 239288576 (23923742537471 / 100000) (4785407557399 / 20000) := by
  exact
    packedTile16384 239255808 239288576 12 1708 15467 28 _ _ (1929303 / 100000) (964653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239288576 :
    ThetaLowerSegment 239288576 239321344 (4785407557399 / 20000) (23930290615457 / 100000) := by
  exact
    packedTile16384 239288576 239321344 12 1686 15468 28 _ _ (1929317 / 100000) (48233 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239321344 :
    ThetaLowerSegment 239321344 239354112 (23930290615457 / 100000) (23933518384547 / 100000) := by
  exact
    packedTile16384 239321344 239354112 12 1673 15470 28 _ _ (192933 / 10000) (1929333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239354112 :
    ThetaLowerSegment 239354112 239386880 (23933518384547 / 100000) (23936726883619 / 100000) := by
  exact
    packedTile16384 239354112 239386880 12 1663 15471 28 _ _ (60292 / 3125) (1929347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239386880 :
    ThetaLowerSegment 239386880 239419648 (23936726883619 / 100000) (23940026085799 / 100000) := by
  exact
    packedTile16384 239386880 239419648 12 1710 15472 28 _ _ (964679 / 50000) (1929361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239419648 :
    ThetaLowerSegment 239419648 239452416 (23940026085799 / 100000) (23943365827 / 100) := by
  exact
    packedTile16384 239419648 239452416 12 1731 15473 28 _ _ (1929371 / 100000) (964687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239452416 :
    ThetaLowerSegment 239452416 239485184 (23943365827 / 100) (47893291563 / 200) := by
  exact
    packedTile16384 239452416 239485184 12 1700 15474 28 _ _ (385877 / 20000) (482347 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239485184 :
    ThetaLowerSegment 239485184 239517952 (47893291563 / 200) (1197502076187 / 5000) := by
  exact
    packedTile16384 239485184 239517952 12 1760 15475 28 _ _ (1929399 / 100000) (964701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239517952 :
    ThetaLowerSegment 239517952 239550720 (1197502076187 / 5000) (5988318804563 / 25000) := by
  exact
    packedTile16384 239517952 239550720 12 1676 15476 28 _ _ (482353 / 25000) (385883 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239550720 :
    ThetaLowerSegment 239550720 239583488 (5988318804563 / 25000) (11978259291679 / 50000) := by
  exact
    packedTile16384 239550720 239583488 12 1681 15477 28 _ _ (964713 / 50000) (1929429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239583488 :
    ThetaLowerSegment 239583488 239616256 (11978259291679 / 50000) (11979893527359 / 50000) := by
  exact
    packedTile16384 239583488 239616256 12 1694 15478 28 _ _ (12059 / 625) (1929443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239616256 :
    ThetaLowerSegment 239616256 239649024 (11979893527359 / 50000) (23963111502237 / 100000) := by
  exact
    packedTile16384 239616256 239649024 12 1723 15479 28 _ _ (1929453 / 100000) (120591 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239649024 :
    ThetaLowerSegment 239649024 239681792 (23963111502237 / 100000) (23966372301467 / 100000) := by
  exact
    packedTile16384 239649024 239681792 12 1690 15480 28 _ _ (1929467 / 100000) (192947 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239681792 :
    ThetaLowerSegment 239681792 239714560 (23966372301467 / 100000) (4793929712041 / 20000) := by
  exact
    packedTile16384 239681792 239714560 12 1698 15481 28 _ _ (1929481 / 100000) (482371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239714560 :
    ThetaLowerSegment 239714560 239747328 (4793929712041 / 20000) (23972915193547 / 100000) := by
  exact
    packedTile16384 239714560 239747328 12 1693 15482 28 _ _ (964747 / 50000) (1929497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239747328 :
    ThetaLowerSegment 239747328 239780096 (23972915193547 / 100000) (23976131683383 / 100000) := by
  exact
    packedTile16384 239747328 239780096 12 1667 15483 28 _ _ (482377 / 25000) (1929511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239780096 :
    ThetaLowerSegment 239780096 239812864 (23976131683383 / 100000) (23979498699273 / 100000) := by
  exact
    packedTile16384 239780096 239812864 12 1745 15484 28 _ _ (964761 / 50000) (77181 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239812864 :
    ThetaLowerSegment 239812864 239845632 (23979498699273 / 100000) (23982744177143 / 100000) := by
  exact
    packedTile16384 239812864 239845632 12 1682 15485 28 _ _ (385907 / 20000) (964769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239845632 :
    ThetaLowerSegment 239845632 239878400 (23982744177143 / 100000) (2398606879007 / 10000) := by
  exact
    packedTile16384 239845632 239878400 12 1723 15486 28 _ _ (1929549 / 100000) (120597 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239878400 :
    ThetaLowerSegment 239878400 239911168 (2398606879007 / 10000) (749664866368 / 3125) := by
  exact
    packedTile16384 239878400 239911168 12 1662 15488 28 _ _ (1929563 / 100000) (964783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239911168 :
    ThetaLowerSegment 239911168 239943936 (749664866368 / 3125) (2999064917629 / 12500) := by
  exact
    packedTile16384 239911168 239943936 12 1681 15489 28 _ _ (241197 / 12500) (1929579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239943936 :
    ThetaLowerSegment 239943936 239976704 (2999064917629 / 12500) (11997931660251 / 50000) := by
  exact
    packedTile16384 239943936 239976704 12 1733 15490 28 _ _ (192959 / 10000) (1929593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell239976704 :
    ThetaLowerSegment 239976704 240009472 (11997931660251 / 50000) (479981406447 / 2000) := by
  exact
    packedTile16384 239976704 240009472 12 1662 15491 28 _ _ (482401 / 25000) (1929607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240009472 :
    ThetaLowerSegment 240009472 240042240 (479981406447 / 2000) (2400246644827 / 10000) := by
  exact
    packedTile16384 240009472 240042240 12 1760 15492 28 _ _ (1929617 / 100000) (96481 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240042240 :
    ThetaLowerSegment 240042240 240075008 (2400246644827 / 10000) (24005733313553 / 100000) := by
  exact
    packedTile16384 240042240 240075008 12 1693 15493 28 _ _ (1929631 / 100000) (964817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240075008 :
    ThetaLowerSegment 240075008 240107776 (24005733313553 / 100000) (24008982835733 / 100000) := by
  exact
    packedTile16384 240075008 240107776 12 1684 15494 28 _ _ (385929 / 20000) (120603 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240107776 :
    ThetaLowerSegment 240107776 240140544 (24008982835733 / 100000) (24012230450147 / 100000) := by
  exact
    packedTile16384 240107776 240140544 12 1683 15495 28 _ _ (964829 / 50000) (1929661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240140544 :
    ThetaLowerSegment 240140544 240173312 (24012230450147 / 100000) (24015545626643 / 100000) := by
  exact
    packedTile16384 240140544 240173312 12 1718 15496 28 _ _ (241209 / 12500) (77187 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240173312 :
    ThetaLowerSegment 240173312 240206080 (24015545626643 / 100000) (24018864686563 / 100000) := by
  exact
    packedTile16384 240173312 240206080 12 1720 15497 28 _ _ (964843 / 50000) (1929689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240206080 :
    ThetaLowerSegment 240206080 240238848 (24018864686563 / 100000) (4804428263093 / 20000) := by
  exact
    packedTile16384 240206080 240238848 12 1698 15498 28 _ _ (1929699 / 100000) (964851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240238848 :
    ThetaLowerSegment 240238848 240271616 (4804428263093 / 20000) (24025475859529 / 100000) := by
  exact
    packedTile16384 240238848 240271616 12 1728 15499 28 _ _ (1929713 / 100000) (482429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240271616 :
    ThetaLowerSegment 240271616 240304384 (24025475859529 / 100000) (12014392670667 / 50000) := by
  exact
    packedTile16384 240271616 240304384 12 1715 15500 28 _ _ (1929727 / 100000) (192973 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240304384 :
    ThetaLowerSegment 240304384 240337152 (12014392670667 / 50000) (12016056106547 / 50000) := by
  exact
    packedTile16384 240304384 240337152 12 1724 15501 28 _ _ (96487 / 5000) (1929743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240337152 :
    ThetaLowerSegment 240337152 240369920 (12016056106547 / 50000) (6008836137761 / 25000) := by
  exact
    packedTile16384 240337152 240369920 12 1675 15502 28 _ _ (964877 / 50000) (1929757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240369920 :
    ThetaLowerSegment 240369920 240402688 (6008836137761 / 25000) (24038600067973 / 100000) := by
  exact
    packedTile16384 240369920 240402688 12 1687 15503 28 _ _ (1929767 / 100000) (192977 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240402688 :
    ThetaLowerSegment 240402688 240435456 (24038600067973 / 100000) (12020968329661 / 50000) := by
  exact
    packedTile16384 240402688 240435456 12 1729 15504 28 _ _ (1929781 / 100000) (241223 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240435456 :
    ThetaLowerSegment 240435456 240468224 (12020968329661 / 50000) (24045261696107 / 100000) := by
  exact
    packedTile16384 240435456 240468224 12 1723 15505 28 _ _ (385959 / 20000) (964899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240468224 :
    ThetaLowerSegment 240468224 240500992 (24045261696107 / 100000) (24048629211067 / 100000) := by
  exact
    packedTile16384 240468224 240500992 12 1745 15507 28 _ _ (120613 / 6250) (1929811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240500992 :
    ThetaLowerSegment 240500992 240533760 (24048629211067 / 100000) (24051933066331 / 100000) := by
  exact
    packedTile16384 240500992 240533760 12 1712 15508 28 _ _ (964911 / 50000) (77193 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240533760 :
    ThetaLowerSegment 240533760 240566528 (24051933066331 / 100000) (24055179050483 / 100000) := by
  exact
    packedTile16384 240533760 240566528 12 1682 15509 28 _ _ (482459 / 25000) (1929839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240566528 :
    ThetaLowerSegment 240566528 240599296 (24055179050483 / 100000) (6014605781663 / 25000) := by
  exact
    packedTile16384 240566528 240599296 12 1681 15510 28 _ _ (1929849 / 100000) (482463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240599296 :
    ThetaLowerSegment 240599296 240632064 (6014605781663 / 25000) (24061659506903 / 100000) := by
  exact
    packedTile16384 240599296 240632064 12 1677 15511 28 _ _ (1929863 / 100000) (964933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240632064 :
    ThetaLowerSegment 240632064 240664832 (24061659506903 / 100000) (24064988543003 / 100000) := by
  exact
    packedTile16384 240632064 240664832 12 1725 15512 28 _ _ (482469 / 25000) (1929879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240664832 :
    ThetaLowerSegment 240664832 240697600 (24064988543003 / 100000) (24068348481493 / 100000) := by
  exact
    packedTile16384 240664832 240697600 12 1741 15513 28 _ _ (192989 / 10000) (1929893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240697600 :
    ThetaLowerSegment 240697600 240730368 (24068348481493 / 100000) (4814315442177 / 20000) := by
  exact
    packedTile16384 240697600 240730368 12 1673 15514 28 _ _ (120619 / 6250) (1929907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240730368 :
    ThetaLowerSegment 240730368 240763136 (4814315442177 / 20000) (24074846490283 / 100000) := by
  exact
    packedTile16384 240730368 240763136 12 1694 15515 28 _ _ (1929917 / 100000) (12062 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240763136 :
    ThetaLowerSegment 240763136 240795904 (24074846490283 / 100000) (4815614666983 / 20000) := by
  exact
    packedTile16384 240763136 240795904 12 1672 15516 28 _ _ (1929931 / 100000) (964967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240795904 :
    ThetaLowerSegment 240795904 240828672 (4815614666983 / 20000) (2408149126751 / 10000) := by
  exact
    packedTile16384 240795904 240828672 12 1771 15517 28 _ _ (385989 / 20000) (482487 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240828672 :
    ThetaLowerSegment 240828672 240861440 (2408149126751 / 10000) (12042420837299 / 50000) := by
  exact
    packedTile16384 240828672 240861440 12 1736 15518 28 _ _ (964979 / 50000) (1929961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240861440 :
    ThetaLowerSegment 240861440 240894208 (12042420837299 / 50000) (2408806665781 / 10000) := by
  exact
    packedTile16384 240861440 240894208 12 1671 15519 28 _ _ (482493 / 25000) (77199 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240894208 :
    ThetaLowerSegment 240894208 240926976 (2408806665781 / 10000) (4818262192519 / 20000) := by
  exact
    packedTile16384 240894208 240926976 12 1681 15520 28 _ _ (385997 / 20000) (482497 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240926976 :
    ThetaLowerSegment 240926976 240959744 (4818262192519 / 20000) (12047285365453 / 50000) := by
  exact
    packedTile16384 240926976 240959744 12 1689 15521 28 _ _ (1929999 / 100000) (965001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240959744 :
    ThetaLowerSegment 240959744 240992512 (12047285365453 / 50000) (24097865263097 / 100000) := by
  exact
    packedTile16384 240959744 240992512 12 1707 15522 28 _ _ (1930013 / 100000) (60313 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell240992512 :
    ThetaLowerSegment 240992512 241025280 (24097865263097 / 100000) (24101069106257 / 100000) := by
  exact
    packedTile16384 240992512 241025280 12 1660 15523 28 _ _ (965013 / 50000) (1930029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241025280 :
    ThetaLowerSegment 241025280 241058048 (24101069106257 / 100000) (24104280692817 / 100000) := by
  exact
    packedTile16384 241025280 241058048 12 1664 15524 28 _ _ (48251 / 2500) (1930043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241058048 :
    ThetaLowerSegment 241058048 241090816 (24104280692817 / 100000) (24107561782917 / 100000) := by
  exact
    packedTile16384 241058048 241090816 12 1700 15526 28 _ _ (1930053 / 100000) (241257 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241090816 :
    ThetaLowerSegment 241090816 241123584 (24107561782917 / 100000) (24110846756951 / 100000) := by
  exact
    packedTile16384 241090816 241123584 12 1702 15527 28 _ _ (1930067 / 100000) (193007 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241123584 :
    ThetaLowerSegment 241123584 241156352 (24110846756951 / 100000) (24114181936919 / 100000) := by
  exact
    packedTile16384 241123584 241156352 12 1728 15528 28 _ _ (1930081 / 100000) (482521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241156352 :
    ThetaLowerSegment 241156352 241189120 (24114181936919 / 100000) (24117492048129 / 100000) := by
  exact
    packedTile16384 241156352 241189120 12 1715 15529 28 _ _ (965047 / 50000) (1930097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241189120 :
    ThetaLowerSegment 241189120 241221888 (24117492048129 / 100000) (24120740419893 / 100000) := by
  exact
    packedTile16384 241189120 241221888 12 1683 15530 28 _ _ (482527 / 25000) (1930111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241221888 :
    ThetaLowerSegment 241221888 241254656 (24120740419893 / 100000) (192992049477 / 800) := by
  exact
    packedTile16384 241221888 241254656 12 1692 15531 28 _ _ (1930121 / 100000) (482531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241254656 :
    ThetaLowerSegment 241254656 241287424 (192992049477 / 800) (1206361378997 / 5000) := by
  exact
    packedTile16384 241254656 241287424 12 1669 15532 28 _ _ (386027 / 20000) (965069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241287424 :
    ThetaLowerSegment 241287424 241320192 (1206361378997 / 5000) (3016321565803 / 12500) := by
  exact
    packedTile16384 241287424 241320192 12 1733 15533 28 _ _ (482537 / 25000) (1930151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241320192 :
    ThetaLowerSegment 241320192 241352960 (3016321565803 / 12500) (12066864170647 / 50000) := by
  exact
    packedTile16384 241320192 241352960 12 1635 15534 28 _ _ (965081 / 50000) (386033 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241352960 :
    ThetaLowerSegment 241352960 241385728 (12066864170647 / 50000) (12068523156919 / 50000) := by
  exact
    packedTile16384 241352960 241385728 12 1719 15535 28 _ _ (60318 / 3125) (1930179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241385728 :
    ThetaLowerSegment 241385728 241418496 (12068523156919 / 50000) (4828047383251 / 20000) := by
  exact
    packedTile16384 241385728 241418496 12 1653 15536 28 _ _ (1930189 / 100000) (120637 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241418496 :
    ThetaLowerSegment 241418496 241451264 (4828047383251 / 20000) (2414356651643 / 10000) := by
  exact
    packedTile16384 241418496 241451264 12 1725 15537 28 _ _ (1930203 / 100000) (965103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241451264 :
    ThetaLowerSegment 241451264 241484032 (2414356651643 / 10000) (12073410430303 / 50000) := by
  exact
    packedTile16384 241451264 241484032 12 1686 15538 28 _ _ (241277 / 12500) (1930219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241484032 :
    ThetaLowerSegment 241484032 241516800 (12073410430303 / 50000) (12075076218793 / 50000) := by
  exact
    packedTile16384 241484032 241516800 12 1726 15539 28 _ _ (193023 / 10000) (1930233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241516800 :
    ThetaLowerSegment 241516800 241549568 (12075076218793 / 50000) (12076720785829 / 50000) := by
  exact
    packedTile16384 241516800 241549568 12 1704 15540 28 _ _ (1930243 / 100000) (965123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241549568 :
    ThetaLowerSegment 241549568 241582336 (12076720785829 / 50000) (3019592788891 / 12500) := by
  exact
    packedTile16384 241549568 241582336 12 1710 15541 28 _ _ (1930257 / 100000) (96513 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241582336 :
    ThetaLowerSegment 241582336 241615104 (3019592788891 / 12500) (301999621553 / 1250) := by
  exact
    packedTile16384 241582336 241615104 12 1672 15542 28 _ _ (1930271 / 100000) (965137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241615104 :
    ThetaLowerSegment 241615104 241647872 (301999621553 / 1250) (6040809423763 / 25000) := by
  exact
    packedTile16384 241615104 241647872 12 1693 15543 28 _ _ (482571 / 25000) (1930287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241647872 :
    ThetaLowerSegment 241647872 241680640 (6040809423763 / 25000) (12083204587333 / 50000) := by
  exact
    packedTile16384 241647872 241680640 12 1643 15545 28 _ _ (965149 / 50000) (1930301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241680640 :
    ThetaLowerSegment 241680640 241713408 (12083204587333 / 50000) (12084841491061 / 50000) := by
  exact
    packedTile16384 241680640 241713408 12 1696 15546 28 _ _ (1930311 / 100000) (965157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241713408 :
    ThetaLowerSegment 241713408 241746176 (12084841491061 / 50000) (12086493849261 / 50000) := by
  exact
    packedTile16384 241713408 241746176 12 1712 15547 28 _ _ (77213 / 4000) (241291 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241746176 :
    ThetaLowerSegment 241746176 241778944 (12086493849261 / 50000) (483525617103 / 2000) := by
  exact
    packedTile16384 241746176 241778944 12 1706 15548 28 _ _ (965169 / 50000) (1930341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241778944 :
    ThetaLowerSegment 241778944 241811712 (483525617103 / 2000) (12089777366071 / 50000) := by
  exact
    packedTile16384 241778944 241811712 12 1696 15549 28 _ _ (120647 / 6250) (386071 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241811712 :
    ThetaLowerSegment 241811712 241844480 (12089777366071 / 50000) (12091398872671 / 50000) := by
  exact
    packedTile16384 241811712 241844480 12 1680 15550 28 _ _ (386073 / 20000) (60324 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241844480 :
    ThetaLowerSegment 241844480 241877248 (12091398872671 / 50000) (2418606394661 / 10000) := by
  exact
    packedTile16384 241844480 241877248 12 1692 15551 28 _ _ (1930379 / 100000) (965191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241877248 :
    ThetaLowerSegment 241877248 241910016 (2418606394661 / 10000) (24189378431391 / 100000) := by
  exact
    packedTile16384 241877248 241910016 12 1717 15552 28 _ _ (1930393 / 100000) (482599 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241910016 :
    ThetaLowerSegment 241910016 241942784 (24189378431391 / 100000) (4838525847019 / 20000) := by
  exact
    packedTile16384 241910016 241942784 12 1684 15553 28 _ _ (965203 / 50000) (1930409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241942784 :
    ThetaLowerSegment 241942784 241975552 (4838525847019 / 20000) (4839180259399 / 20000) := by
  exact
    packedTile16384 241942784 241975552 12 1695 15554 28 _ _ (96521 / 5000) (1930423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell241975552 :
    ThetaLowerSegment 241975552 242008320 (4839180259399 / 20000) (24199156007033 / 100000) := by
  exact
    packedTile16384 241975552 242008320 12 1686 15555 28 _ _ (1930433 / 100000) (482609 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242008320 :
    ThetaLowerSegment 242008320 242041088 (24199156007033 / 100000) (1210121984869 / 5000) := by
  exact
    packedTile16384 242008320 242041088 12 1701 15556 28 _ _ (1930447 / 100000) (38609 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242041088 :
    ThetaLowerSegment 242041088 242073856 (1210121984869 / 5000) (302571542623 / 1250) := by
  exact
    packedTile16384 242041088 242073856 12 1701 15557 28 _ _ (96523 / 5000) (1930463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242073856 :
    ThetaLowerSegment 242073856 242106624 (302571542623 / 1250) (12104495851161 / 50000) := by
  exact
    packedTile16384 242073856 242106624 12 1693 15558 28 _ _ (965237 / 50000) (1930477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242106624 :
    ThetaLowerSegment 242106624 242139392 (12104495851161 / 50000) (6053073208773 / 25000) := by
  exact
    packedTile16384 242106624 242139392 12 1710 15559 28 _ _ (1930487 / 100000) (193049 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242139392 :
    ThetaLowerSegment 242139392 242172160 (6053073208773 / 25000) (3026946835849 / 12500) := by
  exact
    packedTile16384 242139392 242172160 12 1700 15560 28 _ _ (1930501 / 100000) (241313 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242172160 :
    ThetaLowerSegment 242172160 242204928 (3026946835849 / 12500) (1210943021081 / 5000) := by
  exact
    packedTile16384 242172160 242204928 12 1702 15561 28 _ _ (965257 / 50000) (1930517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242204928 :
    ThetaLowerSegment 242204928 242237696 (1210943021081 / 5000) (242220650981 / 1000) := by
  exact
    packedTile16384 242204928 242237696 12 1660 15562 28 _ _ (60329 / 3125) (1930531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242237696 :
    ThetaLowerSegment 242237696 242270464 (242220650981 / 1000) (12112647447433 / 50000) := by
  exact
    packedTile16384 242237696 242270464 12 1673 15563 28 _ _ (965271 / 50000) (386109 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242270464 :
    ThetaLowerSegment 242270464 242303232 (12112647447433 / 50000) (12114265252523 / 50000) := by
  exact
    packedTile16384 242270464 242303232 12 1676 15565 28 _ _ (386111 / 20000) (965279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242303232 :
    ThetaLowerSegment 242303232 242336000 (12114265252523 / 50000) (24231864597709 / 100000) := by
  exact
    packedTile16384 242303232 242336000 12 1727 15566 28 _ _ (1930569 / 100000) (482643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242336000 :
    ThetaLowerSegment 242336000 242368768 (24231864597709 / 100000) (24235030752189 / 100000) := by
  exact
    packedTile16384 242336000 242368768 12 1640 15567 28 _ _ (965291 / 50000) (386117 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242368768 :
    ThetaLowerSegment 242368768 242401536 (24235030752189 / 100000) (4847662939197 / 20000) := by
  exact
    packedTile16384 242368768 242401536 12 1701 15568 28 _ _ (482649 / 25000) (1930599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242401536 :
    ThetaLowerSegment 242401536 242434304 (4847662939197 / 20000) (24241592870067 / 100000) := by
  exact
    packedTile16384 242401536 242434304 12 1698 15569 28 _ _ (1930609 / 100000) (482653 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242434304 :
    ThetaLowerSegment 242434304 242467072 (24241592870067 / 100000) (12122422984911 / 50000) := by
  exact
    packedTile16384 242434304 242467072 12 1685 15570 28 _ _ (1930623 / 100000) (965313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242467072 :
    ThetaLowerSegment 242467072 242499840 (12122422984911 / 50000) (2424818210883 / 10000) := by
  exact
    packedTile16384 242467072 242499840 12 1728 15571 28 _ _ (482659 / 25000) (1930639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242499840 :
    ThetaLowerSegment 242499840 242532608 (2424818210883 / 10000) (606286846677 / 2500) := by
  exact
    packedTile16384 242499840 242532608 12 1705 15572 28 _ _ (38613 / 2000) (1930653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242532608 :
    ThetaLowerSegment 242532608 242565376 (606286846677 / 2500) (12127345175819 / 50000) := by
  exact
    packedTile16384 242532608 242565376 12 1666 15573 28 _ _ (1930663 / 100000) (965333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242565376 :
    ThetaLowerSegment 242565376 242598144 (12127345175819 / 50000) (1516121109397 / 6250) := by
  exact
    packedTile16384 242565376 242598144 12 1682 15574 28 _ _ (1930677 / 100000) (48267 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242598144 :
    ThetaLowerSegment 242598144 242630912 (1516121109397 / 6250) (12130539491491 / 50000) := by
  exact
    packedTile16384 242598144 242630912 12 1627 15575 28 _ _ (193069 / 10000) (1930693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242630912 :
    ThetaLowerSegment 242630912 242663680 (12130539491491 / 50000) (12132214377211 / 50000) := by
  exact
    packedTile16384 242630912 242663680 12 1735 15576 28 _ _ (120669 / 6250) (1930707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242663680 :
    ThetaLowerSegment 242663680 242696448 (12132214377211 / 50000) (12133809149453 / 50000) := by
  exact
    packedTile16384 242663680 242696448 12 1652 15577 28 _ _ (1930717 / 100000) (12067 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242696448 :
    ThetaLowerSegment 242696448 242729216 (12133809149453 / 50000) (24270941086957 / 100000) := by
  exact
    packedTile16384 242696448 242729216 12 1721 15578 28 _ _ (1930731 / 100000) (965367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242729216 :
    ThetaLowerSegment 242729216 242761984 (24270941086957 / 100000) (24274213698037 / 100000) := by
  exact
    packedTile16384 242729216 242761984 12 1695 15579 28 _ _ (241343 / 12500) (1930747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242761984 :
    ThetaLowerSegment 242761984 242794752 (24274213698037 / 100000) (24277453509961 / 100000) := by
  exact
    packedTile16384 242761984 242794752 12 1678 15580 28 _ _ (965379 / 50000) (1930761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242794752 :
    ThetaLowerSegment 242794752 242827520 (24277453509961 / 100000) (4856144847207 / 20000) := by
  exact
    packedTile16384 242794752 242827520 12 1694 15581 28 _ _ (1930771 / 100000) (965387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242827520 :
    ThetaLowerSegment 242827520 242860288 (4856144847207 / 20000) (1214201583537 / 5000) := by
  exact
    packedTile16384 242827520 242860288 12 1713 15582 28 _ _ (386157 / 20000) (482697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242860288 :
    ThetaLowerSegment 242860288 242893056 (1214201583537 / 5000) (12143650255877 / 50000) := by
  exact
    packedTile16384 242860288 242893056 12 1693 15583 28 _ _ (965399 / 50000) (1930801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242893056 :
    ThetaLowerSegment 242893056 242925824 (12143650255877 / 50000) (12145304961761 / 50000) := by
  exact
    packedTile16384 242893056 242925824 12 1714 15585 28 _ _ (482703 / 25000) (386163 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242925824 :
    ThetaLowerSegment 242925824 242958592 (12145304961761 / 50000) (24293871086947 / 100000) := by
  exact
    packedTile16384 242925824 242958592 12 1689 15586 28 _ _ (77233 / 4000) (482707 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242958592 :
    ThetaLowerSegment 242958592 242991360 (24293871086947 / 100000) (2429718633751 / 10000) := by
  exact
    packedTile16384 242958592 242991360 12 1717 15587 28 _ _ (1930839 / 100000) (965421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell242991360 :
    ThetaLowerSegment 242991360 243024128 (2429718633751 / 10000) (12150201568471 / 50000) := by
  exact
    packedTile16384 242991360 243024128 12 1666 15588 28 _ _ (482713 / 25000) (386171 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243024128 :
    ThetaLowerSegment 243024128 243056896 (12150201568471 / 50000) (6075915126971 / 25000) := by
  exact
    packedTile16384 243024128 243056896 12 1687 15589 28 _ _ (965433 / 50000) (1930869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243056896 :
    ThetaLowerSegment 243056896 243089664 (6075915126971 / 25000) (24307006721191 / 100000) := by
  exact
    packedTile16384 243056896 243089664 12 1733 15590 28 _ _ (1930879 / 100000) (965441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243089664 :
    ThetaLowerSegment 243089664 243122432 (24307006721191 / 100000) (24310250621431 / 100000) := by
  exact
    packedTile16384 243089664 243122432 12 1680 15591 28 _ _ (1930893 / 100000) (120681 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243122432 :
    ThetaLowerSegment 243122432 243155200 (24310250621431 / 100000) (24313519645289 / 100000) := by
  exact
    packedTile16384 243122432 243155200 12 1693 15592 28 _ _ (965453 / 50000) (1930909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243155200 :
    ThetaLowerSegment 243155200 243187968 (24313519645289 / 100000) (24316742350769 / 100000) := by
  exact
    packedTile16384 243155200 243187968 12 1669 15593 28 _ _ (48273 / 2500) (1930923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243187968 :
    ThetaLowerSegment 243187968 243220736 (24316742350769 / 100000) (24320071279261 / 100000) := by
  exact
    packedTile16384 243187968 243220736 12 1724 15594 28 _ _ (1930933 / 100000) (241367 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243220736 :
    ThetaLowerSegment 243220736 243253504 (24320071279261 / 100000) (4864681976979 / 20000) := by
  exact
    packedTile16384 243220736 243253504 12 1729 15595 28 _ _ (965473 / 50000) (1930949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243253504 :
    ThetaLowerSegment 243253504 243286272 (4864681976979 / 20000) (4865352020099 / 20000) := by
  exact
    packedTile16384 243253504 243286272 12 1735 15596 28 _ _ (24137 / 1250) (1930963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243286272 :
    ThetaLowerSegment 243286272 243319040 (4865352020099 / 20000) (1216498758527 / 5000) := by
  exact
    packedTile16384 243286272 243319040 12 1665 15597 28 _ _ (1930973 / 100000) (60343 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243319040 :
    ThetaLowerSegment 243319040 243351808 (1216498758527 / 5000) (12166615407311 / 50000) := by
  exact
    packedTile16384 243319040 243351808 12 1686 15598 28 _ _ (1930987 / 100000) (193099 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243351808 :
    ThetaLowerSegment 243351808 243384576 (12166615407311 / 50000) (12168247102311 / 50000) := by
  exact
    packedTile16384 243351808 243384576 12 1690 15599 28 _ _ (1931 / 100) (1931003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243384576 :
    ThetaLowerSegment 243384576 243417344 (12168247102311 / 50000) (12169874947113 / 50000) := by
  exact
    packedTile16384 243384576 243417344 12 1686 15600 28 _ _ (965507 / 50000) (1931017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243417344 :
    ThetaLowerSegment 243417344 243450112 (12169874947113 / 50000) (24342992088559 / 100000) := by
  exact
    packedTile16384 243417344 243450112 12 1679 15601 28 _ _ (1931027 / 100000) (193103 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243450112 :
    ThetaLowerSegment 243450112 243482880 (24342992088559 / 100000) (24346236237439 / 100000) := by
  exact
    packedTile16384 243450112 243482880 12 1680 15602 28 _ _ (1931041 / 100000) (482761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243482880 :
    ThetaLowerSegment 243482880 243515648 (24346236237439 / 100000) (24349590478237 / 100000) := by
  exact
    packedTile16384 243482880 243515648 12 1737 15603 28 _ _ (965527 / 50000) (1931057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243515648 :
    ThetaLowerSegment 243515648 243548416 (24349590478237 / 100000) (24352803775389 / 100000) := by
  exact
    packedTile16384 243515648 243548416 12 1664 15604 28 _ _ (482767 / 25000) (1931071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243548416 :
    ThetaLowerSegment 243548416 243581184 (24352803775389 / 100000) (24356132959033 / 100000) := by
  exact
    packedTile16384 243548416 243581184 12 1724 15606 28 _ _ (1931081 / 100000) (482771 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243581184 :
    ThetaLowerSegment 243581184 243613952 (24356132959033 / 100000) (12179691495959 / 50000) := by
  exact
    packedTile16384 243581184 243613952 12 1683 15607 28 _ _ (386219 / 20000) (965549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243613952 :
    ThetaLowerSegment 243613952 243646720 (12179691495959 / 50000) (12181316523341 / 50000) := by
  exact
    packedTile16384 243613952 243646720 12 1683 15608 28 _ _ (482777 / 25000) (1931111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243646720 :
    ThetaLowerSegment 243646720 243679488 (12181316523341 / 50000) (24365906296777 / 100000) := by
  exact
    packedTile16384 243646720 243679488 12 1695 15609 28 _ _ (1931121 / 100000) (482781 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243679488 :
    ThetaLowerSegment 243679488 243712256 (24365906296777 / 100000) (761535533926 / 3125) := by
  exact
    packedTile16384 243679488 243712256 12 1673 15610 28 _ _ (386227 / 20000) (965569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243712256 :
    ThetaLowerSegment 243712256 243745024 (761535533926 / 3125) (761639333131 / 3125) := by
  exact
    packedTile16384 243712256 243745024 12 1720 15611 28 _ _ (482787 / 25000) (1931151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243745024 :
    ThetaLowerSegment 243745024 243777792 (761639333131 / 3125) (12187846678271 / 50000) := by
  exact
    packedTile16384 243745024 243777792 12 1675 15612 28 _ _ (965581 / 50000) (386233 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243777792 :
    ThetaLowerSegment 243777792 243810560 (12187846678271 / 50000) (24378931937017 / 100000) := by
  exact
    packedTile16384 243777792 243810560 12 1677 15613 28 _ _ (77247 / 4000) (965589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243810560 :
    ThetaLowerSegment 243810560 243843328 (24378931937017 / 100000) (6095551325593 / 25000) := by
  exact
    packedTile16384 243810560 243843328 12 1695 15614 28 _ _ (1931189 / 100000) (241399 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243843328 :
    ThetaLowerSegment 243843328 243876096 (6095551325593 / 25000) (3048197147633 / 12500) := by
  exact
    packedTile16384 243843328 243876096 12 1746 15615 28 _ _ (965601 / 50000) (386241 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243876096 :
    ThetaLowerSegment 243876096 243908864 (3048197147633 / 12500) (3048609945053 / 12500) := by
  exact
    packedTile16384 243876096 243908864 12 1710 15616 28 _ _ (120701 / 6250) (1931219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243908864 :
    ThetaLowerSegment 243908864 243941632 (3048609945053 / 12500) (6098040662431 / 25000) := by
  exact
    packedTile16384 243908864 243941632 12 1700 15617 28 _ _ (1931229 / 100000) (60351 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243941632 :
    ThetaLowerSegment 243941632 243974400 (6098040662431 / 25000) (3049423477983 / 12500) := by
  exact
    packedTile16384 243941632 243974400 12 1670 15618 28 _ _ (965621 / 50000) (386249 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell243974400 :
    ThetaLowerSegment 243974400 244007168 (3049423477983 / 12500) (762455268828 / 3125) := by
  exact
    packedTile16384 243974400 244007168 12 1647 15619 28 _ _ (241407 / 12500) (1931259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244007168 :
    ThetaLowerSegment 244007168 244039936 (762455268828 / 3125) (4880363013137 / 20000) := by
  exact
    packedTile16384 244007168 244039936 12 1681 15620 28 _ _ (1931269 / 100000) (241409 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244039936 :
    ThetaLowerSegment 244039936 244072704 (4880363013137 / 20000) (24405024858031 / 100000) := by
  exact
    packedTile16384 244039936 244072704 12 1662 15621 28 _ _ (1931283 / 100000) (965643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244072704 :
    ThetaLowerSegment 244072704 244105472 (24405024858031 / 100000) (24408294542159 / 100000) := by
  exact
    packedTile16384 244072704 244105472 12 1693 15622 28 _ _ (60353 / 3125) (1931299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244105472 :
    ThetaLowerSegment 244105472 244138240 (24408294542159 / 100000) (24411624120599 / 100000) := by
  exact
    packedTile16384 244105472 244138240 12 1724 15623 28 _ _ (193131 / 10000) (1931313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244138240 :
    ThetaLowerSegment 244138240 244171008 (24411624120599 / 100000) (3051859317151 / 12500) := by
  exact
    packedTile16384 244138240 244171008 12 1683 15624 28 _ _ (1931323 / 100000) (965663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244171008 :
    ThetaLowerSegment 244171008 244203776 (3051859317151 / 12500) (3052276002893 / 12500) := by
  exact
    packedTile16384 244171008 244203776 12 1726 15625 28 _ _ (241417 / 12500) (1931339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244203776 :
    ThetaLowerSegment 244203776 244236544 (3052276002893 / 12500) (12210735036647 / 50000) := by
  exact
    packedTile16384 244203776 244236544 12 1689 15627 28 _ _ (38627 / 2000) (1931353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244236544 :
    ThetaLowerSegment 244236544 244269312 (12210735036647 / 50000) (12212392146101 / 50000) := by
  exact
    packedTile16384 244236544 244269312 12 1716 15628 28 _ _ (1931363 / 100000) (965683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244269312 :
    ThetaLowerSegment 244269312 244302080 (12212392146101 / 50000) (1526754468491 / 6250) := by
  exact
    packedTile16384 244269312 244302080 12 1702 15629 28 _ _ (1931377 / 100000) (96569 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244302080 :
    ThetaLowerSegment 244302080 244334848 (1526754468491 / 6250) (12215662944003 / 50000) := by
  exact
    packedTile16384 244302080 244334848 12 1685 15630 28 _ _ (193139 / 10000) (1931393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244334848 :
    ThetaLowerSegment 244334848 244367616 (12215662944003 / 50000) (12217309465913 / 50000) := by
  exact
    packedTile16384 244334848 244367616 12 1705 15631 28 _ _ (482851 / 25000) (1931407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244367616 :
    ThetaLowerSegment 244367616 244400384 (12217309465913 / 50000) (24437881095139 / 100000) := by
  exact
    packedTile16384 244367616 244400384 12 1689 15632 28 _ _ (1931417 / 100000) (96571 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244400384 :
    ThetaLowerSegment 244400384 244433152 (24437881095139 / 100000) (24441147143269 / 100000) := by
  exact
    packedTile16384 244400384 244433152 12 1691 15633 28 _ _ (193143 / 10000) (1931433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244433152 :
    ThetaLowerSegment 244433152 244465920 (24441147143269 / 100000) (24444403557853 / 100000) := by
  exact
    packedTile16384 244433152 244465920 12 1686 15634 28 _ _ (482861 / 25000) (1931447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244465920 :
    ThetaLowerSegment 244465920 244498688 (24444403557853 / 100000) (12223879249331 / 50000) := by
  exact
    packedTile16384 244465920 244498688 12 1737 15635 28 _ _ (1931457 / 100000) (96573 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244498688 :
    ThetaLowerSegment 244498688 244531456 (12223879249331 / 50000) (24450999507 / 100) := by
  exact
    packedTile16384 244498688 244531456 12 1678 15636 28 _ _ (1931471 / 100000) (965737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244531456 :
    ThetaLowerSegment 244531456 244564224 (24450999507 / 100) (1528395345153 / 6250) := by
  exact
    packedTile16384 244531456 244564224 12 1722 15637 28 _ _ (482871 / 25000) (1931487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244564224 :
    ThetaLowerSegment 244564224 244596992 (1528395345153 / 6250) (4891522199769 / 20000) := by
  exact
    packedTile16384 244564224 244596992 12 1701 15638 28 _ _ (1931497 / 100000) (3863 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244596992 :
    ThetaLowerSegment 244596992 244629760 (4891522199769 / 20000) (24460902293589 / 100000) := by
  exact
    packedTile16384 244596992 244629760 12 1704 15639 28 _ _ (1931511 / 100000) (965757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244629760 :
    ThetaLowerSegment 244629760 244662528 (24460902293589 / 100000) (4892834859049 / 20000) := by
  exact
    packedTile16384 244629760 244662528 12 1694 15640 28 _ _ (482881 / 25000) (1931527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244662528 :
    ThetaLowerSegment 244662528 244695296 (4892834859049 / 20000) (24467596980581 / 100000) := by
  exact
    packedTile16384 244662528 244695296 12 1772 15641 28 _ _ (965769 / 50000) (1931541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244695296 :
    ThetaLowerSegment 244695296 244728064 (24467596980581 / 100000) (12235431616661 / 50000) := by
  exact
    packedTile16384 244695296 244728064 12 1691 15642 28 _ _ (1931551 / 100000) (965777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244728064 :
    ThetaLowerSegment 244728064 244760832 (12235431616661 / 50000) (2447417007089 / 10000) := by
  exact
    packedTile16384 244728064 244760832 12 1712 15643 28 _ _ (482891 / 25000) (1931567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244760832 :
    ThetaLowerSegment 244760832 244793600 (2447417007089 / 10000) (12238715287277 / 50000) := by
  exact
    packedTile16384 244760832 244793600 12 1688 15644 28 _ _ (965789 / 50000) (1931581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244793600 :
    ThetaLowerSegment 244793600 244826368 (12238715287277 / 50000) (12240453719177 / 50000) := by
  exact
    packedTile16384 244793600 244826368 12 1800 15645 28 _ _ (1931591 / 100000) (965797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244826368 :
    ThetaLowerSegment 244826368 244859136 (12240453719177 / 50000) (12242086890359 / 50000) := by
  exact
    packedTile16384 244826368 244859136 12 1691 15646 28 _ _ (482901 / 25000) (1931607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244859136 :
    ThetaLowerSegment 244859136 244891904 (12242086890359 / 50000) (3060938227721 / 12500) := by
  exact
    packedTile16384 244859136 244891904 12 1725 15647 28 _ _ (965809 / 50000) (1931621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244891904 :
    ThetaLowerSegment 244891904 244924672 (3060938227721 / 12500) (765337416281 / 3125) := by
  exact
    packedTile16384 244891904 244924672 12 1704 15649 28 _ _ (1931631 / 100000) (965817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244924672 :
    ThetaLowerSegment 244924672 244957440 (765337416281 / 3125) (24494125545327 / 100000) := by
  exact
    packedTile16384 244924672 244957440 12 1723 15650 28 _ _ (386329 / 20000) (60364 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244957440 :
    ThetaLowerSegment 244957440 244990208 (24494125545327 / 100000) (24497432543823 / 100000) := by
  exact
    packedTile16384 244957440 244990208 12 1712 15651 28 _ _ (965829 / 50000) (1931661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell244990208 :
    ThetaLowerSegment 244990208 245022976 (24497432543823 / 100000) (12250359158097 / 50000) := by
  exact
    packedTile16384 244990208 245022976 12 1701 15652 28 _ _ (1931671 / 100000) (965837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245022976 :
    ThetaLowerSegment 245022976 245055744 (12250359158097 / 50000) (6125995715961 / 25000) := by
  exact
    packedTile16384 245022976 245055744 12 1690 15653 28 _ _ (386337 / 20000) (241461 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245055744 :
    ThetaLowerSegment 245055744 245088512 (6125995715961 / 25000) (12253584116923 / 50000) := by
  exact
    packedTile16384 245055744 245088512 12 1649 15654 28 _ _ (965849 / 50000) (1931701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245088512 :
    ThetaLowerSegment 245088512 245121280 (12253584116923 / 50000) (24510442483991 / 100000) := by
  exact
    packedTile16384 245088512 245121280 12 1695 15655 28 _ _ (1931711 / 100000) (965857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245121280 :
    ThetaLowerSegment 245121280 245154048 (24510442483991 / 100000) (24513830729641 / 100000) := by
  exact
    packedTile16384 245121280 245154048 12 1754 15656 28 _ _ (77269 / 4000) (120733 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245154048 :
    ThetaLowerSegment 245154048 245186816 (24513830729641 / 100000) (24517041278197 / 100000) := by
  exact
    packedTile16384 245154048 245186816 12 1662 15657 28 _ _ (965869 / 50000) (1931741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245186816 :
    ThetaLowerSegment 245186816 245219584 (24517041278197 / 100000) (24520356164629 / 100000) := by
  exact
    packedTile16384 245186816 245219584 12 1716 15658 28 _ _ (241469 / 12500) (386351 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245219584 :
    ThetaLowerSegment 245219584 245252352 (24520356164629 / 100000) (24523628574539 / 100000) := by
  exact
    packedTile16384 245219584 245252352 12 1694 15659 28 _ _ (386353 / 20000) (241471 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245252352 :
    ThetaLowerSegment 245252352 245285120 (24523628574539 / 100000) (24526951232699 / 100000) := by
  exact
    packedTile16384 245252352 245285120 12 1720 15660 28 _ _ (965889 / 50000) (1931781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245285120 :
    ThetaLowerSegment 245285120 245317888 (24526951232699 / 100000) (24530142553083 / 100000) := by
  exact
    packedTile16384 245285120 245317888 12 1652 15661 28 _ _ (120737 / 6250) (386359 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245317888 :
    ThetaLowerSegment 245317888 245350656 (24530142553083 / 100000) (12266750980989 / 50000) := by
  exact
    packedTile16384 245317888 245350656 12 1739 15662 28 _ _ (386361 / 20000) (60369 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245350656 :
    ThetaLowerSegment 245350656 245383424 (12266750980989 / 50000) (1226840171947 / 5000) := by
  exact
    packedTile16384 245350656 245383424 12 1709 15663 28 _ _ (965909 / 50000) (1931821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245383424 :
    ThetaLowerSegment 245383424 245416192 (1226840171947 / 5000) (1227003894709 / 5000) := by
  exact
    packedTile16384 245383424 245416192 12 1695 15664 28 _ _ (241479 / 12500) (386367 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245416192 :
    ThetaLowerSegment 245416192 245448960 (1227003894709 / 5000) (2454335043961 / 10000) := by
  exact
    packedTile16384 245416192 245448960 12 1694 15665 28 _ _ (386369 / 20000) (241481 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245448960 :
    ThetaLowerSegment 245448960 245481728 (2454335043961 / 10000) (12273328890253 / 50000) := by
  exact
    packedTile16384 245448960 245481728 12 1712 15666 28 _ _ (965929 / 50000) (1931861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245481728 :
    ThetaLowerSegment 245481728 245514496 (12273328890253 / 50000) (12274994163917 / 50000) := by
  exact
    packedTile16384 245481728 245514496 12 1724 15667 28 _ _ (60371 / 3125) (3091 / 160) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245514496 :
    ThetaLowerSegment 245514496 245547264 (12274994163917 / 50000) (6138313303371 / 25000) := by
  exact
    packedTile16384 245514496 245547264 12 1690 15668 28 _ _ (386377 / 20000) (120743 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245547264 :
    ThetaLowerSegment 245547264 245580032 (6138313303371 / 25000) (2455644857443 / 10000) := by
  exact
    packedTile16384 245547264 245580032 12 1654 15669 28 _ _ (1931899 / 100000) (965951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245580032 :
    ThetaLowerSegment 245580032 245612800 (2455644857443 / 10000) (12279821978439 / 50000) := by
  exact
    packedTile16384 245580032 245612800 12 1654 15670 28 _ _ (241489 / 12500) (386383 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245612800 :
    ThetaLowerSegment 245612800 245645568 (12279821978439 / 50000) (24562953344403 / 100000) := by
  exact
    packedTile16384 245612800 245645568 12 1713 15672 28 _ _ (77277 / 4000) (241491 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245645568 :
    ThetaLowerSegment 245645568 245678336 (24562953344403 / 100000) (12283123650199 / 50000) := by
  exact
    packedTile16384 245645568 245678336 12 1705 15673 28 _ _ (1931939 / 100000) (965971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245678336 :
    ThetaLowerSegment 245678336 245711104 (12283123650199 / 50000) (2456947559219 / 10000) := by
  exact
    packedTile16384 245678336 245711104 12 1671 15674 28 _ _ (120747 / 6250) (386391 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245711104 :
    ThetaLowerSegment 245711104 245743872 (2456947559219 / 10000) (19658183217 / 80) := by
  exact
    packedTile16384 245711104 245743872 12 1684 15675 28 _ _ (386393 / 20000) (60374 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245743872 :
    ThetaLowerSegment 245743872 245776640 (19658183217 / 80) (12287991236943 / 50000) := by
  exact
    packedTile16384 245743872 245776640 12 1684 15676 28 _ _ (1931979 / 100000) (965991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245776640 :
    ThetaLowerSegment 245776640 245809408 (12287991236943 / 50000) (2457929004419 / 10000) := by
  exact
    packedTile16384 245776640 245809408 12 1712 15677 28 _ _ (241499 / 12500) (386399 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245809408 :
    ThetaLowerSegment 245809408 245842176 (2457929004419 / 10000) (1229129688637 / 5000) := by
  exact
    packedTile16384 245809408 245842176 12 1710 15678 28 _ _ (386401 / 20000) (241501 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245842176 :
    ThetaLowerSegment 245842176 245874944 (1229129688637 / 5000) (24585922641477 / 100000) := by
  exact
    packedTile16384 245842176 245874944 12 1723 15679 28 _ _ (1932019 / 100000) (966011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245874944 :
    ThetaLowerSegment 245874944 245907712 (24585922641477 / 100000) (24589151066949 / 100000) := by
  exact
    packedTile16384 245874944 245907712 12 1671 15680 28 _ _ (60376 / 3125) (386407 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245907712 :
    ThetaLowerSegment 245907712 245940480 (24589151066949 / 100000) (6148112266941 / 25000) := by
  exact
    packedTile16384 245907712 245940480 12 1707 15681 28 _ _ (386409 / 20000) (120753 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245940480 :
    ThetaLowerSegment 245940480 245973248 (6148112266941 / 25000) (6148919867603 / 25000) := by
  exact
    packedTile16384 245940480 245973248 12 1672 15682 28 _ _ (1932059 / 100000) (966031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell245973248 :
    ThetaLowerSegment 245973248 246006016 (6148919867603 / 25000) (6149724575591 / 25000) := by
  exact
    packedTile16384 245973248 246006016 12 1666 15683 28 _ _ (241509 / 12500) (77283 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246006016 :
    ThetaLowerSegment 246006016 246038784 (6149724575591 / 25000) (12301093355517 / 50000) := by
  exact
    packedTile16384 246006016 246038784 12 1702 15684 28 _ _ (386417 / 20000) (241511 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246038784 :
    ThetaLowerSegment 246038784 246071552 (12301093355517 / 50000) (6151362506139 / 25000) := by
  exact
    packedTile16384 246038784 246071552 12 1689 15685 28 _ _ (966049 / 50000) (1932101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246071552 :
    ThetaLowerSegment 246071552 246104320 (6151362506139 / 25000) (6152151290863 / 25000) := by
  exact
    packedTile16384 246071552 246104320 12 1633 15686 28 _ _ (120757 / 6250) (386423 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246104320 :
    ThetaLowerSegment 246104320 246137088 (6152151290863 / 25000) (24611918757827 / 100000) := by
  exact
    packedTile16384 246104320 246137088 12 1715 15687 28 _ _ (15457 / 800) (60379 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246137088 :
    ThetaLowerSegment 246137088 246169856 (24611918757827 / 100000) (24615141564011 / 100000) := by
  exact
    packedTile16384 246137088 246169856 12 1668 15688 28 _ _ (966069 / 50000) (1932141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246169856 :
    ThetaLowerSegment 246169856 246202624 (24615141564011 / 100000) (24618457136843 / 100000) := by
  exact
    packedTile16384 246169856 246202624 12 1716 15689 28 _ _ (241519 / 12500) (386431 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246202624 :
    ThetaLowerSegment 246202624 246235392 (24618457136843 / 100000) (12310854485269 / 50000) := by
  exact
    packedTile16384 246202624 246235392 12 1683 15690 28 _ _ (386433 / 20000) (241521 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246235392 :
    ThetaLowerSegment 246235392 246268160 (12310854485269 / 50000) (12312448532119 / 50000) := by
  exact
    packedTile16384 246235392 246268160 12 1650 15691 28 _ _ (966089 / 50000) (1932181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246268160 :
    ThetaLowerSegment 246268160 246300928 (12312448532119 / 50000) (12314080268263 / 50000) := by
  exact
    packedTile16384 246268160 246300928 12 1689 15692 28 _ _ (60381 / 3125) (386439 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246300928 :
    ThetaLowerSegment 246300928 246333696 (12314080268263 / 50000) (12315745828973 / 50000) := by
  exact
    packedTile16384 246300928 246333696 12 1724 15693 28 _ _ (386441 / 20000) (120763 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246333696 :
    ThetaLowerSegment 246333696 246366464 (12315745828973 / 50000) (12317397875363 / 50000) := by
  exact
    packedTile16384 246333696 246366464 12 1710 15695 28 _ _ (966109 / 50000) (1932221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246366464 :
    ThetaLowerSegment 246366464 246399232 (12317397875363 / 50000) (492760915299 / 2000) := by
  exact
    packedTile16384 246366464 246399232 12 1682 15696 28 _ _ (241529 / 12500) (386447 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246399232 :
    ThetaLowerSegment 246399232 246432000 (492760915299 / 2000) (2464129966553 / 10000) := by
  exact
    packedTile16384 246399232 246432000 12 1684 15697 28 _ _ (386449 / 20000) (241531 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246432000 :
    ThetaLowerSegment 246432000 246464768 (2464129966553 / 10000) (12322334761741 / 50000) := by
  exact
    packedTile16384 246432000 246464768 12 1744 15698 28 _ _ (966129 / 50000) (1932261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246464768 :
    ThetaLowerSegment 246464768 246497536 (12322334761741 / 50000) (24647933129201 / 100000) := by
  exact
    packedTile16384 246464768 246497536 12 1689 15699 28 _ _ (1932271 / 100000) (966137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246497536 :
    ThetaLowerSegment 246497536 246530304 (24647933129201 / 100000) (12325621566703 / 50000) := by
  exact
    packedTile16384 246497536 246530304 12 1713 15700 28 _ _ (386457 / 20000) (60384 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246530304 :
    ThetaLowerSegment 246530304 246563072 (12325621566703 / 50000) (2465450485243 / 10000) := by
  exact
    packedTile16384 246530304 246563072 12 1688 15701 28 _ _ (966149 / 50000) (1932301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246563072 :
    ThetaLowerSegment 246563072 246595840 (2465450485243 / 10000) (6164458072993 / 25000) := by
  exact
    packedTile16384 246563072 246595840 12 1722 15702 28 _ _ (1932311 / 100000) (966157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246595840 :
    ThetaLowerSegment 246595840 246628608 (6164458072993 / 25000) (24661200334447 / 100000) := by
  exact
    packedTile16384 246595840 246628608 12 1743 15703 28 _ _ (77293 / 4000) (241541 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246628608 :
    ThetaLowerSegment 246628608 246661376 (24661200334447 / 100000) (4932881989573 / 20000) := by
  exact
    packedTile16384 246628608 246661376 12 1661 15704 28 _ _ (966169 / 50000) (1932341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246661376 :
    ThetaLowerSegment 246661376 246694144 (4932881989573 / 20000) (4933535124211 / 20000) := by
  exact
    packedTile16384 246661376 246694144 12 1690 15705 28 _ _ (1932351 / 100000) (966177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246694144 :
    ThetaLowerSegment 246694144 246726912 (4933535124211 / 20000) (24670983828223 / 100000) := by
  exact
    packedTile16384 246694144 246726912 12 1712 15706 28 _ _ (483091 / 25000) (1932367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246726912 :
    ThetaLowerSegment 246726912 246759680 (24670983828223 / 100000) (4934855320067 / 20000) := by
  exact
    packedTile16384 246726912 246759680 12 1704 15707 28 _ _ (966189 / 50000) (1932381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246759680 :
    ThetaLowerSegment 246759680 246792448 (4934855320067 / 20000) (24677480504613 / 100000) := by
  exact
    packedTile16384 246759680 246792448 12 1658 15708 28 _ _ (1932391 / 100000) (966197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246792448 :
    ThetaLowerSegment 246792448 246825216 (24677480504613 / 100000) (24680767523817 / 100000) := by
  exact
    packedTile16384 246792448 246825216 12 1701 15709 28 _ _ (483101 / 25000) (1932407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246825216 :
    ThetaLowerSegment 246825216 246857984 (24680767523817 / 100000) (24684089350359 / 100000) := by
  exact
    packedTile16384 246825216 246857984 12 1719 15710 28 _ _ (966209 / 50000) (1932421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246857984 :
    ThetaLowerSegment 246857984 246890752 (24684089350359 / 100000) (24687335834439 / 100000) := by
  exact
    packedTile16384 246857984 246890752 12 1680 15711 28 _ _ (1932431 / 100000) (966217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246890752 :
    ThetaLowerSegment 246890752 246923520 (24687335834439 / 100000) (24690646111011 / 100000) := by
  exact
    packedTile16384 246890752 246923520 12 1713 15712 28 _ _ (483111 / 25000) (1932447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246923520 :
    ThetaLowerSegment 246923520 246956288 (24690646111011 / 100000) (3086731990261 / 12500) := by
  exact
    packedTile16384 246923520 246956288 12 1661 15713 28 _ _ (1932457 / 100000) (96623 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246956288 :
    ThetaLowerSegment 246956288 246989056 (3086731990261 / 12500) (24697112135723 / 100000) := by
  exact
    packedTile16384 246956288 246989056 12 1685 15714 28 _ _ (1932471 / 100000) (966237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell246989056 :
    ThetaLowerSegment 246989056 247021824 (24697112135723 / 100000) (24700381898651 / 100000) := by
  exact
    packedTile16384 246989056 247021824 12 1692 15715 28 _ _ (483121 / 25000) (1932487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247021824 :
    ThetaLowerSegment 247021824 247054592 (24700381898651 / 100000) (3087956702009 / 12500) := by
  exact
    packedTile16384 247021824 247054592 12 1693 15716 28 _ _ (1932497 / 100000) (773 / 40)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247054592 :
    ThetaLowerSegment 247054592 247087360 (3087956702009 / 12500) (6176729889493 / 25000) := by
  exact
    packedTile16384 247054592 247087360 12 1690 15717 28 _ _ (193251 / 10000) (1932513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247087360 :
    ThetaLowerSegment 247087360 247120128 (6176729889493 / 25000) (3088774398269 / 12500) := by
  exact
    packedTile16384 247087360 247120128 12 1695 15719 28 _ _ (483131 / 25000) (1932527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247120128 :
    ThetaLowerSegment 247120128 247152896 (3088774398269 / 12500) (6178350799393 / 25000) := by
  exact
    packedTile16384 247120128 247152896 12 1660 15720 28 _ _ (1932537 / 100000) (96627 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247152896 :
    ThetaLowerSegment 247152896 247185664 (6178350799393 / 25000) (12358364558061 / 50000) := by
  exact
    packedTile16384 247152896 247185664 12 1721 15721 28 _ _ (38651 / 2000) (1932553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247185664 :
    ThetaLowerSegment 247185664 247218432 (12358364558061 / 50000) (12359995642077 / 50000) := by
  exact
    packedTile16384 247185664 247218432 12 1688 15722 28 _ _ (483141 / 25000) (1932567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247218432 :
    ThetaLowerSegment 247218432 247251200 (12359995642077 / 50000) (4944629436479 / 20000) := by
  exact
    packedTile16384 247218432 247251200 12 1633 15723 28 _ _ (1932577 / 100000) (96629 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247251200 :
    ThetaLowerSegment 247251200 247283968 (4944629436479 / 20000) (989056684987 / 4000) := by
  exact
    packedTile16384 247251200 247283968 12 1692 15724 28 _ _ (193259 / 10000) (1932593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247283968 :
    ThetaLowerSegment 247283968 247316736 (989056684987 / 4000) (4945948240367 / 20000) := by
  exact
    packedTile16384 247283968 247316736 12 1720 15725 28 _ _ (1932603 / 100000) (966303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247316736 :
    ThetaLowerSegment 247316736 247349504 (4945948240367 / 20000) (2473309429233 / 10000) := by
  exact
    packedTile16384 247316736 247349504 12 1735 15726 28 _ _ (1932617 / 100000) (96631 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247349504 :
    ThetaLowerSegment 247349504 247382272 (2473309429233 / 10000) (24736397157 / 100) := by
  exact
    packedTile16384 247349504 247382272 12 1709 15727 28 _ _ (193263 / 10000) (1932633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247382272 :
    ThetaLowerSegment 247382272 247415040 (24736397157 / 100) (24739707774459 / 100000) := by
  exact
    packedTile16384 247382272 247415040 12 1713 15728 28 _ _ (1932643 / 100000) (966323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247415040 :
    ThetaLowerSegment 247415040 247447808 (24739707774459 / 100000) (24742964299819 / 100000) := by
  exact
    packedTile16384 247415040 247447808 12 1685 15729 28 _ _ (120791 / 6250) (1932659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247447808 :
    ThetaLowerSegment 247447808 247480576 (24742964299819 / 100000) (24746273030859 / 100000) := by
  exact
    packedTile16384 247447808 247480576 12 1712 15730 28 _ _ (193267 / 10000) (1932673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247480576 :
    ThetaLowerSegment 247480576 247513344 (24746273030859 / 100000) (24749516072933 / 100000) := by
  exact
    packedTile16384 247480576 247513344 12 1678 15731 28 _ _ (1932683 / 100000) (966343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247513344 :
    ThetaLowerSegment 247513344 247546112 (24749516072933 / 100000) (24752706954029 / 100000) := by
  exact
    packedTile16384 247513344 247546112 12 1651 15732 28 _ _ (241587 / 12500) (1932699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247546112 :
    ThetaLowerSegment 247546112 247578880 (24752706954029 / 100000) (12378016573109 / 50000) := by
  exact
    packedTile16384 247546112 247578880 12 1721 15733 28 _ _ (1932709 / 100000) (241589 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247578880 :
    ThetaLowerSegment 247578880 247611648 (12378016573109 / 50000) (773727684917 / 3125) := by
  exact
    packedTile16384 247578880 247611648 12 1683 15734 28 _ _ (966361 / 50000) (77309 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247611648 :
    ThetaLowerSegment 247611648 247644416 (773727684917 / 3125) (773830301119 / 3125) := by
  exact
    packedTile16384 247611648 247644416 12 1699 15735 28 _ _ (60398 / 3125) (1932739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247644416 :
    ThetaLowerSegment 247644416 247677184 (773830301119 / 3125) (12382917990809 / 50000) := by
  exact
    packedTile16384 247644416 247677184 12 1690 15736 28 _ _ (1932749 / 100000) (120797 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247677184 :
    ThetaLowerSegment 247677184 247709952 (12382917990809 / 50000) (3096137068889 / 12500) := by
  exact
    packedTile16384 247677184 247709952 12 1687 15737 28 _ _ (966381 / 50000) (386553 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247709952 :
    ThetaLowerSegment 247709952 247742720 (3096137068889 / 12500) (24772326218137 / 100000) := by
  exact
    packedTile16384 247709952 247742720 12 1671 15738 28 _ _ (77311 / 4000) (966389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247742720 :
    ThetaLowerSegment 247742720 247775488 (24772326218137 / 100000) (6193908305029 / 25000) := by
  exact
    packedTile16384 247742720 247775488 12 1711 15739 28 _ _ (1932789 / 100000) (241599 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247775488 :
    ThetaLowerSegment 247775488 247808256 (6193908305029 / 25000) (3097366322541 / 12500) := by
  exact
    packedTile16384 247775488 247808256 12 1706 15740 28 _ _ (966401 / 50000) (386561 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247808256 :
    ThetaLowerSegment 247808256 247841024 (3097366322541 / 12500) (12391098518839 / 50000) := by
  exact
    packedTile16384 247808256 247841024 12 1690 15741 28 _ _ (386563 / 20000) (966409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247841024 :
    ThetaLowerSegment 247841024 247873792 (12391098518839 / 50000) (12392731758499 / 50000) := by
  exact
    packedTile16384 247841024 247873792 12 1690 15742 28 _ _ (483207 / 25000) (1932831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247873792 :
    ThetaLowerSegment 247873792 247906560 (12392731758499 / 50000) (6197186853889 / 25000) := by
  exact
    packedTile16384 247873792 247906560 12 1699 15744 28 _ _ (966421 / 50000) (386569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247906560 :
    ThetaLowerSegment 247906560 247939328 (6197186853889 / 25000) (6197987055859 / 25000) := by
  exact
    packedTile16384 247906560 247939328 12 1656 15745 28 _ _ (386571 / 20000) (966429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247939328 :
    ThetaLowerSegment 247939328 247972096 (6197987055859 / 25000) (3099413685111 / 12500) := by
  exact
    packedTile16384 247939328 247972096 12 1739 15746 28 _ _ (483217 / 25000) (1932871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell247972096 :
    ThetaLowerSegment 247972096 248004864 (3099413685111 / 12500) (24798577982659 / 100000) := by
  exact
    packedTile16384 247972096 248004864 12 1691 15747 28 _ _ (1932881 / 100000) (483221 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248004864 :
    ThetaLowerSegment 248004864 248037632 (24798577982659 / 100000) (24801898694551 / 100000) := by
  exact
    packedTile16384 248004864 248037632 12 1718 15748 28 _ _ (966447 / 50000) (1932897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248037632 :
    ThetaLowerSegment 248037632 248070400 (24801898694551 / 100000) (24805099590199 / 100000) := by
  exact
    packedTile16384 248037632 248070400 12 1656 15749 28 _ _ (483227 / 25000) (1932911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248070400 :
    ThetaLowerSegment 248070400 248103168 (24805099590199 / 100000) (24808323702427 / 100000) := by
  exact
    packedTile16384 248070400 248103168 12 1668 15750 28 _ _ (1932921 / 100000) (483231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248103168 :
    ThetaLowerSegment 248103168 248135936 (24808323702427 / 100000) (24811636751303 / 100000) := by
  exact
    packedTile16384 248103168 248135936 12 1714 15751 28 _ _ (966467 / 50000) (1932937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248135936 :
    ThetaLowerSegment 248135936 248168704 (24811636751303 / 100000) (24814926627097 / 100000) := by
  exact
    packedTile16384 248135936 248168704 12 1702 15752 28 _ _ (1932947 / 100000) (38659 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248168704 :
    ThetaLowerSegment 248168704 248201472 (24814926627097 / 100000) (24818224256857 / 100000) := by
  exact
    packedTile16384 248168704 248201472 12 1706 15753 28 _ _ (12081 / 625) (1932963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248201472 :
    ThetaLowerSegment 248201472 248234240 (24818224256857 / 100000) (24821626291097 / 100000) := by
  exact
    packedTile16384 248201472 248234240 12 1760 15754 28 _ _ (966487 / 50000) (1932977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248234240 :
    ThetaLowerSegment 248234240 248267008 (24821626291097 / 100000) (6206218910561 / 25000) := by
  exact
    packedTile16384 248234240 248267008 12 1681 15755 28 _ _ (1932987 / 100000) (193299 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248267008 :
    ThetaLowerSegment 248267008 248299776 (6206218910561 / 25000) (6207056866061 / 25000) := by
  exact
    packedTile16384 248267008 248299776 12 1734 15756 28 _ _ (1933 / 100) (1933003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248299776 :
    ThetaLowerSegment 248299776 248332544 (6207056866061 / 25000) (3103935332267 / 12500) := by
  exact
    packedTile16384 248299776 248332544 12 1684 15757 28 _ _ (1933013 / 100000) (241627 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248332544 :
    ThetaLowerSegment 248332544 248365312 (3103935332267 / 12500) (3104343200753 / 12500) := by
  exact
    packedTile16384 248332544 248365312 12 1688 15758 28 _ _ (966513 / 50000) (1933029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248365312 :
    ThetaLowerSegment 248365312 248398080 (3104343200753 / 12500) (3104761703913 / 12500) := by
  exact
    packedTile16384 248365312 248398080 12 1732 15759 28 _ _ (24163 / 1250) (1933043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248398080 :
    ThetaLowerSegment 248398080 248430848 (3104761703913 / 12500) (24841339227291 / 100000) := by
  exact
    packedTile16384 248398080 248430848 12 1679 15760 28 _ _ (1933053 / 100000) (60408 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248430848 :
    ThetaLowerSegment 248430848 248463616 (24841339227291 / 100000) (24844550049917 / 100000) := by
  exact
    packedTile16384 248430848 248463616 12 1661 15761 28 _ _ (966533 / 50000) (1933069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248463616 :
    ThetaLowerSegment 248463616 248496384 (24844550049917 / 100000) (24847894276587 / 100000) := by
  exact
    packedTile16384 248463616 248496384 12 1730 15762 28 _ _ (1933079 / 100000) (966541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248496384 :
    ThetaLowerSegment 248496384 248529152 (24847894276587 / 100000) (24851143804239 / 100000) := by
  exact
    packedTile16384 248496384 248529152 12 1681 15763 28 _ _ (483273 / 25000) (386619 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248529152 :
    ThetaLowerSegment 248529152 248561920 (24851143804239 / 100000) (24854466813453 / 100000) := by
  exact
    packedTile16384 248529152 248561920 12 1719 15764 28 _ _ (966553 / 50000) (1933109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248561920 :
    ThetaLowerSegment 248561920 248594688 (24854466813453 / 100000) (12428867858841 / 50000) := by
  exact
    packedTile16384 248561920 248594688 12 1691 15765 28 _ _ (1933119 / 100000) (966561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248594688 :
    ThetaLowerSegment 248594688 248627456 (12428867858841 / 50000) (2486105877159 / 10000) := by
  exact
    packedTile16384 248594688 248627456 12 1719 15766 28 _ _ (483283 / 25000) (386627 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248627456 :
    ThetaLowerSegment 248627456 248660224 (2486105877159 / 10000) (4972874823053 / 20000) := by
  exact
    packedTile16384 248627456 248660224 12 1715 15767 28 _ _ (386629 / 20000) (483287 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248660224 :
    ThetaLowerSegment 248660224 248692992 (4972874823053 / 20000) (24867654684391 / 100000) := by
  exact
    packedTile16384 248660224 248692992 12 1697 15768 28 _ _ (966579 / 50000) (1933161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248692992 :
    ThetaLowerSegment 248692992 248725760 (24867654684391 / 100000) (621775411719 / 2500) := by
  exact
    packedTile16384 248692992 248725760 12 1739 15770 28 _ _ (1933171 / 100000) (966587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248725760 :
    ThetaLowerSegment 248725760 248758528 (621775411719 / 2500) (4974827712507 / 20000) := by
  exact
    packedTile16384 248725760 248758528 12 1615 15771 28 _ _ (386637 / 20000) (483297 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248758528 :
    ThetaLowerSegment 248758528 248791296 (4974827712507 / 20000) (24877411466749 / 100000) := by
  exact
    packedTile16384 248758528 248791296 12 1693 15772 28 _ _ (966599 / 50000) (1933201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248791296 :
    ThetaLowerSegment 248791296 248824064 (24877411466749 / 100000) (24880659261229 / 100000) := by
  exact
    packedTile16384 248791296 248824064 12 1680 15773 28 _ _ (1933211 / 100000) (966607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248824064 :
    ThetaLowerSegment 248824064 248856832 (24880659261229 / 100000) (24883889678533 / 100000) := by
  exact
    packedTile16384 248824064 248856832 12 1671 15774 28 _ _ (241653 / 12500) (1933227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248856832 :
    ThetaLowerSegment 248856832 248889600 (24883889678533 / 100000) (3110897747643 / 12500) := by
  exact
    packedTile16384 248856832 248889600 12 1703 15775 28 _ _ (1933237 / 100000) (48331 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248889600 :
    ThetaLowerSegment 248889600 248922368 (3110897747643 / 12500) (12445227486697 / 50000) := by
  exact
    packedTile16384 248889600 248922368 12 1693 15776 28 _ _ (7733 / 400) (1933253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248922368 :
    ThetaLowerSegment 248922368 248955136 (12445227486697 / 50000) (12446852395089 / 50000) := by
  exact
    packedTile16384 248922368 248955136 12 1681 15777 28 _ _ (120829 / 6250) (1933267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248955136 :
    ThetaLowerSegment 248955136 248987904 (12446852395089 / 50000) (1556062201727 / 6250) := by
  exact
    packedTile16384 248955136 248987904 12 1702 15778 28 _ _ (1933277 / 100000) (12083 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell248987904 :
    ThetaLowerSegment 248987904 249020672 (1556062201727 / 6250) (12450174742891 / 50000) := by
  exact
    packedTile16384 248987904 249020672 12 1735 15779 28 _ _ (193329 / 10000) (1933293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249020672 :
    ThetaLowerSegment 249020672 249053440 (12450174742891 / 50000) (311295112933 / 1250) := by
  exact
    packedTile16384 249020672 249053440 12 1686 15780 28 _ _ (1933303 / 100000) (966653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249053440 :
    ThetaLowerSegment 249053440 249086208 (311295112933 / 1250) (6226709901419 / 25000) := by
  exact
    packedTile16384 249053440 249086208 12 1671 15781 28 _ _ (483329 / 25000) (1933319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249086208 :
    ThetaLowerSegment 249086208 249118976 (6226709901419 / 25000) (24910182331517 / 100000) := by
  exact
    packedTile16384 249086208 249118976 12 1729 15782 28 _ _ (1933329 / 100000) (483333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249118976 :
    ThetaLowerSegment 249118976 249151744 (24910182331517 / 100000) (24913503814791 / 100000) := by
  exact
    packedTile16384 249118976 249151744 12 1718 15783 28 _ _ (1933343 / 100000) (966673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249151744 :
    ThetaLowerSegment 249151744 249184512 (24913503814791 / 100000) (4983359650683 / 20000) := by
  exact
    packedTile16384 249151744 249184512 12 1704 15784 28 _ _ (483339 / 25000) (1933359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249184512 :
    ThetaLowerSegment 249184512 249217280 (4983359650683 / 20000) (996802625881 / 4000) := by
  exact
    packedTile16384 249184512 249217280 12 1690 15785 28 _ _ (1933369 / 100000) (483343 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249217280 :
    ThetaLowerSegment 249217280 249250048 (996802625881 / 4000) (24923325329077 / 100000) := by
  exact
    packedTile16384 249217280 249250048 12 1686 15786 28 _ _ (966691 / 50000) (386677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249250048 :
    ThetaLowerSegment 249250048 249282816 (24923325329077 / 100000) (1557911927077 / 6250) := by
  exact
    packedTile16384 249250048 249282816 12 1689 15787 28 _ _ (386679 / 20000) (966699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249282816 :
    ThetaLowerSegment 249282816 249315584 (1557911927077 / 6250) (1558113726537 / 6250) := by
  exact
    packedTile16384 249282816 249315584 12 1670 15788 28 _ _ (60419 / 3125) (1933411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249315584 :
    ThetaLowerSegment 249315584 249348352 (1558113726537 / 6250) (3116646038937 / 12500) := by
  exact
    packedTile16384 249315584 249348352 12 1732 15789 28 _ _ (966711 / 50000) (77337 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249348352 :
    ThetaLowerSegment 249348352 249381120 (3116646038937 / 12500) (24936515087481 / 100000) := by
  exact
    packedTile16384 249348352 249381120 12 1731 15790 28 _ _ (386687 / 20000) (966719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249381120 :
    ThetaLowerSegment 249381120 249413888 (24936515087481 / 100000) (24939751679433 / 100000) := by
  exact
    packedTile16384 249381120 249413888 12 1674 15791 28 _ _ (241681 / 12500) (1933451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249413888 :
    ThetaLowerSegment 249413888 249446656 (24939751679433 / 100000) (12471485445999 / 50000) := by
  exact
    packedTile16384 249413888 249446656 12 1665 15792 28 _ _ (1933461 / 100000) (241683 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249446656 :
    ThetaLowerSegment 249446656 249479424 (12471485445999 / 50000) (6236550431763 / 25000) := by
  exact
    packedTile16384 249446656 249479424 12 1671 15793 28 _ _ (966737 / 50000) (1933477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249479424 :
    ThetaLowerSegment 249479424 249512192 (6236550431763 / 25000) (12474750127937 / 50000) := by
  exact
    packedTile16384 249479424 249512192 12 1706 15794 28 _ _ (1933487 / 100000) (193349 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249512192 :
    ThetaLowerSegment 249512192 249544960 (12474750127937 / 50000) (12476426472437 / 50000) := by
  exact
    packedTile16384 249512192 249544960 12 1734 15795 28 _ _ (3867 / 200) (1933503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249544960 :
    ThetaLowerSegment 249544960 249577728 (12476426472437 / 50000) (12478046756331 / 50000) := by
  exact
    packedTile16384 249544960 249577728 12 1676 15796 28 _ _ (1933513 / 100000) (483379 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249577728 :
    ThetaLowerSegment 249577728 249610496 (12478046756331 / 50000) (12479667051957 / 50000) := by
  exact
    packedTile16384 249577728 249610496 12 1676 15798 28 _ _ (1933527 / 100000) (193353 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249610496 :
    ThetaLowerSegment 249610496 249643264 (12479667051957 / 50000) (12481314428037 / 50000) := by
  exact
    packedTile16384 249610496 249643264 12 1704 15799 28 _ _ (96677 / 5000) (1933543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249643264 :
    ThetaLowerSegment 249643264 249676032 (12481314428037 / 50000) (24965886892879 / 100000) := by
  exact
    packedTile16384 249643264 249676032 12 1685 15800 28 _ _ (1933553 / 100000) (483389 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249676032 :
    ThetaLowerSegment 249676032 249708800 (24965886892879 / 100000) (4993840978427 / 20000) := by
  exact
    packedTile16384 249676032 249708800 12 1716 15801 28 _ _ (966783 / 50000) (1933569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249708800 :
    ThetaLowerSegment 249708800 249741568 (4993840978427 / 20000) (6243132178609 / 25000) := by
  exact
    packedTile16384 249708800 249741568 12 1719 15802 28 _ _ (1933579 / 100000) (966791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249741568 :
    ThetaLowerSegment 249741568 249774336 (6243132178609 / 25000) (6243929301911 / 25000) := by
  exact
    packedTile16384 249741568 249774336 12 1649 15803 28 _ _ (241699 / 12500) (386719 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249774336 :
    ThetaLowerSegment 249774336 249807104 (6243929301911 / 25000) (24978963730439 / 100000) := by
  exact
    packedTile16384 249774336 249807104 12 1679 15804 28 _ _ (386721 / 20000) (241701 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249807104 :
    ThetaLowerSegment 249807104 249839872 (24978963730439 / 100000) (24982266349983 / 100000) := by
  exact
    packedTile16384 249807104 249839872 12 1708 15805 28 _ _ (966809 / 50000) (1933621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249839872 :
    ThetaLowerSegment 249839872 249872640 (24982266349983 / 100000) (24985596064287 / 100000) := by
  exact
    packedTile16384 249839872 249872640 12 1722 15806 28 _ _ (60426 / 3125) (386727 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249872640 :
    ThetaLowerSegment 249872640 249905408 (24985596064287 / 100000) (12494421327121 / 50000) := by
  exact
    packedTile16384 249872640 249905408 12 1679 15807 28 _ _ (386729 / 20000) (120853 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249905408 :
    ThetaLowerSegment 249905408 249938176 (12494421327121 / 50000) (1562007996199 / 6250) := by
  exact
    packedTile16384 249905408 249938176 12 1699 15808 28 _ _ (966829 / 50000) (1933661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249938176 :
    ThetaLowerSegment 249938176 249970944 (1562007996199 / 6250) (12497721125639 / 50000) := by
  exact
    packedTile16384 249938176 249970944 12 1714 15809 28 _ _ (1933671 / 100000) (966837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell249970944 :
    ThetaLowerSegment 249970944 250003712 (12497721125639 / 50000) (12499336718621 / 50000) := by
  exact
    packedTile16384 249970944 250003712 12 1671 15810 28 _ _ (483421 / 25000) (1933687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250003712 :
    ThetaLowerSegment 250003712 250036480 (12499336718621 / 50000) (25001947186263 / 100000) := by
  exact
    packedTile16384 250003712 250036480 12 1693 15811 28 _ _ (1933697 / 100000) (19337 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250036480 :
    ThetaLowerSegment 250036480 250069248 (25001947186263 / 100000) (25005168747123 / 100000) := by
  exact
    packedTile16384 250036480 250069248 12 1666 15812 28 _ _ (193371 / 10000) (1933713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250069248 :
    ThetaLowerSegment 250069248 250102016 (25005168747123 / 100000) (25008429004101 / 100000) := by
  exact
    packedTile16384 250069248 250102016 12 1686 15813 28 _ _ (1933723 / 100000) (966863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250102016 :
    ThetaLowerSegment 250102016 250134784 (25008429004101 / 100000) (5002340950577 / 20000) := by
  exact
    packedTile16384 250102016 250134784 12 1694 15814 28 _ _ (241717 / 12500) (1933739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250134784 :
    ThetaLowerSegment 250134784 250167552 (5002340950577 / 20000) (5002990303827 / 20000) := by
  exact
    packedTile16384 250134784 250167552 12 1679 15815 28 _ _ (1547 / 80) (1933753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250167552 :
    ThetaLowerSegment 250167552 250200320 (5002990303827 / 20000) (12509159100259 / 50000) := by
  exact
    packedTile16384 250167552 250200320 12 1741 15816 28 _ _ (1933763 / 100000) (966883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250200320 :
    ThetaLowerSegment 250200320 250233088 (12509159100259 / 50000) (12510811511851 / 50000) := by
  exact
    packedTile16384 250200320 250233088 12 1709 15817 28 _ _ (120861 / 6250) (1933779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250233088 :
    ThetaLowerSegment 250233088 250265856 (12510811511851 / 50000) (5004953859681 / 20000) := by
  exact
    packedTile16384 250233088 250265856 12 1627 15818 28 _ _ (1933789 / 100000) (60431 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250265856 :
    ThetaLowerSegment 250265856 250298624 (5004953859681 / 20000) (25028112842063 / 100000) := by
  exact
    packedTile16384 250265856 250298624 12 1729 15819 28 _ _ (966901 / 50000) (386761 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250298624 :
    ThetaLowerSegment 250298624 250331392 (25028112842063 / 100000) (12515704998319 / 50000) := by
  exact
    packedTile16384 250298624 250331392 12 1705 15820 28 _ _ (386763 / 20000) (966909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250331392 :
    ThetaLowerSegment 250331392 250364160 (12515704998319 / 50000) (12517356487431 / 50000) := by
  exact
    packedTile16384 250331392 250364160 12 1708 15821 28 _ _ (483457 / 25000) (1933831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250364160 :
    ThetaLowerSegment 250364160 250396928 (12517356487431 / 50000) (6259516563789 / 25000) := by
  exact
    packedTile16384 250364160 250396928 12 1734 15822 28 _ _ (1933841 / 100000) (483461 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250396928 :
    ThetaLowerSegment 250396928 250429696 (6259516563789 / 25000) (12520633391763 / 50000) := by
  exact
    packedTile16384 250396928 250429696 12 1655 15823 28 _ _ (966927 / 50000) (1933857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250429696 :
    ThetaLowerSegment 250429696 250462464 (12520633391763 / 50000) (25044428656071 / 100000) := by
  exact
    packedTile16384 250429696 250462464 12 1635 15824 28 _ _ (1933867 / 100000) (193387 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250462464 :
    ThetaLowerSegment 250462464 250495232 (25044428656071 / 100000) (25047760731311 / 100000) := by
  exact
    packedTile16384 250462464 250495232 12 1723 15826 28 _ _ (48347 / 2500) (1933883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250495232 :
    ThetaLowerSegment 250495232 250528000 (25047760731311 / 100000) (25051042549429 / 100000) := by
  exact
    packedTile16384 250495232 250528000 12 1697 15827 28 _ _ (966947 / 50000) (1933897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250528000 :
    ThetaLowerSegment 250528000 250560768 (25051042549429 / 100000) (25054310852259 / 100000) := by
  exact
    packedTile16384 250528000 250560768 12 1690 15828 28 _ _ (1933907 / 100000) (193391 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250560768 :
    ThetaLowerSegment 250560768 250593536 (25054310852259 / 100000) (25057644930339 / 100000) := by
  exact
    packedTile16384 250560768 250593536 12 1724 15829 28 _ _ (12087 / 625) (1933923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250593536 :
    ThetaLowerSegment 250593536 250626304 (25057644930339 / 100000) (5012191164727 / 20000) := by
  exact
    packedTile16384 250593536 250626304 12 1712 15830 28 _ _ (1933933 / 100000) (120871 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250626304 :
    ThetaLowerSegment 250626304 250659072 (5012191164727 / 20000) (1002565099803 / 4000) := by
  exact
    packedTile16384 250626304 250659072 12 1640 15831 28 _ _ (966973 / 50000) (1933949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250659072 :
    ThetaLowerSegment 250659072 250691840 (1002565099803 / 4000) (200539321803 / 800) := by
  exact
    packedTile16384 250659072 250691840 12 1700 15832 28 _ _ (1933959 / 100000) (966981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250691840 :
    ThetaLowerSegment 250691840 250724608 (200539321803 / 800) (5014152199387 / 20000) := by
  exact
    packedTile16384 250691840 250724608 12 1730 15833 28 _ _ (483493 / 25000) (77359 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250724608 :
    ThetaLowerSegment 250724608 250757376 (5014152199387 / 20000) (2507403910151 / 10000) := by
  exact
    packedTile16384 250724608 250757376 12 1695 15834 28 _ _ (386797 / 20000) (483497 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250757376 :
    ThetaLowerSegment 250757376 250790144 (2507403910151 / 10000) (12538655713063 / 50000) := by
  exact
    packedTile16384 250757376 250790144 12 1692 15835 28 _ _ (966999 / 50000) (1934001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250790144 :
    ThetaLowerSegment 250790144 250822912 (12538655713063 / 50000) (25080547026529 / 100000) := by
  exact
    packedTile16384 250790144 250822912 12 1673 15836 28 _ _ (1934011 / 100000) (967007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250822912 :
    ThetaLowerSegment 250822912 250855680 (25080547026529 / 100000) (25083792318801 / 100000) := by
  exact
    packedTile16384 250822912 250855680 12 1678 15837 28 _ _ (241753 / 12500) (1934027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250855680 :
    ThetaLowerSegment 250855680 250888448 (25083792318801 / 100000) (25087126598589 / 100000) := by
  exact
    packedTile16384 250855680 250888448 12 1724 15838 28 _ _ (1934037 / 100000) (48351 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250888448 :
    ThetaLowerSegment 250888448 250921216 (25087126598589 / 100000) (25090455098639 / 100000) := by
  exact
    packedTile16384 250888448 250921216 12 1721 15839 28 _ _ (38681 / 2000) (1934053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250921216 :
    ThetaLowerSegment 250921216 250953984 (25090455098639 / 100000) (25093731401361 / 100000) := by
  exact
    packedTile16384 250921216 250953984 12 1694 15840 28 _ _ (1934063 / 100000) (967033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250953984 :
    ThetaLowerSegment 250953984 250986752 (25093731401361 / 100000) (5019400771929 / 20000) := by
  exact
    packedTile16384 250953984 250986752 12 1692 15841 28 _ _ (1934077 / 100000) (12088 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell250986752 :
    ThetaLowerSegment 250986752 251019520 (5019400771929 / 20000) (5020061843891 / 20000) := by
  exact
    packedTile16384 250986752 251019520 12 1709 15842 28 _ _ (193409 / 10000) (1934093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251019520 :
    ThetaLowerSegment 251019520 251052288 (5020061843891 / 20000) (25103581721731 / 100000) := by
  exact
    packedTile16384 251019520 251052288 12 1692 15843 28 _ _ (1934103 / 100000) (967053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251052288 :
    ThetaLowerSegment 251052288 251085056 (25103581721731 / 100000) (25106832970727 / 100000) := by
  exact
    packedTile16384 251052288 251085056 12 1681 15844 28 _ _ (483529 / 25000) (1934119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251085056 :
    ThetaLowerSegment 251085056 251117824 (25106832970727 / 100000) (627752879691 / 2500) := by
  exact
    packedTile16384 251085056 251117824 12 1697 15845 28 _ _ (1934129 / 100000) (483533 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251117824 :
    ThetaLowerSegment 251117824 251150592 (627752879691 / 2500) (2511343224117 / 10000) := by
  exact
    packedTile16384 251117824 251150592 12 1715 15846 28 _ _ (967071 / 50000) (386829 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251150592 :
    ThetaLowerSegment 251150592 251183360 (2511343224117 / 10000) (502332704037 / 2000) := by
  exact
    packedTile16384 251150592 251183360 12 1656 15847 28 _ _ (386831 / 20000) (967079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251183360 :
    ThetaLowerSegment 251183360 251216128 (502332704037 / 2000) (502399432833 / 2000) := by
  exact
    packedTile16384 251183360 251216128 12 1725 15848 28 _ _ (241771 / 12500) (1934171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251216128 :
    ThetaLowerSegment 251216128 251248896 (502399432833 / 2000) (12561618269589 / 50000) := by
  exact
    packedTile16384 251216128 251248896 12 1688 15849 28 _ _ (1934181 / 100000) (241773 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251248896 :
    ThetaLowerSegment 251248896 251281664 (12561618269589 / 50000) (2512646277477 / 10000) := by
  exact
    packedTile16384 251248896 251281664 12 1668 15850 28 _ _ (967097 / 50000) (1934197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251281664 :
    ThetaLowerSegment 251281664 251314432 (2512646277477 / 10000) (25129822492329 / 100000) := by
  exact
    packedTile16384 251281664 251314432 12 1737 15851 28 _ _ (1934207 / 100000) (193421 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251314432 :
    ThetaLowerSegment 251314432 251347200 (25129822492329 / 100000) (25133166758709 / 100000) := by
  exact
    packedTile16384 251314432 251347200 12 1729 15852 28 _ _ (96711 / 5000) (1934223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251347200 :
    ThetaLowerSegment 251347200 251379968 (25133166758709 / 100000) (25136462691741 / 100000) := by
  exact
    packedTile16384 251347200 251379968 12 1704 15853 28 _ _ (1934233 / 100000) (483559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251379968 :
    ThetaLowerSegment 251379968 251412736 (25136462691741 / 100000) (25139716093513 / 100000) := by
  exact
    packedTile16384 251379968 251412736 12 1682 15854 28 _ _ (967123 / 50000) (1934249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251412736 :
    ThetaLowerSegment 251412736 251445504 (25139716093513 / 100000) (25142984991223 / 100000) := by
  exact
    packedTile16384 251412736 251445504 12 1690 15856 28 _ _ (1934259 / 100000) (967131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251445504 :
    ThetaLowerSegment 251445504 251478272 (25142984991223 / 100000) (5029253103307 / 20000) := by
  exact
    packedTile16384 251445504 251478272 12 1696 15857 28 _ _ (60446 / 3125) (77371 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251478272 :
    ThetaLowerSegment 251478272 251511040 (5029253103307 / 20000) (2514953639247 / 10000) := by
  exact
    packedTile16384 251478272 251511040 12 1691 15858 28 _ _ (386857 / 20000) (120893 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251511040 :
    ThetaLowerSegment 251511040 251543808 (2514953639247 / 10000) (12576396875151 / 50000) := by
  exact
    packedTile16384 251511040 251543808 12 1684 15859 28 _ _ (967149 / 50000) (1934301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251543808 :
    ThetaLowerSegment 251543808 251576576 (12576396875151 / 50000) (25156103356423 / 100000) := by
  exact
    packedTile16384 251543808 251576576 12 1711 15860 28 _ _ (1934311 / 100000) (967157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251576576 :
    ThetaLowerSegment 251576576 251609344 (25156103356423 / 100000) (25159461342887 / 100000) := by
  exact
    packedTile16384 251576576 251609344 12 1736 15861 28 _ _ (483581 / 25000) (1934327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251609344 :
    ThetaLowerSegment 251609344 251642112 (25159461342887 / 100000) (25162703291699 / 100000) := by
  exact
    packedTile16384 251609344 251642112 12 1676 15862 28 _ _ (1934337 / 100000) (96717 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251642112 :
    ThetaLowerSegment 251642112 251674880 (25162703291699 / 100000) (25165925918799 / 100000) := by
  exact
    packedTile16384 251642112 251674880 12 1666 15863 28 _ _ (38687 / 2000) (1934353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251674880 :
    ThetaLowerSegment 251674880 251707648 (25165925918799 / 100000) (1573069972007 / 6250) := by
  exact
    packedTile16384 251674880 251707648 12 1651 15864 28 _ _ (1934363 / 100000) (967183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251707648 :
    ThetaLowerSegment 251707648 251740416 (1573069972007 / 6250) (1258614403 / 5) := by
  exact
    packedTile16384 251707648 251740416 12 1638 15865 28 _ _ (241797 / 12500) (1934379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251740416 :
    ThetaLowerSegment 251740416 251773184 (1258614403 / 5) (25175555243021 / 100000) := by
  exact
    packedTile16384 251740416 251773184 12 1689 15866 28 _ _ (1934389 / 100000) (241799 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251773184 :
    ThetaLowerSegment 251773184 251805952 (25175555243021 / 100000) (25178793431969 / 100000) := by
  exact
    packedTile16384 251773184 251805952 12 1674 15867 28 _ _ (967201 / 50000) (386881 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251805952 :
    ThetaLowerSegment 251805952 251838720 (25178793431969 / 100000) (6295493886161 / 25000) := by
  exact
    packedTile16384 251805952 251838720 12 1645 15868 28 _ _ (386883 / 20000) (967209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251838720 :
    ThetaLowerSegment 251838720 251871488 (6295493886161 / 25000) (6296316018061 / 25000) := by
  exact
    packedTile16384 251838720 251871488 12 1700 15869 28 _ _ (483607 / 25000) (1934431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251871488 :
    ThetaLowerSegment 251871488 251904256 (6296316018061 / 25000) (12594328540879 / 50000) := by
  exact
    packedTile16384 251871488 251904256 12 1754 15870 28 _ _ (1934441 / 100000) (483611 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251904256 :
    ThetaLowerSegment 251904256 251937024 (12594328540879 / 50000) (3148988128753 / 12500) := by
  exact
    packedTile16384 251904256 251937024 12 1679 15871 28 _ _ (967227 / 50000) (1934457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251937024 :
    ThetaLowerSegment 251937024 251969792 (3148988128753 / 12500) (25195137524381 / 100000) := by
  exact
    packedTile16384 251937024 251969792 12 1671 15872 28 _ _ (1934467 / 100000) (193447 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell251969792 :
    ThetaLowerSegment 251969792 252002560 (25195137524381 / 100000) (25198460961021 / 100000) := by
  exact
    packedTile16384 251969792 252002560 12 1718 15873 28 _ _ (24181 / 1250) (1934483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252002560 :
    ThetaLowerSegment 252002560 252035328 (25198460961021 / 100000) (25201811502897 / 100000) := by
  exact
    packedTile16384 252002560 252035328 12 1732 15874 28 _ _ (1934493 / 100000) (60453 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252035328 :
    ThetaLowerSegment 252035328 252068096 (25201811502897 / 100000) (25205055669459 / 100000) := by
  exact
    packedTile16384 252035328 252068096 12 1677 15875 28 _ _ (967253 / 50000) (1934509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252068096 :
    ThetaLowerSegment 252068096 252100864 (25205055669459 / 100000) (1575522368337 / 6250) := by
  exact
    packedTile16384 252068096 252100864 12 1707 15876 28 _ _ (1934519 / 100000) (967261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252100864 :
    ThetaLowerSegment 252100864 252133632 (1575522368337 / 6250) (6302898591357 / 25000) := by
  exact
    packedTile16384 252100864 252133632 12 1673 15877 28 _ _ (483633 / 25000) (386907 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252133632 :
    ThetaLowerSegment 252133632 252166400 (6302898591357 / 25000) (25214854073753 / 100000) := by
  exact
    packedTile16384 252133632 252166400 12 1685 15878 28 _ _ (386909 / 20000) (483637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252166400 :
    ThetaLowerSegment 252166400 252199168 (25214854073753 / 100000) (25218206662767 / 100000) := by
  exact
    packedTile16384 252166400 252199168 12 1733 15879 28 _ _ (967279 / 50000) (1934561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252199168 :
    ThetaLowerSegment 252199168 252231936 (25218206662767 / 100000) (25221541863171 / 100000) := by
  exact
    packedTile16384 252199168 252231936 12 1724 15880 28 _ _ (1934571 / 100000) (967287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252231936 :
    ThetaLowerSegment 252231936 252264704 (25221541863171 / 100000) (25224788095123 / 100000) := by
  exact
    packedTile16384 252231936 252264704 12 1678 15881 28 _ _ (241823 / 12500) (1934587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252264704 :
    ThetaLowerSegment 252264704 252297472 (25224788095123 / 100000) (25227980180173 / 100000) := by
  exact
    packedTile16384 252264704 252297472 12 1650 15882 28 _ _ (1934597 / 100000) (9673 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252297472 :
    ThetaLowerSegment 252297472 252330240 (25227980180173 / 100000) (25231286428663 / 100000) := by
  exact
    packedTile16384 252297472 252330240 12 1709 15883 28 _ _ (193461 / 10000) (1934613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252330240 :
    ThetaLowerSegment 252330240 252363008 (25231286428663 / 100000) (25234494033597 / 100000) := by
  exact
    packedTile16384 252330240 252363008 12 1658 15884 28 _ _ (1934623 / 100000) (967313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252363008 :
    ThetaLowerSegment 252363008 252395776 (25234494033597 / 100000) (5047563547649 / 20000) := by
  exact
    packedTile16384 252363008 252395776 12 1718 15885 28 _ _ (483659 / 25000) (1934639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252395776 :
    ThetaLowerSegment 252395776 252428544 (5047563547649 / 20000) (25241122118737 / 100000) := by
  exact
    packedTile16384 252395776 252428544 12 1708 15886 28 _ _ (1934649 / 100000) (483663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252428544 :
    ThetaLowerSegment 252428544 252461312 (25241122118737 / 100000) (25244325919009 / 100000) := by
  exact
    packedTile16384 252428544 252461312 12 1656 15888 28 _ _ (967331 / 50000) (386933 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252461312 :
    ThetaLowerSegment 252461312 252494080 (25244325919009 / 100000) (12623860636817 / 50000) := by
  exact
    packedTile16384 252461312 252494080 12 1755 15889 28 _ _ (77387 / 4000) (967339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252494080 :
    ThetaLowerSegment 252494080 252526848 (12623860636817 / 50000) (12625496415521 / 50000) := by
  exact
    packedTile16384 252494080 252526848 12 1691 15890 28 _ _ (60459 / 3125) (1934691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252526848 :
    ThetaLowerSegment 252526848 252559616 (12625496415521 / 50000) (157839479046 / 625) := by
  exact
    packedTile16384 252526848 252559616 12 1718 15891 28 _ _ (1934701 / 100000) (120919 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252559616 :
    ThetaLowerSegment 252559616 252592384 (157839479046 / 625) (12628784450797 / 50000) := by
  exact
    packedTile16384 252559616 252592384 12 1681 15892 28 _ _ (967357 / 50000) (1934717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252592384 :
    ThetaLowerSegment 252592384 252625152 (12628784450797 / 50000) (1010434549667 / 4000) := by
  exact
    packedTile16384 252592384 252625152 12 1703 15893 28 _ _ (1934727 / 100000) (193473 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252625152 :
    ThetaLowerSegment 252625152 252657920 (1010434549667 / 4000) (5052803086627 / 20000) := by
  exact
    packedTile16384 252625152 252657920 12 1629 15894 28 _ _ (96737 / 5000) (1934743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252657920 :
    ThetaLowerSegment 252657920 252690688 (5052803086627 / 20000) (25267242601139 / 100000) := by
  exact
    packedTile16384 252657920 252690688 12 1668 15895 28 _ _ (1934753 / 100000) (483689 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252690688 :
    ThetaLowerSegment 252690688 252723456 (25267242601139 / 100000) (25270537507637 / 100000) := by
  exact
    packedTile16384 252690688 252723456 12 1703 15896 28 _ _ (967383 / 50000) (1934769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252723456 :
    ThetaLowerSegment 252723456 252756224 (25270537507637 / 100000) (12636916218137 / 50000) := by
  exact
    packedTile16384 252723456 252756224 12 1703 15897 28 _ _ (1934779 / 100000) (967391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252756224 :
    ThetaLowerSegment 252756224 252788992 (12636916218137 / 50000) (2527704032141 / 10000) := by
  exact
    packedTile16384 252756224 252788992 12 1658 15898 28 _ _ (241849 / 12500) (386959 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252788992 :
    ThetaLowerSegment 252788992 252821760 (2527704032141 / 10000) (5056073250241 / 20000) := by
  exact
    packedTile16384 252788992 252821760 12 1719 15899 28 _ _ (386961 / 20000) (241851 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252821760 :
    ThetaLowerSegment 252821760 252854528 (5056073250241 / 20000) (25283657376623 / 100000) := by
  exact
    packedTile16384 252821760 252854528 12 1701 15900 28 _ _ (967409 / 50000) (1934821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252854528 :
    ThetaLowerSegment 252854528 252887296 (25283657376623 / 100000) (25286993025267 / 100000) := by
  exact
    packedTile16384 252854528 252887296 12 1724 15901 28 _ _ (1934831 / 100000) (967417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252887296 :
    ThetaLowerSegment 252887296 252920064 (25286993025267 / 100000) (25290197126931 / 100000) := by
  exact
    packedTile16384 252887296 252920064 12 1656 15902 28 _ _ (483711 / 25000) (1934847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252920064 :
    ThetaLowerSegment 252920064 252952832 (25290197126931 / 100000) (2529353862497 / 10000) := by
  exact
    packedTile16384 252920064 252952832 12 1727 15903 28 _ _ (1934857 / 100000) (96743 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252952832 :
    ThetaLowerSegment 252952832 252985600 (2529353862497 / 10000) (2529678920657 / 10000) := by
  exact
    packedTile16384 252952832 252985600 12 1680 15904 28 _ _ (193487 / 10000) (1934873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell252985600 :
    ThetaLowerSegment 252985600 253018368 (2529678920657 / 10000) (5059998287587 / 20000) := by
  exact
    packedTile16384 252985600 253018368 12 1655 15905 28 _ _ (1934883 / 100000) (967443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253018368 :
    ThetaLowerSegment 253018368 253051136 (5059998287587 / 20000) (25303269151759 / 100000) := by
  exact
    packedTile16384 253018368 253051136 12 1694 15906 28 _ _ (120931 / 6250) (1934899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253051136 :
    ThetaLowerSegment 253051136 253083904 (25303269151759 / 100000) (25306543017787 / 100000) := by
  exact
    packedTile16384 253051136 253083904 12 1692 15907 28 _ _ (1934909 / 100000) (60466 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253083904 :
    ThetaLowerSegment 253083904 253116672 (25306543017787 / 100000) (5061952545599 / 20000) := by
  exact
    packedTile16384 253083904 253116672 12 1664 15908 28 _ _ (967461 / 50000) (77397 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253116672 :
    ThetaLowerSegment 253116672 253149440 (5061952545599 / 20000) (2531309275113 / 10000) := by
  exact
    packedTile16384 253116672 253149440 12 1721 15909 28 _ _ (386987 / 20000) (967469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253149440 :
    ThetaLowerSegment 253149440 253182208 (2531309275113 / 10000) (12658187211469 / 50000) := by
  exact
    packedTile16384 253149440 253182208 12 1696 15910 28 _ _ (483737 / 25000) (1934951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253182208 :
    ThetaLowerSegment 253182208 253214976 (12658187211469 / 50000) (12659810642909 / 50000) := by
  exact
    packedTile16384 253182208 253214976 12 1678 15911 28 _ _ (24187 / 1250) (1934963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253214976 :
    ThetaLowerSegment 253214976 253247744 (12659810642909 / 50000) (25322885585269 / 100000) := by
  exact
    packedTile16384 253214976 253247744 12 1687 15912 28 _ _ (1934973 / 100000) (60468 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253247744 :
    ThetaLowerSegment 253247744 253280512 (25322885585269 / 100000) (25326209891217 / 100000) := by
  exact
    packedTile16384 253247744 253280512 12 1718 15913 28 _ _ (967493 / 50000) (1934989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253280512 :
    ThetaLowerSegment 253280512 253313280 (25326209891217 / 100000) (12664791297237 / 50000) := by
  exact
    packedTile16384 253280512 253313280 12 1743 15914 28 _ _ (1934999 / 100000) (967501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253313280 :
    ThetaLowerSegment 253313280 253346048 (12664791297237 / 50000) (12666445732497 / 50000) := by
  exact
    packedTile16384 253313280 253346048 12 1710 15915 28 _ _ (483753 / 25000) (387003 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253346048 :
    ThetaLowerSegment 253346048 253378816 (12666445732497 / 50000) (25336163592269 / 100000) := by
  exact
    packedTile16384 253346048 253378816 12 1691 15916 28 _ _ (77401 / 4000) (483757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253378816 :
    ThetaLowerSegment 253378816 253411584 (25336163592269 / 100000) (25339381560463 / 100000) := by
  exact
    packedTile16384 253378816 253411584 12 1663 15917 28 _ _ (967519 / 50000) (1935041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253411584 :
    ThetaLowerSegment 253411584 253444352 (25339381560463 / 100000) (25342682757469 / 100000) := by
  exact
    packedTile16384 253411584 253444352 12 1706 15918 28 _ _ (1935051 / 100000) (967527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253444352 :
    ThetaLowerSegment 253444352 253477120 (25342682757469 / 100000) (25345968496141 / 100000) := by
  exact
    packedTile16384 253444352 253477120 12 1698 15919 28 _ _ (241883 / 12500) (1935067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253477120 :
    ThetaLowerSegment 253477120 253509888 (25345968496141 / 100000) (25349292958427 / 100000) := by
  exact
    packedTile16384 253477120 253509888 12 1718 15920 28 _ _ (1935077 / 100000) (48377 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253509888 :
    ThetaLowerSegment 253509888 253542656 (25349292958427 / 100000) (25352512948187 / 100000) := by
  exact
    packedTile16384 253509888 253542656 12 1664 15921 28 _ _ (193509 / 10000) (1935093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253542656 :
    ThetaLowerSegment 253542656 253575424 (25352512948187 / 100000) (12677910019607 / 50000) := by
  exact
    packedTile16384 253542656 253575424 12 1709 15923 28 _ _ (1935103 / 100000) (967553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253575424 :
    ThetaLowerSegment 253575424 253608192 (12677910019607 / 50000) (12679576154483 / 50000) := by
  exact
    packedTile16384 253575424 253608192 12 1722 15924 28 _ _ (483779 / 25000) (1935119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253608192 :
    ThetaLowerSegment 253608192 253640960 (12679576154483 / 50000) (12681182311553 / 50000) := by
  exact
    packedTile16384 253608192 253640960 12 1660 15925 28 _ _ (1935129 / 100000) (483783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253640960 :
    ThetaLowerSegment 253640960 253673728 (12681182311553 / 50000) (2536563888337 / 10000) := by
  exact
    packedTile16384 253640960 253673728 12 1692 15926 28 _ _ (967571 / 50000) (387029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253673728 :
    ThetaLowerSegment 253673728 253706496 (2536563888337 / 10000) (12684384981271 / 50000) := by
  exact
    packedTile16384 253673728 253706496 12 1618 15927 28 _ _ (967577 / 50000) (1935157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253706496 :
    ThetaLowerSegment 253706496 253739264 (12684384981271 / 50000) (25372065551943 / 100000) := by
  exact
    packedTile16384 253706496 253739264 12 1703 15928 28 _ _ (1935167 / 100000) (193517 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253739264 :
    ThetaLowerSegment 253739264 253772032 (25372065551943 / 100000) (25375277950743 / 100000) := by
  exact
    packedTile16384 253739264 253772032 12 1660 15929 28 _ _ (96759 / 5000) (1935183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253772032 :
    ThetaLowerSegment 253772032 253804800 (25375277950743 / 100000) (25378606482703 / 100000) := by
  exact
    packedTile16384 253772032 253804800 12 1720 15930 28 _ _ (1935193 / 100000) (483799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253804800 :
    ThetaLowerSegment 253804800 253837568 (25378606482703 / 100000) (25381927296199 / 100000) := by
  exact
    packedTile16384 253804800 253837568 12 1716 15931 28 _ _ (967603 / 50000) (1935209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253837568 :
    ThetaLowerSegment 253837568 253870336 (25381927296199 / 100000) (25385213298061 / 100000) := by
  exact
    packedTile16384 253837568 253870336 12 1698 15932 28 _ _ (1935219 / 100000) (967611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253870336 :
    ThetaLowerSegment 253870336 253903104 (25385213298061 / 100000) (25388501257229 / 100000) := by
  exact
    packedTile16384 253870336 253903104 12 1699 15933 28 _ _ (60476 / 3125) (387047 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253903104 :
    ThetaLowerSegment 253903104 253935872 (25388501257229 / 100000) (12695931388897 / 50000) := by
  exact
    packedTile16384 253903104 253935872 12 1737 15934 28 _ _ (387049 / 20000) (120953 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253935872 :
    ThetaLowerSegment 253935872 253968640 (12695931388897 / 50000) (101580471527 / 400) := by
  exact
    packedTile16384 253935872 253968640 12 1682 15935 28 _ _ (967629 / 50000) (1935261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell253968640 :
    ThetaLowerSegment 253968640 254001408 (101580471527 / 400) (6349608734061 / 25000) := by
  exact
    packedTile16384 253968640 254001408 12 1714 15936 28 _ _ (1935271 / 100000) (967637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254001408 :
    ThetaLowerSegment 254001408 254034176 (6349608734061 / 25000) (6350417682773 / 25000) := by
  exact
    packedTile16384 254001408 254034176 12 1672 15937 28 _ _ (483821 / 25000) (1935287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254034176 :
    ThetaLowerSegment 254034176 254066944 (6350417682773 / 25000) (6351237280629 / 25000) := by
  exact
    packedTile16384 254034176 254066944 12 1694 15938 28 _ _ (60478 / 3125) (1935299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254066944 :
    ThetaLowerSegment 254066944 254099712 (6351237280629 / 25000) (794005054233 / 3125) := by
  exact
    packedTile16384 254066944 254099712 12 1660 15939 28 _ _ (1935309 / 100000) (120957 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254099712 :
    ThetaLowerSegment 254099712 254132480 (794005054233 / 3125) (317642469923 / 1250) := by
  exact
    packedTile16384 254099712 254132480 12 1672 15940 28 _ _ (967661 / 50000) (77413 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254132480 :
    ThetaLowerSegment 254132480 254165248 (317642469923 / 1250) (12707339961 / 50) := by
  exact
    packedTile16384 254132480 254165248 12 1696 15941 28 _ _ (387067 / 20000) (967669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254165248 :
    ThetaLowerSegment 254165248 254198016 (12707339961 / 50) (635449734177 / 2500) := by
  exact
    packedTile16384 254165248 254198016 12 1710 15942 28 _ _ (483837 / 25000) (1935351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254198016 :
    ThetaLowerSegment 254198016 254230784 (635449734177 / 2500) (12710657158639 / 50000) := by
  exact
    packedTile16384 254198016 254230784 12 1718 15943 28 _ _ (1935361 / 100000) (483841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254230784 :
    ThetaLowerSegment 254230784 254263552 (12710657158639 / 50000) (12712313838783 / 50000) := by
  exact
    packedTile16384 254230784 254263552 12 1712 15944 28 _ _ (967687 / 50000) (1935377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254263552 :
    ThetaLowerSegment 254263552 254296320 (12712313838783 / 50000) (25427861709243 / 100000) := by
  exact
    packedTile16384 254263552 254296320 12 1671 15945 28 _ _ (1935387 / 100000) (193539 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254296320 :
    ThetaLowerSegment 254296320 254329088 (25427861709243 / 100000) (25431066731643 / 100000) := by
  exact
    packedTile16384 254296320 254329088 12 1656 15946 28 _ _ (9677 / 500) (1935403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254329088 :
    ThetaLowerSegment 254329088 254361856 (25431066731643 / 100000) (25434459508879 / 100000) := by
  exact
    packedTile16384 254329088 254361856 12 1753 15947 28 _ _ (483853 / 25000) (387083 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254361856 :
    ThetaLowerSegment 254361856 254394624 (25434459508879 / 100000) (25437749731379 / 100000) := by
  exact
    packedTile16384 254361856 254394624 12 1700 15948 28 _ _ (77417 / 4000) (483857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254394624 :
    ThetaLowerSegment 254394624 254427392 (25437749731379 / 100000) (25441012879847 / 100000) := by
  exact
    packedTile16384 254394624 254427392 12 1686 15949 28 _ _ (967719 / 50000) (1935441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254427392 :
    ThetaLowerSegment 254427392 254460160 (25441012879847 / 100000) (25444326371959 / 100000) := by
  exact
    packedTile16384 254427392 254460160 12 1712 15950 28 _ _ (1935451 / 100000) (967727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254460160 :
    ThetaLowerSegment 254460160 254492928 (25444326371959 / 100000) (25447608918903 / 100000) := by
  exact
    packedTile16384 254460160 254492928 12 1696 15951 28 _ _ (241933 / 12500) (1935467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254492928 :
    ThetaLowerSegment 254492928 254525696 (25447608918903 / 100000) (12725437034301 / 50000) := by
  exact
    packedTile16384 254492928 254525696 12 1687 15952 28 _ _ (1935477 / 100000) (48387 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254525696 :
    ThetaLowerSegment 254525696 254558464 (12725437034301 / 50000) (3181771276009 / 12500) := by
  exact
    packedTile16384 254525696 254558464 12 1703 15953 28 _ _ (193549 / 10000) (1935493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254558464 :
    ThetaLowerSegment 254558464 254591232 (3181771276009 / 12500) (25457350239501 / 100000) := by
  exact
    packedTile16384 254558464 254591232 12 1643 15954 28 _ _ (1935503 / 100000) (967753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254591232 :
    ThetaLowerSegment 254591232 254624000 (25457350239501 / 100000) (6365187734839 / 25000) := by
  exact
    packedTile16384 254591232 254624000 12 1757 15955 28 _ _ (387103 / 20000) (967759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254624000 :
    ThetaLowerSegment 254624000 254656768 (6365187734839 / 25000) (1273200421649 / 5000) := by
  exact
    packedTile16384 254624000 254656768 12 1683 15956 28 _ _ (241941 / 12500) (1935531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254656768 :
    ThetaLowerSegment 254656768 254689536 (1273200421649 / 5000) (12733690072701 / 50000) := by
  exact
    packedTile16384 254656768 254689536 12 1742 15957 28 _ _ (1935541 / 100000) (241943 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254689536 :
    ThetaLowerSegment 254689536 254722304 (12733690072701 / 50000) (509411940723 / 2000) := by
  exact
    packedTile16384 254689536 254722304 12 1662 15958 28 _ _ (967777 / 50000) (1935557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254722304 :
    ThetaLowerSegment 254722304 254755072 (509411940723 / 2000) (6368459293827 / 25000) := by
  exact
    packedTile16384 254722304 254755072 12 1674 15960 28 _ _ (1935567 / 100000) (193557 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254755072 :
    ThetaLowerSegment 254755072 254787840 (6368459293827 / 25000) (6369270301847 / 25000) := by
  exact
    packedTile16384 254755072 254787840 12 1676 15961 28 _ _ (96779 / 5000) (1935583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254787840 :
    ThetaLowerSegment 254787840 254820608 (6369270301847 / 25000) (1019215565433 / 4000) := by
  exact
    packedTile16384 254787840 254820608 12 1709 15962 28 _ _ (1935593 / 100000) (483899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254820608 :
    ThetaLowerSegment 254820608 254853376 (1019215565433 / 4000) (5096741740023 / 20000) := by
  exact
    packedTile16384 254820608 254853376 12 1715 15963 28 _ _ (967803 / 50000) (1935609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254853376 :
    ThetaLowerSegment 254853376 254886144 (5096741740023 / 20000) (25487016671277 / 100000) := by
  exact
    packedTile16384 254853376 254886144 12 1709 15964 28 _ _ (967809 / 50000) (1935621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254886144 :
    ThetaLowerSegment 254886144 254918912 (25487016671277 / 100000) (5098049060757 / 20000) := by
  exact
    packedTile16384 254886144 254918912 12 1668 15965 28 _ _ (1935631 / 100000) (967817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254918912 :
    ThetaLowerSegment 254918912 254951680 (5098049060757 / 20000) (5098709115361 / 20000) := by
  exact
    packedTile16384 254918912 254951680 12 1705 15966 28 _ _ (483911 / 25000) (1935647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254951680 :
    ThetaLowerSegment 254951680 254984448 (5098709115361 / 20000) (12748391965483 / 50000) := by
  exact
    packedTile16384 254951680 254984448 12 1673 15967 28 _ _ (1935657 / 100000) (96783 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell254984448 :
    ThetaLowerSegment 254984448 255017216 (12748391965483 / 50000) (6375028804759 / 25000) := by
  exact
    packedTile16384 254984448 255017216 12 1721 15968 28 _ _ (193567 / 10000) (1935673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255017216 :
    ThetaLowerSegment 255017216 255049984 (6375028804759 / 25000) (6375849534351 / 25000) := by
  exact
    packedTile16384 255017216 255049984 12 1696 15969 28 _ _ (1935683 / 100000) (967843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255049984 :
    ThetaLowerSegment 255049984 255082752 (6375849534351 / 25000) (6376657687431 / 25000) := by
  exact
    packedTile16384 255049984 255082752 12 1670 15970 28 _ _ (120981 / 6250) (1935699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255082752 :
    ThetaLowerSegment 255082752 255115520 (6376657687431 / 25000) (6377477459769 / 25000) := by
  exact
    packedTile16384 255082752 255115520 12 1694 15971 28 _ _ (483927 / 25000) (1935711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255115520 :
    ThetaLowerSegment 255115520 255148288 (6377477459769 / 25000) (510263779009 / 2000) := by
  exact
    packedTile16384 255115520 255148288 12 1694 15972 28 _ _ (1935721 / 100000) (483931 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255148288 :
    ThetaLowerSegment 255148288 255181056 (510263779009 / 2000) (6379092340353 / 25000) := by
  exact
    packedTile16384 255148288 255181056 12 1643 15973 28 _ _ (967867 / 50000) (1935737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255181056 :
    ThetaLowerSegment 255181056 255213824 (6379092340353 / 25000) (25519665938553 / 100000) := by
  exact
    packedTile16384 255181056 255213824 12 1703 15974 28 _ _ (1935747 / 100000) (7743 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255213824 :
    ThetaLowerSegment 255213824 255246592 (25519665938553 / 100000) (25522958666313 / 100000) := by
  exact
    packedTile16384 255213824 255246592 12 1701 15975 28 _ _ (24197 / 1250) (1935763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255246592 :
    ThetaLowerSegment 255246592 255279360 (25522958666313 / 100000) (12763110221909 / 50000) := by
  exact
    packedTile16384 255246592 255279360 12 1685 15976 28 _ _ (1935773 / 100000) (60493 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255279360 :
    ThetaLowerSegment 255279360 255312128 (12763110221909 / 50000) (12764740152879 / 50000) := by
  exact
    packedTile16384 255279360 255312128 12 1684 15977 28 _ _ (387157 / 20000) (483947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255312128 :
    ThetaLowerSegment 255312128 255344896 (12764740152879 / 50000) (12766366223199 / 50000) := by
  exact
    packedTile16384 255312128 255344896 12 1680 15978 28 _ _ (967899 / 50000) (1935801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255344896 :
    ThetaLowerSegment 255344896 255377664 (12766366223199 / 50000) (25536118179837 / 100000) := by
  exact
    packedTile16384 255344896 255377664 12 1749 15979 28 _ _ (1935811 / 100000) (967907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255377664 :
    ThetaLowerSegment 255377664 255410432 (25536118179837 / 100000) (25539376171629 / 100000) := by
  exact
    packedTile16384 255377664 255410432 12 1683 15980 28 _ _ (120989 / 6250) (1935827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255410432 :
    ThetaLowerSegment 255410432 255443200 (25539376171629 / 100000) (12771338386857 / 50000) := by
  exact
    packedTile16384 255410432 255443200 12 1705 15981 28 _ _ (1935837 / 100000) (12099 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255443200 :
    ThetaLowerSegment 255443200 255475968 (12771338386857 / 50000) (6386492413641 / 25000) := by
  exact
    packedTile16384 255443200 255475968 12 1701 15982 28 _ _ (38717 / 2000) (1935853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255475968 :
    ThetaLowerSegment 255475968 255508736 (6386492413641 / 25000) (6387313219129 / 25000) := by
  exact
    packedTile16384 255475968 255508736 12 1696 15983 28 _ _ (967931 / 50000) (387173 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255508736 :
    ThetaLowerSegment 255508736 255541504 (6387313219129 / 25000) (12776262252633 / 50000) := by
  exact
    packedTile16384 255508736 255541504 12 1690 15984 28 _ _ (15487 / 800) (967939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255541504 :
    ThetaLowerSegment 255541504 255574272 (12776262252633 / 50000) (12777903885657 / 50000) := by
  exact
    packedTile16384 255541504 255574272 12 1696 15985 28 _ _ (120993 / 6250) (1935891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255574272 :
    ThetaLowerSegment 255574272 255607040 (12777903885657 / 50000) (5111816275981 / 20000) := by
  exact
    packedTile16384 255574272 255607040 12 1691 15986 28 _ _ (1935901 / 100000) (60497 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255607040 :
    ThetaLowerSegment 255607040 255639808 (5111816275981 / 20000) (5112482230397 / 20000) := by
  exact
    packedTile16384 255607040 255639808 12 1720 15987 28 _ _ (967957 / 50000) (1935917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255639808 :
    ThetaLowerSegment 255639808 255672576 (5112482230397 / 20000) (5113140445577 / 20000) := by
  exact
    packedTile16384 255639808 255672576 12 1700 15988 28 _ _ (1935927 / 100000) (193593 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255672576 :
    ThetaLowerSegment 255672576 255705344 (5113140445577 / 20000) (6392248815031 / 25000) := by
  exact
    packedTile16384 255672576 255705344 12 1701 15989 28 _ _ (1935939 / 100000) (967971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255705344 :
    ThetaLowerSegment 255705344 255738112 (6392248815031 / 25000) (255722147483 / 1000) := by
  exact
    packedTile16384 255705344 255738112 12 1663 15990 28 _ _ (120997 / 6250) (387191 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255738112 :
    ThetaLowerSegment 255738112 255770880 (255722147483 / 1000) (1023021397131 / 4000) := by
  exact
    packedTile16384 255738112 255770880 12 1715 15991 28 _ _ (387193 / 20000) (60499 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255770880 :
    ThetaLowerSegment 255770880 255803648 (1023021397131 / 4000) (25578822218919 / 100000) := by
  exact
    packedTile16384 255770880 255803648 12 1698 15992 28 _ _ (967989 / 50000) (1935981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255803648 :
    ThetaLowerSegment 255803648 255836416 (25578822218919 / 100000) (1023285775179 / 4000) := by
  exact
    packedTile16384 255803648 255836416 12 1716 15993 28 _ _ (1935991 / 100000) (967997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255836416 :
    ThetaLowerSegment 255836416 255869184 (1023285775179 / 4000) (25585423968557 / 100000) := by
  exact
    packedTile16384 255836416 255869184 12 1694 15994 28 _ _ (1936003 / 100000) (968003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255869184 :
    ThetaLowerSegment 255869184 255901952 (25585423968557 / 100000) (25588697771613 / 100000) := by
  exact
    packedTile16384 255869184 255901952 12 1691 15995 28 _ _ (121001 / 6250) (1936019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255901952 :
    ThetaLowerSegment 255901952 255934720 (25588697771613 / 100000) (12796003222587 / 50000) := by
  exact
    packedTile16384 255901952 255934720 12 1709 15996 28 _ _ (1936029 / 100000) (60501 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255934720 :
    ThetaLowerSegment 255934720 255967488 (12796003222587 / 50000) (1599706712299 / 6250) := by
  exact
    packedTile16384 255934720 255967488 12 1705 15997 28 _ _ (968021 / 50000) (387209 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell255967488 :
    ThetaLowerSegment 255967488 256033024 (1599706712299 / 6250) (25601740907549 / 100000) := by
  exact
    packedTile16384 255967488 256033024 13 3323 15998 28 _ _ (387211 / 20000) (968029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256033024 :
    ThetaLowerSegment 256033024 256065792 (25601740907549 / 100000) (25605005138429 / 100000) := by
  exact
    packedTile16384 256033024 256065792 12 1686 16001 28 _ _ (24201 / 1250) (1936083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256065792 :
    ThetaLowerSegment 256065792 256098560 (25605005138429 / 100000) (25608284879971 / 100000) := by
  exact
    packedTile16384 256065792 256098560 12 1694 16002 28 _ _ (1936093 / 100000) (60503 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256098560 :
    ThetaLowerSegment 256098560 256131328 (25608284879971 / 100000) (5122332289767 / 20000) := by
  exact
    packedTile16384 256098560 256131328 12 1744 16003 28 _ _ (968053 / 50000) (1936109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256131328 :
    ThetaLowerSegment 256131328 256164096 (5122332289767 / 20000) (25614937362183 / 100000) := by
  exact
    packedTile16384 256131328 256164096 12 1692 16004 28 _ _ (1936119 / 100000) (968061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256164096 :
    ThetaLowerSegment 256164096 256196864 (25614937362183 / 100000) (5123631042381 / 20000) := by
  exact
    packedTile16384 256164096 256196864 12 1662 16005 28 _ _ (1936131 / 100000) (968067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256196864 :
    ThetaLowerSegment 256196864 256229632 (5123631042381 / 20000) (25621462145857 / 100000) := by
  exact
    packedTile16384 256196864 256229632 12 1708 16006 28 _ _ (121009 / 6250) (1936147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256229632 :
    ThetaLowerSegment 256229632 256262400 (25621462145857 / 100000) (25624765229699 / 100000) := by
  exact
    packedTile16384 256229632 256262400 12 1706 16007 28 _ _ (1936157 / 100000) (12101 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256262400 :
    ThetaLowerSegment 256262400 256295168 (25624765229699 / 100000) (25628002505939 / 100000) := by
  exact
    packedTile16384 256262400 256295168 12 1672 16008 28 _ _ (193617 / 10000) (1936173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256295168 :
    ThetaLowerSegment 256295168 256327936 (25628002505939 / 100000) (5126244088417 / 20000) := by
  exact
    packedTile16384 256295168 256327936 12 1662 16009 28 _ _ (1936183 / 100000) (968093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256327936 :
    ThetaLowerSegment 256327936 256360704 (5126244088417 / 20000) (1281721048621 / 5000) := by
  exact
    packedTile16384 256327936 256360704 12 1653 16010 28 _ _ (387239 / 20000) (968099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256360704 :
    ThetaLowerSegment 256360704 256393472 (1281721048621 / 5000) (6409419902621 / 25000) := by
  exact
    packedTile16384 256360704 256393472 12 1683 16011 28 _ _ (121013 / 6250) (1936211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256393472 :
    ThetaLowerSegment 256393472 256426240 (6409419902621 / 25000) (6410229242999 / 25000) := by
  exact
    packedTile16384 256393472 256426240 12 1672 16012 28 _ _ (1936221 / 100000) (60507 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256426240 :
    ThetaLowerSegment 256426240 256459008 (6410229242999 / 25000) (12822103316781 / 50000) := by
  exact
    packedTile16384 256426240 256459008 12 1699 16013 28 _ _ (968117 / 50000) (1936237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256459008 :
    ThetaLowerSegment 256459008 256491776 (12822103316781 / 50000) (2564743629189 / 10000) := by
  exact
    packedTile16384 256459008 256491776 12 1668 16014 28 _ _ (968123 / 50000) (1936249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256491776 :
    ThetaLowerSegment 256491776 256524544 (2564743629189 / 10000) (6412659716069 / 25000) := by
  exact
    packedTile16384 256491776 256524544 12 1654 16015 28 _ _ (1936259 / 100000) (968131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256524544 :
    ThetaLowerSegment 256524544 256557312 (6412659716069 / 25000) (6413469561833 / 25000) := by
  exact
    packedTile16384 256524544 256557312 12 1673 16016 28 _ _ (121017 / 6250) (77451 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256557312 :
    ThetaLowerSegment 256557312 256590080 (6413469561833 / 25000) (12828544303931 / 50000) := by
  exact
    packedTile16384 256557312 256590080 12 1658 16017 28 _ _ (387257 / 20000) (60509 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256590080 :
    ThetaLowerSegment 256590080 256622848 (12828544303931 / 50000) (2566033384331 / 10000) := by
  exact
    packedTile16384 256590080 256622848 12 1676 16018 28 _ _ (968149 / 50000) (1936301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256622848 :
    ThetaLowerSegment 256622848 256655616 (2566033384331 / 10000) (513272279049 / 2000) := by
  exact
    packedTile16384 256622848 256655616 12 1694 16019 28 _ _ (193631 / 10000) (1936313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256655616 :
    ThetaLowerSegment 256655616 256688384 (513272279049 / 2000) (12833468341359 / 50000) := by
  exact
    packedTile16384 256655616 256688384 12 1716 16020 28 _ _ (1936323 / 100000) (968163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256688384 :
    ThetaLowerSegment 256688384 256721152 (12833468341359 / 50000) (12835097768103 / 50000) := by
  exact
    packedTile16384 256688384 256721152 12 1683 16021 28 _ _ (121021 / 6250) (1936339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256721152 :
    ThetaLowerSegment 256721152 256753920 (12835097768103 / 50000) (3209181559403 / 12500) := by
  exact
    packedTile16384 256721152 256753920 12 1682 16022 28 _ _ (1936349 / 100000) (60511 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256753920 :
    ThetaLowerSegment 256753920 256786688 (3209181559403 / 12500) (12838362462657 / 50000) := by
  exact
    packedTile16384 256753920 256786688 12 1690 16023 28 _ _ (1936361 / 100000) (484091 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256786688 :
    ThetaLowerSegment 256786688 256819456 (12838362462657 / 50000) (3210003305373 / 12500) := by
  exact
    packedTile16384 256786688 256819456 12 1705 16024 28 _ _ (968187 / 50000) (1936377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256819456 :
    ThetaLowerSegment 256819456 256852224 (3210003305373 / 12500) (6420806338577 / 25000) := by
  exact
    packedTile16384 256819456 256852224 12 1652 16025 28 _ _ (1936387 / 100000) (193639 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256852224 :
    ThetaLowerSegment 256852224 256884992 (6420806338577 / 25000) (6421618658377 / 25000) := by
  exact
    packedTile16384 256852224 256884992 12 1678 16026 28 _ _ (4841 / 250) (1936403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256884992 :
    ThetaLowerSegment 256884992 256917760 (6421618658377 / 25000) (6422461965803 / 25000) := by
  exact
    packedTile16384 256884992 256917760 12 1742 16027 28 _ _ (484103 / 25000) (387283 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256917760 :
    ThetaLowerSegment 256917760 256950528 (6422461965803 / 25000) (12846579574981 / 50000) := by
  exact
    packedTile16384 256917760 256950528 12 1710 16028 28 _ _ (77457 / 4000) (484107 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256950528 :
    ThetaLowerSegment 256950528 256983296 (12846579574981 / 50000) (12848210055777 / 50000) := by
  exact
    packedTile16384 256950528 256983296 12 1684 16029 28 _ _ (968219 / 50000) (1936441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell256983296 :
    ThetaLowerSegment 256983296 257016064 (12848210055777 / 50000) (12849894768147 / 50000) := by
  exact
    packedTile16384 256983296 257016064 12 1740 16030 28 _ _ (1936451 / 100000) (968227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257016064 :
    ThetaLowerSegment 257016064 257048832 (12849894768147 / 50000) (6425773285543 / 25000) := by
  exact
    packedTile16384 257016064 257048832 12 1706 16031 28 _ _ (1936463 / 100000) (968233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257048832 :
    ThetaLowerSegment 257048832 257081600 (6425773285543 / 25000) (3213295481267 / 12500) := by
  exact
    packedTile16384 257048832 257081600 12 1689 16032 28 _ _ (484119 / 25000) (1936479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257081600 :
    ThetaLowerSegment 257081600 257114368 (3213295481267 / 12500) (6427406224403 / 25000) := by
  exact
    packedTile16384 257081600 257114368 12 1684 16033 28 _ _ (1936489 / 100000) (484123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257114368 :
    ThetaLowerSegment 257114368 257147136 (6427406224403 / 25000) (12856449761247 / 50000) := by
  exact
    packedTile16384 257114368 257147136 12 1691 16034 28 _ _ (968251 / 50000) (387301 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257147136 :
    ThetaLowerSegment 257147136 257179904 (12856449761247 / 50000) (12858113226773 / 50000) := by
  exact
    packedTile16384 257147136 257179904 12 1718 16035 28 _ _ (968257 / 50000) (1936517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257179904 :
    ThetaLowerSegment 257179904 257212672 (12858113226773 / 50000) (2571954178777 / 10000) := by
  exact
    packedTile16384 257179904 257212672 12 1712 16036 28 _ _ (1936527 / 100000) (193653 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257212672 :
    ThetaLowerSegment 257212672 257245440 (2571954178777 / 10000) (2572279711151 / 10000) := by
  exact
    packedTile16384 257212672 257245440 12 1681 16037 28 _ _ (96827 / 5000) (1936543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257245440 :
    ThetaLowerSegment 257245440 257278208 (2572279711151 / 10000) (8232351659 / 32) := by
  exact
    packedTile16384 257245440 257278208 12 1705 16038 28 _ _ (1936553 / 100000) (484139 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257278208 :
    ThetaLowerSegment 257278208 257310976 (8232351659 / 32) (5145880542853 / 20000) := by
  exact
    packedTile16384 257278208 257310976 12 1706 16039 28 _ _ (387313 / 20000) (242071 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257310976 :
    ThetaLowerSegment 257310976 257343744 (5145880542853 / 20000) (1029305471981 / 4000) := by
  exact
    packedTile16384 257310976 257343744 12 1670 16040 28 _ _ (968289 / 50000) (1936581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257343744 :
    ThetaLowerSegment 257343744 257376512 (1029305471981 / 4000) (25735886399223 / 100000) := by
  exact
    packedTile16384 257343744 257376512 12 1678 16041 28 _ _ (1936591 / 100000) (968297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257376512 :
    ThetaLowerSegment 257376512 257409280 (25735886399223 / 100000) (25739172816211 / 100000) := by
  exact
    packedTile16384 257376512 257409280 12 1697 16042 28 _ _ (484151 / 25000) (1936607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257409280 :
    ThetaLowerSegment 257409280 257442048 (25739172816211 / 100000) (25742478619723 / 100000) := by
  exact
    packedTile16384 257409280 257442048 12 1707 16043 28 _ _ (242077 / 12500) (1936619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257442048 :
    ThetaLowerSegment 257442048 257474816 (25742478619723 / 100000) (6436423840123 / 25000) := by
  exact
    packedTile16384 257442048 257474816 12 1661 16045 28 _ _ (1936629 / 100000) (242079 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257474816 :
    ThetaLowerSegment 257474816 257507584 (6436423840123 / 25000) (6437252722899 / 25000) := by
  exact
    packedTile16384 257474816 257507584 12 1712 16046 28 _ _ (968321 / 50000) (387329 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257507584 :
    ThetaLowerSegment 257507584 257540352 (6437252722899 / 25000) (2575236323967 / 10000) := by
  exact
    packedTile16384 257507584 257540352 12 1731 16047 28 _ _ (968327 / 50000) (1936657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257540352 :
    ThetaLowerSegment 257540352 257573120 (2575236323967 / 10000) (25755688496909 / 100000) := by
  exact
    packedTile16384 257540352 257573120 12 1717 16048 28 _ _ (1936667 / 100000) (193667 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257573120 :
    ThetaLowerSegment 257573120 257605888 (25755688496909 / 100000) (25758955676069 / 100000) := by
  exact
    packedTile16384 257573120 257605888 12 1687 16049 28 _ _ (48417 / 2500) (1936683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257605888 :
    ThetaLowerSegment 257605888 257638656 (25758955676069 / 100000) (6440561529369 / 25000) := by
  exact
    packedTile16384 257605888 257638656 12 1699 16050 28 _ _ (1936693 / 100000) (242087 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257638656 :
    ThetaLowerSegment 257638656 257671424 (6440561529369 / 25000) (12882747954233 / 50000) := by
  exact
    packedTile16384 257638656 257671424 12 1678 16051 28 _ _ (387341 / 20000) (484177 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257671424 :
    ThetaLowerSegment 257671424 257704192 (12882747954233 / 50000) (2576878445563 / 10000) := by
  exact
    packedTile16384 257671424 257704192 12 1698 16052 28 _ _ (968359 / 50000) (1936721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257704192 :
    ThetaLowerSegment 257704192 257736960 (2576878445563 / 10000) (25771997492359 / 100000) := by
  exact
    packedTile16384 257704192 257736960 12 1659 16053 28 _ _ (1936731 / 100000) (968367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257736960 :
    ThetaLowerSegment 257736960 257769728 (25771997492359 / 100000) (25775266716231 / 100000) := by
  exact
    packedTile16384 257736960 257769728 12 1688 16054 28 _ _ (242093 / 12500) (1936747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257769728 :
    ThetaLowerSegment 257769728 257802496 (25775266716231 / 100000) (5155709516179 / 20000) := by
  exact
    packedTile16384 257769728 257802496 12 1694 16055 28 _ _ (484189 / 25000) (1936759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257802496 :
    ThetaLowerSegment 257802496 257835264 (5155709516179 / 20000) (12890911328637 / 50000) := by
  exact
    packedTile16384 257802496 257835264 12 1691 16056 28 _ _ (1936769 / 100000) (484193 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257835264 :
    ThetaLowerSegment 257835264 257868032 (12890911328637 / 50000) (3223140608823 / 12500) := by
  exact
    packedTile16384 257835264 257868032 12 1705 16057 28 _ _ (968391 / 50000) (387357 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257868032 :
    ThetaLowerSegment 257868032 257900800 (3223140608823 / 12500) (1289418353187 / 5000) := by
  exact
    packedTile16384 257868032 257900800 12 1674 16058 28 _ _ (968397 / 50000) (1936797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257900800 :
    ThetaLowerSegment 257900800 257933568 (1289418353187 / 5000) (5158318369479 / 20000) := by
  exact
    packedTile16384 257900800 257933568 12 1665 16059 28 _ _ (1936807 / 100000) (193681 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257933568 :
    ThetaLowerSegment 257933568 257966336 (5158318369479 / 20000) (1031796849639 / 4000) := by
  exact
    packedTile16384 257933568 257966336 12 1719 16060 28 _ _ (96841 / 5000) (1936823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257966336 :
    ThetaLowerSegment 257966336 257999104 (1031796849639 / 4000) (25798231286863 / 100000) := by
  exact
    packedTile16384 257966336 257999104 12 1709 16061 28 _ _ (60526 / 3125) (387367 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell257999104 :
    ThetaLowerSegment 257999104 258031872 (25798231286863 / 100000) (6450379528207 / 25000) := by
  exact
    packedTile16384 257999104 258031872 12 1697 16062 28 _ _ (387369 / 20000) (121053 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258031872 :
    ThetaLowerSegment 258031872 258064640 (6450379528207 / 25000) (12902344374687 / 50000) := by
  exact
    packedTile16384 258031872 258064640 12 1637 16063 28 _ _ (968429 / 50000) (1936861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258064640 :
    ThetaLowerSegment 258064640 258097408 (12902344374687 / 50000) (6451990515341 / 25000) := by
  exact
    packedTile16384 258064640 258097408 12 1690 16064 28 _ _ (1936871 / 100000) (968437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258097408 :
    ThetaLowerSegment 258097408 258130176 (6451990515341 / 25000) (12905602201753 / 50000) := by
  exact
    packedTile16384 258097408 258130176 12 1674 16065 28 _ _ (1936883 / 100000) (968443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258130176 :
    ThetaLowerSegment 258130176 258162944 (12905602201753 / 50000) (12907289238169 / 50000) := by
  exact
    packedTile16384 258130176 258162944 12 1742 16066 28 _ _ (60528 / 3125) (1936899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258162944 :
    ThetaLowerSegment 258162944 258195712 (12907289238169 / 50000) (806808596733 / 3125) := by
  exact
    packedTile16384 258162944 258195712 12 1702 16067 28 _ _ (1936909 / 100000) (121057 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258195712 :
    ThetaLowerSegment 258195712 258228480 (806808596733 / 3125) (25821150428867 / 100000) := by
  exact
    packedTile16384 258195712 258228480 12 1691 16068 28 _ _ (1936921 / 100000) (484231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258228480 :
    ThetaLowerSegment 258228480 258261248 (25821150428867 / 100000) (25824480018413 / 100000) := by
  exact
    packedTile16384 258228480 258261248 12 1719 16069 28 _ _ (968467 / 50000) (1936937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258261248 :
    ThetaLowerSegment 258261248 258294016 (25824480018413 / 100000) (6456928195739 / 25000) := by
  exact
    packedTile16384 258261248 258294016 12 1669 16070 28 _ _ (1936947 / 100000) (38739 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258294016 :
    ThetaLowerSegment 258294016 258326784 (6456928195739 / 25000) (2583097849583 / 10000) := by
  exact
    packedTile16384 258294016 258326784 12 1686 16071 28 _ _ (1936959 / 100000) (968481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258326784 :
    ThetaLowerSegment 258326784 258359552 (2583097849583 / 10000) (12917138579573 / 50000) := by
  exact
    packedTile16384 258326784 258359552 12 1703 16072 28 _ _ (484243 / 25000) (77479 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258359552 :
    ThetaLowerSegment 258359552 258392320 (12917138579573 / 50000) (6459387665949 / 25000) := by
  exact
    packedTile16384 258359552 258392320 12 1690 16073 28 _ _ (387397 / 20000) (484247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258392320 :
    ThetaLowerSegment 258392320 258425088 (6459387665949 / 25000) (5168159801553 / 20000) := by
  exact
    packedTile16384 258392320 258425088 12 1677 16074 28 _ _ (1936997 / 100000) (1937 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258425088 :
    ThetaLowerSegment 258425088 258457856 (5168159801553 / 20000) (5168814510933 / 20000) := by
  exact
    packedTile16384 258425088 258457856 12 1690 16075 28 _ _ (193701 / 10000) (1937013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258457856 :
    ThetaLowerSegment 258457856 258490624 (5168814510933 / 20000) (12923654660049 / 50000) := by
  exact
    packedTile16384 258457856 258490624 12 1671 16076 28 _ _ (1937023 / 100000) (968513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258490624 :
    ThetaLowerSegment 258490624 258523392 (12923654660049 / 50000) (12925305013869 / 50000) := by
  exact
    packedTile16384 258490624 258523392 12 1704 16077 28 _ _ (387407 / 20000) (968519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258523392 :
    ThetaLowerSegment 258523392 258556160 (12925305013869 / 50000) (12926914700757 / 50000) := by
  exact
    packedTile16384 258523392 258556160 12 1662 16078 28 _ _ (242131 / 12500) (1937051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258556160 :
    ThetaLowerSegment 258556160 258588928 (12926914700757 / 50000) (3232144659039 / 12500) := by
  exact
    packedTile16384 258556160 258588928 12 1718 16079 28 _ _ (1937061 / 100000) (242133 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258588928 :
    ThetaLowerSegment 258588928 258621696 (3232144659039 / 12500) (12930243551259 / 50000) := by
  exact
    packedTile16384 258588928 258621696 12 1719 16080 28 _ _ (968537 / 50000) (1937077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258621696 :
    ThetaLowerSegment 258621696 258654464 (12930243551259 / 50000) (129318774833 / 500) := by
  exact
    packedTile16384 258621696 258654464 12 1687 16081 28 _ _ (968543 / 50000) (1937089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258654464 :
    ThetaLowerSegment 258654464 258687232 (129318774833 / 500) (25867007355821 / 100000) := by
  exact
    packedTile16384 258654464 258687232 12 1679 16082 28 _ _ (1937099 / 100000) (968551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258687232 :
    ThetaLowerSegment 258687232 258720000 (25867007355821 / 100000) (25870368245141 / 100000) := by
  exact
    packedTile16384 258687232 258720000 12 1735 16083 28 _ _ (242139 / 12500) (387423 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258720000 :
    ThetaLowerSegment 258720000 258752768 (25870368245141 / 100000) (25873589682353 / 100000) := by
  exact
    packedTile16384 258720000 258752768 12 1663 16084 28 _ _ (484281 / 25000) (1937127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258752768 :
    ThetaLowerSegment 258752768 258785536 (25873589682353 / 100000) (25876867318157 / 100000) := by
  exact
    packedTile16384 258752768 258785536 12 1692 16085 28 _ _ (1937137 / 100000) (96857 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258785536 :
    ThetaLowerSegment 258785536 258818304 (25876867318157 / 100000) (25880098484357 / 100000) := by
  exact
    packedTile16384 258785536 258818304 12 1668 16086 28 _ _ (38743 / 2000) (1937153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258818304 :
    ThetaLowerSegment 258818304 258851072 (25880098484357 / 100000) (25883430402997 / 100000) := by
  exact
    packedTile16384 258818304 258851072 12 1720 16087 28 _ _ (968581 / 50000) (387433 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258851072 :
    ThetaLowerSegment 258851072 258883840 (25883430402997 / 100000) (25886708103097 / 100000) := by
  exact
    packedTile16384 258851072 258883840 12 1692 16088 28 _ _ (77487 / 4000) (968589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258883840 :
    ThetaLowerSegment 258883840 258916608 (25886708103097 / 100000) (25890067187089 / 100000) := by
  exact
    packedTile16384 258883840 258916608 12 1734 16089 28 _ _ (484297 / 25000) (1937191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258916608 :
    ThetaLowerSegment 258916608 258949376 (25890067187089 / 100000) (25893282939089 / 100000) := by
  exact
    packedTile16384 258916608 258949376 12 1660 16090 28 _ _ (4843 / 250) (1937203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258949376 :
    ThetaLowerSegment 258949376 258982144 (25893282939089 / 100000) (809265524233 / 3125) := by
  exact
    packedTile16384 258949376 258982144 12 1659 16091 28 _ _ (1937213 / 100000) (60538 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell258982144 :
    ThetaLowerSegment 258982144 259014912 (809265524233 / 3125) (12949854347253 / 50000) := by
  exact
    packedTile16384 258982144 259014912 12 1658 16092 28 _ _ (77489 / 4000) (484307 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259014912 :
    ThetaLowerSegment 259014912 259047680 (12949854347253 / 50000) (12951506811267 / 50000) := by
  exact
    packedTile16384 259014912 259047680 12 1706 16093 28 _ _ (968619 / 50000) (1937241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259047680 :
    ThetaLowerSegment 259047680 259080448 (12951506811267 / 50000) (3238288852967 / 12500) := by
  exact
    packedTile16384 259047680 259080448 12 1702 16094 28 _ _ (1937251 / 100000) (968627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259080448 :
    ThetaLowerSegment 259080448 259113216 (3238288852967 / 12500) (25909555739261 / 100000) := by
  exact
    packedTile16384 259080448 259113216 12 1675 16095 28 _ _ (1937263 / 100000) (968633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259113216 :
    ThetaLowerSegment 259113216 259145984 (25909555739261 / 100000) (25912843296633 / 100000) := by
  exact
    packedTile16384 259113216 259145984 12 1697 16096 28 _ _ (484319 / 25000) (1937279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259145984 :
    ThetaLowerSegment 259145984 259178752 (25912843296633 / 100000) (2591608438113 / 10000) := by
  exact
    packedTile16384 259145984 259178752 12 1673 16098 28 _ _ (1937289 / 100000) (484323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259178752 :
    ThetaLowerSegment 259178752 259211520 (2591608438113 / 10000) (1619958448263 / 6250) := by
  exact
    packedTile16384 259178752 259211520 12 1678 16099 28 _ _ (1937301 / 100000) (242163 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259211520 :
    ThetaLowerSegment 259211520 259244288 (1619958448263 / 6250) (12961321083603 / 50000) := by
  exact
    packedTile16384 259211520 259244288 12 1707 16100 28 _ _ (968657 / 50000) (1937317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259244288 :
    ThetaLowerSegment 259244288 259277056 (12961321083603 / 50000) (25926018928167 / 100000) := by
  exact
    packedTile16384 259244288 259277056 12 1743 16101 28 _ _ (1937327 / 100000) (193733 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259277056 :
    ThetaLowerSegment 259277056 259309824 (25926018928167 / 100000) (25929327903179 / 100000) := by
  exact
    packedTile16384 259277056 259309824 12 1708 16102 28 _ _ (1937339 / 100000) (968671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259309824 :
    ThetaLowerSegment 259309824 259342592 (25929327903179 / 100000) (25932603965411 / 100000) := by
  exact
    packedTile16384 259309824 259342592 12 1691 16103 28 _ _ (242169 / 12500) (387471 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259342592 :
    ThetaLowerSegment 259342592 259375360 (25932603965411 / 100000) (25935897485911 / 100000) := by
  exact
    packedTile16384 259342592 259375360 12 1700 16104 28 _ _ (387473 / 20000) (242171 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259375360 :
    ThetaLowerSegment 259375360 259408128 (25935897485911 / 100000) (1621201981983 / 6250) := by
  exact
    packedTile16384 259375360 259408128 12 1721 16105 28 _ _ (1937377 / 100000) (96869 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259408128 :
    ThetaLowerSegment 259408128 259440896 (1621201981983 / 6250) (12971234545209 / 50000) := by
  exact
    packedTile16384 259408128 259440896 12 1671 16106 28 _ _ (193739 / 10000) (1937393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259440896 :
    ThetaLowerSegment 259440896 259473664 (12971234545209 / 50000) (2594573555019 / 10000) := by
  exact
    packedTile16384 259440896 259473664 12 1686 16107 28 _ _ (968701 / 50000) (387481 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259473664 :
    ThetaLowerSegment 259473664 259506432 (2594573555019 / 10000) (1037961088731 / 4000) := by
  exact
    packedTile16384 259473664 259506432 12 1699 16108 28 _ _ (387483 / 20000) (968709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259506432 :
    ThetaLowerSegment 259506432 259539200 (1037961088731 / 4000) (25952357657007 / 100000) := by
  exact
    packedTile16384 259506432 259539200 12 1719 16109 28 _ _ (484357 / 25000) (1937431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259539200 :
    ThetaLowerSegment 259539200 259571968 (25952357657007 / 100000) (25955639680367 / 100000) := by
  exact
    packedTile16384 259539200 259571968 12 1694 16110 28 _ _ (12109 / 625) (1937443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259571968 :
    ThetaLowerSegment 259571968 259604736 (25955639680367 / 100000) (12979469581413 / 50000) := by
  exact
    packedTile16384 259571968 259604736 12 1703 16111 28 _ _ (1937453 / 100000) (121091 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259604736 :
    ThetaLowerSegment 259604736 259637504 (12979469581413 / 50000) (12981073803261 / 50000) := by
  exact
    packedTile16384 259604736 259637504 12 1656 16112 28 _ _ (968733 / 50000) (1937469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259637504 :
    ThetaLowerSegment 259637504 259670272 (12981073803261 / 50000) (12982674160089 / 50000) := by
  exact
    packedTile16384 259637504 259670272 12 1652 16113 28 _ _ (968739 / 50000) (1937481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259670272 :
    ThetaLowerSegment 259670272 259703040 (12982674160089 / 50000) (5193731123463 / 20000) := by
  exact
    packedTile16384 259670272 259703040 12 1707 16114 28 _ _ (1937491 / 100000) (968747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259703040 :
    ThetaLowerSegment 259703040 259735808 (5193731123463 / 20000) (12985890404827 / 50000) := by
  exact
    packedTile16384 259703040 259735808 12 1613 16115 28 _ _ (1937503 / 100000) (968753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259735808 :
    ThetaLowerSegment 259735808 259768576 (12985890404827 / 50000) (12987541168459 / 50000) := by
  exact
    packedTile16384 259735808 259768576 12 1704 16116 28 _ _ (484379 / 25000) (1937519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259768576 :
    ThetaLowerSegment 259768576 259801344 (12987541168459 / 50000) (12989133817297 / 50000) := by
  exact
    packedTile16384 259768576 259801344 12 1644 16117 28 _ _ (1937529 / 100000) (484383 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259801344 :
    ThetaLowerSegment 259801344 259834112 (12989133817297 / 50000) (25981617642983 / 100000) := by
  exact
    packedTile16384 259801344 259834112 12 1729 16118 28 _ _ (1937541 / 100000) (242193 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259834112 :
    ThetaLowerSegment 259834112 259866880 (25981617642983 / 100000) (25984857233271 / 100000) := by
  exact
    packedTile16384 259834112 259866880 12 1672 16119 28 _ _ (968777 / 50000) (1937557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259866880 :
    ThetaLowerSegment 259866880 259899648 (25984857233271 / 100000) (3248513801033 / 12500) := by
  exact
    packedTile16384 259866880 259899648 12 1679 16120 28 _ _ (1937567 / 100000) (193757 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259899648 :
    ThetaLowerSegment 259899648 259932416 (3248513801033 / 12500) (259913732913 / 1000) := by
  exact
    packedTile16384 259899648 259932416 12 1684 16121 28 _ _ (1937579 / 100000) (968791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259932416 :
    ThetaLowerSegment 259932416 259965184 (259913732913 / 1000) (1299733844283 / 5000) := by
  exact
    packedTile16384 259932416 259965184 12 1705 16122 28 _ _ (242199 / 12500) (387519 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259965184 :
    ThetaLowerSegment 259965184 259997952 (1299733844283 / 5000) (6499485921501 / 25000) := by
  exact
    packedTile16384 259965184 259997952 12 1686 16123 28 _ _ (484401 / 25000) (1937607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell259997952 :
    ThetaLowerSegment 259997952 260030720 (6499485921501 / 25000) (2600127251201 / 10000) := by
  exact
    packedTile16384 259997952 260030720 12 1718 16124 28 _ _ (1937617 / 100000) (96881 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260030720 :
    ThetaLowerSegment 260030720 260063488 (2600127251201 / 10000) (2600461686139 / 10000) := by
  exact
    packedTile16384 260030720 260063488 12 1726 16125 28 _ _ (193763 / 10000) (1937633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260063488 :
    ThetaLowerSegment 260063488 260096256 (2600461686139 / 10000) (2600781397069 / 10000) := by
  exact
    packedTile16384 260063488 260096256 12 1650 16126 28 _ _ (968821 / 50000) (387529 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260096256 :
    ThetaLowerSegment 260096256 260129024 (2600781397069 / 10000) (5202215783873 / 20000) := by
  exact
    packedTile16384 260096256 260129024 12 1685 16127 28 _ _ (387531 / 20000) (968829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260129024 :
    ThetaLowerSegment 260129024 260161792 (5202215783873 / 20000) (26014287695917 / 100000) := by
  exact
    packedTile16384 260129024 260161792 12 1656 16128 28 _ _ (1937667 / 100000) (193767 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260161792 :
    ThetaLowerSegment 260161792 260194560 (26014287695917 / 100000) (26017628256237 / 100000) := by
  exact
    packedTile16384 260161792 260194560 12 1724 16129 28 _ _ (24221 / 1250) (1937683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260194560 :
    ThetaLowerSegment 260194560 260227328 (26017628256237 / 100000) (6505218473003 / 25000) := by
  exact
    packedTile16384 260194560 260227328 12 1675 16130 28 _ _ (1937693 / 100000) (60553 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260227328 :
    ThetaLowerSegment 260227328 260260096 (6505218473003 / 25000) (26024138924937 / 100000) := by
  exact
    packedTile16384 260227328 260260096 12 1685 16131 28 _ _ (387541 / 20000) (484427 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260260096 :
    ThetaLowerSegment 260260096 260292864 (26024138924937 / 100000) (26027467924461 / 100000) := by
  exact
    packedTile16384 260260096 260292864 12 1718 16132 28 _ _ (968859 / 50000) (1937721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260292864 :
    ThetaLowerSegment 260292864 260325632 (26027467924461 / 100000) (26030667116691 / 100000) := by
  exact
    packedTile16384 260292864 260325632 12 1651 16133 28 _ _ (193773 / 10000) (1937733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260325632 :
    ThetaLowerSegment 260325632 260358400 (26030667116691 / 100000) (26033969030763 / 100000) := by
  exact
    packedTile16384 260325632 260358400 12 1704 16134 28 _ _ (1937743 / 100000) (968873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260358400 :
    ThetaLowerSegment 260358400 260391168 (26033969030763 / 100000) (26037201206103 / 100000) := by
  exact
    packedTile16384 260358400 260391168 12 1668 16135 28 _ _ (387551 / 20000) (968879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260391168 :
    ThetaLowerSegment 260391168 260423936 (26037201206103 / 100000) (26040448905271 / 100000) := by
  exact
    packedTile16384 260391168 260423936 12 1676 16136 28 _ _ (242221 / 12500) (1937771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260423936 :
    ThetaLowerSegment 260423936 260456704 (26040448905271 / 100000) (5208754052381 / 20000) := by
  exact
    packedTile16384 260423936 260456704 12 1714 16137 28 _ _ (1937781 / 100000) (242223 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260456704 :
    ThetaLowerSegment 260456704 260489472 (5208754052381 / 20000) (13023529348313 / 50000) := by
  exact
    packedTile16384 260456704 260489472 12 1697 16138 28 _ _ (1937793 / 100000) (484449 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260489472 :
    ThetaLowerSegment 260489472 260522240 (13023529348313 / 50000) (1628143790379 / 6250) := by
  exact
    packedTile16384 260489472 260522240 12 1673 16139 28 _ _ (968903 / 50000) (1937809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260522240 :
    ThetaLowerSegment 260522240 260555008 (1628143790379 / 6250) (2605360850139 / 10000) := by
  exact
    packedTile16384 260522240 260555008 12 1707 16140 28 _ _ (968909 / 50000) (1937821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260555008 :
    ThetaLowerSegment 260555008 260587776 (2605360850139 / 10000) (13028482412341 / 50000) := by
  exact
    packedTile16384 260555008 260587776 12 1732 16141 28 _ _ (1937831 / 100000) (968917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260587776 :
    ThetaLowerSegment 260587776 260620544 (13028482412341 / 50000) (13030125704053 / 50000) := by
  exact
    packedTile16384 260587776 260620544 12 1696 16142 28 _ _ (484461 / 25000) (1937847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260620544 :
    ThetaLowerSegment 260620544 260653312 (13030125704053 / 50000) (13031736062389 / 50000) := by
  exact
    packedTile16384 260620544 260653312 12 1662 16143 28 _ _ (60558 / 3125) (1937859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260653312 :
    ThetaLowerSegment 260653312 260686080 (13031736062389 / 50000) (26066741309781 / 100000) := by
  exact
    packedTile16384 260653312 260686080 12 1687 16144 28 _ _ (1937869 / 100000) (121117 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260686080 :
    ThetaLowerSegment 260686080 260718848 (26066741309781 / 100000) (26070027955957 / 100000) := by
  exact
    packedTile16384 260686080 260718848 12 1696 16145 28 _ _ (1937881 / 100000) (484471 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260718848 :
    ThetaLowerSegment 260718848 260751616 (26070027955957 / 100000) (26073347568379 / 100000) := by
  exact
    packedTile16384 260718848 260751616 12 1713 16146 28 _ _ (968947 / 50000) (1937897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260751616 :
    ThetaLowerSegment 260751616 260784384 (26073347568379 / 100000) (26076597436741 / 100000) := by
  exact
    packedTile16384 260751616 260784384 12 1677 16147 28 _ _ (968953 / 50000) (1937909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260784384 :
    ThetaLowerSegment 260784384 260817152 (26076597436741 / 100000) (6519987024673 / 25000) := by
  exact
    packedTile16384 260784384 260817152 12 1729 16148 28 _ _ (1937919 / 100000) (968961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260817152 :
    ThetaLowerSegment 260817152 260849920 (6519987024673 / 25000) (3260407987543 / 12500) := by
  exact
    packedTile16384 260817152 260849920 12 1711 16149 28 _ _ (484483 / 25000) (387587 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260849920 :
    ThetaLowerSegment 260849920 260882688 (3260407987543 / 12500) (652163184951 / 2500) := by
  exact
    packedTile16384 260849920 260882688 12 1684 16150 28 _ _ (242243 / 12500) (1937947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260882688 :
    ThetaLowerSegment 260882688 260915456 (652163184951 / 2500) (26089819986983 / 100000) := by
  exact
    packedTile16384 260882688 260915456 12 1699 16151 28 _ _ (1937957 / 100000) (48449 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260915456 :
    ThetaLowerSegment 260915456 260948224 (26089819986983 / 100000) (13046529166591 / 50000) := by
  exact
    packedTile16384 260915456 260948224 12 1671 16152 28 _ _ (1937969 / 100000) (484493 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260948224 :
    ThetaLowerSegment 260948224 260980992 (13046529166591 / 50000) (13048213272949 / 50000) := by
  exact
    packedTile16384 260948224 260980992 12 1738 16153 28 _ _ (968991 / 50000) (387597 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell260980992 :
    ThetaLowerSegment 260980992 261013760 (13048213272949 / 50000) (3262459085731 / 12500) := by
  exact
    packedTile16384 260980992 261013760 12 1675 16154 28 _ _ (968997 / 50000) (1937997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261013760 :
    ThetaLowerSegment 261013760 261046528 (3262459085731 / 12500) (2610290140551 / 10000) := by
  exact
    packedTile16384 261013760 261046528 12 1666 16155 28 _ _ (1938007 / 100000) (193801 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261046528 :
    ThetaLowerSegment 261046528 261079296 (2610290140551 / 10000) (5221229517467 / 20000) := by
  exact
    packedTile16384 261046528 261079296 12 1675 16156 28 _ _ (1938019 / 100000) (969011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261079296 :
    ThetaLowerSegment 261079296 261112064 (5221229517467 / 20000) (26109448055831 / 100000) := by
  exact
    packedTile16384 261079296 261112064 12 1703 16157 28 _ _ (121127 / 6250) (387607 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261112064 :
    ThetaLowerSegment 261112064 261144832 (26109448055831 / 100000) (6528191981729 / 25000) := by
  exact
    packedTile16384 261112064 261144832 12 1713 16158 28 _ _ (387609 / 20000) (60564 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261144832 :
    ThetaLowerSegment 261144832 261177600 (6528191981729 / 25000) (2611610526107 / 10000) := by
  exact
    packedTile16384 261144832 261177600 12 1722 16159 28 _ _ (1938057 / 100000) (96903 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261177600 :
    ThetaLowerSegment 261177600 261210368 (2611610526107 / 10000) (2611930695271 / 10000) := by
  exact
    packedTile16384 261177600 261210368 12 1652 16160 28 _ _ (193807 / 10000) (1938073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261210368 :
    ThetaLowerSegment 261210368 261243136 (2611930695271 / 10000) (522450870993 / 2000) := by
  exact
    packedTile16384 261210368 261243136 12 1670 16162 28 _ _ (969041 / 50000) (387617 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261243136 :
    ThetaLowerSegment 261243136 261275904 (522450870993 / 2000) (163286271409 / 625) := by
  exact
    packedTile16384 261243136 261275904 12 1682 16163 28 _ _ (387619 / 20000) (969049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261275904 :
    ThetaLowerSegment 261275904 261308672 (163286271409 / 625) (13064562670419 / 50000) := by
  exact
    packedTile16384 261275904 261308672 12 1714 16164 28 _ _ (1938107 / 100000) (193811 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261308672 :
    ThetaLowerSegment 261308672 261341440 (13064562670419 / 50000) (13066180031559 / 50000) := by
  exact
    packedTile16384 261308672 261341440 12 1669 16165 28 _ _ (48453 / 2500) (1938123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261341440 :
    ThetaLowerSegment 261341440 261374208 (13066180031559 / 50000) (13067835196287 / 50000) := by
  exact
    packedTile16384 261341440 261374208 12 1708 16166 28 _ _ (484533 / 25000) (387627 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261374208 :
    ThetaLowerSegment 261374208 261406976 (13067835196287 / 50000) (26139029197859 / 100000) := by
  exact
    packedTile16384 261374208 261406976 12 1733 16167 28 _ _ (387629 / 20000) (484537 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261406976 :
    ThetaLowerSegment 261406976 261439744 (26139029197859 / 100000) (13071176568557 / 50000) := by
  exact
    packedTile16384 261406976 261439744 12 1715 16168 28 _ _ (1938157 / 100000) (24227 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261439744 :
    ThetaLowerSegment 261439744 261472512 (13071176568557 / 50000) (817052167062 / 3125) := by
  exact
    packedTile16384 261439744 261472512 12 1711 16169 28 _ _ (193817 / 10000) (1938173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261472512 :
    ThetaLowerSegment 261472512 261505280 (817052167062 / 3125) (2614895068811 / 10000) := by
  exact
    packedTile16384 261472512 261505280 12 1693 16170 28 _ _ (969091 / 50000) (387637 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261505280 :
    ThetaLowerSegment 261505280 261538048 (2614895068811 / 10000) (653806625039 / 2500) := by
  exact
    packedTile16384 261505280 261538048 12 1710 16171 28 _ _ (387639 / 20000) (969099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261538048 :
    ThetaLowerSegment 261538048 261570816 (653806625039 / 2500) (3269439906599 / 12500) := by
  exact
    packedTile16384 261538048 261570816 12 1679 16172 28 _ _ (60569 / 3125) (1938211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261570816 :
    ThetaLowerSegment 261570816 261603584 (3269439906599 / 12500) (6539690473713 / 25000) := by
  exact
    packedTile16384 261570816 261603584 12 1673 16173 28 _ _ (96911 / 5000) (1938223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261603584 :
    ThetaLowerSegment 261603584 261636352 (6539690473713 / 25000) (13081003248447 / 50000) := by
  exact
    packedTile16384 261603584 261636352 12 1674 16174 28 _ _ (1938233 / 100000) (484559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261636352 :
    ThetaLowerSegment 261636352 261669120 (13081003248447 / 50000) (1635332071429 / 6250) := by
  exact
    packedTile16384 261636352 261669120 12 1706 16175 28 _ _ (387649 / 20000) (242281 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261669120 :
    ThetaLowerSegment 261669120 261701888 (1635332071429 / 6250) (6542149137979 / 25000) := by
  exact
    packedTile16384 261669120 261701888 12 1694 16176 28 _ _ (969129 / 50000) (1938261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261701888 :
    ThetaLowerSegment 261701888 261734656 (6542149137979 / 25000) (6542953520029 / 25000) := by
  exact
    packedTile16384 261701888 261734656 12 1660 16177 28 _ _ (193827 / 10000) (1938273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261734656 :
    ThetaLowerSegment 261734656 261767424 (6542953520029 / 25000) (2617506651899 / 10000) := by
  exact
    packedTile16384 261734656 261767424 12 1678 16178 28 _ _ (1938283 / 100000) (969143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261767424 :
    ThetaLowerSegment 261767424 261800192 (2617506651899 / 10000) (2617835386731 / 10000) := by
  exact
    packedTile16384 261767424 261800192 12 1696 16179 28 _ _ (387659 / 20000) (969149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261800192 :
    ThetaLowerSegment 261800192 261832960 (2617835386731 / 10000) (13090831279533 / 50000) := by
  exact
    packedTile16384 261800192 261832960 12 1707 16180 28 _ _ (484577 / 25000) (1938311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261832960 :
    ThetaLowerSegment 261832960 261865728 (13090831279533 / 50000) (13092460437493 / 50000) := by
  exact
    packedTile16384 261832960 261865728 12 1681 16181 28 _ _ (24229 / 1250) (1938323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261865728 :
    ThetaLowerSegment 261865728 261898496 (13092460437493 / 50000) (5237644371217 / 20000) := by
  exact
    packedTile16384 261865728 261898496 12 1703 16182 28 _ _ (1938333 / 100000) (60573 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261898496 :
    ThetaLowerSegment 261898496 261931264 (5237644371217 / 20000) (5238298756489 / 20000) := by
  exact
    packedTile16384 261898496 261931264 12 1688 16183 28 _ _ (387669 / 20000) (484587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261931264 :
    ThetaLowerSegment 261931264 261964032 (5238298756489 / 20000) (26194674627923 / 100000) := by
  exact
    packedTile16384 261931264 261964032 12 1641 16184 28 _ _ (969179 / 50000) (1938361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261964032 :
    ThetaLowerSegment 261964032 261996800 (26194674627923 / 100000) (26197991178993 / 100000) := by
  exact
    packedTile16384 261964032 261996800 12 1711 16185 28 _ _ (193837 / 10000) (1938373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell261996800 :
    ThetaLowerSegment 261996800 262029568 (26197991178993 / 100000) (26201344581583 / 100000) := by
  exact
    packedTile16384 261996800 262029568 12 1730 16186 28 _ _ (1938383 / 100000) (969193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262029568 :
    ThetaLowerSegment 262029568 262062336 (26201344581583 / 100000) (6551142033117 / 25000) := by
  exact
    packedTile16384 262029568 262062336 12 1663 16187 28 _ _ (387679 / 20000) (969199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262062336 :
    ThetaLowerSegment 262062336 262095104 (6551142033117 / 25000) (6551976517761 / 25000) := by
  exact
    packedTile16384 262062336 262095104 12 1722 16188 28 _ _ (242301 / 12500) (1938411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262095104 :
    ThetaLowerSegment 262095104 262127872 (6551976517761 / 25000) (1638204326859 / 6250) := by
  exact
    packedTile16384 262095104 262127872 12 1735 16189 28 _ _ (96921 / 5000) (1938423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262127872 :
    ThetaLowerSegment 262127872 262193408 (1638204326859 / 6250) (26217888978439 / 100000) := by
  exact
    packedTile16384 262127872 262193408 13 3415 16190 28 _ _ (1938433 / 100000) (484609 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262193408 :
    ThetaLowerSegment 262193408 262258944 (26217888978439 / 100000) (26224501058677 / 100000) := by
  exact
    packedTile16384 262193408 262258944 13 3411 16192 28 _ _ (969229 / 50000) (1938461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262258944 :
    ThetaLowerSegment 262258944 262324480 (26224501058677 / 100000) (13115560489061 / 50000) := by
  exact
    packedTile16384 262258944 262324480 13 3415 16194 28 _ _ (1938483 / 100000) (969243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262324480 :
    ThetaLowerSegment 262324480 262390016 (13115560489061 / 50000) (13118825905787 / 50000) := by
  exact
    packedTile16384 262324480 262390016 13 3369 16196 28 _ _ (484627 / 25000) (1938511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262390016 :
    ThetaLowerSegment 262390016 262455552 (13118825905787 / 50000) (13122109780689 / 50000) := by
  exact
    packedTile16384 262390016 262455552 13 3388 16198 28 _ _ (1938533 / 100000) (242317 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262455552 :
    ThetaLowerSegment 262455552 262521088 (13122109780689 / 50000) (6562694425773 / 25000) := by
  exact
    packedTile16384 262455552 262521088 13 3383 16200 28 _ _ (969279 / 50000) (1938561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262521088 :
    ThetaLowerSegment 262521088 262586624 (6562694425773 / 25000) (26257413472701 / 100000) := by
  exact
    packedTile16384 262521088 262586624 13 3423 16202 28 _ _ (1938583 / 100000) (969293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262586624 :
    ThetaLowerSegment 262586624 262652160 (26257413472701 / 100000) (26263950458877 / 100000) := by
  exact
    packedTile16384 262586624 262652160 13 3372 16204 28 _ _ (121163 / 6250) (1938611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262652160 :
    ThetaLowerSegment 262652160 262717696 (26263950458877 / 100000) (13135229224929 / 50000) := by
  exact
    packedTile16384 262652160 262717696 13 3357 16206 28 _ _ (1938633 / 100000) (484659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262717696 :
    ThetaLowerSegment 262717696 262783232 (13135229224929 / 50000) (2627694132221 / 10000) := by
  exact
    packedTile16384 262717696 262783232 13 3344 16208 28 _ _ (969329 / 50000) (1938661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262783232 :
    ThetaLowerSegment 262783232 262848768 (2627694132221 / 10000) (657088805781 / 2500) := by
  exact
    packedTile16384 262783232 262848768 13 3410 16210 28 _ _ (1938683 / 100000) (969343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262848768 :
    ThetaLowerSegment 262848768 262914304 (657088805781 / 2500) (26290126386677 / 100000) := by
  exact
    packedTile16384 262848768 262914304 13 3391 16212 28 _ _ (1938707 / 100000) (193871 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262914304 :
    ThetaLowerSegment 262914304 262979840 (26290126386677 / 100000) (26296739401529 / 100000) := by
  exact
    packedTile16384 262914304 262979840 13 3411 16214 28 _ _ (484683 / 25000) (387747 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell262979840 :
    ThetaLowerSegment 262979840 263045376 (26296739401529 / 100000) (13151585129249 / 50000) := by
  exact
    packedTile16384 262979840 263045376 13 3317 16216 28 _ _ (1938757 / 100000) (48469 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263045376 :
    ThetaLowerSegment 263045376 263110912 (13151585129249 / 50000) (13154879119867 / 50000) := by
  exact
    packedTile16384 263045376 263110912 13 3398 16218 28 _ _ (969391 / 50000) (387757 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263110912 :
    ThetaLowerSegment 263110912 263176448 (13154879119867 / 50000) (6579080760059 / 25000) := by
  exact
    packedTile16384 263110912 263176448 13 3386 16220 28 _ _ (1938807 / 100000) (193881 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263176448 :
    ThetaLowerSegment 263176448 263241984 (6579080760059 / 25000) (6580747186163 / 25000) := by
  exact
    packedTile16384 263176448 263241984 13 3438 16222 28 _ _ (121177 / 6250) (387767 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263241984 :
    ThetaLowerSegment 263241984 263307520 (6580747186163 / 25000) (26329303601901 / 100000) := by
  exact
    packedTile16384 263241984 263307520 13 3257 16224 28 _ _ (1938857 / 100000) (96943 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263307520 :
    ThetaLowerSegment 263307520 263373056 (26329303601901 / 100000) (26335884167409 / 100000) := by
  exact
    packedTile16384 263307520 263373056 13 3394 16226 28 _ _ (969441 / 50000) (387777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263373056 :
    ThetaLowerSegment 263373056 263438592 (26335884167409 / 100000) (1053694249559 / 4000) := by
  exact
    packedTile16384 263373056 263438592 13 3338 16228 28 _ _ (1938907 / 100000) (193891 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263438592 :
    ThetaLowerSegment 263438592 263504128 (1053694249559 / 4000) (26348925340591 / 100000) := by
  exact
    packedTile16384 263438592 263504128 13 3388 16230 28 _ _ (484733 / 25000) (387787 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263504128 :
    ThetaLowerSegment 263504128 263569664 (26348925340591 / 100000) (26355420843191 / 100000) := by
  exact
    packedTile16384 263504128 263569664 13 3350 16232 28 _ _ (484739 / 25000) (1938959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263569664 :
    ThetaLowerSegment 263569664 263635200 (26355420843191 / 100000) (5272361569321 / 20000) := by
  exact
    packedTile16384 263569664 263635200 13 3294 16234 28 _ _ (1938981 / 100000) (242373 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263635200 :
    ThetaLowerSegment 263635200 263667968 (5272361569321 / 20000) (26365080888733 / 100000) := by
  exact
    packedTile16384 263635200 263667968 12 1688 16236 28 _ _ (969503 / 50000) (1939009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263667968 :
    ThetaLowerSegment 263667968 263700736 (26365080888733 / 100000) (26368330684577 / 100000) := by
  exact
    packedTile16384 263667968 263700736 12 1676 16237 28 _ _ (1939019 / 100000) (969511 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263700736 :
    ThetaLowerSegment 263700736 263733504 (26368330684577 / 100000) (26371665817897 / 100000) := by
  exact
    packedTile16384 263700736 263733504 12 1720 16238 28 _ _ (1939031 / 100000) (969517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263733504 :
    ThetaLowerSegment 263733504 263766272 (26371665817897 / 100000) (6593735215381 / 25000) := by
  exact
    packedTile16384 263733504 263766272 12 1689 16239 28 _ _ (1939043 / 100000) (969523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263766272 :
    ThetaLowerSegment 263766272 263799040 (6593735215381 / 25000) (6594553012249 / 25000) := by
  exact
    packedTile16384 263766272 263799040 12 1687 16240 28 _ _ (121191 / 6250) (1939059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263799040 :
    ThetaLowerSegment 263799040 263831808 (6594553012249 / 25000) (6595374207547 / 25000) := by
  exact
    packedTile16384 263799040 263831808 12 1694 16241 28 _ _ (484767 / 25000) (1939071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263831808 :
    ThetaLowerSegment 263831808 263864576 (6595374207547 / 25000) (6596173108919 / 25000) := by
  exact
    packedTile16384 263831808 263864576 12 1648 16242 28 _ _ (1939081 / 100000) (484771 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263864576 :
    ThetaLowerSegment 263864576 263897344 (6596173108919 / 25000) (26388006345613 / 100000) := by
  exact
    packedTile16384 263864576 263897344 12 1709 16243 28 _ _ (1939093 / 100000) (242387 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263897344 :
    ThetaLowerSegment 263897344 263930112 (26388006345613 / 100000) (26391269861011 / 100000) := by
  exact
    packedTile16384 263897344 263930112 12 1683 16244 28 _ _ (969553 / 50000) (1939109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263930112 :
    ThetaLowerSegment 263930112 263962880 (26391269861011 / 100000) (26394488796891 / 100000) := by
  exact
    packedTile16384 263930112 263962880 12 1660 16245 28 _ _ (969559 / 50000) (1939121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263962880 :
    ThetaLowerSegment 263962880 263995648 (26394488796891 / 100000) (26397721326601 / 100000) := by
  exact
    packedTile16384 263962880 263995648 12 1667 16246 28 _ _ (193913 / 10000) (1939133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell263995648 :
    ThetaLowerSegment 263995648 264028416 (26397721326601 / 100000) (660024137821 / 2500) := by
  exact
    packedTile16384 263995648 264028416 12 1673 16247 28 _ _ (1939143 / 100000) (969573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264028416 :
    ThetaLowerSegment 264028416 264061184 (660024137821 / 2500) (660105582331 / 2500) := by
  exact
    packedTile16384 264028416 264061184 12 1680 16248 28 _ _ (387831 / 20000) (969579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264061184 :
    ThetaLowerSegment 264061184 264093952 (660105582331 / 2500) (3300934894539 / 12500) := by
  exact
    packedTile16384 264061184 264093952 12 1679 16249 28 _ _ (60599 / 3125) (1939171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264093952 :
    ThetaLowerSegment 264093952 264126720 (3300934894539 / 12500) (6602679881523 / 25000) := by
  exact
    packedTile16384 264093952 264126720 12 1671 16250 28 _ _ (96959 / 5000) (1939183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264126720 :
    ThetaLowerSegment 264126720 264159488 (6602679881523 / 25000) (264140142133 / 1000) := by
  exact
    packedTile16384 264126720 264159488 12 1699 16251 28 _ _ (242399 / 12500) (387839 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264159488 :
    ThetaLowerSegment 264159488 264192256 (264140142133 / 1000) (5283472644067 / 20000) := by
  exact
    packedTile16384 264159488 264192256 12 1727 16252 28 _ _ (387841 / 20000) (242401 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264192256 :
    ThetaLowerSegment 264192256 264225024 (5283472644067 / 20000) (26420628861763 / 100000) := by
  exact
    packedTile16384 264192256 264225024 12 1684 16253 28 _ _ (1939217 / 100000) (96961 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264225024 :
    ThetaLowerSegment 264225024 264257792 (26420628861763 / 100000) (26423939127373 / 100000) := by
  exact
    packedTile16384 264225024 264257792 12 1707 16254 28 _ _ (193923 / 10000) (1939233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264257792 :
    ThetaLowerSegment 264257792 264290560 (26423939127373 / 100000) (26427313408453 / 100000) := by
  exact
    packedTile16384 264257792 264290560 12 1740 16256 28 _ _ (969621 / 50000) (387849 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264290560 :
    ThetaLowerSegment 264290560 264323328 (26427313408453 / 100000) (26430559719649 / 100000) := by
  exact
    packedTile16384 264290560 264323328 12 1674 16257 28 _ _ (969627 / 50000) (1939257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264323328 :
    ThetaLowerSegment 264323328 264356096 (26430559719649 / 100000) (26433821566743 / 100000) := by
  exact
    packedTile16384 264323328 264356096 12 1682 16258 28 _ _ (1939267 / 100000) (193927 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264356096 :
    ThetaLowerSegment 264356096 264388864 (26433821566743 / 100000) (5287411256823 / 20000) := by
  exact
    packedTile16384 264356096 264388864 12 1668 16259 28 _ _ (1939279 / 100000) (969641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264388864 :
    ThetaLowerSegment 264388864 264421632 (5287411256823 / 20000) (26440444227239 / 100000) := by
  exact
    packedTile16384 264388864 264421632 12 1747 16260 28 _ _ (484823 / 25000) (387859 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264421632 :
    ThetaLowerSegment 264421632 264454400 (26440444227239 / 100000) (5288738124427 / 20000) := by
  exact
    packedTile16384 264421632 264454400 12 1674 16261 28 _ _ (242413 / 12500) (1939307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264454400 :
    ThetaLowerSegment 264454400 264487168 (5288738124427 / 20000) (26446937037119 / 100000) := by
  exact
    packedTile16384 264454400 264487168 12 1674 16262 28 _ _ (484829 / 25000) (1939319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264487168 :
    ThetaLowerSegment 264487168 264519936 (26446937037119 / 100000) (330626687383 / 1250) := by
  exact
    packedTile16384 264487168 264519936 12 1649 16263 28 _ _ (1939329 / 100000) (484833 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264519936 :
    ThetaLowerSegment 264519936 264552704 (330626687383 / 1250) (26453406658907 / 100000) := by
  exact
    packedTile16384 264519936 264552704 12 1687 16264 28 _ _ (1939341 / 100000) (121209 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264552704 :
    ThetaLowerSegment 264552704 264585472 (26453406658907 / 100000) (26456647319441 / 100000) := by
  exact
    packedTile16384 264552704 264585472 12 1671 16265 28 _ _ (969677 / 50000) (1939357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264585472 :
    ThetaLowerSegment 264585472 264618240 (26456647319441 / 100000) (26459909333053 / 100000) := by
  exact
    packedTile16384 264585472 264618240 12 1682 16266 28 _ _ (969683 / 50000) (1939369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264618240 :
    ThetaLowerSegment 264618240 264651008 (26459909333053 / 100000) (26463231487567 / 100000) := by
  exact
    packedTile16384 264618240 264651008 12 1713 16267 28 _ _ (969689 / 50000) (1939381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264651008 :
    ThetaLowerSegment 264651008 264683776 (26463231487567 / 100000) (26466512937139 / 100000) := by
  exact
    packedTile16384 264651008 264683776 12 1692 16268 28 _ _ (1939391 / 100000) (969697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264683776 :
    ThetaLowerSegment 264683776 264716544 (26466512937139 / 100000) (26469751740149 / 100000) := by
  exact
    packedTile16384 264683776 264716544 12 1670 16269 28 _ _ (1939403 / 100000) (969703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264716544 :
    ThetaLowerSegment 264716544 264749312 (26469751740149 / 100000) (26472986686037 / 100000) := by
  exact
    packedTile16384 264716544 264749312 12 1668 16270 28 _ _ (242427 / 12500) (1939419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264749312 :
    ThetaLowerSegment 264749312 264782080 (26472986686037 / 100000) (26476242985649 / 100000) := by
  exact
    packedTile16384 264749312 264782080 12 1679 16271 28 _ _ (484857 / 25000) (1939431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264782080 :
    ThetaLowerSegment 264782080 264814848 (26476242985649 / 100000) (26479497365969 / 100000) := by
  exact
    packedTile16384 264782080 264814848 12 1678 16272 28 _ _ (24243 / 1250) (1939443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264814848 :
    ThetaLowerSegment 264814848 264847616 (26479497365969 / 100000) (1059311932599 / 4000) := by
  exact
    packedTile16384 264814848 264847616 12 1702 16273 28 _ _ (1939453 / 100000) (60608 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264847616 :
    ThetaLowerSegment 264847616 264880384 (1059311932599 / 4000) (2648610898173 / 10000) := by
  exact
    packedTile16384 264847616 264880384 12 1707 16274 28 _ _ (387893 / 20000) (484867 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264880384 :
    ThetaLowerSegment 264880384 264913152 (2648610898173 / 10000) (26489442942693 / 100000) := by
  exact
    packedTile16384 264880384 264913152 12 1719 16275 28 _ _ (1939477 / 100000) (48487 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264913152 :
    ThetaLowerSegment 264913152 264945920 (26489442942693 / 100000) (26492776926003 / 100000) := by
  exact
    packedTile16384 264913152 264945920 12 1719 16276 28 _ _ (193949 / 10000) (1939493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264945920 :
    ThetaLowerSegment 264945920 264978688 (26492776926003 / 100000) (26496015894343 / 100000) := by
  exact
    packedTile16384 264945920 264978688 12 1670 16277 28 _ _ (969751 / 50000) (387901 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell264978688 :
    ThetaLowerSegment 264978688 265011456 (26496015894343 / 100000) (26499256822237 / 100000) := by
  exact
    packedTile16384 264978688 265011456 12 1671 16278 28 _ _ (969757 / 50000) (1939517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265011456 :
    ThetaLowerSegment 265011456 265044224 (26499256822237 / 100000) (13251272160251 / 50000) := by
  exact
    packedTile16384 265011456 265044224 12 1695 16279 28 _ _ (1939527 / 100000) (193953 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265044224 :
    ThetaLowerSegment 265044224 265076992 (13251272160251 / 50000) (26505831839107 / 100000) := by
  exact
    packedTile16384 265044224 265076992 12 1695 16280 28 _ _ (1939539 / 100000) (969771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265076992 :
    ThetaLowerSegment 265076992 265109760 (26505831839107 / 100000) (26509123258851 / 100000) := by
  exact
    packedTile16384 265076992 265109760 12 1697 16281 28 _ _ (60611 / 3125) (387911 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265109760 :
    ThetaLowerSegment 265109760 265142528 (26509123258851 / 100000) (26512408880267 / 100000) := by
  exact
    packedTile16384 265109760 265142528 12 1694 16282 28 _ _ (484891 / 25000) (1939567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265142528 :
    ThetaLowerSegment 265142528 265175296 (26512408880267 / 100000) (26515713917771 / 100000) := by
  exact
    packedTile16384 265142528 265175296 12 1704 16283 28 _ _ (242447 / 12500) (1939579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265175296 :
    ThetaLowerSegment 265175296 265208064 (26515713917771 / 100000) (13259504639741 / 50000) := by
  exact
    packedTile16384 265175296 265208064 12 1699 16284 28 _ _ (1939589 / 100000) (242449 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265208064 :
    ThetaLowerSegment 265208064 265240832 (13259504639741 / 50000) (26522258111157 / 100000) := by
  exact
    packedTile16384 265208064 265240832 12 1675 16285 28 _ _ (1939601 / 100000) (484901 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265240832 :
    ThetaLowerSegment 265240832 265273600 (26522258111157 / 100000) (3315693219399 / 12500) := by
  exact
    packedTile16384 265240832 265273600 12 1695 16286 28 _ _ (1939613 / 100000) (60613 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265273600 :
    ThetaLowerSegment 265273600 265306368 (3315693219399 / 12500) (3316114118241 / 12500) := by
  exact
    packedTile16384 265273600 265306368 12 1736 16287 28 _ _ (969813 / 50000) (1939629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265306368 :
    ThetaLowerSegment 265306368 265339136 (3316114118241 / 12500) (829131572829 / 3125) := by
  exact
    packedTile16384 265306368 265339136 12 1700 16288 28 _ _ (969819 / 50000) (1939641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell265339136 :
    ThetaLowerSegment 265339136 265341184 (829131572829 / 3125) (6633105923007 / 25000) := by
  exact
    packedTile16384 265339136 265341184 8 110 16289 28 _ _ (38793 / 2000) (1939653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_234012928_265341184 :
    ThetaLowerSegment 234012928 265341184 (5849673503353 / 25000) (6633105923007 / 25000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell234012928 cell234045696)
                      (ThetaLowerSegment.join cell234078464 cell234111232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell234144000 cell234176768)
                      (ThetaLowerSegment.join cell234209536 cell234242304)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell234275072 cell234307840)
                      (ThetaLowerSegment.join cell234340608 cell234373376))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell234406144 cell234438912)
                      (ThetaLowerSegment.join cell234471680 cell234504448))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell234537216 cell234569984)
                      (ThetaLowerSegment.join cell234602752 cell234635520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell234668288 cell234701056)
                      (ThetaLowerSegment.join cell234733824 cell234766592)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell234799360 cell234832128)
                      (ThetaLowerSegment.join cell234864896 cell234897664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell234930432 cell234963200)
                      (ThetaLowerSegment.join cell234995968 cell235028736)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell235061504 cell235094272)
                      (ThetaLowerSegment.join cell235127040 cell235159808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell235192576 cell235225344)
                      (ThetaLowerSegment.join cell235258112 cell235290880)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell235323648 cell235356416)
                      (ThetaLowerSegment.join cell235389184 cell235421952))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell235454720 cell235487488)
                      (ThetaLowerSegment.join cell235520256 cell235553024))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell235585792 cell235618560)
                      (ThetaLowerSegment.join cell235651328 cell235684096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell235716864 cell235749632)
                      (ThetaLowerSegment.join cell235782400 cell235815168)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell235847936 cell235880704)
                      (ThetaLowerSegment.join cell235913472 cell235946240))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell235979008 cell236011776)
                      (ThetaLowerSegment.join cell236044544 cell236077312))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell236110080 cell236142848)
                      (ThetaLowerSegment.join cell236175616 cell236208384))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell236241152 cell236273920)
                      (ThetaLowerSegment.join cell236306688 cell236339456)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell236372224 cell236404992)
                      (ThetaLowerSegment.join cell236437760 cell236470528))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell236503296 cell236536064)
                      (ThetaLowerSegment.join cell236568832 cell236601600))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell236634368 cell236667136)
                      (ThetaLowerSegment.join cell236699904 cell236732672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell236765440 cell236798208)
                      (ThetaLowerSegment.join cell236830976 cell236863744)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell236896512 cell236929280)
                      (ThetaLowerSegment.join cell236962048 cell236994816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell237027584 cell237060352)
                      (ThetaLowerSegment.join cell237093120 cell237125888)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell237158656 cell237191424)
                      (ThetaLowerSegment.join cell237224192 cell237256960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell237289728 cell237322496)
                      (ThetaLowerSegment.join cell237355264 cell237388032)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell237420800 cell237453568)
                      (ThetaLowerSegment.join cell237486336 cell237519104))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell237551872 cell237584640)
                      (ThetaLowerSegment.join cell237617408 cell237650176))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell237682944 cell237715712)
                      (ThetaLowerSegment.join cell237748480 cell237781248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell237814016 cell237846784)
                      (ThetaLowerSegment.join cell237879552 cell237912320)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell237945088 cell237977856)
                      (ThetaLowerSegment.join cell238010624 cell238043392))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell238076160 cell238108928)
                      (ThetaLowerSegment.join cell238141696 cell238174464)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell238207232 cell238240000)
                      (ThetaLowerSegment.join cell238272768 cell238305536))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell238338304 cell238371072)
                      (ThetaLowerSegment.join cell238403840 cell238436608)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell238469376 cell238502144)
                      (ThetaLowerSegment.join cell238534912 cell238567680))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell238600448 cell238633216)
                      (ThetaLowerSegment.join cell238665984 cell238698752))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell238731520 cell238764288)
                      (ThetaLowerSegment.join cell238797056 cell238829824))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell238862592 cell238895360)
                      (ThetaLowerSegment.join cell238928128 cell238960896)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell238993664 cell239026432)
                      (ThetaLowerSegment.join cell239059200 cell239091968))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell239124736 cell239157504)
                      (ThetaLowerSegment.join cell239190272 cell239223040)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell239255808 cell239288576)
                      (ThetaLowerSegment.join cell239321344 cell239354112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell239386880 cell239419648)
                      (ThetaLowerSegment.join cell239452416 cell239485184)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell239517952 cell239550720)
                      (ThetaLowerSegment.join cell239583488 cell239616256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell239649024 cell239681792)
                      (ThetaLowerSegment.join cell239714560 cell239747328))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell239780096 cell239812864)
                      (ThetaLowerSegment.join cell239845632 cell239878400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell239911168 cell239943936)
                      (ThetaLowerSegment.join cell239976704 cell240009472)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell240042240 cell240075008)
                      (ThetaLowerSegment.join cell240107776 cell240140544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell240173312 cell240206080)
                      (ThetaLowerSegment.join cell240238848 cell240271616))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell240304384 cell240337152)
                      (ThetaLowerSegment.join cell240369920 cell240402688))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell240435456 cell240468224)
                      (ThetaLowerSegment.join cell240500992 cell240533760)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell240566528 cell240599296)
                      (ThetaLowerSegment.join cell240632064 cell240664832))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell240697600 cell240730368)
                      (ThetaLowerSegment.join cell240763136 cell240795904))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell240828672 cell240861440)
                      (ThetaLowerSegment.join cell240894208 cell240926976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell240959744 cell240992512)
                      (ThetaLowerSegment.join cell241025280 cell241058048)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell241090816 cell241123584)
                      (ThetaLowerSegment.join cell241156352 cell241189120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell241221888 cell241254656)
                      (ThetaLowerSegment.join cell241287424 cell241320192)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell241352960 cell241385728)
                      (ThetaLowerSegment.join cell241418496 cell241451264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell241484032 cell241516800)
                      (ThetaLowerSegment.join cell241549568 cell241582336)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell241615104 cell241647872)
                      (ThetaLowerSegment.join cell241680640 cell241713408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell241746176 cell241778944)
                      (ThetaLowerSegment.join cell241811712 cell241844480))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell241877248 cell241910016)
                      (ThetaLowerSegment.join cell241942784 cell241975552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell242008320 cell242041088)
                      (ThetaLowerSegment.join cell242073856 cell242106624)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell242139392 cell242172160)
                      (ThetaLowerSegment.join cell242204928 cell242237696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell242270464 cell242303232)
                      (ThetaLowerSegment.join cell242336000 cell242368768))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell242401536 cell242434304)
                      (ThetaLowerSegment.join cell242467072 cell242499840))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell242532608 cell242565376)
                      (ThetaLowerSegment.join cell242598144 cell242630912)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell242663680 cell242696448)
                      (ThetaLowerSegment.join cell242729216 cell242761984))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell242794752 cell242827520)
                      (ThetaLowerSegment.join cell242860288 cell242893056))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell242925824 cell242958592)
                      (ThetaLowerSegment.join cell242991360 cell243024128))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell243056896 cell243089664)
                      (ThetaLowerSegment.join cell243122432 cell243155200)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell243187968 cell243220736)
                      (ThetaLowerSegment.join cell243253504 cell243286272))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell243319040 cell243351808)
                      (ThetaLowerSegment.join cell243384576 cell243417344)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell243450112 cell243482880)
                      (ThetaLowerSegment.join cell243515648 cell243548416))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell243581184 cell243613952)
                      (ThetaLowerSegment.join cell243646720 cell243679488)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell243712256 cell243745024)
                      (ThetaLowerSegment.join cell243777792 cell243810560))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell243843328 cell243876096)
                      (ThetaLowerSegment.join cell243908864 cell243941632))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell243974400 cell244007168)
                      (ThetaLowerSegment.join cell244039936 cell244072704))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell244105472 cell244138240)
                      (ThetaLowerSegment.join cell244171008 cell244203776)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell244236544 cell244269312)
                      (ThetaLowerSegment.join cell244302080 cell244334848))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell244367616 cell244400384)
                      (ThetaLowerSegment.join cell244433152 cell244465920))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell244498688 cell244531456)
                      (ThetaLowerSegment.join cell244564224 cell244596992))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell244629760 cell244662528)
                      (ThetaLowerSegment.join cell244695296 cell244728064)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell244760832 cell244793600)
                      (ThetaLowerSegment.join cell244826368 cell244859136))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell244891904 cell244924672)
                      (ThetaLowerSegment.join cell244957440 cell244990208))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell245022976 cell245055744)
                      (ThetaLowerSegment.join cell245088512 cell245121280))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell245154048 cell245186816)
                      (ThetaLowerSegment.join cell245219584 cell245252352)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell245285120 cell245317888)
                      (ThetaLowerSegment.join cell245350656 cell245383424))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell245416192 cell245448960)
                      (ThetaLowerSegment.join cell245481728 cell245514496)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell245547264 cell245580032)
                      (ThetaLowerSegment.join cell245612800 cell245645568))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell245678336 cell245711104)
                      (ThetaLowerSegment.join cell245743872 cell245776640)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell245809408 cell245842176)
                      (ThetaLowerSegment.join cell245874944 cell245907712))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell245940480 cell245973248)
                      (ThetaLowerSegment.join cell246006016 cell246038784))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell246071552 cell246104320)
                      (ThetaLowerSegment.join cell246137088 cell246169856))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell246202624 cell246235392)
                      (ThetaLowerSegment.join cell246268160 cell246300928)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell246333696 cell246366464)
                      (ThetaLowerSegment.join cell246399232 cell246432000))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell246464768 cell246497536)
                      (ThetaLowerSegment.join cell246530304 cell246563072)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell246595840 cell246628608)
                      (ThetaLowerSegment.join cell246661376 cell246694144))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell246726912 cell246759680)
                      (ThetaLowerSegment.join cell246792448 cell246825216)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell246857984 cell246890752)
                      (ThetaLowerSegment.join cell246923520 cell246956288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell246989056 cell247021824)
                      (ThetaLowerSegment.join cell247054592 cell247087360))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell247120128 cell247152896)
                      (ThetaLowerSegment.join cell247185664 cell247218432))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell247251200 cell247283968)
                      (ThetaLowerSegment.join cell247316736 cell247349504)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell247382272 cell247415040)
                      (ThetaLowerSegment.join cell247447808 cell247480576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell247513344 cell247546112)
                      (ThetaLowerSegment.join cell247578880 cell247611648)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell247644416 cell247677184)
                      (ThetaLowerSegment.join cell247709952 cell247742720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell247775488 cell247808256)
                      (ThetaLowerSegment.join cell247841024 cell247873792)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell247906560 cell247939328)
                      (ThetaLowerSegment.join cell247972096 cell248004864))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell248037632 cell248070400)
                      (ThetaLowerSegment.join cell248103168 cell248135936))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell248168704 cell248201472)
                      (ThetaLowerSegment.join cell248234240 cell248267008))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell248299776 cell248332544)
                      (ThetaLowerSegment.join cell248365312 cell248398080)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell248430848 cell248463616)
                      (ThetaLowerSegment.join cell248496384 cell248529152))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell248561920 cell248594688)
                      (ThetaLowerSegment.join cell248627456 cell248660224))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell248692992 cell248725760)
                      (ThetaLowerSegment.join cell248758528 cell248791296))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell248824064 cell248856832)
                      (ThetaLowerSegment.join cell248889600 cell248922368)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell248955136 cell248987904)
                      (ThetaLowerSegment.join cell249020672 cell249053440))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell249086208 cell249118976)
                      (ThetaLowerSegment.join cell249151744 cell249184512))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell249217280 cell249250048)
                      (ThetaLowerSegment.join cell249282816 cell249315584))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell249348352 cell249381120)
                      (ThetaLowerSegment.join cell249413888 cell249446656)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell249479424 cell249512192)
                      (ThetaLowerSegment.join cell249544960 cell249577728))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell249610496 cell249643264)
                      (ThetaLowerSegment.join cell249676032 cell249708800)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell249741568 cell249774336)
                      (ThetaLowerSegment.join cell249807104 cell249839872))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell249872640 cell249905408)
                      (ThetaLowerSegment.join cell249938176 cell249970944)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell250003712 cell250036480)
                      (ThetaLowerSegment.join cell250069248 cell250102016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell250134784 cell250167552)
                      (ThetaLowerSegment.join cell250200320 cell250233088))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell250265856 cell250298624)
                      (ThetaLowerSegment.join cell250331392 cell250364160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell250396928 cell250429696)
                      (ThetaLowerSegment.join cell250462464 cell250495232)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell250528000 cell250560768)
                      (ThetaLowerSegment.join cell250593536 cell250626304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell250659072 cell250691840)
                      (ThetaLowerSegment.join cell250724608 cell250757376)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell250790144 cell250822912)
                      (ThetaLowerSegment.join cell250855680 cell250888448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell250921216 cell250953984)
                      (ThetaLowerSegment.join cell250986752 cell251019520)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell251052288 cell251085056)
                      (ThetaLowerSegment.join cell251117824 cell251150592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell251183360 cell251216128)
                      (ThetaLowerSegment.join cell251248896 cell251281664))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell251314432 cell251347200)
                      (ThetaLowerSegment.join cell251379968 cell251412736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell251445504 cell251478272)
                      (ThetaLowerSegment.join cell251511040 cell251543808)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell251576576 cell251609344)
                      (ThetaLowerSegment.join cell251642112 cell251674880))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell251707648 cell251740416)
                      (ThetaLowerSegment.join cell251773184 cell251805952)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell251838720 cell251871488)
                      (ThetaLowerSegment.join cell251904256 cell251937024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell251969792 cell252002560)
                      (ThetaLowerSegment.join cell252035328 cell252068096)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell252100864 cell252133632)
                      (ThetaLowerSegment.join cell252166400 cell252199168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell252231936 cell252264704)
                      (ThetaLowerSegment.join cell252297472 cell252330240))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell252363008 cell252395776)
                      (ThetaLowerSegment.join cell252428544 cell252461312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell252494080 cell252526848)
                      (ThetaLowerSegment.join cell252559616 cell252592384)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell252625152 cell252657920)
                      (ThetaLowerSegment.join cell252690688 cell252723456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell252756224 cell252788992)
                      (ThetaLowerSegment.join cell252821760 cell252854528))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell252887296 cell252920064)
                      (ThetaLowerSegment.join cell252952832 cell252985600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell253018368 cell253051136)
                      (ThetaLowerSegment.join cell253083904 cell253116672)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell253149440 cell253182208)
                      (ThetaLowerSegment.join cell253214976 cell253247744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell253280512 cell253313280)
                      (ThetaLowerSegment.join cell253346048 cell253378816))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell253411584 cell253444352)
                      (ThetaLowerSegment.join cell253477120 cell253509888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell253542656 cell253575424)
                      (ThetaLowerSegment.join cell253608192 cell253640960)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell253673728 cell253706496)
                      (ThetaLowerSegment.join cell253739264 cell253772032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell253804800 cell253837568)
                      (ThetaLowerSegment.join cell253870336 cell253903104)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell253935872 cell253968640)
                      (ThetaLowerSegment.join cell254001408 cell254034176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell254066944 cell254099712)
                      (ThetaLowerSegment.join cell254132480 cell254165248)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell254198016 cell254230784)
                      (ThetaLowerSegment.join cell254263552 cell254296320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell254329088 cell254361856)
                      (ThetaLowerSegment.join cell254394624 cell254427392))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell254460160 cell254492928)
                      (ThetaLowerSegment.join cell254525696 cell254558464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell254591232 cell254624000)
                      (ThetaLowerSegment.join cell254656768 cell254689536)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell254722304 cell254755072)
                      (ThetaLowerSegment.join cell254787840 cell254820608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell254853376 cell254886144)
                      (ThetaLowerSegment.join cell254918912 cell254951680)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell254984448 cell255017216)
                      (ThetaLowerSegment.join cell255049984 cell255082752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell255115520 cell255148288)
                      (ThetaLowerSegment.join cell255181056 cell255213824)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell255246592 cell255279360)
                      (ThetaLowerSegment.join cell255312128 cell255344896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell255377664 cell255410432)
                      (ThetaLowerSegment.join cell255443200 cell255475968))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell255508736 cell255541504)
                      (ThetaLowerSegment.join cell255574272 cell255607040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell255639808 cell255672576)
                      (ThetaLowerSegment.join cell255705344 cell255738112)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell255770880 cell255803648)
                      (ThetaLowerSegment.join cell255836416 cell255869184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell255901952 cell255934720)
                      (ThetaLowerSegment.join cell255967488 cell256033024)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell256065792 cell256098560)
                      (ThetaLowerSegment.join cell256131328 cell256164096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell256196864 cell256229632)
                      (ThetaLowerSegment.join cell256262400 cell256295168)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell256327936 cell256360704)
                      (ThetaLowerSegment.join cell256393472 cell256426240))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell256459008 cell256491776)
                      (ThetaLowerSegment.join cell256524544 cell256557312))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell256590080 cell256622848)
                      (ThetaLowerSegment.join cell256655616 cell256688384))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell256721152 cell256753920)
                      (ThetaLowerSegment.join cell256786688 cell256819456)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell256852224 cell256884992)
                      (ThetaLowerSegment.join cell256917760 cell256950528))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell256983296 cell257016064)
                      (ThetaLowerSegment.join cell257048832 cell257081600))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell257114368 cell257147136)
                      (ThetaLowerSegment.join cell257179904 cell257212672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell257245440 cell257278208)
                      (ThetaLowerSegment.join cell257310976 cell257343744)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell257376512 cell257409280)
                      (ThetaLowerSegment.join cell257442048 cell257474816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell257507584 cell257540352)
                      (ThetaLowerSegment.join cell257573120 cell257605888))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell257638656 cell257671424)
                      (ThetaLowerSegment.join cell257704192 cell257736960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell257769728 cell257802496)
                      (ThetaLowerSegment.join cell257835264 cell257868032)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell257900800 cell257933568)
                      (ThetaLowerSegment.join cell257966336 cell257999104))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell258031872 cell258064640)
                      (ThetaLowerSegment.join cell258097408 cell258130176)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell258162944 cell258195712)
                      (ThetaLowerSegment.join cell258228480 cell258261248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell258294016 cell258326784)
                      (ThetaLowerSegment.join cell258359552 cell258392320)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell258425088 cell258457856)
                      (ThetaLowerSegment.join cell258490624 cell258523392))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell258556160 cell258588928)
                      (ThetaLowerSegment.join cell258621696 cell258654464))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell258687232 cell258720000)
                      (ThetaLowerSegment.join cell258752768 cell258785536))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell258818304 cell258851072)
                      (ThetaLowerSegment.join cell258883840 cell258916608)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell258949376 cell258982144)
                      (ThetaLowerSegment.join cell259014912 cell259047680))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell259080448 cell259113216)
                      (ThetaLowerSegment.join cell259145984 cell259178752))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell259211520 cell259244288)
                      (ThetaLowerSegment.join cell259277056 cell259309824))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell259342592 cell259375360)
                      (ThetaLowerSegment.join cell259408128 cell259440896)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell259473664 cell259506432)
                      (ThetaLowerSegment.join cell259539200 cell259571968))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell259604736 cell259637504)
                      (ThetaLowerSegment.join cell259670272 cell259703040))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell259735808 cell259768576)
                      (ThetaLowerSegment.join cell259801344 cell259834112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell259866880 cell259899648)
                      (ThetaLowerSegment.join cell259932416 cell259965184)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell259997952 cell260030720)
                      (ThetaLowerSegment.join cell260063488 cell260096256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell260129024 cell260161792)
                      (ThetaLowerSegment.join cell260194560 cell260227328)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell260260096 cell260292864)
                      (ThetaLowerSegment.join cell260325632 cell260358400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell260391168 cell260423936)
                      (ThetaLowerSegment.join cell260456704 cell260489472)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell260522240 cell260555008)
                      (ThetaLowerSegment.join cell260587776 cell260620544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell260653312 cell260686080)
                      (ThetaLowerSegment.join cell260718848 cell260751616))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell260784384 cell260817152)
                      (ThetaLowerSegment.join cell260849920 cell260882688))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell260915456 cell260948224)
                      (ThetaLowerSegment.join cell260980992 cell261013760)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell261046528 cell261079296)
                      (ThetaLowerSegment.join cell261112064 cell261144832))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell261177600 cell261210368)
                      (ThetaLowerSegment.join cell261243136 cell261275904))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell261308672 cell261341440)
                      (ThetaLowerSegment.join cell261374208 cell261406976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell261439744 cell261472512)
                      (ThetaLowerSegment.join cell261505280 cell261538048)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell261570816 cell261603584)
                      (ThetaLowerSegment.join cell261636352 cell261669120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell261701888 cell261734656)
                      (ThetaLowerSegment.join cell261767424 cell261800192))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell261832960 cell261865728)
                      (ThetaLowerSegment.join cell261898496 cell261931264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell261964032 cell261996800)
                      (ThetaLowerSegment.join cell262029568 cell262062336)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell262095104 cell262127872)
                      (ThetaLowerSegment.join cell262193408 cell262258944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell262324480 cell262390016)
                      (ThetaLowerSegment.join cell262455552 cell262521088)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell262586624 cell262652160)
                      (ThetaLowerSegment.join cell262717696 cell262783232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell262848768 cell262914304)
                      (ThetaLowerSegment.join cell262979840 cell263045376)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell263110912 cell263176448)
                      (ThetaLowerSegment.join cell263241984 cell263307520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell263373056 cell263438592)
                      (ThetaLowerSegment.join cell263504128 cell263569664))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell263635200 cell263667968)
                      (ThetaLowerSegment.join cell263700736 cell263733504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell263766272 cell263799040)
                      (ThetaLowerSegment.join cell263831808 cell263864576)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell263897344 cell263930112)
                      (ThetaLowerSegment.join cell263962880 cell263995648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell264028416 cell264061184)
                      (ThetaLowerSegment.join cell264093952 cell264126720)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell264159488 cell264192256)
                    (ThetaLowerSegment.join cell264225024 cell264257792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell264290560 cell264323328)
                    (ThetaLowerSegment.join cell264356096 cell264388864)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell264421632 cell264454400)
                    (ThetaLowerSegment.join cell264487168 cell264519936))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell264552704 cell264585472)
                    (ThetaLowerSegment.join cell264618240 cell264651008))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell264683776 cell264716544)
                    (ThetaLowerSegment.join cell264749312 cell264782080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell264814848 cell264847616)
                    (ThetaLowerSegment.join cell264880384 cell264913152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell264945920 cell264978688)
                    (ThetaLowerSegment.join cell265011456 cell265044224))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell265076992 cell265109760)
                    (ThetaLowerSegment.join cell265142528 cell265175296)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell265208064 cell265240832)
                (ThetaLowerSegment.join cell265273600 cell265306368))
              cell265339136)))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
