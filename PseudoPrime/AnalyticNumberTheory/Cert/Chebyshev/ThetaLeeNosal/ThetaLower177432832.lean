/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis16384

/-! # Direct theta estimate up to 177432832 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell152170752 :
    ThetaLowerSegment 152170752 152203520 (15215211428653 / 100000) (15218435038203 / 100000) := by
  exact
    packedTile16384 152170752 152203520 12 1711 12335 27 _ _ (37681 / 2000) (1884053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152203520 :
    ThetaLowerSegment 152203520 152236288 (15218435038203 / 100000) (76108255737 / 500) := by
  exact
    packedTile16384 152203520 152236288 12 1707 12337 27 _ _ (1884071 / 100000) (942037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152236288 :
    ThetaLowerSegment 152236288 152269056 (76108255737 / 500) (1903124662071 / 12500) := by
  exact
    packedTile16384 152236288 152269056 12 1776 12338 27 _ _ (1884093 / 100000) (58878 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152269056 :
    ThetaLowerSegment 152269056 152301824 (1903124662071 / 12500) (3807060435219 / 25000) := by
  exact
    packedTile16384 152269056 152301824 12 1722 12339 27 _ _ (942057 / 50000) (1884117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152301824 :
    ThetaLowerSegment 152301824 152334592 (3807060435219 / 25000) (761577325771 / 5000) := by
  exact
    packedTile16384 152301824 152334592 12 1754 12341 27 _ _ (235517 / 12500) (1884139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152334592 :
    ThetaLowerSegment 152334592 152367360 (761577325771 / 5000) (3046951800621 / 20000) := by
  exact
    packedTile16384 152334592 152367360 12 1705 12342 27 _ _ (1884157 / 100000) (11776 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152367360 :
    ThetaLowerSegment 152367360 152400128 (3046951800621 / 20000) (15237973412479 / 100000) := by
  exact
    packedTile16384 152367360 152400128 12 1706 12343 27 _ _ (1884179 / 100000) (942091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152400128 :
    ThetaLowerSegment 152400128 152432896 (15237973412479 / 100000) (1905157667903 / 12500) := by
  exact
    packedTile16384 152400128 152432896 12 1745 12345 27 _ _ (1884201 / 100000) (471051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152432896 :
    ThetaLowerSegment 152432896 152465664 (1905157667903 / 12500) (1905566544077 / 12500) := by
  exact
    packedTile16384 152432896 152465664 12 1736 12346 27 _ _ (942111 / 50000) (75369 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152465664 :
    ThetaLowerSegment 152465664 152498432 (1905566544077 / 12500) (3049563317633 / 20000) := by
  exact
    packedTile16384 152465664 152498432 12 1743 12347 27 _ _ (1884243 / 100000) (942123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152498432 :
    ThetaLowerSegment 152498432 152531200 (3049563317633 / 20000) (1525112724177 / 10000) := by
  exact
    packedTile16384 152498432 152531200 12 1757 12349 27 _ _ (376853 / 20000) (471067 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152531200 :
    ThetaLowerSegment 152531200 152563968 (1525112724177 / 10000) (3813587813779 / 25000) := by
  exact
    packedTile16384 152531200 152563968 12 1711 12350 27 _ _ (942143 / 50000) (1884289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152563968 :
    ThetaLowerSegment 152563968 152596736 (3813587813779 / 25000) (953599163247 / 6250) := by
  exact
    packedTile16384 152563968 152596736 12 1717 12351 27 _ _ (471077 / 25000) (1884311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152596736 :
    ThetaLowerSegment 152596736 152629504 (953599163247 / 6250) (15260938833243 / 100000) := by
  exact
    packedTile16384 152596736 152629504 12 1779 12353 27 _ _ (1884329 / 100000) (471083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152629504 :
    ThetaLowerSegment 152629504 152662272 (15260938833243 / 100000) (30528687711 / 200) := by
  exact
    packedTile16384 152629504 152662272 12 1807 12354 27 _ _ (1884351 / 100000) (942177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152662272 :
    ThetaLowerSegment 152662272 152695040 (30528687711 / 200) (3816904723509 / 25000) := by
  exact
    packedTile16384 152662272 152695040 12 1738 12355 27 _ _ (471093 / 25000) (603 / 32) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152695040 :
    ThetaLowerSegment 152695040 152727808 (3816904723509 / 25000) (7635451696389 / 50000) := by
  exact
    packedTile16384 152695040 152727808 12 1743 12356 27 _ _ (942197 / 50000) (1884397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152727808 :
    ThetaLowerSegment 152727808 152760576 (7635451696389 / 50000) (15274187928123 / 100000) := by
  exact
    packedTile16384 152727808 152760576 12 1743 12358 27 _ _ (376883 / 20000) (942209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152760576 :
    ThetaLowerSegment 152760576 152793344 (15274187928123 / 100000) (3055488093277 / 20000) := by
  exact
    packedTile16384 152760576 152793344 12 1726 12359 27 _ _ (1884437 / 100000) (47111 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152793344 :
    ThetaLowerSegment 152793344 152826112 (3055488093277 / 20000) (15280853219823 / 100000) := by
  exact
    packedTile16384 152793344 152826112 12 1811 12360 27 _ _ (942229 / 50000) (1884461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152826112 :
    ThetaLowerSegment 152826112 152858880 (15280853219823 / 100000) (15284068142703 / 100000) := by
  exact
    packedTile16384 152826112 152858880 12 1706 12362 27 _ _ (11778 / 625) (1884483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152858880 :
    ThetaLowerSegment 152858880 152891648 (15284068142703 / 100000) (15287305715421 / 100000) := by
  exact
    packedTile16384 152858880 152891648 12 1718 12363 27 _ _ (1884501 / 100000) (235563 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152891648 :
    ThetaLowerSegment 152891648 152924416 (15287305715421 / 100000) (7645246221907 / 50000) := by
  exact
    packedTile16384 152891648 152924416 12 1691 12364 27 _ _ (1884523 / 100000) (942263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152924416 :
    ThetaLowerSegment 152924416 152957184 (7645246221907 / 50000) (7646921581523 / 50000) := by
  exact
    packedTile16384 152924416 152957184 12 1778 12366 27 _ _ (58892 / 3125) (1884547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152957184 :
    ThetaLowerSegment 152957184 152989952 (7646921581523 / 50000) (15297067653761 / 100000) := by
  exact
    packedTile16384 152957184 152989952 12 1711 12367 27 _ _ (376913 / 20000) (235571 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell152989952 :
    ThetaLowerSegment 152989952 153022720 (15297067653761 / 100000) (15300354373489 / 100000) := by
  exact
    packedTile16384 152989952 153022720 12 1744 12368 27 _ _ (1884587 / 100000) (188459 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153022720 :
    ThetaLowerSegment 153022720 153055488 (15300354373489 / 100000) (15303716514161 / 100000) := by
  exact
    packedTile16384 153022720 153055488 12 1784 12370 27 _ _ (58894 / 3125) (1884611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153055488 :
    ThetaLowerSegment 153055488 153088256 (15303716514161 / 100000) (15307022155181 / 100000) := by
  exact
    packedTile16384 153055488 153088256 12 1754 12371 27 _ _ (188463 / 10000) (1884633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153088256 :
    ThetaLowerSegment 153088256 153121024 (15307022155181 / 100000) (15310331602337 / 100000) := by
  exact
    packedTile16384 153088256 153121024 12 1756 12372 27 _ _ (1884651 / 100000) (942327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153121024 :
    ThetaLowerSegment 153121024 153153792 (15310331602337 / 100000) (15313652394401 / 100000) := by
  exact
    packedTile16384 153121024 153153792 12 1762 12374 27 _ _ (58896 / 3125) (75387 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153153792 :
    ThetaLowerSegment 153153792 153186560 (15313652394401 / 100000) (15316897837469 / 100000) := by
  exact
    packedTile16384 153153792 153186560 12 1722 12375 27 _ _ (942347 / 50000) (1884697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153186560 :
    ThetaLowerSegment 153186560 153219328 (15316897837469 / 100000) (1915012024853 / 12500) := by
  exact
    packedTile16384 153186560 153219328 12 1697 12376 27 _ _ (376943 / 20000) (942359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153219328 :
    ThetaLowerSegment 153219328 153252096 (1915012024853 / 12500) (957710506391 / 6250) := by
  exact
    packedTile16384 153219328 153252096 12 1736 12378 27 _ _ (1884737 / 100000) (94237 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153252096 :
    ThetaLowerSegment 153252096 153284864 (957710506391 / 6250) (766332190583 / 5000) := by
  exact
    packedTile16384 153252096 153284864 12 1738 12379 27 _ _ (942379 / 50000) (1884761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153284864 :
    ThetaLowerSegment 153284864 153317632 (766332190583 / 5000) (479061046362 / 3125) := by
  exact
    packedTile16384 153284864 153317632 12 1756 12380 27 _ _ (1884779 / 100000) (942391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153317632 :
    ThetaLowerSegment 153317632 153350400 (479061046362 / 3125) (15333133142871 / 100000) := by
  exact
    packedTile16384 153317632 153350400 12 1687 12382 27 _ _ (1884801 / 100000) (471201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153350400 :
    ThetaLowerSegment 153350400 153383168 (15333133142871 / 100000) (15336478701921 / 100000) := by
  exact
    packedTile16384 153350400 153383168 12 1775 12383 27 _ _ (942411 / 50000) (75393 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153383168 :
    ThetaLowerSegment 153383168 153415936 (15336478701921 / 100000) (15339720631881 / 100000) := by
  exact
    packedTile16384 153383168 153415936 12 1720 12384 27 _ _ (1884843 / 100000) (942423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153415936 :
    ThetaLowerSegment 153415936 153448704 (15339720631881 / 100000) (7671516169843 / 50000) := by
  exact
    packedTile16384 153415936 153448704 12 1757 12386 27 _ _ (376973 / 20000) (471217 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153448704 :
    ThetaLowerSegment 153448704 153481472 (7671516169843 / 50000) (7673144711347 / 50000) := by
  exact
    packedTile16384 153448704 153481472 12 1728 12387 27 _ _ (942443 / 50000) (1884889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153481472 :
    ThetaLowerSegment 153481472 153514240 (7673144711347 / 50000) (7674782696399 / 50000) := by
  exact
    packedTile16384 153481472 153514240 12 1738 12388 27 _ _ (471227 / 25000) (1884911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153514240 :
    ThetaLowerSegment 153514240 153547008 (7674782696399 / 50000) (7676433894203 / 50000) := by
  exact
    packedTile16384 153514240 153547008 12 1752 12390 27 _ _ (1884929 / 100000) (471233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153547008 :
    ThetaLowerSegment 153547008 153579776 (7676433894203 / 50000) (3839033601689 / 25000) := by
  exact
    packedTile16384 153547008 153579776 12 1733 12391 27 _ _ (37699 / 2000) (1884953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153579776 :
    ThetaLowerSegment 153579776 153612544 (3839033601689 / 25000) (959962095209 / 6250) := by
  exact
    packedTile16384 153579776 153612544 12 1729 12392 27 _ _ (471243 / 25000) (75399 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153612544 :
    ThetaLowerSegment 153612544 153645312 (959962095209 / 6250) (614508972239 / 4000) := by
  exact
    packedTile16384 153612544 153645312 12 1767 12394 27 _ _ (1884993 / 100000) (471249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153645312 :
    ThetaLowerSegment 153645312 153678080 (614508972239 / 4000) (15365989150223 / 100000) := by
  exact
    packedTile16384 153645312 153678080 12 1732 12395 27 _ _ (942507 / 50000) (1885017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153678080 :
    ThetaLowerSegment 153678080 153710848 (15365989150223 / 100000) (15369246492431 / 100000) := by
  exact
    packedTile16384 153678080 153710848 12 1728 12396 27 _ _ (471259 / 25000) (1885039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153710848 :
    ThetaLowerSegment 153710848 153743616 (15369246492431 / 100000) (3074513592573 / 20000) := by
  exact
    packedTile16384 153710848 153743616 12 1762 12398 27 _ _ (1885057 / 100000) (94253 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153743616 :
    ThetaLowerSegment 153743616 153776384 (3074513592573 / 20000) (15375870619521 / 100000) := by
  exact
    packedTile16384 153743616 153776384 12 1752 12399 27 _ _ (942539 / 50000) (1885081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153776384 :
    ThetaLowerSegment 153776384 153809152 (15375870619521 / 100000) (15379145038221 / 100000) := by
  exact
    packedTile16384 153776384 153809152 12 1737 12400 27 _ _ (18851 / 1000) (1885103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153809152 :
    ThetaLowerSegment 153809152 153841920 (15379145038221 / 100000) (15382455310697 / 100000) := by
  exact
    packedTile16384 153809152 153841920 12 1756 12401 27 _ _ (1885121 / 100000) (471281 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153841920 :
    ThetaLowerSegment 153841920 153874688 (15382455310697 / 100000) (3077148599669 / 20000) := by
  exact
    packedTile16384 153841920 153874688 12 1744 12403 27 _ _ (942571 / 50000) (377029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153874688 :
    ThetaLowerSegment 153874688 153907456 (3077148599669 / 20000) (123113241147 / 800) := by
  exact
    packedTile16384 153874688 153907456 12 1810 12404 27 _ _ (1885163 / 100000) (942583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153907456 :
    ThetaLowerSegment 153907456 153940224 (123113241147 / 800) (192404428779 / 1250) := by
  exact
    packedTile16384 153907456 153940224 12 1697 12405 27 _ _ (377037 / 20000) (471297 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153940224 :
    ThetaLowerSegment 153940224 153972992 (192404428779 / 1250) (7697780518863 / 50000) := by
  exact
    packedTile16384 153940224 153972992 12 1701 12407 27 _ _ (942603 / 50000) (1885209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell153972992 :
    ThetaLowerSegment 153972992 154005760 (7697780518863 / 50000) (7699409354991 / 50000) := by
  exact
    packedTile16384 153972992 154005760 12 1728 12408 27 _ _ (1885227 / 100000) (188523 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154005760 :
    ThetaLowerSegment 154005760 154038528 (7699409354991 / 50000) (7701030669131 / 50000) := by
  exact
    packedTile16384 154005760 154038528 12 1720 12409 27 _ _ (1885249 / 100000) (471313 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154038528 :
    ThetaLowerSegment 154038528 154071296 (7701030669131 / 50000) (7702653886601 / 50000) := by
  exact
    packedTile16384 154038528 154071296 12 1722 12411 27 _ _ (188527 / 10000) (1885273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154071296 :
    ThetaLowerSegment 154071296 154104064 (7702653886601 / 50000) (3081726308247 / 20000) := by
  exact
    packedTile16384 154071296 154104064 12 1763 12412 27 _ _ (1885291 / 100000) (942647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154104064 :
    ThetaLowerSegment 154104064 154136832 (3081726308247 / 20000) (123294994223 / 800) := by
  exact
    packedTile16384 154104064 154136832 12 1720 12413 27 _ _ (58916 / 3125) (377063 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154136832 :
    ThetaLowerSegment 154136832 154169600 (123294994223 / 800) (15415118937689 / 100000) := by
  exact
    packedTile16384 154136832 154169600 12 1721 12415 27 _ _ (942667 / 50000) (1885337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154169600 :
    ThetaLowerSegment 154169600 154202368 (15415118937689 / 100000) (7709198785017 / 50000) := by
  exact
    packedTile16384 154169600 154202368 12 1739 12416 27 _ _ (377071 / 20000) (942679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154202368 :
    ThetaLowerSegment 154202368 154235136 (7709198785017 / 50000) (7710834348697 / 50000) := by
  exact
    packedTile16384 154202368 154235136 12 1735 12417 27 _ _ (58918 / 3125) (1885379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154235136 :
    ThetaLowerSegment 154235136 154267904 (7710834348697 / 50000) (96405673809 / 625) := by
  exact
    packedTile16384 154235136 154267904 12 1718 12419 27 _ _ (1885397 / 100000) (9427 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154267904 :
    ThetaLowerSegment 154267904 154300672 (96405673809 / 625) (3857054651301 / 25000) := by
  exact
    packedTile16384 154267904 154300672 12 1756 12420 27 _ _ (1885419 / 100000) (942711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154300672 :
    ThetaLowerSegment 154300672 154333440 (3857054651301 / 25000) (3857869632741 / 25000) := by
  exact
    packedTile16384 154300672 154333440 12 1729 12421 27 _ _ (11784 / 625) (1885443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154333440 :
    ThetaLowerSegment 154333440 154366208 (3857869632741 / 25000) (3086948452791 / 20000) := by
  exact
    packedTile16384 154333440 154366208 12 1731 12423 27 _ _ (1885461 / 100000) (235683 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154366208 :
    ThetaLowerSegment 154366208 154398976 (3086948452791 / 20000) (3087615913419 / 20000) := by
  exact
    packedTile16384 154366208 154398976 12 1770 12424 27 _ _ (942741 / 50000) (377097 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154398976 :
    ThetaLowerSegment 154398976 154431744 (3087615913419 / 20000) (3088260755787 / 20000) := by
  exact
    packedTile16384 154398976 154431744 12 1710 12425 27 _ _ (58922 / 3125) (1885507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154431744 :
    ThetaLowerSegment 154431744 154464512 (3088260755787 / 20000) (1544465058581 / 10000) := by
  exact
    packedTile16384 154431744 154464512 12 1775 12427 27 _ _ (75421 / 4000) (235691 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154464512 :
    ThetaLowerSegment 154464512 154497280 (1544465058581 / 10000) (7723995886661 / 50000) := by
  exact
    packedTile16384 154464512 154497280 12 1772 12428 27 _ _ (942773 / 50000) (1885549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154497280 :
    ThetaLowerSegment 154497280 154530048 (7723995886661 / 50000) (3090227756929 / 20000) := by
  exact
    packedTile16384 154497280 154530048 12 1669 12429 27 _ _ (1885567 / 100000) (188557 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154530048 :
    ThetaLowerSegment 154530048 154562816 (3090227756929 / 20000) (15454483817757 / 100000) := by
  exact
    packedTile16384 154530048 154562816 12 1774 12431 27 _ _ (471397 / 25000) (1885591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154562816 :
    ThetaLowerSegment 154562816 154595584 (15454483817757 / 100000) (15457823233067 / 100000) := by
  exact
    packedTile16384 154562816 154595584 12 1771 12432 27 _ _ (188561 / 10000) (1885613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154595584 :
    ThetaLowerSegment 154595584 154628352 (15457823233067 / 100000) (7730537973271 / 50000) := by
  exact
    packedTile16384 154595584 154628352 12 1725 12433 27 _ _ (1885631 / 100000) (942817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154628352 :
    ThetaLowerSegment 154628352 154661120 (7730537973271 / 50000) (7732209603769 / 50000) := by
  exact
    packedTile16384 154628352 154661120 12 1773 12434 27 _ _ (471413 / 25000) (377131 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154661120 :
    ThetaLowerSegment 154661120 154693888 (7732209603769 / 50000) (7733865224663 / 50000) := by
  exact
    packedTile16384 154661120 154693888 12 1756 12436 27 _ _ (1885673 / 100000) (471419 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154693888 :
    ThetaLowerSegment 154693888 154726656 (7733865224663 / 50000) (1933872437511 / 12500) := by
  exact
    packedTile16384 154693888 154726656 12 1723 12437 27 _ _ (942847 / 50000) (1885697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154726656 :
    ThetaLowerSegment 154726656 154759424 (1933872437511 / 12500) (773708035149 / 5000) := by
  exact
    packedTile16384 154726656 154759424 12 1687 12438 27 _ _ (471429 / 25000) (1885719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154759424 :
    ThetaLowerSegment 154759424 154792192 (773708035149 / 5000) (3869358585603 / 25000) := by
  exact
    packedTile16384 154759424 154792192 12 1736 12440 27 _ _ (1885737 / 100000) (94287 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154792192 :
    ThetaLowerSegment 154792192 154824960 (3869358585603 / 25000) (1935085202211 / 12500) := by
  exact
    packedTile16384 154792192 154824960 12 1722 12441 27 _ _ (942879 / 50000) (1885761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154824960 :
    ThetaLowerSegment 154824960 154857728 (1935085202211 / 12500) (15483991159833 / 100000) := by
  exact
    packedTile16384 154824960 154857728 12 1755 12442 27 _ _ (1885779 / 100000) (942891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154857728 :
    ThetaLowerSegment 154857728 154890496 (15483991159833 / 100000) (15487221535233 / 100000) := by
  exact
    packedTile16384 154857728 154890496 12 1713 12444 27 _ _ (9429 / 500) (1885803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154890496 :
    ThetaLowerSegment 154890496 154923264 (15487221535233 / 100000) (7745259918081 / 50000) := by
  exact
    packedTile16384 154890496 154923264 12 1749 12445 27 _ _ (1885821 / 100000) (58932 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154923264 :
    ThetaLowerSegment 154923264 154956032 (7745259918081 / 50000) (3098768161137 / 20000) := by
  exact
    packedTile16384 154923264 154956032 12 1761 12446 27 _ _ (1885843 / 100000) (942923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154956032 :
    ThetaLowerSegment 154956032 154988800 (3098768161137 / 20000) (15497058089669 / 100000) := by
  exact
    packedTile16384 154956032 154988800 12 1706 12448 27 _ _ (235733 / 12500) (1885867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell154988800 :
    ThetaLowerSegment 154988800 155021568 (15497058089669 / 100000) (15500339529569 / 100000) := by
  exact
    packedTile16384 154988800 155021568 12 1740 12449 27 _ _ (377177 / 20000) (58934 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155021568 :
    ThetaLowerSegment 155021568 155054336 (15500339529569 / 100000) (15503573858359 / 100000) := by
  exact
    packedTile16384 155021568 155054336 12 1715 12450 27 _ _ (942953 / 50000) (1885909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155054336 :
    ThetaLowerSegment 155054336 155087104 (15503573858359 / 100000) (15506896861733 / 100000) := by
  exact
    packedTile16384 155054336 155087104 12 1762 12452 27 _ _ (1885927 / 100000) (188593 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155087104 :
    ThetaLowerSegment 155087104 155119872 (15506896861733 / 100000) (15510202928577 / 100000) := by
  exact
    packedTile16384 155087104 155119872 12 1753 12453 27 _ _ (471487 / 25000) (1885951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155119872 :
    ThetaLowerSegment 155119872 155152640 (15510202928577 / 100000) (7756735656427 / 50000) := by
  exact
    packedTile16384 155119872 155152640 12 1733 12454 27 _ _ (1885969 / 100000) (471493 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155152640 :
    ThetaLowerSegment 155152640 155185408 (7756735656427 / 50000) (7758384011687 / 50000) := by
  exact
    packedTile16384 155152640 155185408 12 1748 12456 27 _ _ (188599 / 10000) (1885993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155185408 :
    ThetaLowerSegment 155185408 155218176 (7758384011687 / 50000) (7759986178881 / 50000) := by
  exact
    packedTile16384 155185408 155218176 12 1699 12457 27 _ _ (471503 / 25000) (377203 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155218176 :
    ThetaLowerSegment 155218176 155250944 (7759986178881 / 50000) (15523248397083 / 100000) := by
  exact
    packedTile16384 155218176 155250944 12 1737 12458 27 _ _ (1886033 / 100000) (471509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155250944 :
    ThetaLowerSegment 155250944 155283712 (15523248397083 / 100000) (15526569738177 / 100000) := by
  exact
    packedTile16384 155250944 155283712 12 1761 12459 27 _ _ (943027 / 50000) (1886057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155283712 :
    ThetaLowerSegment 155283712 155316480 (15526569738177 / 100000) (7764954988501 / 50000) := by
  exact
    packedTile16384 155283712 155316480 12 1771 12461 27 _ _ (75443 / 4000) (943039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155316480 :
    ThetaLowerSegment 155316480 155349248 (7764954988501 / 50000) (1553310313753 / 10000) := by
  exact
    packedTile16384 155316480 155349248 12 1693 12462 27 _ _ (117881 / 6250) (1886099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155349248 :
    ThetaLowerSegment 155349248 155382016 (1553310313753 / 10000) (15536292561377 / 100000) := by
  exact
    packedTile16384 155349248 155382016 12 1691 12463 27 _ _ (1886117 / 100000) (47153 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155382016 :
    ThetaLowerSegment 155382016 155414784 (15536292561377 / 100000) (3107920923941 / 20000) := by
  exact
    packedTile16384 155382016 155414784 12 1756 12465 27 _ _ (943069 / 50000) (1886141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155414784 :
    ThetaLowerSegment 155414784 155447552 (3107920923941 / 20000) (1942854451259 / 12500) := by
  exact
    packedTile16384 155414784 155447552 12 1713 12466 27 _ _ (1886159 / 100000) (943081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155447552 :
    ThetaLowerSegment 155447552 155480320 (1942854451259 / 12500) (3886531748543 / 25000) := by
  exact
    packedTile16384 155447552 155480320 12 1745 12467 27 _ _ (94309 / 5000) (1886183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155480320 :
    ThetaLowerSegment 155480320 155513088 (3886531748543 / 25000) (15549373146093 / 100000) := by
  exact
    packedTile16384 155480320 155513088 12 1721 12469 27 _ _ (1886201 / 100000) (471551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155513088 :
    ThetaLowerSegment 155513088 155545856 (15549373146093 / 100000) (15552760802601 / 100000) := by
  exact
    packedTile16384 155513088 155545856 12 1796 12470 27 _ _ (1886223 / 100000) (943113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155545856 :
    ThetaLowerSegment 155545856 155578624 (15552760802601 / 100000) (3111205178193 / 20000) := by
  exact
    packedTile16384 155545856 155578624 12 1731 12471 27 _ _ (471561 / 25000) (1886247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155578624 :
    ThetaLowerSegment 155578624 155611392 (3111205178193 / 20000) (388984916163 / 2500) := by
  exact
    packedTile16384 155578624 155611392 12 1787 12473 27 _ _ (377253 / 20000) (471567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155611392 :
    ThetaLowerSegment 155611392 155644160 (388984916163 / 2500) (7781336562651 / 50000) := by
  exact
    packedTile16384 155611392 155644160 12 1737 12474 27 _ _ (943143 / 50000) (1886289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155644160 :
    ThetaLowerSegment 155644160 155676928 (7781336562651 / 50000) (15565942095333 / 100000) := by
  exact
    packedTile16384 155644160 155676928 12 1733 12475 27 _ _ (1886307 / 100000) (188631 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155676928 :
    ThetaLowerSegment 155676928 155709696 (15565942095333 / 100000) (3113852029257 / 20000) := by
  exact
    packedTile16384 155676928 155709696 12 1759 12477 27 _ _ (235791 / 12500) (1886331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155709696 :
    ThetaLowerSegment 155709696 155742464 (3113852029257 / 20000) (15572459394189 / 100000) := by
  exact
    packedTile16384 155709696 155742464 12 1696 12478 27 _ _ (1886349 / 100000) (117897 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155742464 :
    ThetaLowerSegment 155742464 155775232 (15572459394189 / 100000) (15575641700379 / 100000) := by
  exact
    packedTile16384 155742464 155775232 12 1687 12479 27 _ _ (188637 / 10000) (1886373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155775232 :
    ThetaLowerSegment 155775232 155808000 (15575641700379 / 100000) (15578984385231 / 100000) := by
  exact
    packedTile16384 155775232 155808000 12 1772 12480 27 _ _ (1886391 / 100000) (943197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155808000 :
    ThetaLowerSegment 155808000 155840768 (15578984385231 / 100000) (3116465421459 / 20000) := by
  exact
    packedTile16384 155808000 155840768 12 1772 12482 27 _ _ (471603 / 25000) (377283 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155840768 :
    ThetaLowerSegment 155840768 155873536 (3116465421459 / 20000) (7792788715677 / 50000) := by
  exact
    packedTile16384 155840768 155873536 12 1723 12483 27 _ _ (1886433 / 100000) (471609 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155873536 :
    ThetaLowerSegment 155873536 155906304 (7792788715677 / 50000) (1948611491379 / 12500) := by
  exact
    packedTile16384 155873536 155906304 12 1757 12484 27 _ _ (943227 / 50000) (1886457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155906304 :
    ThetaLowerSegment 155906304 155939072 (1948611491379 / 12500) (974517974127 / 6250) := by
  exact
    packedTile16384 155906304 155939072 12 1800 12486 27 _ _ (75459 / 4000) (943239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155939072 :
    ThetaLowerSegment 155939072 155971840 (974517974127 / 6250) (974716763643 / 6250) := by
  exact
    packedTile16384 155939072 155971840 12 1686 12487 27 _ _ (58953 / 3125) (1886499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell155971840 :
    ThetaLowerSegment 155971840 156004608 (974716763643 / 6250) (15598741325283 / 100000) := by
  exact
    packedTile16384 155971840 156004608 12 1735 12488 27 _ _ (1886517 / 100000) (47163 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156004608 :
    ThetaLowerSegment 156004608 156037376 (15598741325283 / 100000) (15602042766783 / 100000) := by
  exact
    packedTile16384 156004608 156037376 12 1750 12490 27 _ _ (943269 / 50000) (1886541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156037376 :
    ThetaLowerSegment 156037376 156070144 (15602042766783 / 100000) (1560531217353 / 10000) := by
  exact
    packedTile16384 156037376 156070144 12 1733 12491 27 _ _ (1886559 / 100000) (943281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156070144 :
    ThetaLowerSegment 156070144 156102912 (1560531217353 / 10000) (1560863632749 / 10000) := by
  exact
    packedTile16384 156070144 156102912 12 1762 12492 27 _ _ (94329 / 5000) (1886583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156102912 :
    ThetaLowerSegment 156102912 156135680 (1560863632749 / 10000) (15611951085447 / 100000) := by
  exact
    packedTile16384 156102912 156135680 12 1757 12494 27 _ _ (1886601 / 100000) (471651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156135680 :
    ThetaLowerSegment 156135680 156168448 (15611951085447 / 100000) (15615224374617 / 100000) := by
  exact
    packedTile16384 156135680 156168448 12 1735 12495 27 _ _ (943311 / 50000) (15093 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156168448 :
    ThetaLowerSegment 156168448 156201216 (15615224374617 / 100000) (780923564361 / 5000) := by
  exact
    packedTile16384 156168448 156201216 12 1721 12496 27 _ _ (1886643 / 100000) (943323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156201216 :
    ThetaLowerSegment 156201216 156233984 (780923564361 / 5000) (3905420597337 / 25000) := by
  exact
    packedTile16384 156201216 156233984 12 1702 12498 27 _ _ (235833 / 12500) (1886667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156233984 :
    ThetaLowerSegment 156233984 156266752 (3905420597337 / 25000) (15624974654673 / 100000) := by
  exact
    packedTile16384 156233984 156266752 12 1745 12499 27 _ _ (377337 / 20000) (58959 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156266752 :
    ThetaLowerSegment 156266752 156299520 (15624974654673 / 100000) (15628278276879 / 100000) := by
  exact
    packedTile16384 156266752 156299520 12 1751 12500 27 _ _ (943353 / 50000) (1886709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156299520 :
    ThetaLowerSegment 156299520 156332288 (15628278276879 / 100000) (781580228829 / 5000) := by
  exact
    packedTile16384 156299520 156332288 12 1763 12501 27 _ _ (1886727 / 100000) (188673 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156332288 :
    ThetaLowerSegment 156332288 156365056 (781580228829 / 5000) (977182474551 / 6250) := by
  exact
    packedTile16384 156332288 156365056 12 1757 12503 27 _ _ (471687 / 25000) (1886751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156365056 :
    ThetaLowerSegment 156365056 156397824 (977182474551 / 6250) (7819061663289 / 50000) := by
  exact
    packedTile16384 156365056 156397824 12 1698 12504 27 _ _ (1886769 / 100000) (471693 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156397824 :
    ThetaLowerSegment 156397824 156430592 (7819061663289 / 50000) (7820703170589 / 50000) := by
  exact
    packedTile16384 156397824 156430592 12 1740 12505 27 _ _ (188679 / 10000) (1886793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156430592 :
    ThetaLowerSegment 156430592 156463360 (7820703170589 / 50000) (15644679958263 / 100000) := by
  exact
    packedTile16384 156430592 156463360 12 1735 12507 27 _ _ (1886811 / 100000) (943407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156463360 :
    ThetaLowerSegment 156463360 156496128 (15644679958263 / 100000) (15648032858727 / 100000) := by
  exact
    packedTile16384 156463360 156496128 12 1777 12508 27 _ _ (117927 / 6250) (377367 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156496128 :
    ThetaLowerSegment 156496128 156528896 (15648032858727 / 100000) (1565129900127 / 10000) := by
  exact
    packedTile16384 156496128 156528896 12 1731 12509 27 _ _ (1886853 / 100000) (235857 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156528896 :
    ThetaLowerSegment 156528896 156561664 (1565129900127 / 10000) (7827287307267 / 50000) := by
  exact
    packedTile16384 156528896 156561664 12 1736 12511 27 _ _ (943437 / 50000) (1886877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156561664 :
    ThetaLowerSegment 156561664 156594432 (7827287307267 / 50000) (15657738937449 / 100000) := by
  exact
    packedTile16384 156561664 156594432 12 1677 12512 27 _ _ (377379 / 20000) (943449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156594432 :
    ThetaLowerSegment 156594432 156627200 (15657738937449 / 100000) (1957629893973 / 12500) := by
  exact
    packedTile16384 156594432 156627200 12 1749 12513 27 _ _ (377383 / 20000) (943459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156627200 :
    ThetaLowerSegment 156627200 156659968 (1957629893973 / 12500) (1958042189489 / 12500) := by
  exact
    packedTile16384 156627200 156659968 12 1748 12515 27 _ _ (235867 / 12500) (1886939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156659968 :
    ThetaLowerSegment 156659968 156692736 (1958042189489 / 12500) (7833797201847 / 50000) := by
  exact
    packedTile16384 156659968 156692736 12 1726 12516 27 _ _ (1886957 / 100000) (23587 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156692736 :
    ThetaLowerSegment 156692736 156725504 (7833797201847 / 50000) (3917728399499 / 25000) := by
  exact
    packedTile16384 156692736 156725504 12 1759 12517 27 _ _ (943489 / 50000) (1886981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156725504 :
    ThetaLowerSegment 156725504 156758272 (3917728399499 / 25000) (62696833193 / 400) := by
  exact
    packedTile16384 156725504 156758272 12 1746 12519 27 _ _ (1886999 / 100000) (943501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156758272 :
    ThetaLowerSegment 156758272 156791040 (62696833193 / 400) (1567748982603 / 10000) := by
  exact
    packedTile16384 156758272 156791040 12 1739 12520 27 _ _ (94351 / 5000) (1887023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156791040 :
    ThetaLowerSegment 156791040 156823808 (1567748982603 / 10000) (3136141446187 / 20000) := by
  exact
    packedTile16384 156791040 156823808 12 1705 12521 27 _ _ (1887041 / 100000) (471761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156823808 :
    ThetaLowerSegment 156823808 156856576 (3136141446187 / 20000) (125472001233 / 800) := by
  exact
    packedTile16384 156823808 156856576 12 1745 12522 27 _ _ (943531 / 50000) (377413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156856576 :
    ThetaLowerSegment 156856576 156889344 (125472001233 / 800) (25099684079 / 160) := by
  exact
    packedTile16384 156856576 156889344 12 1750 12524 27 _ _ (1887083 / 100000) (943543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156889344 :
    ThetaLowerSegment 156889344 156922112 (25099684079 / 160) (15690610642687 / 100000) := by
  exact
    packedTile16384 156889344 156922112 12 1753 12525 27 _ _ (58972 / 3125) (1887107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156922112 :
    ThetaLowerSegment 156922112 156954880 (15690610642687 / 100000) (490433310416 / 3125) := by
  exact
    packedTile16384 156922112 156954880 12 1725 12526 27 _ _ (15097 / 800) (235891 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156954880 :
    ThetaLowerSegment 156954880 156987648 (490433310416 / 3125) (15697121258437 / 100000) := by
  exact
    packedTile16384 156954880 156987648 12 1725 12528 27 _ _ (377429 / 20000) (471787 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell156987648 :
    ThetaLowerSegment 156987648 157020416 (15697121258437 / 100000) (3140078343423 / 20000) := by
  exact
    packedTile16384 156987648 157020416 12 1733 12529 27 _ _ (943583 / 50000) (1887169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157020416 :
    ThetaLowerSegment 157020416 157053184 (3140078343423 / 20000) (15703622581259 / 100000) := by
  exact
    packedTile16384 157020416 157053184 12 1712 12530 27 _ _ (1887187 / 100000) (188719 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157053184 :
    ThetaLowerSegment 157053184 157085952 (15703622581259 / 100000) (15706961052211 / 100000) := by
  exact
    packedTile16384 157053184 157085952 12 1769 12532 27 _ _ (235901 / 12500) (1887211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157085952 :
    ThetaLowerSegment 157085952 157118720 (15706961052211 / 100000) (15710214635007 / 100000) := by
  exact
    packedTile16384 157085952 157118720 12 1724 12533 27 _ _ (1887229 / 100000) (58976 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157118720 :
    ThetaLowerSegment 157118720 157151488 (15710214635007 / 100000) (15713473915757 / 100000) := by
  exact
    packedTile16384 157118720 157151488 12 1727 12534 27 _ _ (7549 / 400) (1887253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157151488 :
    ThetaLowerSegment 157151488 157184256 (15713473915757 / 100000) (15716693600083 / 100000) := by
  exact
    packedTile16384 157151488 157184256 12 1706 12536 27 _ _ (1887271 / 100000) (943637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157184256 :
    ThetaLowerSegment 157184256 157217024 (15716693600083 / 100000) (15720064301809 / 100000) := by
  exact
    packedTile16384 157184256 157217024 12 1786 12537 27 _ _ (1887291 / 100000) (943647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157217024 :
    ThetaLowerSegment 157217024 157249792 (15720064301809 / 100000) (15723333126193 / 100000) := by
  exact
    packedTile16384 157217024 157249792 12 1732 12538 27 _ _ (117957 / 6250) (377463 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157249792 :
    ThetaLowerSegment 157249792 157282560 (15723333126193 / 100000) (3931655686903 / 25000) := by
  exact
    packedTile16384 157249792 157282560 12 1743 12539 27 _ _ (1887333 / 100000) (235917 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157282560 :
    ThetaLowerSegment 157282560 157315328 (3931655686903 / 25000) (7864901469551 / 50000) := by
  exact
    packedTile16384 157282560 157315328 12 1685 12541 27 _ _ (943677 / 50000) (1887357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157315328 :
    ThetaLowerSegment 157315328 157348096 (7864901469551 / 50000) (7866535936301 / 50000) := by
  exact
    packedTile16384 157315328 157348096 12 1732 12542 27 _ _ (15099 / 800) (943689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157348096 :
    ThetaLowerSegment 157348096 157380864 (7866535936301 / 50000) (7868194013687 / 50000) := by
  exact
    packedTile16384 157348096 157380864 12 1757 12543 27 _ _ (471849 / 25000) (1887399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157380864 :
    ThetaLowerSegment 157380864 157413632 (7868194013687 / 50000) (7869843615271 / 50000) := by
  exact
    packedTile16384 157380864 157413632 12 1748 12545 27 _ _ (235927 / 12500) (1887419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157413632 :
    ThetaLowerSegment 157413632 157446400 (7869843615271 / 50000) (7871466811091 / 50000) := by
  exact
    packedTile16384 157413632 157446400 12 1720 12546 27 _ _ (1887437 / 100000) (23593 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157446400 :
    ThetaLowerSegment 157446400 157479168 (7871466811091 / 50000) (1574626687301 / 10000) := by
  exact
    packedTile16384 157446400 157479168 12 1766 12547 27 _ _ (943729 / 50000) (1887461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157479168 :
    ThetaLowerSegment 157479168 157511936 (1574626687301 / 10000) (15749571848739 / 100000) := by
  exact
    packedTile16384 157479168 157511936 12 1751 12549 27 _ _ (1887479 / 100000) (943741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157511936 :
    ThetaLowerSegment 157511936 157544704 (15749571848739 / 100000) (15752835336239 / 100000) := by
  exact
    packedTile16384 157511936 157544704 12 1729 12550 27 _ _ (151 / 8) (1887503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157544704 :
    ThetaLowerSegment 157544704 157577472 (15752835336239 / 100000) (15756153596399 / 100000) := by
  exact
    packedTile16384 157544704 157577472 12 1758 12551 27 _ _ (11797 / 625) (1887523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157577472 :
    ThetaLowerSegment 157577472 157610240 (15756153596399 / 100000) (787970102723 / 5000) := by
  exact
    packedTile16384 157577472 157610240 12 1721 12552 27 _ _ (1887541 / 100000) (235943 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157610240 :
    ThetaLowerSegment 157610240 157643008 (787970102723 / 5000) (7881334712141 / 50000) := by
  exact
    packedTile16384 157610240 157643008 12 1731 12554 27 _ _ (943781 / 50000) (377513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157643008 :
    ThetaLowerSegment 157643008 157675776 (7881334712141 / 50000) (985364327389 / 6250) := by
  exact
    packedTile16384 157643008 157675776 12 1674 12555 27 _ _ (1887583 / 100000) (943793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157675776 :
    ThetaLowerSegment 157675776 157708544 (985364327389 / 6250) (492786689766 / 3125) := by
  exact
    packedTile16384 157675776 157708544 12 1772 12556 27 _ _ (471901 / 25000) (1887607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157708544 :
    ThetaLowerSegment 157708544 157741312 (492786689766 / 3125) (1971564159921 / 12500) := by
  exact
    packedTile16384 157708544 157741312 12 1769 12558 27 _ _ (235953 / 12500) (1887627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157741312 :
    ThetaLowerSegment 157741312 157774080 (1971564159921 / 12500) (15775682635323 / 100000) := by
  exact
    packedTile16384 157741312 157774080 12 1679 12559 27 _ _ (377529 / 20000) (58989 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157774080 :
    ThetaLowerSegment 157774080 157806848 (15775682635323 / 100000) (15778978500159 / 100000) := by
  exact
    packedTile16384 157774080 157806848 12 1746 12560 27 _ _ (943833 / 50000) (1887669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157806848 :
    ThetaLowerSegment 157806848 157839616 (15778978500159 / 100000) (15782270626287 / 100000) := by
  exact
    packedTile16384 157806848 157839616 12 1744 12562 27 _ _ (1887687 / 100000) (188769 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157839616 :
    ThetaLowerSegment 157839616 157872384 (15782270626287 / 100000) (493298070222 / 3125) := by
  exact
    packedTile16384 157839616 157872384 12 1731 12563 27 _ _ (1887707 / 100000) (188771 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157872384 :
    ThetaLowerSegment 157872384 157905152 (493298070222 / 3125) (493400479466 / 3125) := by
  exact
    packedTile16384 157872384 157905152 12 1736 12564 27 _ _ (117983 / 6250) (1887731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157905152 :
    ThetaLowerSegment 157905152 157937920 (493400479466 / 3125) (789604246209 / 5000) := by
  exact
    packedTile16384 157905152 157937920 12 1732 12566 27 _ _ (1887749 / 100000) (235969 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157937920 :
    ThetaLowerSegment 157937920 157970688 (789604246209 / 5000) (197442356521 / 1250) := by
  exact
    packedTile16384 157937920 157970688 12 1750 12567 27 _ _ (188777 / 10000) (1887773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell157970688 :
    ThetaLowerSegment 157970688 158003456 (197442356521 / 1250) (493708775912 / 3125) := by
  exact
    packedTile16384 157970688 158003456 12 1744 12568 27 _ _ (1887791 / 100000) (943897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158003456 :
    ThetaLowerSegment 158003456 158036224 (493708775912 / 3125) (7900958268619 / 50000) := by
  exact
    packedTile16384 158003456 158036224 12 1714 12569 27 _ _ (1887811 / 100000) (943907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158036224 :
    ThetaLowerSegment 158036224 158068992 (7900958268619 / 50000) (1580530708351 / 10000) := by
  exact
    packedTile16384 158036224 158068992 12 1796 12571 27 _ _ (235979 / 12500) (377567 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158068992 :
    ThetaLowerSegment 158068992 158101760 (1580530708351 / 10000) (15808548527111 / 100000) := by
  exact
    packedTile16384 158068992 158101760 12 1717 12572 27 _ _ (1887853 / 100000) (117991 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158101760 :
    ThetaLowerSegment 158101760 158134528 (15808548527111 / 100000) (15811803220163 / 100000) := by
  exact
    packedTile16384 158101760 158134528 12 1724 12573 27 _ _ (1887873 / 100000) (471969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158134528 :
    ThetaLowerSegment 158134528 158167296 (15811803220163 / 100000) (15814910693687 / 100000) := by
  exact
    packedTile16384 158134528 158167296 12 1646 12575 27 _ _ (943947 / 50000) (1887897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158167296 :
    ThetaLowerSegment 158167296 158200064 (15814910693687 / 100000) (7909125207661 / 50000) := by
  exact
    packedTile16384 158167296 158200064 12 1769 12576 27 _ _ (377583 / 20000) (943959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158200064 :
    ThetaLowerSegment 158200064 158232832 (7909125207661 / 50000) (7910785647373 / 50000) := by
  exact
    packedTile16384 158200064 158232832 12 1759 12577 27 _ _ (58998 / 3125) (1887939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158232832 :
    ThetaLowerSegment 158232832 158265600 (7910785647373 / 50000) (7912425337159 / 50000) := by
  exact
    packedTile16384 158232832 158265600 12 1737 12579 27 _ _ (471989 / 25000) (1887959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158265600 :
    ThetaLowerSegment 158265600 158298368 (7912425337159 / 50000) (15828084778919 / 100000) := by
  exact
    packedTile16384 158265600 158298368 12 1713 12580 27 _ _ (1887977 / 100000) (94399 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158298368 :
    ThetaLowerSegment 158298368 158331136 (15828084778919 / 100000) (15831381223427 / 100000) := by
  exact
    packedTile16384 158298368 158331136 12 1746 12581 27 _ _ (943999 / 50000) (1888001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158331136 :
    ThetaLowerSegment 158331136 158363904 (15831381223427 / 100000) (3166918548409 / 20000) := by
  exact
    packedTile16384 158331136 158363904 12 1701 12582 27 _ _ (944009 / 50000) (1888021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158363904 :
    ThetaLowerSegment 158363904 158396672 (3166918548409 / 20000) (15837893034217 / 100000) := by
  exact
    packedTile16384 158363904 158396672 12 1748 12584 27 _ _ (1888039 / 100000) (944021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158396672 :
    ThetaLowerSegment 158396672 158429440 (15837893034217 / 100000) (15841202803397 / 100000) := by
  exact
    packedTile16384 158396672 158429440 12 1753 12585 27 _ _ (94403 / 5000) (1888063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158429440 :
    ThetaLowerSegment 158429440 158462208 (15841202803397 / 100000) (15844421979797 / 100000) := by
  exact
    packedTile16384 158429440 158462208 12 1705 12586 27 _ _ (23601 / 1250) (1888083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158462208 :
    ThetaLowerSegment 158462208 158494976 (15844421979797 / 100000) (792387535093 / 5000) := by
  exact
    packedTile16384 158462208 158494976 12 1763 12588 27 _ _ (1888101 / 100000) (236013 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158494976 :
    ThetaLowerSegment 158494976 158527744 (792387535093 / 5000) (3962757120413 / 25000) := by
  exact
    packedTile16384 158494976 158527744 12 1736 12589 27 _ _ (944061 / 50000) (3021 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158527744 :
    ThetaLowerSegment 158527744 158560512 (3962757120413 / 25000) (15854270423183 / 100000) := by
  exact
    packedTile16384 158527744 158560512 12 1717 12590 27 _ _ (1888143 / 100000) (944073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158560512 :
    ThetaLowerSegment 158560512 158593280 (15854270423183 / 100000) (15857457642327 / 100000) := by
  exact
    packedTile16384 158560512 158593280 12 1688 12592 27 _ _ (1888163 / 100000) (944083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158593280 :
    ThetaLowerSegment 158593280 158626048 (15857457642327 / 100000) (15860701542439 / 100000) := by
  exact
    packedTile16384 158593280 158626048 12 1718 12593 27 _ _ (236023 / 12500) (1888187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158626048 :
    ThetaLowerSegment 158626048 158658816 (15860701542439 / 100000) (15863922820169 / 100000) := by
  exact
    packedTile16384 158626048 158658816 12 1706 12594 27 _ _ (377641 / 20000) (118013 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158658816 :
    ThetaLowerSegment 158658816 158691584 (15863922820169 / 100000) (3966797834411 / 25000) := by
  exact
    packedTile16384 158658816 158691584 12 1731 12595 27 _ _ (75529 / 4000) (472057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158691584 :
    ThetaLowerSegment 158691584 158724352 (3966797834411 / 25000) (99190315314 / 625) := by
  exact
    packedTile16384 158691584 158724352 12 1726 12597 27 _ _ (944123 / 50000) (1888249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158724352 :
    ThetaLowerSegment 158724352 158757120 (99190315314 / 625) (992104253469 / 6250) := by
  exact
    packedTile16384 158724352 158757120 12 1704 12598 27 _ _ (944133 / 50000) (1888269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158757120 :
    ThetaLowerSegment 158757120 158789888 (992104253469 / 6250) (7938478725729 / 50000) := by
  exact
    packedTile16384 158757120 158789888 12 1742 12599 27 _ _ (1888287 / 100000) (188829 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158789888 :
    ThetaLowerSegment 158789888 158822656 (7938478725729 / 50000) (7940086619991 / 50000) := by
  exact
    packedTile16384 158789888 158822656 12 1703 12601 27 _ _ (472077 / 25000) (1888311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158822656 :
    ThetaLowerSegment 158822656 158855424 (7940086619991 / 50000) (1588350802723 / 10000) := by
  exact
    packedTile16384 158822656 158855424 12 1766 12602 27 _ _ (236041 / 12500) (1888331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158855424 :
    ThetaLowerSegment 158855424 158888192 (1588350802723 / 10000) (15886791866141 / 100000) := by
  exact
    packedTile16384 158855424 158888192 12 1739 12603 27 _ _ (1888349 / 100000) (59011 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158888192 :
    ThetaLowerSegment 158888192 158920960 (15886791866141 / 100000) (15890105955491 / 100000) := by
  exact
    packedTile16384 158888192 158920960 12 1755 12605 27 _ _ (188837 / 10000) (1888373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158920960 :
    ThetaLowerSegment 158920960 158953728 (15890105955491 / 100000) (15893399307651 / 100000) := by
  exact
    packedTile16384 158920960 158953728 12 1744 12606 27 _ _ (188839 / 10000) (1888393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158953728 :
    ThetaLowerSegment 158953728 158986496 (15893399307651 / 100000) (794834162719 / 5000) := by
  exact
    packedTile16384 158953728 158986496 12 1739 12607 27 _ _ (1888411 / 100000) (944207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell158986496 :
    ThetaLowerSegment 158986496 159019264 (794834162719 / 5000) (1987498028971 / 12500) := by
  exact
    packedTile16384 158986496 159019264 12 1748 12608 27 _ _ (1888431 / 100000) (944217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159019264 :
    ThetaLowerSegment 159019264 159052032 (1987498028971 / 12500) (397582508837 / 2500) := by
  exact
    packedTile16384 159019264 159052032 12 1756 12610 27 _ _ (472113 / 25000) (377691 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159052032 :
    ThetaLowerSegment 159052032 159084800 (397582508837 / 2500) (15906569300243 / 100000) := by
  exact
    packedTile16384 159052032 159084800 12 1731 12611 27 _ _ (1888473 / 100000) (472119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159084800 :
    ThetaLowerSegment 159084800 159117568 (15906569300243 / 100000) (15909945925727 / 100000) := by
  exact
    packedTile16384 159084800 159117568 12 1788 12612 27 _ _ (1888493 / 100000) (118031 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159117568 :
    ThetaLowerSegment 159117568 159150336 (15909945925727 / 100000) (15913213054947 / 100000) := by
  exact
    packedTile16384 159117568 159150336 12 1730 12614 27 _ _ (944257 / 50000) (1888517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159150336 :
    ThetaLowerSegment 159150336 159183104 (15913213054947 / 100000) (15916425451281 / 100000) := by
  exact
    packedTile16384 159150336 159183104 12 1701 12615 27 _ _ (944267 / 50000) (1888537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159183104 :
    ThetaLowerSegment 159183104 159215872 (15916425451281 / 100000) (1989958512527 / 12500) := by
  exact
    packedTile16384 159183104 159215872 12 1717 12616 27 _ _ (377711 / 20000) (944279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159215872 :
    ThetaLowerSegment 159215872 159248640 (1989958512527 / 12500) (15922942891 / 100) := by
  exact
    packedTile16384 159215872 159248640 12 1734 12618 27 _ _ (59018 / 3125) (1888579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159248640 :
    ThetaLowerSegment 159248640 159281408 (15922942891 / 100) (3981544513987 / 25000) := by
  exact
    packedTile16384 159248640 159281408 12 1713 12619 27 _ _ (472149 / 25000) (1888599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159281408 :
    ThetaLowerSegment 159281408 159314176 (3981544513987 / 25000) (7964749122317 / 50000) := by
  exact
    packedTile16384 159281408 159314176 12 1758 12620 27 _ _ (1888617 / 100000) (94431 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159314176 :
    ThetaLowerSegment 159314176 159346944 (7964749122317 / 50000) (995799265643 / 6250) := by
  exact
    packedTile16384 159314176 159346944 12 1742 12621 27 _ _ (1888637 / 100000) (11804 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159346944 :
    ThetaLowerSegment 159346944 159379712 (995799265643 / 6250) (7968066531803 / 50000) := by
  exact
    packedTile16384 159346944 159379712 12 1771 12623 27 _ _ (944329 / 50000) (1888661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159379712 :
    ThetaLowerSegment 159379712 159412480 (7968066531803 / 50000) (15939334374511 / 100000) := by
  exact
    packedTile16384 159379712 159412480 12 1695 12624 27 _ _ (1888679 / 100000) (944341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159412480 :
    ThetaLowerSegment 159412480 159445248 (15939334374511 / 100000) (1594262259947 / 10000) := by
  exact
    packedTile16384 159412480 159445248 12 1741 12625 27 _ _ (1888699 / 100000) (944351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159445248 :
    ThetaLowerSegment 159445248 159478016 (1594262259947 / 10000) (1594594863539 / 10000) := by
  exact
    packedTile16384 159445248 159478016 12 1761 12627 27 _ _ (23609 / 1250) (1888723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159478016 :
    ThetaLowerSegment 159478016 159510784 (1594594863539 / 10000) (1594913305103 / 10000) := by
  exact
    packedTile16384 159478016 159510784 12 1686 12628 27 _ _ (94437 / 5000) (1888743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159510784 :
    ThetaLowerSegment 159510784 159543552 (1594913305103 / 10000) (15952478046761 / 100000) := by
  exact
    packedTile16384 159510784 159543552 12 1771 12629 27 _ _ (1888761 / 100000) (472191 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159543552 :
    ThetaLowerSegment 159543552 159576320 (15952478046761 / 100000) (15955738082767 / 100000) := by
  exact
    packedTile16384 159543552 159576320 12 1726 12631 27 _ _ (1888781 / 100000) (118049 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159576320 :
    ThetaLowerSegment 159576320 159609088 (15955738082767 / 100000) (15958996266217 / 100000) := by
  exact
    packedTile16384 159576320 159609088 12 1725 12632 27 _ _ (944401 / 50000) (377761 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159609088 :
    ThetaLowerSegment 159609088 159641856 (15958996266217 / 100000) (15962169487177 / 100000) := by
  exact
    packedTile16384 159609088 159641856 12 1680 12633 27 _ _ (944411 / 50000) (75553 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159641856 :
    ThetaLowerSegment 159641856 159674624 (15962169487177 / 100000) (15965406964079 / 100000) := by
  exact
    packedTile16384 159641856 159674624 12 1714 12634 27 _ _ (1888843 / 100000) (944423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159674624 :
    ThetaLowerSegment 159674624 159707392 (15965406964079 / 100000) (15968689807973 / 100000) := by
  exact
    packedTile16384 159674624 159707392 12 1738 12636 27 _ _ (1888863 / 100000) (944433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159707392 :
    ThetaLowerSegment 159707392 159740160 (15968689807973 / 100000) (15972004799393 / 100000) := by
  exact
    packedTile16384 159707392 159740160 12 1755 12637 27 _ _ (472221 / 25000) (1888887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159740160 :
    ThetaLowerSegment 159740160 159772928 (15972004799393 / 100000) (15975317937009 / 100000) := by
  exact
    packedTile16384 159740160 159772928 12 1754 12638 27 _ _ (236113 / 12500) (1888907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159772928 :
    ThetaLowerSegment 159772928 159805696 (15975317937009 / 100000) (15978695334909 / 100000) := by
  exact
    packedTile16384 159772928 159805696 12 1788 12640 27 _ _ (75557 / 4000) (59029 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159805696 :
    ThetaLowerSegment 159805696 159838464 (15978695334909 / 100000) (15982034989669 / 100000) := by
  exact
    packedTile16384 159805696 159838464 12 1768 12641 27 _ _ (377789 / 20000) (472237 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159838464 :
    ThetaLowerSegment 159838464 159871232 (15982034989669 / 100000) (15985344458101 / 100000) := by
  exact
    packedTile16384 159838464 159871232 12 1752 12642 27 _ _ (944483 / 50000) (1888969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159871232 :
    ThetaLowerSegment 159871232 159904000 (15985344458101 / 100000) (15988570846189 / 100000) := by
  exact
    packedTile16384 159871232 159904000 12 1708 12644 27 _ _ (944493 / 50000) (1888989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159904000 :
    ThetaLowerSegment 159904000 159936768 (15988570846189 / 100000) (15991827494257 / 100000) := by
  exact
    packedTile16384 159904000 159936768 12 1724 12645 27 _ _ (1889007 / 100000) (188901 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159936768 :
    ThetaLowerSegment 159936768 159969536 (15991827494257 / 100000) (499846911814 / 3125) := by
  exact
    packedTile16384 159936768 159969536 12 1733 12646 27 _ _ (1889027 / 100000) (188903 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell159969536 :
    ThetaLowerSegment 159969536 160002304 (499846911814 / 3125) (499950337192 / 3125) := by
  exact
    packedTile16384 159969536 160002304 12 1752 12647 27 _ _ (236131 / 12500) (1889051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160002304 :
    ThetaLowerSegment 160002304 160035072 (499950337192 / 3125) (4000420191713 / 25000) := by
  exact
    packedTile16384 160002304 160035072 12 1731 12649 27 _ _ (472267 / 25000) (1889071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160035072 :
    ThetaLowerSegment 160035072 160067840 (4000420191713 / 25000) (8002489558123 / 50000) := by
  exact
    packedTile16384 160035072 160067840 12 1746 12650 27 _ _ (1889089 / 100000) (472273 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160067840 :
    ThetaLowerSegment 160067840 160100608 (8002489558123 / 50000) (16008264276797 / 100000) := by
  exact
    packedTile16384 160067840 160100608 12 1739 12651 27 _ _ (1889109 / 100000) (236139 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160100608 :
    ThetaLowerSegment 160100608 160133376 (16008264276797 / 100000) (16011545695607 / 100000) := by
  exact
    packedTile16384 160100608 160133376 12 1737 12653 27 _ _ (188913 / 10000) (1889133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160133376 :
    ThetaLowerSegment 160133376 160166144 (16011545695607 / 100000) (16014859264707 / 100000) := by
  exact
    packedTile16384 160133376 160166144 12 1754 12654 27 _ _ (37783 / 2000) (1889153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160166144 :
    ThetaLowerSegment 160166144 160198912 (16014859264707 / 100000) (3203624750439 / 20000) := by
  exact
    packedTile16384 160166144 160198912 12 1728 12655 27 _ _ (1889171 / 100000) (944587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160198912 :
    ThetaLowerSegment 160198912 160231680 (3203624750439 / 20000) (16021426058063 / 100000) := by
  exact
    packedTile16384 160198912 160231680 12 1748 12656 27 _ _ (1889191 / 100000) (944597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160231680 :
    ThetaLowerSegment 160231680 160264448 (16021426058063 / 100000) (16024737846699 / 100000) := by
  exact
    packedTile16384 160231680 160264448 12 1753 12658 27 _ _ (472303 / 25000) (377843 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160264448 :
    ThetaLowerSegment 160264448 160297216 (16024737846699 / 100000) (16027923091851 / 100000) := by
  exact
    packedTile16384 160264448 160297216 12 1686 12659 27 _ _ (118077 / 6250) (377847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160297216 :
    ThetaLowerSegment 160297216 160329984 (16027923091851 / 100000) (8015581580373 / 50000) := by
  exact
    packedTile16384 160297216 160329984 12 1715 12660 27 _ _ (1889253 / 100000) (236157 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160329984 :
    ThetaLowerSegment 160329984 160362752 (8015581580373 / 50000) (16034497727591 / 100000) := by
  exact
    packedTile16384 160329984 160362752 12 1765 12662 27 _ _ (1889273 / 100000) (472319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160362752 :
    ThetaLowerSegment 160362752 160395520 (16034497727591 / 100000) (16037735975793 / 100000) := by
  exact
    packedTile16384 160362752 160395520 12 1714 12663 27 _ _ (1889293 / 100000) (118081 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160395520 :
    ThetaLowerSegment 160395520 160428288 (16037735975793 / 100000) (16040995042443 / 100000) := by
  exact
    packedTile16384 160395520 160428288 12 1725 12664 27 _ _ (944657 / 50000) (1889317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160428288 :
    ThetaLowerSegment 160428288 160461056 (16040995042443 / 100000) (16044327827619 / 100000) := by
  exact
    packedTile16384 160428288 160461056 12 1764 12666 27 _ _ (944667 / 50000) (1889337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160461056 :
    ThetaLowerSegment 160461056 160493824 (16044327827619 / 100000) (16047687100809 / 100000) := by
  exact
    packedTile16384 160461056 160493824 12 1778 12667 27 _ _ (377871 / 20000) (944679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160493824 :
    ThetaLowerSegment 160493824 160526592 (16047687100809 / 100000) (4012725231921 / 25000) := by
  exact
    packedTile16384 160493824 160526592 12 1701 12668 27 _ _ (3023 / 160) (944689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160526592 :
    ThetaLowerSegment 160526592 160559360 (4012725231921 / 25000) (4013534838107 / 25000) := by
  exact
    packedTile16384 160526592 160559360 12 1714 12669 27 _ _ (472349 / 25000) (1889399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160559360 :
    ThetaLowerSegment 160559360 160592128 (4013534838107 / 25000) (4014364291731 / 25000) := by
  exact
    packedTile16384 160559360 160592128 12 1756 12671 27 _ _ (236177 / 12500) (1889419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160592128 :
    ThetaLowerSegment 160592128 160624896 (4014364291731 / 25000) (4015206035469 / 25000) := by
  exact
    packedTile16384 160592128 160624896 12 1782 12672 27 _ _ (472359 / 25000) (1889439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160624896 :
    ThetaLowerSegment 160624896 160657664 (4015206035469 / 25000) (3212821225737 / 20000) := by
  exact
    packedTile16384 160624896 160657664 12 1737 12673 27 _ _ (1889457 / 100000) (94473 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160657664 :
    ThetaLowerSegment 160657664 160690432 (3212821225737 / 20000) (502104816864 / 3125) := by
  exact
    packedTile16384 160657664 160690432 12 1719 12675 27 _ _ (1889477 / 100000) (47237 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160690432 :
    ThetaLowerSegment 160690432 160723200 (502104816864 / 3125) (8035306761849 / 50000) := by
  exact
    packedTile16384 160690432 160723200 12 1725 12676 27 _ _ (944749 / 50000) (1889501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160723200 :
    ThetaLowerSegment 160723200 160755968 (8035306761849 / 50000) (321477043151 / 2000) := by
  exact
    packedTile16384 160723200 160755968 12 1714 12677 27 _ _ (944759 / 50000) (1889521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160755968 :
    ThetaLowerSegment 160755968 160788736 (321477043151 / 2000) (8038564308221 / 50000) := by
  exact
    packedTile16384 160755968 160788736 12 1734 12678 27 _ _ (944769 / 50000) (1889541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160788736 :
    ThetaLowerSegment 160788736 160821504 (8038564308221 / 50000) (1608047691499 / 10000) := by
  exact
    packedTile16384 160788736 160821504 12 1772 12680 27 _ _ (1889559 / 100000) (944781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160821504 :
    ThetaLowerSegment 160821504 160854272 (1608047691499 / 10000) (16083842255189 / 100000) := by
  exact
    packedTile16384 160821504 160854272 12 1781 12681 27 _ _ (1889579 / 100000) (944791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160854272 :
    ThetaLowerSegment 160854272 160887040 (16083842255189 / 100000) (8043567913123 / 50000) := by
  exact
    packedTile16384 160854272 160887040 12 1743 12682 27 _ _ (1889599 / 100000) (944801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160887040 :
    ThetaLowerSegment 160887040 160919808 (8043567913123 / 50000) (8045190151893 / 50000) := by
  exact
    packedTile16384 160887040 160919808 12 1717 12684 27 _ _ (94481 / 5000) (1889623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160919808 :
    ThetaLowerSegment 160919808 160952576 (8045190151893 / 50000) (8046859648833 / 50000) := by
  exact
    packedTile16384 160919808 160952576 12 1767 12685 27 _ _ (47241 / 2500) (1889643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160952576 :
    ThetaLowerSegment 160952576 160985344 (8046859648833 / 50000) (4024247102799 / 25000) := by
  exact
    packedTile16384 160952576 160985344 12 1730 12686 27 _ _ (1889661 / 100000) (59052 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell160985344 :
    ThetaLowerSegment 160985344 161018112 (4024247102799 / 25000) (16100214096663 / 100000) := by
  exact
    packedTile16384 160985344 161018112 12 1707 12688 27 _ _ (1889681 / 100000) (472421 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161018112 :
    ThetaLowerSegment 161018112 161050880 (16100214096663 / 100000) (16103513514609 / 100000) := by
  exact
    packedTile16384 161018112 161050880 12 1746 12689 27 _ _ (1889701 / 100000) (236213 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161050880 :
    ThetaLowerSegment 161050880 161083648 (16103513514609 / 100000) (16106820528109 / 100000) := by
  exact
    packedTile16384 161050880 161083648 12 1750 12690 27 _ _ (944861 / 50000) (75589 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161083648 :
    ThetaLowerSegment 161083648 161116416 (16106820528109 / 100000) (16110063325381 / 100000) := by
  exact
    packedTile16384 161083648 161116416 12 1716 12691 27 _ _ (944871 / 50000) (377949 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161116416 :
    ThetaLowerSegment 161116416 161149184 (16110063325381 / 100000) (16113370408881 / 100000) := by
  exact
    packedTile16384 161116416 161149184 12 1750 12693 27 _ _ (944881 / 50000) (377953 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161149184 :
    ThetaLowerSegment 161149184 161181952 (16113370408881 / 100000) (402915190179 / 2500) := by
  exact
    packedTile16384 161149184 161181952 12 1713 12694 27 _ _ (1889783 / 100000) (944893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161181952 :
    ThetaLowerSegment 161181952 161214720 (402915190179 / 2500) (16119901533789 / 100000) := by
  exact
    packedTile16384 161181952 161214720 12 1743 12695 27 _ _ (1889803 / 100000) (944903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161214720 :
    ThetaLowerSegment 161214720 161247488 (16119901533789 / 100000) (503848796202 / 3125) := by
  exact
    packedTile16384 161214720 161247488 12 1725 12697 27 _ _ (1889823 / 100000) (944913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161247488 :
    ThetaLowerSegment 161247488 161280256 (503848796202 / 3125) (806319561093 / 5000) := by
  exact
    packedTile16384 161247488 161280256 12 1709 12698 27 _ _ (472461 / 25000) (1889847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161280256 :
    ThetaLowerSegment 161280256 161313024 (806319561093 / 5000) (4032404777393 / 25000) := by
  exact
    packedTile16384 161280256 161313024 12 1708 12699 27 _ _ (236233 / 12500) (1889867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161313024 :
    ThetaLowerSegment 161313024 161345792 (4032404777393 / 25000) (4033217427513 / 25000) := by
  exact
    packedTile16384 161313024 161345792 12 1720 12700 27 _ _ (472471 / 25000) (1889887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161345792 :
    ThetaLowerSegment 161345792 161378560 (4033217427513 / 25000) (8068062063231 / 50000) := by
  exact
    packedTile16384 161345792 161378560 12 1722 12702 27 _ _ (377981 / 20000) (472477 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161378560 :
    ThetaLowerSegment 161378560 161411328 (8068062063231 / 50000) (8069664719631 / 50000) := by
  exact
    packedTile16384 161378560 161411328 12 1696 12703 27 _ _ (75597 / 4000) (236241 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161411328 :
    ThetaLowerSegment 161411328 161444096 (8069664719631 / 50000) (16142582034607 / 100000) := by
  exact
    packedTile16384 161411328 161444096 12 1721 12704 27 _ _ (377989 / 20000) (472487 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161444096 :
    ThetaLowerSegment 161444096 161476864 (16142582034607 / 100000) (16145806314897 / 100000) := by
  exact
    packedTile16384 161444096 161476864 12 1706 12706 27 _ _ (377993 / 20000) (118123 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161476864 :
    ThetaLowerSegment 161476864 161509632 (16145806314897 / 100000) (16149187499851 / 100000) := by
  exact
    packedTile16384 161476864 161509632 12 1789 12707 27 _ _ (944993 / 50000) (1889989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161509632 :
    ThetaLowerSegment 161509632 161542400 (16149187499851 / 100000) (16152449650207 / 100000) := by
  exact
    packedTile16384 161509632 161542400 12 1726 12708 27 _ _ (945003 / 50000) (1890009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161542400 :
    ThetaLowerSegment 161542400 161575168 (16152449650207 / 100000) (16155692934823 / 100000) := by
  exact
    packedTile16384 161542400 161575168 12 1716 12709 27 _ _ (945013 / 50000) (1890029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161575168 :
    ThetaLowerSegment 161575168 161607936 (16155692934823 / 100000) (4039733591357 / 25000) := by
  exact
    packedTile16384 161575168 161607936 12 1715 12711 27 _ _ (1890047 / 100000) (37801 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161607936 :
    ThetaLowerSegment 161607936 161640704 (4039733591357 / 25000) (3232456334817 / 20000) := by
  exact
    packedTile16384 161607936 161640704 12 1771 12712 27 _ _ (1890067 / 100000) (189007 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161640704 :
    ThetaLowerSegment 161640704 161673472 (3232456334817 / 20000) (16165506162507 / 100000) := by
  exact
    packedTile16384 161640704 161673472 12 1706 12713 27 _ _ (1890087 / 100000) (189009 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161673472 :
    ThetaLowerSegment 161673472 161706240 (16165506162507 / 100000) (16168779827831 / 100000) := by
  exact
    packedTile16384 161673472 161706240 12 1732 12715 27 _ _ (1890107 / 100000) (189011 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161706240 :
    ThetaLowerSegment 161706240 161739008 (16168779827831 / 100000) (646883350863 / 4000) := by
  exact
    packedTile16384 161706240 161739008 12 1748 12716 27 _ _ (118133 / 6250) (1890131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161739008 :
    ThetaLowerSegment 161739008 161771776 (646883350863 / 4000) (16175310254211 / 100000) := by
  exact
    packedTile16384 161739008 161771776 12 1707 12717 27 _ _ (472537 / 25000) (1890151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161771776 :
    ThetaLowerSegment 161771776 161804544 (16175310254211 / 100000) (16178582135019 / 100000) := by
  exact
    packedTile16384 161771776 161804544 12 1731 12718 27 _ _ (236271 / 12500) (1890171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161804544 :
    ThetaLowerSegment 161804544 161837312 (16178582135019 / 100000) (16181840819131 / 100000) := by
  exact
    packedTile16384 161804544 161837312 12 1724 12720 27 _ _ (472547 / 25000) (1890191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161837312 :
    ThetaLowerSegment 161837312 161870080 (16181840819131 / 100000) (505784892229 / 3125) := by
  exact
    packedTile16384 161837312 161870080 12 1733 12721 27 _ _ (1890209 / 100000) (472553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161870080 :
    ThetaLowerSegment 161870080 161902848 (505784892229 / 3125) (16188369635437 / 100000) := by
  exact
    packedTile16384 161870080 161902848 12 1721 12722 27 _ _ (1890229 / 100000) (236279 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161902848 :
    ThetaLowerSegment 161902848 161935616 (16188369635437 / 100000) (16191632205211 / 100000) := by
  exact
    packedTile16384 161902848 161935616 12 1726 12724 27 _ _ (1890249 / 100000) (472563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161935616 :
    ThetaLowerSegment 161935616 161968384 (16191632205211 / 100000) (3238975181363 / 20000) := by
  exact
    packedTile16384 161935616 161968384 12 1716 12725 27 _ _ (1890269 / 100000) (59071 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell161968384 :
    ThetaLowerSegment 161968384 162001152 (3238975181363 / 20000) (647926902903 / 4000) := by
  exact
    packedTile16384 161968384 162001152 12 1744 12726 27 _ _ (189029 / 10000) (1890293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162001152 :
    ThetaLowerSegment 162001152 162033920 (647926902903 / 4000) (3240283646969 / 20000) := by
  exact
    packedTile16384 162001152 162033920 12 1717 12727 27 _ _ (189031 / 10000) (1890313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162033920 :
    ThetaLowerSegment 162033920 162066688 (3240283646969 / 20000) (3240927871433 / 20000) := by
  exact
    packedTile16384 162033920 162066688 12 1704 12729 27 _ _ (189033 / 10000) (1890333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162066688 :
    ThetaLowerSegment 162066688 162099456 (3240927871433 / 20000) (3241591384283 / 20000) := by
  exact
    packedTile16384 162066688 162099456 12 1755 12730 27 _ _ (37807 / 2000) (1890353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162099456 :
    ThetaLowerSegment 162099456 162132224 (3241591384283 / 20000) (1013205602843 / 6250) := by
  exact
    packedTile16384 162099456 162132224 12 1763 12731 27 _ _ (1890371 / 100000) (945187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162132224 :
    ThetaLowerSegment 162132224 162164992 (1013205602843 / 6250) (1621450709097 / 10000) := by
  exact
    packedTile16384 162132224 162164992 12 1702 12733 27 _ _ (1890391 / 100000) (945197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162164992 :
    ThetaLowerSegment 162164992 162197760 (1621450709097 / 10000) (16217813419809 / 100000) := by
  exact
    packedTile16384 162164992 162197760 12 1749 12734 27 _ _ (1890411 / 100000) (945207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162197760 :
    ThetaLowerSegment 162197760 162230528 (16217813419809 / 100000) (8110573124831 / 50000) := by
  exact
    packedTile16384 162197760 162230528 12 1763 12735 27 _ _ (1890431 / 100000) (945217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162230528 :
    ThetaLowerSegment 162230528 162263296 (8110573124831 / 50000) (8112180008181 / 50000) := by
  exact
    packedTile16384 162230528 162263296 12 1700 12736 27 _ _ (1890451 / 100000) (945227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162263296 :
    ThetaLowerSegment 162263296 162296064 (8112180008181 / 50000) (8113782183201 / 50000) := by
  exact
    packedTile16384 162263296 162296064 12 1695 12738 27 _ _ (236309 / 12500) (75619 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162296064 :
    ThetaLowerSegment 162296064 162328832 (8113782183201 / 50000) (1623088028937 / 10000) := by
  exact
    packedTile16384 162296064 162328832 12 1754 12739 27 _ _ (472623 / 25000) (378099 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162328832 :
    ThetaLowerSegment 162328832 162361600 (1623088028937 / 10000) (8117105685757 / 50000) := by
  exact
    packedTile16384 162328832 162361600 12 1762 12740 27 _ _ (118157 / 6250) (378103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162361600 :
    ThetaLowerSegment 162361600 162394368 (8117105685757 / 50000) (8118766518119 / 50000) := by
  exact
    packedTile16384 162361600 162394368 12 1757 12742 27 _ _ (472633 / 25000) (378107 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162394368 :
    ThetaLowerSegment 162394368 162427136 (8118766518119 / 50000) (8120394283391 / 50000) := by
  exact
    packedTile16384 162394368 162427136 12 1722 12743 27 _ _ (236319 / 12500) (378111 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162427136 :
    ThetaLowerSegment 162427136 162459904 (8120394283391 / 50000) (16244106522397 / 100000) := by
  exact
    packedTile16384 162427136 162459904 12 1755 12744 27 _ _ (1890573 / 100000) (118161 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162459904 :
    ThetaLowerSegment 162459904 162492672 (16244106522397 / 100000) (16247396154217 / 100000) := by
  exact
    packedTile16384 162459904 162492672 12 1740 12745 27 _ _ (1890593 / 100000) (472649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162492672 :
    ThetaLowerSegment 162492672 162525440 (16247396154217 / 100000) (16250595071413 / 100000) := by
  exact
    packedTile16384 162492672 162525440 12 1692 12747 27 _ _ (1890613 / 100000) (236327 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162525440 :
    ThetaLowerSegment 162525440 162558208 (16250595071413 / 100000) (16253850741439 / 100000) := by
  exact
    packedTile16384 162525440 162558208 12 1722 12748 27 _ _ (1890633 / 100000) (472659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162558208 :
    ThetaLowerSegment 162558208 162590976 (16253850741439 / 100000) (4064291264037 / 25000) := by
  exact
    packedTile16384 162558208 162590976 12 1753 12749 27 _ _ (1890653 / 100000) (59083 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162590976 :
    ThetaLowerSegment 162590976 162623744 (4064291264037 / 25000) (16260426467073 / 100000) := by
  exact
    packedTile16384 162590976 162623744 12 1725 12751 27 _ _ (1890673 / 100000) (472669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162623744 :
    ThetaLowerSegment 162623744 162656512 (16260426467073 / 100000) (4065915360699 / 25000) := by
  exact
    packedTile16384 162623744 162656512 12 1711 12752 27 _ _ (1890693 / 100000) (236337 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162656512 :
    ThetaLowerSegment 162656512 162689280 (4065915360699 / 25000) (4066747274859 / 25000) := by
  exact
    packedTile16384 162656512 162689280 12 1760 12753 27 _ _ (945357 / 50000) (1890717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162689280 :
    ThetaLowerSegment 162689280 162722048 (4066747274859 / 25000) (813511679949 / 5000) := by
  exact
    packedTile16384 162689280 162722048 12 1716 12754 27 _ _ (945367 / 50000) (1890737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162722048 :
    ThetaLowerSegment 162722048 162754816 (813511679949 / 5000) (8136755137831 / 50000) := by
  exact
    packedTile16384 162722048 162754816 12 1733 12756 27 _ _ (945377 / 50000) (1890757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162754816 :
    ThetaLowerSegment 162754816 162787584 (8136755137831 / 50000) (4069187292881 / 25000) := by
  exact
    packedTile16384 162754816 162787584 12 1713 12757 27 _ _ (945387 / 50000) (1890777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162787584 :
    ThetaLowerSegment 162787584 162820352 (4069187292881 / 25000) (8140024303527 / 50000) := by
  exact
    packedTile16384 162787584 162820352 12 1745 12758 27 _ _ (945397 / 50000) (1890797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162820352 :
    ThetaLowerSegment 162820352 162853120 (8140024303527 / 50000) (2035415200761 / 12500) := by
  exact
    packedTile16384 162820352 162853120 12 1731 12760 27 _ _ (945407 / 50000) (1890817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162853120 :
    ThetaLowerSegment 162853120 162885888 (2035415200761 / 12500) (1017917955663 / 6250) := by
  exact
    packedTile16384 162853120 162885888 12 1780 12761 27 _ _ (945417 / 50000) (1890837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162885888 :
    ThetaLowerSegment 162885888 162918656 (1017917955663 / 6250) (16289971705743 / 100000) := by
  exact
    packedTile16384 162885888 162918656 12 1737 12762 27 _ _ (378171 / 20000) (945429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162918656 :
    ThetaLowerSegment 162918656 162951424 (16289971705743 / 100000) (16293235355993 / 100000) := by
  exact
    packedTile16384 162918656 162951424 12 1726 12763 27 _ _ (15127 / 800) (945439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162951424 :
    ThetaLowerSegment 162951424 162984192 (16293235355993 / 100000) (16296499040763 / 100000) := by
  exact
    packedTile16384 162951424 162984192 12 1726 12765 27 _ _ (378179 / 20000) (945449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell162984192 :
    ThetaLowerSegment 162984192 163016960 (16296499040763 / 100000) (8149884216399 / 50000) := by
  exact
    packedTile16384 162984192 163016960 12 1729 12766 27 _ _ (378183 / 20000) (945459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163016960 :
    ThetaLowerSegment 163016960 163049728 (8149884216399 / 50000) (8151525547979 / 50000) := by
  exact
    packedTile16384 163016960 163049728 12 1736 12767 27 _ _ (378187 / 20000) (945469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163049728 :
    ThetaLowerSegment 163049728 163082496 (8151525547979 / 50000) (16306275174233 / 100000) := by
  exact
    packedTile16384 163049728 163082496 12 1705 12769 27 _ _ (378191 / 20000) (945479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163082496 :
    ThetaLowerSegment 163082496 163115264 (16306275174233 / 100000) (16309588162433 / 100000) := by
  exact
    packedTile16384 163082496 163115264 12 1752 12770 27 _ _ (75639 / 4000) (945489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163115264 :
    ThetaLowerSegment 163115264 163148032 (16309588162433 / 100000) (16312840673833 / 100000) := by
  exact
    packedTile16384 163115264 163148032 12 1720 12771 27 _ _ (378199 / 20000) (945499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163148032 :
    ThetaLowerSegment 163148032 163180800 (16312840673833 / 100000) (16316051617303 / 100000) := by
  exact
    packedTile16384 163148032 163180800 12 1698 12772 27 _ _ (378203 / 20000) (945509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163180800 :
    ThetaLowerSegment 163180800 163213568 (16316051617303 / 100000) (2039923189001 / 12500) := by
  exact
    packedTile16384 163180800 163213568 12 1763 12774 27 _ _ (378207 / 20000) (945519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163213568 :
    ThetaLowerSegment 163213568 163246336 (2039923189001 / 12500) (408067466053 / 2500) := by
  exact
    packedTile16384 163213568 163246336 12 1752 12775 27 _ _ (118191 / 6250) (1891059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163246336 :
    ThetaLowerSegment 163246336 163279104 (408067466053 / 2500) (4081517607657 / 25000) := by
  exact
    packedTile16384 163246336 163279104 12 1783 12776 27 _ _ (472769 / 25000) (1891079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163279104 :
    ThetaLowerSegment 163279104 163311872 (4081517607657 / 25000) (4082333615581 / 25000) := by
  exact
    packedTile16384 163279104 163311872 12 1726 12778 27 _ _ (236387 / 12500) (1891099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163311872 :
    ThetaLowerSegment 163311872 163344640 (4082333615581 / 25000) (4083143013229 / 25000) := by
  exact
    packedTile16384 163311872 163344640 12 1712 12779 27 _ _ (472779 / 25000) (1891119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163344640 :
    ThetaLowerSegment 163344640 163377408 (4083143013229 / 25000) (6534366989 / 40) := by
  exact
    packedTile16384 163344640 163377408 12 1769 12780 27 _ _ (59098 / 3125) (1891139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163377408 :
    ThetaLowerSegment 163377408 163410176 (6534366989 / 40) (4084803912141 / 25000) := by
  exact
    packedTile16384 163377408 163410176 12 1744 12781 27 _ _ (472789 / 25000) (1891159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163410176 :
    ThetaLowerSegment 163410176 163442944 (4084803912141 / 25000) (32685092019 / 200) := by
  exact
    packedTile16384 163410176 163442944 12 1761 12783 27 _ _ (236397 / 12500) (1891179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163442944 :
    ThetaLowerSegment 163442944 163475712 (32685092019 / 200) (817288997733 / 5000) := by
  exact
    packedTile16384 163442944 163475712 12 1710 12784 27 _ _ (472799 / 25000) (1891199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163475712 :
    ThetaLowerSegment 163475712 163508480 (817288997733 / 5000) (817454006329 / 5000) := by
  exact
    packedTile16384 163475712 163508480 12 1745 12785 27 _ _ (118201 / 6250) (1891219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163508480 :
    ThetaLowerSegment 163508480 163541248 (817454006329 / 5000) (817619489479 / 5000) := by
  exact
    packedTile16384 163508480 163541248 12 1750 12787 27 _ _ (472809 / 25000) (1891239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163541248 :
    ThetaLowerSegment 163541248 163574016 (817619489479 / 5000) (817784974379 / 5000) := by
  exact
    packedTile16384 163541248 163574016 12 1750 12788 27 _ _ (236407 / 12500) (1891259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163574016 :
    ThetaLowerSegment 163574016 163606784 (817784974379 / 5000) (511217442379 / 3125) := by
  exact
    packedTile16384 163574016 163606784 12 1723 12789 27 _ _ (472819 / 25000) (1891279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163606784 :
    ThetaLowerSegment 163606784 163639552 (511217442379 / 3125) (511322704822 / 3125) := by
  exact
    packedTile16384 163606784 163639552 12 1781 12790 27 _ _ (59103 / 3125) (1891299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163639552 :
    ThetaLowerSegment 163639552 163672320 (511322704822 / 3125) (2045691305451 / 12500) := by
  exact
    packedTile16384 163639552 163672320 12 1694 12792 27 _ _ (472829 / 25000) (1891319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163672320 :
    ThetaLowerSegment 163672320 163705088 (2045691305451 / 12500) (102305334506 / 625) := by
  exact
    packedTile16384 163672320 163705088 12 1757 12793 27 _ _ (236417 / 12500) (1891339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163705088 :
    ThetaLowerSegment 163705088 163737856 (102305334506 / 625) (2046512858821 / 12500) := by
  exact
    packedTile16384 163705088 163737856 12 1718 12794 27 _ _ (472839 / 25000) (1891359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163737856 :
    ThetaLowerSegment 163737856 163770624 (2046512858821 / 12500) (2046919031817 / 12500) := by
  exact
    packedTile16384 163737856 163770624 12 1718 12796 27 _ _ (118211 / 6250) (1891379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163770624 :
    ThetaLowerSegment 163770624 163803392 (2046919031817 / 12500) (2047332301843 / 12500) := by
  exact
    packedTile16384 163770624 163803392 12 1748 12797 27 _ _ (472849 / 25000) (1891399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163803392 :
    ThetaLowerSegment 163803392 163836160 (2047332301843 / 12500) (2047745576239 / 12500) := by
  exact
    packedTile16384 163803392 163836160 12 1748 12798 27 _ _ (236427 / 12500) (1891419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163836160 :
    ThetaLowerSegment 163836160 163868928 (2047745576239 / 12500) (409632716719 / 2500) := by
  exact
    packedTile16384 163836160 163868928 12 1768 12799 27 _ _ (472859 / 25000) (1891439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163868928 :
    ThetaLowerSegment 163868928 163901696 (409632716719 / 2500) (2048570483067 / 12500) := by
  exact
    packedTile16384 163868928 163901696 12 1721 12801 27 _ _ (59108 / 3125) (1891459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163901696 :
    ThetaLowerSegment 163901696 163934464 (2048570483067 / 12500) (2048984716311 / 12500) := by
  exact
    packedTile16384 163901696 163934464 12 1752 12802 27 _ _ (472869 / 25000) (1891479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163934464 :
    ThetaLowerSegment 163934464 163967232 (2048984716311 / 12500) (512350506904 / 3125) := by
  exact
    packedTile16384 163934464 163967232 12 1765 12803 27 _ _ (236437 / 12500) (1891499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell163967232 :
    ThetaLowerSegment 163967232 164000000 (512350506904 / 3125) (102490813481 / 625) := by
  exact
    packedTile16384 163967232 164000000 12 1752 12804 27 _ _ (472879 / 25000) (1891519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164000000 :
    ThetaLowerSegment 164000000 164032768 (102490813481 / 625) (512553491266 / 3125) := by
  exact
    packedTile16384 164000000 164032768 12 1682 12806 27 _ _ (118221 / 6250) (1891539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164032768 :
    ThetaLowerSegment 164032768 164065536 (512553491266 / 3125) (2050617339381 / 12500) := by
  exact
    packedTile16384 164032768 164065536 12 1706 12807 27 _ _ (472889 / 25000) (1891559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164065536 :
    ThetaLowerSegment 164065536 164098304 (2050617339381 / 12500) (512754174591 / 3125) := by
  exact
    packedTile16384 164065536 164098304 12 1689 12808 27 _ _ (236447 / 12500) (1891579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164098304 :
    ThetaLowerSegment 164098304 164131072 (512754174591 / 3125) (1025712168651 / 6250) := by
  exact
    packedTile16384 164098304 164131072 12 1724 12810 27 _ _ (472899 / 25000) (1891599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164131072 :
    ThetaLowerSegment 164131072 164163840 (1025712168651 / 6250) (1025919773507 / 6250) := by
  exact
    packedTile16384 164131072 164163840 12 1756 12811 27 _ _ (59113 / 3125) (1891619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164163840 :
    ThetaLowerSegment 164163840 164196608 (1025919773507 / 6250) (820897837429 / 5000) := by
  exact
    packedTile16384 164163840 164196608 12 1713 12812 27 _ _ (472909 / 25000) (1891639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164196608 :
    ThetaLowerSegment 164196608 164229376 (820897837429 / 5000) (164212103969 / 1000) := by
  exact
    packedTile16384 164196608 164229376 12 1720 12813 27 _ _ (236457 / 12500) (1891659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164229376 :
    ThetaLowerSegment 164229376 164262144 (164212103969 / 1000) (4106112236553 / 25000) := by
  exact
    packedTile16384 164229376 164262144 12 1712 12815 27 _ _ (472919 / 25000) (1891679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164262144 :
    ThetaLowerSegment 164262144 164294912 (4106112236553 / 25000) (4106937016009 / 25000) := by
  exact
    packedTile16384 164262144 164294912 12 1744 12816 27 _ _ (118231 / 6250) (1891699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164294912 :
    ThetaLowerSegment 164294912 164327680 (4106937016009 / 25000) (1026938914027 / 6250) := by
  exact
    packedTile16384 164294912 164327680 12 1731 12817 27 _ _ (472929 / 25000) (1891719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164327680 :
    ThetaLowerSegment 164327680 164360448 (1026938914027 / 6250) (513572438392 / 3125) := by
  exact
    packedTile16384 164327680 164360448 12 1742 12819 27 _ _ (236467 / 12500) (1891739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164360448 :
    ThetaLowerSegment 164360448 164393216 (513572438392 / 3125) (4109394381033 / 25000) := by
  exact
    packedTile16384 164360448 164393216 12 1723 12820 27 _ _ (472939 / 25000) (1891759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164393216 :
    ThetaLowerSegment 164393216 164425984 (4109394381033 / 25000) (4110217303593 / 25000) := by
  exact
    packedTile16384 164393216 164425984 12 1740 12821 27 _ _ (59118 / 3125) (1891779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164425984 :
    ThetaLowerSegment 164425984 164458752 (4110217303593 / 25000) (164441193199 / 1000) := by
  exact
    packedTile16384 164425984 164458752 12 1718 12822 27 _ _ (472949 / 25000) (1891799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164458752 :
    ThetaLowerSegment 164458752 164491520 (164441193199 / 1000) (4111844256763 / 25000) := by
  exact
    packedTile16384 164458752 164491520 12 1722 12824 27 _ _ (236477 / 12500) (1891819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164491520 :
    ThetaLowerSegment 164491520 164524288 (4111844256763 / 25000) (2056335494329 / 12500) := by
  exact
    packedTile16384 164491520 164524288 12 1748 12825 27 _ _ (378367 / 20000) (945919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164524288 :
    ThetaLowerSegment 164524288 164557056 (2056335494329 / 12500) (4113497729293 / 25000) := by
  exact
    packedTile16384 164524288 164557056 12 1748 12826 27 _ _ (378371 / 20000) (945929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164557056 :
    ThetaLowerSegment 164557056 164589824 (4113497729293 / 25000) (16457299806547 / 100000) := by
  exact
    packedTile16384 164557056 164589824 12 1749 12827 27 _ _ (3027 / 160) (945939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164589824 :
    ThetaLowerSegment 164589824 164622592 (16457299806547 / 100000) (16460603055217 / 100000) := by
  exact
    packedTile16384 164589824 164622592 12 1746 12829 27 _ _ (378379 / 20000) (945949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164622592 :
    ThetaLowerSegment 164622592 164655360 (16460603055217 / 100000) (8231935196211 / 50000) := by
  exact
    packedTile16384 164622592 164655360 12 1727 12830 27 _ _ (378383 / 20000) (945959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164655360 :
    ThetaLowerSegment 164655360 164688128 (8231935196211 / 50000) (16467164251257 / 100000) := by
  exact
    packedTile16384 164655360 164688128 12 1741 12831 27 _ _ (378387 / 20000) (945969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164688128 :
    ThetaLowerSegment 164688128 164720896 (16467164251257 / 100000) (16470441117317 / 100000) := by
  exact
    packedTile16384 164688128 164720896 12 1732 12833 27 _ _ (378391 / 20000) (945979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164720896 :
    ThetaLowerSegment 164720896 164753664 (16470441117317 / 100000) (8236805087721 / 50000) := by
  exact
    packedTile16384 164720896 164753664 12 1675 12834 27 _ _ (75679 / 4000) (945989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164753664 :
    ThetaLowerSegment 164753664 164786432 (8236805087721 / 50000) (16476915490707 / 100000) := by
  exact
    packedTile16384 164753664 164786432 12 1747 12835 27 _ _ (378399 / 20000) (945999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164786432 :
    ThetaLowerSegment 164786432 164819200 (16476915490707 / 100000) (16480215164867 / 100000) := by
  exact
    packedTile16384 164786432 164819200 12 1744 12836 27 _ _ (378403 / 20000) (946009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164819200 :
    ThetaLowerSegment 164819200 164851968 (16480215164867 / 100000) (16483450543007 / 100000) := by
  exact
    packedTile16384 164819200 164851968 12 1710 12838 27 _ _ (946017 / 50000) (1892037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164851968 :
    ThetaLowerSegment 164851968 164884736 (16483450543007 / 100000) (3297343624053 / 20000) := by
  exact
    packedTile16384 164851968 164884736 12 1727 12839 27 _ _ (946027 / 50000) (1892057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164884736 :
    ThetaLowerSegment 164884736 164917504 (3297343624053 / 20000) (16489978163767 / 100000) := by
  exact
    packedTile16384 164884736 164917504 12 1723 12840 27 _ _ (946037 / 50000) (1892077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164917504 :
    ThetaLowerSegment 164917504 164950272 (16489978163767 / 100000) (16493230673353 / 100000) := by
  exact
    packedTile16384 164917504 164950272 12 1719 12842 27 _ _ (946047 / 50000) (1892097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164950272 :
    ThetaLowerSegment 164950272 164983040 (16493230673353 / 100000) (16496572146677 / 100000) := by
  exact
    packedTile16384 164950272 164983040 12 1766 12843 27 _ _ (946057 / 50000) (1892117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell164983040 :
    ThetaLowerSegment 164983040 165015808 (16496572146677 / 100000) (16499843646363 / 100000) := by
  exact
    packedTile16384 164983040 165015808 12 1729 12844 27 _ _ (946067 / 50000) (1892137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165015808 :
    ThetaLowerSegment 165015808 165048576 (16499843646363 / 100000) (16503022465083 / 100000) := by
  exact
    packedTile16384 165015808 165048576 12 1680 12845 27 _ _ (946077 / 50000) (1892157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165048576 :
    ThetaLowerSegment 165048576 165081344 (16503022465083 / 100000) (16506312955669 / 100000) := by
  exact
    packedTile16384 165048576 165081344 12 1739 12847 27 _ _ (946087 / 50000) (1892177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165081344 :
    ThetaLowerSegment 165081344 165114112 (16506312955669 / 100000) (16509567527629 / 100000) := by
  exact
    packedTile16384 165081344 165114112 12 1720 12848 27 _ _ (1892193 / 100000) (473049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165114112 :
    ThetaLowerSegment 165114112 165146880 (16509567527629 / 100000) (16512878900379 / 100000) := by
  exact
    packedTile16384 165114112 165146880 12 1750 12849 27 _ _ (1892213 / 100000) (236527 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165146880 :
    ThetaLowerSegment 165146880 165179648 (16512878900379 / 100000) (16516148679003 / 100000) := by
  exact
    packedTile16384 165146880 165179648 12 1728 12850 27 _ _ (1892233 / 100000) (473059 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165179648 :
    ThetaLowerSegment 165179648 165212416 (16516148679003 / 100000) (4129849419351 / 25000) := by
  exact
    packedTile16384 165179648 165212416 12 1717 12852 27 _ _ (1892253 / 100000) (59133 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165212416 :
    ThetaLowerSegment 165212416 165245184 (4129849419351 / 25000) (16522692124697 / 100000) := by
  exact
    packedTile16384 165212416 165245184 12 1741 12853 27 _ _ (1892273 / 100000) (473069 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165245184 :
    ThetaLowerSegment 165245184 165277952 (16522692124697 / 100000) (8262970595889 / 50000) := by
  exact
    packedTile16384 165245184 165277952 12 1717 12854 27 _ _ (1892293 / 100000) (236537 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165277952 :
    ThetaLowerSegment 165277952 165310720 (8262970595889 / 50000) (8264592307273 / 50000) := by
  exact
    packedTile16384 165277952 165310720 12 1714 12856 27 _ _ (236539 / 12500) (378463 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165310720 :
    ThetaLowerSegment 165310720 165343488 (8264592307273 / 50000) (1653246213357 / 10000) := by
  exact
    packedTile16384 165310720 165343488 12 1732 12857 27 _ _ (473083 / 25000) (378467 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165343488 :
    ThetaLowerSegment 165343488 165376256 (1653246213357 / 10000) (8267885928609 / 50000) := by
  exact
    packedTile16384 165343488 165376256 12 1749 12858 27 _ _ (59136 / 3125) (378471 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165376256 :
    ThetaLowerSegment 165376256 165409024 (8267885928609 / 50000) (1653894347269 / 10000) := by
  exact
    packedTile16384 165376256 165409024 12 1676 12859 27 _ _ (473093 / 25000) (15139 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165409024 :
    ThetaLowerSegment 165409024 165441792 (1653894347269 / 10000) (8271117171189 / 50000) := by
  exact
    packedTile16384 165409024 165441792 12 1739 12861 27 _ _ (236549 / 12500) (378479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165441792 :
    ThetaLowerSegment 165441792 165474560 (8271117171189 / 50000) (16545513890641 / 100000) := by
  exact
    packedTile16384 165441792 165474560 12 1733 12862 27 _ _ (1892411 / 100000) (946207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165474560 :
    ThetaLowerSegment 165474560 165507328 (16545513890641 / 100000) (3309777997509 / 20000) := by
  exact
    packedTile16384 165474560 165507328 12 1784 12863 27 _ _ (1892431 / 100000) (946217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165507328 :
    ThetaLowerSegment 165507328 165540096 (3309777997509 / 20000) (1655209769199 / 10000) := by
  exact
    packedTile16384 165507328 165540096 12 1695 12864 27 _ _ (1892451 / 100000) (946227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165540096 :
    ThetaLowerSegment 165540096 165572864 (1655209769199 / 10000) (8277668801171 / 50000) := by
  exact
    packedTile16384 165540096 165572864 12 1712 12866 27 _ _ (1892471 / 100000) (946237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165572864 :
    ThetaLowerSegment 165572864 165605632 (8277668801171 / 50000) (8279300128413 / 50000) := by
  exact
    packedTile16384 165572864 165605632 12 1724 12867 27 _ _ (1892491 / 100000) (946247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165605632 :
    ThetaLowerSegment 165605632 165638400 (8279300128413 / 50000) (517558276143 / 3125) := by
  exact
    packedTile16384 165605632 165638400 12 1725 12868 27 _ _ (189251 / 10000) (1892513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165638400 :
    ThetaLowerSegment 165638400 165671168 (517558276143 / 3125) (1035314321671 / 6250) := by
  exact
    packedTile16384 165638400 165671168 12 1672 12870 27 _ _ (189253 / 10000) (1892533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165671168 :
    ThetaLowerSegment 165671168 165703936 (1035314321671 / 6250) (8284141220093 / 50000) := by
  exact
    packedTile16384 165671168 165703936 12 1719 12871 27 _ _ (37851 / 2000) (1892553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165703936 :
    ThetaLowerSegment 165703936 165736704 (8284141220093 / 50000) (4142890565999 / 25000) := by
  exact
    packedTile16384 165703936 165736704 12 1733 12872 27 _ _ (189257 / 10000) (1892573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165736704 :
    ThetaLowerSegment 165736704 165769472 (4142890565999 / 25000) (4143728983369 / 25000) := by
  exact
    packedTile16384 165736704 165769472 12 1772 12873 27 _ _ (189259 / 10000) (1892593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165769472 :
    ThetaLowerSegment 165769472 165802240 (4143728983369 / 25000) (8289095073523 / 50000) := by
  exact
    packedTile16384 165769472 165802240 12 1730 12875 27 _ _ (1892609 / 100000) (473153 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165802240 :
    ThetaLowerSegment 165802240 165835008 (8289095073523 / 50000) (16581379226911 / 100000) := by
  exact
    packedTile16384 165802240 165835008 12 1685 12876 27 _ _ (1892629 / 100000) (236579 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165835008 :
    ThetaLowerSegment 165835008 165867776 (16581379226911 / 100000) (829237501739 / 5000) := by
  exact
    packedTile16384 165835008 165867776 12 1781 12877 27 _ _ (1892649 / 100000) (473163 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165867776 :
    ThetaLowerSegment 165867776 165900544 (829237501739 / 5000) (8293989464047 / 50000) := by
  exact
    packedTile16384 165867776 165900544 12 1706 12878 27 _ _ (1892669 / 100000) (59146 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165900544 :
    ThetaLowerSegment 165900544 165933312 (8293989464047 / 50000) (8295624746479 / 50000) := by
  exact
    packedTile16384 165900544 165933312 12 1728 12880 27 _ _ (118293 / 6250) (1892691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165933312 :
    ThetaLowerSegment 165933312 165966080 (8295624746479 / 50000) (8297266670669 / 50000) := by
  exact
    packedTile16384 165933312 165966080 12 1735 12881 27 _ _ (473177 / 25000) (1892711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165966080 :
    ThetaLowerSegment 165966080 165998848 (8297266670669 / 50000) (8298919968577 / 50000) := by
  exact
    packedTile16384 165966080 165998848 12 1747 12882 27 _ _ (236591 / 12500) (1892731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell165998848 :
    ThetaLowerSegment 165998848 166031616 (8298919968577 / 50000) (8300577069451 / 50000) := by
  exact
    packedTile16384 165998848 166031616 12 1751 12884 27 _ _ (473187 / 25000) (1892751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166031616 :
    ThetaLowerSegment 166031616 166064384 (8300577069451 / 50000) (8302178350333 / 50000) := by
  exact
    packedTile16384 166031616 166064384 12 1692 12885 27 _ _ (1892767 / 100000) (189277 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166064384 :
    ThetaLowerSegment 166064384 166097152 (8302178350333 / 50000) (3321521323189 / 20000) := by
  exact
    packedTile16384 166064384 166097152 12 1717 12886 27 _ _ (1892787 / 100000) (189279 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166097152 :
    ThetaLowerSegment 166097152 166129920 (3321521323189 / 20000) (16610866029599 / 100000) := by
  exact
    packedTile16384 166097152 166129920 12 1722 12887 27 _ _ (1892807 / 100000) (189281 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166129920 :
    ThetaLowerSegment 166129920 166162688 (16610866029599 / 100000) (16614163334233 / 100000) := by
  exact
    packedTile16384 166129920 166162688 12 1742 12889 27 _ _ (1892827 / 100000) (189283 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166162688 :
    ThetaLowerSegment 166162688 166195456 (16614163334233 / 100000) (16617409565123 / 100000) := by
  exact
    packedTile16384 166162688 166195456 12 1715 12890 27 _ _ (946423 / 50000) (1892849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166195456 :
    ThetaLowerSegment 166195456 166228224 (16617409565123 / 100000) (16620759937943 / 100000) := by
  exact
    packedTile16384 166195456 166228224 12 1770 12891 27 _ _ (946433 / 50000) (1892869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166228224 :
    ThetaLowerSegment 166228224 166260992 (16620759937943 / 100000) (16624134953681 / 100000) := by
  exact
    packedTile16384 166228224 166260992 12 1783 12892 27 _ _ (946443 / 50000) (1892889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166260992 :
    ThetaLowerSegment 166260992 166293760 (16624134953681 / 100000) (16627432394191 / 100000) := by
  exact
    packedTile16384 166260992 166293760 12 1742 12894 27 _ _ (378581 / 20000) (473227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166293760 :
    ThetaLowerSegment 166293760 166326528 (16627432394191 / 100000) (16630665510091 / 100000) := by
  exact
    packedTile16384 166293760 166326528 12 1708 12895 27 _ _ (75717 / 4000) (59154 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166326528 :
    ThetaLowerSegment 166326528 166359296 (16630665510091 / 100000) (8316971098943 / 50000) := by
  exact
    packedTile16384 166326528 166359296 12 1731 12896 27 _ _ (378589 / 20000) (473237 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166359296 :
    ThetaLowerSegment 166359296 166392064 (8316971098943 / 50000) (16637222706231 / 100000) := by
  exact
    packedTile16384 166359296 166392064 12 1733 12898 27 _ _ (378593 / 20000) (236621 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166392064 :
    ThetaLowerSegment 166392064 166424832 (16637222706231 / 100000) (16640505140487 / 100000) := by
  exact
    packedTile16384 166392064 166424832 12 1734 12899 27 _ _ (236623 / 12500) (1892987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166424832 :
    ThetaLowerSegment 166424832 166457600 (16640505140487 / 100000) (3328758657687 / 20000) := by
  exact
    packedTile16384 166424832 166457600 12 1737 12900 27 _ _ (473251 / 25000) (1893007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166457600 :
    ThetaLowerSegment 166457600 166490368 (3328758657687 / 20000) (16647121224627 / 100000) := by
  exact
    packedTile16384 166457600 166490368 12 1758 12901 27 _ _ (59157 / 3125) (1893027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166490368 :
    ThetaLowerSegment 166490368 166523136 (16647121224627 / 100000) (2081315851123 / 12500) := by
  exact
    packedTile16384 166490368 166523136 12 1799 12903 27 _ _ (1893043 / 100000) (946523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166523136 :
    ThetaLowerSegment 166523136 166555904 (2081315851123 / 12500) (16653727978517 / 100000) := by
  exact
    packedTile16384 166523136 166555904 12 1691 12904 27 _ _ (1893063 / 100000) (946533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166555904 :
    ThetaLowerSegment 166555904 166588672 (16653727978517 / 100000) (4164240814341 / 25000) := by
  exact
    packedTile16384 166555904 166588672 12 1709 12905 27 _ _ (1893083 / 100000) (946543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166588672 :
    ThetaLowerSegment 166588672 166621440 (4164240814341 / 25000) (8330120108463 / 50000) := by
  exact
    packedTile16384 166588672 166621440 12 1731 12906 27 _ _ (946551 / 50000) (378621 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166621440 :
    ThetaLowerSegment 166621440 166654208 (8330120108463 / 50000) (8331808773287 / 50000) := by
  exact
    packedTile16384 166621440 166654208 12 1784 12908 27 _ _ (946561 / 50000) (3029 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166654208 :
    ThetaLowerSegment 166654208 166686976 (8331808773287 / 50000) (1041679017819 / 6250) := by
  exact
    packedTile16384 166654208 166686976 12 1715 12909 27 _ _ (946571 / 50000) (378629 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166686976 :
    ThetaLowerSegment 166686976 166719744 (1041679017819 / 6250) (3334016910393 / 20000) := by
  exact
    packedTile16384 166686976 166719744 12 1701 12910 27 _ _ (1893161 / 100000) (473291 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166719744 :
    ThetaLowerSegment 166719744 166752512 (3334016910393 / 20000) (2084167366263 / 12500) := by
  exact
    packedTile16384 166719744 166752512 12 1719 12912 27 _ _ (1893181 / 100000) (59162 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166752512 :
    ThetaLowerSegment 166752512 166785280 (2084167366263 / 12500) (8338318443123 / 50000) := by
  exact
    packedTile16384 166752512 166785280 12 1742 12913 27 _ _ (1893201 / 100000) (473301 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166785280 :
    ThetaLowerSegment 166785280 166818048 (8338318443123 / 50000) (8339978797063 / 50000) := by
  exact
    packedTile16384 166785280 166818048 12 1754 12914 27 _ _ (94661 / 5000) (1893223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166818048 :
    ThetaLowerSegment 166818048 166850816 (8339978797063 / 50000) (8341590890923 / 50000) := by
  exact
    packedTile16384 166818048 166850816 12 1703 12915 27 _ _ (47331 / 2500) (1893243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166850816 :
    ThetaLowerSegment 166850816 166883584 (8341590890923 / 50000) (8343199215293 / 50000) := by
  exact
    packedTile16384 166850816 166883584 12 1699 12917 27 _ _ (94663 / 5000) (1893263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166883584 :
    ThetaLowerSegment 166883584 166916352 (8343199215293 / 50000) (3337931352749 / 20000) := by
  exact
    packedTile16384 166883584 166916352 12 1721 12918 27 _ _ (1893279 / 100000) (946641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166916352 :
    ThetaLowerSegment 166916352 166949120 (3337931352749 / 20000) (16692996543181 / 100000) := by
  exact
    packedTile16384 166916352 166949120 12 1764 12919 27 _ _ (1893299 / 100000) (946651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166949120 :
    ThetaLowerSegment 166949120 166981888 (16692996543181 / 100000) (16696213290463 / 100000) := by
  exact
    packedTile16384 166949120 166981888 12 1699 12920 27 _ _ (946659 / 50000) (1893321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell166981888 :
    ThetaLowerSegment 166981888 167014656 (16696213290463 / 100000) (16699555032033 / 100000) := by
  exact
    packedTile16384 166981888 167014656 12 1765 12922 27 _ _ (946669 / 50000) (1893341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167014656 :
    ThetaLowerSegment 167014656 167047424 (16699555032033 / 100000) (3340575196393 / 20000) := by
  exact
    packedTile16384 167014656 167047424 12 1754 12923 27 _ _ (946679 / 50000) (1893361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167047424 :
    ThetaLowerSegment 167047424 167080192 (3340575196393 / 20000) (3341226518081 / 20000) := by
  exact
    packedTile16384 167047424 167080192 12 1720 12924 27 _ _ (1893377 / 100000) (94669 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167080192 :
    ThetaLowerSegment 167080192 167112960 (3341226518081 / 20000) (8354710710497 / 50000) := by
  exact
    packedTile16384 167080192 167112960 12 1737 12925 27 _ _ (1893397 / 100000) (9467 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167112960 :
    ThetaLowerSegment 167112960 167145728 (8354710710497 / 50000) (835635608987 / 5000) := by
  exact
    packedTile16384 167112960 167145728 12 1738 12927 27 _ _ (1893417 / 100000) (94671 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167145728 :
    ThetaLowerSegment 167145728 167178496 (835635608987 / 5000) (522374441991 / 3125) := by
  exact
    packedTile16384 167145728 167178496 12 1727 12928 27 _ _ (473359 / 25000) (1893439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167178496 :
    ThetaLowerSegment 167178496 167211264 (522374441991 / 3125) (522478937094 / 3125) := by
  exact
    packedTile16384 167178496 167211264 12 1766 12929 27 _ _ (118341 / 6250) (1893459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167211264 :
    ThetaLowerSegment 167211264 167244032 (522478937094 / 3125) (2090322845501 / 12500) := by
  exact
    packedTile16384 167211264 167244032 12 1720 12931 27 _ _ (75739 / 4000) (946739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167244032 :
    ThetaLowerSegment 167244032 167276800 (2090322845501 / 12500) (8362936829159 / 50000) := by
  exact
    packedTile16384 167244032 167276800 12 1738 12932 27 _ _ (378699 / 20000) (946749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167276800 :
    ThetaLowerSegment 167276800 167309568 (8362936829159 / 50000) (16729143758723 / 100000) := by
  exact
    packedTile16384 167276800 167309568 12 1727 12933 27 _ _ (378703 / 20000) (946759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167309568 :
    ThetaLowerSegment 167309568 167342336 (16729143758723 / 100000) (16732411998407 / 100000) := by
  exact
    packedTile16384 167309568 167342336 12 1726 12934 27 _ _ (946767 / 50000) (1893537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167342336 :
    ThetaLowerSegment 167342336 167375104 (16732411998407 / 100000) (669424635671 / 4000) := by
  exact
    packedTile16384 167342336 167375104 12 1692 12936 27 _ _ (946777 / 50000) (1893557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167375104 :
    ThetaLowerSegment 167375104 167407872 (669424635671 / 4000) (4184741405603 / 25000) := by
  exact
    packedTile16384 167375104 167407872 12 1769 12937 27 _ _ (1893573 / 100000) (236697 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167407872 :
    ThetaLowerSegment 167407872 167440640 (4184741405603 / 25000) (2092778772093 / 12500) := by
  exact
    packedTile16384 167407872 167440640 12 1724 12938 27 _ _ (1893593 / 100000) (473399 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167440640 :
    ThetaLowerSegment 167440640 167473408 (2092778772093 / 12500) (4186374164361 / 25000) := by
  exact
    packedTile16384 167440640 167473408 12 1725 12939 27 _ _ (473403 / 25000) (378723 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167473408 :
    ThetaLowerSegment 167473408 167506176 (4186374164361 / 25000) (4187205468809 / 25000) := by
  exact
    packedTile16384 167473408 167506176 12 1756 12941 27 _ _ (59176 / 3125) (378727 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167506176 :
    ThetaLowerSegment 167506176 167538944 (4187205468809 / 25000) (4188023526473 / 25000) := by
  exact
    packedTile16384 167506176 167538944 12 1728 12942 27 _ _ (473413 / 25000) (378731 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167538944 :
    ThetaLowerSegment 167538944 167571712 (4188023526473 / 25000) (16755364475709 / 100000) := by
  exact
    packedTile16384 167538944 167571712 12 1727 12943 27 _ _ (1893671 / 100000) (946837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167571712 :
    ThetaLowerSegment 167571712 167604480 (16755364475709 / 100000) (8379313652651 / 50000) := by
  exact
    packedTile16384 167571712 167604480 12 1723 12944 27 _ _ (1893691 / 100000) (946847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167604480 :
    ThetaLowerSegment 167604480 167637248 (8379313652651 / 50000) (2095242898939 / 12500) := by
  exact
    packedTile16384 167604480 167637248 12 1751 12946 27 _ _ (189371 / 10000) (1893713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167637248 :
    ThetaLowerSegment 167637248 167670016 (2095242898939 / 12500) (2095650050889 / 12500) := by
  exact
    packedTile16384 167637248 167670016 12 1720 12947 27 _ _ (189373 / 10000) (1893733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167670016 :
    ThetaLowerSegment 167670016 167702784 (2095650050889 / 12500) (16768429249157 / 100000) := by
  exact
    packedTile16384 167670016 167702784 12 1705 12948 27 _ _ (1893749 / 100000) (236719 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167702784 :
    ThetaLowerSegment 167702784 167735552 (16768429249157 / 100000) (838584989411 / 5000) := by
  exact
    packedTile16384 167702784 167735552 12 1727 12950 27 _ _ (1893769 / 100000) (473443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167735552 :
    ThetaLowerSegment 167735552 167768320 (838584989411 / 5000) (524219717541 / 3125) := by
  exact
    packedTile16384 167735552 167768320 12 1759 12951 27 _ _ (473447 / 25000) (1893791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167768320 :
    ThetaLowerSegment 167768320 167801088 (524219717541 / 3125) (1048644084709 / 6250) := by
  exact
    packedTile16384 167768320 167801088 12 1729 12952 27 _ _ (118363 / 6250) (1893811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167801088 :
    ThetaLowerSegment 167801088 167833856 (1048644084709 / 6250) (16781583569881 / 100000) := by
  exact
    packedTile16384 167801088 167833856 12 1731 12953 27 _ _ (1893827 / 100000) (189383 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167833856 :
    ThetaLowerSegment 167833856 167866624 (16781583569881 / 100000) (1049053626959 / 6250) := by
  exact
    packedTile16384 167833856 167866624 12 1729 12955 27 _ _ (1893847 / 100000) (37877 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167866624 :
    ThetaLowerSegment 167866624 167899392 (1049053626959 / 6250) (4197049703183 / 25000) := by
  exact
    packedTile16384 167866624 167899392 12 1764 12956 27 _ _ (1893867 / 100000) (189387 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167899392 :
    ThetaLowerSegment 167899392 167932160 (4197049703183 / 25000) (524733364374 / 3125) := by
  exact
    packedTile16384 167899392 167932160 12 1726 12957 27 _ _ (946943 / 50000) (1893889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167932160 :
    ThetaLowerSegment 167932160 167964928 (524733364374 / 3125) (8397337021413 / 50000) := by
  exact
    packedTile16384 167932160 167964928 12 1693 12958 27 _ _ (946953 / 50000) (1893909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167964928 :
    ThetaLowerSegment 167964928 167997696 (8397337021413 / 50000) (4199517936069 / 25000) := by
  exact
    packedTile16384 167964928 167997696 12 1794 12960 27 _ _ (75757 / 4000) (236741 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell167997696 :
    ThetaLowerSegment 167997696 168030464 (4199517936069 / 25000) (8400651407223 / 50000) := by
  exact
    packedTile16384 167997696 168030464 12 1706 12961 27 _ _ (378789 / 20000) (473487 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168030464 :
    ThetaLowerSegment 168030464 168063232 (8400651407223 / 50000) (8402259382659 / 50000) := by
  exact
    packedTile16384 168030464 168063232 12 1698 12962 27 _ _ (473491 / 25000) (1893967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168063232 :
    ThetaLowerSegment 168063232 168096000 (8402259382659 / 50000) (8403874951011 / 50000) := by
  exact
    packedTile16384 168063232 168096000 12 1706 12963 27 _ _ (59187 / 3125) (1893987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168096000 :
    ThetaLowerSegment 168096000 168128768 (8403874951011 / 50000) (4202756631803 / 25000) := by
  exact
    packedTile16384 168096000 168128768 12 1730 12965 27 _ _ (1894003 / 100000) (947003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168128768 :
    ThetaLowerSegment 168128768 168161536 (4202756631803 / 25000) (16814320233209 / 100000) := by
  exact
    packedTile16384 168128768 168161536 12 1739 12966 27 _ _ (1894023 / 100000) (947013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168161536 :
    ThetaLowerSegment 168161536 168194304 (16814320233209 / 100000) (16817653747129 / 100000) := by
  exact
    packedTile16384 168161536 168194304 12 1760 12967 27 _ _ (947021 / 50000) (378809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168194304 :
    ThetaLowerSegment 168194304 168227072 (16817653747129 / 100000) (16820938050637 / 100000) := by
  exact
    packedTile16384 168194304 168227072 12 1734 12968 27 _ _ (947031 / 50000) (378813 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168227072 :
    ThetaLowerSegment 168227072 168259840 (16820938050637 / 100000) (841208183529 / 5000) := by
  exact
    packedTile16384 168227072 168259840 12 1703 12970 27 _ _ (1894081 / 100000) (473521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168259840 :
    ThetaLowerSegment 168259840 168292608 (841208183529 / 5000) (3365486198961 / 20000) := by
  exact
    packedTile16384 168259840 168292608 12 1725 12971 27 _ _ (1894101 / 100000) (236763 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168292608 :
    ThetaLowerSegment 168292608 168325376 (3365486198961 / 20000) (3366144595073 / 20000) := by
  exact
    packedTile16384 168292608 168325376 12 1738 12972 27 _ _ (47353 / 2500) (1894123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168325376 :
    ThetaLowerSegment 168325376 168358144 (3366144595073 / 20000) (8417019806377 / 50000) := by
  exact
    packedTile16384 168325376 168358144 12 1751 12974 27 _ _ (1894139 / 100000) (947071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168358144 :
    ThetaLowerSegment 168358144 168390912 (8417019806377 / 50000) (16837280518803 / 100000) := by
  exact
    packedTile16384 168358144 168390912 12 1711 12975 27 _ _ (1894159 / 100000) (947081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168390912 :
    ThetaLowerSegment 168390912 168423680 (16837280518803 / 100000) (16840542293319 / 100000) := by
  exact
    packedTile16384 168390912 168423680 12 1722 12976 27 _ _ (947089 / 50000) (1894181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168423680 :
    ThetaLowerSegment 168423680 168456448 (16840542293319 / 100000) (3368768397247 / 20000) := by
  exact
    packedTile16384 168423680 168456448 12 1742 12977 27 _ _ (947099 / 50000) (1894201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168456448 :
    ThetaLowerSegment 168456448 168489216 (3368768397247 / 20000) (2105890583037 / 12500) := by
  exact
    packedTile16384 168456448 168489216 12 1733 12979 27 _ _ (1894217 / 100000) (94711 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168489216 :
    ThetaLowerSegment 168489216 168521984 (2105890583037 / 12500) (16850369492277 / 100000) := by
  exact
    packedTile16384 168489216 168521984 12 1713 12980 27 _ _ (1894237 / 100000) (11839 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168521984 :
    ThetaLowerSegment 168521984 168554752 (16850369492277 / 100000) (16853612458549 / 100000) := by
  exact
    packedTile16384 168521984 168554752 12 1712 12981 27 _ _ (118391 / 6250) (1894259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168554752 :
    ThetaLowerSegment 168554752 168587520 (16853612458549 / 100000) (16856823256369 / 100000) := by
  exact
    packedTile16384 168554752 168587520 12 1695 12982 27 _ _ (473569 / 25000) (1894279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168587520 :
    ThetaLowerSegment 168587520 168620288 (16856823256369 / 100000) (16860232987369 / 100000) := by
  exact
    packedTile16384 168587520 168620288 12 1800 12984 27 _ _ (378859 / 20000) (947149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168620288 :
    ThetaLowerSegment 168620288 168653056 (16860232987369 / 100000) (16863601077661 / 100000) := by
  exact
    packedTile16384 168620288 168653056 12 1778 12985 27 _ _ (947157 / 50000) (1894317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168653056 :
    ThetaLowerSegment 168653056 168685824 (16863601077661 / 100000) (16866849860471 / 100000) := by
  exact
    packedTile16384 168653056 168685824 12 1715 12986 27 _ _ (947167 / 50000) (1894337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168685824 :
    ThetaLowerSegment 168685824 168718592 (16866849860471 / 100000) (16870119513749 / 100000) := by
  exact
    packedTile16384 168685824 168718592 12 1726 12987 27 _ _ (1894353 / 100000) (473589 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168718592 :
    ThetaLowerSegment 168718592 168751360 (16870119513749 / 100000) (16873385412801 / 100000) := by
  exact
    packedTile16384 168718592 168751360 12 1724 12989 27 _ _ (1894373 / 100000) (236797 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168751360 :
    ThetaLowerSegment 168751360 168784128 (16873385412801 / 100000) (16876651344609 / 100000) := by
  exact
    packedTile16384 168751360 168784128 12 1724 12990 27 _ _ (236799 / 12500) (378879 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168784128 :
    ThetaLowerSegment 168784128 168816896 (16876651344609 / 100000) (3375983083297 / 20000) := by
  exact
    packedTile16384 168784128 168816896 12 1723 12991 27 _ _ (473603 / 25000) (378883 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168816896 :
    ThetaLowerSegment 168816896 168849664 (3375983083297 / 20000) (1055198009657 / 6250) := by
  exact
    packedTile16384 168816896 168849664 12 1717 12992 27 _ _ (1894431 / 100000) (947217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168849664 :
    ThetaLowerSegment 168849664 168882432 (1055198009657 / 6250) (2110804273289 / 12500) := by
  exact
    packedTile16384 168849664 168882432 12 1724 12994 27 _ _ (37889 / 2000) (1894453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168882432 :
    ThetaLowerSegment 168882432 168915200 (2110804273289 / 12500) (1055608160257 / 6250) := by
  exact
    packedTile16384 168882432 168915200 12 1740 12995 27 _ _ (189447 / 10000) (1894473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168915200 :
    ThetaLowerSegment 168915200 168947968 (1055608160257 / 6250) (3378608047279 / 20000) := by
  exact
    packedTile16384 168915200 168947968 12 1747 12996 27 _ _ (1894489 / 100000) (473623 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168947968 :
    ThetaLowerSegment 168947968 168980736 (3378608047279 / 20000) (16896268479731 / 100000) := by
  exact
    packedTile16384 168947968 168980736 12 1704 12997 27 _ _ (1894509 / 100000) (118407 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell168980736 :
    ThetaLowerSegment 168980736 169013504 (16896268479731 / 100000) (3379917917463 / 20000) := by
  exact
    packedTile16384 168980736 169013504 12 1753 12999 27 _ _ (59204 / 3125) (1894531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169013504 :
    ThetaLowerSegment 169013504 169046272 (3379917917463 / 20000) (4225721051137 / 25000) := by
  exact
    packedTile16384 169013504 169046272 12 1739 13000 27 _ _ (1894547 / 100000) (37891 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169046272 :
    ThetaLowerSegment 169046272 169079040 (4225721051137 / 25000) (16906175067427 / 100000) := by
  exact
    packedTile16384 169046272 169079040 12 1737 13001 27 _ _ (1894567 / 100000) (189457 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169079040 :
    ThetaLowerSegment 169079040 169111808 (16906175067427 / 100000) (676379093233 / 4000) := by
  exact
    packedTile16384 169079040 169111808 12 1743 13003 27 _ _ (947293 / 50000) (1894589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169111808 :
    ThetaLowerSegment 169111808 169144576 (676379093233 / 4000) (16912737947751 / 100000) := by
  exact
    packedTile16384 169111808 169144576 12 1721 13004 27 _ _ (947303 / 50000) (1894609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169144576 :
    ThetaLowerSegment 169144576 169177344 (16912737947751 / 100000) (2114505508547 / 12500) := by
  exact
    packedTile16384 169144576 169177344 12 1745 13005 27 _ _ (15157 / 800) (473657 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169177344 :
    ThetaLowerSegment 169177344 169210112 (2114505508547 / 12500) (4229810083201 / 25000) := by
  exact
    packedTile16384 169177344 169210112 12 1687 13006 27 _ _ (473661 / 25000) (1894647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169210112 :
    ThetaLowerSegment 169210112 169242880 (4229810083201 / 25000) (4230618631063 / 25000) := by
  exact
    packedTile16384 169210112 169242880 12 1707 13008 27 _ _ (236833 / 12500) (1894667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169242880 :
    ThetaLowerSegment 169242880 169275648 (4230618631063 / 25000) (16925822429113 / 100000) := by
  exact
    packedTile16384 169242880 169275648 12 1767 13009 27 _ _ (1894683 / 100000) (947343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169275648 :
    ThetaLowerSegment 169275648 169308416 (16925822429113 / 100000) (16929126789401 / 100000) := by
  exact
    packedTile16384 169275648 169308416 12 1744 13010 27 _ _ (947351 / 50000) (378941 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169308416 :
    ThetaLowerSegment 169308416 169341184 (16929126789401 / 100000) (16932381921797 / 100000) := by
  exact
    packedTile16384 169308416 169341184 12 1718 13011 27 _ _ (947361 / 50000) (75789 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169341184 :
    ThetaLowerSegment 169341184 169373952 (16932381921797 / 100000) (16935800034561 / 100000) := by
  exact
    packedTile16384 169341184 169373952 12 1804 13013 27 _ _ (1894741 / 100000) (236843 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169373952 :
    ThetaLowerSegment 169373952 169406720 (16935800034561 / 100000) (16939123443601 / 100000) := by
  exact
    packedTile16384 169373952 169406720 12 1754 13014 27 _ _ (47369 / 2500) (1894763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169406720 :
    ThetaLowerSegment 169406720 169439488 (16939123443601 / 100000) (16942433624261 / 100000) := by
  exact
    packedTile16384 169406720 169439488 12 1747 13015 27 _ _ (94739 / 5000) (1894783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169439488 :
    ThetaLowerSegment 169439488 169472256 (16942433624261 / 100000) (16945654782561 / 100000) := by
  exact
    packedTile16384 169439488 169472256 12 1700 13016 27 _ _ (1894799 / 100000) (947401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169472256 :
    ThetaLowerSegment 169472256 169505024 (16945654782561 / 100000) (16948983977787 / 100000) := by
  exact
    packedTile16384 169472256 169505024 12 1757 13018 27 _ _ (947409 / 50000) (1894821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169505024 :
    ThetaLowerSegment 169505024 169537792 (16948983977787 / 100000) (16952277206231 / 100000) := by
  exact
    packedTile16384 169505024 169537792 12 1738 13019 27 _ _ (947419 / 50000) (1894841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169537792 :
    ThetaLowerSegment 169537792 169570560 (16952277206231 / 100000) (16955566677983 / 100000) := by
  exact
    packedTile16384 169537792 169570560 12 1736 13020 27 _ _ (1894857 / 100000) (94743 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169570560 :
    ThetaLowerSegment 169570560 169603328 (16955566677983 / 100000) (16958850498091 / 100000) := by
  exact
    packedTile16384 169570560 169603328 12 1733 13021 27 _ _ (473719 / 25000) (1894879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169603328 :
    ThetaLowerSegment 169603328 169636096 (16958850498091 / 100000) (3392423459759 / 20000) := by
  exact
    packedTile16384 169603328 169636096 12 1724 13023 27 _ _ (118431 / 6250) (1894899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169636096 :
    ThetaLowerSegment 169636096 169668864 (3392423459759 / 20000) (848268353901 / 5000) := by
  exact
    packedTile16384 169636096 169668864 12 1715 13024 27 _ _ (378983 / 20000) (947459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169668864 :
    ThetaLowerSegment 169668864 169701632 (848268353901 / 5000) (8484285705707 / 50000) := by
  exact
    packedTile16384 169668864 169701632 12 1691 13025 27 _ _ (947467 / 50000) (1894937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169701632 :
    ThetaLowerSegment 169701632 169734400 (8484285705707 / 50000) (106074048668 / 625) := by
  exact
    packedTile16384 169701632 169734400 12 1729 13026 27 _ _ (947477 / 50000) (1894957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169734400 :
    ThetaLowerSegment 169734400 169767168 (106074048668 / 625) (4243790049921 / 25000) := by
  exact
    packedTile16384 169734400 169767168 12 1748 13028 27 _ _ (1894973 / 100000) (59218 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169767168 :
    ThetaLowerSegment 169767168 169799936 (4243790049921 / 25000) (4244598737757 / 25000) := by
  exact
    packedTile16384 169767168 169799936 12 1707 13029 27 _ _ (118437 / 6250) (378999 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169799936 :
    ThetaLowerSegment 169799936 169832704 (4244598737757 / 25000) (4245417382941 / 25000) := by
  exact
    packedTile16384 169799936 169832704 12 1728 13030 27 _ _ (473753 / 25000) (379003 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169832704 :
    ThetaLowerSegment 169832704 169865472 (4245417382941 / 25000) (16984995311169 / 100000) := by
  exact
    packedTile16384 169832704 169865472 12 1755 13031 27 _ _ (1895031 / 100000) (947517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169865472 :
    ThetaLowerSegment 169865472 169898240 (16984995311169 / 100000) (16988304068469 / 100000) := by
  exact
    packedTile16384 169865472 169898240 12 1746 13033 27 _ _ (37901 / 2000) (1895053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169898240 :
    ThetaLowerSegment 169898240 169931008 (16988304068469 / 100000) (16991548428309 / 100000) := by
  exact
    packedTile16384 169898240 169931008 12 1712 13034 27 _ _ (189507 / 10000) (1895073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169931008 :
    ThetaLowerSegment 169931008 169963776 (16991548428309 / 100000) (16994785240321 / 100000) := by
  exact
    packedTile16384 169931008 169963776 12 1708 13035 27 _ _ (1895089 / 100000) (473773 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169963776 :
    ThetaLowerSegment 169963776 169996544 (16994785240321 / 100000) (16998014504353 / 100000) := by
  exact
    packedTile16384 169963776 169996544 12 1704 13037 27 _ _ (473777 / 25000) (1895111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell169996544 :
    ThetaLowerSegment 169996544 170029312 (16998014504353 / 100000) (17001327186349 / 100000) := by
  exact
    packedTile16384 169996544 170029312 12 1748 13038 27 _ _ (1895127 / 100000) (189513 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170029312 :
    ThetaLowerSegment 170029312 170062080 (17001327186349 / 100000) (3400916609779 / 20000) := by
  exact
    packedTile16384 170029312 170062080 12 1718 13039 27 _ _ (1895147 / 100000) (37903 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170062080 :
    ThetaLowerSegment 170062080 170094848 (3400916609779 / 20000) (17007952654043 / 100000) := by
  exact
    packedTile16384 170062080 170094848 12 1778 13040 27 _ _ (947583 / 50000) (1895169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170094848 :
    ThetaLowerSegment 170094848 170127616 (17007952654043 / 100000) (17011246485573 / 100000) := by
  exact
    packedTile16384 170094848 170127616 12 1738 13042 27 _ _ (379037 / 20000) (473797 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170127616 :
    ThetaLowerSegment 170127616 170160384 (17011246485573 / 100000) (3402904279617 / 20000) := by
  exact
    packedTile16384 170127616 170160384 12 1728 13043 27 _ _ (473801 / 25000) (1895207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170160384 :
    ThetaLowerSegment 170160384 170193152 (3402904279617 / 20000) (17017898687253 / 100000) := by
  exact
    packedTile16384 170160384 170193152 12 1782 13044 27 _ _ (236903 / 12500) (1895227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170193152 :
    ThetaLowerSegment 170193152 170225920 (17017898687253 / 100000) (17021154714727 / 100000) := by
  exact
    packedTile16384 170193152 170225920 12 1718 13045 27 _ _ (1895243 / 100000) (947623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170225920 :
    ThetaLowerSegment 170225920 170258688 (17021154714727 / 100000) (17024416460629 / 100000) := by
  exact
    packedTile16384 170225920 170258688 12 1721 13047 27 _ _ (947631 / 50000) (379053 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170258688 :
    ThetaLowerSegment 170258688 170291456 (17024416460629 / 100000) (17027718040131 / 100000) := by
  exact
    packedTile16384 170258688 170291456 12 1742 13048 27 _ _ (1895281 / 100000) (473821 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170291456 :
    ThetaLowerSegment 170291456 170324224 (17027718040131 / 100000) (17030962795443 / 100000) := by
  exact
    packedTile16384 170291456 170324224 12 1712 13049 27 _ _ (1895301 / 100000) (236913 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170324224 :
    ThetaLowerSegment 170324224 170356992 (17030962795443 / 100000) (17034249280323 / 100000) := by
  exact
    packedTile16384 170324224 170356992 12 1734 13050 27 _ _ (47383 / 2500) (1895323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170356992 :
    ThetaLowerSegment 170356992 170389760 (17034249280323 / 100000) (8518770742083 / 50000) := by
  exact
    packedTile16384 170356992 170389760 12 1737 13052 27 _ _ (1895339 / 100000) (947671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170389760 :
    ThetaLowerSegment 170389760 170422528 (8518770742083 / 50000) (8520403593 / 50) := by
  exact
    packedTile16384 170389760 170422528 12 1723 13053 27 _ _ (947679 / 50000) (1895361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170422528 :
    ThetaLowerSegment 170422528 170455296 (8520403593 / 50) (4261015861351 / 25000) := by
  exact
    packedTile16384 170422528 170455296 12 1718 13054 27 _ _ (947689 / 50000) (1895381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170455296 :
    ThetaLowerSegment 170455296 170488064 (4261015861351 / 25000) (17047333005229 / 100000) := by
  exact
    packedTile16384 170455296 170488064 12 1725 13055 27 _ _ (1895397 / 100000) (9477 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170488064 :
    ThetaLowerSegment 170488064 170520832 (17047333005229 / 100000) (17050570375757 / 100000) := by
  exact
    packedTile16384 170488064 170520832 12 1708 13057 27 _ _ (236927 / 12500) (1895419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170520832 :
    ThetaLowerSegment 170520832 170553600 (17050570375757 / 100000) (8526933268611 / 50000) := by
  exact
    packedTile16384 170520832 170553600 12 1739 13058 27 _ _ (379087 / 20000) (947719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170553600 :
    ThetaLowerSegment 170553600 170586368 (8526933268611 / 50000) (8528555778091 / 50000) := by
  exact
    packedTile16384 170553600 170586368 12 1712 13059 27 _ _ (379091 / 20000) (947729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170586368 :
    ThetaLowerSegment 170586368 170619136 (8528555778091 / 50000) (2132546708367 / 12500) := by
  exact
    packedTile16384 170586368 170619136 12 1721 13060 27 _ _ (947737 / 50000) (1895477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170619136 :
    ThetaLowerSegment 170619136 170651904 (2132546708367 / 12500) (8531830225899 / 50000) := by
  exact
    packedTile16384 170619136 170651904 12 1734 13062 27 _ _ (1895493 / 100000) (236937 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170651904 :
    ThetaLowerSegment 170651904 170684672 (8531830225899 / 50000) (8533407291883 / 50000) := by
  exact
    packedTile16384 170651904 170684672 12 1664 13063 27 _ _ (236939 / 12500) (379103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170684672 :
    ThetaLowerSegment 170684672 170717440 (8533407291883 / 50000) (8535071568101 / 50000) := by
  exact
    packedTile16384 170684672 170717440 12 1756 13064 27 _ _ (1895531 / 100000) (947767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170717440 :
    ThetaLowerSegment 170717440 170750208 (8535071568101 / 50000) (2134174013827 / 12500) := by
  exact
    packedTile16384 170717440 170750208 12 1714 13065 27 _ _ (1895551 / 100000) (947777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170750208 :
    ThetaLowerSegment 170750208 170782976 (2134174013827 / 12500) (4269173548389 / 25000) := by
  exact
    packedTile16384 170750208 170782976 12 1742 13067 27 _ _ (189557 / 10000) (1895573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170782976 :
    ThetaLowerSegment 170782976 170815744 (4269173548389 / 25000) (17079914799267 / 100000) := by
  exact
    packedTile16384 170782976 170815744 12 1699 13068 27 _ _ (1895589 / 100000) (236949 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170815744 :
    ThetaLowerSegment 170815744 170848512 (17079914799267 / 100000) (17083226426443 / 100000) := by
  exact
    packedTile16384 170815744 170848512 12 1747 13069 27 _ _ (236951 / 12500) (1895611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170848512 :
    ThetaLowerSegment 170848512 170881280 (17083226426443 / 100000) (4271634521703 / 25000) := by
  exact
    packedTile16384 170848512 170881280 12 1747 13070 27 _ _ (1895627 / 100000) (189563 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170881280 :
    ThetaLowerSegment 170881280 170914048 (4271634521703 / 25000) (8544879394683 / 50000) := by
  exact
    packedTile16384 170881280 170914048 12 1699 13072 27 _ _ (947823 / 50000) (1895649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170914048 :
    ThetaLowerSegment 170914048 170946816 (8544879394683 / 50000) (4273279003463 / 25000) := by
  exact
    packedTile16384 170914048 170946816 12 1771 13073 27 _ _ (947833 / 50000) (1895669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170946816 :
    ThetaLowerSegment 170946816 170979584 (4273279003463 / 25000) (17096344365407 / 100000) := by
  exact
    packedTile16384 170946816 170979584 12 1703 13074 27 _ _ (379137 / 20000) (236961 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell170979584 :
    ThetaLowerSegment 170979584 171012352 (17096344365407 / 100000) (3419935023467 / 20000) := by
  exact
    packedTile16384 170979584 171012352 12 1757 13075 27 _ _ (236963 / 12500) (1895707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171012352 :
    ThetaLowerSegment 171012352 171045120 (3419935023467 / 20000) (17102966092463 / 100000) := by
  exact
    packedTile16384 171012352 171045120 12 1736 13077 27 _ _ (1895723 / 100000) (947863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171045120 :
    ThetaLowerSegment 171045120 171077888 (17102966092463 / 100000) (17106258996317 / 100000) := by
  exact
    packedTile16384 171045120 171077888 12 1737 13078 27 _ _ (947871 / 50000) (379149 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171077888 :
    ThetaLowerSegment 171077888 171110656 (17106258996317 / 100000) (1069346284913 / 6250) := by
  exact
    packedTile16384 171077888 171110656 12 1731 13079 27 _ _ (1895761 / 100000) (473941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171110656 :
    ThetaLowerSegment 171110656 171143424 (1069346284913 / 6250) (8556455628613 / 50000) := by
  exact
    packedTile16384 171110656 171143424 12 1778 13080 27 _ _ (1895781 / 100000) (236973 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171143424 :
    ThetaLowerSegment 171143424 171176192 (8556455628613 / 50000) (8558099287213 / 50000) := by
  exact
    packedTile16384 171143424 171176192 12 1734 13082 27 _ _ (9479 / 500) (1895803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171176192 :
    ThetaLowerSegment 171176192 171208960 (8558099287213 / 50000) (534982750256 / 3125) := by
  exact
    packedTile16384 171176192 171208960 12 1714 13083 27 _ _ (1895819 / 100000) (947911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171208960 :
    ThetaLowerSegment 171208960 171241728 (534982750256 / 3125) (428069427493 / 2500) := by
  exact
    packedTile16384 171208960 171241728 12 1756 13084 27 _ _ (947919 / 50000) (1895841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171241728 :
    ThetaLowerSegment 171241728 171274496 (428069427493 / 2500) (17126111912183 / 100000) := by
  exact
    packedTile16384 171241728 171274496 12 1759 13085 27 _ _ (1895857 / 100000) (94793 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171274496 :
    ThetaLowerSegment 171274496 171307264 (17126111912183 / 100000) (17129384194159 / 100000) := by
  exact
    packedTile16384 171274496 171307264 12 1726 13087 27 _ _ (473969 / 25000) (1895879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171307264 :
    ThetaLowerSegment 171307264 171340032 (17129384194159 / 100000) (17132648925349 / 100000) := by
  exact
    packedTile16384 171307264 171340032 12 1722 13088 27 _ _ (379179 / 20000) (947949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171340032 :
    ThetaLowerSegment 171340032 171372800 (17132648925349 / 100000) (1070991643319 / 6250) := by
  exact
    packedTile16384 171340032 171372800 12 1697 13089 27 _ _ (379183 / 20000) (947959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171372800 :
    ThetaLowerSegment 171372800 171405568 (1070991643319 / 6250) (2142395652283 / 12500) := by
  exact
    packedTile16384 171372800 171405568 12 1740 13090 27 _ _ (947967 / 50000) (1895937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171405568 :
    ThetaLowerSegment 171405568 171438336 (2142395652283 / 12500) (17142485031967 / 100000) := by
  exact
    packedTile16384 171405568 171438336 12 1751 13092 27 _ _ (1895953 / 100000) (473989 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171438336 :
    ThetaLowerSegment 171438336 171471104 (17142485031967 / 100000) (17145721456171 / 100000) := by
  exact
    packedTile16384 171438336 171471104 12 1707 13093 27 _ _ (473993 / 25000) (75839 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171471104 :
    ThetaLowerSegment 171471104 171503872 (17145721456171 / 100000) (8574526356179 / 50000) := by
  exact
    packedTile16384 171471104 171503872 12 1757 13094 27 _ _ (1895991 / 100000) (947997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171503872 :
    ThetaLowerSegment 171503872 171536640 (8574526356179 / 50000) (8576189156949 / 50000) := by
  exact
    packedTile16384 171503872 171536640 12 1754 13095 27 _ _ (189601 / 10000) (1896013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171536640 :
    ThetaLowerSegment 171536640 171569408 (8576189156949 / 50000) (2144443085291 / 12500) := by
  exact
    packedTile16384 171536640 171569408 12 1670 13097 27 _ _ (1896029 / 100000) (59251 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171569408 :
    ThetaLowerSegment 171569408 171602176 (2144443085291 / 12500) (2144856186749 / 12500) := by
  exact
    packedTile16384 171569408 171602176 12 1743 13098 27 _ _ (118503 / 6250) (1896051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171602176 :
    ThetaLowerSegment 171602176 171634944 (2144856186749 / 12500) (8581034507879 / 50000) := by
  exact
    packedTile16384 171602176 171634944 12 1698 13099 27 _ _ (1896067 / 100000) (189607 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171634944 :
    ThetaLowerSegment 171634944 171667712 (8581034507879 / 50000) (4291322142871 / 25000) := by
  exact
    packedTile16384 171634944 171667712 12 1698 13100 27 _ _ (1896087 / 100000) (189609 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171667712 :
    ThetaLowerSegment 171667712 171700480 (4291322142871 / 25000) (8584283469379 / 50000) := by
  exact
    packedTile16384 171667712 171700480 12 1729 13102 27 _ _ (948053 / 50000) (1896109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171700480 :
    ThetaLowerSegment 171700480 171733248 (8584283469379 / 50000) (2146486592751 / 12500) := by
  exact
    packedTile16384 171700480 171733248 12 1754 13103 27 _ _ (15169 / 800) (59254 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171733248 :
    ThetaLowerSegment 171733248 171766016 (2146486592751 / 12500) (2146903033377 / 12500) := by
  exact
    packedTile16384 171733248 171766016 12 1757 13104 27 _ _ (118509 / 6250) (1896147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171766016 :
    ThetaLowerSegment 171766016 171798784 (2146903033377 / 12500) (17178536863777 / 100000) := by
  exact
    packedTile16384 171766016 171798784 12 1747 13105 27 _ _ (1896163 / 100000) (948083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171798784 :
    ThetaLowerSegment 171798784 171831552 (17178536863777 / 100000) (17181845701367 / 100000) := by
  exact
    packedTile16384 171798784 171831552 12 1745 13107 27 _ _ (948091 / 50000) (379237 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171831552 :
    ThetaLowerSegment 171831552 171864320 (17181845701367 / 100000) (17185145091107 / 100000) := by
  exact
    packedTile16384 171831552 171864320 12 1740 13108 27 _ _ (1896201 / 100000) (474051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171864320 :
    ThetaLowerSegment 171864320 171897088 (17185145091107 / 100000) (17188364872667 / 100000) := by
  exact
    packedTile16384 171864320 171897088 12 1698 13109 27 _ _ (94811 / 5000) (1896223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171897088 :
    ThetaLowerSegment 171897088 171929856 (17188364872667 / 100000) (17191615026313 / 100000) := by
  exact
    packedTile16384 171897088 171929856 12 1714 13110 27 _ _ (1896239 / 100000) (948121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171929856 :
    ThetaLowerSegment 171929856 171962624 (17191615026313 / 100000) (17194882278847 / 100000) := by
  exact
    packedTile16384 171929856 171962624 12 1723 13112 27 _ _ (948129 / 50000) (1896261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171962624 :
    ThetaLowerSegment 171962624 171995392 (17194882278847 / 100000) (17198124912517 / 100000) := by
  exact
    packedTile16384 171962624 171995392 12 1710 13113 27 _ _ (1896277 / 100000) (47407 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell171995392 :
    ThetaLowerSegment 171995392 172028160 (17198124912517 / 100000) (3440284134993 / 20000) := by
  exact
    packedTile16384 171995392 172028160 12 1738 13114 27 _ _ (237037 / 12500) (1896299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172028160 :
    ThetaLowerSegment 172028160 172060928 (3440284134993 / 20000) (68818873467 / 400) := by
  exact
    packedTile16384 172028160 172060928 12 1739 13115 27 _ _ (379263 / 20000) (948159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172060928 :
    ThetaLowerSegment 172060928 172093696 (68818873467 / 400) (2150998218779 / 12500) := by
  exact
    packedTile16384 172060928 172093696 12 1723 13117 27 _ _ (948167 / 50000) (1896337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172093696 :
    ThetaLowerSegment 172093696 172126464 (2150998218779 / 12500) (2151415416439 / 12500) := by
  exact
    packedTile16384 172093696 172126464 12 1760 13118 27 _ _ (1896353 / 100000) (474089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172126464 :
    ThetaLowerSegment 172126464 172159232 (2151415416439 / 12500) (17214514927271 / 100000) := by
  exact
    packedTile16384 172126464 172159232 12 1683 13119 27 _ _ (1896373 / 100000) (237047 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172159232 :
    ThetaLowerSegment 172159232 172192000 (17214514927271 / 100000) (17217824131311 / 100000) := by
  exact
    packedTile16384 172159232 172192000 12 1745 13120 27 _ _ (237049 / 12500) (379279 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172192000 :
    ThetaLowerSegment 172192000 172224768 (17217824131311 / 100000) (17221051822833 / 100000) := by
  exact
    packedTile16384 172192000 172224768 12 1702 13122 27 _ _ (1896411 / 100000) (948207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172224768 :
    ThetaLowerSegment 172224768 172257536 (17221051822833 / 100000) (17224383850343 / 100000) := by
  exact
    packedTile16384 172224768 172257536 12 1757 13123 27 _ _ (189643 / 10000) (1896433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172257536 :
    ThetaLowerSegment 172257536 172290304 (17224383850343 / 100000) (17227702636093 / 100000) := by
  exact
    packedTile16384 172257536 172290304 12 1750 13124 27 _ _ (1896449 / 100000) (474113 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172290304 :
    ThetaLowerSegment 172290304 172323072 (17227702636093 / 100000) (17230913356417 / 100000) := by
  exact
    packedTile16384 172290304 172323072 12 1693 13125 27 _ _ (474117 / 25000) (1896471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172323072 :
    ThetaLowerSegment 172323072 172355840 (17230913356417 / 100000) (4308549992097 / 25000) := by
  exact
    packedTile16384 172323072 172355840 12 1733 13127 27 _ _ (1896487 / 100000) (189649 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172355840 :
    ThetaLowerSegment 172355840 172388608 (4308549992097 / 25000) (1723755109449 / 10000) := by
  exact
    packedTile16384 172355840 172388608 12 1767 13128 27 _ _ (948253 / 50000) (1896509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172388608 :
    ThetaLowerSegment 172388608 172421376 (1723755109449 / 10000) (431019474501 / 2500) := by
  exact
    packedTile16384 172388608 172421376 12 1702 13129 27 _ _ (75861 / 4000) (118533 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172421376 :
    ThetaLowerSegment 172421376 172454144 (431019474501 / 2500) (431102448301 / 2500) := by
  exact
    packedTile16384 172421376 172454144 12 1750 13130 27 _ _ (59267 / 3125) (1896547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172454144 :
    ThetaLowerSegment 172454144 172486912 (431102448301 / 2500) (17247282261317 / 100000) := by
  exact
    packedTile16384 172454144 172486912 12 1679 13132 27 _ _ (1896563 / 100000) (948283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172486912 :
    ThetaLowerSegment 172486912 172519680 (17247282261317 / 100000) (3450119876647 / 20000) := by
  exact
    packedTile16384 172486912 172519680 12 1749 13133 27 _ _ (948291 / 50000) (379317 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172519680 :
    ThetaLowerSegment 172519680 172552448 (3450119876647 / 20000) (1078369783649 / 6250) := by
  exact
    packedTile16384 172519680 172552448 12 1749 13134 27 _ _ (1896601 / 100000) (474151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172552448 :
    ThetaLowerSegment 172552448 172585216 (1078369783649 / 6250) (539285175607 / 3125) := by
  exact
    packedTile16384 172552448 172585216 12 1692 13135 27 _ _ (94831 / 5000) (1896623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172585216 :
    ThetaLowerSegment 172585216 172617984 (539285175607 / 3125) (690418472297 / 4000) := by
  exact
    packedTile16384 172585216 172617984 12 1759 13137 27 _ _ (1896639 / 100000) (948321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172617984 :
    ThetaLowerSegment 172617984 172650752 (690418472297 / 4000) (17263722162527 / 100000) := by
  exact
    packedTile16384 172617984 172650752 12 1719 13138 27 _ _ (948329 / 50000) (1896661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172650752 :
    ThetaLowerSegment 172650752 172683520 (17263722162527 / 100000) (17266980653613 / 100000) := by
  exact
    packedTile16384 172650752 172683520 12 1718 13139 27 _ _ (1896677 / 100000) (47417 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172683520 :
    ThetaLowerSegment 172683520 172716288 (17266980653613 / 100000) (17270241074037 / 100000) := by
  exact
    packedTile16384 172683520 172716288 12 1719 13140 27 _ _ (237087 / 12500) (1896699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172716288 :
    ThetaLowerSegment 172716288 172749056 (17270241074037 / 100000) (17273526184417 / 100000) := by
  exact
    packedTile16384 172716288 172749056 12 1732 13142 27 _ _ (379343 / 20000) (948359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172749056 :
    ThetaLowerSegment 172749056 172781824 (17273526184417 / 100000) (17276780979961 / 100000) := by
  exact
    packedTile16384 172749056 172781824 12 1716 13143 27 _ _ (948367 / 50000) (1896737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172781824 :
    ThetaLowerSegment 172781824 172814592 (17276780979961 / 100000) (8640045406973 / 50000) := by
  exact
    packedTile16384 172781824 172814592 12 1745 13144 27 _ _ (1896753 / 100000) (474189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172814592 :
    ThetaLowerSegment 172814592 172847360 (8640045406973 / 50000) (17283290666623 / 100000) := by
  exact
    packedTile16384 172814592 172847360 12 1687 13145 27 _ _ (1896771 / 100000) (948387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172847360 :
    ThetaLowerSegment 172847360 172880128 (17283290666623 / 100000) (17286642294553 / 100000) := by
  exact
    packedTile16384 172847360 172880128 12 1767 13147 27 _ _ (189679 / 10000) (1896793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172880128 :
    ThetaLowerSegment 172880128 172912896 (17286642294553 / 100000) (8644923002477 / 50000) := by
  exact
    packedTile16384 172880128 172912896 12 1689 13148 27 _ _ (1896809 / 100000) (474203 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172912896 :
    ThetaLowerSegment 172912896 172945664 (8644923002477 / 50000) (8646562810283 / 50000) := by
  exact
    packedTile16384 172912896 172945664 12 1729 13149 27 _ _ (474207 / 25000) (1896831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172945664 :
    ThetaLowerSegment 172945664 172978432 (8646562810283 / 50000) (4324086616693 / 25000) := by
  exact
    packedTile16384 172945664 172978432 12 1698 13150 27 _ _ (1896847 / 100000) (37937 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell172978432 :
    ThetaLowerSegment 172978432 173011200 (4324086616693 / 25000) (4324921237733 / 25000) := by
  exact
    packedTile16384 172978432 173011200 12 1760 13152 27 _ _ (948433 / 50000) (1896869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173011200 :
    ThetaLowerSegment 173011200 173043968 (4324921237733 / 25000) (8651502249841 / 50000) := by
  exact
    packedTile16384 173011200 173043968 12 1750 13153 27 _ _ (379377 / 20000) (237111 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173043968 :
    ThetaLowerSegment 173043968 173076736 (8651502249841 / 50000) (1730629942193 / 10000) := by
  exact
    packedTile16384 173043968 173076736 12 1737 13154 27 _ _ (237113 / 12500) (1896907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173076736 :
    ThetaLowerSegment 173076736 173109504 (1730629942193 / 10000) (865477158013 / 5000) := by
  exact
    packedTile16384 173076736 173109504 12 1710 13155 27 _ _ (1896923 / 100000) (948463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173109504 :
    ThetaLowerSegment 173109504 173142272 (865477158013 / 5000) (8656413383431 / 50000) := by
  exact
    packedTile16384 173109504 173142272 12 1731 13157 27 _ _ (948471 / 50000) (379389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173142272 :
    ThetaLowerSegment 173142272 173175040 (8656413383431 / 50000) (4329029024309 / 25000) := by
  exact
    packedTile16384 173142272 173175040 12 1734 13158 27 _ _ (1896961 / 100000) (474241 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173175040 :
    ThetaLowerSegment 173175040 173207808 (4329029024309 / 25000) (4329852313629 / 25000) := by
  exact
    packedTile16384 173175040 173207808 12 1736 13159 27 _ _ (94849 / 5000) (1896983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173207808 :
    ThetaLowerSegment 173207808 173240576 (4329852313629 / 25000) (17322624667821 / 100000) := by
  exact
    packedTile16384 173207808 173240576 12 1695 13160 27 _ _ (1896999 / 100000) (948501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173240576 :
    ThetaLowerSegment 173240576 173273344 (17322624667821 / 100000) (17325828731223 / 100000) := by
  exact
    packedTile16384 173240576 173273344 12 1689 13162 27 _ _ (948509 / 50000) (1897021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173273344 :
    ThetaLowerSegment 173273344 173306112 (17325828731223 / 100000) (17329186486713 / 100000) := by
  exact
    packedTile16384 173273344 173306112 12 1770 13163 27 _ _ (1897037 / 100000) (23713 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173306112 :
    ThetaLowerSegment 173306112 173338880 (17329186486713 / 100000) (17332489261209 / 100000) := by
  exact
    packedTile16384 173306112 173338880 12 1741 13164 27 _ _ (59283 / 3125) (1897059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173338880 :
    ThetaLowerSegment 173338880 173371648 (17332489261209 / 100000) (17335757919711 / 100000) := by
  exact
    packedTile16384 173338880 173371648 12 1723 13165 27 _ _ (948537 / 50000) (1897077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173371648 :
    ThetaLowerSegment 173371648 173404416 (17335757919711 / 100000) (17339119568507 / 100000) := by
  exact
    packedTile16384 173371648 173404416 12 1772 13167 27 _ _ (1897093 / 100000) (237137 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173404416 :
    ThetaLowerSegment 173404416 173437184 (17339119568507 / 100000) (17342403469379 / 100000) := by
  exact
    packedTile16384 173404416 173437184 12 1731 13168 27 _ _ (237139 / 12500) (379423 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173437184 :
    ThetaLowerSegment 173437184 173469952 (17342403469379 / 100000) (3469139377759 / 20000) := by
  exact
    packedTile16384 173437184 173469952 12 1736 13169 27 _ _ (1897131 / 100000) (948567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173469952 :
    ThetaLowerSegment 173469952 173502720 (3469139377759 / 20000) (3469789720779 / 20000) := by
  exact
    packedTile16384 173469952 173502720 12 1714 13170 27 _ _ (37943 / 2000) (1897153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173502720 :
    ThetaLowerSegment 173502720 173535488 (3469789720779 / 20000) (694092263721 / 4000) := by
  exact
    packedTile16384 173502720 173535488 12 1770 13172 27 _ _ (1897169 / 100000) (474293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173535488 :
    ThetaLowerSegment 173535488 173568256 (694092263721 / 4000) (17355611494521 / 100000) := by
  exact
    packedTile16384 173535488 173568256 12 1742 13173 27 _ _ (474297 / 25000) (1897191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173568256 :
    ThetaLowerSegment 173568256 173601024 (17355611494521 / 100000) (17358863307319 / 100000) := by
  exact
    packedTile16384 173568256 173601024 12 1714 13174 27 _ _ (1897207 / 100000) (189721 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173601024 :
    ThetaLowerSegment 173601024 173633792 (17358863307319 / 100000) (17362134124943 / 100000) := by
  exact
    packedTile16384 173601024 173633792 12 1724 13175 27 _ _ (948613 / 50000) (1897229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173633792 :
    ThetaLowerSegment 173633792 173666560 (17362134124943 / 100000) (3473074923539 / 20000) := by
  exact
    packedTile16384 173633792 173666560 12 1708 13177 27 _ _ (474311 / 25000) (1897247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173666560 :
    ThetaLowerSegment 173666560 173699328 (3473074923539 / 20000) (8684365437971 / 50000) := by
  exact
    packedTile16384 173666560 173699328 12 1769 13178 27 _ _ (1897263 / 100000) (948633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173699328 :
    ThetaLowerSegment 173699328 173732096 (8684365437971 / 50000) (434300281913 / 2500) := by
  exact
    packedTile16384 173699328 173732096 12 1729 13179 27 _ _ (948641 / 50000) (379457 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173732096 :
    ThetaLowerSegment 173732096 173764864 (434300281913 / 2500) (17375219612511 / 100000) := by
  exact
    packedTile16384 173732096 173764864 12 1691 13180 27 _ _ (1897301 / 100000) (237163 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173764864 :
    ThetaLowerSegment 173764864 173797632 (17375219612511 / 100000) (17378469721671 / 100000) := by
  exact
    packedTile16384 173764864 173797632 12 1713 13181 27 _ _ (47433 / 2500) (1897323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173797632 :
    ThetaLowerSegment 173797632 173830400 (17378469721671 / 100000) (8690878905079 / 50000) := by
  exact
    packedTile16384 173797632 173830400 12 1733 13183 27 _ _ (1897339 / 100000) (948671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173830400 :
    ThetaLowerSegment 173830400 173863168 (8690878905079 / 50000) (4346238714597 / 25000) := by
  exact
    packedTile16384 173830400 173863168 12 1685 13184 27 _ _ (948679 / 50000) (1897361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173863168 :
    ThetaLowerSegment 173863168 173895936 (4346238714597 / 25000) (4347061701437 / 25000) := by
  exact
    packedTile16384 173863168 173895936 12 1735 13185 27 _ _ (59293 / 3125) (1897379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173895936 :
    ThetaLowerSegment 173895936 173928704 (4347061701437 / 25000) (1086972715763 / 6250) := by
  exact
    packedTile16384 173895936 173928704 12 1748 13186 27 _ _ (379479 / 20000) (948699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173928704 :
    ThetaLowerSegment 173928704 173961472 (1086972715763 / 6250) (8697393579297 / 50000) := by
  exact
    packedTile16384 173928704 173961472 12 1699 13188 27 _ _ (948707 / 50000) (1897417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173961472 :
    ThetaLowerSegment 173961472 173994240 (8697393579297 / 50000) (17398086794581 / 100000) := by
  exact
    packedTile16384 173961472 173994240 12 1739 13189 27 _ _ (1897433 / 100000) (474359 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell173994240 :
    ThetaLowerSegment 173994240 174027008 (17398086794581 / 100000) (17401390258513 / 100000) := by
  exact
    packedTile16384 173994240 174027008 12 1741 13190 27 _ _ (474363 / 25000) (379491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174027008 :
    ThetaLowerSegment 174027008 174059776 (17401390258513 / 100000) (8702348775233 / 50000) := by
  exact
    packedTile16384 174027008 174059776 12 1743 13191 27 _ _ (1897471 / 100000) (948737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174059776 :
    ThetaLowerSegment 174059776 174092544 (8702348775233 / 50000) (17408027643661 / 100000) := by
  exact
    packedTile16384 174059776 174092544 12 1755 13193 27 _ _ (1897489 / 100000) (474373 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174092544 :
    ThetaLowerSegment 174092544 174125312 (17408027643661 / 100000) (17411262894801 / 100000) := by
  exact
    packedTile16384 174092544 174125312 12 1705 13194 27 _ _ (474377 / 25000) (1897511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174125312 :
    ThetaLowerSegment 174125312 174158080 (17411262894801 / 100000) (17414560796727 / 100000) := by
  exact
    packedTile16384 174125312 174158080 12 1738 13195 27 _ _ (1897527 / 100000) (189753 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174158080 :
    ThetaLowerSegment 174158080 174190848 (17414560796727 / 100000) (17417786624927 / 100000) := by
  exact
    packedTile16384 174158080 174190848 12 1700 13196 27 _ _ (948773 / 50000) (1897549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174190848 :
    ThetaLowerSegment 174190848 174223616 (17417786624927 / 100000) (17421073207507 / 100000) := by
  exact
    packedTile16384 174190848 174223616 12 1732 13198 27 _ _ (379513 / 20000) (59299 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174223616 :
    ThetaLowerSegment 174223616 174256384 (17421073207507 / 100000) (3484871964599 / 20000) := by
  exact
    packedTile16384 174223616 174256384 12 1732 13199 27 _ _ (118599 / 6250) (1897587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174256384 :
    ThetaLowerSegment 174256384 174289152 (3484871964599 / 20000) (17427674933689 / 100000) := by
  exact
    packedTile16384 174256384 174289152 12 1747 13200 27 _ _ (948801 / 50000) (379521 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174289152 :
    ThetaLowerSegment 174289152 174321920 (17427674933689 / 100000) (8715458983989 / 50000) := by
  exact
    packedTile16384 174289152 174321920 12 1709 13201 27 _ _ (1897621 / 100000) (237203 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174321920 :
    ThetaLowerSegment 174321920 174354688 (8715458983989 / 50000) (8717099493769 / 50000) := by
  exact
    packedTile16384 174321920 174354688 12 1729 13203 27 _ _ (47441 / 2500) (1897643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174354688 :
    ThetaLowerSegment 174354688 174387456 (8717099493769 / 50000) (1743747814229 / 10000) := by
  exact
    packedTile16384 174354688 174387456 12 1728 13204 27 _ _ (1897659 / 100000) (948831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174387456 :
    ThetaLowerSegment 174387456 174420224 (1743747814229 / 10000) (1744072317167 / 10000) := by
  exact
    packedTile16384 174387456 174420224 12 1710 13205 27 _ _ (948839 / 50000) (1897681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174420224 :
    ThetaLowerSegment 174420224 174452992 (1744072317167 / 10000) (8721957548171 / 50000) := by
  exact
    packedTile16384 174420224 174452992 12 1682 13206 27 _ _ (59303 / 3125) (1897699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174452992 :
    ThetaLowerSegment 174452992 174485760 (8721957548171 / 50000) (8723612355651 / 50000) := by
  exact
    packedTile16384 174452992 174485760 12 1744 13208 27 _ _ (379543 / 20000) (948859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174485760 :
    ThetaLowerSegment 174485760 174518528 (8723612355651 / 50000) (8725231122753 / 50000) := by
  exact
    packedTile16384 174485760 174518528 12 1706 13209 27 _ _ (948867 / 50000) (1897737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174518528 :
    ThetaLowerSegment 174518528 174551296 (8725231122753 / 50000) (872688027011 / 5000) := by
  exact
    packedTile16384 174518528 174551296 12 1738 13210 27 _ _ (1897753 / 100000) (474439 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174551296 :
    ThetaLowerSegment 174551296 174584064 (872688027011 / 5000) (17457011421943 / 100000) := by
  exact
    packedTile16384 174551296 174584064 12 1713 13211 27 _ _ (1897771 / 100000) (948887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174584064 :
    ThetaLowerSegment 174584064 174616832 (17457011421943 / 100000) (17460266131793 / 100000) := by
  exact
    packedTile16384 174584064 174616832 12 1715 13213 27 _ _ (189779 / 10000) (1897793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174616832 :
    ThetaLowerSegment 174616832 174649600 (17460266131793 / 100000) (2182933466947 / 12500) := by
  exact
    packedTile16384 174616832 174649600 12 1687 13214 27 _ _ (1897809 / 100000) (474453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174649600 :
    ThetaLowerSegment 174649600 174682368 (2182933466947 / 12500) (1091669563841 / 6250) := by
  exact
    packedTile16384 174649600 174682368 12 1710 13215 27 _ _ (474457 / 25000) (1897831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174682368 :
    ThetaLowerSegment 174682368 174715136 (1091669563841 / 6250) (8734993402903 / 50000) := by
  exact
    packedTile16384 174682368 174715136 12 1725 13216 27 _ _ (948923 / 50000) (1897849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174715136 :
    ThetaLowerSegment 174715136 174747904 (8734993402903 / 50000) (8736640749723 / 50000) := by
  exact
    packedTile16384 174715136 174747904 12 1736 13217 27 _ _ (379573 / 20000) (474467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174747904 :
    ThetaLowerSegment 174747904 174780672 (8736640749723 / 50000) (8738298551397 / 50000) := by
  exact
    packedTile16384 174747904 174780672 12 1747 13219 27 _ _ (474471 / 25000) (1897887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174780672 :
    ThetaLowerSegment 174780672 174813440 (8738298551397 / 50000) (3495963568837 / 20000) := by
  exact
    packedTile16384 174780672 174813440 12 1697 13220 27 _ _ (1897903 / 100000) (948953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174813440 :
    ThetaLowerSegment 174813440 174846208 (3495963568837 / 20000) (8741534491429 / 50000) := by
  exact
    packedTile16384 174813440 174846208 12 1713 13221 27 _ _ (1897921 / 100000) (474481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174846208 :
    ThetaLowerSegment 174846208 174878976 (8741534491429 / 50000) (8743193290989 / 50000) := by
  exact
    packedTile16384 174846208 174878976 12 1748 13222 27 _ _ (94897 / 5000) (1897943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174878976 :
    ThetaLowerSegment 174878976 174911744 (8743193290989 / 50000) (8744863494909 / 50000) := by
  exact
    packedTile16384 174878976 174911744 12 1760 13224 27 _ _ (1897959 / 100000) (948981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174911744 :
    ThetaLowerSegment 174911744 174944512 (8744863494909 / 50000) (874646633733 / 5000) := by
  exact
    packedTile16384 174911744 174944512 12 1689 13225 27 _ _ (948989 / 50000) (1897981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174944512 :
    ThetaLowerSegment 174944512 174977280 (874646633733 / 5000) (1093512445361 / 6250) := by
  exact
    packedTile16384 174944512 174977280 12 1721 13226 27 _ _ (474499 / 25000) (1897999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell174977280 :
    ThetaLowerSegment 174977280 175010048 (1093512445361 / 6250) (17499488385771 / 100000) := by
  exact
    packedTile16384 174977280 175010048 12 1733 13227 27 _ _ (379603 / 20000) (949009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175010048 :
    ThetaLowerSegment 175010048 175042816 (17499488385771 / 100000) (17502771984591 / 100000) := by
  exact
    packedTile16384 175010048 175042816 12 1730 13229 27 _ _ (949017 / 50000) (1898037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175042816 :
    ThetaLowerSegment 175042816 175075584 (17502771984591 / 100000) (8753028757167 / 50000) := by
  exact
    packedTile16384 175042816 175075584 12 1731 13230 27 _ _ (1898053 / 100000) (237257 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175075584 :
    ThetaLowerSegment 175075584 175108352 (8753028757167 / 50000) (875464781173 / 5000) := by
  exact
    packedTile16384 175075584 175108352 12 1706 13231 27 _ _ (1898071 / 100000) (949037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175108352 :
    ThetaLowerSegment 175108352 175141120 (875464781173 / 5000) (1751258880961 / 10000) := by
  exact
    packedTile16384 175108352 175141120 12 1735 13232 27 _ _ (189809 / 10000) (1898093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175141120 :
    ThetaLowerSegment 175141120 175173888 (1751258880961 / 10000) (8757922982327 / 50000) := by
  exact
    packedTile16384 175141120 175173888 12 1716 13234 27 _ _ (1898109 / 100000) (59316 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175173888 :
    ThetaLowerSegment 175173888 175206656 (8757922982327 / 50000) (17519127826237 / 100000) := by
  exact
    packedTile16384 175173888 175206656 12 1729 13235 27 _ _ (1898127 / 100000) (189813 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175206656 :
    ThetaLowerSegment 175206656 175239424 (17519127826237 / 100000) (17522459072467 / 100000) := by
  exact
    packedTile16384 175206656 175239424 12 1755 13236 27 _ _ (949073 / 50000) (1898149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175239424 :
    ThetaLowerSegment 175239424 175272192 (17522459072467 / 100000) (17525735305257 / 100000) := by
  exact
    packedTile16384 175239424 175272192 12 1726 13237 27 _ _ (379633 / 20000) (237271 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175272192 :
    ThetaLowerSegment 175272192 175304960 (17525735305257 / 100000) (3505827370197 / 20000) := by
  exact
    packedTile16384 175272192 175304960 12 1792 13239 27 _ _ (237273 / 12500) (1898187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175304960 :
    ThetaLowerSegment 175304960 175337728 (3505827370197 / 20000) (17532481482909 / 100000) := by
  exact
    packedTile16384 175304960 175337728 12 1762 13240 27 _ _ (949101 / 50000) (379641 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175337728 :
    ThetaLowerSegment 175337728 175370496 (17532481482909 / 100000) (1095984981911 / 6250) := by
  exact
    packedTile16384 175337728 175370496 12 1727 13241 27 _ _ (1898221 / 100000) (118639 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175370496 :
    ThetaLowerSegment 175370496 175403264 (1095984981911 / 6250) (1096188924071 / 6250) := by
  exact
    packedTile16384 175370496 175403264 12 1719 13242 27 _ _ (11864 / 625) (1898243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175403264 :
    ThetaLowerSegment 175403264 175436032 (1096188924071 / 6250) (4385586184159 / 25000) := by
  exact
    packedTile16384 175403264 175436032 12 1750 13243 27 _ _ (949129 / 50000) (1898261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175436032 :
    ThetaLowerSegment 175436032 175468800 (4385586184159 / 25000) (4386410036377 / 25000) := by
  exact
    packedTile16384 175436032 175468800 12 1736 13245 27 _ _ (1898277 / 100000) (47457 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175468800 :
    ThetaLowerSegment 175468800 175501568 (4386410036377 / 25000) (4387230574823 / 25000) := by
  exact
    packedTile16384 175468800 175501568 12 1729 13246 27 _ _ (237287 / 12500) (1898299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175501568 :
    ThetaLowerSegment 175501568 175534336 (4387230574823 / 25000) (4388046849843 / 25000) := by
  exact
    packedTile16384 175501568 175534336 12 1720 13247 27 _ _ (949157 / 50000) (1898317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175534336 :
    ThetaLowerSegment 175534336 175567104 (4388046849843 / 25000) (3511083292761 / 20000) := by
  exact
    packedTile16384 175534336 175567104 12 1701 13248 27 _ _ (1898333 / 100000) (59323 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175567104 :
    ThetaLowerSegment 175567104 175599872 (3511083292761 / 20000) (17558780343549 / 100000) := by
  exact
    packedTile16384 175567104 175599872 12 1772 13250 27 _ _ (118647 / 6250) (379671 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175599872 :
    ThetaLowerSegment 175599872 175632640 (17558780343549 / 100000) (17561956316559 / 100000) := by
  exact
    packedTile16384 175599872 175632640 12 1673 13251 27 _ _ (189837 / 10000) (1898373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175632640 :
    ThetaLowerSegment 175632640 175665408 (17561956316559 / 100000) (17565274700531 / 100000) := by
  exact
    packedTile16384 175632640 175665408 12 1748 13252 27 _ _ (1898389 / 100000) (237299 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175665408 :
    ThetaLowerSegment 175665408 175698176 (17565274700531 / 100000) (17568591219307 / 100000) := by
  exact
    packedTile16384 175665408 175698176 12 1747 13253 27 _ _ (237301 / 12500) (1898411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175698176 :
    ThetaLowerSegment 175698176 175730944 (17568591219307 / 100000) (17571772981283 / 100000) := by
  exact
    packedTile16384 175698176 175730944 12 1676 13255 27 _ _ (949213 / 50000) (1898429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175730944 :
    ThetaLowerSegment 175730944 175763712 (17571772981283 / 100000) (17575068681803 / 100000) := by
  exact
    packedTile16384 175730944 175763712 12 1736 13256 27 _ _ (379689 / 20000) (118653 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175763712 :
    ThetaLowerSegment 175763712 175796480 (17575068681803 / 100000) (17578259999787 / 100000) := by
  exact
    packedTile16384 175763712 175796480 12 1681 13257 27 _ _ (59327 / 3125) (1898467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175796480 :
    ThetaLowerSegment 175796480 175829248 (17578259999787 / 100000) (17581603226589 / 100000) := by
  exact
    packedTile16384 175796480 175829248 12 1761 13258 27 _ _ (949241 / 50000) (379697 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175829248 :
    ThetaLowerSegment 175829248 175862016 (17581603226589 / 100000) (17584925603339 / 100000) := by
  exact
    packedTile16384 175829248 175862016 12 1750 13260 27 _ _ (1898501 / 100000) (237313 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175862016 :
    ThetaLowerSegment 175862016 175894784 (17584925603339 / 100000) (17588139797699 / 100000) := by
  exact
    packedTile16384 175862016 175894784 12 1693 13261 27 _ _ (47463 / 2500) (1898523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175894784 :
    ThetaLowerSegment 175894784 175927552 (17588139797699 / 100000) (17591420471363 / 100000) := by
  exact
    packedTile16384 175894784 175927552 12 1728 13262 27 _ _ (949269 / 50000) (1898541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175927552 :
    ThetaLowerSegment 175927552 175960320 (17591420471363 / 100000) (4398670073433 / 25000) := by
  exact
    packedTile16384 175927552 175960320 12 1717 13263 27 _ _ (1898557 / 100000) (11866 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175960320 :
    ThetaLowerSegment 175960320 175993088 (4398670073433 / 25000) (17598000901407 / 100000) := by
  exact
    packedTile16384 175960320 175993088 12 1749 13265 27 _ _ (75943 / 4000) (949289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell175993088 :
    ThetaLowerSegment 175993088 176025856 (17598000901407 / 100000) (3520269244807 / 20000) := by
  exact
    packedTile16384 175993088 176025856 12 1762 13266 27 _ _ (949297 / 50000) (1898597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176025856 :
    ThetaLowerSegment 176025856 176058624 (3520269244807 / 20000) (17604604243943 / 100000) := by
  exact
    packedTile16384 176025856 176058624 12 1716 13267 27 _ _ (1898613 / 100000) (237327 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176058624 :
    ThetaLowerSegment 176058624 176091392 (17604604243943 / 100000) (1760786419337 / 10000) := by
  exact
    packedTile16384 176058624 176091392 12 1717 13268 27 _ _ (1898631 / 100000) (949317 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176091392 :
    ThetaLowerSegment 176091392 176124160 (1760786419337 / 10000) (110069644762 / 625) := by
  exact
    packedTile16384 176091392 176124160 12 1727 13269 27 _ _ (37973 / 2000) (1898653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176124160 :
    ThetaLowerSegment 176124160 176156928 (110069644762 / 625) (88071949421 / 500) := by
  exact
    packedTile16384 176124160 176156928 12 1710 13271 27 _ _ (474667 / 25000) (1898671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176156928 :
    ThetaLowerSegment 176156928 176189696 (88071949421 / 500) (17617668916649 / 100000) := by
  exact
    packedTile16384 176156928 176189696 12 1727 13272 27 _ _ (1898687 / 100000) (189869 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176189696 :
    ThetaLowerSegment 176189696 176222464 (17617668916649 / 100000) (17620913805203 / 100000) := by
  exact
    packedTile16384 176189696 176222464 12 1709 13273 27 _ _ (949353 / 50000) (1898709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176222464 :
    ThetaLowerSegment 176222464 176255232 (17620913805203 / 100000) (17624211888791 / 100000) := by
  exact
    packedTile16384 176222464 176255232 12 1737 13274 27 _ _ (474681 / 25000) (1898727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176255232 :
    ThetaLowerSegment 176255232 176288000 (17624211888791 / 100000) (352549288711 / 2000) := by
  exact
    packedTile16384 176255232 176288000 12 1713 13276 27 _ _ (1898743 / 100000) (949373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176288000 :
    ThetaLowerSegment 176288000 176320768 (352549288711 / 2000) (17630743595797 / 100000) := by
  exact
    packedTile16384 176288000 176320768 12 1727 13277 27 _ _ (1898761 / 100000) (474691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176320768 :
    ThetaLowerSegment 176320768 176353536 (17630743595797 / 100000) (17634000003497 / 100000) := by
  exact
    packedTile16384 176320768 176353536 12 1715 13278 27 _ _ (94939 / 5000) (1898783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176353536 :
    ThetaLowerSegment 176353536 176386304 (17634000003497 / 100000) (17637311508953 / 100000) := by
  exact
    packedTile16384 176353536 176386304 12 1744 13279 27 _ _ (1898799 / 100000) (949401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176386304 :
    ThetaLowerSegment 176386304 176419072 (17637311508953 / 100000) (17640630641069 / 100000) := by
  exact
    packedTile16384 176386304 176419072 12 1748 13281 27 _ _ (1898817 / 100000) (94941 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176419072 :
    ThetaLowerSegment 176419072 176451840 (17640630641069 / 100000) (17643896638989 / 100000) := by
  exact
    packedTile16384 176419072 176451840 12 1720 13282 27 _ _ (474709 / 25000) (1898839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176451840 :
    ThetaLowerSegment 176451840 176484608 (17643896638989 / 100000) (17647124690789 / 100000) := by
  exact
    packedTile16384 176451840 176484608 12 1700 13283 27 _ _ (949427 / 50000) (1898857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176484608 :
    ThetaLowerSegment 176484608 176517376 (17647124690789 / 100000) (17650405943333 / 100000) := by
  exact
    packedTile16384 176484608 176517376 12 1728 13284 27 _ _ (1898873 / 100000) (474719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176517376 :
    ThetaLowerSegment 176517376 176550144 (17650405943333 / 100000) (4413431775923 / 25000) := by
  exact
    packedTile16384 176517376 176550144 12 1749 13285 27 _ _ (1898891 / 100000) (949447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176550144 :
    ThetaLowerSegment 176550144 176582912 (4413431775923 / 25000) (4414252105043 / 25000) := by
  exact
    packedTile16384 176550144 176582912 12 1728 13287 27 _ _ (189891 / 10000) (1898913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176582912 :
    ThetaLowerSegment 176582912 176615680 (4414252105043 / 25000) (2207531473863 / 12500) := by
  exact
    packedTile16384 176582912 176615680 12 1708 13288 27 _ _ (1898929 / 100000) (474733 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176615680 :
    ThetaLowerSegment 176615680 176648448 (2207531473863 / 12500) (17663512282903 / 100000) := by
  exact
    packedTile16384 176615680 176648448 12 1717 13289 27 _ _ (1898947 / 100000) (37979 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176648448 :
    ThetaLowerSegment 176648448 176681216 (17663512282903 / 100000) (17666761413729 / 100000) := by
  exact
    packedTile16384 176648448 176681216 12 1711 13290 27 _ _ (949483 / 50000) (1898969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176681216 :
    ThetaLowerSegment 176681216 176713984 (17666761413729 / 100000) (17670039060113 / 100000) := by
  exact
    packedTile16384 176681216 176713984 12 1726 13292 27 _ _ (237373 / 12500) (1898987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176713984 :
    ThetaLowerSegment 176713984 176746752 (17670039060113 / 100000) (2209162456033 / 12500) := by
  exact
    packedTile16384 176713984 176746752 12 1717 13293 27 _ _ (1899003 / 100000) (949503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176746752 :
    ThetaLowerSegment 176746752 176779520 (2209162456033 / 12500) (8838300073381 / 50000) := by
  exact
    packedTile16384 176746752 176779520 12 1738 13294 27 _ _ (1899021 / 100000) (118689 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176779520 :
    ThetaLowerSegment 176779520 176812288 (8838300073381 / 50000) (8840015856021 / 50000) := by
  exact
    packedTile16384 176779520 176812288 12 1807 13295 27 _ _ (11869 / 625) (1899043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176812288 :
    ThetaLowerSegment 176812288 176845056 (8840015856021 / 50000) (8841656642133 / 50000) := by
  exact
    packedTile16384 176812288 176845056 12 1728 13297 27 _ _ (949529 / 50000) (1899061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176845056 :
    ThetaLowerSegment 176845056 176877824 (8841656642133 / 50000) (3537307203587 / 20000) := by
  exact
    packedTile16384 176845056 176877824 12 1697 13298 27 _ _ (1899077 / 100000) (47477 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176877824 :
    ThetaLowerSegment 176877824 176910592 (3537307203587 / 20000) (176897777731 / 1000) := by
  exact
    packedTile16384 176877824 176910592 12 1707 13299 27 _ _ (379819 / 20000) (949549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176910592 :
    ThetaLowerSegment 176910592 176943360 (176897777731 / 1000) (8846557258199 / 50000) := by
  exact
    packedTile16384 176910592 176943360 12 1757 13300 27 _ _ (949557 / 50000) (1899117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176943360 :
    ThetaLowerSegment 176943360 176976128 (8846557258199 / 50000) (17696394319089 / 100000) := by
  exact
    packedTile16384 176943360 176976128 12 1727 13302 27 _ _ (1899133 / 100000) (59348 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell176976128 :
    ThetaLowerSegment 176976128 177008896 (17696394319089 / 100000) (1769968174947 / 10000) := by
  exact
    packedTile16384 176976128 177008896 12 1731 13303 27 _ _ (1899151 / 100000) (949577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177008896 :
    ThetaLowerSegment 177008896 177041664 (1769968174947 / 10000) (1770295971689 / 10000) := by
  exact
    packedTile16384 177008896 177041664 12 1726 13304 27 _ _ (189917 / 10000) (1899173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177041664 :
    ThetaLowerSegment 177041664 177074432 (1770295971689 / 10000) (8853143547133 / 50000) := by
  exact
    packedTile16384 177041664 177074432 12 1752 13305 27 _ _ (474797 / 25000) (1899191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177074432 :
    ThetaLowerSegment 177074432 177107200 (8853143547133 / 50000) (8854792058809 / 50000) := by
  exact
    packedTile16384 177074432 177107200 12 1736 13306 27 _ _ (1899207 / 100000) (189921 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177107200 :
    ThetaLowerSegment 177107200 177139968 (8854792058809 / 50000) (17712886869893 / 100000) := by
  exact
    packedTile16384 177107200 177139968 12 1739 13308 27 _ _ (75969 / 4000) (474807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177139968 :
    ThetaLowerSegment 177139968 177172736 (17712886869893 / 100000) (17716182058233 / 100000) := by
  exact
    packedTile16384 177139968 177172736 12 1735 13309 27 _ _ (474811 / 25000) (1899247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177172736 :
    ThetaLowerSegment 177172736 177205504 (17716182058233 / 100000) (17719492471899 / 100000) := by
  exact
    packedTile16384 177172736 177205504 12 1743 13310 27 _ _ (949631 / 50000) (379853 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177205504 :
    ThetaLowerSegment 177205504 177238272 (17719492471899 / 100000) (17722690861103 / 100000) := by
  exact
    packedTile16384 177205504 177238272 12 1684 13311 27 _ _ (1899281 / 100000) (474821 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177238272 :
    ThetaLowerSegment 177238272 177271040 (17722690861103 / 100000) (17725923468001 / 100000) := by
  exact
    packedTile16384 177238272 177271040 12 1702 13313 27 _ _ (1899299 / 100000) (949651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177271040 :
    ThetaLowerSegment 177271040 177303808 (17725923468001 / 100000) (17729135214739 / 100000) := by
  exact
    packedTile16384 177271040 177303808 12 1691 13314 27 _ _ (949659 / 50000) (1899321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177303808 :
    ThetaLowerSegment 177303808 177336576 (17729135214739 / 100000) (17732483744107 / 100000) := by
  exact
    packedTile16384 177303808 177336576 12 1763 13315 27 _ _ (237417 / 12500) (1899339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177336576 :
    ThetaLowerSegment 177336576 177369344 (17732483744107 / 100000) (8867857273481 / 50000) := by
  exact
    packedTile16384 177336576 177369344 12 1701 13316 27 _ _ (379871 / 20000) (949679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177369344 :
    ThetaLowerSegment 177369344 177402112 (8867857273481 / 50000) (3547815667309 / 20000) := by
  exact
    packedTile16384 177369344 177402112 12 1771 13318 27 _ _ (1899373 / 100000) (118711 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177402112 :
    ThetaLowerSegment 177402112 177418496 (3547815667309 / 20000) (17740651032293 / 100000) := by
  exact
    packedTile16384 177402112 177418496 11 828 13319 27 _ _ (1899391 / 100000) (949697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177418496 :
    ThetaLowerSegment 177418496 177426688 (17740651032293 / 100000) (8870736736463 / 50000) := by
  exact
    packedTile16384 177418496 177426688 10 433 13319 27 _ _ (1899401 / 100000) (474851 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177426688 :
    ThetaLowerSegment 177426688 177430784 (8870736736463 / 50000) (17741904637861 / 100000) := by
  exact
    packedTile16384 177426688 177430784 9 227 13320 27 _ _ (379881 / 20000) (118713 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell177430784 :
    ThetaLowerSegment 177430784 177432832 (17741904637861 / 100000) (17742096478069 / 100000) := by
  exact
    packedTile16384 177430784 177432832 8 101 13320 27 _ _ (118713 / 6250) (1899411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_152170752_177432832 :
    ThetaLowerSegment 152170752 177432832 (15215211428653 / 100000) (17742096478069 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell152170752 cell152203520)
                      (ThetaLowerSegment.join cell152236288 cell152269056))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell152301824 cell152334592)
                      (ThetaLowerSegment.join cell152367360 cell152400128)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell152432896 cell152465664)
                      (ThetaLowerSegment.join cell152498432 cell152531200))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell152563968 cell152596736)
                      (ThetaLowerSegment.join cell152629504 cell152662272))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell152695040 cell152727808)
                      (ThetaLowerSegment.join cell152760576 cell152793344))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell152826112 cell152858880)
                      (ThetaLowerSegment.join cell152891648 cell152924416)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell152957184 cell152989952)
                      (ThetaLowerSegment.join cell153022720 cell153055488))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell153088256 cell153121024)
                      (ThetaLowerSegment.join cell153153792 cell153186560)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell153219328 cell153252096)
                      (ThetaLowerSegment.join cell153284864 cell153317632))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell153350400 cell153383168)
                      (ThetaLowerSegment.join cell153415936 cell153448704)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell153481472 cell153514240)
                      (ThetaLowerSegment.join cell153547008 cell153579776))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell153612544 cell153645312)
                      (ThetaLowerSegment.join cell153678080 cell153710848))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell153743616 cell153776384)
                      (ThetaLowerSegment.join cell153809152 cell153841920))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell153874688 cell153907456)
                      (ThetaLowerSegment.join cell153940224 cell153972992)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell154005760 cell154038528)
                      (ThetaLowerSegment.join cell154071296 cell154104064))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell154136832 cell154169600)
                      (ThetaLowerSegment.join cell154202368 cell154235136))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell154267904 cell154300672)
                      (ThetaLowerSegment.join cell154333440 cell154366208))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell154398976 cell154431744)
                      (ThetaLowerSegment.join cell154464512 cell154497280)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell154530048 cell154562816)
                      (ThetaLowerSegment.join cell154595584 cell154628352))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell154661120 cell154693888)
                      (ThetaLowerSegment.join cell154726656 cell154759424))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell154792192 cell154824960)
                      (ThetaLowerSegment.join cell154857728 cell154890496))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell154923264 cell154956032)
                      (ThetaLowerSegment.join cell154988800 cell155021568)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell155054336 cell155087104)
                      (ThetaLowerSegment.join cell155119872 cell155152640))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell155185408 cell155218176)
                      (ThetaLowerSegment.join cell155250944 cell155283712)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell155316480 cell155349248)
                      (ThetaLowerSegment.join cell155382016 cell155414784))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell155447552 cell155480320)
                      (ThetaLowerSegment.join cell155513088 cell155545856)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell155578624 cell155611392)
                      (ThetaLowerSegment.join cell155644160 cell155676928))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell155709696 cell155742464)
                      (ThetaLowerSegment.join cell155775232 cell155808000))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell155840768 cell155873536)
                      (ThetaLowerSegment.join cell155906304 cell155939072))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell155971840 cell156004608)
                      (ThetaLowerSegment.join cell156037376 cell156070144)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell156102912 cell156135680)
                      (ThetaLowerSegment.join cell156168448 cell156201216))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell156233984 cell156266752)
                      (ThetaLowerSegment.join cell156299520 cell156332288)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell156365056 cell156397824)
                      (ThetaLowerSegment.join cell156430592 cell156463360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell156496128 cell156528896)
                      (ThetaLowerSegment.join cell156561664 cell156594432)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell156627200 cell156659968)
                      (ThetaLowerSegment.join cell156692736 cell156725504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell156758272 cell156791040)
                      (ThetaLowerSegment.join cell156823808 cell156856576))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell156889344 cell156922112)
                      (ThetaLowerSegment.join cell156954880 cell156987648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell157020416 cell157053184)
                      (ThetaLowerSegment.join cell157085952 cell157118720)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell157151488 cell157184256)
                      (ThetaLowerSegment.join cell157217024 cell157249792))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell157282560 cell157315328)
                      (ThetaLowerSegment.join cell157348096 cell157380864)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell157413632 cell157446400)
                      (ThetaLowerSegment.join cell157479168 cell157511936))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell157544704 cell157577472)
                      (ThetaLowerSegment.join cell157610240 cell157643008)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell157675776 cell157708544)
                      (ThetaLowerSegment.join cell157741312 cell157774080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell157806848 cell157839616)
                      (ThetaLowerSegment.join cell157872384 cell157905152))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell157937920 cell157970688)
                      (ThetaLowerSegment.join cell158003456 cell158036224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell158068992 cell158101760)
                      (ThetaLowerSegment.join cell158134528 cell158167296)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell158200064 cell158232832)
                      (ThetaLowerSegment.join cell158265600 cell158298368))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell158331136 cell158363904)
                      (ThetaLowerSegment.join cell158396672 cell158429440))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell158462208 cell158494976)
                      (ThetaLowerSegment.join cell158527744 cell158560512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell158593280 cell158626048)
                      (ThetaLowerSegment.join cell158658816 cell158691584)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell158724352 cell158757120)
                      (ThetaLowerSegment.join cell158789888 cell158822656))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell158855424 cell158888192)
                      (ThetaLowerSegment.join cell158920960 cell158953728))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell158986496 cell159019264)
                      (ThetaLowerSegment.join cell159052032 cell159084800))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell159117568 cell159150336)
                      (ThetaLowerSegment.join cell159183104 cell159215872)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell159248640 cell159281408)
                      (ThetaLowerSegment.join cell159314176 cell159346944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell159379712 cell159412480)
                      (ThetaLowerSegment.join cell159445248 cell159478016)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell159510784 cell159543552)
                      (ThetaLowerSegment.join cell159576320 cell159609088))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell159641856 cell159674624)
                      (ThetaLowerSegment.join cell159707392 cell159740160)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell159772928 cell159805696)
                      (ThetaLowerSegment.join cell159838464 cell159871232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell159904000 cell159936768)
                      (ThetaLowerSegment.join cell159969536 cell160002304))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell160035072 cell160067840)
                      (ThetaLowerSegment.join cell160100608 cell160133376))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell160166144 cell160198912)
                      (ThetaLowerSegment.join cell160231680 cell160264448)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell160297216 cell160329984)
                      (ThetaLowerSegment.join cell160362752 cell160395520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell160428288 cell160461056)
                      (ThetaLowerSegment.join cell160493824 cell160526592))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell160559360 cell160592128)
                      (ThetaLowerSegment.join cell160624896 cell160657664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell160690432 cell160723200)
                      (ThetaLowerSegment.join cell160755968 cell160788736)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell160821504 cell160854272)
                      (ThetaLowerSegment.join cell160887040 cell160919808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell160952576 cell160985344)
                      (ThetaLowerSegment.join cell161018112 cell161050880))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell161083648 cell161116416)
                      (ThetaLowerSegment.join cell161149184 cell161181952))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell161214720 cell161247488)
                      (ThetaLowerSegment.join cell161280256 cell161313024)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell161345792 cell161378560)
                      (ThetaLowerSegment.join cell161411328 cell161444096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell161476864 cell161509632)
                      (ThetaLowerSegment.join cell161542400 cell161575168)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell161607936 cell161640704)
                      (ThetaLowerSegment.join cell161673472 cell161706240))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell161739008 cell161771776)
                      (ThetaLowerSegment.join cell161804544 cell161837312)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell161870080 cell161902848)
                      (ThetaLowerSegment.join cell161935616 cell161968384))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell162001152 cell162033920)
                      (ThetaLowerSegment.join cell162066688 cell162099456))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell162132224 cell162164992)
                      (ThetaLowerSegment.join cell162197760 cell162230528))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell162263296 cell162296064)
                      (ThetaLowerSegment.join cell162328832 cell162361600)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell162394368 cell162427136)
                      (ThetaLowerSegment.join cell162459904 cell162492672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell162525440 cell162558208)
                      (ThetaLowerSegment.join cell162590976 cell162623744))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell162656512 cell162689280)
                      (ThetaLowerSegment.join cell162722048 cell162754816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell162787584 cell162820352)
                      (ThetaLowerSegment.join cell162853120 cell162885888)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell162918656 cell162951424)
                      (ThetaLowerSegment.join cell162984192 cell163016960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell163049728 cell163082496)
                      (ThetaLowerSegment.join cell163115264 cell163148032))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell163180800 cell163213568)
                      (ThetaLowerSegment.join cell163246336 cell163279104))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell163311872 cell163344640)
                      (ThetaLowerSegment.join cell163377408 cell163410176)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell163442944 cell163475712)
                      (ThetaLowerSegment.join cell163508480 cell163541248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell163574016 cell163606784)
                      (ThetaLowerSegment.join cell163639552 cell163672320)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell163705088 cell163737856)
                      (ThetaLowerSegment.join cell163770624 cell163803392))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell163836160 cell163868928)
                      (ThetaLowerSegment.join cell163901696 cell163934464)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell163967232 cell164000000)
                      (ThetaLowerSegment.join cell164032768 cell164065536))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell164098304 cell164131072)
                      (ThetaLowerSegment.join cell164163840 cell164196608))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell164229376 cell164262144)
                      (ThetaLowerSegment.join cell164294912 cell164327680))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell164360448 cell164393216)
                      (ThetaLowerSegment.join cell164425984 cell164458752)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell164491520 cell164524288)
                      (ThetaLowerSegment.join cell164557056 cell164589824))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell164622592 cell164655360)
                      (ThetaLowerSegment.join cell164688128 cell164720896)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell164753664 cell164786432)
                      (ThetaLowerSegment.join cell164819200 cell164851968))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell164884736 cell164917504)
                      (ThetaLowerSegment.join cell164950272 cell164983040)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell165015808 cell165048576)
                      (ThetaLowerSegment.join cell165081344 cell165114112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell165146880 cell165179648)
                      (ThetaLowerSegment.join cell165212416 cell165245184))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell165277952 cell165310720)
                      (ThetaLowerSegment.join cell165343488 cell165376256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell165409024 cell165441792)
                      (ThetaLowerSegment.join cell165474560 cell165507328)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell165540096 cell165572864)
                      (ThetaLowerSegment.join cell165605632 cell165638400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell165671168 cell165703936)
                      (ThetaLowerSegment.join cell165736704 cell165769472)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell165802240 cell165835008)
                      (ThetaLowerSegment.join cell165867776 cell165900544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell165933312 cell165966080)
                      (ThetaLowerSegment.join cell165998848 cell166031616)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell166064384 cell166097152)
                      (ThetaLowerSegment.join cell166129920 cell166162688))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell166195456 cell166228224)
                      (ThetaLowerSegment.join cell166260992 cell166293760))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell166326528 cell166359296)
                      (ThetaLowerSegment.join cell166392064 cell166424832))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell166457600 cell166490368)
                      (ThetaLowerSegment.join cell166523136 cell166555904)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell166588672 cell166621440)
                      (ThetaLowerSegment.join cell166654208 cell166686976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell166719744 cell166752512)
                      (ThetaLowerSegment.join cell166785280 cell166818048))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell166850816 cell166883584)
                      (ThetaLowerSegment.join cell166916352 cell166949120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell166981888 cell167014656)
                      (ThetaLowerSegment.join cell167047424 cell167080192)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell167112960 cell167145728)
                      (ThetaLowerSegment.join cell167178496 cell167211264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell167244032 cell167276800)
                      (ThetaLowerSegment.join cell167309568 cell167342336))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell167375104 cell167407872)
                      (ThetaLowerSegment.join cell167440640 cell167473408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell167506176 cell167538944)
                      (ThetaLowerSegment.join cell167571712 cell167604480)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell167637248 cell167670016)
                      (ThetaLowerSegment.join cell167702784 cell167735552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell167768320 cell167801088)
                      (ThetaLowerSegment.join cell167833856 cell167866624)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell167899392 cell167932160)
                      (ThetaLowerSegment.join cell167964928 cell167997696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell168030464 cell168063232)
                      (ThetaLowerSegment.join cell168096000 cell168128768)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell168161536 cell168194304)
                      (ThetaLowerSegment.join cell168227072 cell168259840))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell168292608 cell168325376)
                      (ThetaLowerSegment.join cell168358144 cell168390912))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell168423680 cell168456448)
                      (ThetaLowerSegment.join cell168489216 cell168521984))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell168554752 cell168587520)
                      (ThetaLowerSegment.join cell168620288 cell168653056)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell168685824 cell168718592)
                      (ThetaLowerSegment.join cell168751360 cell168784128))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell168816896 cell168849664)
                      (ThetaLowerSegment.join cell168882432 cell168915200)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell168947968 cell168980736)
                      (ThetaLowerSegment.join cell169013504 cell169046272))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell169079040 cell169111808)
                      (ThetaLowerSegment.join cell169144576 cell169177344)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell169210112 cell169242880)
                      (ThetaLowerSegment.join cell169275648 cell169308416))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell169341184 cell169373952)
                      (ThetaLowerSegment.join cell169406720 cell169439488))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell169472256 cell169505024)
                      (ThetaLowerSegment.join cell169537792 cell169570560))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell169603328 cell169636096)
                      (ThetaLowerSegment.join cell169668864 cell169701632)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell169734400 cell169767168)
                      (ThetaLowerSegment.join cell169799936 cell169832704))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell169865472 cell169898240)
                      (ThetaLowerSegment.join cell169931008 cell169963776)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell169996544 cell170029312)
                      (ThetaLowerSegment.join cell170062080 cell170094848))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell170127616 cell170160384)
                      (ThetaLowerSegment.join cell170193152 cell170225920)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell170258688 cell170291456)
                      (ThetaLowerSegment.join cell170324224 cell170356992))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell170389760 cell170422528)
                      (ThetaLowerSegment.join cell170455296 cell170488064))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell170520832 cell170553600)
                      (ThetaLowerSegment.join cell170586368 cell170619136))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell170651904 cell170684672)
                      (ThetaLowerSegment.join cell170717440 cell170750208)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell170782976 cell170815744)
                      (ThetaLowerSegment.join cell170848512 cell170881280))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell170914048 cell170946816)
                      (ThetaLowerSegment.join cell170979584 cell171012352))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell171045120 cell171077888)
                      (ThetaLowerSegment.join cell171110656 cell171143424))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell171176192 cell171208960)
                      (ThetaLowerSegment.join cell171241728 cell171274496)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell171307264 cell171340032)
                      (ThetaLowerSegment.join cell171372800 cell171405568))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell171438336 cell171471104)
                      (ThetaLowerSegment.join cell171503872 cell171536640))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell171569408 cell171602176)
                      (ThetaLowerSegment.join cell171634944 cell171667712))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell171700480 cell171733248)
                      (ThetaLowerSegment.join cell171766016 cell171798784)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell171831552 cell171864320)
                      (ThetaLowerSegment.join cell171897088 cell171929856))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell171962624 cell171995392)
                      (ThetaLowerSegment.join cell172028160 cell172060928)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell172093696 cell172126464)
                      (ThetaLowerSegment.join cell172159232 cell172192000))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell172224768 cell172257536)
                      (ThetaLowerSegment.join cell172290304 cell172323072)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell172355840 cell172388608)
                      (ThetaLowerSegment.join cell172421376 cell172454144))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell172486912 cell172519680)
                      (ThetaLowerSegment.join cell172552448 cell172585216))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell172617984 cell172650752)
                      (ThetaLowerSegment.join cell172683520 cell172716288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell172749056 cell172781824)
                      (ThetaLowerSegment.join cell172814592 cell172847360)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell172880128 cell172912896)
                      (ThetaLowerSegment.join cell172945664 cell172978432))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell173011200 cell173043968)
                      (ThetaLowerSegment.join cell173076736 cell173109504)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell173142272 cell173175040)
                      (ThetaLowerSegment.join cell173207808 cell173240576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell173273344 cell173306112)
                      (ThetaLowerSegment.join cell173338880 cell173371648)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell173404416 cell173437184)
                      (ThetaLowerSegment.join cell173469952 cell173502720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell173535488 cell173568256)
                      (ThetaLowerSegment.join cell173601024 cell173633792))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell173666560 cell173699328)
                      (ThetaLowerSegment.join cell173732096 cell173764864))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell173797632 cell173830400)
                      (ThetaLowerSegment.join cell173863168 cell173895936)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell173928704 cell173961472)
                      (ThetaLowerSegment.join cell173994240 cell174027008))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell174059776 cell174092544)
                      (ThetaLowerSegment.join cell174125312 cell174158080)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell174190848 cell174223616)
                      (ThetaLowerSegment.join cell174256384 cell174289152))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell174321920 cell174354688)
                      (ThetaLowerSegment.join cell174387456 cell174420224)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell174452992 cell174485760)
                      (ThetaLowerSegment.join cell174518528 cell174551296))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell174584064 cell174616832)
                      (ThetaLowerSegment.join cell174649600 cell174682368))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell174715136 cell174747904)
                      (ThetaLowerSegment.join cell174780672 cell174813440))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell174846208 cell174878976)
                      (ThetaLowerSegment.join cell174911744 cell174944512)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell174977280 cell175010048)
                      (ThetaLowerSegment.join cell175042816 cell175075584))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell175108352 cell175141120)
                      (ThetaLowerSegment.join cell175173888 cell175206656))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell175239424 cell175272192)
                      (ThetaLowerSegment.join cell175304960 cell175337728))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell175370496 cell175403264)
                      (ThetaLowerSegment.join cell175436032 cell175468800)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell175501568 cell175534336)
                      (ThetaLowerSegment.join cell175567104 cell175599872))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell175632640 cell175665408)
                      (ThetaLowerSegment.join cell175698176 cell175730944))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell175763712 cell175796480)
                      (ThetaLowerSegment.join cell175829248 cell175862016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell175894784 cell175927552)
                      (ThetaLowerSegment.join cell175960320 cell175993088)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell176025856 cell176058624)
                      (ThetaLowerSegment.join cell176091392 cell176124160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell176156928 cell176189696)
                      (ThetaLowerSegment.join cell176222464 cell176255232)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell176288000 cell176320768)
                      (ThetaLowerSegment.join cell176353536 cell176386304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell176419072 cell176451840)
                      (ThetaLowerSegment.join cell176484608 cell176517376)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell176550144 cell176582912)
                      (ThetaLowerSegment.join cell176615680 cell176648448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell176681216 cell176713984)
                      (ThetaLowerSegment.join cell176746752 cell176779520))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell176812288 cell176845056)
                      (ThetaLowerSegment.join cell176877824 cell176910592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell176943360 cell176976128)
                      (ThetaLowerSegment.join cell177008896 cell177041664)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell177074432 cell177107200)
                      (ThetaLowerSegment.join cell177139968 cell177172736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell177205504 cell177238272)
                      (ThetaLowerSegment.join cell177271040 cell177303808))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join (ThetaLowerSegment.join cell177336576 cell177369344)
            (ThetaLowerSegment.join cell177402112 cell177418496))
          (ThetaLowerSegment.join cell177426688 cell177430784))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
