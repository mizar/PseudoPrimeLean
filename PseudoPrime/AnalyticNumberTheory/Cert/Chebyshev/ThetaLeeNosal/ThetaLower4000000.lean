/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Direct theta estimate up to 4000000 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private def base : ℕ :=
  let n : ℕ := 0x134c43df05c1b2271
  let n := (n <<< 240) + 0xbb1d3eacca431a87bdfd6193b3da20584feed2db5d79762955a76c03d726
  let n := (n <<< 240) + 0xdefb75b0ed5b77545c660545973c5eeac854abcc980fd38cfa87d63d24bc
  let n := (n <<< 240) + 0xa0ca6dc5d144ec32741caee69d8c17bda126c3606f4f54110f5aa8afb07f
  let n := (n <<< 240) + 0x0800715ba8103dcbd38a1efdbc3b8eded49fba5e348c5d3699ab5627c656
  let n := (n <<< 240) + 0xfc3e6ff6fce67b917dae2817d23c4e8c2ad94a68821db300d37a2b4742c2
  let n := (n <<< 240) + 0x220df58c067ac037d73f4e78db5e64a2ebe82de8cd63ccc1694ce7b7c422
  let n := (n <<< 240) + 0x9d406f1bb4005cca805859f0a6fadba86f6cbcdb91b7c6b4421cf2da4d9d
  let n := (n <<< 240) + 0xa334d1edc07a110535632b8b939741024f19e691b1c7f767ed656a1e4397
  let n := (n <<< 240) + 0xe8ace81d8dbcc455b7924251d2ea670b64e6624203372af08abde2a694dd
  let n := (n <<< 240) + 0x1f941882f4a724253b92024f3978f17990d6e9f22c6e98d3b822e5ef0b5b
  let n := (n <<< 240) + 0x260254b9538bd1ddc15eb80183d041c1df7744a006ae549814c71910c23a
  let n := (n <<< 240) + 0xc3472b608810c7b6f1f3d9ca2d55ae26b06e46c2249d8b4e4fe67dbe6800
  n

private theorem covers (m : ℕ) (hm : 2 ≤ m) (hb : m ≤ 2048) : m ∣ base := by
  have h : divisorBase 11 1 = base := by decide +kernel
  rw [← h]
  exact dvd_divisorBase 11 1 m ((by decide : 1 ≤ 2).trans hm) (Nat.lt_succ_of_le hb)

private theorem tile (a b t d k r j : ℕ) (e f q u : ℚ) (ha : 1000000 ≤ a)
    (hb : b < (2048 + 1) * (2048 + 1)) (he : a + 2 ^ (t + d) = b)
    (hc : tiledPrimeCount base 200560490130 t d a = k) (hs : r ^ 2 ≤ a)
    (hl : PseudoPrime.Analysis.rationalLogIntervalCheck a j 20 q u = true) (hf : f ≤ e + k * q)
    (hw : (b : ℚ) ≤ e + 5 * r) : ThetaLowerSegment a b e f := by
  apply theta_segment_of_count covers a b t d k 200560490130 r e f q ha hb he hc hs _ hf hw
  simpa only [Rat.cast_natCast] using (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1

private theorem cell2000000 :
    ThetaLowerSegment 2000000 2004096 (39958899001 / 20000) (200203638653 / 100000) := by
  exact
    tile 2000000 2004096 7 5 282 1414 21 _ _ (90679 / 6250) (1450867 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2004096 :
    ThetaLowerSegment 2004096 2008192 (200203638653 / 100000) (25078963001 / 12500) := by
  exact
    tile 2004096 2008192 7 5 295 1415 21 _ _ (1451069 / 100000) (45346 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2008192 :
    ThetaLowerSegment 2008192 2012288 (25078963001 / 12500) (100517578951 / 50000) := by
  exact
    tile 2008192 2012288 7 5 278 1417 21 _ _ (1451273 / 100000) (362819 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2012288 :
    ThetaLowerSegment 2012288 2016384 (100517578951 / 50000) (201466246571 / 100000) := by
  exact
    tile 2012288 2016384 7 5 297 1418 21 _ _ (1451477 / 100000) (36287 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2016384 :
    ThetaLowerSegment 2016384 2020480 (201466246571 / 100000) (201866910251 / 100000) := by
  exact
    tile 2016384 2020480 7 5 276 1419 21 _ _ (9073 / 625) (1451683 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2020480 :
    ThetaLowerSegment 2020480 2024576 (201866910251 / 100000) (202282148789 / 100000) := by
  exact
    tile 2020480 2024576 7 5 286 1421 21 _ _ (1451883 / 100000) (725943 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2024576 :
    ThetaLowerSegment 2024576 2028672 (202282148789 / 100000) (202688732869 / 100000) := by
  exact
    tile 2024576 2028672 7 5 280 1422 21 _ _ (726043 / 50000) (1452089 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2028672 :
    ThetaLowerSegment 2028672 2032768 (202688732869 / 100000) (203099730373 / 100000) := by
  exact
    tile 2028672 2032768 7 5 283 1424 21 _ _ (45384 / 3125) (1452291 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2032768 :
    ThetaLowerSegment 2032768 2036864 (203099730373 / 100000) (101759749847 / 50000) := by
  exact
    tile 2032768 2036864 7 5 289 1425 21 _ _ (1452489 / 100000) (363123 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2036864 :
    ThetaLowerSegment 2036864 2040960 (101759749847 / 50000) (203921895101 / 100000) := by
  exact
    tile 2036864 2040960 7 5 277 1427 21 _ _ (1452691 / 100000) (726347 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2040960 :
    ThetaLowerSegment 2040960 2045056 (203921895101 / 100000) (204333063537 / 100000) := by
  exact
    tile 2040960 2045056 7 5 283 1428 21 _ _ (363223 / 25000) (290579 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2045056 :
    ThetaLowerSegment 2045056 2049152 (204333063537 / 100000) (40944789057 / 20000) := by
  exact
    tile 2045056 2049152 7 5 269 1430 21 _ _ (363273 / 25000) (290619 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2049152 :
    ThetaLowerSegment 2049152 2053248 (40944789057 / 20000) (41024720117 / 20000) := by
  exact
    tile 2049152 2053248 7 5 275 1431 21 _ _ (363323 / 25000) (290659 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2053248 :
    ThetaLowerSegment 2053248 2057344 (41024720117 / 20000) (205532031837 / 100000) := by
  exact
    tile 2053248 2057344 7 5 281 1432 21 _ _ (363373 / 25000) (290699 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2057344 :
    ThetaLowerSegment 2057344 2061440 (205532031837 / 100000) (205956509609 / 100000) := by
  exact
    tile 2057344 2061440 7 5 292 1434 21 _ _ (1453691 / 100000) (726847 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2061440 :
    ThetaLowerSegment 2061440 2065536 (205956509609 / 100000) (206367960479 / 100000) := by
  exact
    tile 2061440 2065536 7 5 283 1435 21 _ _ (145389 / 10000) (1453893 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2065536 :
    ThetaLowerSegment 2065536 2069632 (206367960479 / 100000) (206775105399 / 100000) := by
  exact
    tile 2065536 2069632 7 5 280 1437 21 _ _ (1454089 / 100000) (363523 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2069632 :
    ThetaLowerSegment 2069632 2073728 (206775105399 / 100000) (207188122907 / 100000) := by
  exact
    tile 2069632 2073728 7 5 284 1438 21 _ _ (1454287 / 100000) (145429 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2073728 :
    ThetaLowerSegment 2073728 2077824 (207188122907 / 100000) (207570652199 / 100000) := by
  exact
    tile 2073728 2077824 7 5 263 1440 21 _ _ (363621 / 25000) (1454487 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2077824 :
    ThetaLowerSegment 2077824 2081920 (207570652199 / 100000) (207986691251 / 100000) := by
  exact
    tile 2077824 2081920 7 5 286 1441 21 _ _ (727341 / 50000) (290937 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2081920 :
    ThetaLowerSegment 2081920 2086016 (207986691251 / 100000) (208391147613 / 100000) := by
  exact
    tile 2081920 2086016 7 5 278 1442 21 _ _ (1454879 / 100000) (727441 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2086016 :
    ThetaLowerSegment 2086016 2090112 (208391147613 / 100000) (104407287219 / 50000) := by
  exact
    tile 2086016 2090112 7 5 291 1444 21 _ _ (58203 / 4000) (727539 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2090112 :
    ThetaLowerSegment 2090112 2094208 (104407287219 / 50000) (6538098118 / 3125) := by
  exact
    tile 2090112 2094208 7 5 278 1445 21 _ _ (1455271 / 100000) (727637 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2094208 :
    ThetaLowerSegment 2094208 2098304 (6538098118 / 3125) (209613571333 / 100000) := by
  exact
    tile 2094208 2098304 7 5 271 1447 21 _ _ (1455467 / 100000) (145547 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2098304 :
    ThetaLowerSegment 2098304 2102400 (209613571333 / 100000) (210028435003 / 100000) := by
  exact
    tile 2098304 2102400 7 5 285 1448 21 _ _ (727831 / 50000) (291133 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2102400 :
    ThetaLowerSegment 2102400 2106496 (210028435003 / 100000) (210455001397 / 100000) := by
  exact
    tile 2102400 2106496 7 5 293 1449 21 _ _ (727929 / 50000) (1455861 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2106496 :
    ThetaLowerSegment 2106496 2110592 (210455001397 / 100000) (42172247981 / 20000) := by
  exact
    tile 2106496 2110592 7 5 279 1451 21 _ _ (364013 / 25000) (291211 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2110592 :
    ThetaLowerSegment 2110592 2114688 (42172247981 / 20000) (8450177053 / 4000) := by
  exact
    tile 2110592 2114688 7 5 270 1452 21 _ _ (728123 / 50000) (1456249 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2114688 :
    ThetaLowerSegment 2114688 2118784 (8450177053 / 4000) (42336523937 / 20000) := by
  exact
    tile 2114688 2118784 7 5 294 1454 21 _ _ (36411 / 2500) (1456443 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2118784 :
    ThetaLowerSegment 2118784 2122880 (42336523937 / 20000) (212081737401 / 100000) := by
  exact
    tile 2118784 2122880 7 5 274 1455 21 _ _ (728317 / 50000) (1456637 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2122880 :
    ThetaLowerSegment 2122880 2126976 (212081737401 / 100000) (106247009721 / 50000) := by
  exact
    tile 2122880 2126976 7 5 283 1457 21 _ _ (1456827 / 100000) (145683 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2126976 :
    ThetaLowerSegment 2126976 2131072 (106247009721 / 50000) (106450992521 / 50000) := by
  exact
    tile 2126976 2131072 7 5 280 1458 21 _ _ (72851 / 5000) (1457023 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2131072 :
    ThetaLowerSegment 2131072 2135168 (106450992521 / 50000) (106649901959 / 50000) := by
  exact
    tile 2131072 2135168 7 5 273 1459 21 _ _ (364303 / 25000) (291443 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2135168 :
    ThetaLowerSegment 2135168 2139264 (106649901959 / 50000) (106858310731 / 50000) := by
  exact
    tile 2135168 2139264 7 5 286 1461 21 _ _ (364351 / 25000) (1457407 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2139264 :
    ThetaLowerSegment 2139264 2143360 (106858310731 / 50000) (107066018161 / 50000) := by
  exact
    tile 2139264 2143360 7 5 285 1462 21 _ _ (364399 / 25000) (1457599 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2143360 :
    ThetaLowerSegment 2143360 2147456 (107066018161 / 50000) (214556252339 / 100000) := by
  exact
    tile 2143360 2147456 7 5 291 1464 21 _ _ (1457787 / 100000) (145779 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2147456 :
    ThetaLowerSegment 2147456 2151552 (214556252339 / 100000) (214955738311 / 100000) := by
  exact
    tile 2147456 2151552 7 5 274 1465 21 _ _ (728989 / 50000) (1457981 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2151552 :
    ThetaLowerSegment 2151552 2155648 (214955738311 / 100000) (43074554929 / 20000) := by
  exact
    tile 2151552 2155648 7 5 286 1466 21 _ _ (1458169 / 100000) (364543 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2155648 :
    ThetaLowerSegment 2155648 2159744 (43074554929 / 20000) (43162056469 / 20000) := by
  exact
    tile 2155648 2159744 7 5 300 1468 21 _ _ (1458359 / 100000) (729181 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2159744 :
    ThetaLowerSegment 2159744 2163840 (43162056469 / 20000) (108110067307 / 50000) := by
  exact
    tile 2159744 2163840 7 5 281 1469 21 _ _ (1458549 / 100000) (182319 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2163840 :
    ThetaLowerSegment 2163840 2167936 (108110067307 / 50000) (108298244509 / 50000) := by
  exact
    tile 2163840 2167936 7 5 258 1470 21 _ _ (729369 / 50000) (1458741 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2167936 :
    ThetaLowerSegment 2167936 2172032 (108298244509 / 50000) (108505412143 / 50000) := by
  exact
    tile 2167936 2172032 7 5 284 1472 21 _ _ (1458927 / 100000) (145893 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2172032 :
    ThetaLowerSegment 2172032 2176128 (108505412143 / 50000) (108710417941 / 50000) := by
  exact
    tile 2172032 2176128 7 5 281 1473 21 _ _ (364779 / 25000) (1459119 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2176128 :
    ThetaLowerSegment 2176128 2180224 (108710417941 / 50000) (4356939053 / 2000) := by
  exact
    tile 2176128 2180224 7 5 292 1475 21 _ _ (182413 / 12500) (1459307 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2180224 :
    ThetaLowerSegment 2180224 2184320 (4356939053 / 2000) (109119777999 / 50000) := by
  exact
    tile 2180224 2184320 7 5 269 1476 21 _ _ (364873 / 25000) (291899 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2184320 :
    ThetaLowerSegment 2184320 2188416 (109119777999 / 50000) (109324863039 / 50000) := by
  exact
    tile 2184320 2188416 7 5 281 1477 21 _ _ (9123 / 625) (1459683 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2188416 :
    ThetaLowerSegment 2188416 2192512 (109324863039 / 50000) (13690973069 / 6250) := by
  exact
    tile 2188416 2192512 7 5 278 1479 21 _ _ (1459867 / 100000) (145987 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2192512 :
    ThetaLowerSegment 2192512 2196608 (13690973069 / 6250) (109735842247 / 50000) := by
  exact
    tile 2192512 2196608 7 5 285 1480 21 _ _ (730027 / 50000) (1460057 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2196608 :
    ThetaLowerSegment 2196608 2200704 (109735842247 / 50000) (21984550619 / 10000) := by
  exact
    tile 2196608 2200704 7 5 256 1482 21 _ _ (1460241 / 100000) (365061 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2200704 :
    ThetaLowerSegment 2200704 2204800 (21984550619 / 10000) (220267569593 / 100000) := by
  exact
    tile 2200704 2204800 7 5 289 1483 21 _ _ (1460427 / 100000) (146043 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2204800 :
    ThetaLowerSegment 2204800 2208896 (220267569593 / 100000) (220685304911 / 100000) := by
  exact
    tile 2204800 2208896 7 5 286 1484 21 _ _ (1460613 / 100000) (182577 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2208896 :
    ThetaLowerSegment 2208896 2212992 (220685304911 / 100000) (221106015023 / 100000) := by
  exact
    tile 2208896 2212992 7 5 288 1486 21 _ _ (1460799 / 100000) (730401 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2212992 :
    ThetaLowerSegment 2212992 2217088 (221106015023 / 100000) (221494636767 / 100000) := by
  exact
    tile 2212992 2217088 7 5 266 1487 21 _ _ (182623 / 12500) (1460987 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2217088 :
    ThetaLowerSegment 2217088 2221184 (221494636767 / 100000) (221874540707 / 100000) := by
  exact
    tile 2217088 2221184 7 5 260 1488 21 _ _ (1461169 / 100000) (365293 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2221184 :
    ThetaLowerSegment 2221184 2225280 (221874540707 / 100000) (222292487951 / 100000) := by
  exact
    tile 2221184 2225280 7 5 286 1490 21 _ _ (730677 / 50000) (1461357 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2225280 :
    ThetaLowerSegment 2225280 2229376 (222292487951 / 100000) (222716333971 / 100000) := by
  exact
    tile 2225280 2229376 7 5 290 1491 21 _ _ (730769 / 50000) (1461541 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2229376 :
    ThetaLowerSegment 2229376 2233472 (222716333971 / 100000) (223118307521 / 100000) := by
  exact
    tile 2229376 2233472 7 5 275 1493 21 _ _ (730861 / 50000) (58469 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2233472 :
    ThetaLowerSegment 2233472 2237568 (223118307521 / 100000) (27943696187 / 12500) := by
  exact
    tile 2233472 2237568 7 5 295 1494 21 _ _ (292381 / 20000) (365477 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2237568 :
    ThetaLowerSegment 2237568 2241664 (27943696187 / 12500) (27993407213 / 12500) := by
  exact
    tile 2237568 2241664 7 5 272 1495 21 _ _ (1462089 / 100000) (365523 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2241664 :
    ThetaLowerSegment 2241664 2245760 (27993407213 / 12500) (112176884521 / 50000) := by
  exact
    tile 2241664 2245760 7 5 278 1497 21 _ _ (1462271 / 100000) (731137 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2245760 :
    ThetaLowerSegment 2245760 2249856 (112176884521 / 50000) (56188985973 / 25000) := by
  exact
    tile 2245760 2249856 7 5 275 1498 21 _ _ (731227 / 50000) (1462457 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2249856 :
    ThetaLowerSegment 2249856 2253952 (56188985973 / 25000) (56289176539 / 25000) := by
  exact
    tile 2249856 2253952 7 5 274 1499 21 _ _ (365659 / 25000) (1462639 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2253952 :
    ThetaLowerSegment 2253952 2258048 (56289176539 / 25000) (56397425071 / 25000) := by
  exact
    tile 2253952 2258048 7 5 296 1501 21 _ _ (731409 / 50000) (1462821 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2258048 :
    ThetaLowerSegment 2258048 2262144 (56397425071 / 25000) (56500932321 / 25000) := by
  exact
    tile 2258048 2262144 7 5 283 1502 21 _ _ (1463 / 100) (1463003 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2262144 :
    ThetaLowerSegment 2262144 2266240 (56500932321 / 25000) (226417809507 / 100000) := by
  exact
    tile 2262144 2266240 7 5 283 1504 21 _ _ (1463181 / 100000) (91449 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2266240 :
    ThetaLowerSegment 2266240 2270336 (226417809507 / 100000) (226846574573 / 100000) := by
  exact
    tile 2266240 2270336 7 5 293 1505 21 _ _ (731681 / 50000) (292673 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2270336 :
    ThetaLowerSegment 2270336 2274432 (226846574573 / 100000) (227278319463 / 100000) := by
  exact
    tile 2270336 2274432 7 5 295 1506 21 _ _ (731771 / 50000) (292709 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2274432 :
    ThetaLowerSegment 2274432 2278528 (227278319463 / 100000) (227688161903 / 100000) := by
  exact
    tile 2274432 2278528 7 5 280 1508 21 _ _ (1463723 / 100000) (731863 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2278528 :
    ThetaLowerSegment 2278528 2282624 (227688161903 / 100000) (45614926459 / 20000) := by
  exact
    tile 2278528 2282624 7 5 264 1509 21 _ _ (1463903 / 100000) (731953 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2282624 :
    ThetaLowerSegment 2282624 2286720 (45614926459 / 20000) (228458221779 / 100000) := by
  exact
    tile 2282624 2286720 7 5 262 1510 21 _ _ (732041 / 50000) (292817 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2286720 :
    ThetaLowerSegment 2286720 2290816 (228458221779 / 100000) (114436303821 / 50000) := by
  exact
    tile 2286720 2290816 7 5 283 1512 21 _ _ (1464261 / 100000) (183033 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2290816 :
    ThetaLowerSegment 2290816 2294912 (114436303821 / 50000) (114640593201 / 50000) := by
  exact
    tile 2290816 2294912 7 5 279 1513 21 _ _ (36611 / 2500) (1464443 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2294912 :
    ThetaLowerSegment 2294912 2299008 (114640593201 / 50000) (1435588806 / 625) := by
  exact
    tile 2294912 2299008 7 5 282 1514 21 _ _ (1464619 / 100000) (732311 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2299008 :
    ThetaLowerSegment 2299008 2303104 (1435588806 / 625) (57527552827 / 25000) := by
  exact
    tile 2299008 2303104 7 5 284 1516 21 _ _ (1464797 / 100000) (1831 / 125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2303104 :
    ThetaLowerSegment 2303104 2307200 (57527552827 / 25000) (230510149483 / 100000) := by
  exact
    tile 2303104 2307200 7 5 273 1517 21 _ _ (58599 / 4000) (732489 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2307200 :
    ThetaLowerSegment 2307200 2311296 (230510149483 / 100000) (115468254503 / 50000) := by
  exact
    tile 2307200 2311296 7 5 291 1518 21 _ _ (1465153 / 100000) (366289 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2311296 :
    ThetaLowerSegment 2311296 2315392 (115468254503 / 50000) (57831938029 / 25000) := by
  exact
    tile 2311296 2315392 7 5 267 1520 21 _ _ (146533 / 10000) (1465333 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2315392 :
    ThetaLowerSegment 2315392 2319488 (57831938029 / 25000) (11586318501 / 5000) := by
  exact
    tile 2315392 2319488 7 5 272 1521 21 _ _ (1465507 / 100000) (146551 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2319488 :
    ThetaLowerSegment 2319488 2323584 (11586318501 / 5000) (14507723149 / 6250) := by
  exact
    tile 2319488 2323584 7 5 271 1522 21 _ _ (366421 / 25000) (1465687 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2323584 :
    ThetaLowerSegment 2323584 2327680 (14507723149 / 6250) (11626407401 / 5000) := by
  exact
    tile 2323584 2327680 7 5 276 1524 21 _ _ (1465861 / 100000) (183233 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2327680 :
    ThetaLowerSegment 2327680 2331776 (11626407401 / 5000) (232922511973 / 100000) := by
  exact
    tile 2327680 2331776 7 5 269 1525 21 _ _ (1466037 / 100000) (36651 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2331776 :
    ThetaLowerSegment 2331776 2335872 (232922511973 / 100000) (233344781317 / 100000) := by
  exact
    tile 2331776 2335872 7 5 288 1527 21 _ _ (1466213 / 100000) (183277 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2335872 :
    ThetaLowerSegment 2335872 2339968 (233344781317 / 100000) (46748434493 / 20000) := by
  exact
    tile 2335872 2339968 7 5 271 1528 21 _ _ (366597 / 25000) (1466391 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2339968 :
    ThetaLowerSegment 2339968 2344064 (46748434493 / 20000) (5854003573 / 2500) := by
  exact
    tile 2339968 2344064 7 5 285 1529 21 _ _ (1466563 / 100000) (733283 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2344064 :
    ThetaLowerSegment 2344064 2348160 (5854003573 / 2500) (23454882849 / 10000) := by
  exact
    tile 2344064 2348160 7 5 265 1531 21 _ _ (733369 / 50000) (1466741 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2348160 :
    ThetaLowerSegment 2348160 2352256 (23454882849 / 10000) (234961031043 / 100000) := by
  exact
    tile 2348160 2352256 7 5 281 1532 21 _ _ (1466913 / 100000) (366729 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2352256 :
    ThetaLowerSegment 2352256 2356352 (234961031043 / 100000) (235354210359 / 100000) := by
  exact
    tile 2352256 2356352 7 5 268 1533 21 _ _ (1467087 / 100000) (146709 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2356352 :
    ThetaLowerSegment 2356352 2360448 (235354210359 / 100000) (235779716049 / 100000) := by
  exact
    tile 2356352 2360448 7 5 290 1535 21 _ _ (1467261 / 100000) (45852 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2360448 :
    ThetaLowerSegment 2360448 2364544 (235779716049 / 100000) (236199402459 / 100000) := by
  exact
    tile 2360448 2364544 7 5 286 1536 21 _ _ (293487 / 20000) (733719 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2364544 :
    ThetaLowerSegment 2364544 2368640 (236199402459 / 100000) (236617670739 / 100000) := by
  exact
    tile 2364544 2368640 7 5 285 1537 21 _ _ (183451 / 12500) (1467611 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2368640 :
    ThetaLowerSegment 2368640 2372736 (236617670739 / 100000) (237011036047 / 100000) := by
  exact
    tile 2368640 2372736 7 5 268 1539 21 _ _ (1467781 / 100000) (183473 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2372736 :
    ThetaLowerSegment 2372736 2376832 (237011036047 / 100000) (237414723397 / 100000) := by
  exact
    tile 2372736 2376832 7 5 275 1540 21 _ _ (733977 / 50000) (1467957 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2376832 :
    ThetaLowerSegment 2376832 2380928 (237414723397 / 100000) (237821394299 / 100000) := by
  exact
    tile 2376832 2380928 7 5 277 1541 21 _ _ (734063 / 50000) (1468129 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2380928 :
    ThetaLowerSegment 2380928 2385024 (237821394299 / 100000) (238235454617 / 100000) := by
  exact
    tile 2380928 2385024 7 5 282 1543 21 _ _ (1468299 / 100000) (734151 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2385024 :
    ThetaLowerSegment 2385024 2389120 (238235454617 / 100000) (238659842447 / 100000) := by
  exact
    tile 2385024 2389120 7 5 289 1544 21 _ _ (146847 / 10000) (1468473 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2389120 :
    ThetaLowerSegment 2389120 2393216 (238659842447 / 100000) (239072530849 / 100000) := by
  exact
    tile 2389120 2393216 7 5 281 1545 21 _ _ (734321 / 50000) (293729 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2393216 :
    ThetaLowerSegment 2393216 2397312 (239072530849 / 100000) (59867644793 / 25000) := by
  exact
    tile 2393216 2397312 7 5 271 1547 21 _ _ (1468813 / 100000) (91801 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2397312 :
    ThetaLowerSegment 2397312 2401408 (59867644793 / 25000) (59971575411 / 25000) := by
  exact
    tile 2397312 2401408 7 5 283 1548 21 _ _ (183623 / 12500) (1468987 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2401408 :
    ThetaLowerSegment 2401408 2405504 (59971575411 / 25000) (60074416261 / 25000) := by
  exact
    tile 2401408 2405504 7 5 280 1549 21 _ _ (293831 / 20000) (734579 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2405504 :
    ThetaLowerSegment 2405504 2409600 (60074416261 / 25000) (24069585239 / 10000) := by
  exact
    tile 2405504 2409600 7 5 271 1550 21 _ _ (734663 / 50000) (1469329 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2409600 :
    ThetaLowerSegment 2409600 2413696 (24069585239 / 10000) (120549247147 / 50000) := by
  exact
    tile 2409600 2413696 7 5 274 1552 21 _ _ (183687 / 12500) (1469499 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2413696 :
    ThetaLowerSegment 2413696 2417792 (120549247147 / 50000) (241514409489 / 100000) := by
  exact
    tile 2413696 2417792 7 5 283 1553 21 _ _ (293933 / 20000) (367417 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2417792 :
    ThetaLowerSegment 2417792 2421888 (241514409489 / 100000) (120965186397 / 50000) := by
  exact
    tile 2417792 2421888 7 5 283 1554 21 _ _ (293967 / 20000) (734919 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2421888 :
    ThetaLowerSegment 2421888 2425984 (120965186397 / 50000) (121165841943 / 50000) := by
  exact
    tile 2421888 2425984 7 5 273 1556 21 _ _ (367501 / 25000) (1470007 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2425984 :
    ThetaLowerSegment 2425984 2430080 (121165841943 / 50000) (12137019599 / 5000) := by
  exact
    tile 2425984 2430080 7 5 278 1557 21 _ _ (1470173 / 100000) (45943 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2430080 :
    ThetaLowerSegment 2430080 2434176 (12137019599 / 5000) (1519608652 / 625) := by
  exact
    tile 2430080 2434176 7 5 270 1558 21 _ _ (735171 / 50000) (294069 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2434176 :
    ThetaLowerSegment 2434176 2438272 (1519608652 / 625) (24353295151 / 10000) := by
  exact
    tile 2434176 2438272 7 5 269 1560 21 _ _ (147051 / 10000) (1470513 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2438272 :
    ThetaLowerSegment 2438272 2442368 (24353295151 / 10000) (60986920747 / 25000) := by
  exact
    tile 2438272 2442368 7 5 282 1561 21 _ _ (1470679 / 100000) (735341 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2442368 :
    ThetaLowerSegment 2442368 2446464 (60986920747 / 25000) (15273021559 / 6250) := by
  exact
    tile 2442368 2446464 7 5 286 1562 21 _ _ (735423 / 50000) (1470849 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2446464 :
    ThetaLowerSegment 2446464 2450560 (15273021559 / 6250) (30596793101 / 12500) := by
  exact
    tile 2446464 2450560 7 5 276 1564 21 _ _ (735507 / 50000) (1471017 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2450560 :
    ThetaLowerSegment 2450560 2454656 (30596793101 / 12500) (122600493649 / 50000) := by
  exact
    tile 2450560 2454656 7 5 290 1565 21 _ _ (1471181 / 100000) (91949 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2454656 :
    ThetaLowerSegment 2454656 2458752 (122600493649 / 50000) (122803539673 / 50000) := by
  exact
    tile 2454656 2458752 7 5 276 1566 21 _ _ (367837 / 25000) (1471351 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2458752 :
    ThetaLowerSegment 2458752 2462848 (122803539673 / 50000) (15376377911 / 6250) := by
  exact
    tile 2458752 2462848 7 5 282 1568 21 _ _ (294303 / 20000) (735759 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2462848 :
    ThetaLowerSegment 2462848 2466944 (15376377911 / 6250) (246435588937 / 100000) := by
  exact
    tile 2462848 2466944 7 5 281 1569 21 _ _ (1471681 / 100000) (367921 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2466944 :
    ThetaLowerSegment 2466944 2471040 (246435588937 / 100000) (49365420101 / 20000) := by
  exact
    tile 2466944 2471040 7 5 266 1570 21 _ _ (183981 / 12500) (1471851 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2471040 :
    ThetaLowerSegment 2471040 2475136 (49365420101 / 20000) (123617424053 / 50000) := by
  exact
    tile 2471040 2475136 7 5 277 1571 21 _ _ (1472013 / 100000) (92001 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2475136 :
    ThetaLowerSegment 2475136 2479232 (123617424053 / 50000) (247627919899 / 100000) := by
  exact
    tile 2475136 2479232 7 5 267 1573 21 _ _ (1472179 / 100000) (736091 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2479232 :
    ThetaLowerSegment 2479232 2483328 (247627919899 / 100000) (1984309631 / 800) := by
  exact
    tile 2479232 2483328 7 5 279 1574 21 _ _ (184043 / 12500) (1472347 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2483328 :
    ThetaLowerSegment 2483328 2487424 (1984309631 / 800) (49692262849 / 20000) := by
  exact
    tile 2483328 2487424 7 5 287 1575 21 _ _ (147251 / 10000) (1472513 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2487424 :
    ThetaLowerSegment 2487424 2491520 (49692262849 / 20000) (248872190291 / 100000) := by
  exact
    tile 2487424 2491520 7 5 279 1577 21 _ _ (736337 / 50000) (1472677 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2491520 :
    ThetaLowerSegment 2491520 2495616 (248872190291 / 100000) (12463566483 / 5000) := by
  exact
    tile 2491520 2495616 7 5 271 1578 21 _ _ (1472839 / 100000) (736421 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2495616 :
    ThetaLowerSegment 2495616 2499712 (12463566483 / 5000) (249682297497 / 100000) := by
  exact
    tile 2495616 2499712 7 5 279 1579 21 _ _ (1473003 / 100000) (736503 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2499712 :
    ThetaLowerSegment 2499712 2503808 (249682297497 / 100000) (250094784257 / 100000) := by
  exact
    tile 2499712 2503808 7 5 280 1581 21 _ _ (1473167 / 100000) (147317 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2503808 :
    ThetaLowerSegment 2503808 2507904 (250094784257 / 100000) (125252921803 / 50000) := by
  exact
    tile 2503808 2507904 7 5 279 1582 21 _ _ (1473331 / 100000) (736667 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2507904 :
    ThetaLowerSegment 2507904 2512000 (125252921803 / 50000) (125459210963 / 50000) := by
  exact
    tile 2507904 2512000 7 5 280 1583 21 _ _ (736747 / 50000) (1473497 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2512000 :
    ThetaLowerSegment 2512000 2516096 (125459210963 / 50000) (62834971957 / 25000) := by
  exact
    tile 2512000 2516096 7 5 286 1584 21 _ _ (1473657 / 100000) (73683 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2516096 :
    ThetaLowerSegment 2516096 2520192 (62834971957 / 25000) (7866392339 / 3125) := by
  exact
    tile 2516096 2520192 7 5 261 1586 21 _ _ (73691 / 5000) (1473823 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2520192 :
    ThetaLowerSegment 2520192 2524288 (7866392339 / 3125) (126076004959 / 50000) := by
  exact
    tile 2520192 2524288 7 5 290 1587 21 _ _ (1473983 / 100000) (736993 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2524288 :
    ThetaLowerSegment 2524288 2528384 (126076004959 / 50000) (252554451503 / 100000) := by
  exact
    tile 2524288 2528384 7 5 273 1588 21 _ _ (294829 / 20000) (368537 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2528384 :
    ThetaLowerSegment 2528384 2532480 (252554451503 / 100000) (252998218211 / 100000) := by
  exact
    tile 2528384 2532480 7 5 301 1590 21 _ _ (368577 / 25000) (1474311 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2532480 :
    ThetaLowerSegment 2532480 2536576 (252998218211 / 100000) (253387478027 / 100000) := by
  exact
    tile 2532480 2536576 7 5 264 1591 21 _ _ (1474469 / 100000) (184309 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2536576 :
    ThetaLowerSegment 2536576 2540672 (253387478027 / 100000) (25379005229 / 10000) := by
  exact
    tile 2536576 2540672 7 5 273 1592 21 _ _ (1474631 / 100000) (737317 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2540672 :
    ThetaLowerSegment 2540672 2544768 (25379005229 / 10000) (127096335253 / 50000) := by
  exact
    tile 2540672 2544768 7 5 273 1593 21 _ _ (184349 / 12500) (294959 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2544768 :
    ThetaLowerSegment 2544768 2548864 (127096335253 / 50000) (1591202394 / 625) := by
  exact
    tile 2544768 2548864 7 5 271 1595 21 _ _ (737477 / 50000) (1474957 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2548864 :
    ThetaLowerSegment 2548864 2552960 (1591202394 / 625) (127501969923 / 50000) := by
  exact
    tile 2548864 2552960 7 5 279 1596 21 _ _ (737557 / 50000) (1475117 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2552960 :
    ThetaLowerSegment 2552960 2557056 (127501969923 / 50000) (127705557873 / 50000) := by
  exact
    tile 2552960 2557056 7 5 276 1597 21 _ _ (59011 / 4000) (737639 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2557056 :
    ThetaLowerSegment 2557056 2561152 (127705557873 / 50000) (7994599638 / 3125) := by
  exact
    tile 2557056 2561152 7 5 282 1599 21 _ _ (295087 / 20000) (737719 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2561152 :
    ThetaLowerSegment 2561152 2565248 (7994599638 / 3125) (256238879421 / 100000) := by
  exact
    tile 2561152 2565248 7 5 279 1600 21 _ _ (295119 / 20000) (737799 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2565248 :
    ThetaLowerSegment 2565248 2569344 (256238879421 / 100000) (64161915889 / 25000) := by
  exact
    tile 2565248 2569344 7 5 277 1601 21 _ _ (295151 / 20000) (737879 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2569344 :
    ThetaLowerSegment 2569344 2573440 (64161915889 / 25000) (257059443841 / 100000) := by
  exact
    tile 2569344 2573440 7 5 279 1602 21 _ _ (295183 / 20000) (737959 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2573440 :
    ThetaLowerSegment 2573440 2577536 (257059443841 / 100000) (257486029227 / 100000) := by
  exact
    tile 2573440 2577536 7 5 289 1604 21 _ _ (738037 / 50000) (1476077 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2577536 :
    ThetaLowerSegment 2577536 2581632 (257486029227 / 100000) (257914136797 / 100000) := by
  exact
    tile 2577536 2581632 7 5 290 1605 21 _ _ (1476233 / 100000) (369059 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2581632 :
    ThetaLowerSegment 2581632 2585728 (257914136797 / 100000) (258327526557 / 100000) := by
  exact
    tile 2581632 2585728 7 5 280 1606 21 _ _ (184549 / 12500) (295279 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2585728 :
    ThetaLowerSegment 2585728 2589824 (258327526557 / 100000) (258748343307 / 100000) := by
  exact
    tile 2585728 2589824 7 5 285 1608 21 _ _ (29531 / 2000) (1476553 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2589824 :
    ThetaLowerSegment 2589824 2593920 (258748343307 / 100000) (51827048213 / 20000) := by
  exact
    tile 2589824 2593920 7 5 262 1609 21 _ _ (1476709 / 100000) (184589 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2593920 :
    ThetaLowerSegment 2593920 2598016 (51827048213 / 20000) (64890513907 / 25000) := by
  exact
    tile 2593920 2598016 7 5 289 1610 21 _ _ (1476867 / 100000) (147687 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2598016 :
    ThetaLowerSegment 2598016 2602112 (64890513907 / 25000) (64989843771 / 25000) := by
  exact
    tile 2598016 2602112 7 5 269 1611 21 _ _ (46157 / 3125) (1477027 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2602112 :
    ThetaLowerSegment 2602112 2606208 (64989843771 / 25000) (13017762993 / 5000) := by
  exact
    tile 2602112 2606208 7 5 268 1613 21 _ _ (738591 / 50000) (295437 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2606208 :
    ThetaLowerSegment 2606208 2610304 (13017762993 / 5000) (32593898339 / 12500) := by
  exact
    tile 2606208 2610304 7 5 268 1614 21 _ _ (1477339 / 100000) (738671 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2610304 :
    ThetaLowerSegment 2610304 2614400 (32593898339 / 12500) (8161725877 / 3125) := by
  exact
    tile 2610304 2614400 7 5 287 1615 21 _ _ (184687 / 12500) (1477499 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2614400 :
    ThetaLowerSegment 2614400 2618496 (8161725877 / 3125) (261593403863 / 100000) := by
  exact
    tile 2614400 2618496 7 5 283 1616 21 _ _ (1477653 / 100000) (184707 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2618496 :
    ThetaLowerSegment 2618496 2622592 (261593403863 / 100000) (261986501323 / 100000) := by
  exact
    tile 2618496 2622592 7 5 266 1618 21 _ _ (147781 / 10000) (1477813 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2622592 :
    ThetaLowerSegment 2622592 2626688 (261986501323 / 100000) (10495540323 / 4000) := by
  exact
    tile 2622592 2626688 7 5 272 1619 21 _ _ (738983 / 50000) (1477969 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2626688 :
    ThetaLowerSegment 2626688 2630784 (10495540323 / 4000) (52560476447 / 20000) := by
  exact
    tile 2626688 2630784 7 5 280 1620 21 _ _ (739061 / 50000) (473 / 32) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2630784 :
    ThetaLowerSegment 2630784 2634880 (52560476447 / 20000) (263239952523 / 100000) := by
  exact
    tile 2630784 2634880 7 5 296 1621 21 _ _ (739139 / 50000) (1478281 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2634880 :
    ThetaLowerSegment 2634880 2638976 (263239952523 / 100000) (16476613971 / 6250) := by
  exact
    tile 2634880 2638976 7 5 261 1623 21 _ _ (1478433 / 100000) (369609 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2638976 :
    ThetaLowerSegment 2638976 2643072 (16476613971 / 6250) (264038349867 / 100000) := by
  exact
    tile 2638976 2643072 7 5 279 1624 21 _ _ (1478589 / 100000) (46206 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2643072 :
    ThetaLowerSegment 2643072 2647168 (264038349867 / 100000) (264464228139 / 100000) := by
  exact
    tile 2643072 2647168 7 5 288 1625 21 _ _ (184843 / 12500) (1478747 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2647168 :
    ThetaLowerSegment 2647168 2651264 (264464228139 / 100000) (264872404263 / 100000) := by
  exact
    tile 2647168 2651264 7 5 276 1627 21 _ _ (1478899 / 100000) (739451 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2651264 :
    ThetaLowerSegment 2651264 2655360 (264872404263 / 100000) (265286539103 / 100000) := by
  exact
    tile 2651264 2655360 7 5 280 1628 21 _ _ (1479053 / 100000) (92441 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2655360 :
    ThetaLowerSegment 2655360 2659456 (265286539103 / 100000) (265725863879 / 100000) := by
  exact
    tile 2655360 2659456 7 5 297 1629 21 _ _ (184901 / 12500) (1479211 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2659456 :
    ThetaLowerSegment 2659456 2663552 (265725863879 / 100000) (266111977361 / 100000) := by
  exact
    tile 2659456 2663552 7 5 261 1630 21 _ _ (739681 / 50000) (295873 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2663552 :
    ThetaLowerSegment 2663552 2667648 (266111977361 / 100000) (266529200873 / 100000) := by
  exact
    tile 2663552 2667648 7 5 282 1632 21 _ _ (369879 / 25000) (1479519 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2667648 :
    ThetaLowerSegment 2667648 2671744 (266529200873 / 100000) (133454737903 / 50000) := by
  exact
    tile 2667648 2671744 7 5 257 1633 21 _ _ (1479669 / 100000) (184959 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2671744 :
    ThetaLowerSegment 2671744 2675840 (133454737903 / 50000) (1336604333 / 500) := by
  exact
    tile 2671744 2675840 7 5 278 1634 21 _ _ (1479823 / 100000) (739913 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2675840 :
    ThetaLowerSegment 2675840 2679936 (1336604333 / 500) (16733176247 / 6250) := by
  exact
    tile 2675840 2679936 7 5 277 1635 21 _ _ (184997 / 12500) (1479979 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2679936 :
    ThetaLowerSegment 2679936 2684032 (16733176247 / 6250) (268137855427 / 100000) := by
  exact
    tile 2679936 2684032 7 5 275 1637 21 _ _ (1480129 / 100000) (370033 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2684032 :
    ThetaLowerSegment 2684032 2688128 (268137855427 / 100000) (53710170821 / 20000) := by
  exact
    tile 2684032 2688128 7 5 279 1638 21 _ _ (740141 / 50000) (296057 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2688128 :
    ThetaLowerSegment 2688128 2692224 (53710170821 / 20000) (268971297361 / 100000) := by
  exact
    tile 2688128 2692224 7 5 284 1639 21 _ _ (740217 / 50000) (1480437 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2692224 :
    ThetaLowerSegment 2692224 2696320 (268971297361 / 100000) (53878356757 / 20000) := by
  exact
    tile 2692224 2696320 7 5 284 1640 21 _ _ (740293 / 50000) (1480589 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2696320 :
    ThetaLowerSegment 2696320 2700416 (53878356757 / 20000) (10792255617 / 4000) := by
  exact
    tile 2696320 2700416 7 5 280 1642 21 _ _ (740369 / 50000) (1480741 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2700416 :
    ThetaLowerSegment 2700416 2704512 (10792255617 / 4000) (54039172899 / 20000) := by
  exact
    tile 2700416 2704512 7 5 263 1643 21 _ _ (148089 / 10000) (1480893 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2704512 :
    ThetaLowerSegment 2704512 2708608 (54039172899 / 20000) (270628328759 / 100000) := by
  exact
    tile 2704512 2708608 7 5 292 1644 21 _ _ (740521 / 50000) (296209 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2708608 :
    ThetaLowerSegment 2708608 2712704 (270628328759 / 100000) (271043062799 / 100000) := by
  exact
    tile 2708608 2712704 7 5 280 1645 21 _ _ (1481193 / 100000) (370299 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2712704 :
    ThetaLowerSegment 2712704 2716800 (271043062799 / 100000) (271453395087 / 100000) := by
  exact
    tile 2712704 2716800 7 5 277 1647 21 _ _ (46292 / 3125) (1481347 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2716800 :
    ThetaLowerSegment 2716800 2720896 (271453395087 / 100000) (271877102657 / 100000) := by
  exact
    tile 2716800 2720896 7 5 286 1648 21 _ _ (296299 / 20000) (740749 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2720896 :
    ThetaLowerSegment 2720896 2724992 (271877102657 / 100000) (272275665431 / 100000) := by
  exact
    tile 2720896 2724992 7 5 269 1649 21 _ _ (740823 / 50000) (1481649 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2724992 :
    ThetaLowerSegment 2724992 2729088 (272275665431 / 100000) (272657968799 / 100000) := by
  exact
    tile 2724992 2729088 7 5 258 1650 21 _ _ (370449 / 25000) (1481799 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2729088 :
    ThetaLowerSegment 2729088 2733184 (272657968799 / 100000) (273075877571 / 100000) := by
  exact
    tile 2729088 2733184 7 5 282 1651 21 _ _ (740973 / 50000) (1481949 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2733184 :
    ThetaLowerSegment 2733184 2737280 (273075877571 / 100000) (273453812051 / 100000) := by
  exact
    tile 2733184 2737280 7 5 255 1653 21 _ _ (92631 / 6250) (1482099 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2737280 :
    ThetaLowerSegment 2737280 2741376 (273453812051 / 100000) (273871805423 / 100000) := by
  exact
    tile 2737280 2741376 7 5 282 1654 21 _ _ (741123 / 50000) (1482249 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2741376 :
    ThetaLowerSegment 2741376 2745472 (273871805423 / 100000) (274286876303 / 100000) := by
  exact
    tile 2741376 2745472 7 5 280 1655 21 _ _ (370599 / 25000) (1482399 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2745472 :
    ThetaLowerSegment 2745472 2749568 (274286876303 / 100000) (137344322999 / 50000) := by
  exact
    tile 2745472 2749568 7 5 271 1656 21 _ _ (296509 / 20000) (370637 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2749568 :
    ThetaLowerSegment 2749568 2753664 (137344322999 / 50000) (137545969383 / 50000) := by
  exact
    tile 2749568 2753664 7 5 272 1658 21 _ _ (741347 / 50000) (1482697 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2753664 :
    ThetaLowerSegment 2753664 2757760 (137545969383 / 50000) (275493789219 / 100000) := by
  exact
    tile 2753664 2757760 7 5 271 1659 21 _ _ (1482843 / 100000) (741423 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2757760 :
    ThetaLowerSegment 2757760 2761856 (275493789219 / 100000) (137958220827 / 50000) := by
  exact
    tile 2757760 2761856 7 5 285 1660 21 _ _ (1482991 / 100000) (741497 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2761856 :
    ThetaLowerSegment 2761856 2765952 (137958220827 / 50000) (138165860427 / 50000) := by
  exact
    tile 2761856 2765952 7 5 280 1661 21 _ _ (74157 / 5000) (1483143 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2765952 :
    ThetaLowerSegment 2765952 2770048 (138165860427 / 50000) (138368329239 / 50000) := by
  exact
    tile 2765952 2770048 7 5 273 1663 21 _ _ (185411 / 12500) (1483291 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2770048 :
    ThetaLowerSegment 2770048 2774144 (138368329239 / 50000) (138574526843 / 50000) := by
  exact
    tile 2770048 2774144 7 5 278 1664 21 _ _ (370859 / 25000) (1483439 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2774144 :
    ThetaLowerSegment 2774144 2778240 (138574526843 / 50000) (138778519643 / 50000) := by
  exact
    tile 2774144 2778240 7 5 275 1665 21 _ _ (46362 / 3125) (1483587 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2778240 :
    ThetaLowerSegment 2778240 2782336 (138778519643 / 50000) (11118246517 / 4000) := by
  exact
    tile 2778240 2782336 7 5 269 1666 21 _ _ (1483731 / 100000) (741867 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2782336 :
    ThetaLowerSegment 2782336 2786432 (11118246517 / 4000) (278374616803 / 100000) := by
  exact
    tile 2782336 2786432 7 5 282 1668 21 _ _ (1483879 / 100000) (741941 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2786432 :
    ThetaLowerSegment 2786432 2790528 (278374616803 / 100000) (278760463563 / 100000) := by
  exact
    tile 2786432 2790528 7 5 260 1669 21 _ _ (742013 / 50000) (1484029 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2790528 :
    ThetaLowerSegment 2790528 2794624 (278760463563 / 100000) (279176032003 / 100000) := by
  exact
    tile 2790528 2794624 7 5 280 1670 21 _ _ (1484173 / 100000) (92761 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2794624 :
    ThetaLowerSegment 2794624 2798720 (279176032003 / 100000) (34946543147 / 12500) := by
  exact
    tile 2794624 2798720 7 5 267 1671 21 _ _ (1484319 / 100000) (742161 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2798720 :
    ThetaLowerSegment 2798720 2802816 (34946543147 / 12500) (139994740061 / 50000) := by
  exact
    tile 2798720 2802816 7 5 281 1672 21 _ _ (742233 / 50000) (1484469 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2802816 :
    ThetaLowerSegment 2802816 2806912 (139994740061 / 50000) (140214462637 / 50000) := by
  exact
    tile 2802816 2806912 7 5 296 1674 21 _ _ (371153 / 25000) (296923 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2806912 :
    ThetaLowerSegment 2806912 2811008 (140214462637 / 50000) (35106510163 / 12500) := by
  exact
    tile 2806912 2811008 7 5 285 1675 21 _ _ (742379 / 50000) (1484761 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2811008 :
    ThetaLowerSegment 2811008 2815104 (35106510163 / 12500) (35160709159 / 12500) := by
  exact
    tile 2811008 2815104 7 5 292 1676 21 _ _ (185613 / 12500) (1484907 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2815104 :
    ThetaLowerSegment 2815104 2819200 (35160709159 / 12500) (140846288349 / 50000) := by
  exact
    tile 2815104 2819200 7 5 274 1677 21 _ _ (1485049 / 100000) (371263 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2819200 :
    ThetaLowerSegment 2819200 2823296 (140846288349 / 50000) (17632705203 / 6250) := by
  exact
    tile 2819200 2823296 7 5 290 1679 21 _ _ (297039 / 20000) (742599 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2823296 :
    ThetaLowerSegment 2823296 2827392 (17632705203 / 6250) (70626996577 / 25000) := by
  exact
    tile 2823296 2827392 7 5 259 1680 21 _ _ (74267 / 5000) (1485343 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2827392 :
    ThetaLowerSegment 2827392 2831488 (70626996577 / 25000) (35364747521 / 12500) := by
  exact
    tile 2827392 2831488 7 5 276 1681 21 _ _ (297097 / 20000) (92843 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2831488 :
    ThetaLowerSegment 2831488 2835584 (35364747521 / 12500) (141681091769 / 50000) := by
  exact
    tile 2831488 2835584 7 5 299 1682 21 _ _ (148563 / 10000) (1485633 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2835584 :
    ThetaLowerSegment 2835584 2839680 (141681091769 / 50000) (17736230377 / 6250) := by
  exact
    tile 2835584 2839680 7 5 281 1683 21 _ _ (742887 / 50000) (1485777 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2839680 :
    ThetaLowerSegment 2839680 2843776 (17736230377 / 6250) (284194257433 / 100000) := by
  exact
    tile 2839680 2843776 7 5 279 1685 21 _ _ (1485919 / 100000) (742961 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2843776 :
    ThetaLowerSegment 2843776 2847872 (284194257433 / 100000) (8893377004 / 3125) := by
  exact
    tile 2843776 2847872 7 5 265 1686 21 _ _ (1486063 / 100000) (743033 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2847872 :
    ThetaLowerSegment 2847872 2851968 (8893377004 / 3125) (71252536729 / 25000) := by
  exact
    tile 2847872 2851968 7 5 284 1687 21 _ _ (1486207 / 100000) (148621 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2851968 :
    ThetaLowerSegment 2851968 2856064 (71252536729 / 25000) (142707960233 / 50000) := by
  exact
    tile 2851968 2856064 7 5 273 1688 21 _ _ (29727 / 2000) (1486353 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2856064 :
    ThetaLowerSegment 2856064 2860160 (142707960233 / 50000) (142901204453 / 50000) := by
  exact
    tile 2856064 2860160 7 5 260 1689 21 _ _ (743247 / 50000) (1486497 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2860160 :
    ThetaLowerSegment 2860160 2864256 (142901204453 / 50000) (35776961749 / 12500) := by
  exact
    tile 2860160 2864256 7 5 278 1691 21 _ _ (1486637 / 100000) (18583 / 1250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2864256 :
    ThetaLowerSegment 2864256 2868352 (35776961749 / 12500) (71660599963 / 25000) := by
  exact
    tile 2864256 2868352 7 5 287 1692 21 _ _ (74339 / 5000) (1486783 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2868352 :
    ThetaLowerSegment 2868352 2872448 (71660599963 / 25000) (14351152607 / 5000) := by
  exact
    tile 2868352 2872448 7 5 256 1693 21 _ _ (1486923 / 100000) (743463 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2872448 :
    ThetaLowerSegment 2872448 2876544 (14351152607 / 5000) (143711536447 / 50000) := by
  exact
    tile 2872448 2876544 7 5 269 1694 21 _ _ (743533 / 50000) (1487069 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2876544 :
    ThetaLowerSegment 2876544 2880640 (143711536447 / 50000) (35977333811 / 12500) := by
  exact
    tile 2876544 2880640 7 5 266 1696 21 _ _ (1487209 / 100000) (371803 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2880640 :
    ThetaLowerSegment 2880640 2884736 (35977333811 / 12500) (28823810347 / 10000) := by
  exact
    tile 2880640 2884736 7 5 282 1697 21 _ _ (1487351 / 100000) (743677 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2884736 :
    ThetaLowerSegment 2884736 2888832 (28823810347 / 10000) (57729432809 / 20000) := by
  exact
    tile 2884736 2888832 7 5 275 1698 21 _ _ (1487493 / 100000) (185937 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2888832 :
    ThetaLowerSegment 2888832 2892928 (57729432809 / 20000) (57808574991 / 20000) := by
  exact
    tile 2888832 2892928 7 5 266 1699 21 _ _ (297527 / 20000) (743819 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2892928 :
    ThetaLowerSegment 2892928 2897024 (57808574991 / 20000) (289456476683 / 100000) := by
  exact
    tile 2892928 2897024 7 5 278 1700 21 _ _ (46493 / 3125) (1487779 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2897024 :
    ThetaLowerSegment 2897024 2901120 (289456476683 / 100000) (289865654133 / 100000) := by
  exact
    tile 2897024 2901120 7 5 275 1702 21 _ _ (743959 / 50000) (1487921 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2901120 :
    ThetaLowerSegment 2901120 2905216 (289865654133 / 100000) (290273382299 / 100000) := by
  exact
    tile 2901120 2905216 7 5 274 1703 21 _ _ (1488059 / 100000) (744031 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2905216 :
    ThetaLowerSegment 2905216 2909312 (290273382299 / 100000) (290691566499 / 100000) := by
  exact
    tile 2905216 2909312 7 5 281 1704 21 _ _ (7441 / 500) (1488203 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2909312 :
    ThetaLowerSegment 2909312 2913408 (290691566499 / 100000) (291093418569 / 100000) := by
  exact
    tile 2909312 2913408 7 5 270 1705 21 _ _ (1488341 / 100000) (186043 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2913408 :
    ThetaLowerSegment 2913408 2917504 (291093418569 / 100000) (291490843263 / 100000) := by
  exact
    tile 2913408 2917504 7 5 267 1706 21 _ _ (744241 / 50000) (297697 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2917504 :
    ThetaLowerSegment 2917504 2921600 (291490843263 / 100000) (291913611911 / 100000) := by
  exact
    tile 2917504 2921600 7 5 284 1708 21 _ _ (744311 / 50000) (11909 / 800) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2921600 :
    ThetaLowerSegment 2921600 2925696 (291913611911 / 100000) (11693099521 / 4000) := by
  exact
    tile 2921600 2925696 7 5 278 1709 21 _ _ (1488763 / 100000) (744383 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2925696 :
    ThetaLowerSegment 2925696 2929792 (11693099521 / 4000) (292726514029 / 100000) := by
  exact
    tile 2925696 2929792 7 5 268 1710 21 _ _ (1488903 / 100000) (744453 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2929792 :
    ThetaLowerSegment 2929792 2933888 (292726514029 / 100000) (293125577553 / 100000) := by
  exact
    tile 2929792 2933888 7 5 268 1711 21 _ _ (1489043 / 100000) (744523 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2933888 :
    ThetaLowerSegment 2933888 2937984 (293125577553 / 100000) (58710296721 / 20000) := by
  exact
    tile 2933888 2937984 7 5 286 1712 21 _ _ (744591 / 50000) (297837 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2937984 :
    ThetaLowerSegment 2937984 2942080 (58710296721 / 20000) (293952111223 / 100000) := by
  exact
    tile 2937984 2942080 7 5 269 1714 21 _ _ (744661 / 50000) (59573 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2942080 :
    ThetaLowerSegment 2942080 2946176 (293952111223 / 100000) (73586704597 / 25000) := by
  exact
    tile 2942080 2946176 7 5 265 1715 21 _ _ (1489461 / 100000) (186183 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2946176 :
    ThetaLowerSegment 2946176 2950272 (73586704597 / 25000) (73689114597 / 25000) := by
  exact
    tile 2946176 2950272 7 5 275 1716 21 _ _ (1862 / 125) (1489603 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell2950272 :
    ThetaLowerSegment 2950272 2954368 (73689114597 / 25000) (295160177657 / 100000) := by
  exact
    tile 2950272 2954368 7 5 271 1717 21 _ _ (1489739 / 100000) (744871 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2954368 :
    ThetaLowerSegment 2954368 2958464 (295160177657 / 100000) (59109807163 / 20000) := by
  exact
    tile 2954368 2958464 7 5 261 1718 21 _ _ (744939 / 50000) (1489881 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2958464 :
    ThetaLowerSegment 2958464 2962560 (59109807163 / 20000) (147988335347 / 50000) := by
  exact
    tile 2958464 2962560 7 5 287 1720 21 _ _ (1490017 / 100000) (74501 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2962560 :
    ThetaLowerSegment 2962560 2966656 (147988335347 / 50000) (296383483009 / 100000) := by
  exact
    tile 2962560 2966656 7 5 273 1721 21 _ _ (298031 / 20000) (745079 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2966656 :
    ThetaLowerSegment 2966656 2970752 (296383483009 / 100000) (296812687393 / 100000) := by
  exact
    tile 2966656 2970752 7 5 288 1722 22 _ _ (1490293 / 100000) (186287 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2970752 :
    ThetaLowerSegment 2970752 2974848 (296812687393 / 100000) (59440636063 / 20000) := by
  exact
    tile 2970752 2974848 7 5 262 1723 22 _ _ (1490431 / 100000) (745217 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2974848 :
    ThetaLowerSegment 2974848 2978944 (59440636063 / 20000) (18600258961 / 6250) := by
  exact
    tile 2974848 2978944 7 5 269 1724 22 _ _ (1490569 / 100000) (372643 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2978944 :
    ThetaLowerSegment 2978944 2983040 (18600258961 / 6250) (29803495741 / 10000) := by
  exact
    tile 2978944 2983040 7 5 289 1725 22 _ _ (745353 / 50000) (1490709 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2983040 :
    ThetaLowerSegment 2983040 2987136 (29803495741 / 10000) (149230669397 / 50000) := by
  exact
    tile 2983040 2987136 7 5 286 1727 22 _ _ (372711 / 25000) (1490847 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2987136 :
    ThetaLowerSegment 2987136 2991232 (149230669397 / 50000) (29884302993 / 10000) := by
  exact
    tile 2987136 2991232 7 5 256 1728 22 _ _ (1490981 / 100000) (186373 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2991232 :
    ThetaLowerSegment 2991232 2995328 (29884302993 / 10000) (18703504351 / 6250) := by
  exact
    tile 2991232 2995328 7 5 277 1729 22 _ _ (745559 / 50000) (1491121 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2995328 :
    ThetaLowerSegment 2995328 2999424 (18703504351 / 6250) (149841284273 / 50000) := by
  exact
    tile 2995328 2999424 7 5 286 1730 22 _ _ (298251 / 20000) (745629 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2999424 :
    ThetaLowerSegment 2999424 3003520 (149841284273 / 50000) (150050824849 / 50000) := by
  exact
    tile 2999424 3003520 7 5 281 1731 22 _ _ (46606 / 3125) (298279 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3003520 :
    ThetaLowerSegment 3003520 3007616 (150050824849 / 50000) (150252181129 / 50000) := by
  exact
    tile 3003520 3007616 7 5 270 1733 22 _ _ (186441 / 12500) (1491531 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3007616 :
    ThetaLowerSegment 3007616 3011712 (150252181129 / 50000) (150460268257 / 50000) := by
  exact
    tile 3007616 3011712 7 5 279 1734 22 _ _ (93229 / 6250) (1491667 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3011712 :
    ThetaLowerSegment 3011712 3015808 (150460268257 / 50000) (150662407157 / 50000) := by
  exact
    tile 3011712 3015808 7 5 271 1735 22 _ _ (7459 / 500) (1491803 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3015808 :
    ThetaLowerSegment 3015808 3019904 (150662407157 / 50000) (150857850773 / 50000) := by
  exact
    tile 3015808 3019904 7 5 262 1736 22 _ _ (46623 / 3125) (1491939 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3019904 :
    ThetaLowerSegment 3019904 3024000 (150857850773 / 50000) (30212154513 / 10000) := by
  exact
    tile 3019904 3024000 7 5 272 1737 22 _ _ (186509 / 12500) (59683 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3024000 :
    ThetaLowerSegment 3024000 3028096 (30212154513 / 10000) (151266697269 / 50000) := by
  exact
    tile 3024000 3028096 7 5 276 1738 22 _ _ (93263 / 6250) (1492211 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3028096 :
    ThetaLowerSegment 3028096 3032192 (151266697269 / 50000) (151466671231 / 50000) := by
  exact
    tile 3028096 3032192 7 5 268 1740 22 _ _ (1492343 / 100000) (746173 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3032192 :
    ThetaLowerSegment 3032192 3036288 (151466671231 / 50000) (30333034161 / 10000) := by
  exact
    tile 3032192 3036288 7 5 266 1741 22 _ _ (746239 / 50000) (1492481 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3036288 :
    ThetaLowerSegment 3036288 3040384 (30333034161 / 10000) (303734839733 / 100000) := by
  exact
    tile 3036288 3040384 7 5 271 1742 22 _ _ (1492613 / 100000) (186577 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3040384 :
    ThetaLowerSegment 3040384 3044480 (303734839733 / 100000) (304157287417 / 100000) := by
  exact
    tile 3040384 3044480 7 5 283 1743 22 _ _ (373187 / 25000) (1492751 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3044480 :
    ThetaLowerSegment 3044480 3048576 (304157287417 / 100000) (76138225353 / 25000) := by
  exact
    tile 3044480 3048576 7 5 265 1744 22 _ _ (1492883 / 100000) (746443 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3048576 :
    ThetaLowerSegment 3048576 3052672 (76138225353 / 25000) (60990904597 / 20000) := by
  exact
    tile 3048576 3052672 7 5 269 1746 22 _ _ (1493017 / 100000) (74651 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3052672 :
    ThetaLowerSegment 3052672 3056768 (60990904597 / 20000) (305360660057 / 100000) := by
  exact
    tile 3052672 3056768 7 5 272 1747 22 _ _ (1493151 / 100000) (746577 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3056768 :
    ThetaLowerSegment 3056768 3060864 (305360660057 / 100000) (305769820147 / 100000) := by
  exact
    tile 3056768 3060864 7 5 274 1748 22 _ _ (298657 / 20000) (186661 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3060864 :
    ThetaLowerSegment 3060864 3064960 (305769820147 / 100000) (30615362883 / 10000) := by
  exact
    tile 3060864 3064960 7 5 257 1749 22 _ _ (1493419 / 100000) (746711 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3064960 :
    ThetaLowerSegment 3064960 3069056 (30615362883 / 10000) (306570330117 / 100000) := by
  exact
    tile 3064960 3069056 7 5 279 1750 22 _ _ (1493553 / 100000) (373389 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3069056 :
    ThetaLowerSegment 3069056 3073152 (306570330117 / 100000) (9593625966 / 3125) := by
  exact
    tile 3069056 3073152 7 5 285 1751 22 _ _ (1493687 / 100000) (149369 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3073152 :
    ThetaLowerSegment 3073152 3077248 (9593625966 / 3125) (76856189313 / 25000) := by
  exact
    tile 3073152 3077248 7 5 287 1753 22 _ _ (74691 / 5000) (1493823 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3077248 :
    ThetaLowerSegment 3077248 3081344 (76856189313 / 25000) (9620282497 / 3125) := by
  exact
    tile 3077248 3081344 7 5 284 1754 22 _ _ (1493953 / 100000) (373489 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3081344 :
    ThetaLowerSegment 3081344 3085440 (9620282497 / 3125) (154123980433 / 50000) := by
  exact
    tile 3081344 3085440 7 5 267 1755 22 _ _ (747043 / 50000) (1494089 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3085440 :
    ThetaLowerSegment 3085440 3089536 (154123980433 / 50000) (61736555719 / 20000) := by
  exact
    tile 3085440 3089536 7 5 291 1756 22 _ _ (1494219 / 100000) (747111 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3089536 :
    ThetaLowerSegment 3089536 3093632 (61736555719 / 20000) (309099702803 / 100000) := by
  exact
    tile 3089536 3093632 7 5 279 1757 22 _ _ (93397 / 6250) (298871 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3093632 :
    ThetaLowerSegment 3093632 3097728 (309099702803 / 100000) (309497235547 / 100000) := by
  exact
    tile 3093632 3097728 7 5 266 1758 22 _ _ (373621 / 25000) (1494487 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3097728 :
    ThetaLowerSegment 3097728 3101824 (309497235547 / 100000) (309866405699 / 100000) := by
  exact
    tile 3097728 3101824 7 5 247 1760 22 _ _ (186827 / 12500) (1494619 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3101824 :
    ThetaLowerSegment 3101824 3105920 (309866405699 / 100000) (155150688829 / 50000) := by
  exact
    tile 3101824 3105920 7 5 291 1761 22 _ _ (1494749 / 100000) (46711 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3105920 :
    ThetaLowerSegment 3105920 3110016 (155150688829 / 50000) (155359972169 / 50000) := by
  exact
    tile 3105920 3110016 7 5 280 1762 22 _ _ (1494881 / 100000) (373721 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3110016 :
    ThetaLowerSegment 3110016 3114112 (155359972169 / 50000) (155560303777 / 50000) := by
  exact
    tile 3110016 3114112 7 5 268 1763 22 _ _ (373753 / 25000) (299003 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3114112 :
    ThetaLowerSegment 3114112 3118208 (155560303777 / 50000) (155771119081 / 50000) := by
  exact
    tile 3114112 3118208 7 5 282 1764 22 _ _ (186893 / 12500) (1495147 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3118208 :
    ThetaLowerSegment 3118208 3122304 (155771119081 / 50000) (311959419887 / 100000) := by
  exact
    tile 3118208 3122304 7 5 279 1765 22 _ _ (59811 / 4000) (747639 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3122304 :
    ThetaLowerSegment 3122304 3126400 (311959419887 / 100000) (78089673389 / 25000) := by
  exact
    tile 3122304 3126400 7 5 267 1767 22 _ _ (1495407 / 100000) (149541 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3126400 :
    ThetaLowerSegment 3126400 3130496 (78089673389 / 25000) (39097554409 / 12500) := by
  exact
    tile 3126400 3130496 7 5 282 1768 22 _ _ (747769 / 50000) (1495541 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3130496 :
    ThetaLowerSegment 3130496 3134592 (39097554409 / 12500) (313188752909 / 100000) := by
  exact
    tile 3130496 3134592 7 5 273 1769 22 _ _ (1495669 / 100000) (186959 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3134592 :
    ThetaLowerSegment 3134592 3138688 (313188752909 / 100000) (9799348639 / 3125) := by
  exact
    tile 3134592 3138688 7 5 261 1770 22 _ _ (1495799 / 100000) (747901 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3138688 :
    ThetaLowerSegment 3138688 3142784 (9799348639 / 3125) (9812064044 / 3125) := by
  exact
    tile 3138688 3142784 7 5 272 1771 22 _ _ (149593 / 10000) (1495933 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3142784 :
    ThetaLowerSegment 3142784 3146880 (9812064044 / 3125) (39299496231 / 12500) := by
  exact
    tile 3142784 3146880 7 5 274 1772 22 _ _ (74803 / 5000) (1496063 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3146880 :
    ThetaLowerSegment 3146880 3150976 (39299496231 / 12500) (78702229641 / 25000) := by
  exact
    tile 3146880 3150976 7 5 276 1773 22 _ _ (1496191 / 100000) (748097 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3150976 :
    ThetaLowerSegment 3150976 3155072 (78702229641 / 25000) (315238362691 / 100000) := by
  exact
    tile 3150976 3155072 7 5 287 1775 22 _ _ (1496321 / 100000) (374081 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3155072 :
    ThetaLowerSegment 3155072 3159168 (315238362691 / 100000) (315636418657 / 100000) := by
  exact
    tile 3155072 3159168 7 5 266 1776 22 _ _ (1496451 / 100000) (748227 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3159168 :
    ThetaLowerSegment 3159168 3163264 (315636418657 / 100000) (316021039717 / 100000) := by
  exact
    tile 3159168 3163264 7 5 257 1777 22 _ _ (74829 / 5000) (1496583 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3163264 :
    ThetaLowerSegment 3163264 3167360 (316021039717 / 100000) (316470052717 / 100000) := by
  exact
    tile 3163264 3167360 7 5 300 1778 22 _ _ (149671 / 10000) (1496713 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3167360 :
    ThetaLowerSegment 3167360 3171456 (316470052717 / 100000) (31686970873 / 10000) := by
  exact
    tile 3167360 3171456 7 5 267 1779 22 _ _ (1496839 / 100000) (748421 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3171456 :
    ThetaLowerSegment 3171456 3175552 (31686970873 / 10000) (158641436087 / 50000) := by
  exact
    tile 3171456 3175552 7 5 276 1780 22 _ _ (1496969 / 100000) (374243 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3175552 :
    ThetaLowerSegment 3175552 3179648 (158641436087 / 50000) (158840550121 / 50000) := by
  exact
    tile 3175552 3179648 7 5 266 1782 22 _ _ (748549 / 50000) (1497101 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3179648 :
    ThetaLowerSegment 3179648 3183744 (158840550121 / 50000) (31810631271 / 10000) := by
  exact
    tile 3179648 3183744 7 5 284 1783 22 _ _ (1497227 / 100000) (149723 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3183744 :
    ThetaLowerSegment 3183744 3187840 (31810631271 / 10000) (101924829 / 32) := by
  exact
    tile 3183744 3187840 7 5 273 1784 22 _ _ (299471 / 20000) (748679 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3187840 :
    ThetaLowerSegment 3187840 3191936 (101924829 / 32) (318938878597 / 100000) := by
  exact
    tile 3187840 3191936 7 5 283 1785 22 _ _ (374371 / 25000) (1497487 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3191936 :
    ThetaLowerSegment 3191936 3196032 (318938878597 / 100000) (319346229061 / 100000) := by
  exact
    tile 3191936 3196032 7 5 272 1786 22 _ _ (374403 / 25000) (299523 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3196032 :
    ThetaLowerSegment 3196032 3200128 (319346229061 / 100000) (159886542623 / 50000) := by
  exact
    tile 3196032 3200128 7 5 285 1787 22 _ _ (1497741 / 100000) (93609 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3200128 :
    ThetaLowerSegment 3200128 3204224 (159886542623 / 50000) (40025933407 / 12500) := by
  exact
    tile 3200128 3204224 7 5 290 1788 22 _ _ (1497869 / 100000) (93617 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3204224 :
    ThetaLowerSegment 3204224 3208320 (40025933407 / 12500) (320610428449 / 100000) := by
  exact
    tile 3204224 3208320 7 5 269 1790 22 _ _ (1497997 / 100000) (749 / 50) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3208320 :
    ThetaLowerSegment 3208320 3212416 (320610428449 / 100000) (321046382533 / 100000) := by
  exact
    tile 3208320 3212416 7 5 291 1791 22 _ _ (374531 / 25000) (1498127 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3212416 :
    ThetaLowerSegment 3212416 3216512 (321046382533 / 100000) (321455405329 / 100000) := by
  exact
    tile 3212416 3216512 7 5 273 1792 22 _ _ (374563 / 25000) (299651 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3216512 :
    ThetaLowerSegment 3216512 3220608 (321455405329 / 100000) (160930733019 / 50000) := by
  exact
    tile 3216512 3220608 7 5 271 1793 22 _ _ (1498379 / 100000) (749191 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3220608 :
    ThetaLowerSegment 3220608 3224704 (160930733019 / 50000) (64453512287 / 20000) := by
  exact
    tile 3220608 3224704 7 5 271 1794 22 _ _ (1498507 / 100000) (149851 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3224704 :
    ThetaLowerSegment 3224704 3228800 (64453512287 / 20000) (64535937157 / 20000) := by
  exact
    tile 3224704 3228800 7 5 275 1795 22 _ _ (749317 / 50000) (1498637 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3228800 :
    ThetaLowerSegment 3228800 3232896 (64535937157 / 20000) (161547421291 / 50000) := by
  exact
    tile 3228800 3232896 7 5 277 1796 22 _ _ (1498761 / 100000) (374691 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3232896 :
    ThetaLowerSegment 3232896 3236992 (161547421291 / 50000) (40440440533 / 12500) := by
  exact
    tile 3232896 3236992 7 5 286 1798 22 _ _ (1498887 / 100000) (149889 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3236992 :
    ThetaLowerSegment 3236992 3241088 (40440440533 / 12500) (80982064511 / 25000) := by
  exact
    tile 3236992 3241088 7 5 270 1799 22 _ _ (749507 / 50000) (1499017 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3241088 :
    ThetaLowerSegment 3241088 3245184 (80982064511 / 25000) (10135172817 / 3125) := by
  exact
    tile 3241088 3245184 7 5 265 1800 22 _ _ (74957 / 5000) (1499143 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3245184 :
    ThetaLowerSegment 3245184 3249280 (10135172817 / 3125) (162368164651 / 50000) := by
  exact
    tile 3245184 3249280 7 5 274 1801 22 _ _ (1499267 / 100000) (149927 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3249280 :
    ThetaLowerSegment 3249280 3253376 (162368164651 / 50000) (162572082099 / 50000) := by
  exact
    tile 3249280 3253376 7 5 272 1802 22 _ _ (1499393 / 100000) (374849 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3253376 :
    ThetaLowerSegment 3253376 3257472 (162572082099 / 50000) (32554603529 / 10000) := by
  exact
    tile 3253376 3257472 7 5 268 1803 22 _ _ (1499519 / 100000) (749761 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3257472 :
    ThetaLowerSegment 3257472 3261568 (32554603529 / 10000) (65195286681 / 20000) := by
  exact
    tile 3257472 3261568 7 5 287 1804 22 _ _ (299929 / 20000) (46864 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3261568 :
    ThetaLowerSegment 3261568 3265664 (65195286681 / 20000) (65274474537 / 20000) := by
  exact
    tile 3261568 3265664 7 5 264 1805 22 _ _ (149977 / 10000) (1499773 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3265664 :
    ThetaLowerSegment 3265664 3269760 (65274474537 / 20000) (326789343773 / 100000) := by
  exact
    tile 3265664 3269760 7 5 278 1807 22 _ _ (187487 / 12500) (1499899 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3269760 :
    ThetaLowerSegment 3269760 3273856 (326789343773 / 100000) (327179349233 / 100000) := by
  exact
    tile 3269760 3273856 7 5 260 1808 22 _ _ (1500021 / 100000) (187503 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3273856 :
    ThetaLowerSegment 3273856 3277952 (327179349233 / 100000) (327621892303 / 100000) := by
  exact
    tile 3273856 3277952 7 5 295 1809 22 _ _ (750073 / 50000) (1500149 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3277952 :
    ThetaLowerSegment 3277952 3282048 (327621892303 / 100000) (65602992661 / 20000) := by
  exact
    tile 3277952 3282048 7 5 262 1810 22 _ _ (1500271 / 100000) (750137 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3282048 :
    ThetaLowerSegment 3282048 3286144 (65602992661 / 20000) (328423071017 / 100000) := by
  exact
    tile 3282048 3286144 7 5 272 1811 22 _ _ (375099 / 25000) (1500399 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3286144 :
    ThetaLowerSegment 3286144 3290240 (328423071017 / 100000) (164425359751 / 50000) := by
  exact
    tile 3286144 3290240 7 5 285 1812 22 _ _ (1500521 / 100000) (375131 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3290240 :
    ThetaLowerSegment 3290240 3294336 (164425359751 / 50000) (82310597027 / 25000) := by
  exact
    tile 3290240 3294336 7 5 261 1813 22 _ _ (750323 / 50000) (1500649 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3294336 :
    ThetaLowerSegment 3294336 3298432 (82310597027 / 25000) (164827549929 / 50000) := by
  exact
    tile 3294336 3298432 7 5 275 1815 22 _ _ (150077 / 10000) (1500773 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3298432 :
    ThetaLowerSegment 3298432 3302528 (164827549929 / 50000) (165018163467 / 50000) := by
  exact
    tile 3298432 3302528 7 5 254 1816 22 _ _ (750447 / 50000) (1500897 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3302528 :
    ThetaLowerSegment 3302528 3306624 (165018163467 / 50000) (165228305987 / 50000) := by
  exact
    tile 3302528 3306624 7 5 280 1817 22 _ _ (750509 / 50000) (1501021 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3306624 :
    ThetaLowerSegment 3306624 3310720 (165228305987 / 50000) (165430960157 / 50000) := by
  exact
    tile 3306624 3310720 7 5 270 1818 22 _ _ (750571 / 50000) (300229 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3310720 :
    ThetaLowerSegment 3310720 3314816 (165430960157 / 50000) (41410096691 / 12500) := by
  exact
    tile 3310720 3314816 7 5 279 1819 22 _ _ (750633 / 50000) (1501269 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3314816 :
    ThetaLowerSegment 3314816 3318912 (41410096691 / 12500) (165840822329 / 50000) := by
  exact
    tile 3314816 3318912 7 5 267 1820 22 _ _ (150139 / 10000) (1501393 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3318912 :
    ThetaLowerSegment 3318912 3323008 (165840822329 / 50000) (66420113357 / 20000) := by
  exact
    tile 3318912 3323008 7 5 279 1821 22 _ _ (1501513 / 100000) (375379 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3323008 :
    ThetaLowerSegment 3323008 3327104 (66420113357 / 20000) (166255256843 / 50000) := by
  exact
    tile 3323008 3327104 7 5 273 1822 22 _ _ (1501637 / 100000) (37541 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3327104 :
    ThetaLowerSegment 3327104 3331200 (166255256843 / 50000) (166461748843 / 50000) := by
  exact
    tile 3327104 3331200 7 5 275 1824 22 _ _ (9386 / 625) (1501763 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3331200 :
    ThetaLowerSegment 3331200 3335296 (166461748843 / 50000) (333306477851 / 100000) := by
  exact
    tile 3331200 3335296 7 5 255 1825 22 _ _ (1501883 / 100000) (750943 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3335296 :
    ThetaLowerSegment 3335296 3339392 (333306477851 / 100000) (333715023483 / 100000) := by
  exact
    tile 3335296 3339392 7 5 272 1826 22 _ _ (751003 / 50000) (1502009 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3339392 :
    ThetaLowerSegment 3339392 3343488 (333715023483 / 100000) (334150640603 / 100000) := by
  exact
    tile 3339392 3343488 7 5 290 1827 22 _ _ (93883 / 6250) (1502131 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3343488 :
    ThetaLowerSegment 3343488 3347584 (334150640603 / 100000) (33453671911 / 10000) := by
  exact
    tile 3343488 3347584 7 5 257 1828 22 _ _ (1502251 / 100000) (751127 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3347584 :
    ThetaLowerSegment 3347584 3351680 (33453671911 / 10000) (334961890669 / 100000) := by
  exact
    tile 3347584 3351680 7 5 283 1829 22 _ _ (1502373 / 100000) (187797 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3351680 :
    ThetaLowerSegment 3351680 3355776 (334961890669 / 100000) (67069305929 / 20000) := by
  exact
    tile 3351680 3355776 7 5 256 1830 22 _ _ (46953 / 3125) (1502499 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3355776 :
    ThetaLowerSegment 3355776 3359872 (67069305929 / 20000) (335716173673 / 100000) := by
  exact
    tile 3355776 3359872 7 5 246 1831 22 _ _ (751309 / 50000) (1502621 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3359872 :
    ThetaLowerSegment 3359872 3363968 (335716173673 / 100000) (336109891553 / 100000) := by
  exact
    tile 3359872 3363968 7 5 262 1832 22 _ _ (75137 / 5000) (1502743 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3363968 :
    ThetaLowerSegment 3363968 3368064 (336109891553 / 100000) (336563755877 / 100000) := by
  exact
    tile 3363968 3368064 7 5 302 1834 22 _ _ (751431 / 50000) (300573 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3368064 :
    ThetaLowerSegment 3368064 3372160 (336563755877 / 100000) (336975573219 / 100000) := by
  exact
    tile 3368064 3372160 7 5 274 1835 22 _ _ (1502983 / 100000) (751493 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3372160 :
    ThetaLowerSegment 3372160 3376256 (336975573219 / 100000) (337369386729 / 100000) := by
  exact
    tile 3372160 3376256 7 5 262 1836 22 _ _ (300621 / 20000) (375777 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3376256 :
    ThetaLowerSegment 3376256 3380352 (337369386729 / 100000) (337788786783 / 100000) := by
  exact
    tile 3376256 3380352 7 5 279 1837 22 _ _ (751613 / 50000) (1503229 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3380352 :
    ThetaLowerSegment 3380352 3384448 (337788786783 / 100000) (338190180699 / 100000) := by
  exact
    tile 3380352 3384448 7 5 267 1838 22 _ _ (375837 / 25000) (1503351 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3384448 :
    ThetaLowerSegment 3384448 3388544 (338190180699 / 100000) (84657674279 / 25000) := by
  exact
    tile 3384448 3388544 7 5 293 1839 22 _ _ (1503469 / 100000) (93967 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3388544 :
    ThetaLowerSegment 3388544 3392640 (84657674279 / 25000) (84755407629 / 25000) := by
  exact
    tile 3388544 3392640 7 5 260 1840 22 _ _ (150359 / 10000) (1503593 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3392640 :
    ThetaLowerSegment 3392640 3396736 (84755407629 / 25000) (169722086513 / 50000) := by
  exact
    tile 3392640 3396736 7 5 281 1841 22 _ _ (150371 / 10000) (1503713 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3396736 :
    ThetaLowerSegment 3396736 3400832 (169722086513 / 50000) (339839680579 / 100000) := by
  exact
    tile 3396736 3400832 7 5 263 1843 22 _ _ (1503831 / 100000) (751917 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3400832 :
    ThetaLowerSegment 3400832 3404928 (339839680579 / 100000) (340292370131 / 100000) := by
  exact
    tile 3400832 3404928 7 5 301 1844 22 _ _ (93997 / 6250) (300791 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3404928 :
    ThetaLowerSegment 3404928 3409024 (340292370131 / 100000) (340680420707 / 100000) := by
  exact
    tile 3404928 3409024 7 5 258 1845 22 _ _ (188009 / 12500) (60163 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3409024 :
    ThetaLowerSegment 3409024 3413120 (340680420707 / 100000) (341119644771 / 100000) := by
  exact
    tile 3409024 3413120 7 5 292 1846 22 _ _ (47006 / 3125) (300839 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3413120 :
    ThetaLowerSegment 3413120 3417216 (341119644771 / 100000) (341515278827 / 100000) := by
  exact
    tile 3413120 3417216 7 5 263 1847 22 _ _ (188039 / 12500) (300863 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3417216 :
    ThetaLowerSegment 3417216 3421312 (341515278827 / 100000) (341921475467 / 100000) := by
  exact
    tile 3417216 3421312 7 5 270 1848 22 _ _ (94027 / 6250) (300887 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3421312 :
    ThetaLowerSegment 3421312 3425408 (341921475467 / 100000) (68466744543 / 20000) := by
  exact
    tile 3421312 3425408 7 5 274 1849 22 _ _ (188069 / 12500) (300911 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3425408 :
    ThetaLowerSegment 3425408 3429504 (68466744543 / 20000) (342746002843 / 100000) := by
  exact
    tile 3425408 3429504 7 5 274 1850 22 _ _ (47021 / 3125) (60187 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3429504 :
    ThetaLowerSegment 3429504 3433600 (342746002843 / 100000) (343167344323 / 100000) := by
  exact
    tile 3429504 3433600 7 5 280 1851 22 _ _ (1504791 / 100000) (752397 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3433600 :
    ThetaLowerSegment 3433600 3437696 (343167344323 / 100000) (343588719123 / 100000) := by
  exact
    tile 3433600 3437696 7 5 280 1852 22 _ _ (150491 / 10000) (1504913 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3437696 :
    ThetaLowerSegment 3437696 3441792 (343588719123 / 100000) (343998087283 / 100000) := by
  exact
    tile 3437696 3441792 7 5 272 1854 22 _ _ (150503 / 10000) (1505033 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3441792 :
    ThetaLowerSegment 3441792 3445888 (343998087283 / 100000) (172218042821 / 50000) := by
  exact
    tile 3441792 3445888 7 5 291 1855 22 _ _ (1505149 / 100000) (47036 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3445888 :
    ThetaLowerSegment 3445888 3449984 (172218042821 / 50000) (172416738197 / 50000) := by
  exact
    tile 3445888 3449984 7 5 264 1856 22 _ _ (376317 / 25000) (1505271 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3449984 :
    ThetaLowerSegment 3449984 3454080 (172416738197 / 50000) (2157636664 / 625) := by
  exact
    tile 3449984 3454080 7 5 258 1857 22 _ _ (1505387 / 100000) (150539 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3454080 :
    ThetaLowerSegment 3454080 3458176 (2157636664 / 625) (69126573821 / 20000) := by
  exact
    tile 3454080 3458176 7 5 273 1858 22 _ _ (301101 / 20000) (376377 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3458176 :
    ThetaLowerSegment 3458176 3462272 (69126573821 / 20000) (346025836969 / 100000) := by
  exact
    tile 3458176 3462272 7 5 261 1859 22 _ _ (188203 / 12500) (1505627 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3462272 :
    ThetaLowerSegment 3462272 3466368 (346025836969 / 100000) (346427870083 / 100000) := by
  exact
    tile 3462272 3466368 7 5 267 1860 22 _ _ (752871 / 50000) (301149 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3466368 :
    ThetaLowerSegment 3466368 3470464 (346427870083 / 100000) (346837464003 / 100000) := by
  exact
    tile 3466368 3470464 7 5 272 1861 22 _ _ (75293 / 5000) (1505863 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3470464 :
    ThetaLowerSegment 3470464 3474560 (346837464003 / 100000) (347248595997 / 100000) := by
  exact
    tile 3470464 3474560 7 5 273 1862 22 _ _ (752989 / 50000) (1505981 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3474560 :
    ThetaLowerSegment 3474560 3478656 (347248595997 / 100000) (347617589517 / 100000) := by
  exact
    tile 3474560 3478656 7 5 245 1864 22 _ _ (94131 / 6250) (1506099 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3478656 :
    ThetaLowerSegment 3478656 3482752 (347617589517 / 100000) (348016736227 / 100000) := by
  exact
    tile 3478656 3482752 7 5 265 1865 22 _ _ (753107 / 50000) (1506217 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3482752 :
    ThetaLowerSegment 3482752 3486848 (348016736227 / 100000) (69681375243 / 20000) := by
  exact
    tile 3482752 3486848 7 5 259 1866 22 _ _ (376583 / 25000) (301267 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3486848 :
    ThetaLowerSegment 3486848 3490944 (69681375243 / 20000) (87200014851 / 25000) := by
  exact
    tile 3486848 3490944 7 5 261 1867 22 _ _ (1506449 / 100000) (376613 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3490944 :
    ThetaLowerSegment 3490944 3495040 (87200014851 / 25000) (349232444133 / 100000) := by
  exact
    tile 3490944 3495040 7 5 287 1868 22 _ _ (1506567 / 100000) (150657 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3495040 :
    ThetaLowerSegment 3495040 3499136 (349232444133 / 100000) (349618155237 / 100000) := by
  exact
    tile 3495040 3499136 7 5 256 1869 22 _ _ (376671 / 25000) (1506687 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3499136 :
    ThetaLowerSegment 3499136 3503232 (349618155237 / 100000) (175005715149 / 50000) := by
  exact
    tile 3499136 3503232 7 5 261 1870 22 _ _ (1506801 / 100000) (376701 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3503232 :
    ThetaLowerSegment 3503232 3507328 (175005715149 / 50000) (175213669833 / 50000) := by
  exact
    tile 3503232 3507328 7 5 276 1871 22 _ _ (753459 / 50000) (1506921 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3507328 :
    ThetaLowerSegment 3507328 3511424 (175213669833 / 50000) (350838760221 / 100000) := by
  exact
    tile 3507328 3511424 7 5 273 1872 22 _ _ (301407 / 20000) (753519 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3511424 :
    ThetaLowerSegment 3511424 3515520 (350838760221 / 100000) (351265284237 / 100000) := by
  exact
    tile 3511424 3515520 7 5 283 1873 22 _ _ (94197 / 6250) (301431 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3515520 :
    ThetaLowerSegment 3515520 3519616 (351265284237 / 100000) (351655666649 / 100000) := by
  exact
    tile 3515520 3519616 7 5 259 1874 22 _ _ (376817 / 25000) (1507271 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3519616 :
    ThetaLowerSegment 3519616 3523712 (351655666649 / 100000) (352050601519 / 100000) := by
  exact
    tile 3519616 3523712 7 5 262 1876 22 _ _ (301477 / 20000) (376847 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3523712 :
    ThetaLowerSegment 3523712 3527808 (352050601519 / 100000) (352430491771 / 100000) := by
  exact
    tile 3523712 3527808 7 5 252 1877 22 _ _ (1507501 / 100000) (94219 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3527808 :
    ThetaLowerSegment 3527808 3531904 (352430491771 / 100000) (352846594063 / 100000) := by
  exact
    tile 3527808 3531904 7 5 276 1878 22 _ _ (1507617 / 100000) (75381 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3531904 :
    ThetaLowerSegment 3531904 3536000 (352846594063 / 100000) (70654958047 / 20000) := by
  exact
    tile 3531904 3536000 7 5 284 1879 22 _ _ (1507733 / 100000) (188467 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3536000 :
    ThetaLowerSegment 3536000 3540096 (70654958047 / 20000) (70730350497 / 20000) := by
  exact
    tile 3536000 3540096 7 5 250 1880 22 _ _ (1507849 / 100000) (376963 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3540096 :
    ThetaLowerSegment 3540096 3544192 (70730350497 / 20000) (70811177421 / 20000) := by
  exact
    tile 3540096 3544192 7 5 268 1881 22 _ _ (301593 / 20000) (47124 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3544192 :
    ThetaLowerSegment 3544192 3548288 (70811177421 / 20000) (177239828933 / 50000) := by
  exact
    tile 3544192 3548288 7 5 281 1882 22 _ _ (1508081 / 100000) (377021 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3548288 :
    ThetaLowerSegment 3548288 3552384 (177239828933 / 50000) (177432123923 / 50000) := by
  exact
    tile 3548288 3552384 7 5 255 1883 22 _ _ (377049 / 25000) (1508199 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3552384 :
    ThetaLowerSegment 3552384 3556480 (177432123923 / 50000) (17763876253 / 5000) := by
  exact
    tile 3552384 3556480 7 5 274 1884 22 _ _ (1508311 / 100000) (754157 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3556480 :
    ThetaLowerSegment 3556480 3560576 (17763876253 / 5000) (17784994231 / 5000) := by
  exact
    tile 3556480 3560576 7 5 280 1885 22 _ _ (1508427 / 100000) (150843 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3560576 :
    ThetaLowerSegment 3560576 3564672 (17784994231 / 5000) (178048315583 / 50000) := by
  exact
    tile 3560576 3564672 7 5 263 1886 22 _ _ (754271 / 50000) (301709 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3564672 :
    ThetaLowerSegment 3564672 3568768 (178048315583 / 50000) (356523581097 / 100000) := by
  exact
    tile 3564672 3568768 7 5 283 1888 22 _ _ (1508657 / 100000) (75433 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3568768 :
    ThetaLowerSegment 3568768 3572864 (356523581097 / 100000) (356923405677 / 100000) := by
  exact
    tile 3568768 3572864 7 5 265 1889 22 _ _ (377193 / 25000) (60351 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3572864 :
    ThetaLowerSegment 3572864 3576960 (356923405677 / 100000) (357329296011 / 100000) := by
  exact
    tile 3572864 3576960 7 5 269 1890 22 _ _ (754443 / 50000) (1508889 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3576960 :
    ThetaLowerSegment 3576960 3581056 (357329296011 / 100000) (178863081637 / 50000) := by
  exact
    tile 3576960 3581056 7 5 263 1891 22 _ _ (1509001 / 100000) (377251 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3581056 :
    ThetaLowerSegment 3581056 3585152 (178863081637 / 50000) (179068321277 / 50000) := by
  exact
    tile 3581056 3585152 7 5 272 1892 22 _ _ (301823 / 20000) (754559 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3585152 :
    ThetaLowerSegment 3585152 3589248 (179068321277 / 50000) (179279613477 / 50000) := by
  exact
    tile 3585152 3589248 7 5 280 1893 22 _ _ (150923 / 10000) (1509233 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3589248 :
    ThetaLowerSegment 3589248 3593344 (179279613477 / 50000) (179470545493 / 50000) := by
  exact
    tile 3589248 3593344 7 5 253 1894 22 _ _ (47167 / 3125) (1509347 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3593344 :
    ThetaLowerSegment 3593344 3597440 (179470545493 / 50000) (179689416903 / 50000) := by
  exact
    tile 3593344 3597440 7 5 290 1895 22 _ _ (754729 / 50000) (1509461 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3597440 :
    ThetaLowerSegment 3597440 3601536 (179689416903 / 50000) (179900002197 / 50000) := by
  exact
    tile 3597440 3601536 7 5 279 1896 22 _ _ (377393 / 25000) (60383 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3601536 :
    ThetaLowerSegment 3601536 3605632 (179900002197 / 50000) (90050772639 / 25000) := by
  exact
    tile 3601536 3605632 7 5 267 1897 22 _ _ (754843 / 50000) (1509689 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3605632 :
    ThetaLowerSegment 3605632 3609728 (90050772639 / 25000) (45080493983 / 12500) := by
  exact
    tile 3605632 3609728 7 5 292 1898 22 _ _ (1509799 / 100000) (754901 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3609728 :
    ThetaLowerSegment 3609728 3613824 (45080493983 / 12500) (180537893491 / 50000) := by
  exact
    tile 3609728 3613824 7 5 286 1899 22 _ _ (1509913 / 100000) (377479 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3613824 :
    ThetaLowerSegment 3613824 3617920 (180537893491 / 50000) (45186758023 / 12500) := by
  exact
    tile 3613824 3617920 7 5 277 1901 22 _ _ (755013 / 50000) (1510029 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3617920 :
    ThetaLowerSegment 3617920 3622016 (45186758023 / 12500) (14476011663 / 4000) := by
  exact
    tile 3617920 3622016 7 5 269 1902 22 _ _ (1510139 / 100000) (755071 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3622016 :
    ThetaLowerSegment 3622016 3626112 (14476011663 / 4000) (362326182921 / 100000) := by
  exact
    tile 3622016 3626112 7 5 282 1903 22 _ _ (1510253 / 100000) (94391 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3626112 :
    ThetaLowerSegment 3626112 3630208 (362326182921 / 100000) (362744554303 / 100000) := by
  exact
    tile 3626112 3630208 7 5 277 1904 22 _ _ (755183 / 50000) (1510369 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3630208 :
    ThetaLowerSegment 3630208 3634304 (362744554303 / 100000) (363161446507 / 100000) := by
  exact
    tile 3630208 3634304 7 5 276 1905 22 _ _ (1510479 / 100000) (755241 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3634304 :
    ThetaLowerSegment 3634304 3638400 (363161446507 / 100000) (363548157803 / 100000) := by
  exact
    tile 3634304 3638400 7 5 256 1906 22 _ _ (1510591 / 100000) (755297 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3638400 :
    ThetaLowerSegment 3638400 3642496 (363548157803 / 100000) (72792115999 / 20000) := by
  exact
    tile 3638400 3642496 7 5 273 1907 22 _ _ (94419 / 6250) (1510707 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3642496 :
    ThetaLowerSegment 3642496 3646592 (72792115999 / 20000) (72872189247 / 20000) := by
  exact
    tile 3642496 3646592 7 5 265 1908 22 _ _ (47213 / 3125) (1510819 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3646592 :
    ThetaLowerSegment 3646592 3650688 (72872189247 / 20000) (364747744059 / 100000) := by
  exact
    tile 3646592 3650688 7 5 256 1909 22 _ _ (1510929 / 100000) (377733 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3650688 :
    ThetaLowerSegment 3650688 3654784 (364747744059 / 100000) (365116438063 / 100000) := by
  exact
    tile 3650688 3654784 7 5 244 1910 22 _ _ (1511041 / 100000) (377761 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3654784 :
    ThetaLowerSegment 3654784 3658880 (365116438063 / 100000) (365557694739 / 100000) := by
  exact
    tile 3654784 3658880 7 5 292 1911 22 _ _ (1511153 / 100000) (377789 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3658880 :
    ThetaLowerSegment 3658880 3662976 (365557694739 / 100000) (91486522461 / 25000) := by
  exact
    tile 3658880 3662976 7 5 257 1912 22 _ _ (302253 / 20000) (377817 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3662976 :
    ThetaLowerSegment 3662976 3667072 (91486522461 / 25000) (7327325053 / 2000) := by
  exact
    tile 3662976 3667072 7 5 278 1913 22 _ _ (1511377 / 100000) (75569 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3667072 :
    ThetaLowerSegment 3667072 3671168 (7327325053 / 2000) (366775866169 / 100000) := by
  exact
    tile 3667072 3671168 7 5 271 1914 22 _ _ (1511489 / 100000) (377873 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3671168 :
    ThetaLowerSegment 3671168 3675264 (366775866169 / 100000) (367190044843 / 100000) := by
  exact
    tile 3671168 3675264 7 5 274 1916 22 _ _ (1511601 / 100000) (377901 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3675264 :
    ThetaLowerSegment 3675264 3679360 (367190044843 / 100000) (367654140427 / 100000) := by
  exact
    tile 3675264 3679360 7 5 307 1917 22 _ _ (47241 / 3125) (302343 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3679360 :
    ThetaLowerSegment 3679360 3683456 (367654140427 / 100000) (184021339469 / 50000) := by
  exact
    tile 3679360 3683456 7 5 257 1918 22 _ _ (1511823 / 100000) (755913 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3683456 :
    ThetaLowerSegment 3683456 3687552 (184021339469 / 50000) (368443341713 / 100000) := by
  exact
    tile 3683456 3687552 7 5 265 1919 22 _ _ (302387 / 20000) (755969 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3687552 :
    ThetaLowerSegment 3687552 3691648 (368443341713 / 100000) (73772435691 / 20000) := by
  exact
    tile 3687552 3691648 7 5 277 1920 22 _ _ (756023 / 50000) (1512049 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3691648 :
    ThetaLowerSegment 3691648 3695744 (73772435691 / 20000) (36927802163 / 10000) := by
  exact
    tile 3691648 3695744 7 5 275 1921 22 _ _ (1512157 / 100000) (9451 / 625) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3695744 :
    ThetaLowerSegment 3695744 3699840 (36927802163 / 10000) (184849972201 / 50000) := by
  exact
    tile 3695744 3699840 7 5 279 1922 22 _ _ (378067 / 25000) (1512271 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3699840 :
    ThetaLowerSegment 3699840 3703936 (184849972201 / 50000) (92527071683 / 25000) := by
  exact
    tile 3699840 3703936 7 5 270 1923 22 _ _ (1512379 / 100000) (756191 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3703936 :
    ThetaLowerSegment 3703936 3708032 (92527071683 / 25000) (370509096317 / 100000) := by
  exact
    tile 3703936 3708032 7 5 265 1924 22 _ _ (1512489 / 100000) (378123 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3708032 :
    ThetaLowerSegment 3708032 3712128 (370509096317 / 100000) (370908422717 / 100000) := by
  exact
    tile 3708032 3712128 7 5 264 1925 22 _ _ (7563 / 500) (1512603 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3712128 :
    ThetaLowerSegment 3712128 3716224 (370908422717 / 100000) (371324417967 / 100000) := by
  exact
    tile 3712128 3716224 7 5 275 1926 22 _ _ (151271 / 10000) (1512713 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3716224 :
    ThetaLowerSegment 3716224 3720320 (371324417967 / 100000) (371743469107 / 100000) := by
  exact
    tile 3716224 3720320 7 5 277 1927 22 _ _ (75641 / 5000) (1512823 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3720320 :
    ThetaLowerSegment 3720320 3724416 (371743469107 / 100000) (93039881283 / 25000) := by
  exact
    tile 3720320 3724416 7 5 275 1928 22 _ _ (1512931 / 100000) (756467 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3724416 :
    ThetaLowerSegment 3724416 3728512 (93039881283 / 25000) (18629764047 / 5000) := by
  exact
    tile 3724416 3728512 7 5 288 1929 22 _ _ (1513041 / 100000) (378261 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3728512 :
    ThetaLowerSegment 3728512 3732608 (18629764047 / 5000) (4662850523 / 1250) := by
  exact
    tile 3728512 3732608 7 5 286 1930 22 _ _ (30263 / 2000) (1513153 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3732608 :
    ThetaLowerSegment 3732608 3736704 (4662850523 / 1250) (373430569 / 100) := by
  exact
    tile 3732608 3736704 7 5 266 1931 22 _ _ (75663 / 5000) (1513263 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3736704 :
    ThetaLowerSegment 3736704 3740800 (373430569 / 100) (37382253183 / 10000) := by
  exact
    tile 3736704 3740800 7 5 259 1933 22 _ _ (151337 / 10000) (1513373 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3740800 :
    ThetaLowerSegment 3740800 3744896 (37382253183 / 10000) (37421906359 / 10000) := by
  exact
    tile 3740800 3744896 7 5 262 1934 22 _ _ (37837 / 2500) (1513483 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3744896 :
    ThetaLowerSegment 3744896 3748992 (37421906359 / 10000) (374638327743 / 100000) := by
  exact
    tile 3744896 3748992 7 5 277 1935 22 _ _ (1513589 / 100000) (189199 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3748992 :
    ThetaLowerSegment 3748992 3753088 (374638327743 / 100000) (375057622089 / 100000) := by
  exact
    tile 3748992 3753088 7 5 277 1936 22 _ _ (756849 / 50000) (1513701 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3753088 :
    ThetaLowerSegment 3753088 3757184 (375057622089 / 100000) (375481488049 / 100000) := by
  exact
    tile 3753088 3757184 7 5 280 1937 22 _ _ (1513807 / 100000) (151381 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3757184 :
    ThetaLowerSegment 3757184 3761280 (375481488049 / 100000) (75171387893 / 20000) := by
  exact
    tile 3757184 3761280 7 5 248 1938 22 _ _ (1513917 / 100000) (9462 / 625) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3761280 :
    ThetaLowerSegment 3761280 3765376 (75171387893 / 20000) (75247694753 / 20000) := by
  exact
    tile 3761280 3765376 7 5 252 1939 22 _ _ (60561 / 4000) (378507 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3765376 :
    ThetaLowerSegment 3765376 3769472 (75247694753 / 20000) (376650318213 / 100000) := by
  exact
    tile 3765376 3769472 7 5 272 1940 22 _ _ (757067 / 50000) (1514137 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3769472 :
    ThetaLowerSegment 3769472 3773568 (376650318213 / 100000) (7540850143 / 2000) := by
  exact
    tile 3769472 3773568 7 5 259 1941 22 _ _ (1514243 / 100000) (757123 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3773568 :
    ThetaLowerSegment 3773568 3777664 (7540850143 / 2000) (188731748503 / 50000) := by
  exact
    tile 3773568 3777664 7 5 278 1942 22 _ _ (94647 / 6250) (302871 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3777664 :
    ThetaLowerSegment 3777664 3781760 (188731748503 / 50000) (188933171683 / 50000) := by
  exact
    tile 3777664 3781760 7 5 266 1943 22 _ _ (75723 / 5000) (1514463 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3781760 :
    ThetaLowerSegment 3781760 3785856 (188933171683 / 50000) (189139153067 / 50000) := by
  exact
    tile 3781760 3785856 7 5 272 1944 22 _ _ (1514569 / 100000) (378643 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3785856 :
    ThetaLowerSegment 3785856 3789952 (189139153067 / 50000) (189345149139 / 50000) := by
  exact
    tile 3785856 3789952 7 5 272 1945 22 _ _ (1514677 / 100000) (37867 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3789952 :
    ThetaLowerSegment 3789952 3794048 (189345149139 / 50000) (379085657163 / 100000) := by
  exact
    tile 3789952 3794048 7 5 261 1946 22 _ _ (302957 / 20000) (378697 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3794048 :
    ThetaLowerSegment 3794048 3798144 (379085657163 / 100000) (379494678273 / 100000) := by
  exact
    tile 3794048 3798144 7 5 270 1947 22 _ _ (1514893 / 100000) (94681 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3798144 :
    ThetaLowerSegment 3798144 3802240 (379494678273 / 100000) (379912818549 / 100000) := by
  exact
    tile 3798144 3802240 7 5 276 1948 22 _ _ (1515001 / 100000) (378751 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3802240 :
    ThetaLowerSegment 3802240 3806336 (379912818549 / 100000) (9508388349 / 2500) := by
  exact
    tile 3802240 3806336 7 5 279 1949 22 _ _ (1515109 / 100000) (189389 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3806336 :
    ThetaLowerSegment 3806336 3810432 (9508388349 / 2500) (47591943873 / 12500) := by
  exact
    tile 3806336 3810432 7 5 264 1950 22 _ _ (94701 / 6250) (1515219 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3810432 :
    ThetaLowerSegment 3810432 3814528 (47591943873 / 12500) (19057158657 / 5000) := by
  exact
    tile 3810432 3814528 7 5 269 1952 22 _ _ (378831 / 25000) (1515327 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3814528 :
    ThetaLowerSegment 3814528 3818624 (19057158657 / 5000) (190794354927 / 50000) := by
  exact
    tile 3814528 3818624 7 5 294 1953 22 _ _ (1515431 / 100000) (757717 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3818624 :
    ThetaLowerSegment 3818624 3822720 (190794354927 / 50000) (191006530387 / 50000) := by
  exact
    tile 3818624 3822720 7 5 280 1954 22 _ _ (1515539 / 100000) (757771 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3822720 :
    ThetaLowerSegment 3822720 3826816 (191006530387 / 50000) (11950175409 / 3125) := by
  exact
    tile 3822720 3826816 7 5 259 1955 22 _ _ (757823 / 50000) (1515649 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3826816 :
    ThetaLowerSegment 3826816 3830912 (11950175409 / 3125) (191419559223 / 50000) := by
  exact
    tile 3826816 3830912 7 5 286 1956 22 _ _ (1515753 / 100000) (378939 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3830912 :
    ThetaLowerSegment 3830912 3835008 (191419559223 / 50000) (191607525863 / 50000) := by
  exact
    tile 3830912 3835008 7 5 248 1957 22 _ _ (75793 / 5000) (1515863 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3835008 :
    ThetaLowerSegment 3835008 3839104 (191607525863 / 50000) (383625878783 / 100000) := by
  exact
    tile 3835008 3839104 7 5 271 1958 22 _ _ (1515967 / 100000) (151597 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3839104 :
    ThetaLowerSegment 3839104 3843200 (383625878783 / 100000) (384062507807 / 100000) := by
  exact
    tile 3839104 3843200 7 5 288 1959 22 _ _ (1516073 / 100000) (379019 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3843200 :
    ThetaLowerSegment 3843200 3847296 (384062507807 / 100000) (384462779327 / 100000) := by
  exact
    tile 3843200 3847296 7 5 264 1960 22 _ _ (75809 / 5000) (1516183 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3847296 :
    ThetaLowerSegment 3847296 3851392 (384462779327 / 100000) (38487066053 / 10000) := by
  exact
    tile 3847296 3851392 7 5 269 1961 22 _ _ (1516287 / 100000) (151629 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3851392 :
    ThetaLowerSegment 3851392 3855488 (38487066053 / 10000) (192635494141 / 50000) := by
  exact
    tile 3851392 3855488 7 5 264 1962 22 _ _ (1516393 / 100000) (379099 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3855488 :
    ThetaLowerSegment 3855488 3859584 (192635494141 / 50000) (385698641 / 100) := by
  exact
    tile 3855488 3859584 7 5 282 1963 22 _ _ (1516499 / 100000) (758251 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3859584 :
    ThetaLowerSegment 3859584 3863680 (385698641 / 100) (77218288339 / 20000) := by
  exact
    tile 3859584 3863680 7 5 259 1964 22 _ _ (303321 / 20000) (47394 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3863680 :
    ThetaLowerSegment 3863680 3867776 (77218288339 / 20000) (386496403799 / 100000) := by
  exact
    tile 3863680 3867776 7 5 267 1965 22 _ _ (189589 / 12500) (303343 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3867776 :
    ThetaLowerSegment 3867776 3871872 (386496403799 / 100000) (77378762023 / 20000) := by
  exact
    tile 3867776 3871872 7 5 262 1966 22 _ _ (758409 / 50000) (1516821 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3871872 :
    ThetaLowerSegment 3871872 3875968 (77378762023 / 20000) (15492135173 / 4000) := by
  exact
    tile 3871872 3875968 7 5 270 1967 22 _ _ (1516923 / 100000) (758463 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3875968 :
    ThetaLowerSegment 3875968 3880064 (15492135173 / 4000) (387706909039 / 100000) := by
  exact
    tile 3875968 3880064 7 5 266 1968 22 _ _ (1517029 / 100000) (189629 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3880064 :
    ThetaLowerSegment 3880064 3884160 (387706909039 / 100000) (194060543447 / 50000) := by
  exact
    tile 3880064 3884160 7 5 273 1969 22 _ _ (303427 / 20000) (758569 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3884160 :
    ThetaLowerSegment 3884160 3888256 (194060543447 / 50000) (194265370847 / 50000) := by
  exact
    tile 3884160 3888256 7 5 270 1970 22 _ _ (37931 / 2500) (1517243 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3888256 :
    ThetaLowerSegment 3888256 3892352 (194265370847 / 50000) (97237002961 / 25000) := by
  exact
    tile 3888256 3892352 7 5 275 1971 22 _ _ (758673 / 50000) (1517349 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3892352 :
    ThetaLowerSegment 3892352 3896448 (97237002961 / 25000) (194694036317 / 50000) := by
  exact
    tile 3892352 3896448 7 5 290 1972 22 _ _ (1517451 / 100000) (758727 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3896448 :
    ThetaLowerSegment 3896448 3900544 (194694036317 / 50000) (38977656697 / 10000) := by
  exact
    tile 3896448 3900544 7 5 256 1973 22 _ _ (379389 / 25000) (1517559 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3900544 :
    ThetaLowerSegment 3900544 3904640 (38977656697 / 10000) (195082544093 / 50000) := by
  exact
    tile 3900544 3904640 7 5 256 1974 22 _ _ (1517661 / 100000) (47427 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3904640 :
    ThetaLowerSegment 3904640 3908736 (195082544093 / 50000) (97648653991 / 25000) := by
  exact
    tile 3904640 3908736 7 5 283 1976 22 _ _ (758883 / 50000) (1517769 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3908736 :
    ThetaLowerSegment 3908736 3912832 (97648653991 / 25000) (195502220567 / 50000) := by
  exact
    tile 3908736 3912832 7 5 270 1977 22 _ _ (1517871 / 100000) (758937 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3912832 :
    ThetaLowerSegment 3912832 3916928 (195502220567 / 50000) (195706388339 / 50000) := by
  exact
    tile 3912832 3916928 7 5 269 1978 22 _ _ (189747 / 12500) (1517979 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3916928 :
    ThetaLowerSegment 3916928 3921024 (195706388339 / 50000) (195909811059 / 50000) := by
  exact
    tile 3916928 3921024 7 5 268 1979 22 _ _ (9488 / 625) (1518083 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell3921024 :
    ThetaLowerSegment 3921024 3925120 (195909811059 / 50000) (392237122993 / 100000) := by
  exact
    tile 3921024 3925120 7 5 275 1980 22 _ _ (303637 / 20000) (379547 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3925120 :
    ThetaLowerSegment 3925120 3929216 (392237122993 / 100000) (392656170757 / 100000) := by
  exact
    tile 3925120 3929216 7 5 276 1981 22 _ _ (1518289 / 100000) (379573 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3929216 :
    ThetaLowerSegment 3929216 3933312 (392656170757 / 100000) (393075247501 / 100000) := by
  exact
    tile 3929216 3933312 7 5 276 1982 22 _ _ (759197 / 50000) (1518397 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3933312 :
    ThetaLowerSegment 3933312 3937408 (393075247501 / 100000) (393471575479 / 100000) := by
  exact
    tile 3933312 3937408 7 5 261 1983 22 _ _ (759249 / 50000) (1518501 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3937408 :
    ThetaLowerSegment 3937408 3941504 (393471575479 / 100000) (78778749367 / 20000) := by
  exact
    tile 3937408 3941504 7 5 278 1984 22 _ _ (759301 / 50000) (303721 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3941504 :
    ThetaLowerSegment 3941504 3945600 (78778749367 / 20000) (394300760043 / 100000) := by
  exact
    tile 3941504 3945600 7 5 268 1985 22 _ _ (759353 / 50000) (1518709 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3945600 :
    ThetaLowerSegment 3945600 3949696 (394300760043 / 100000) (394735139703 / 100000) := by
  exact
    tile 3945600 3949696 7 5 286 1986 22 _ _ (151881 / 10000) (1518813 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3949696 :
    ThetaLowerSegment 3949696 3953792 (394735139703 / 100000) (98779856173 / 25000) := by
  exact
    tile 3949696 3953792 7 5 253 1987 22 _ _ (1518913 / 100000) (379729 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3953792 :
    ThetaLowerSegment 3953792 3957888 (98779856173 / 25000) (197764779641 / 50000) := by
  exact
    tile 3953792 3957888 7 5 270 1988 22 _ _ (1519017 / 100000) (75951 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3957888 :
    ThetaLowerSegment 3957888 3961984 (197764779641 / 50000) (395926049863 / 100000) := by
  exact
    tile 3957888 3961984 7 5 261 1989 22 _ _ (1519121 / 100000) (379781 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3961984 :
    ThetaLowerSegment 3961984 3966080 (395926049863 / 100000) (396308894311 / 100000) := by
  exact
    tile 3961984 3966080 7 5 252 1990 22 _ _ (189903 / 12500) (1519227 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3966080 :
    ThetaLowerSegment 3966080 3970176 (396308894311 / 100000) (198361835291 / 50000) := by
  exact
    tile 3966080 3970176 7 5 273 1991 22 _ _ (1519327 / 100000) (151933 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3970176 :
    ThetaLowerSegment 3970176 3974272 (198361835291 / 50000) (397135436383 / 100000) := by
  exact
    tile 3970176 3974272 7 5 271 1992 22 _ _ (1519431 / 100000) (759717 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3974272 :
    ThetaLowerSegment 3974272 3978368 (397135436383 / 100000) (397570023107 / 100000) := by
  exact
    tile 3974272 3978368 7 5 286 1993 22 _ _ (759767 / 50000) (1519537 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3978368 :
    ThetaLowerSegment 3978368 3982464 (397570023107 / 100000) (198984843819 / 50000) := by
  exact
    tile 3978368 3982464 7 5 263 1994 22 _ _ (1519637 / 100000) (37991 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3982464 :
    ThetaLowerSegment 3982464 3986560 (198984843819 / 50000) (199172531709 / 50000) := by
  exact
    tile 3982464 3986560 7 5 247 1995 22 _ _ (75987 / 5000) (1519743 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3986560 :
    ThetaLowerSegment 3986560 3990656 (199172531709 / 50000) (199371631011 / 50000) := by
  exact
    tile 3986560 3990656 7 5 262 1996 22 _ _ (759921 / 50000) (303969 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3990656 :
    ThetaLowerSegment 3990656 3994752 (199371631011 / 50000) (99788411793 / 25000) := by
  exact
    tile 3990656 3994752 7 5 270 1997 22 _ _ (303989 / 20000) (379987 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3994752 :
    ThetaLowerSegment 3994752 3998848 (99788411793 / 25000) (99887974937 / 25000) := by
  exact
    tile 3994752 3998848 7 5 262 1998 22 _ _ (95003 / 6250) (1520051 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3998848 :
    ThetaLowerSegment 3998848 3999872 (99887974937 / 25000) (199823834599 / 50000) := by
  exact
    tile 3998848 3999872 7 3 63 1999 22 _ _ (30403 / 2000) (1520153 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3999872 :
    ThetaLowerSegment 3999872 4000000 (199823834599 / 50000) (39965831043 / 10000) := by
  exact
    tile 3999872 4000000 7 0 7 1999 22 _ _ (95011 / 6250) (1520179 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2000000_4000000 :
    ThetaLowerSegment 2000000 4000000 (39958899001 / 20000) (39965831043 / 10000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2000000 cell2004096)
                    (ThetaLowerSegment.join cell2008192 cell2012288))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2016384 cell2020480)
                    (ThetaLowerSegment.join cell2024576 cell2028672)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2032768 cell2036864)
                    (ThetaLowerSegment.join cell2040960 cell2045056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2049152 cell2053248)
                    (ThetaLowerSegment.join cell2057344 cell2061440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2065536 cell2069632)
                    (ThetaLowerSegment.join cell2073728 cell2077824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2081920 cell2086016)
                    (ThetaLowerSegment.join cell2090112 cell2094208)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2098304 cell2102400)
                    (ThetaLowerSegment.join cell2106496 cell2110592))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2114688 cell2118784)
                    (ThetaLowerSegment.join cell2122880 cell2126976)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2131072 cell2135168)
                    (ThetaLowerSegment.join cell2139264 cell2143360))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2147456 cell2151552)
                    (ThetaLowerSegment.join cell2155648 cell2159744)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2163840 cell2167936)
                    (ThetaLowerSegment.join cell2172032 cell2176128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2180224 cell2184320)
                    (ThetaLowerSegment.join cell2188416 cell2192512))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2196608 cell2200704)
                    (ThetaLowerSegment.join cell2204800 cell2208896))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2212992 cell2217088)
                    (ThetaLowerSegment.join cell2221184 cell2225280)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2229376 cell2233472)
                    (ThetaLowerSegment.join cell2237568 cell2241664))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2245760 cell2249856)
                    (ThetaLowerSegment.join cell2253952 cell2258048))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2262144 cell2266240)
                    (ThetaLowerSegment.join cell2270336 cell2274432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2278528 cell2282624)
                    (ThetaLowerSegment.join cell2286720 cell2290816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2294912 cell2299008)
                    (ThetaLowerSegment.join cell2303104 cell2307200))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2311296 cell2315392)
                    (ThetaLowerSegment.join cell2319488 cell2323584))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2327680 cell2331776)
                    (ThetaLowerSegment.join cell2335872 cell2339968))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2344064 cell2348160)
                    (ThetaLowerSegment.join cell2352256 cell2356352)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2360448 cell2364544)
                    (ThetaLowerSegment.join cell2368640 cell2372736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2376832 cell2380928)
                    (ThetaLowerSegment.join cell2385024 cell2389120)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2393216 cell2397312)
                    (ThetaLowerSegment.join cell2401408 cell2405504))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2409600 cell2413696)
                    (ThetaLowerSegment.join cell2417792 cell2421888)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2425984 cell2430080)
                    (ThetaLowerSegment.join cell2434176 cell2438272))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2442368 cell2446464)
                    (ThetaLowerSegment.join cell2450560 cell2454656))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2458752 cell2462848)
                    (ThetaLowerSegment.join cell2466944 cell2471040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2475136 cell2479232)
                    (ThetaLowerSegment.join cell2483328 cell2487424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2491520 cell2495616)
                    (ThetaLowerSegment.join cell2499712 cell2503808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2507904 cell2512000)
                    (ThetaLowerSegment.join cell2516096 cell2520192)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2524288 cell2528384)
                    (ThetaLowerSegment.join cell2532480 cell2536576))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2540672 cell2544768)
                    (ThetaLowerSegment.join cell2548864 cell2552960)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2557056 cell2561152)
                    (ThetaLowerSegment.join cell2565248 cell2569344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2573440 cell2577536)
                    (ThetaLowerSegment.join cell2581632 cell2585728))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2589824 cell2593920)
                    (ThetaLowerSegment.join cell2598016 cell2602112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2606208 cell2610304)
                    (ThetaLowerSegment.join cell2614400 cell2618496)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2622592 cell2626688)
                    (ThetaLowerSegment.join cell2630784 cell2634880))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2638976 cell2643072)
                    (ThetaLowerSegment.join cell2647168 cell2651264)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2655360 cell2659456)
                    (ThetaLowerSegment.join cell2663552 cell2667648))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2671744 cell2675840)
                    (ThetaLowerSegment.join cell2679936 cell2684032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2688128 cell2692224)
                    (ThetaLowerSegment.join cell2696320 cell2700416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2704512 cell2708608)
                    (ThetaLowerSegment.join cell2712704 cell2716800))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2720896 cell2724992)
                    (ThetaLowerSegment.join cell2729088 cell2733184))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2737280 cell2741376)
                    (ThetaLowerSegment.join cell2745472 cell2749568)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2753664 cell2757760)
                    (ThetaLowerSegment.join cell2761856 cell2765952))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2770048 cell2774144)
                    (ThetaLowerSegment.join cell2778240 cell2782336))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2786432 cell2790528)
                    (ThetaLowerSegment.join cell2794624 cell2798720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2802816 cell2806912)
                    (ThetaLowerSegment.join cell2811008 cell2815104)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2819200 cell2823296)
                    (ThetaLowerSegment.join cell2827392 cell2831488))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2835584 cell2839680)
                    (ThetaLowerSegment.join cell2843776 cell2847872))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2851968 cell2856064)
                    (ThetaLowerSegment.join cell2860160 cell2864256))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2868352 cell2872448)
                    (ThetaLowerSegment.join cell2876544 cell2880640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2884736 cell2888832)
                    (ThetaLowerSegment.join cell2892928 cell2897024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2901120 cell2905216)
                    (ThetaLowerSegment.join cell2909312 cell2913408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2917504 cell2921600)
                    (ThetaLowerSegment.join cell2925696 cell2929792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2933888 cell2937984)
                    (ThetaLowerSegment.join cell2942080 cell2946176)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2950272 cell2954368)
                    (ThetaLowerSegment.join cell2958464 cell2962560))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2966656 cell2970752)
                    (ThetaLowerSegment.join cell2974848 cell2978944))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2983040 cell2987136)
                    (ThetaLowerSegment.join cell2991232 cell2995328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell2999424 cell3003520)
                    (ThetaLowerSegment.join cell3007616 cell3011712)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3015808 cell3019904)
                    (ThetaLowerSegment.join cell3024000 cell3028096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3032192 cell3036288)
                    (ThetaLowerSegment.join cell3040384 cell3044480))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3048576 cell3052672)
                    (ThetaLowerSegment.join cell3056768 cell3060864))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3064960 cell3069056)
                    (ThetaLowerSegment.join cell3073152 cell3077248)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3081344 cell3085440)
                    (ThetaLowerSegment.join cell3089536 cell3093632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3097728 cell3101824)
                    (ThetaLowerSegment.join cell3105920 cell3110016))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3114112 cell3118208)
                    (ThetaLowerSegment.join cell3122304 cell3126400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3130496 cell3134592)
                    (ThetaLowerSegment.join cell3138688 cell3142784)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3146880 cell3150976)
                    (ThetaLowerSegment.join cell3155072 cell3159168))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3163264 cell3167360)
                    (ThetaLowerSegment.join cell3171456 cell3175552)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3179648 cell3183744)
                    (ThetaLowerSegment.join cell3187840 cell3191936))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3196032 cell3200128)
                    (ThetaLowerSegment.join cell3204224 cell3208320)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3212416 cell3216512)
                    (ThetaLowerSegment.join cell3220608 cell3224704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3228800 cell3232896)
                    (ThetaLowerSegment.join cell3236992 cell3241088))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3245184 cell3249280)
                    (ThetaLowerSegment.join cell3253376 cell3257472))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3261568 cell3265664)
                    (ThetaLowerSegment.join cell3269760 cell3273856)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3277952 cell3282048)
                    (ThetaLowerSegment.join cell3286144 cell3290240))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3294336 cell3298432)
                    (ThetaLowerSegment.join cell3302528 cell3306624))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3310720 cell3314816)
                    (ThetaLowerSegment.join cell3318912 cell3323008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3327104 cell3331200)
                    (ThetaLowerSegment.join cell3335296 cell3339392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3343488 cell3347584)
                    (ThetaLowerSegment.join cell3351680 cell3355776))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3359872 cell3363968)
                    (ThetaLowerSegment.join cell3368064 cell3372160))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3376256 cell3380352)
                    (ThetaLowerSegment.join cell3384448 cell3388544))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3392640 cell3396736)
                    (ThetaLowerSegment.join cell3400832 cell3404928)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3409024 cell3413120)
                    (ThetaLowerSegment.join cell3417216 cell3421312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3425408 cell3429504)
                    (ThetaLowerSegment.join cell3433600 cell3437696)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3441792 cell3445888)
                    (ThetaLowerSegment.join cell3449984 cell3454080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3458176 cell3462272)
                    (ThetaLowerSegment.join cell3466368 cell3470464)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3474560 cell3478656)
                    (ThetaLowerSegment.join cell3482752 cell3486848))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3490944 cell3495040)
                    (ThetaLowerSegment.join cell3499136 cell3503232))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3507328 cell3511424)
                    (ThetaLowerSegment.join cell3515520 cell3519616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3523712 cell3527808)
                    (ThetaLowerSegment.join cell3531904 cell3536000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3540096 cell3544192)
                    (ThetaLowerSegment.join cell3548288 cell3552384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3556480 cell3560576)
                    (ThetaLowerSegment.join cell3564672 cell3568768)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3572864 cell3576960)
                    (ThetaLowerSegment.join cell3581056 cell3585152))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3589248 cell3593344)
                    (ThetaLowerSegment.join cell3597440 cell3601536)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3605632 cell3609728)
                    (ThetaLowerSegment.join cell3613824 cell3617920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3622016 cell3626112)
                    (ThetaLowerSegment.join cell3630208 cell3634304))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3638400 cell3642496)
                    (ThetaLowerSegment.join cell3646592 cell3650688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3654784 cell3658880)
                    (ThetaLowerSegment.join cell3662976 cell3667072)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3671168 cell3675264)
                    (ThetaLowerSegment.join cell3679360 cell3683456))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3687552 cell3691648)
                    (ThetaLowerSegment.join cell3695744 cell3699840)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3703936 cell3708032)
                    (ThetaLowerSegment.join cell3712128 cell3716224))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3720320 cell3724416)
                    (ThetaLowerSegment.join cell3728512 cell3732608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3736704 cell3740800)
                    (ThetaLowerSegment.join cell3744896 cell3748992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3753088 cell3757184)
                    (ThetaLowerSegment.join cell3761280 cell3765376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3769472 cell3773568)
                    (ThetaLowerSegment.join cell3777664 cell3781760))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3785856 cell3789952)
                    (ThetaLowerSegment.join cell3794048 cell3798144)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3802240 cell3806336)
                    (ThetaLowerSegment.join cell3810432 cell3814528))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3818624 cell3822720)
                    (ThetaLowerSegment.join cell3826816 cell3830912))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3835008 cell3839104)
                    (ThetaLowerSegment.join cell3843200 cell3847296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3851392 cell3855488)
                    (ThetaLowerSegment.join cell3859584 cell3863680)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3867776 cell3871872)
                    (ThetaLowerSegment.join cell3875968 cell3880064))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3884160 cell3888256)
                    (ThetaLowerSegment.join cell3892352 cell3896448))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3900544 cell3904640)
                    (ThetaLowerSegment.join cell3908736 cell3912832))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3916928 cell3921024)
                    (ThetaLowerSegment.join cell3925120 cell3929216)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3933312 cell3937408)
                    (ThetaLowerSegment.join cell3941504 cell3945600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell3949696 cell3953792)
                    (ThetaLowerSegment.join cell3957888 cell3961984)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3966080 cell3970176)
                  (ThetaLowerSegment.join cell3974272 cell3978368))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3982464 cell3986560)
                  (ThetaLowerSegment.join cell3990656 cell3994752)))
              (ThetaLowerSegment.join cell3998848 cell3999872))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
