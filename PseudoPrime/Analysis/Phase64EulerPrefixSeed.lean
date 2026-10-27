/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSignedEulerIntervals
public import PseudoPrime.Analysis.Phase64DyadicEulerBounds

/-! # A compact signed Euler prefix seed through 500 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- One prime-power seed row with rounded rational lower allowance. The
logarithm scale is computed from the prime, and the ten power intervals use
the actual phase-node order. All candidate endpoints are checked below. -/
def phase64PrefixSeedRow (p k lo lower : ℕ) (digits : List ℕ) : GammaFiniteEulerRow × ℚ :=
  ({ prime := p, exponent := k, logScale := Nat.log2 p + 1, logTerms := 20,
     logLower := (lo : ℚ) / 100000, logUpper := ((lo : ℚ) + 3) / 100000,
     ratios := fun a ↦
       let j := (phaseResolvent64Coefficients.map Prod.fst).idxOf a
       let v := digits.getD j 0
       ((v : ℚ) / 100000000, ((v : ℚ) + 1) / 100000000) },
    (lower : ℚ) / 1000000)

/-- The 114 candidate prime-power rows through 500, paired with rounded
lower weights of denominator one million. Exact coverage is not assumed;
index distinctness, membership and every local bound are independently checked. -/
def phase64PrefixSeedRows : List (GammaFiniteEulerRow × ℚ) :=
  [phase64PrefixSeedRow 2 0 69313 363655
      [35355339, 30778610, 26794336, 12500000, 8838834, 2209708, 552427, 69053, 2157, 67],
    phase64PrefixSeedRow 2 1 69313 160626
      [12500000, 9473228, 7179364, 1562500, 781250, 48828, 3051, 47, 0, 0],
    phase64PrefixSeedRow 2 2 69313 64581
      [4419417, 2915728, 1923663, 195312, 69053, 1078, 16, 0, 0, 0],
    phase64PrefixSeedRow 2 3 69313 24861 [1562500, 897420, 515432, 24414, 6103, 23, 0, 0, 0, 0],
    phase64PrefixSeedRow 2 4 69313 9267 [552427, 276213, 138106, 3051, 539, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 2 5 69313 3369 [195312, 85014, 37004, 381, 47, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 2 6 69313 1202 [69053, 26166, 9915, 47, 4, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 2 7 69313 423 [24414, 8053, 2656, 5, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 3 0 109860 363853
      [19245008, 15448768, 12401368, 3703703, 2138334, 237592, 26399, 977, 4, 0],
    phase64PrefixSeedRow 3 1 109860 87261
      [3703703, 2386644, 1537939, 137174, 45724, 564, 6, 0, 0, 0],
    phase64PrefixSeedRow 3 2 109860 18756 [712778, 368707, 190725, 5080, 977, 1, 0, 0, 0, 0],
    phase64PrefixSeedRow 3 3 109860 3769 [137174, 56960, 23652, 188, 20, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 3 4 109860 726 [26399, 8799, 2933, 6, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 5 0 160942 279870
      [8944271, 6482626, 4698475, 800000, 357770, 14310, 572, 4, 0, 0],
    phase64PrefixSeedRow 5 1 160942 30678 [800000, 420244, 220756, 6400, 1280, 2, 0, 0, 0, 0],
    phase64PrefixSeedRow 5 2 160942 2892 [71554, 27242, 10372, 51, 4, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 7 0 194590 216952
      [5399492, 3658755, 2479212, 291545, 110193, 2248, 45, 0, 0, 0],
    phase64PrefixSeedRow 7 1 194590 14003 [291545, 133864, 61464, 849, 121, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 7 2 194590 763 [15741, 4897, 1523, 2, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 11 0 239788 144744
      [2741012, 1696806, 1050398, 75131, 22652, 187, 1, 0, 0, 0],
    phase64PrefixSeedRow 11 1 239788 4524 [75131, 28791, 11033, 56, 5, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 13 0 256493 122912
      [2133462, 1277309, 764729, 45516, 12624, 74, 0, 0, 0, 0],
    phase64PrefixSeedRow 13 1 256493 2932 [45516, 16315, 5848, 20, 1, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 17 0 283320 93328 [1426680, 809537, 459353, 20354, 4936, 17, 0, 0, 0, 0],
    phase64PrefixSeedRow 17 1 283320 1440 [20354, 6553, 2110, 4, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 19 0 294442 82914 [1207451, 670068, 371850, 14579, 3344, 9, 0, 0, 0, 0],
    phase64PrefixSeedRow 19 1 294442 1068 [14579, 4489, 1382, 2, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 23 0 313548 67323 [906584, 484242, 258652, 8218, 1713, 3, 0, 0, 0, 0],
    phase64PrefixSeedRow 29 0 336728 51881 [640328, 326530, 166511, 4100, 761, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 31 0 343397 48063 [579371, 291531, 146694, 3356, 602, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 37 0 361090 39129 [444321, 215802, 104813, 1974, 324, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 41 0 371356 34665 [380911, 181245, 86240, 1450, 226, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 43 0 376119 32756 [354647, 167148, 78778, 1257, 191, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 47 0 385013 29448 [310351, 143692, 66529, 963, 140, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 53 0 397028 25467 [259170, 117146, 52951, 671, 92, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 59 0 407752 22342 [220659, 97622, 43189, 486, 63, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 61 0 411086 21446 [209896, 92244, 40539, 440, 56, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 67 0 420468 19102 [182342, 78645, 33920, 332, 40, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 71 0 426266 17775 [167152, 71262, 30381, 279, 33, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 73 0 429044 17171 [160330, 67975, 28819, 257, 30, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 79 0 436943 15557 [142416, 59433, 24803, 202, 22, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 83 0 441883 14621 [132246, 54647, 22581, 174, 19, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 89 0 448862 13390 [119100, 48532, 19776, 141, 15, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 97 0 457470 12006 [104674, 41926, 16793, 109, 11, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 101 0 461511 11405 [98518, 39142, 15552, 97, 9, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 103 0 463471 11123 [95663, 37859, 14983, 91, 9, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 107 0 467281 10595 [90349, 35485, 13937, 81, 7, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 109 0 469133 10347 [87873, 34385, 13455, 77, 7, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 113 0 472737 9881 [83249, 32341, 12564, 69, 6, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 127 0 484417 8502 [69870, 26517, 10064, 48, 4, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 131 0 487518 8168 [66694, 25155, 9488, 44, 3, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 137 0 491997 7708 [62361, 23311, 8714, 38, 3, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 139 0 493446 7565 [61020, 22744, 8477, 37, 3, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 149 0 500393 6912 [54982, 20210, 7429, 30, 2, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 151 0 501726 6793 [53893, 19757, 7243, 29, 2, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 157 0 505623 6457 [50833, 18491, 6726, 25, 2, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 163 0 509374 6149 [48052, 17349, 6263, 23, 1, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 167 0 511798 5957 [46336, 16648, 5981, 21, 1, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 173 0 515328 5688 [43947, 15679, 5593, 19, 1, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 179 0 518737 5439 [41756, 14796, 5242, 17, 1, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 181 0 519848 5360 [41065, 14519, 5133, 16, 1, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 191 0 525226 4994 [37883, 13250, 4634, 14, 1, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 193 0 526268 4926 [37296, 13018, 4544, 13, 1, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 197 0 528319 4795 [36166, 12572, 4370, 13, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 199 0 529329 4731 [35622, 12358, 4287, 12, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 211 0 535184 4379 [32626, 11187, 3835, 10, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 223 0 540716 4070 [30029, 10183, 3453, 9, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 227 0 542494 3975 [29238, 9879, 3338, 8, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 229 0 543371 3929 [28856, 9733, 3283, 8, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 233 0 545102 3839 [28116, 9451, 3177, 7, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 239 0 547645 3712 [27064, 9051, 3027, 7, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 241 0 548478 3671 [26728, 8924, 2979, 7, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 251 0 552544 3478 [25147, 8328, 2758, 6, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 257 0 554906 3370 [24271, 8000, 2637, 5, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 263 0 557214 3268 [23445, 7692, 2523, 5, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 269 0 559470 3171 [22665, 7403, 2418, 5, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 271 0 560210 3140 [22415, 7310, 2384, 5, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 277 0 562400 3049 [21691, 7043, 2287, 4, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 281 0 563834 2991 [21229, 6873, 2225, 4, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 283 0 564543 2963 [21004, 6791, 2195, 4, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 293 0 568016 2829 [19938, 6402, 2055, 3, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 307 0 572683 2657 [18590, 5913, 1881, 3, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 311 0 573978 2611 [18233, 5785, 1835, 3, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 313 0 574619 2589 [18058, 5722, 1813, 3, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 317 0 575889 2545 [17717, 5600, 1770, 3, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 331 0 580210 2401 [16605, 5203, 1630, 2, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 337 0 582007 2344 [16164, 5046, 1575, 2, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 347 0 584931 2254 [15470, 4802, 1490, 2, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 349 0 585506 2236 [15337, 4755, 1474, 2, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 353 0 586645 2202 [15077, 4664, 1442, 2, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 359 0 588331 2153 [14701, 4532, 1397, 2, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 367 0 590535 2089 [14223, 4365, 1340, 2, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 373 0 592156 2044 [13881, 4247, 1299, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 379 0 593752 2001 [13553, 4133, 1260, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 383 0 594802 1972 [13341, 4060, 1235, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 389 0 596356 1931 [13033, 3954, 1199, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 397 0 598392 1879 [12641, 3819, 1154, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 401 0 599395 1854 [12453, 3755, 1132, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 409 0 601370 1805 [12089, 3631, 1090, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 419 0 603786 1747 [11659, 3485, 1041, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 421 0 604262 1735 [11576, 3457, 1032, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 431 0 606609 1681 [11175, 3321, 987, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 433 0 607072 1670 [11098, 3295, 978, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 439 0 608448 1639 [10871, 3219, 953, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 443 0 609355 1619 [10724, 3170, 937, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 449 0 610701 1590 [10510, 3098, 913, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 457 0 612467 1552 [10235, 3007, 883, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 461 0 613338 1534 [10102, 2962, 868, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 463 0 613771 1525 [10037, 2941, 861, 1, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 467 0 614631 1507 [9908, 2898, 847, 0, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 479 0 617169 1456 [9538, 2776, 807, 0, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 487 0 618825 1423 [9304, 2698, 782, 0, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 491 0 619643 1408 [9191, 2661, 770, 0, 0, 0, 0, 0, 0, 0],
    phase64PrefixSeedRow 499 0 621259 1377 [8971, 2589, 747, 0, 0, 0, 0, 0, 0, 0]]

/-- A row's exact certificate predicate: primality, the parameterized power
and logarithm check, the rounded lower allowance, and an index in (0,500]. -/
def phase64PrefixSeedValid (r : GammaFiniteEulerRow × ℚ) : Prop :=
  r.1.prime.Prime ∧
    r.1.signedCheck phaseResolvent64Coefficients 20 = true ∧
    r.2 ≤ r.1.signedLower phaseResolvent64Coefficients ∧ 0 < r.1.index ∧ r.1.index ≤ 500

/-- Computable decidability of the seed predicate, using only finite
natural, rational and Boolean arithmetic. It supports kernel-only block checks. -/
instance phase64PrefixSeedDecidable (r : GammaFiniteEulerRow × ℚ) :
    Decidable (phase64PrefixSeedValid r) := by
  dsimp only [phase64PrefixSeedValid]
  infer_instance

/-- Seed rows 0 through 15 pass the exact local predicate.
Kernel arithmetic checks this bounded block without resource overrides. -/
theorem phase64_prefix_seed_block0 :
    ((phase64PrefixSeedRows.drop 0).take 16).Forall phase64PrefixSeedValid := by decide +kernel

/-- Seed rows 16 through 31 pass the exact local predicate.
Kernel arithmetic checks this bounded block without resource overrides. -/
theorem phase64_prefix_seed_block1 :
    ((phase64PrefixSeedRows.drop 16).take 16).Forall phase64PrefixSeedValid := by decide +kernel

/-- Seed rows 32 through 47 pass the exact local predicate.
Kernel arithmetic checks this bounded block without resource overrides. -/
theorem phase64_prefix_seed_block2 :
    ((phase64PrefixSeedRows.drop 32).take 16).Forall phase64PrefixSeedValid := by decide +kernel

/-- Seed rows 48 through 63 pass the exact local predicate.
Kernel arithmetic checks this bounded block without resource overrides. -/
theorem phase64_prefix_seed_block3 :
    ((phase64PrefixSeedRows.drop 48).take 16).Forall phase64PrefixSeedValid := by decide +kernel

/-- Seed rows 64 through 79 pass the exact local predicate.
Kernel arithmetic checks this bounded block without resource overrides. -/
theorem phase64_prefix_seed_block4 :
    ((phase64PrefixSeedRows.drop 64).take 16).Forall phase64PrefixSeedValid := by decide +kernel

/-- Seed rows 80 through 95 pass the exact local predicate.
Kernel arithmetic checks this bounded block without resource overrides. -/
theorem phase64_prefix_seed_block5 :
    ((phase64PrefixSeedRows.drop 80).take 16).Forall phase64PrefixSeedValid := by decide +kernel

/-- Seed rows 96 through 111 pass the exact local predicate.
Kernel arithmetic checks this bounded block without resource overrides. -/
theorem phase64_prefix_seed_block6 :
    ((phase64PrefixSeedRows.drop 96).take 16).Forall phase64PrefixSeedValid := by decide +kernel

/-- Seed rows 112 through 113 pass the exact local predicate.
Kernel arithmetic checks this bounded block without resource overrides. -/
theorem phase64_prefix_seed_block7 :
    ((phase64PrefixSeedRows.drop 112).take 16).Forall phase64PrefixSeedValid := by decide +kernel

/-- All seed rows pass their local certificates. Join the eight bounded
row blocks by finite-list append; the last block contains only two rows. -/
theorem phase64_prefix_seed_checks : phase64PrefixSeedRows.Forall phase64PrefixSeedValid := by
  have he :
    phase64PrefixSeedRows =
      (phase64PrefixSeedRows.drop 0).take 16 ++ (phase64PrefixSeedRows.drop 16).take 16 ++
        (phase64PrefixSeedRows.drop 32).take 16 ++
        (phase64PrefixSeedRows.drop 48).take 16 ++
        (phase64PrefixSeedRows.drop 64).take 16 ++
        (phase64PrefixSeedRows.drop 80).take 16 ++
        (phase64PrefixSeedRows.drop 96).take 16 ++
        (phase64PrefixSeedRows.drop 112).take 16 :=
    rfl
  have h1 := List.forall_append.mpr ⟨phase64_prefix_seed_block0, phase64_prefix_seed_block1⟩
  have h2 := List.forall_append.mpr ⟨h1, phase64_prefix_seed_block2⟩
  have h3 := List.forall_append.mpr ⟨h2, phase64_prefix_seed_block3⟩
  have h4 := List.forall_append.mpr ⟨h3, phase64_prefix_seed_block4⟩
  have h5 := List.forall_append.mpr ⟨h4, phase64_prefix_seed_block5⟩
  have h6 := List.forall_append.mpr ⟨h5, phase64_prefix_seed_block6⟩
  have h7 := List.forall_append.mpr ⟨h6, phase64_prefix_seed_block7⟩
  rw [he]
  exact h7

/-- All 114 prime-power indices are distinct. Kernel natural arithmetic
checks this condition before any row sum is compared with the full prefix. -/
theorem phase64_prefix_seed_indices_nodup :
    (phase64PrefixSeedRows.map (fun r ↦ r.1.index)).Nodup := by decide +kernel

/-- The rounded rational row allowances sum to at least 57/20. Exact
kernel arithmetic verifies the small-denominator sum. -/
theorem phase64_prefix_seed_rational_lower :
    (57 / 20 : ℚ) ≤ (phase64PrefixSeedRows.map Prod.snd).sum := by decide +kernel

/-- The actual signed Mangoldt prefix through 500 is at least 57/20.
Apply every checked row lower bound, distinctness and nonnegativity of omitted
weights, then transfer the rational sum certificate into the reals. -/
theorem phase64_prefix_seed_lower :
    (57 / 20 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 500, finiteSignedMangoldtWeight phaseResolvent64Coefficients n := by
  have hr :=
    nonnegative_weight_prefix_le_of_rows (finiteSignedMangoldtWeight phaseResolvent64Coefficients)
      (finiteSignedMangoldtWeight_nonneg phaseResolvent64Coefficients
        (fun u hu ↦ phaseResolvent64_euler_nonneg hu))
      phase64PrefixSeedRows (fun r ↦ r.1.index) Prod.snd phase64_prefix_seed_indices_nodup
      (fun r hr ↦ by
        have h := List.forall_iff_forall_mem.mp phase64_prefix_seed_checks r hr
        exact ⟨h.2.2.2.1, h.2.2.2.2⟩)
      (fun r hr ↦ by
        have h := List.forall_iff_forall_mem.mp phase64_prefix_seed_checks r hr
        exact
          ((Rat.cast_le (K := ℝ)).mpr h.2.2.1).trans
            (r.1.signedLower_le phaseResolvent64Coefficients (by norm_num only : 0 < (20 : ℕ)) h.1
              h.2.1))
  have hc := (Rat.cast_le (K := ℝ)).mpr phase64_prefix_seed_rational_lower
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_list_sum, List.map_map,
    Function.comp_def] at hr hc
  linarith only [hr, hc]

/-- At any real cutoff at least 500, the actual signed Mangoldt prefix is
at least 57/20. The seed prefix is a subset and every additional combined
Mangoldt weight is nonnegative. No input enumeration is involved. -/
theorem phase64_prefix_lower_of_cutoff_ge_500 {b : ℝ} (hb : 500 ≤ b) :
    (57 / 20 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, finiteSignedMangoldtWeight phaseResolvent64Coefficients n := by
  have hfloor : 500 ≤ ⌊b⌋₊ := (Nat.le_floor_iff (by linarith only [hb] : 0 ≤ b)).mpr hb
  have hsub : Finset.Ioc 0 500 ⊆ Finset.Ioc 0 ⌊b⌋₊ := fun n hn ↦
    Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans hfloor⟩
  exact
    phase64_prefix_seed_lower.trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ ↦
          finiteSignedMangoldtWeight_nonneg phaseResolvent64Coefficients
            (fun u hu ↦ phaseResolvent64_euler_nonneg hu) n))

end PseudoPrime.Analysis
