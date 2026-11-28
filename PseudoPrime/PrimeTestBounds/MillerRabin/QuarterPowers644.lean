/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterComparison644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterOdd574
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareGain570
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipal644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalCorrection644

/-! # Prime-power recovery on the common section 122 window -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The fixed window uses squared prime powers with roots in (322,1200]
and the 23 odd prime powers of section 122. The union counts each index once. -/
private def fixedPowers644 : Finset ℕ :=
  (((Finset.Ioc 322 1200).filter IsPrimePow).image (fun t ↦ t ^ 2)) ∪
    ((insert (113, 3) (insert (17, 5) oddData574)).image (fun u ↦ u.1 ^ u.2))

/-- Every selected power exceeds the right cutoff, stays inside the common
support bound, and has prime base below the left cutoff. -/
private theorem fixed_power_data_644 {m : ℕ} (hm : m ∈ fixedPowers644) :
    322 ^ 2 < m ∧ m ≤ 1202 ^ 2 ∧ ∃ p k : ℕ, p.Prime ∧ p ≤ 316 ^ 2 ∧ m = p ^ k := by
  rcases Finset.mem_union.mp hm with he | ho
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hb, ht⟩ := Finset.mem_filter.mp ht
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff t).mp ht
    obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hb
    have hp' : p ≤ p ^ k := le_self_pow₀ hp.one_lt.le hk.ne'
    exact
      ⟨Nat.pow_lt_pow_left hl (by decide), (Nat.pow_le_pow_left hu 2).trans (by decide), p, k * 2,
        hp, hp'.trans (hu.trans (by decide)), (pow_mul p k 2).symm⟩
  · obtain ⟨⟨p, k⟩, hk, rfl⟩ := Finset.mem_image.mp ho
    have h :=
      (show
          ∀ u ∈ insert (113, 3) (insert (17, 5) oddData574),
            Nat.Prime u.1 ∧ u.1 ≤ 316 ^ 2 ∧ 322 ^ 2 < u.1 ^ u.2 ∧ u.1 ^ u.2 ≤ 1202 ^ 2
          by decide +kernel)
        (p, k) hk
    exact ⟨h.2.2.1, h.2.2.2, p, k, h.1, h.2.1, rfl⟩

/-- Each selected power lies in the nonzero main-kernel window at
the left endpoint, and hence at every larger radius. -/
private theorem fixed_power_log_window_644 {r : ℝ} (hr : 316 ≤ r) {m : ℕ}
    (hm : m ∈ fixedPowers644) : Real.log ((m : ℝ) / r ^ 2) < 2687 / 1000 := by
  obtain ⟨hm₀, hm₁, _⟩ := fixed_power_data_644 hm
  have hr₀ : 0 < r := by linarith only [hr]
  have hmp : 0 < (m : ℝ) := Nat.cast_pos.mpr ((by decide : 0 < 322 ^ 2).trans hm₀)
  have hR := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 316) hr 2
  have hq : (m : ℝ) / r ^ 2 ≤ 29 / 2 := by
    apply (div_le_iff₀ (pow_pos hr₀ _)).mpr
    have hM : (m : ℝ) ≤ (1202 : ℝ) ^ 2 := by exact_mod_cast hm₁
    linarith only [hM, hR]
  rw [Real.log_lt_iff_lt_exp (div_pos hmp (pow_pos hr₀ _))]
  have he := Real.sum_le_exp_of_nonneg (by norm_num only : 0 ≤ (2687 / 1000 : ℝ)) 12
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero] at he
  exact hq.trans_lt (by linarith only [he])

/-- The fourfold contribution of the fixed prime powers to the principal
main-kernel sum at radius r, used in the section 122 comparison. -/
noncomputable def fixedPowerGain644 (r : ℝ) : ℝ :=
  4 * ∑ m ∈ fixedPowers644, (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) m).re

/-- The fixed prime-power credit increases on the section 122 radius interval.
Each selected weight stays inside its support and on the increasing part of the profile. -/
theorem fixed_power_gain_mono_644 : MonotoneOn fixedPowerGain644 (Set.Icc 316 322) := by
  intro s hsR r hr hsr
  have hs₀ : 0 < s := by linarith only [hsR.1]
  have hr₀ : 0 < r := by linarith only [hr.1]
  unfold fixedPowerGain644
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  apply Finset.sum_le_sum
  intro m hm
  have hm₀ : 0 < m := (by decide : 0 < 322 ^ 2).trans (fixed_power_data_644 hm).1
  have hs := fixed_power_log_window_644 hr.1 hm
  have hsLog := fixed_power_log_window_644 hsR.1 hm
  rw [quarter_summand_644 (pow_pos hs₀ _) hm₀ hsLog.le,
    quarter_summand_644 (pow_pos hr₀ _) hm₀ hs.le]
  have hM : r ^ 2 ≤ (m : ℝ) :=
    (pow_le_pow_left₀ hr₀.le hr.2 2).trans
      (show (322 : ℝ) ^ 2 ≤ m by exact_mod_cast (fixed_power_data_644 hm).1.le)
  have hL := Real.log_nonneg ((one_le_div (pow_pos hr₀ 2)).mpr hM)
  have hlog :=
    Real.log_le_log (div_pos (Nat.cast_pos.mpr hm₀) (pow_pos hr₀ 2))
      (div_le_div_of_nonneg_left (Nat.cast_nonneg m) (pow_pos hs₀ 2)
        (pow_le_pow_left₀ hs₀.le hsr 2))
  unfold quarterWeight644
  dsimp only
  apply mul_le_mul_of_nonneg_right _ ArithmeticFunction.vonMangoldt_nonneg
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by norm_num only)
  apply fifth_increasing
  · exact ⟨by linarith only [hsLog], by linarith only [hlog, hL]⟩
  · exact ⟨by linarith only [hs], by linarith only [hL]⟩
  · linarith only [hlog]

/-- The value at 316 bounds the fixed prime-power credit from below throughout
the section 122 radius interval, by monotonicity. -/
theorem fixed_power_gain_left_644 {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    fixedPowerGain644 316 ≤ fixedPowerGain644 r := by
  exact fixed_power_gain_mono_644 ⟨le_rfl, by norm_num only⟩ hr hr.1

/-- At any positive radius below the prime-power root, lower bounds for the logarithm and profile,
and a positive upper bound for the square root, certify a prime-power credit.
The profile can be evaluated at a lower argument because it increases on [0,5]. -/
theorem quarter_power_row_lower_644 {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) {r z l s e : ℝ}
    (hr : 0 < r) (hz : 0 ≤ z)
    (harg : z ≤ (107 / 100) * (2687 / 1000 - Real.log (((p ^ k : ℕ) : ℝ) / r ^ 2)))
    (hcut : r ^ 2 ≤ (p ^ k : ℕ)) (hl : 0 ≤ l) (hlog : l ≤ Real.log p)
    (hs : Real.sqrt (p ^ k : ℕ) ≤ s) (he : e ≤ Real.exp (-z)) :
    4 * (l / s) * (z ^ 5 * e / 120) ≤
      4 * (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) (p ^ k)).re := by
  have hm : 0 < p ^ k := pow_pos hp.pos _
  have hsq : 0 < Real.sqrt (p ^ k : ℕ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hm)
  have hs₀ := hsq.trans_le hs
  have hL := Real.log_nonneg ((one_le_div (pow_pos hr 2)).mpr hcut)
  have hS : Real.log (((p ^ k : ℕ) : ℝ) / r ^ 2) ≤ 2687 / 1000 := by linarith only [hz, harg]
  rw [quarter_summand_644 (pow_pos hr 2) hm hS, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  let v := (107 / 100 : ℝ) * (2687 / 1000 - Real.log (((p ^ k : ℕ) : ℝ) / r ^ 2))
  have hv : v ∈ Set.Icc 0 5 :=
    ⟨hz.trans harg, by
      dsimp only [v]; linarith only [hL]⟩
  have hzp : z ∈ Set.Icc 0 5 := ⟨hz, harg.trans hv.2⟩
  have hf := fifth_increasing hzp hv harg
  have hw := (mul_le_mul_of_nonneg_left he (pow_nonneg hz 5)).trans hf
  have hq : l / s ≤ Real.log p / Real.sqrt (p ^ k : ℕ) :=
    (div_le_div_of_nonneg_left hl hsq hs).trans (div_le_div_of_nonneg_right hlog hsq.le)
  have hV : 0 ≤ v ^ 5 * Real.exp (-v) / 120 := by positivity
  have hh :=
    mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hw (by norm_num only))
            (div_nonneg hl hs₀.le)).trans
        (mul_le_mul_of_nonneg_right hq hV))
      (by norm_num only : (0 : ℝ) ≤ 4)
  dsimp only [quarterWeight644]
  rw [mul_assoc (4 : ℝ) (l / s)]
  refine hh.trans_eq ?_
  dsimp only [v]
  ring

private theorem log_box {n : ℕ} {j : ℕ} {l u : ℚ}
    (h : Analysis.rationalLogIntervalCheck n j 27 l u = true) :
    (l : ℝ) ≤ Real.log n ∧ Real.log n ≤ (u : ℝ) := by
  simpa only [Rat.cast_natCast] using Analysis.rationalLogIntervalCheck_sound h

private theorem exp_neg_lower {z e : ℝ} (hz : 0 ≤ z) (hs : z / 17 ≤ 1 / 2)
    (h :
      e *
          ((∑ k ∈ Finset.range 16, z ^ k / (k.factorial : ℝ)) +
            z ^ 16 / ((16 : ℕ).factorial : ℝ) * 2) ≤
        1) :
    e ≤ Real.exp (-z) := by
  by_cases he : 0 ≤ e
  · rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
    exact
      (mul_le_mul_of_nonneg_left (Analysis.exp_le_taylor_add_two_next (n := 16) hz hs) he).trans h
  · exact (le_of_not_ge he).trans (Real.exp_pos _).le

/-- A certified lower bound for the exponential at the original profile argument
also bounds the exponential at the shifted argument after multiplication by one minus
the shift. This reuses the same row at a larger radius. -/
private theorem exp_shift_lower_644 {z e d : ℝ} (he₀ : 0 ≤ e) (he : e ≤ Real.exp (-z)) :
    e * (1 - d) ≤ Real.exp (-(z + d)) := by
  rw [neg_add, Real.exp_add]
  have hd : 1 - d ≤ Real.exp (-d) := by
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-d)
  exact (mul_le_mul_of_nonneg_left hd he₀).trans (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le)

private noncomputable def anchorPowerCredit644 (n : ℕ) : ℝ :=
  4 * (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) (316 ^ 2) n).re

private theorem anchor_power_nonneg (n : ℕ) : 0 ≤ anchorPowerCredit644 n :=
  mul_nonneg (by norm_num only) (quarterKernel644.principal_summand_re_nonneg (by norm_num only) n)

private structure PowerRow644 where
  p : ℕ
  k : ℕ
  scale : ℕ
  logLo : ℕ
  logHi : ℕ
  profileLo : ℕ
  expLo : ℕ
  rootHi : ℕ
  credit : ℕ
  deriving DecidableEq

private def oddPowerRows644 : List PowerRow644 :=
  [⟨47, 3, 6, 3850146, 3850149, 2833309, 58816, 322216, 4277⟩,
    ⟨53, 3, 6, 3970290, 3970293, 2447647, 86495, 385846, 2606⟩,
    ⟨59, 3, 6, 4077536, 4077539, 2103387, 122041, 453188, 1506⟩,
    ⟨61, 3, 6, 4110872, 4110875, 1996379, 135825, 476426, 1238⟩,
    ⟨67, 3, 7, 4204691, 4204694, 1695220, 183557, 548419, 656⟩,
    ⟨71, 3, 7, 4262678, 4262681, 1509081, 221112, 598257, 411⟩,
    ⟨73, 3, 7, 4290458, 4290461, 1419908, 241735, 623713, 319⟩,
    ⟨79, 3, 7, 4369446, 4369449, 1166356, 311498, 702168, 139⟩,
    ⟨83, 3, 7, 4418839, 4418842, 1007805, 365018, 756166, 73⟩,
    ⟨89, 3, 7, 4488635, 4488638, 783760, 456684, 839625, 24⟩,
    ⟨97, 3, 7, 4574709, 4574712, 507462, 602020, 955340, 3⟩,
    ⟨101, 3, 7, 4615119, 4615122, 377746, 685403, 1015038, 0⟩,
    ⟨103, 3, 7, 4634727, 4634730, 314804, 729930, 1045336, 0⟩,
    ⟨107, 3, 7, 4672827, 4672830, 192503, 824890, 1106817, 0⟩,
    ⟨109, 3, 7, 4691346, 4691349, 133057, 875414, 1137994, 0⟩,
    ⟨113, 3, 7, 4727386, 4727389, 17369, 982779, 1201207, 0⟩,
    ⟨11, 5, 4, 2397894, 2397897, 2363539, 94085, 401312, 1382⟩,
    ⟨13, 5, 4, 2564948, 2564951, 1469800, 229970, 609339, 221⟩,
    ⟨17, 5, 5, 2833212, 2833215, 34587, 966003, 1191578, 0⟩,
    ⟨7, 7, 3, 1945909, 1945912, 617407, 539340, 907493, 3⟩,
    ⟨3, 11, 2, 1098611, 1098614, 2261601, 104182, 420889, 536⟩,
    ⟨2, 17, 1, 693146, 693149, 2583907, 75477, 362039, 554⟩,
    ⟨2, 19, 1, 693146, 693149, 1100568, 332681, 724078, 17⟩]

private def evenPowerRows644 : List PowerRow644 :=
  [⟨331, 2, 9, 5802117, 5802120, 2775751, 62301, 331000, 5998⟩,
    ⟨337, 2, 9, 5820081, 5820084, 2737308, 64743, 337000, 5727⟩,
    ⟨7, 6, 3, 1945909, 1945912, 2699532, 67235, 343000, 1822⟩,
    ⟨347, 2, 9, 5849323, 5849326, 2674730, 68924, 347000, 5301⟩,
    ⟨349, 2, 9, 5855070, 5855073, 2662431, 69777, 349000, 5220⟩,
    ⟨353, 2, 9, 5866467, 5866470, 2638042, 71500, 353000, 5060⟩,
    ⟨359, 2, 9, 5883321, 5883324, 2601974, 74126, 359000, 4829⟩,
    ⟨19, 4, 5, 2944437, 2944440, 2590084, 75012, 361000, 2377⟩,
    ⟨367, 2, 9, 5905360, 5905363, 2554811, 77705, 367000, 4536⟩,
    ⟨373, 2, 9, 5921577, 5921580, 2520106, 80450, 373000, 4327⟩,
    ⟨379, 2, 9, 5937535, 5937538, 2485956, 83244, 379000, 4127⟩,
    ⟨383, 2, 9, 5948033, 5948036, 2463490, 85136, 383000, 3998⟩,
    ⟨389, 2, 9, 5963578, 5963581, 2430224, 88016, 389000, 3812⟩,
    ⟨397, 2, 9, 5983935, 5983938, 2386660, 91935, 397000, 3576⟩,
    ⟨401, 2, 9, 5993960, 5993963, 2365207, 93928, 401000, 3464⟩,
    ⟨409, 2, 9, 6013714, 6013717, 2322933, 97984, 409000, 3248⟩,
    ⟨419, 2, 9, 6037869, 6037872, 2271241, 103183, 419000, 2995⟩,
    ⟨421, 2, 9, 6042631, 6042634, 2261051, 104239, 421000, 2947⟩,
    ⟨431, 2, 9, 6066107, 6066110, 2210812, 109610, 431000, 2715⟩,
    ⟨433, 2, 9, 6070736, 6070739, 2200906, 110701, 433000, 2671⟩,
    ⟨439, 2, 9, 6084498, 6084501, 2171455, 114010, 439000, 2542⟩,
    ⟨443, 2, 9, 6093568, 6093571, 2152046, 116245, 443000, 2460⟩,
    ⟨449, 2, 9, 6107021, 6107024, 2123256, 119640, 449000, 2340⟩,
    ⟨457, 2, 9, 6124682, 6124685, 2085462, 124248, 457000, 2189⟩,
    ⟨461, 2, 9, 6133397, 6133400, 2066812, 126587, 461000, 2117⟩,
    ⟨463, 2, 9, 6137726, 6137729, 2057547, 127765, 463000, 2081⟩,
    ⟨467, 2, 9, 6146328, 6146331, 2039139, 130139, 467000, 2012⟩,
    ⟨479, 2, 9, 6171699, 6171702, 1984845, 137400, 479000, 1817⟩,
    ⟨487, 2, 9, 6188263, 6188266, 1949398, 142358, 487000, 1697⟩,
    ⟨491, 2, 9, 6196443, 6196446, 1931893, 144872, 491000, 1639⟩,
    ⟨499, 2, 9, 6212605, 6212608, 1897306, 149971, 499000, 1530⟩,
    ⟨503, 2, 9, 6220589, 6220592, 1880221, 152555, 503000, 1477⟩,
    ⟨509, 2, 9, 6232447, 6232450, 1854844, 156476, 509000, 1402⟩,
    ⟨2, 18, 1, 693146, 693149, 1842238, 158461, 512000, 151⟩,
    ⟨521, 2, 10, 6255749, 6255752, 1804978, 164477, 521000, 1261⟩,
    ⟨523, 2, 10, 6259580, 6259583, 1796780, 165831, 523000, 1238⟩,
    ⟨23, 4, 5, 3135493, 3135496, 1772365, 169929, 529000, 587⟩,
    ⟨541, 2, 10, 6293418, 6293421, 1724367, 178284, 541000, 1053⟩,
    ⟨547, 2, 10, 6304447, 6304450, 1700764, 182543, 547000, 997⟩,
    ⟨557, 2, 10, 6322564, 6322567, 1661994, 189759, 557000, 910⟩,
    ⟨563, 2, 10, 6333278, 6333281, 1639066, 194160, 563000, 861⟩,
    ⟨569, 2, 10, 6343879, 6343882, 1616380, 198615, 569000, 814⟩,
    ⟨571, 2, 10, 6347388, 6347391, 1608871, 200112, 571000, 799⟩,
    ⟨577, 2, 10, 6357841, 6357844, 1586501, 204639, 577000, 755⟩,
    ⟨587, 2, 10, 6375023, 6375026, 1549732, 212303, 587000, 687⟩,
    ⟨593, 2, 10, 6385193, 6385196, 1527968, 216975, 593000, 648⟩,
    ⟨599, 2, 10, 6395260, 6395263, 1506425, 221700, 599000, 612⟩,
    ⟨601, 2, 10, 6398593, 6398596, 1499292, 223287, 601000, 600⟩,
    ⟨607, 2, 10, 6408527, 6408530, 1478033, 228084, 607000, 566⟩,
    ⟨613, 2, 10, 6418363, 6418366, 1456984, 232936, 613000, 533⟩,
    ⟨617, 2, 10, 6424868, 6424871, 1443064, 236201, 617000, 513⟩,
    ⟨619, 2, 10, 6428104, 6428107, 1436139, 237843, 619000, 502⟩,
    ⟨5, 8, 3, 1609436, 1609439, 1415490, 242805, 625000, 118⟩,
    ⟨631, 2, 10, 6447304, 6447307, 1395051, 247819, 631000, 445⟩,
    ⟨641, 2, 10, 6463028, 6463031, 1361401, 256300, 641000, 402⟩,
    ⟨643, 2, 10, 6466143, 6466146, 1354735, 258014, 643000, 394⟩,
    ⟨647, 2, 10, 6472345, 6472348, 1341463, 261461, 647000, 378⟩,
    ⟨653, 2, 10, 6481576, 6481579, 1321708, 266678, 653000, 355⟩,
    ⟨659, 2, 10, 6490722, 6490725, 1302136, 271949, 659000, 334⟩,
    ⟨661, 2, 10, 6493752, 6493755, 1295652, 273718, 661000, 327⟩,
    ⟨673, 2, 10, 6511744, 6511747, 1257149, 284462, 673000, 288⟩,
    ⟨677, 2, 10, 6517670, 6517673, 1244467, 288093, 677000, 275⟩,
    ⟨683, 2, 10, 6526493, 6526496, 1225586, 293584, 683000, 258⟩,
    ⟨691, 2, 10, 6538138, 6538141, 1200666, 300992, 691000, 236⟩,
    ⟨701, 2, 10, 6552506, 6552509, 1169918, 310391, 701000, 211⟩,
    ⟨709, 2, 10, 6563854, 6563857, 1145634, 318021, 709000, 193⟩,
    ⟨719, 2, 10, 6577860, 6577863, 1115661, 327697, 719000, 172⟩,
    ⟨727, 2, 10, 6588925, 6588928, 1091982, 335549, 727000, 157⟩,
    ⟨3, 12, 2, 1098611, 1098614, 1086084, 337534, 729000, 25⟩,
    ⟨733, 2, 10, 6597144, 6597147, 1074393, 341503, 733000, 146⟩,
    ⟨739, 2, 10, 6605296, 6605299, 1056948, 347513, 739000, 136⟩,
    ⟨743, 2, 10, 6610695, 6610698, 1045394, 351552, 743000, 130⟩,
    ⟨751, 2, 10, 6621404, 6621407, 1022477, 359701, 751000, 118⟩,
    ⟨757, 2, 10, 6629362, 6629365, 1005446, 365880, 757000, 109⟩,
    ⟨761, 2, 10, 6634632, 6634635, 994169, 370029, 761000, 104⟩,
    ⟨769, 2, 10, 6645089, 6645092, 971791, 378403, 769000, 94⟩,
    ⟨773, 2, 10, 6650278, 6650281, 960686, 382629, 773000, 89⟩,
    ⟨787, 2, 10, 6668227, 6668230, 922275, 397612, 787000, 74⟩,
    ⟨797, 2, 10, 6680853, 6680856, 895256, 408502, 797000, 65⟩,
    ⟨809, 2, 10, 6695797, 6695800, 863275, 421777, 809000, 55⟩,
    ⟨811, 2, 10, 6698267, 6698270, 857990, 424012, 811000, 54⟩,
    ⟨821, 2, 10, 6710522, 6710525, 831764, 435279, 821000, 47⟩,
    ⟨823, 2, 10, 6712955, 6712958, 826557, 437552, 823000, 45⟩,
    ⟨827, 2, 10, 6717803, 6717806, 816183, 442114, 827000, 43⟩,
    ⟨829, 2, 10, 6720219, 6720222, 811012, 444407, 829000, 42⟩,
    ⟨839, 2, 10, 6732209, 6732212, 785354, 455957, 839000, 36⟩,
    ⟨29, 4, 5, 3367294, 3367297, 780256, 458287, 841000, 17⟩,
    ⟨853, 2, 10, 6748758, 6748761, 749939, 472394, 853000, 29⟩,
    ⟨857, 2, 10, 6753436, 6753439, 739928, 477147, 857000, 27⟩,
    ⟨859, 2, 10, 6755767, 6755770, 734940, 479533, 859000, 26⟩,
    ⟨863, 2, 10, 6760413, 6760416, 724997, 484325, 863000, 25⟩,
    ⟨877, 2, 10, 6776505, 6776508, 690560, 501294, 877000, 20⟩,
    ⟨881, 2, 10, 6781056, 6781059, 680821, 506200, 881000, 18⟩,
    ⟨883, 2, 10, 6783324, 6783327, 675968, 508662, 883000, 18⟩,
    ⟨887, 2, 10, 6787843, 6787846, 666297, 513605, 887000, 17⟩]

private def powerRows644 : List PowerRow644 :=
  evenPowerRows644 ++ oddPowerRows644

private def PowerRow644.Eligible (a : PowerRow644) : Prop :=
  (a.p, a.k) ∈ insert (113, 3) (insert (17, 5) oddData574) ∨
    (a.k = (a.k / 2) * 2 ∧ 0 < a.k / 2 ∧ 322 < a.p ^ (a.k / 2) ∧ a.p ^ (a.k / 2) ≤ 1200)

private instance (a : PowerRow644) : Decidable a.Eligible := by
  unfold PowerRow644.Eligible
  infer_instance

private def PowerRow644.Valid (a : PowerRow644) : Prop :=
  a.p.Prime ∧
    a.k ≠ 0 ∧
      322 ^ 2 < a.p ^ a.k ∧
        a.Eligible ∧
          Analysis.rationalLogIntervalCheck a.p a.scale 27 (a.logLo / 1000000) (a.logHi / 1000000) =
              true ∧
            a.p ^ a.k * 1000000 ≤ a.rootHi ^ 2 ∧
              let z : ℚ := a.profileLo / 1000000
              let e : ℚ := a.expLo / 1000000
              z ≤ (107 / 100) * (2687 / 1000 - (a.k * (a.logHi / 1000000) - 2 * (57557 / 10000))) ∧
                z / 17 ≤ 1 / 2 ∧
                e *
                    ((∑ i ∈ Finset.range 16, z ^ i / (i.factorial : ℚ)) +
                      z ^ 16 / ((16 : ℕ).factorial : ℚ) * 2) ≤
                  1 ∧
                (a.credit : ℚ) / 1000000 ≤
                  4 * ((a.logLo / 1000000) / (a.rootHi / 1000)) * (z ^ 5 * e / 120)

private instance (a : PowerRow644) : Decidable a.Valid := by
  unfold PowerRow644.Valid
  infer_instance

private theorem shifted_power_row_sound (a : PowerRow644) (h : a.Valid) {r d : ℝ} (hr₀ : 0 < r)
    (hrU : r ≤ 322) (hd₀ : 0 ≤ d) (hd : d ≤ (107 / 50) * (Real.log r - 57557 / 10000)) :
    4 * (((a.logLo : ℝ) / 1000000) / (a.rootHi / 1000)) *
        (((a.profileLo : ℝ) / 1000000 + d) ^ 5 * (a.expLo / 1000000 * (1 - d)) / 120) ≤
      4 * (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) (a.p ^ a.k)).re := by
  obtain ⟨hp, hk, hcut, _, hlog, hr, hz, hs, he, _⟩ := h
  have hlog := log_box hlog
  simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hlog
  have hA := (Rat.cast_le (K := ℝ)).2 hz
  have hS := (Rat.cast_le (K := ℝ)).2 hs
  have hE := (Rat.cast_le (K := ℝ)).2 he
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_sum, Rat.cast_add, Rat.cast_one] at hA hS hE
  have hl :
    Real.log ((a.p ^ a.k : ℕ) / r ^ 2) ≤ (a.k : ℝ) * (a.logHi / 1000000) - 2 * Real.log r := by
    rw [Nat.cast_pow,
      Real.log_div (pow_ne_zero _ (Nat.cast_pos.mpr hp.pos).ne') (pow_ne_zero _ hr₀.ne'),
      Real.log_pow, Real.log_pow, Nat.cast_ofNat]
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hlog.2 (Nat.cast_nonneg _)) _
  have hr' : Real.sqrt (a.p ^ a.k : ℕ) ≤ (a.rootHi : ℝ) / 1000 := by
    have hh : ((a.p ^ a.k : ℕ) : ℝ) * 1000000 ≤ (a.rootHi : ℝ) ^ 2 := by exact_mod_cast hr
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith only [hh]⟩
  have hcut' : r ^ 2 ≤ (a.p ^ a.k : ℕ) :=
    (pow_le_pow_left₀ hr₀.le hrU 2).trans (by exact_mod_cast hcut.le)
  exact
    quarter_power_row_lower_644 hp hk hr₀ (by positivity) (by linarith only [hA, hl, hd]) hcut'
      (by positivity) hlog.1 hr'
      (exp_shift_lower_644 (by positivity) (exp_neg_lower (by positivity) hS hE))

private theorem power_row_sound (a : PowerRow644) (h : a.Valid) :
    (a.credit : ℝ) / 1000000 ≤
      4 * (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) (316 ^ 2) (a.p ^ a.k)).re := by
  have ⟨_, _, _, _, _, _, _, _, _, hc⟩ := h
  have hbase := (log_box (n := 316) (j := 9) (l := 57557 / 10000) (u := 6) (by decide +kernel)).1
  simp only [Rat.cast_div, Rat.cast_ofNat] at hbase
  have hs :=
    shifted_power_row_sound a h (r := 316) (d := 0) (by norm_num only) (by norm_num only) le_rfl
      (by linarith only [hbase])
  have hC := (Rat.cast_le (K := ℝ)).2 hc
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow] at hC
  exact hC.trans (by simpa only [add_zero, sub_zero, mul_one] using hs)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
-- The finite list uses one bounded check of its endpoint certificates.
private theorem power_rows_valid : ∀ a ∈ powerRows644, a.Valid := by decide +kernel

private def powerIndices644 : Finset ℕ :=
  powerRows644.toFinset.image (fun a ↦ a.p ^ a.k)

private theorem row_index_mem (a : PowerRow644) (h : a.Valid) : a.p ^ a.k ∈ fixedPowers644 := by
  rcases h.2.2.2.1 with ho | he
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a.p, a.k), ho, rfl⟩)
  obtain ⟨hk, hk₀, hlo, hhi⟩ := he
  have hpow : IsPrimePow (a.p ^ (a.k / 2)) :=
    (isPrimePow_nat_iff _).mpr ⟨a.p, a.k / 2, h.1, hk₀, rfl⟩
  have hx : (a.p ^ (a.k / 2)) ^ 2 = a.p ^ a.k :=
    (pow_mul _ _ _).symm.trans (congrArg (fun k : ℕ ↦ a.p ^ k) hk.symm)
  exact
    Finset.mem_union_left _
      (Finset.mem_image.mpr
        ⟨a.p ^ (a.k / 2), Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo, hhi⟩, hpow⟩, hx⟩)

private theorem power_rows_subset : powerIndices644 ⊆ fixedPowers644 := by
  intro n hn
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
  exact row_index_mem a (power_rows_valid a (List.mem_toFinset.mp ha))

/-- The shifted row credit rounded down in units of one hundred-millionth.
Rounding each row keeps the denominators of the sum bounded. -/
private def shiftedPowerUnits644 (d : ℚ) (a : PowerRow644) : ℤ :=
  Int.floor
    (100000000 *
      (4 * ((a.logLo / 1000000 : ℚ) / (a.rootHi / 1000)) *
        (((a.profileLo / 1000000 : ℚ) + d) ^ 5 * (a.expLo / 1000000 * (1 - d)) / 120)))

private theorem shifted_power_units_le (d : ℚ) (a : PowerRow644) (h : a.Valid) {r : ℝ} (hr : 0 < r)
    (hU : r ≤ 322) (hd₀ : 0 ≤ (d : ℝ)) (hd : (d : ℝ) ≤ (107 / 50) * (Real.log r - 57557 / 10000)) :
    (shiftedPowerUnits644 d a : ℝ) / 100000000 ≤
      4 * (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) (a.p ^ a.k)).re := by
  have hfloor :=
    (Rat.cast_le (K := ℝ)).2
      (Int.floor_le
        (100000000 *
          (4 * ((a.logLo / 1000000 : ℚ) / (a.rootHi / 1000)) *
            (((a.profileLo / 1000000 : ℚ) + d) ^ 5 * (a.expLo / 1000000 * (1 - d)) / 120))))
  change (((shiftedPowerUnits644 d a : ℤ) : ℚ) : ℝ) ≤ _ at hfloor
  simp only [Rat.cast_intCast, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_add, Rat.cast_sub, Rat.cast_one] at hfloor
  exact
    ((div_le_iff₀ (by norm_num only : (0 : ℝ) < 100000000)).mpr
          (by
            rw [mul_comm]; exact hfloor)).trans
      (shifted_power_row_sound a h hr hU hd₀ hd)

/-- The rounded shifted credits bound the full fixed prime-power sum from below.
The fixed certificate checks membership and excludes duplicate indices. -/
private theorem shifted_power_sum_le (d : ℚ) {r : ℝ} (hr : r ∈ Set.Icc 316 322) (hd₀ : 0 ≤ (d : ℝ))
    (hd : (d : ℝ) ≤ (107 / 50) * (Real.log r - 57557 / 10000)) :
    ((∑ a ∈ powerRows644.toFinset, shiftedPowerUnits644 d a : ℤ) : ℝ) / 100000000 ≤
      fixedPowerGain644 r := by
  have hcard : powerIndices644.card = powerRows644.toFinset.card := by decide +kernel
  have hinj := Finset.injOn_of_card_image_eq hcard
  have hrow :=
    Finset.sum_le_sum (s := powerRows644.toFinset)
      (fun a ha ↦
        shifted_power_units_le d a (power_rows_valid a (List.mem_toFinset.mp ha))
          (by linarith only [hr.1]) hr.2 hd₀ hd)
  have hr₀ : 0 < r := by linarith only [hr.1]
  have hsub :=
    Finset.sum_le_sum_of_subset_of_nonneg power_rows_subset (f := fun m ↦
      4 * (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) m).re)
      (fun m _ _ ↦
        mul_nonneg (by norm_num only)
          (quarterKernel644.principal_summand_re_nonneg (pow_pos hr₀ 2) m))
  unfold powerIndices644 at hsub
  rw [Finset.sum_image (fun _ ha _ hb he ↦ hinj ha hb he)] at hsub
  rw [← Finset.sum_div, ← Int.cast_sum] at hrow
  unfold fixedPowerGain644
  rw [Finset.mul_sum]
  exact hrow.trans hsub

/-- The lower bound on the profile shift follows from the logarithm bound at
316 and the tangent bound for the logarithm at the reciprocal radius ratio. -/
private theorem power_log_shift_lower_644 {r : ℝ} (hr : 0 < r) :
    (107 / 50) * (1 - 316 / r) ≤ (107 / 50) * (Real.log r - 57557 / 10000) := by
  have hb := (log_box (n := 316) (j := 9) (l := 57557 / 10000) (u := 6) (by decide +kernel)).1
  simp only [Rat.cast_div, Rat.cast_ofNat] at hb
  have h := Real.log_le_sub_one_of_pos (div_pos (by norm_num only : (0 : ℝ) < 316) hr)
  rw [Real.log_div (by norm_num only) hr.ne'] at h
  linarith only [h, hb]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
-- Kernel reduction evaluates the rounded credits of the shared rows at radius 320.
/-- The fixed prime-power sum supplies the required credit for the second
section 122 comparison, by a shared certificate at radius 320. -/
theorem fixed_power_gain_320_644 {r : ℝ} (hr : r ∈ Set.Icc 320 322) :
    0.14274902 ≤ fixedPowerGain644 r := by
  have hsum :=
    shifted_power_sum_le (267 / 10000 : ℚ) (r := 320) (by constructor <;> norm_num only)
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat])
      ((by norm_num only [Rat.cast_div, Rat.cast_ofNat] :
            ((267 / 10000 : ℚ) : ℝ) ≤ (107 / 50) * (1 - 316 / 320)).trans
        (power_log_shift_lower_644 (by norm_num only : (0 : ℝ) < 320)))
  have hc : (14274902 : ℤ) ≤ ∑ a ∈ powerRows644.toFinset, shiftedPowerUnits644 (267 / 10000) a := by
    decide +kernel
  have hR :
    (14274902 : ℝ) ≤
      ((∑ a ∈ powerRows644.toFinset, shiftedPowerUnits644 (267 / 10000) a : ℤ) : ℝ) := by
    exact_mod_cast hc
  exact
    (show 0.14274902 ≤ fixedPowerGain644 320 by linarith only [hR, hsum]).trans
      (fixed_power_gain_mono_644 (by constructor <;> norm_num only)
        ⟨(by norm_num only : (316 : ℝ) ≤ 320).trans hr.1, hr.2⟩ hr.1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
-- Kernel reduction evaluates the rounded credits of the shared rows at radius 321.75.
/-- The same prime-power rows supply the required credit for the third
section 122 comparison from radius 321.75 onward. -/
theorem fixed_power_gain_32175_644 {r : ℝ} (hr : r ∈ Set.Icc (1287 / 4) 322) :
    0.14524702 ≤ fixedPowerGain644 r := by
  have hsum :=
    shifted_power_sum_le (382 / 10000 : ℚ) (r := 1287 / 4) (by constructor <;> norm_num only)
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat])
      ((by norm_num only [Rat.cast_div, Rat.cast_ofNat] :
            ((382 / 10000 : ℚ) : ℝ) ≤ (107 / 50) * (1 - 316 / (1287 / 4))).trans
        (power_log_shift_lower_644 (by norm_num only : (0 : ℝ) < 1287 / 4)))
  have hc : (14524702 : ℤ) ≤ ∑ a ∈ powerRows644.toFinset, shiftedPowerUnits644 (382 / 10000) a := by
    decide +kernel
  have hR :
    (14524702 : ℝ) ≤
      ((∑ a ∈ powerRows644.toFinset, shiftedPowerUnits644 (382 / 10000) a : ℤ) : ℝ) := by
    exact_mod_cast hc
  exact
    (show 0.14524702 ≤ fixedPowerGain644 (1287 / 4) by linarith only [hR, hsum]).trans
      (fixed_power_gain_mono_644 (by constructor <;> norm_num only)
        ⟨(by norm_num only : (316 : ℝ) ≤ 1287 / 4).trans hr.1, hr.2⟩ hr.1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
-- Kernel reduction evaluates the rounded credits of the shared rows at radius 321.8.
/-- The same prime-power rows supply the required credit for the final
section 122 comparison from radius 321.8 onward. -/
theorem fixed_power_gain_3218_644 {r : ℝ} (hr : r ∈ Set.Icc (1609 / 5) 322) :
    0.14326402 ≤ fixedPowerGain644 r := by
  have hsum :=
    shifted_power_sum_le (385 / 10000 : ℚ) (r := 1609 / 5) (by constructor <;> norm_num only)
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat])
      ((by norm_num only [Rat.cast_div, Rat.cast_ofNat] :
            ((385 / 10000 : ℚ) : ℝ) ≤ (107 / 50) * (1 - 316 / (1609 / 5))).trans
        (power_log_shift_lower_644 (by norm_num only : (0 : ℝ) < 1609 / 5)))
  have hc : (14326402 : ℤ) ≤ ∑ a ∈ powerRows644.toFinset, shiftedPowerUnits644 (385 / 10000) a := by
    decide +kernel
  have hR :
    (14326402 : ℝ) ≤
      ((∑ a ∈ powerRows644.toFinset, shiftedPowerUnits644 (385 / 10000) a : ℤ) : ℝ) := by
    exact_mod_cast hc
  exact
    (show 0.14326402 ≤ fixedPowerGain644 (1609 / 5) by linarith only [hR, hsum]).trans
      (fixed_power_gain_mono_644 (by constructor <;> norm_num only)
        ⟨(by norm_num only : (316 : ℝ) ≤ 1609 / 5).trans hr.1, hr.2⟩ hr.1)

/-- The certified prime powers supply at least 0.13825 throughout
the section 122 radius interval. An injectivity check prevents double counting. -/
theorem fixed_power_gain_lower_644 {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    (0.13825 : ℝ) ≤ fixedPowerGain644 r := by
  apply le_trans _ (fixed_power_gain_left_644 hr)
  have hcard : powerIndices644.card = powerRows644.toFinset.card := by decide +kernel
  have hinj := Finset.injOn_of_card_image_eq hcard
  have hrow :=
    Finset.sum_le_sum (s := powerRows644.toFinset)
      (fun a ha ↦ power_row_sound a (power_rows_valid a (List.mem_toFinset.mp ha)))
  have h :=
    Finset.sum_le_sum_of_subset_of_nonneg power_rows_subset (f := anchorPowerCredit644)
      (fun m _ _ ↦ anchor_power_nonneg m)
  unfold powerIndices644 at h
  rw [Finset.sum_image (fun _ ha _ hb he ↦ hinj ha hb he)] at h
  rw [← Finset.sum_div, ← Nat.cast_sum] at hrow
  have hN : 138250 ≤ ∑ a ∈ powerRows644.toFinset, a.credit := by decide +kernel
  have hR : (138250 : ℝ) ≤ ((∑ a ∈ powerRows644.toFinset, a.credit : ℕ) : ℝ) := by exact_mod_cast hN
  unfold fixedPowerGain644
  rw [Finset.mul_sum]
  exact
    (show (0.13825 : ℝ) ≤ ((∑ a ∈ powerRows644.toFinset, a.credit : ℕ) : ℝ) / 1000000 by
          linarith only [hR]).trans
      (hrow.trans h)

/-- Agreement on the tested primes recovers the whole fixed power set
uniformly for radii in [316,322]. -/
theorem quarter_fixed_power_credit_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ}
    (hr : r ∈ Set.Icc 316 322) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    let f := fun m : ℕ ↦ (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) X m).re
    4 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, f m) + fixedPowerGain644 r - (∑' m : ℕ, f m) ≤
      (∑' m, quarterKernel644.summand a X m).re + (∑' m, quarterKernel644.summand b X m).re +
        (∑' m, quarterKernel644.summand c X m).re := by
  intro X f
  have hr₀ : 0 < r := by linarith only [hr.1]
  apply quarter_power_credit_644 a b c (pow_pos hr₀ _) fixedPowers644 _ ht ha hb hc
  intro m hm
  obtain ⟨hm', _, p, k, hp, hp', he⟩ := fixed_power_data_644 hm
  exact
    ⟨(pow_le_pow_left₀ hr₀.le hr.2 2).trans_lt (by exact_mod_cast hm'), p, k, hp,
      (show (p : ℝ) ≤ (316 : ℝ) ^ 2 by exact_mod_cast hp').trans
        (pow_le_pow_left₀ (by norm_num only) hr.1 2),
      he⟩

/-- The positive recovery from the weight at one contributes at least
0.00167 on the section 122 interval. Bound its power at 322 and its
logarithmic factor at 316. -/
theorem quarter_boundary_gain_644 {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    (0.00167 : ℝ) ≤ 1.023 * quarterWeight644 (r ^ 2) 1 := by
  have hr₀ : 0 < r := by linarith only [hr.1]
  have hL := (log_box (n := 316) (j := 9) (l := 57557 / 10000) (u := 6) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hL
  have hl := hL.trans (Real.log_le_log (by norm_num only) hr.1)
  let z := 2687 / 1000 + 2 * Real.log r
  let z₀ : ℝ := 2687 / 1000 + 2 * (57557 / 10000)
  have hz : z₀ ≤ z := by
    dsimp only [z, z₀]; linarith only [hl]
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 103684) (p := 107) (d :=
        100) (lo := 4297 / 1000000000) (hi := 1) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hp
  rw [show (103684 : ℝ) = (322 : ℝ) ^ 2 by norm_num only, ←
    Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 322)] at hp
  norm_num only [Nat.cast_ofNat] at hp
  have hP :=
    hp.trans (Real.rpow_le_rpow_of_nonpos hr₀ hr.2 (by norm_num only : (-(107 / 50) : ℝ) ≤ 0))
  have he :=
    exp_neg_lower (z := 287509 / 100000) (e := 564 / 10000) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have heq :
    Real.exp (-(107 / 100) * z) = Real.exp (-(287509 / 100000)) * r ^ (-(107 / 50) : ℝ) := by
    rw [Real.rpow_def_of_pos hr₀, ← Real.exp_add]
    congr 1
    dsimp only [z]
    ring
  have hprod :=
    mul_le_mul (mul_le_mul he hP (by norm_num only) (Real.exp_pos (-(287509 / 100000))).le)
      (pow_le_pow_left₀ (by norm_num only [z₀]) hz 5) (pow_nonneg (by norm_num only [z₀]) _)
      (by positivity)
  rw [quarter_weight_one_644]
  change _ ≤ 1.023 * ((107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z) * z ^ 5)
  rw [heq, mul_assoc ((107 / 100 : ℝ) ^ 5 / 120)]
  exact
    (by norm_num only [z₀] :
          (0.00167 : ℝ) ≤
            1.023 * ((107 / 100) ^ 5 / 120 * ((564 / 10000) * (4297 / 1000000000) * z₀ ^ 5))).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (by norm_num only))
        (by norm_num only))

/-- With the wide Euler credit in the mass bound, combine the main forward
upper bound, fixed-power lower bound and Gamma recovery. The remaining
condition is a scalar lower bound for the recovered terms on each row. -/
theorem quarter_contradiction_of_gain_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 316 322)
    (hlog : Real.log p + Real.log q + Real.log s = 4 * r)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hprefix :
      ∀ n ∈ Finset.Ioc 0 99000,
        ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3)
    (hM :
      quarterMass644 a + quarterMass644 b + quarterMass644 c ≤
        3 / 4 * r - 11.7421197 + 4 * positiveTail644 (r ^ 2) - 0.0113)
    (hgain :
      320 < r →
        (if r ≤ 1287 / 4 then 0.14274902 else if r ≤ 1609 / 5 then 0.14524702 else 0.14326402) ≤
          fixedPowerGain644 r) :
    False := by
  have hf := quarter_fixed_power_credit_644 a b c hr (fun n ↦ (ht n).1) hA hB hC
  dsimp only at hf
  have hF := quarter_three_forward_upper_644 ha hb hc hp hq hs hG hr hlog hA hB hC ht hprefix
  have hR := quarter_main_remainders_644 ha.1 hb.1 hc.1 ha.2 hb.2 hc.2 hr hlog.le
  dsimp only at hF hR
  have hrow :
    (if r ≤ 320 then 0.783042
      else if r ≤ 1287 / 4 then 0.809968 else if r ≤ 1609 / 5 then 0.823698 else 0.816491) ≤
      fixedPowerGain644 r + 3.35663498 -
          (if r ≤ 320 then 2.242 else if r ≤ 1287 / 4 then 2.235 else 2.22971) +
        1.023 * quarterWeight644 (r ^ 2) 1 +
        (if r ≤ 320 then -0.456620
        else
          if r ≤ 1287 / 4 then -0.452096 else if r ≤ 1609 / 5 then -0.450144 else -0.450088) := by
    by_cases h₁ : r ≤ 320
    · simp only [ite_eq_left h₁]
      linarith only [fixed_power_gain_lower_644 hr, quarter_boundary_gain_644 hr]
    have hgain := hgain (lt_of_not_ge h₁)
    simp only [ite_eq_right h₁]
    by_cases h₂ : r ≤ 1287 / 4
    · simp only [ite_eq_left h₂] at hgain ⊢
      linarith only [hgain, quarter_boundary_gain_644 hr]
    simp only [ite_eq_right h₂] at hgain ⊢
    by_cases h₃ : r ≤ 1609 / 5
    · simp only [ite_eq_left h₃] at hgain ⊢
      linarith only [hgain, quarter_boundary_gain_644 hr]
    simp only [ite_eq_right h₃] at hgain ⊢
    linarith only [hgain, quarter_boundary_gain_644 hr]
  apply
    quarter_comparison_644 hG.riemann hr (fun n ↦ (a n).re + (b n).re + (c n).re)
      (fun n ↦ (ht n : _ ∧ _)) hprefix (M :=
      quarterMass644 a + quarterMass644 b + quarterMass644 c + 0.0113) (by linarith only [hM]) hrow
  unfold quarterAdjustedGap644 quarterPrincipalGap644
  dsimp only
  linarith only [hf, hF, hR]

end PseudoPrime.PrimeTestBounds.MillerRabin
