/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterOdd574
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterOdd574

/-! # Shared fixed power recovery through logarithm 632 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A selected principal term increases with the radius when the index stays
above the cutoff and lies in the kernel support at the left radius. -/
theorem fixed_power_weight_mono {m : ℕ} {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (hm : r ^ 2 ≤ (m : ℝ))
    (hs : Real.log ((m : ℝ) / a ^ 2) ≤ 14 / 5) :
    (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (a ^ 2) m).re ≤
      (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) m).re := by
  have hr := ha.trans_le har
  have hm0 : 0 < m := Nat.cast_pos.mp ((sq_pos_of_pos hr).trans_le hm)
  have hx := pow_le_pow_left₀ ha.le har 2
  have hl :=
    Real.log_le_log (div_pos (Nat.cast_pos.mpr hm0) (sq_pos_of_pos hr))
      (div_le_div_of_nonneg_left (Nat.cast_nonneg m) (sq_pos_of_pos ha) hx)
  have h0 := Real.log_nonneg ((one_le_div (sq_pos_of_pos hr)).mpr hm)
  rw [quarter_summand_570 (sq_pos_of_pos ha) hm0 hs,
    quarter_summand_570 (sq_pos_of_pos hr) hm0 (hl.trans hs)]
  apply mul_le_mul_of_nonneg_right _ ArithmeticFunction.vonMangoldt_nonneg
  unfold quarterWeight570
  dsimp only
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by norm_num only)
  apply fifth_increasing
  · constructor <;> norm_num only <;> linarith only [hs, hl, h0]
  · constructor <;> norm_num only <;> linarith only [hs, hl, h0]
  · norm_num only
    linarith only [hl]

/-- Any finite set of additional prime powers above the cutoff may be recovered
when their prime bases lie in the passing prefix. The set can mix odd and
even powers, with disjointness from the principal prefix checked by size. -/
theorem quarter_recover_fixed_powers {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {X : ℝ}
    (hX : 0 < X) (T : Finset ℕ) (hT : ∀ m ∈ T, X < m ∧ ∃ l k : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ m = l ^ k)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + 4 * (∑ k ∈ T, f k) -
        (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  exact kernel_recover_fixed_powers quarterKernel570 a b c hX T hT ht hA hB hC

/-- The even indices are squares of the selected prime powers. The enclosing
root interval works at all five comparison radii. -/
private def evenIndices632 : Finset ℕ :=
  ((Finset.Ioc 316 1096).filter IsPrimePow).image (fun t ↦ t ^ 2)

/-- One set of prime powers is shared over the whole radius range. -/
private def powerIndices632 : Finset ℕ :=
  evenIndices632 ∪ oddIndices574

/-- Every selected index is above the prefix, stays in the left support,
and is a power of a prime in the passing prefix. -/
private theorem power_data632 (m : ℕ) (hm : m ∈ powerIndices632) :
    316 ^ 2 < m ∧ m ≤ 16 * 313 ^ 2 ∧ ∃ p k : ℕ, p.Prime ∧ p ≤ 313 ^ 2 ∧ m = p ^ k := by
  rcases Finset.mem_union.mp hm with he | ho
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hb, ht⟩ := Finset.mem_filter.mp ht
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff t).mp ht
    obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hb
    have hpk : p ≤ p ^ k := le_self_pow₀ hp.one_lt.le hk.ne'
    exact
      ⟨(Nat.pow_lt_pow_left hl (by decide)), (Nat.pow_le_pow_left hu 2).trans (by decide), p, k * 2,
        hp, hpk.trans (hu.trans (by decide)), (pow_mul p k 2).symm⟩
  · obtain ⟨⟨p, k⟩, hk, rfl⟩ := Finset.mem_image.mp ho
    have h :=
      (show
          ∀ u ∈ oddData574,
            u.1.Prime ∧ u.1 ≤ 313 ^ 2 ∧ 316 ^ 2 < u.1 ^ u.2 ∧ u.1 ^ u.2 ≤ 16 * 313 ^ 2
          by decide +kernel)
        (p, k) hk
    exact ⟨h.2.2.1, h.2.2.2, p, k, h.1, h.2.1, rfl⟩

/-- Four times the additional principal mass from the fixed power set. -/
noncomputable def fixedPowerGain632 (r : ℝ) : ℝ :=
  4 * ∑ k ∈ powerIndices632, (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re

/-- The shared fixed power gain increases throughout the radius interval. -/
theorem fixed_power_gain_mono_632 {a r : ℝ} (ha : 313 ≤ a) (har : a ≤ r) (hr : r ≤ 316) :
    fixedPowerGain632 a ≤ fixedPowerGain632 r := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  apply Finset.sum_le_sum
  intro m hm
  have h := power_data632 m hm
  have ha0 : 0 < a := by linarith only [ha]
  have hr0 : 0 < r := ha0.trans_le har
  have hm' : r ^ 2 ≤ (m : ℝ) := (pow_le_pow_left₀ hr0.le hr 2).trans (by exact_mod_cast h.1.le)
  have h16 : (m : ℝ) / a ^ 2 ≤ (2 : ℝ) ^ 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos ha0)).mpr
    have hb : (m : ℝ) ≤ 16 * (313 : ℝ) ^ 2 := by exact_mod_cast h.2.1
    have hc :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num only) ha 2)
        (by norm_num only : (0 : ℝ) ≤ 16)
    linarith only [hb, hc]
  have hpj : 0 < (m : ℝ) := (sq_pos_of_pos hr0).trans_le hm'
  have hs := Real.log_le_log (div_pos hpj (sq_pos_of_pos ha0)) h16
  rw [Real.log_pow, Nat.cast_ofNat] at hs
  exact fixed_power_weight_mono ha0 har hm' (by linarith only [hs, Real.log_two_lt_d9])

/-- The fixed odd and even powers can be recovered together above the
quarter-square cutoff in the three passing pair characters. -/
theorem fixed_arithmetic_lower_632 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ}
    (hr : r ∈ Set.Icc 313 316) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + fixedPowerGain632 r -
        (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  have hr0 : 0 < r := by linarith only [hr.1]
  apply quarter_recover_fixed_powers a b c (sq_pos_of_pos hr0) powerIndices632 _ ht hA hB hC
  intro m hm
  obtain ⟨hM, _, l, k, hprime, hsmall, hpow⟩ := power_data632 m hm
  have h₁ := pow_le_pow_left₀ hr0.le hr.2 2
  have h₂ := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 313) hr.1 2
  exact
    ⟨h₁.trans_lt (by exact_mod_cast hM), l, k, hprime,
      (show (l : ℝ) ≤ 313 ^ 2 by exact_mod_cast hsmall).trans h₂, hpow⟩

/-- Rounded logarithm, square-root and credit certificates at radius 313. -/
private def fixedRows313 : List Row :=
  [⟨317, 2, 9, 1, 5758901, 25397, 25398, 317001, 64873506⟩,
    ⟨47, 3, 6, 1, 3850147, 58036, 58037, 322216, 41579715⟩,
    ⟨331, 2, 9, 1, 5802118, 111830, 111831, 331001, 58359712⟩,
    ⟨337, 2, 9, 1, 5820082, 147759, 147760, 337001, 55763613⟩,
    ⟨7, 6, 3, 1, 1945910, 183054, 183055, 343001, 17759233⟩,
    ⟨347, 2, 9, 1, 5849324, 206243, 206244, 347001, 51679309⟩,
    ⟨349, 2, 9, 1, 5855071, 217737, 217738, 349001, 50897305⟩,
    ⟨353, 2, 9, 1, 5866468, 240529, 240530, 353001, 49366822⟩,
    ⟨359, 2, 9, 1, 5883322, 274238, 274239, 359001, 47152512⟩,
    ⟨19, 4, 5, 1, 2944438, 285349, 285350, 361001, 23217759⟩,
    ⟨2, 17, 2, 1, 693147, 291095, 291096, 362039, 5419686⟩,
    ⟨367, 2, 9, 1, 5905361, 318317, 318318, 367001, 44345810⟩,
    ⟨373, 2, 9, 1, 5921578, 350750, 350751, 373001, 42344994⟩,
    ⟨379, 2, 9, 1, 5937536, 382666, 382667, 379001, 40429315⟩,
    ⟨383, 2, 9, 1, 5948034, 403663, 403664, 383001, 39197777⟩,
    ⟨53, 3, 6, 1, 3970291, 418469, 418470, 385846, 25562112⟩,
    ⟨389, 2, 9, 1, 5963579, 434752, 434753, 389001, 37416221⟩,
    ⟨397, 2, 9, 1, 5983936, 475466, 475467, 397001, 35158520⟩,
    ⟨401, 2, 9, 1, 5993961, 495516, 495517, 401001, 34078025⟩,
    ⟨11, 5, 4, 1, 2397895, 497069, 497070, 401312, 13598095⟩,
    ⟨409, 2, 9, 1, 6013715, 535023, 535024, 409001, 32009268⟩,
    ⟨419, 2, 9, 1, 6037870, 583335, 583336, 419001, 29587519⟩,
    ⟨3, 11, 2, 1, 1098612, 592328, 592329, 420889, 5299962⟩,
    ⟨421, 2, 9, 1, 6042632, 592859, 592860, 421001, 29124058⟩,
    ⟨431, 2, 9, 1, 6066108, 639809, 639810, 431001, 26905991⟩,
    ⟨433, 2, 9, 1, 6070737, 649069, 649070, 433001, 26481543⟩,
    ⟨439, 2, 9, 1, 6084499, 676592, 676593, 439001, 25245098⟩,
    ⟨443, 2, 9, 2, 6093569, 694733, 694734, 443001, 24450601⟩,
    ⟨449, 2, 9, 2, 6107022, 721639, 721640, 449001, 23301964⟩,
    ⟨59, 3, 6, 2, 4077537, 740205, 740206, 453188, 15019978⟩,
    ⟨457, 2, 9, 2, 6124683, 756960, 756961, 457001, 21847549⟩,
    ⟨461, 2, 9, 2, 6133398, 774389, 774390, 461001, 21152033⟩,
    ⟨463, 2, 9, 2, 6137727, 783047, 783048, 463001, 20811935⟩,
    ⟨467, 2, 9, 2, 6146329, 800252, 800253, 467001, 20146692⟩,
    ⟨61, 3, 6, 2, 4110873, 840215, 840216, 476426, 12436923⟩,
    ⟨479, 2, 9, 2, 6171700, 850994, 850995, 479001, 18265911⟩,
    ⟨487, 2, 9, 2, 6188264, 884121, 884122, 487001, 17102556⟩,
    ⟨491, 2, 9, 2, 6196444, 900481, 900482, 491001, 16546539⟩,
    ⟨499, 2, 9, 2, 6212606, 932805, 932806, 499001, 15483476⟩,
    ⟨503, 2, 9, 2, 6220590, 948773, 948774, 503001, 14975533⟩,
    ⟨509, 2, 9, 2, 6232448, 972489, 972490, 509001, 14241867⟩,
    ⟨2, 18, 2, 2, 693147, 984242, 984243, 512001, 1543041⟩,
    ⟨521, 2, 10, 2, 6255750, 1019093, 1019094, 521001, 12871186⟩,
    ⟨523, 2, 10, 2, 6259581, 1026756, 1026757, 523001, 12654684⟩,
    ⟨23, 4, 5, 2, 3135494, 1049570, 1049571, 529001, 6012366⟩,
    ⟨541, 2, 10, 2, 6293419, 1094432, 1094433, 541001, 10848731⟩,
    ⟨547, 2, 10, 2, 6304448, 1116491, 1116492, 547001, 10300374⟩,
    ⟨67, 3, 7, 2, 4204692, 1121671, 1121672, 548419, 6782951⟩,
    ⟨557, 2, 10, 2, 6322565, 1152724, 1152725, 557001, 9441402⟩,
    ⟨563, 2, 10, 2, 6333279, 1174152, 1174153, 563001, 8957332⟩,
    ⟨569, 2, 10, 2, 6343880, 1195354, 1195355, 569001, 8495514⟩,
    ⟨571, 2, 10, 2, 6347389, 1202372, 1202373, 571001, 8346357⟩,
    ⟨577, 2, 10, 2, 6357842, 1223278, 1223279, 577001, 7912798⟩,
    ⟨587, 2, 10, 2, 6375024, 1257643, 1257644, 587001, 7234555⟩,
    ⟨593, 2, 10, 2, 6385194, 1277982, 1277983, 593001, 6852857⟩,
    ⟨71, 3, 7, 2, 4262679, 1295633, 1295634, 598257, 4355489⟩,
    ⟨599, 2, 10, 2, 6395261, 1298116, 1298117, 599001, 6489118⟩,
    ⟨601, 2, 10, 2, 6398594, 1304783, 1304784, 601001, 6371722⟩,
    ⟨607, 2, 10, 2, 6408528, 1324651, 1324652, 607001, 6030734⟩,
    ⟨13, 5, 4, 2, 2564949, 1332340, 1332341, 609339, 2360916⟩,
    ⟨613, 2, 10, 2, 6418364, 1344323, 1344324, 613001, 5705977⟩,
    ⟨617, 2, 10, 2, 6424869, 1357331, 1357332, 617001, 5498142⟩,
    ⟨619, 2, 10, 2, 6428105, 1363804, 1363805, 619001, 5396741⟩,
    ⟨73, 3, 7, 2, 4290459, 1378971, 1378972, 623713, 3442895⟩,
    ⟨5, 8, 3, 2, 1609437, 1383096, 1383097, 625001, 1275595⟩,
    ⟨631, 2, 10, 3, 6447305, 1402205, 1402206, 631001, 4822229⟩,
    ⟨641, 2, 10, 3, 6463029, 1433652, 1433653, 641001, 4385273⟩,
    ⟨643, 2, 10, 3, 6466144, 1439883, 1439884, 643001, 4302173⟩,
    ⟨647, 2, 10, 3, 6472346, 1452286, 1452287, 647001, 4140117⟩,
    ⟨653, 2, 10, 3, 6481577, 1470747, 1470748, 653001, 3907059⟩,
    ⟨659, 2, 10, 3, 6490723, 1489040, 1489041, 659001, 3685552⟩,
    ⟨661, 2, 10, 3, 6493753, 1495101, 1495102, 661001, 3614193⟩,
    ⟨673, 2, 10, 3, 6511745, 1531084, 1531085, 673001, 3210842⟩,
    ⟨677, 2, 10, 3, 6517671, 1542936, 1542937, 677001, 3085412⟩,
    ⟨683, 2, 10, 3, 6526494, 1560583, 1560584, 683001, 2905268⟩,
    ⟨691, 2, 10, 3, 6538139, 1583873, 1583874, 691001, 2679338⟩,
    ⟨701, 2, 10, 3, 6552507, 1612609, 1612610, 701001, 2418491⟩,
    ⟨79, 3, 7, 3, 4369447, 1615937, 1615938, 702168, 1593017⟩,
    ⟨709, 2, 10, 3, 6563855, 1635304, 1635305, 709001, 2225949⟩,
    ⟨719, 2, 10, 3, 6577861, 1663316, 1663317, 719001, 2004024⟩,
    ⟨2, 19, 2, 3, 693147, 1677390, 1677391, 724078, 199879⟩,
    ⟨727, 2, 10, 3, 6588926, 1685446, 1685447, 727001, 1840506⟩,
    ⟨3, 12, 2, 3, 1098612, 1690941, 1690942, 729001, 300244⟩,
    ⟨733, 2, 10, 3, 6597145, 1701885, 1701886, 733001, 1725539⟩,
    ⟨739, 2, 10, 3, 6605297, 1718189, 1718190, 739001, 1616816⟩,
    ⟨743, 2, 10, 3, 6610696, 1728985, 1728986, 743001, 1547656⟩,
    ⟨751, 2, 10, 3, 6621405, 1750404, 1750405, 751001, 1416927⟩,
    ⟨83, 3, 7, 3, 4418840, 1764115, 1764116, 756166, 891763⟩,
    ⟨757, 2, 10, 3, 6629363, 1766320, 1766321, 757001, 1325206⟩,
    ⟨761, 2, 10, 3, 6634633, 1776860, 1776861, 761001, 1266932⟩,
    ⟨769, 2, 10, 3, 6645090, 1797775, 1797776, 769001, 1156941⟩,
    ⟨773, 2, 10, 3, 6650279, 1808151, 1808152, 773001, 1105084⟩,
    ⟨787, 2, 10, 3, 6668228, 1844050, 1844051, 787001, 938904⟩,
    ⟨797, 2, 10, 3, 6680854, 1869302, 1869303, 797001, 833706⟩,
    ⟨809, 2, 10, 3, 6695798, 1899191, 1899192, 809001, 720864⟩,
    ⟨811, 2, 10, 3, 6698268, 1904129, 1904130, 811001, 703383⟩,
    ⟨821, 2, 10, 3, 6710523, 1928639, 1928640, 821001, 621275⟩,
    ⟨823, 2, 10, 3, 6712956, 1933506, 1933507, 823001, 605868⟩,
    ⟨827, 2, 10, 3, 6717804, 1943203, 1943204, 827001, 576028⟩,
    ⟨829, 2, 10, 3, 6720220, 1948033, 1948034, 829001, 561583⟩,
    ⟨839, 2, 10, 3, 6732210, 1972015, 1972016, 839001, 493859⟩,
    ⟨89, 3, 7, 3, 4488636, 1973502, 1973503, 839625, 326582⟩,
    ⟨29, 4, 5, 3, 3367295, 1976776, 1976777, 841001, 240591⟩,
    ⟨853, 2, 10, 3, 6748759, 2005112, 2005113, 853001, 410734⟩,
    ⟨857, 2, 10, 3, 6753437, 2014469, 2014470, 857001, 389280⟩,
    ⟨859, 2, 10, 3, 6755768, 2019131, 2019132, 859001, 378912⟩,
    ⟨863, 2, 10, 3, 6760414, 2028423, 2028424, 863001, 358873⟩,
    ⟨877, 2, 10, 3, 6776506, 2060607, 2060608, 877001, 295612⟩,
    ⟨881, 2, 10, 3, 6781057, 2069708, 2069709, 881001, 279367⟩,
    ⟨883, 2, 10, 3, 6783325, 2074244, 2074245, 883001, 271528⟩,
    ⟨887, 2, 10, 4, 6787844, 2083283, 2083284, 887001, 256407⟩,
    ⟨907, 2, 10, 4, 6810142, 2127878, 2127879, 907001, 190953⟩,
    ⟨7, 7, 3, 4, 1945910, 2128964, 2128965, 907493, 54153⟩,
    ⟨911, 2, 10, 4, 6814542, 2136679, 2136680, 911001, 179711⟩,
    ⟨919, 2, 10, 4, 6823286, 2154165, 2154166, 919001, 158880⟩,
    ⟨929, 2, 10, 4, 6834108, 2175811, 2175812, 929001, 135712⟩,
    ⟨937, 2, 10, 4, 6842683, 2192960, 2192961, 937001, 119272⟩,
    ⟨941, 2, 10, 4, 6846943, 2201479, 2201480, 941001, 111698⟩,
    ⟨947, 2, 10, 4, 6853299, 2214191, 2214192, 947001, 101088⟩,
    ⟨953, 2, 10, 4, 6859614, 2226823, 2226824, 953001, 91331⟩,
    ⟨97, 3, 7, 4, 4574710, 2231726, 2231727, 955340, 58497⟩,
    ⟨31, 4, 5, 4, 3433987, 2243542, 2243543, 961001, 39775⟩,
    ⟨967, 2, 10, 4, 6874198, 2255990, 2255991, 967001, 71568⟩,
    ⟨971, 2, 10, 4, 6878326, 2264246, 2264247, 971001, 66625⟩,
    ⟨977, 2, 10, 4, 6884486, 2276566, 2276567, 977001, 59743⟩,
    ⟨983, 2, 10, 4, 6890609, 2288811, 2288812, 983001, 53461⟩,
    ⟨991, 2, 10, 4, 6898714, 2305022, 2305023, 991001, 45944⟩,
    ⟨997, 2, 10, 4, 6904750, 2317095, 2317096, 997001, 40899⟩,
    ⟨1009, 2, 10, 4, 6916715, 2341023, 2341024, 1009001, 32175⟩,
    ⟨1013, 2, 10, 4, 6920671, 2348936, 2348937, 1013001, 29634⟩,
    ⟨101, 3, 7, 4, 4615120, 2352955, 2352956, 1015038, 18936⟩,
    ⟨1019, 2, 10, 4, 6926577, 2360747, 2360748, 1019001, 26134⟩,
    ⟨1021, 2, 10, 4, 6928537, 2364669, 2364670, 1021001, 25046⟩,
    ⟨2, 20, 2, 4, 693147, 2370537, 2370538, 1024001, 2348⟩,
    ⟨1031, 2, 11, 4, 6938284, 2384162, 2384163, 1031001, 20150⟩,
    ⟨1033, 2, 11, 4, 6940222, 2388038, 2388039, 1033001, 19272⟩,
    ⟨1039, 2, 11, 4, 6946013, 2399621, 2399622, 1039001, 16826⟩,
    ⟨103, 3, 7, 4, 4634728, 2411780, 2411781, 1045336, 9684⟩,
    ⟨1049, 2, 11, 4, 6955592, 2418778, 2418779, 1049001, 13318⟩,
    ⟨1051, 2, 11, 4, 6957497, 2422588, 2422589, 1051001, 12694⟩,
    ⟨1061, 2, 11, 4, 6966967, 2441527, 2441528, 1061001, 9924⟩,
    ⟨1063, 2, 11, 4, 6968850, 2445294, 2445295, 1063001, 9434⟩,
    ⟨1069, 2, 11, 4, 6974478, 2456551, 2456552, 1069001, 8083⟩,
    ⟨1087, 2, 11, 4, 6991176, 2489947, 2489948, 1087001, 4943⟩,
    ⟨1091, 2, 11, 4, 6994849, 2497293, 2497294, 1091001, 4403⟩,
    ⟨1093, 2, 11, 4, 6996681, 2500956, 2500957, 1093001, 4152⟩,
    ⟨107, 3, 7, 4, 4672828, 2526080, 2526081, 1106817, 1811⟩,
    ⟨109, 3, 7, 4, 4691347, 2581637, 2581638, 1137994, 602⟩]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
-- The independent row checks use the fixed set once at its left anchor.
/-- Every entry of the fixed certificate passes the analytic row checker. -/
private theorem fixed_rows_valid313 : ∀ a ∈ fixedRows313, a.Valid 313 := by decide +kernel

/-- The finite certificate and the analytic recovery have the same index set. -/
private theorem fixed_rows_image313 :
    powerIndices632 = fixedRows313.toFinset.image (fun a ↦ a.p ^ a.j) := by decide +kernel

/-- The index map has no repeated values among the certificate rows. -/
private theorem fixed_rows_inj313 :
    ∀ a ∈ fixedRows313.toFinset, ∀ b ∈ fixedRows313.toFinset, a.p ^ a.j = b.p ^ b.j → a = b := by
  have hc :
    (fixedRows313.toFinset.image (fun a ↦ a.p ^ a.j)).card = fixedRows313.toFinset.card := by
    decide +kernel
  exact fun _ ha _ hb he ↦ Finset.injOn_of_card_image_eq hc ha hb he

/-- The summed integer credits clear the first anchor threshold. -/
private theorem fixed_rows_total313 : 1448000000 < ∑ a ∈ fixedRows313.toFinset, a.credit := by
  decide +kernel

/-- The recovered mass is above 0.1448 throughout radii 313 to 316. -/
theorem fixed_power_gain_lower_632 {r : ℝ} (hr : r ∈ Set.Icc 313 316) :
    0.1448 < fixedPowerGain632 r := by
  have hm := fixed_power_gain_mono_632 (by norm_num only : (313 : ℝ) ≤ 313) hr.1 hr.2
  apply lt_of_lt_of_le _ hm
  have h :=
    Finset.sum_le_sum (s := fixedRows313.toFinset)
      (fun a ha ↦
        row_sound a (by decide : 0 < 313) (fixed_rows_valid313 a (List.mem_toFinset.mp ha)))
  unfold fixedPowerGain632
  rw [fixed_rows_image313, Finset.sum_image fixed_rows_inj313, Finset.mul_sum]
  apply lt_of_lt_of_le _ h
  rw [← Finset.sum_div, ← Nat.cast_sum]
  have hn : (1448000000 : ℝ) < ((∑ a ∈ fixedRows313.toFinset, a.credit : ℕ) : ℝ) := by
    exact_mod_cast fixed_rows_total313
  linarith only [hn]

end PseudoPrime.PrimeTestBounds.MillerRabin
