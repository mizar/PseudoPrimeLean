/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterOdd574
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterOdd574

/-! # Fixed prime-power recovery for section 107 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def squares : List Row :=
  [⟨317, 2, 8, 0, 5758900, 110237, 110240, 317000, 60564105⟩,
    ⟨331, 2, 8, 0, 5802117, 196670, 196673, 331000, 54207278⟩,
    ⟨337, 2, 8, 0, 5820081, 232599, 232602, 337000, 51681661⟩,
    ⟨347, 2, 9, 1, 5849323, 291083, 291086, 347000, 47718152⟩,
    ⟨349, 2, 9, 1, 5855070, 302577, 302580, 349000, 46960728⟩,
    ⟨353, 2, 9, 1, 5866467, 325370, 325373, 353000, 45479716⟩,
    ⟨359, 2, 9, 1, 5883321, 359078, 359081, 359000, 43340508⟩,
    ⟨367, 2, 9, 1, 5905360, 403157, 403160, 367000, 40635043⟩,
    ⟨373, 2, 9, 1, 5921577, 435590, 435593, 373000, 38710797⟩,
    ⟨379, 2, 9, 1, 5937535, 467506, 467509, 379000, 36872059⟩,
    ⟨383, 2, 9, 1, 5948033, 488504, 488507, 383000, 35691907⟩,
    ⟨389, 2, 9, 1, 5963578, 519592, 519595, 389000, 33987627⟩,
    ⟨397, 2, 9, 1, 5983935, 560306, 560309, 397000, 31832885⟩,
    ⟨401, 2, 9, 1, 5993960, 580356, 580359, 401000, 30803781⟩,
    ⟨409, 2, 9, 1, 6013714, 619864, 619867, 409000, 28837430⟩,
    ⟨419, 2, 9, 1, 6037869, 668175, 668178, 419000, 26542836⟩,
    ⟨421, 2, 9, 1, 6042631, 677699, 677702, 421000, 26104640⟩,
    ⟨431, 2, 9, 1, 6066107, 724650, 724653, 431000, 24011909⟩,
    ⟨433, 2, 9, 1, 6070736, 733909, 733912, 433000, 23612358⟩,
    ⟨439, 2, 9, 1, 6084498, 761432, 761435, 439000, 22450036⟩,
    ⟨443, 2, 9, 1, 6093568, 779573, 779576, 443000, 21704542⟩,
    ⟨449, 2, 9, 1, 6107021, 806479, 806482, 449000, 20628745⟩,
    ⟨457, 2, 9, 1, 6124682, 841800, 841803, 457000, 19270131⟩,
    ⟨461, 2, 9, 1, 6133397, 859230, 859233, 461000, 18621889⟩,
    ⟨463, 2, 9, 1, 6137726, 867888, 867891, 463000, 18305286⟩,
    ⟨467, 2, 9, 1, 6146328, 885092, 885095, 467000, 17686747⟩,
    ⟨479, 2, 9, 1, 6171699, 935835, 935838, 479000, 15943313⟩,
    ⟨487, 2, 9, 1, 6188263, 968962, 968965, 487000, 14869238⟩,
    ⟨491, 2, 9, 2, 6196443, 985322, 985325, 491000, 14357146⟩,
    ⟨499, 2, 9, 2, 6212605, 1017646, 1017649, 499000, 13380462⟩]

private def odds : List Row :=
  [⟨47, 3, 6, 0, 3850146, 142876, 142879, 322216, 38744724⟩,
    ⟨53, 3, 6, 1, 3970290, 503309, 503312, 385846, 23249242⟩,
    ⟨59, 3, 6, 1, 4077536, 825046, 825049, 453188, 13271339⟩,
    ⟨61, 3, 6, 1, 4110872, 925055, 925058, 476426, 10869096⟩,
    ⟨67, 3, 6, 2, 4204691, 1206511, 1206514, 548419, 5706346⟩,
    ⟨71, 3, 6, 2, 4262678, 1380473, 1380476, 598257, 3552756⟩,
    ⟨73, 3, 6, 2, 4290458, 1463812, 1463815, 623713, 2759474⟩,
    ⟨79, 3, 6, 3, 4369446, 1700777, 1700780, 702168, 1197715⟩,
    ⟨83, 3, 6, 3, 4418839, 1848955, 1848958, 756166, 634270⟩,
    ⟨89, 3, 7, 3, 4488635, 2058343, 2058346, 839625, 207193⟩,
    ⟨97, 3, 7, 3, 4574709, 2316566, 2316569, 955340, 28418⟩,
    ⟨101, 3, 7, 4, 4615119, 2437795, 2437798, 1015038, 7209⟩,
    ⟨103, 3, 7, 4, 4634727, 2496621, 2496624, 1045336, 3077⟩,
    ⟨107, 3, 7, 4, 4672827, 2610920, 2610923, 1106817, 309⟩,
    ⟨109, 3, 7, 4, 4691346, 2666477, 2666480, 1137994, 56⟩,
    ⟨11, 5, 4, 1, 2397894, 581910, 581913, 401312, 12289946⟩,
    ⟨13, 5, 4, 2, 2564948, 1417180, 1417183, 609339, 1911439⟩,
    ⟨7, 7, 3, 3, 1945909, 2213805, 2213808, 907493, 30038⟩,
    ⟨3, 11, 2, 1, 1098611, 677169, 677172, 420889, 4750699⟩,
    ⟨2, 17, 1, 1, 693146, 375936, 375939, 362039, 4975696⟩,
    ⟨2, 19, 1, 3, 693146, 1762230, 1762233, 724078, 147131⟩]

private def roots : Finset ℕ :=
  squares.toFinset.image Row.p

private theorem square_valid : ∀ a ∈ squares, a.Valid 300 := by decide +kernel

private theorem square_degrees : ∀ a ∈ squares.toFinset, a.j = 2 := by decide +kernel

private theorem roots_range : ∀ k ∈ roots, 313 < k ∧ k ≤ 499 := by decide +kernel

private theorem odd_gain107 {r : ℝ} (hr : r ∈ Set.Icc 300 313) : 0.01243 < oddGain574 r := by
  have h :=
    endpoint_rows_lower (R := 300) (by decide) odds (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (M := 124300000) (by decide +kernel)
  have hm : oddGain574 300 ≤ oddGain574 r :=
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun _ hk ↦ term_mono hk (by norm_num only) hr.1 hr.2)) (by norm_num only)
  norm_num only at h
  linarith only [h, hm]

private theorem square_gain107 {r : ℝ} (hr : r ∈ Set.Icc 300 313) :
    0.09196 <
      4 *
        ∑ k ∈ roots,
          (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) (k ^ 2)).re := by
  have hm (k : ℕ) (hk : k ∈ roots) :
    (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (300 ^ 2) (k ^ 2)).re ≤
      (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) (k ^ 2)).re := by
    obtain ⟨hl, hu⟩ := roots_range k hk
    apply power_term_mono (m := k ^ 2) (U := 313) _ (by norm_num only) hr.1 hr.2
    exact ⟨Nat.pow_lt_pow_left hl (by decide), (Nat.pow_le_pow_left hu 2).trans (by decide)⟩
  apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hm) (by norm_num only))
  unfold roots
  rw [Finset.sum_image
      (show ∀ a ∈ squares.toFinset, ∀ b ∈ squares.toFinset, a.p = b.p → a = b by decide +kernel),
    Finset.mul_sum]
  have hs :=
    Finset.sum_le_sum (s := squares.toFinset)
      (fun a ha ↦ by
        have h := row_sound a (by decide : 0 < 300) (square_valid a (List.mem_toFinset.mp ha))
        simpa only [square_degrees a ha, Nat.cast_ofNat] using h)
  have ht : 919600000 < ∑ a ∈ squares.toFinset, a.credit := by decide +kernel
  have hh : (919600000 : ℝ) < ∑ a ∈ squares.toFinset, (a.credit : ℝ) := by exact_mod_cast ht
  rw [← Finset.sum_div] at hs
  linarith only [hh, hs]

/-- Passing pair characters on the section 107 interval recover 0.09196
from selected squares and 0.01243 from the shared odd powers. -/
theorem section107_arithmetic_recovered {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r P : ℝ}
    (hr : r ∈ Set.Icc 300 313) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    P ≤ 4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) - (∑' k : ℕ, f k) →
      P + 0.09196 + 0.01243 <
        (∑' k : ℕ, quarterKernel570.summand a X k).re +
          (∑' k : ℕ, quarterKernel570.summand b X k).re +
          (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  intro X f hP
  have hroots (k : ℕ) (hk : k ∈ roots) : (k : ℝ) ≤ r ^ 2 ∧ r ^ 2 < (k : ℝ) ^ 2 := by
    obtain ⟨hl, hu⟩ := roots_range k hk
    have h0 : 0 ≤ r := (by norm_num only : (0 : ℝ) ≤ 300).trans hr.1
    exact
      ⟨(show (k : ℝ) ≤ 499 by exact_mod_cast hu).trans
          ((by norm_num only : (499 : ℝ) ≤ 300 ^ 2).trans
            (pow_le_pow_left₀ (by norm_num only) hr.1 2)),
        pow_lt_pow_left₀ (hr.2.trans_lt (by exact_mod_cast hl)) h0 (by decide)⟩
  have ha := square_odd_lower_626 a b c (by linarith only [hr.1]) hr.2 roots hroots ht hA hB hC
  dsimp only [X, f] at ha hP ⊢
  rw [←
    Complex.re_tsum
      (quarterKernel570.summable_summand (1 : DirichletCharacter ℂ 1)
        (sq_pos_of_pos (by linarith only [hr.1] : 0 < r)))] at hP
  linarith only [ha, hP, square_gain107 hr, odd_gain107 hr]

end PseudoPrime.PrimeTestBounds.MillerRabin
