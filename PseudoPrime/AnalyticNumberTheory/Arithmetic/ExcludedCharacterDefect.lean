/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CompositeMangoldtSqrtBound

/-! # Weighted character defects with an arbitrary excluded prime support -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a nonnegative real weight, the character defect at any integer is at
most twice its Mangoldt weight. Use the character norm bound and the real-part
lower bound. This termwise estimate controls both prime and composite contributions. -/
theorem mangoldt_character_defect_term_le {f : ℕ} (χ : DirichletCharacter ℂ f) (n : ℕ) {w : ℝ}
    (hw : 0 ≤ w) :
    (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w ≤
      2 * ArithmeticFunction.vonMangoldt n * w := by
  have hr := (abs_le.mp (Complex.abs_re_le_norm (χ n))).1
  have hn := χ.norm_le_one n
  have hc : 1 - (χ n).re ≤ 2 := by linarith only [hr, hn]
  have hm :=
    mul_le_mul_of_nonneg_right hc (mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) hw)
  nlinarith only [hm]

/-- If a character is one on every prime through x outside nonzero m, its
prime-indexed weighted defect, with weights between zero and 1/3, costs at most
(2/3) times the log of the distinct prime support of m. Restrict to divisors
of m and compare nonnegative sums over primeFactors. -/
theorem prime_character_defect_le_excluded {f m : ℕ} (χ : DirichletCharacter ℂ f) (hm : m ≠ 0)
    {x : ℝ} (hx : 0 ≤ x) (w : ℕ → ℝ) (hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, 0 ≤ w n ∧ w n ≤ 1 / 3)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬p ∣ m → χ p = 1) :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
        (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w n) ≤
      (2 / 3 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p := by
  classical
  let P := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime
  let T := P.filter (fun n ↦ n ∣ m)
  let D := fun n : ℕ ↦ (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w n
  have he : ∑ n ∈ T, D n = ∑ n ∈ P, D n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    have hnP := Finset.mem_filter.mp hn
    have hnd : ¬n ∣ m := fun hd ↦ hnot (Finset.mem_filter.mpr ⟨hn, hd⟩)
    have hnle := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hnP.1).2).trans (Nat.floor_le hx)
    dsimp only [D]
    rw [hsmall n hnP.2 hnle hnd, Complex.one_re]
    ring
  change (∑ n ∈ P, D n) ≤ _
  rw [← he]
  calc
    _ ≤ ∑ n ∈ T, (2 / 3 : ℝ) * Real.log n := by
      apply Finset.sum_le_sum
      intro n hn
      have ht := Finset.mem_filter.mp hn
      have hP := Finset.mem_filter.mp ht.1
      have hb := mangoldt_character_defect_term_le χ n (hw n hP.1).1
      have hc :=
        mul_le_mul_of_nonneg_left (hw n hP.1).2
          (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
            (ArithmeticFunction.vonMangoldt_nonneg (n := n)))
      rw [ArithmeticFunction.vonMangoldt_apply_prime hP.2] at hb hc
      dsimp only [D]
      rw [ArithmeticFunction.vonMangoldt_apply_prime hP.2]
      nlinarith only [hb, hc]
    _ ≤ ∑ n ∈ m.primeFactors, (2 / 3 : ℝ) * Real.log n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have ht := Finset.mem_filter.mp hn
        exact Nat.mem_primeFactors.mpr ⟨(Finset.mem_filter.mp ht.1).2, ht.2, hm⟩
      · intro n hn _
        apply mul_nonneg (by norm_num only)
        apply Real.log_nonneg
        exact_mod_cast (Nat.prime_of_mem_primeFactors hn).one_lt.le
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- For x ≥ 1 and nonzero excluded modulus m, prime triviality outside m
bounds the full weighted character defect by (2/3)sum(log p)+12sqrt x.
Split prime and nonprime indices and combine their certified costs.
The character level is independent of m and no RH is needed. -/
theorem weighted_character_defect_le_excluded {f m : ℕ} (χ : DirichletCharacter ℂ f) (hm : m ≠ 0)
    {x : ℝ} (hx : 1 ≤ x) (w : ℕ → ℝ) (hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, 0 ≤ w n ∧ w n ≤ 1 / 3)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬p ∣ m → χ p = 1) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w n) ≤
      (2 / 3 : ℝ) * (∑ p ∈ m.primeFactors, Real.log p) + 12 * Real.sqrt x := by
  have hp := prime_character_defect_le_excluded χ hm (zero_le_one.trans hx) w hw hsmall
  have hc :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
        (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w n) ≤
      12 * Real.sqrt x := by
    apply
      le_trans
        (Finset.sum_le_sum
          (fun n hn ↦ mangoldt_character_defect_term_le χ n (hw n (Finset.mem_filter.mp hn).1).1))
    exact composite_mangoldt_weight_le_twelve_sqrt hx w (fun n hn ↦ (hw n hn).2)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊x⌋₊) Nat.Prime]
  exact add_le_add hp hc

end PseudoPrime.AnalyticNumberTheory.Arithmetic
