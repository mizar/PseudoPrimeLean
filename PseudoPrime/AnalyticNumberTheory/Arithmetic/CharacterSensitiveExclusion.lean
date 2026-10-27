/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExcludedCharacterDefect

/-! # Character-sensitive excluded-prime costs -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Sum (1-Re chi(p))log p over the distinct prime factors of m.
The character level is independent of m. This nonnegative cost retains trivial
values at excluded primes instead of charging all of them the maximal defect. -/
noncomputable def characterExclusionCost {f : ℕ} (χ : DirichletCharacter ℂ f) (m : ℕ) : ℝ :=
  ∑ p ∈ m.primeFactors, (1 - (χ p).re) * Real.log p

/-- Every character defect is nonnegative because the real part is at most
the norm, which is at most one. This provides the sign for weighted comparisons. -/
theorem character_defect_nonneg {f : ℕ} (χ : DirichletCharacter ℂ f) (n : ℕ) :
    0 ≤ 1 - (χ n).re := by
  have hr := (abs_le.mp (Complex.abs_re_le_norm (χ n))).2
  have hn := χ.norm_le_one n
  linarith only [hr, hn]

/-- The character-sensitive excluded-prime cost is nonnegative for every m,
including zero. Each prime logarithm and character defect is nonnegative. -/
theorem characterExclusionCost_nonneg {f : ℕ} (χ : DirichletCharacter ℂ f) (m : ℕ) :
    0 ≤ characterExclusionCost χ m := by
  apply Finset.sum_nonneg
  intro p hp
  apply mul_nonneg (character_defect_nonneg χ p)
  exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)

/-- Prime triviality outside nonzero m bounds the prime-weighted defect by one
third of the character-sensitive cost. Restrict the prime sum to divisors of m
and use the nonnegative defect before comparing the weight with 1/3. -/
theorem prime_character_defect_le_sensitive {f m : ℕ} (χ : DirichletCharacter ℂ f) (hm : m ≠ 0)
    {x : ℝ} (hx : 0 ≤ x) (w : ℕ → ℝ) (hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, w n ≤ 1 / 3)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬p ∣ m → χ p = 1) :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
        (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w n) ≤
      characterExclusionCost χ m / 3 := by
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
    _ ≤ ∑ n ∈ T, ((1 - (χ n).re) * Real.log n) / 3 := by
      apply Finset.sum_le_sum
      intro n hn
      have hP := Finset.mem_filter.mp (Finset.mem_filter.mp hn).1
      have hc :=
        mul_le_mul_of_nonneg_left (hw n hP.1)
          (mul_nonneg (character_defect_nonneg χ n)
            (ArithmeticFunction.vonMangoldt_nonneg (n := n)))
      dsimp only [D]
      rw [ArithmeticFunction.vonMangoldt_apply_prime hP.2] at hc ⊢
      nlinarith only [hc]
    _ ≤ ∑ n ∈ m.primeFactors, ((1 - (χ n).re) * Real.log n) / 3 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have ht := Finset.mem_filter.mp hn
        exact Nat.mem_primeFactors.mpr ⟨(Finset.mem_filter.mp ht.1).2, ht.2, hm⟩
      · intro n hn _
        exact
          div_nonneg
            (mul_nonneg (character_defect_nonneg χ n)
              (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hn).one_lt.le)))
            (by norm_num only)
    _ = _ := by
      rw [← Finset.sum_div]; rfl

/-- For x at least one, prime triviality outside nonzero m bounds the full
weighted defect by E_chi(m)/3+12sqrt x. Split prime and nonprime indices and
retain the character-sensitive prime cost for later cubic extraction. -/
theorem weighted_character_defect_le_sensitive {f m : ℕ} (χ : DirichletCharacter ℂ f) (hm : m ≠ 0)
    {x : ℝ} (hx : 1 ≤ x) (w : ℕ → ℝ) (hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, 0 ≤ w n ∧ w n ≤ 1 / 3)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬p ∣ m → χ p = 1) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w n) ≤
      characterExclusionCost χ m / 3 + 12 * Real.sqrt x := by
  have hp :=
    prime_character_defect_le_sensitive χ hm (zero_le_one.trans hx) w (fun n hn ↦ (hw n hn).2)
      hsmall
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

/-- The character-sensitive cost never exceeds twice the distinct-prime
logarithm sum. Use the lower bound on the real part termwise. This compares
the refined extraction with the previous uniform exclusion budget. -/
theorem characterExclusionCost_le_twice {f : ℕ} (χ : DirichletCharacter ℂ f) (m : ℕ) :
    characterExclusionCost χ m ≤ 2 * ∑ p ∈ m.primeFactors, Real.log p := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hr := (abs_le.mp (Complex.abs_re_le_norm (χ p))).1
  have hn := χ.norm_le_one p
  have hc : 1 - (χ p).re ≤ 2 := by linarith only [hr, hn]
  exact
    mul_le_mul_of_nonneg_right hc
      (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
