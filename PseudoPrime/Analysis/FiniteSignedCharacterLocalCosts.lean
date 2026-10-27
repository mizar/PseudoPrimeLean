/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSignedPrimeProgression

/-! # Character corrections with signed prime-power progression costs -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: signed nodes with positive exponents, a prime, and positive step and offset.
Claim: the corresponding Mangoldt prime-power progression is summable.
Proof: factor out log(p) from the summable Euler progression.
Role: justify local infinite sums before any positivity estimate. -/
theorem summable_finiteSignedMangoldtWeight_progression (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, 0 < (1 / 2 : ℝ) + (ab.1 : ℝ)) {p : ℕ} (hp : p.Prime) {d r : ℕ} (hd : 0 < d)
    (hr : 0 < r) : Summable (fun k : ℕ ↦ finiteSignedMangoldtWeight l (p ^ (d * k + r))) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  simpa only [finiteSignedMangoldtWeight,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt (Nat.add_pos_right _ hr)),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow] using
    (summable_finiteSignedEulerWeight_progression l ha hp1 hd r).mul_left (Real.log p)

/-- Input: the convergent prime-power progression hypotheses.
Claim: its exact sum is log(p) times the signed finite progression cost.
Proof: evaluate Mangoldt on prime powers and use the geometric cost identity.
Role: preserve coefficient cancellation in actual local corrections. -/
theorem tsum_finiteSignedMangoldtWeight_progression_eq_cost (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, 0 < (1 / 2 : ℝ) + (ab.1 : ℝ)) {p : ℕ} (hp : p.Prime) {d r : ℕ} (hd : 0 < d)
    (hr : 0 < r) :
    (∑' k : ℕ, finiteSignedMangoldtWeight l (p ^ (d * k + r))) =
      Real.log p * finiteSignedPrimeProgressionCost l p d r := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  simp only [finiteSignedMangoldtWeight,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt (Nat.add_pos_right _ hr)),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow]
  rw [tsum_mul_left, tsum_finiteSignedEulerWeight_progression_eq_cost l ha hp1 hd r]

/-- Input: a complex character and a combined Euler weight nonnegative above one.
Claim: every natural-index character correction is nonnegative.
Proof: the character real part is at most one and the combined Mangoldt weight is nonnegative.
Role: enlarge a finite correction only after signed coefficients have been combined. -/
theorem finiteSigned_character_correction_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    (l : List (ℚ × ℚ)) (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ finiteSignedEulerWeight l u) (n : ℕ) :
    0 ≤ (1 - (χ n).re) * finiteSignedMangoldtWeight l n := by
  exact
    mul_nonneg (sub_nonneg.mpr ((Complex.re_le_norm (χ n)).trans (χ.norm_le_one n)))
      (finiteSignedMangoldtWeight_nonneg l hW n)

/-- Input: local character value minus one and an arbitrary real weight.
Claim: even powers have zero correction and odd powers have twice the weight.
Proof: use multiplicativity and parity of powers of minus one.
Role: retain exact parity independently of a chosen kernel. -/
theorem character_minus_one_weighted_power_corrections {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ p = -1) (W : ℕ → ℝ) (k : ℕ) :
    (1 - (χ (p ^ (2 * k))).re) * W (p ^ (2 * k)) = 0 ∧
      (1 - (χ (p ^ (2 * k + 1))).re) * W (p ^ (2 * k + 1)) = 2 * W (p ^ (2 * k + 1)) := by
  norm_num only [Nat.cast_pow, map_pow, map_mul, hχ, pow_add, pow_mul, pow_one, one_pow, one_mul,
    true_and, Complex.one_re, Complex.neg_re, sub_self, zero_mul]

/-- Input: a prime with local character value minus one and positive signed-node exponents.
Claim: the full correction converges and equals twice the odd-power signed local cost.
Proof: split the infinite sum into even and odd indices before evaluating it.
Role: bound square-part and dyadic losses without counting even powers. -/
theorem finiteSigned_minus_one_positive_series_eq_cost {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hχ : χ p = -1) (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, 0 < (1 / 2 : ℝ) + (ab.1 : ℝ)) :
    Summable (fun k : ℕ ↦ (1 - (χ (p ^ (k + 1))).re) * finiteSignedMangoldtWeight l (p ^ (k + 1))) ∧
      (∑' k : ℕ, (1 - (χ (p ^ (k + 1))).re) * finiteSignedMangoldtWeight l (p ^ (k + 1))) =
        2 * (Real.log p * finiteSignedPrimeProgressionCost l p 2 1) := by
  let F : ℕ → ℝ := fun k ↦ (1 - (χ (p ^ (k + 1))).re) * finiteSignedMangoldtWeight l (p ^ (k + 1))
  have heq (k : ℕ) : F (2 * k) = 2 * finiteSignedMangoldtWeight l (p ^ (2 * k + 1)) :=
    (character_minus_one_weighted_power_corrections χ hχ (finiteSignedMangoldtWeight l) k).2
  have hoq (k : ℕ) : F (2 * k + 1) = 0 := by
    dsimp only [F]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    exact
      (character_minus_one_weighted_power_corrections χ hχ (finiteSignedMangoldtWeight l) (k + 1)).1
  have hs :=
    summable_finiteSignedMangoldtWeight_progression l ha hp (by norm_num only : 0 < (2 : ℕ))
      (by norm_num only : 0 < (1 : ℕ))
  have he := (hs.mul_left 2).congr (fun k ↦ (heq k).symm)
  have ho : Summable (fun k : ℕ ↦ F (2 * k + 1)) := by
    simpa only [hoq] using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
  refine ⟨Summable.even_add_odd he ho, ?_⟩
  change (∑' k : ℕ, F k) = _
  rw [← tsum_even_add_odd he ho]
  simp only [heq, hoq, tsum_zero, add_zero, tsum_mul_left,
    tsum_finiteSignedMangoldtWeight_progression_eq_cost l ha hp (by norm_num only : 0 < (2 : ℕ))
        (by norm_num only : 0 < (1 : ℕ))]

/-- Input: the minus-one local hypotheses and nonnegative combined Euler weight.
Claim: any finite positive-power correction is at most twice the odd-power full cost.
Proof: enlarge the nonnegative correction to its parity-cancelled series.
Role: connect arbitrary prefix sets to numerical dyadic and square-prime certificates. -/
theorem finiteSigned_minus_one_positive_prefix_le_cost {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hχ : χ p = -1) (l : List (ℚ × ℚ)) (ha : ∀ ab ∈ l, 0 < (1 / 2 : ℝ) + (ab.1 : ℝ))
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ finiteSignedEulerWeight l u) (K : Finset ℕ) :
    (∑ k ∈ K, (1 - (χ (p ^ (k + 1))).re) * finiteSignedMangoldtWeight l (p ^ (k + 1))) ≤
      2 * (Real.log p * finiteSignedPrimeProgressionCost l p 2 1) := by
  have hs := finiteSigned_minus_one_positive_series_eq_cost χ hp hχ l ha
  rw [← hs.2]
  exact
    hs.1.sum_le_tsum K
      (fun k _ ↦ by
        simpa only [Nat.cast_pow] using
          finiteSigned_character_correction_nonneg χ l hW (p ^ (k + 1)))

end PseudoPrime.Analysis
