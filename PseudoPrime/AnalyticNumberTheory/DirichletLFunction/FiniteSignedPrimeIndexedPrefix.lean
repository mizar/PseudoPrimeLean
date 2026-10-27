/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPrimeIndexedPrefix
public import PseudoPrime.Analysis.Phase64DyadicLocalBounds

/-! # Exact prime-indexed prefixes for arbitrary signed resolvents -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The finite signed character correction vanishes off prime powers. Mangoldt
support makes this independent of the coefficients and character; it permits exact reindexing. -/
theorem finiteSigned_character_prefix_weight_eq_zero (l : List (ℚ × ℚ)) {q n : ℕ}
    (χ : DirichletCharacter ℂ q) (hn : ¬IsPrimePow n) :
    (1 - (χ n).re) * Analysis.finiteSignedMangoldtWeight l n = 0 := by
  simp only [Analysis.finiteSignedMangoldtWeight, ArithmeticFunction.vonMangoldt_apply,
    ite_eq_right hn, zero_mul, mul_zero]

/-- At a nonnegative cutoff, any signed Mangoldt character prefix equals its exact
prime-power decomposition. Restrict to Mangoldt support and apply the prime-power bijection. -/
theorem finiteSigned_character_prefix_eq_prime_power_sum (l : List (ℚ × ℚ)) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {b : ℝ} (hb : 0 ≤ b) :
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (1 - (χ n).re) * Analysis.finiteSignedMangoldtWeight l n) =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log b / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊b ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime,
          (1 - (χ (p ^ k)).re) * Analysis.finiteSignedMangoldtWeight l (p ^ k) := by
  have he :
    (∑ n ∈ (Finset.Ioc 0 ⌊b⌋₊).filter IsPrimePow,
        (1 - (χ n).re) * Analysis.finiteSignedMangoldtWeight l n) =
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (1 - (χ n).re) * Analysis.finiteSignedMangoldtWeight l n :=
    Finset.sum_subset (Finset.filter_subset _ _)
      (fun n hn hnot ↦
        finiteSigned_character_prefix_weight_eq_zero l χ
          (fun hpow ↦ hnot (Finset.mem_filter.mpr ⟨hn, hpow⟩)))
  rw [← he, Chebyshev.sum_PrimePow_eq_sum_sum _ hb]
  simp only [Nat.cast_pow]

/-- The exact signed integer correction equals a prime-indexed sum over finite
positive-power prefixes. Finite row interchange preserves all signed contributions. -/
theorem finiteSigned_character_prefix_eq_prime_indexed (l : List (ℚ × ℚ)) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {b : ℝ} (hb : 0 ≤ b) :
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (1 - (χ n).re) * Analysis.finiteSignedMangoldtWeight l n) =
      ∑ p ∈ gammaPrefixPrimeSet b,
        ∑ k ∈ gammaPrefixPowerIndices b p,
          (1 - (χ (p ^ (k + 1))).re) * Analysis.finiteSignedMangoldtWeight l (p ^ (k + 1)) := by
  rw [finiteSigned_character_prefix_eq_prime_power_sum l χ hb, gamma_positive_exponent_sum_eq_range]
  exact
    gamma_prefix_rows_eq_prime_sums (Finset.range (gammaPrefixExponentCount b))
      (gammaPrefixRowPrimes b)
      (fun k p ↦ (1 - (χ (p ^ (k + 1))).re) * Analysis.finiteSignedMangoldtWeight l (p ^ (k + 1)))

/-- Under prime triviality away from the ambient modulus, each retained outside
prime has zero signed Euler correction. Multiplicativity proves the claim for every power. -/
theorem finiteSigned_prefix_euler_sum_eq_zero_of_not_dvd (l : List (ℚ × ℚ)) {q a : ℕ}
    (χ : DirichletCharacter ℂ q) {b : ℝ} (hb : 1 ≤ b)
    (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p a → χ p = 1) {p : ℕ}
    (hp : p ∈ gammaPrefixPrimeSet b) (hpa : ¬p ∣ a) :
    (∑ k ∈ gammaPrefixPowerIndices b p,
        (1 - (χ (p ^ (k + 1))).re) * Analysis.finiteSignedMangoldtWeight l (p ^ (k + 1))) =
      0 := by
  have hv := gamma_prefix_prime_value_one_of_not_dvd χ hb hone hp hpa
  simp only [map_pow, hv, one_pow, Complex.one_re, sub_self, zero_mul, Finset.sum_const_zero]

/-- At cutoff at least one, ambient prime triviality restricts the exact signed
integer correction to ambient factors. Outside terms vanish and absent prefixes are empty. -/
theorem finiteSigned_character_prefix_eq_ambient_prime_sum (l : List (ℚ × ℚ)) {q a : ℕ}
    (χ : DirichletCharacter ℂ q) (ha : 0 < a) {b : ℝ} (hb : 1 ≤ b)
    (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p a → χ p = 1) :
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (1 - (χ n).re) * Analysis.finiteSignedMangoldtWeight l n) =
      ∑ p ∈ a.primeFactors,
        ∑ k ∈ gammaPrefixPowerIndices b p,
          (1 - (χ (p ^ (k + 1))).re) * Analysis.finiteSignedMangoldtWeight l (p ^ (k + 1)) := by
  let F : ℕ → ℝ := fun p ↦
    ∑ k ∈ gammaPrefixPowerIndices b p,
      (1 - (χ (p ^ (k + 1))).re) * Analysis.finiteSignedMangoldtWeight l (p ^ (k + 1))
  let S := (gammaPrefixPrimeSet b).filter (fun p : ℕ ↦ p ∣ a)
  have hsub : S ⊆ a.primeFactors := by
    intro p hp
    have hd := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(gamma_prefix_prime_data hb hd.1).1, hd.2, ha.ne'⟩
  have he0 : (∑ p ∈ S, F p) = ∑ p ∈ gammaPrefixPrimeSet b, F p :=
    Finset.sum_subset (Finset.filter_subset _ _)
      (fun p hp hnot ↦
        finiteSigned_prefix_euler_sum_eq_zero_of_not_dvd l χ hb hone hp
          (fun hd ↦ hnot (Finset.mem_filter.mpr ⟨hp, hd⟩)))
  have he1 : (∑ p ∈ S, F p) = ∑ p ∈ a.primeFactors, F p := by
    apply Finset.sum_subset hsub
    intro p hp hnot
    have hnotP : p ∉ gammaPrefixPrimeSet b := fun hP ↦
      hnot (Finset.mem_filter.mpr ⟨hP, Nat.dvd_of_mem_primeFactors hp⟩)
    dsimp only [F]
    rw [gamma_prefix_power_indices_eq_empty hnotP, Finset.sum_empty]
  rw [finiteSigned_character_prefix_eq_prime_indexed l χ (zero_le_one.trans hb)]
  exact he0.symm.trans he1

/-- The signed integer correction and ambient ramp sum equal the sum of actual
local costs. Exact ambient reindexing connects signed prefix budgets to the local certificates. -/
theorem finiteSigned_character_prefix_add_ambient_ramp_eq_local_cost (l : List (ℚ × ℚ)) {q a : ℕ}
    (χ : DirichletCharacter ℂ q) (ha : 0 < a) {b : ℝ} (hb : 1 ≤ b)
    (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p a → χ p = 1) (x : ℝ) :
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (1 - (χ n).re) * Analysis.finiteSignedMangoldtWeight l n) +
        (∑ p ∈ a.primeFactors,
          Real.log p *
            ((∑' k : ℕ,
                Analysis.exponentialRampLocalCorrection (χ p) ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
              Real.sqrt x)) =
      ∑ p ∈ a.primeFactors,
        Analysis.finiteSignedActualPrimeLocalCost l χ p (gammaPrefixPowerIndices b p) x := by
  rw [finiteSigned_character_prefix_eq_ambient_prime_sum l χ ha hb hone]
  simp only [Analysis.finiteSignedActualPrimeLocalCost, Finset.sum_add_distrib]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
