/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison

/-! # Logarithmic character sums under prime triviality at arbitrary cutoffs -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a positive cutoff and prime triviality within it, a logarithmic summand
equals its unsigned weight on coprime inputs and is zero otherwise.
Reduce the nonzero Mangoldt support to prime powers and use multiplicativity.
This supplies the exact original-level support at a freely chosen cutoff. -/
theorem characterLogWeightedTerm_re_eq_ite_of_prime_trivial {q n : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    (characterLogWeightedTerm x χ n).re =
      if Nat.Coprime n q then logWeightedMangoldtTerm x n else 0 := by
  by_cases hcop : Nat.Coprime n q
  · rw [ite_eq_left hcop]
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · rw [characterLogWeightedTerm, logWeightedMangoldtTerm, hΛ, zero_mul]
      norm_num only [Complex.ofReal_zero, zero_mul, Complex.zero_re]
    · obtain ⟨p, k, hp, hk, rfl⟩ :=
        (isPrimePow_nat_iff (n := n)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
      have hpdiv : p ∣ p ^ k := dvd_pow_self p hk.ne'
      have hpcop : Nat.Coprime p q := hcop.of_dvd_left hpdiv
      have hpbound : (p : ℝ) ≤ x := by
        have hpowFloor := (Finset.mem_Ioc.mp hn).2
        have hpPow : p ≤ p ^ k := Nat.le_pow hk
        exact
          (show (p : ℝ) ≤ (p ^ k : ℕ) by exact_mod_cast hpPow).trans
            ((Nat.le_floor_iff hx.le).mp hpowFloor)
      have hpvalue : χ p = 1 := htrivial p hp (hp.coprime_iff_not_dvd.mp hpcop) hpbound
      rw [characterLogWeightedTerm]
      simp only [Nat.cast_pow, map_pow, hpvalue, one_pow, mul_one, Complex.ofReal_re]
  · rw [ite_eq_right hcop]
    have hχzero : χ n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hcop)
    rw [characterLogWeightedTerm, hχzero, mul_zero, Complex.zero_re]

/-- Under prime triviality up to a positive cutoff, the logarithmic character sum
has real part equal to the unsigned sum minus the common-factor terms.
Sum the support identity and partition the unsigned sum into coprime and remaining inputs.
This gives the lower comparison at an arbitrary no-witness cutoff. -/
theorem characterLogWeightedSum_re_eq_sub_common_of_prime_trivial {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    (characterLogWeightedSum x χ).re =
      logWeightedMangoldtSum x - commonFactorLogWeightedSum x q := by
  rw [characterLogWeightedSum, logWeightedMangoldtSum, commonFactorLogWeightedSum]
  simp only [Complex.re_sum]
  have heq :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (characterLogWeightedTerm x χ n).re =
      ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ Nat.Coprime n q, logWeightedMangoldtTerm x n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    exact characterLogWeightedTerm_re_eq_ite_of_prime_trivial x χ hx hn htrivial
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc 0 ⌊x⌋₊) (f := logWeightedMangoldtTerm x)
      (p := fun n ↦ Nat.Coprime n q)
  linarith only [heq, hsplit]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
