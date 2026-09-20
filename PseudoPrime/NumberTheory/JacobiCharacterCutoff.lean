/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.JacobiCharacterArithmetic

/-!
# Jacobi character cutoff lemmas

Converts absence of a `PrimeNeOneWitnessSet n` witness up to a real cutoff `y²` into
`primitiveQuadraticCharacter n hn = 1` on every prime and prime power that appears in the
`p ^ k ≤ y²`-indexed summation ranges used by the analytic Jacobi-character bounds. The chain runs
from a single prime power (`_prime_pow`), through the root cutoff `⌊(y²)^(1/k)⌋₊` for a fixed
exponent `k` (`_in_root_cutoff`), to the `hodd`-shaped provider ranging over both `k` and `p`
(`_in_log_square_range`) and its `JacobiCharacterArithmeticData` bridge-level counterpart
`primitiveCharacter_eq_one_in_log_square_range`.
-/

namespace PseudoPrime.NumberTheory

/-- The no-witness hypothesis propagates the value one from an odd prime to all
of its nontrivial prime powers at or below the cutoff. -/
theorem primitiveQuadraticCharacter_eq_one_of_no_primeNeOne_witness_prime_pow {n X p k : ℕ}
    (hn : Odd n) (hp : p.Prime) (hodd : Odd p) (hk : k ≠ 0) (hpowX : p ^ k ≤ X)
    (hno : ∀ q, q.Prime → Odd q → q ≤ X → q ∉ PrimeNeOneWitnessSet n) (hpdvd : ¬p ∣ n) :
    primitiveQuadraticCharacter n hn (p ^ k : ℤ) = 1 := by
  have hpX : p ≤ X := by
    have hpowpos : 0 < p ^ k := Nat.pow_pos (Nat.zero_lt_of_lt hp.one_lt)
    have hppow : p ≤ p ^ k := Nat.le_of_dvd hpowpos (dvd_pow_self p hk)
    exact hppow.trans hpowX
  have hprime : primitiveQuadraticCharacter n hn (p : ℤ) = 1 :=
    primitiveQuadraticCharacter_eq_one_of_no_primeNeOne_witness hn hp hodd hpX hno hpdvd
  rw [Int.cast_pow, map_pow, hprime]
  simp only [one_pow]

/--
Input/assumptions: odd `n`, `y ≥ 1`, an exponent `k ≥ 1`, an odd prime `p` in the root cutoff,
and absence of `PseudoPrime.NumberTheory.PrimeNeOneWitnessSet n` at or below `⌊y²⌋₊`.
Conclusion: the primitive quadratic character is one at `p`.
Content: the root cutoff is bounded by `y²` because `1 / k ≤ 1` and the base `y²` is at least one;
the resulting integer bound is exactly the natural cutoff consumed by the arithmetic bridge.
Proof: cast the finite-set upper bound to `ℝ`, use `Real.rpow_le_rpow_of_exponent_le`, and apply
the no-witness character lemma.
Role: turns absence of a Jacobi witness up to `⌊y²⌋₊` into character value one on each
prime-power summation range.
-/
theorem primitiveQuadraticCharacter_eq_one_of_no_primeNeOne_witness_in_root_cutoff {n p k : ℕ}
    (hn : Odd n) {y : ℝ} (hy : 1 ≤ y) (hp : p.Prime) (hodd : Odd p) (hk : 1 ≤ k)
    (hpmem : p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊y ^ 2⌋₊ → q ∉ PrimeNeOneWitnessSet n) :
    primitiveQuadraticCharacter n hn (p : ℤ) = 1 := by
  have hbase : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt hk
  have hexp : (1 : ℝ) / k ≤ 1 := by
    rw [div_le_iff₀ hkpos]
    simpa only [one_mul] using (show (1 : ℝ) ≤ (k : ℝ) by exact_mod_cast hk)
  have hpow' : (y ^ 2) ^ ((1 : ℝ) / k) ≤ (y ^ 2) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hpow : (y ^ 2) ^ ((1 : ℝ) / k) ≤ y ^ 2 := by simpa only [one_div, Real.rpow_one] using hpow'
  have hpX : p ≤ ⌊y ^ 2⌋₊ := by
    apply Nat.le_floor
    have hpcast : (p : ℝ) ≤ (y ^ 2) ^ ((1 : ℝ) / k) := by
      calc
        (p : ℝ) ≤ (⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ : ℕ) := by exact_mod_cast (Finset.mem_Ioc.mp hpmem).2
        _ ≤ (y ^ 2) ^ ((1 : ℝ) / k) := Nat.floor_le (by positivity)
    exact hpcast.trans hpow
  exact
    primitiveQuadraticCharacter_eq_one_of_no_primeNeOne_witness hn hp hodd hpX hno
      (not_dvd_of_no_primeNeOne_witness hp hodd hpX hno)

/-- The preceding cutoff lemma packaged in the exact `hodd` shape used by the analytic bounds. -/
theorem primitiveQuadraticCharacter_eq_one_of_no_primeNeOne_witness_in_log_square_range {n : ℕ}
    (hn : Odd n) {y : ℝ} (hy : 1 ≤ y)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊y ^ 2⌋₊ → q ∉ PrimeNeOneWitnessSet n) :
    ∀ {k p : ℕ},
      k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
        p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
        p.Prime → Odd p → primitiveQuadraticCharacter n hn (p : ℤ) = 1 := by
  intro k p hk hpmem hp hodd
  exact
    primitiveQuadraticCharacter_eq_one_of_no_primeNeOne_witness_in_root_cutoff hn hy hp hodd
      (Finset.mem_Icc.mp hk).1 hpmem hno

/-- The bridge-level version of the preceding `hodd` provider for analytic downstream theorems. -/
theorem JacobiCharacterArithmeticData.primitiveCharacter_eq_one_in_log_square_range {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n} [NeZero (complexQuadraticCharacter n hn).conductor]
    (bridge : JacobiCharacterArithmeticData n hn hns) {y : ℝ} (hy : 1 ≤ y)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊y ^ 2⌋₊ → q ∉ PrimeNeOneWitnessSet n) :
    ∀ {k p : ℕ},
      k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
        p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
        p.Prime → Odd p → bridge.character.primitiveCharacter p = 1 := by
  intro k p hk hpmem hp hodd
  have hbase : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt (Finset.mem_Icc.mp hk).1
  have hexp : (1 : ℝ) / k ≤ 1 := by
    rw [div_le_iff₀ hkpos]
    simpa only [one_mul] using (show (1 : ℝ) ≤ (k : ℝ) by exact_mod_cast (Finset.mem_Icc.mp hk).1)
  have hpow' : (y ^ 2) ^ ((1 : ℝ) / k) ≤ (y ^ 2) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hpow : (y ^ 2) ^ ((1 : ℝ) / k) ≤ y ^ 2 := by simpa only [one_div, Real.rpow_one] using hpow'
  have hpX : p ≤ ⌊y ^ 2⌋₊ := by
    apply Nat.le_floor
    have hpcast : (p : ℝ) ≤ (y ^ 2) ^ ((1 : ℝ) / k) := by
      calc
        (p : ℝ) ≤ (⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ : ℕ) := by exact_mod_cast (Finset.mem_Ioc.mp hpmem).2
        _ ≤ (y ^ 2) ^ ((1 : ℝ) / k) := Nat.floor_le (by positivity)
    exact hpcast.trans hpow
  simpa only [Int.cast_natCast] using
    bridge.primitiveCharacter_eq_one_of_no_primeNeOne_witness hp hodd hpX hno

end PseudoPrime.NumberTheory
