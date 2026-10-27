/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-! # Products over prime factors and the totient

Bounds for finite products indexed by the prime factors of a natural number.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory.TotientProductBounds

/--
Inputs: a positive natural modulus `Q`.

Claim: the product of `1 + 1/p` over the prime factors of `Q` is at most
`Q / φ(Q)`.

Proof: compare each factor with `(1 - 1/p)⁻¹`, multiply the inequalities over
the nonnegative factors, and use Euler's product formula for `φ(Q)`.

Role: bounds the reciprocal weight lost when squarefree integers are reduced
to those coprime to `Q`.
-/
theorem primeFactor_one_add_inv_prod_le_div_totient {Q : ℕ} (hQ : 0 < Q) :
    (∏ p ∈ Q.primeFactors, (1 + (p : ℝ)⁻¹)) ≤ (Q : ℝ) / (Nat.totient Q : ℝ) := by
  have hfactor : ∀ p ∈ Q.primeFactors, 1 + (p : ℝ)⁻¹ ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpR : 1 < (p : ℝ) := by exact_mod_cast hpprime.one_lt
    have hpinv : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by exact_mod_cast hpprime.pos)).2 hpR
    have hden : 0 < 1 - (p : ℝ)⁻¹ := by linarith only [hpinv]
    have hmul : (1 + (p : ℝ)⁻¹) * (1 - (p : ℝ)⁻¹) ≤ 1 := by
      calc
        (1 + (p : ℝ)⁻¹) * (1 - (p : ℝ)⁻¹) = 1 - ((p : ℝ)⁻¹) ^ 2 := by ring_nf
        _ ≤ 1 := sub_le_self 1 (sq_nonneg ((p : ℝ)⁻¹))
    simpa only [one_div] using (le_div_iff₀ hden).2 hmul
  have hprod :
    (∏ p ∈ Q.primeFactors, (1 + (p : ℝ)⁻¹)) ≤ (∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := by
    calc
      _ ≤ ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ :=
        Finset.prod_le_prod₀
          (fun p hp =>
            add_nonneg (by norm_num only) (inv_nonneg.mpr (by exact_mod_cast Nat.zero_le p)))
          hfactor
      _ = (∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := by rw [Finset.prod_inv_distrib]
  have hphiQ := Nat.totient_eq_mul_prod_factors Q
  have hphiR := congrArg (fun x : ℚ => (x : ℝ)) hphiQ
  simp only [Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one, Rat.cast_inv,
    Rat.cast_natCast] at hphiR
  let F : ℝ := ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹)
  have hphi : (Nat.totient Q : ℝ) = (Q : ℝ) * F := by simpa only [F] using hphiR
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hphiPos : (Nat.totient Q : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast Nat.totient_pos.mpr hQ)
  have hF : F ≠ 0 := by
    intro hf
    apply hphiPos
    rw [hphi, hf]
    simp only [mul_zero]
  calc
    _ ≤ (∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := hprod
    _ = (Q : ℝ) / (Nat.totient Q : ℝ) := by
      rw [hphi]
      change F⁻¹ = (Q : ℝ) / ((Q : ℝ) * F)
      field_simp [hQR, hF]

/--
Inputs: a natural number `n`.

Claim: the totient is at least `n / 2 ^ ω(n)`, where `ω(n)` is represented by
the cardinality of its distinct prime factors.

Proof: Euler's product formula writes `φ(n)/n` as a product of `1 - 1/p`;
each factor for a prime divisor is at least one half.

Role: bounds reciprocal totients using only the divisor count of a squarefree
integer in the truncated Selberg weight estimate.
-/
theorem totient_ge_div_two_pow_primeFactorsCard (n : ℕ) :
    (n : ℝ) / (2 : ℝ) ^ n.primeFactors.card ≤ (Nat.totient n : ℝ) := by
  have hprod : (∏ p ∈ n.primeFactors, (1 / 2 : ℝ)) ≤ ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      norm_num only
    · intro p hp
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
      have hinv : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
        simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num only) hp2)
      nlinarith only [hinv]
  have hphiQ := Nat.totient_eq_mul_prod_factors n
  have hphi := congrArg (fun x : ℚ => (x : ℝ)) hphiQ
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_prod, Rat.cast_sub, Rat.cast_one,
    Rat.cast_inv] at hphi
  have hprod' : (1 / 2 : ℝ) ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa only [Finset.prod_const] using hprod
  calc
    (n : ℝ) / (2 : ℝ) ^ n.primeFactors.card = (n : ℝ) * (1 / 2 : ℝ) ^ n.primeFactors.card := by
      rw [div_eq_mul_inv, ← inv_pow]
      congr 1
      norm_num only
    _ ≤ (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left hprod' (by positivity)
    _ = (Nat.totient n : ℝ) := hphi.symm

/--
Inputs: a positive natural number `n`.

Claim: `n / φ(n)` is at most `2 ^ ω(n)`, with `ω(n)` represented by the
cardinality of the distinct prime factors.

Proof: rearrange the lower bound for `φ(n)` using positivity of the power and
of the totient.

Role: bounds each divisor-to-totient ratio in the Selberg weight mass.
-/
theorem div_totient_le_two_pow_cardFactors {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / (Nat.totient n : ℝ) ≤ (2 : ℝ) ^ n.primeFactors.card := by
  have hphi : 0 < (Nat.totient n : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  have hpow : 0 < (2 : ℝ) ^ n.primeFactors.card := by positivity
  have hmul : (n : ℝ) ≤ (2 : ℝ) ^ n.primeFactors.card * (Nat.totient n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hpow).mp (totient_ge_div_two_pow_primeFactorsCard n)
  exact (div_le_iff₀ hphi).2 hmul

/--
Inputs: a positive natural number `n`.

Claim: `1 / φ(n)` is at most `2 ^ ω(n) / n`, with `ω(n)` represented by the
cardinality of the distinct prime factors.

Proof: rearrange the preceding lower bound, using positivity of `n` and its
totient.

Role: converts divisor sums with a totient denominator into reciprocal
divisor sums.
-/
theorem one_div_totient_le_two_pow_primeFactorsCard_div {n : ℕ} (hn : 0 < n) :
    1 / (Nat.totient n : ℝ) ≤ (2 : ℝ) ^ n.primeFactors.card / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hphi : 0 < (Nat.totient n : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  have hpow : 0 < (2 : ℝ) ^ n.primeFactors.card := by positivity
  have hmul : (n : ℝ) ≤ (2 : ℝ) ^ n.primeFactors.card * (Nat.totient n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hpow).mp (totient_ge_div_two_pow_primeFactorsCard n)
  rw [div_le_div_iff₀ hphi hnR]
  simpa only [one_mul] using hmul

end PseudoPrime.NumberTheory.TotientProductBounds
