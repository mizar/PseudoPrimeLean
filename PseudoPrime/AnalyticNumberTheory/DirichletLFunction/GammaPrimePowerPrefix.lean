/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaRamifiedPrefix
public import Mathlib.NumberTheory.Chebyshev

/-! # Exact prime-power decomposition of the ramified Gamma prefix -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The ramified prefix summand vanishes away from positive prime powers.
Mangoldt is zero at such inputs, so multiplication by the signed Euler
weight leaves zero in either coprimality branch. This permits exact
prime-power reindexing without discarding a correction term. -/
theorem gamma_nonunit_prefix_weight_eq_zero {q n : ℕ} (hn : ¬IsPrimePow n) :
    (if Nat.Coprime n q then 0 else Analysis.gammaResolventMangoldtWeight n) = 0 := by
  simp only [Analysis.gammaResolventMangoldtWeight, ArithmeticFunction.vonMangoldt_apply,
    ite_eq_right hn, zero_mul, ite_self]

/-- The nonunit Gamma prefix sum equals its restriction to prime powers.
Every discarded summand is exactly zero by Mangoldt support. This supplies
the finite-support premise of the exact prime-power decomposition. -/
theorem gamma_nonunit_prefix_eq_primePow_filter (q : ℕ) (B : Finset ℕ) :
    (∑ n ∈ B, if Nat.Coprime n q then 0 else Analysis.gammaResolventMangoldtWeight n) =
      ∑ n ∈ B.filter IsPrimePow,
        if Nat.Coprime n q then 0 else Analysis.gammaResolventMangoldtWeight n := by
  symm
  exact
    Finset.sum_subset (Finset.filter_subset _ _)
      (fun n hn hnot ↦
        gamma_nonunit_prefix_weight_eq_zero (fun hpow ↦ hnot (Finset.mem_filter.mpr ⟨hn, hpow⟩)))

/-- At nonnegative real cutoff b, the entire ramified prefix equals a
finite sum over positive exponents and primes dividing the modulus.
Mathlib's prime-power bijection supplies the exact cutoff ranges; prime
coprimality identifies the ramified base. This connects the original
integer prefix to the local prime-power accounting. -/
theorem gamma_nonunit_prefix_eq_prime_power_sum (q : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊,
        if Nat.Coprime n q then 0 else Analysis.gammaResolventMangoldtWeight n) =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log b / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊b ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime,
          if p ∣ q then Analysis.gammaResolventMangoldtWeight (p ^ k) else 0 := by
  rw [gamma_nonunit_prefix_eq_primePow_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ hb]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  exact
    gamma_primePower_ramified_correction_eq (Finset.mem_filter.mp hp).2
      (zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)

/-- Any actual character prefix summand vanishes off prime powers.
Mangoldt support is independent of the character, so this restriction
does not assume that all primitive-modulus units have value one. -/
theorem gamma_character_prefix_weight_eq_zero {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (hn : ¬IsPrimePow n) : (1 - (χ n).re) * Analysis.gammaResolventMangoldtWeight n = 0 := by
  simp only [Analysis.gammaResolventMangoldtWeight, ArithmeticFunction.vonMangoldt_apply,
    ite_eq_right hn, zero_mul, mul_zero]

/-- The actual character correction at a real cutoff is exactly a
finite prime-power sum. Retain every character value, including omitted
ambient primes with value minus one. Mangoldt support and the exact
prime-power bijection prove this before any no-witness assumption. -/
theorem gamma_character_prefix_eq_prime_power_sum {q : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 0 ≤ b) :
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (1 - (χ n).re) * Analysis.gammaResolventMangoldtWeight n) =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log b / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊b ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime,
          (1 - (χ (p ^ k)).re) * Analysis.gammaResolventMangoldtWeight (p ^ k) := by
  have he :
    (∑ n ∈ (Finset.Ioc 0 ⌊b⌋₊).filter IsPrimePow,
        (1 - (χ n).re) * Analysis.gammaResolventMangoldtWeight n) =
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (1 - (χ n).re) * Analysis.gammaResolventMangoldtWeight n :=
    Finset.sum_subset (Finset.filter_subset _ _)
      (fun n hn hnot ↦
        gamma_character_prefix_weight_eq_zero χ
          (fun hpow ↦ hnot (Finset.mem_filter.mpr ⟨hn, hpow⟩)))
  rw [← he, Chebyshev.sum_PrimePow_eq_sum_sum _ hb]
  simp only [Nat.cast_pow]

/-- Under individual RH for primitive conductor data, the signed
zero-mass prefix bound has its actual character loss expressed as
positive prime-power corrections. Apply the exact decomposition to
the signed prefix theorem. No coprimality loss is removed or set to zero. -/
theorem gammaResolvent_zeroMass_le_prime_power_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {b : ℝ} (hb : 0 ≤ b) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) ≤
      (11783423 / 25000000 : ℝ) * Real.log q +
            (Analysis.gammaResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) -
          2 * (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight n) +
        ∑ k ∈ Finset.Icc 1 ⌊Real.log b / Real.log 2⌋₊,
          ∑ p ∈ (Finset.Ioc 0 ⌊b ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime,
            (1 - (χ (p ^ k)).re) * Analysis.gammaResolventMangoldtWeight (p ^ k) := by
  have h := gammaResolvent_zeroMass_le_signed_prefix hq hRH hp hne hinv (Finset.Ioc 0 ⌊b⌋₊)
  rw [gamma_character_prefix_eq_prime_power_sum χ hb] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
