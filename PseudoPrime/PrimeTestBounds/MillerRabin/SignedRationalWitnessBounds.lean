/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformStarting3000
public import PseudoPrime.PrimeTestBounds.MillerRabin.SignedLogarithmicWitnessBounds

/-! # Rational coefficient-0.796 Miller–Rabin profiles

The two rational triples use their own starting values: (199/250,0,117) from
10^15188 and (199/250,0,216) from 3000. Coprime witnesses are retained for
a primality criterion even when the squared cutoff exceeds the modulus.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a positive decimal exponent, n ≥ 10^d implies n > 1.
Compare one with the decimal power. This avoids evaluating a large closed exponent. -/
private theorem one_lt_of_decimal_power {n d : ℕ} (hd : d ≠ 0) (hn : 10 ^ d ≤ n) : 1 < n := by
  exact (Nat.one_lt_pow hd (by decide : (1 : ℕ) < 10)).trans_le hn

/-- For odd composite n > 1, a uniform proper-unit-subgroup cutoff B yields
a coprime prime Miller–Rabin witness through B. Choose a proper subgroup containing
passing residues and retain the coprimality of its outside prime.
This supports cutoffs that may exceed n near their starting value. -/
theorem exists_prime_coprime_witness_of_uniform_unit_subgroup_cutoff {n : ℕ} {B : ℝ} (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hbound :
      ∀ H : Subgroup (ZMod n)ˣ,
        H ≠ ⊤ →
          ∃ p : ℕ, p.Prime ∧ ¬p ∣ n ∧ ¬LLS.PaperStatements.residueInSubgroup n H p ∧ (p : ℝ) ≤ B) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ n ∧ (p : ℝ) ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨H, hH, hpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  obtain ⟨p, hp, hd, hout, hb⟩ := hbound H hH
  exact ⟨p, hp, hd, hb, PrimeTest.not_pass_of_outside_subgroup hpass hout⟩

/-- Under GRH, every odd composite n ≥ 10^15188 has a coprime prime
Miller–Rabin witness through (199/250)(log n+117)².
Apply the rational LLS profile to the subgroup containing passing residues.
No factorization, conductor or index condition is added. -/
theorem exists_prime_witness_le_gamma_199_div_250_plus_117_15188 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 10 ^ 15188 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ n ∧
        (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log n + 117) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn1 : 1 < n := one_lt_of_decimal_power (by decide : (15188 : ℕ) ≠ 0) hn
  exact
    exists_prime_coprime_witness_of_uniform_unit_subgroup_cutoff hn1 hnOdd hnComposite
      (fun H hH ↦
        LLS.PaperStatements.exists_prime_outside_le_gamma_199_div_250_plus_117_15188 H hH hGRH hn)

/-- Under GRH, every odd composite n ≥ 3000 has a coprime prime
Miller–Rabin witness through (199/250)(log n+216)².
Apply the uniform small-start LLS profile to the subgroup containing passing residues.
This exposes the rational triple (199/250,0,216) at the starting value 3000. -/
theorem exists_prime_witness_le_gamma_199_div_250_plus_216_3000 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 3000 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ n ∧
        (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log n + 216) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn1 : 1 < n := (by decide : (1 : ℕ) < 3000).trans_le hn
  exact
    exists_prime_coprime_witness_of_uniform_unit_subgroup_cutoff hn1 hnOdd hnComposite
      (fun H hH ↦
        LLS.PaperStatements.exists_prime_outside_le_gamma_199_div_250_plus_216_3000 H hH hGRH hn)

/-- Under GRH, an odd n ≥ 3000 is prime exactly when every coprime prime
base through (199/250)(log n+216)² passes Miller–Rabin.
Use the coprime witness for a composite and the prime acceptance theorem otherwise.
Coprimality is explicit because this cutoff may exceed n near the entrance. -/
theorem prime_iff_millerRabin_for_coprime_primes_le_gamma_199_div_250_plus_216_3000 {n : ℕ}
    (hnOdd : Odd n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 3000 ≤ n) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log n + 216) ^ 2 →
          ¬p ∣ n → PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  constructor
  · intro hpass
    by_contra hc
    obtain ⟨p, hp, hd, hb, hfail⟩ :=
      exists_prime_witness_le_gamma_199_div_250_plus_216_3000 hnOdd hc hGRH hn
    exact hfail (hpass p hp hb hd)
  · intro hp p hprime _hb hd
    exact
      PrimeTest.strongMillerRabinWithBase_eq_true_iff_pass.mp
        (PrimeTest.strongMillerRabinWithBase_of_prime hp (hprime.coprime_iff_not_dvd.mpr hd))

/-- Under GRH, every odd composite with log n at least 34971 has a coprime
prime MR witness at most (199/250)(log n+117)^2. Transfer the natural-log
LLS profile to the subgroup of bases that pass the strong test. -/
theorem exists_prime_witness_le_gamma_199_div_250_plus_117_log_34971 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 34971 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ n ∧
        (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log n + 117) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnOdd.pos
  have hn : 1 < n := by
    by_contra h
    have hnle : n ≤ 1 := by omega
    have hnR : (n : ℝ) ≤ 1 := by exact_mod_cast hnle
    have hlog := Real.log_le_sub_one_of_pos hn0
    linarith only [hlog, hL, hnR]
  exact
    exists_prime_coprime_witness_of_uniform_unit_subgroup_cutoff hn hnOdd hnComposite
      (fun H hH ↦
        LLS.PaperStatements.exists_prime_outside_le_gamma_199_div_250_plus_117_log H hH hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
