/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSignedWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS

/-! # Miller–Rabin witnesses with rational signed logarithmic corrections

The three certified LLS profiles give Miller–Rabin witnesses for every odd
composite at the same decimal entrances. The coefficient is 4/5 and both
positive and negative corrections occur.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A positive decimal exponent and n ≥ 10^d imply n > 1.
Compare one with the decimal power. This avoids evaluating a large closed power. -/
private theorem one_lt_of_decimal_power {n d : ℕ} (hd : d ≠ 0) (hn : 10 ^ d ≤ n) : 1 < n := by
  exact (Nat.one_lt_pow hd (by decide : (1 : ℕ) < 10)).trans_le hn

/-- For odd composite n > 1, a uniform proper-unit-subgroup cutoff B gives
a prime Miller–Rabin witness through B. Choose a proper subgroup containing all
passing residues and apply the outside-prime bound.
This transfers a pointwise LLS bound without changing its expression. -/
theorem exists_prime_witness_of_uniform_unit_subgroup_cutoff {n : ℕ} {B : ℝ} (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hbound :
      ∀ H : Subgroup (ZMod n)ˣ,
        H ≠ ⊤ →
          ∃ p : ℕ, p.Prime ∧ ¬p ∣ n ∧ ¬LLS.PaperStatements.residueInSubgroup n H p ∧ (p : ℝ) ≤ B) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨H, hH, hpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  obtain ⟨p, hp, _hd, hout, hb⟩ := hbound H hH
  exact ⟨p, hp, hb, PrimeTest.not_pass_of_outside_subgroup hpass hout⟩

/-- Under GRH, every odd composite with log n at least 34971 has a prime MR
witness at most (4/5)(log n+29)^2. Transfer the natural-log subgroup theorem
to the subgroup of bases that pass the strong test. This exposes the analytic
entrance independently of its decimal-threshold corollary. -/
theorem exists_prime_witness_le_gamma_four_fifths_plus_twentyNine_log_34971 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 34971 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n + 29) ^ 2 ∧
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
    exists_prime_witness_of_uniform_unit_subgroup_cutoff hn hnOdd hnComposite
      (fun H hH ↦
        LLS.PaperStatements.exists_prime_outside_le_gamma_four_fifths_log_plus_twentyNine H hH hGRH
          hL)

/-- Under GRH, every odd composite with log n at least 46330 has a prime MR
witness at most (4/5)(log n-2)^2. Transfer the natural-log subgroup theorem
to the subgroup of bases that pass the strong test. -/
theorem exists_prime_witness_le_gamma_four_fifths_minus_two_log_46330 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 46330 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n - 2) ^ 2 ∧
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
    exists_prime_witness_of_uniform_unit_subgroup_cutoff hn hnOdd hnComposite
      (fun H hH ↦
        LLS.PaperStatements.exists_prime_outside_le_gamma_four_fifths_log_minus_two H hH hGRH hL)

/-- Under GRH, every odd composite with log n at least 50880 has a prime MR
witness at most (4/5)(log n-log log n)^2. Transfer the natural-log subgroup
theorem to the subgroup of bases that pass the strong test. -/
theorem exists_prime_witness_le_gamma_four_fifths_minus_loglog_log_50880 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 50880 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n - Real.log (Real.log n)) ^ 2 ∧
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
    exists_prime_witness_of_uniform_unit_subgroup_cutoff hn hnOdd hnComposite
      (fun H hH ↦
        LLS.PaperStatements.exists_prime_outside_le_gamma_four_fifths_log_minus_loglog H hH hGRH hL)

/-- Under GRH, every odd composite n ≥ 10^15188 has a prime Miller–Rabin
witness at most (4/5)(log n+29)². Apply the signed LLS profile to the subgroup
containing passing residues. No further factorization or index hypothesis is needed. -/
theorem exists_prime_witness_le_gamma_four_fifths_plus_twentyNine_15188 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 10 ^ 15188 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n + 29) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn1 : 1 < n := one_lt_of_decimal_power (by decide : (15188 : ℕ) ≠ 0) hn
  exact
    exists_prime_witness_of_uniform_unit_subgroup_cutoff hn1 hnOdd hnComposite
      (fun H hH ↦
        LLS.PaperStatements.exists_prime_outside_le_gamma_four_fifths_plus_twentyNine_15188 H hH
          hGRH hn)

/-- Under GRH, every odd composite n ≥ 10^20121 has a prime Miller–Rabin
witness at most (4/5)(log n-2)². Apply the signed LLS profile to the subgroup
containing passing residues. No further factorization or index hypothesis is needed. -/
theorem exists_prime_witness_le_gamma_four_fifths_minus_two_20121 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 10 ^ 20121 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n - 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn1 : 1 < n := one_lt_of_decimal_power (by decide : (20121 : ℕ) ≠ 0) hn
  exact
    exists_prime_witness_of_uniform_unit_subgroup_cutoff hn1 hnOdd hnComposite
      (fun H hH ↦
        LLS.PaperStatements.exists_prime_outside_le_gamma_four_fifths_minus_two_20121 H hH hGRH hn)

/-- Under GRH, every odd composite n ≥ 10^22097 has a prime Miller–Rabin
witness at most (4/5)(log n-log log n)². Apply the signed LLS profile to the subgroup
containing passing residues. No further factorization or index hypothesis is needed. -/
theorem exists_prime_witness_le_gamma_four_fifths_minus_loglog_22097 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 10 ^ 22097 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n - Real.log (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn1 : 1 < n := one_lt_of_decimal_power (by decide : (22097 : ℕ) ≠ 0) hn
  exact
    exists_prime_witness_of_uniform_unit_subgroup_cutoff hn1 hnOdd hnComposite
      (fun H hH ↦
        LLS.PaperStatements.exists_prime_outside_le_gamma_four_fifths_minus_loglog_22097 H hH hGRH
          hn)

end PseudoPrime.PrimeTestBounds.MillerRabin
