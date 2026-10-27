/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalTheorem11S2
public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS

/-! # Miller–Rabin with rational constant 193/40 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite n ≥ 3000 has a prime Miller–Rabin witness
through the minimum of (log n)² and (log n-2 log log n+193/40)².
Apply the rational Part 2 subgroup-image bound to the subgroup containing passing residues.
This is the large-input branch of the smaller rational cutoff. -/
theorem exists_prime_witness_le_rationalCutoff_of_large {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hnLarge : 3000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ min ((Real.log n) ^ 2) ((Analysis.rationalPart2CutoffRoot (Real.log n)) ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨(zero_lt_one.trans hn).ne'⟩
  obtain ⟨H, hH, hpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.exists_prime_outside_subgroup_image_le_rationalPart2Cutoff hnLarge H hH hGRH
  exact ⟨p, hp, hb, PrimeTest.not_pass_of_outside_subgroup hpass hout⟩

/-- For 1 < n < 3000, the rational minimum cutoff equals (log n)².
Bound log n by ten and show that the rational corrected root is at least log n.
This preserves the existing finite Miller–Rabin certificate. -/
theorem rationalCutoff_eq_log_sq_of_lt_3000 {n : ℕ} (hn : 1 < n) (hsmall : n < 3000) :
    min ((Real.log n) ^ 2) ((Analysis.rationalPart2CutoffRoot (Real.log n)) ^ 2) =
      (Real.log n) ^ 2 := by
  have hL0 := Real.log_pos (Nat.one_lt_cast.mpr hn)
  have hl :=
    Real.log_le_log (Nat.cast_pos.mpr (zero_lt_one.trans hn))
      (Nat.cast_le.mpr (hsmall.le.trans (by decide : 3000 ≤ 4096)))
  norm_num only [Nat.cast_ofNat] at hl
  rw [show (4096 : ℝ) = 2 ^ 12 by norm_num only, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hL10 : Real.log n ≤ 10 := by linarith only [hl, Real.log_two_lt_d9]
  have hz := Real.log_le_log hL0 hL10
  have hz10 : Real.log (10 : ℝ) < 12 / 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (5 : ℝ) ≠ 0)]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hr : Real.log n ≤ Analysis.rationalPart2CutoffRoot (Real.log n) := by
    unfold Analysis.rationalPart2CutoffRoot
    linarith only [hz, hz10]
  exact min_eq_left ((sq_le_sq₀ hL0.le (hL0.le.trans hr)).mpr hr)

theorem exists_prime_witness_le_rationalCutoff
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ min ((Real.log n) ^ 2) ((Analysis.rationalPart2CutoffRoot (Real.log n)) ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hsmall : n < 3000
  · obtain ⟨p, hp, hb, hf⟩ :=
      exists_prime_millerRabin_witness_le_log_sq_of_lt_3000 hn hnOdd hnComposite hsmall
    refine ⟨p, hp, ?_, PrimeTest.not_strongMillerRabinPass_iff.mpr hf⟩
    rw [rationalCutoff_eq_log_sq_of_lt_3000 hn hsmall]
    exact hb
  · exact
      exists_prime_witness_le_rationalCutoff_of_large hn hnOdd hnComposite (Nat.le_of_not_lt hsmall)
        hGRH

/-- Under GRH, an odd n > 1 is prime exactly when every prime base through
the rational minimum cutoff passes Miller–Rabin.
Use the witness for a composite and the existing pure-cutoff prime acceptance otherwise.
This is the public primality criterion for the improved rational cutoff. -/
theorem prime_iff_millerRabin_for_all_primes_le_rationalCutoff
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (hnOdd : Odd n) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ min ((Real.log n) ^ 2) ((Analysis.rationalPart2CutoffRoot (Real.log n)) ^ 2) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  constructor
  · intro hpass
    by_contra hc
    obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_rationalCutoff hGRH hn hnOdd hc
    exact hf (hpass p hp hb)
  · intro hp p hprime hb
    exact
      (prime_iff_millerRabin_for_all_primes_le_log_sq hGRH hn hnOdd).mpr hp p hprime
        (hb.trans (min_le_left _ _))

end PseudoPrime.PrimeTestBounds.MillerRabin
