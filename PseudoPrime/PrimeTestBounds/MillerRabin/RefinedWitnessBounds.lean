/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RefinedTheorem11S2
public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS
public import PseudoPrime.PrimeTestBounds.MillerRabin.LogarithmicCutoffApplications

/-! # Miller–Rabin witnesses below the refined logarithmic cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite n≥3000 has a prime Miller–Rabin witness
below min((log(n))²,(log(n)−2log(log(n))+5)²).
Pull back a nonprincipal quotient character of the subgroup containing passing residues
and apply the refined Part 2 theorem. Nonunit witnesses are allowed.
This is the large-input branch of the strengthened witness theorem. -/
theorem exists_prime_witness_le_refinedCutoff_of_large {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hnLarge : 3000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ min ((Real.log n) ^ 2) ((Analysis.logarithmicCutoffRoot (Real.log n)) ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let _ : NeZero n := ⟨(zero_lt_one.trans hn).ne'⟩
  obtain ⟨H, hH, hpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.exists_prime_outside_subgroup_image_le_refinedPart2Cutoff hnLarge H hH hGRH
  exact ⟨p, hp, hb, PrimeTest.not_pass_of_outside_subgroup hpass hout⟩

/-- For 1<n<3000, the refined minimum cutoff equals (log(n))².
Bound log(n) by the logarithm of 4096 and apply the small-root comparison.
This reuses the existing finite witness certificate without new finite calculations. -/
theorem refinedCutoff_eq_log_sq_of_lt_3000 {n : ℕ} (hn : 1 < n) (hsmall : n < 3000) :
    min ((Real.log n) ^ 2) ((Analysis.logarithmicCutoffRoot (Real.log n)) ^ 2) =
      (Real.log n) ^ 2 := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (zero_lt_one.trans hn)
  have hnR : (n : ℝ) ≤ 4096 := Nat.cast_le.mpr (hsmall.le.trans (by norm_num only : 3000 ≤ 4096))
  have hl := Real.log_le_log hn0 hnR
  rw [show (4096 : ℝ) = 2 ^ (12 : ℕ) by norm_num only, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  apply Analysis.logarithmicCutoff_min_eq_sq_of_small (Real.log_pos (Nat.one_lt_cast.mpr hn))
  linarith only [hl, Real.log_two_lt_d9]

/-- Under GRH, every odd composite n>1 has a prime witness below the refined
minimum cutoff. The finite branch below 3000 uses the unchanged old cutoff;
the large branch uses the arbitrary-cutoff analytic comparison.
This gives a single explicit Miller–Rabin witness bound on the entire odd domain. -/
theorem exists_prime_witness_le_refinedCutoff
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ min ((Real.log n) ^ 2) ((Analysis.logarithmicCutoffRoot (Real.log n)) ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hsmall : n < 3000
  · obtain ⟨p, hp, hb, hf⟩ :=
      exists_prime_millerRabin_witness_le_log_sq_of_lt_3000 hn hnOdd hnComposite hsmall
    refine ⟨p, hp, ?_, PrimeTest.not_strongMillerRabinPass_iff.mpr hf⟩
    rw [refinedCutoff_eq_log_sq_of_lt_3000 hn hsmall]
    exact hb
  · exact
      exists_prime_witness_le_refinedCutoff_of_large hn hnOdd hnComposite (Nat.le_of_not_lt hsmall)
        hGRH

/-- Under GRH and odd n>1, passing every prime base below the refined minimum
cutoff is equivalent to primality. A composite has the strengthened witness;
a prime accepts these bases because they also lie below the old logarithmic cutoff.
This is the public primality criterion corresponding to the refined witness theorem. -/
theorem prime_iff_millerRabin_for_all_primes_le_refinedCutoff
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (hnOdd : Odd n) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ min ((Real.log n) ^ 2) ((Analysis.logarithmicCutoffRoot (Real.log n)) ^ 2) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  constructor
  · intro hpass
    by_contra hc
    obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_refinedCutoff hGRH hn hnOdd hc
    exact hf (hpass p hp hb)
  · intro hp p hprime hb
    exact
      (prime_iff_millerRabin_for_all_primes_le_log_sq hGRH hn hnOdd).mpr hp p hprime
        (hb.trans (min_le_left _ _))

end PseudoPrime.PrimeTestBounds.MillerRabin
