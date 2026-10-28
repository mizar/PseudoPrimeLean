/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SharpIntervalSelection

/-! # Strict finite-principal gains for both sharp public cutoffs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every valid finite-principal profile bounds the sharp selection for inputs above one.
Project the finite base after rewriting the guarded-selection identity. -/
theorem sharpSelected_le_finite (f : Analysis.FinitePrimeProfile) {n : ℕ} (hn : 1 < n)
    (hL : Real.log n ≤ f.logCap) : sharpSelectedEnvelope n ≤ f.bound := by
  rw [← sharp_eq_selected hn]
  exact (sharpWitness_le_low n).trans (lowFinite_le_profile f hL)

/-- Every valid finite-principal prime constant bounds the rounded sharp cutoff.
Use monotonicity of prime rounding and the primality of the fixed bound. -/
theorem sharpPrime_le_finite (f : Analysis.FinitePrimeProfile) {n : ℕ}
    (hL : Real.log n ≤ f.logCap) : sharpPrimeEnvelope n ≤ f.bound := by
  have hp : f.bound.Prime := by cases f <;> decide +kernel
  change primeRound (sharpWitnessEnvelope n) ≤ (f.bound : ℝ)
  rw [← primeRound_prime hp]
  exact primeRound_mono ((sharpWitness_le_low n).trans (lowFinite_le_profile f hL))

/-- On each of the nine extended low-prime bands, both sharp public cutoffs
strictly improve their respective current refined cutoffs. Transfer the certified prime gap. -/
theorem sharpStrict_low_profile (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (hN : 3000 ≤ n) (hL : (f.tightLogCap : ℝ) < Real.log n)
    (hU : Real.log n ≤ (lowPrincipalProfile f).logCap) :
    sharpSelectedEnvelope n < refinedSelectedEnvelope n ∧
      sharpPrimeEnvelope n < refinedPrimeEnvelope n := by
  have hs := finitePrincipal_low_strict f hn hN hL hU
  exact
    ⟨(sharpSelected_le_finite (lowPrincipalProfile f) hn hU).trans_lt hs.1,
      (sharpPrime_le_finite (lowPrincipalProfile f) hU).trans_lt hs.2⟩

/-- On each of the four specified closed finite cells, both sharp public cutoffs
strictly improve their respective current refined cutoffs. The rounded strict comparison
uses the fixed prime bound rather than a strict real-cutoff rounding claim. -/
theorem sharpStrict_upper_profile (c : LLS.PaperStatements.FiniteRoundCell) {n : ℕ} (hn : 1 < n)
    (hL : (c.left : ℝ) ≤ Real.log n) (hU : Real.log n ≤ c.profile.logCap) :
    sharpSelectedEnvelope n < refinedSelectedEnvelope n ∧
      sharpPrimeEnvelope n < refinedPrimeEnvelope n := by
  have hs := finitePrincipal_upper_strict c hn hL hU
  exact
    ⟨(sharpSelected_le_finite c.profile hn hU).trans_lt hs.1,
      (sharpPrime_le_finite c.profile hU).trans_lt hs.2⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
