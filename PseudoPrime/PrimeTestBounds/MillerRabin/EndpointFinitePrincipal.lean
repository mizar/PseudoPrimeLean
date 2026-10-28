/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.EndpointFiniteProfiles
public import PseudoPrime.Analysis.EndpointFiniteSums
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointLowPrime

/-! # Actual Miller–Rabin prime witnesses from finite principal certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Actual finite principal lower bounds and positive gap provide a rejecting MR prime. -/
theorem exists_prime_of_finitePrincipal_gap {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 2 ≤ y) (dR dS : ℝ)
    (hR :
      2 * Real.log y - Analysis.pointwiseReciprocalLoss y + dR ≤
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (y ^ 2))
    (hS :
      y ^ 2 - y / 20 - (1839 / 500 : ℝ) * Real.log y - 21 / 20 + dS ≤
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2))
    (hgap :
      0 < LLS.PaperStatements.finitePrincipalGap (Real.log n) (2096 / 1831) y (Real.log y) dR dS) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  obtain ⟨χ, hne, hpass⟩ := exists_character_trivial_on_pass hn ho hc
  have heven := character_even_of_trivial_on_pass hn ho hpass
  obtain ⟨p, hp, hb, hv⟩ :=
    LLS.PaperStatements.finitePrincipal_ne_one_prime χ hne heven hGRH hy dR dS hR hS hgap
  exact ⟨p, hp, hb, fun h ↦ hv (hpass p h)⟩

/-- No prime lies strictly between a finite profile cutoff and its next prime. -/
theorem finitePrincipal_no_between (f : Analysis.FinitePrimeProfile) :
    ∀ k ∈ Finset.Ioo f.bound f.nextPrime, ¬Nat.Prime k := by cases f <;> decide +kernel

/-- A prime below a profile's next prime is at most its fixed cutoff. -/
theorem finitePrincipal_round (f : Analysis.FinitePrimeProfile) {p : ℕ} (hp : p.Prime)
    (hq : p < f.nextPrime) : p ≤ f.bound := by
  by_contra hb
  exact finitePrincipal_no_between f p (Finset.mem_Ioo.mpr ⟨Nat.lt_of_not_ge hb, hq⟩) hp

/-- Each of thirteen finite-principal profiles gives an actual rejecting prime through its cap. -/
theorem exists_prime_finitePrincipal (f : Analysis.FinitePrimeProfile) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ f.logCap) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ f.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hr⟩ :=
    exists_prime_of_finitePrincipal_gap hn ho hc hGRH (Analysis.finitePrincipal_radius_bounds f).1
      f.deltaR f.deltaS (Analysis.finitePrincipal_reciprocal f)
      (Analysis.finitePrincipal_smoothed f) (LLS.PaperStatements.finitePrincipal_profile_gap f hL)
  have hq : (p : ℝ) < f.nextPrime := hb.trans_lt (Analysis.finitePrincipal_radius_bounds f).2
  exact ⟨p, hp, Nat.cast_le.mpr (finitePrincipal_round f hp (by exact_mod_cast hq)), hr⟩

/-- The least rejecting prime also satisfies each of the thirteen strengthened fixed cutoffs. -/
theorem exists_least_finitePrincipal (f : Analysis.FinitePrimeProfile) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ f.logCap) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject
      (exists_prime_finitePrincipal f hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
