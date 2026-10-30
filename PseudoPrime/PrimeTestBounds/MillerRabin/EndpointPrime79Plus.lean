/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.EndpointPrime79Plus
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFinitePrincipal
public import PseudoPrime.PrimeTestBounds.MillerRabin.TunedIntervalSelection

/-! # Fixed-79 actual prime witnesses, least witnesses and both sharp strict comparisons -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The fixed-79 profile supplies an actual rejecting prime through its stated cap. -/
theorem exists_prime_endpoint79Plus {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ LLS.PaperStatements.prime79PlusCap) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 79 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hr⟩ :=
    exists_prime_of_finitePrincipal_gap hn ho hc hGRH
      LLS.PaperStatements.prime79Plus_radius_bounds.1
      LLS.PaperStatements.prime79PlusCreditR LLS.PaperStatements.prime79PlusCreditS
      LLS.PaperStatements.prime79Plus_reciprocal
      LLS.PaperStatements.prime79Plus_smoothed
      (LLS.PaperStatements.prime79Plus_gap hL)
  have hq : (p : ℝ) < 83 := hb.trans_lt LLS.PaperStatements.prime79Plus_radius_bounds.2
  have hg : ∀ k ∈ Finset.Ioo 79 83, ¬Nat.Prime k := by decide +kernel
  have h79 : p ≤ 79 := by
    by_contra hn
    exact hg p (Finset.mem_Ioo.mpr ⟨Nat.lt_of_not_ge hn, Nat.cast_lt.mp hq⟩) hp
  exact ⟨p, hp, Nat.cast_le.mpr h79, hr⟩

/-- The least rejecting prime also lies below 79 through the fixed-79 cap. -/
theorem exists_least_endpoint79Plus {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ LLS.PaperStatements.prime79PlusCap) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 79 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (exists_prime_endpoint79Plus hn ho hc hGRH hL)

/-- Above the old final finite cap and below the Gaussian entrance, the full tuned
selection equals its pointwise cutoff. All new high and analytic guards are inactive. -/
theorem tunedSelected_eq_pointwise_low {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n)
    (hL : 126409 / 10000 < Real.log n) (hU : Real.log n < 63) :
    tunedSelectedEnvelope n = LLS.PaperStatements.pointwiseCutoff (Real.log n) := by
  rw [← tuned_eq_selected hn, tunedWitnessEnvelope, ite_eq_right (not_lt.mpr hN),
    tunedHigh_eq_base (by linarith only [hU] : Real.log n < 30000000000)]
  simp only [sharpGuardMin, ite_eq_right (not_le.mpr hU), min_self]
  rw [tunedFinite_eq_sharp_of_log hn hL, sharp_eq_selected hn, sharpSelected_eq_low hN hU,
    lowFiniteSelected_eq_refined hn (by linarith only [hL]),
    refined_eq_pointwise_low hn (by linarith only [hL]) hU]

/-- The newly certified fixed value 79 is strictly below both complete tuned public
cutoffs on the closed logarithmic interval [12.65,12.659]. The comparison uses the
pointwise identity and the already proved prime-83 lower bound, without numerical roots. -/
theorem endpoint79Plus_strict {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n) (hL : 1265 / 100 ≤ Real.log n)
    (hU : Real.log n ≤ LLS.PaperStatements.prime79PlusCap) :
    (79 : ℝ) < tunedSelectedEnvelope n ∧ (79 : ℝ) < tunedPrimeEnvelope n := by
  norm_num only [LLS.PaperStatements.prime79PlusCap, Rat.cast_div, Rat.cast_ofNat] at hU
  have he := tunedSelected_eq_pointwise_low hn hN (by linarith only [hL]) (by linarith only [hU])
  have hb : (83 : ℝ) < tunedSelectedEnvelope n := by
    rw [he]
    exact LLS.PaperStatements.prime79_pointwise_lower (by linarith only [hL])
  have hp : Nat.Prime 83 := by decide +kernel
  have hr : (83 : ℝ) ≤ tunedPrimeEnvelope n := by
    rw [tunedPrimeEnvelope, tuned_eq_selected hn]
    exact prime_le_primeRound hp hb.le
  constructor <;> linarith only [hb, hr]

end PseudoPrime.PrimeTestBounds.MillerRabin
