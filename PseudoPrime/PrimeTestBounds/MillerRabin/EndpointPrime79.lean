/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.EndpointPrime79
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFinitePrincipal
public import PseudoPrime.PrimeTestBounds.MillerRabin.SharpNormalForm

/-! # Fixed-79 actual prime witnesses, least witnesses and both sharp strict comparisons -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The fixed-79 profile supplies an actual rejecting prime through its stated cap. -/
theorem exists_prime_endpoint79 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ Analysis.prime79Cap) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 79 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hr⟩ :=
    exists_prime_of_finitePrincipal_gap hn ho hc hGRH Analysis.prime79_radius_bounds.1
      Analysis.prime79CreditR Analysis.prime79CreditS Analysis.prime79_reciprocal
      Analysis.prime79_smoothed (LLS.PaperStatements.prime79_gap hL)
  have hq : (p : ℝ) < 83 := hb.trans_lt Analysis.prime79_radius_bounds.2
  have hg : ∀ k ∈ Finset.Ioo 79 83, ¬Nat.Prime k := by decide +kernel
  have h79 : p ≤ 79 := by
    by_contra hn
    exact hg p (Finset.mem_Ioo.mpr ⟨Nat.lt_of_not_ge hn, by exact_mod_cast hq⟩) hp
  exact ⟨p, hp, Nat.cast_le.mpr h79, hr⟩

/-- The least rejecting prime also lies below 79 through the fixed-79 cap. -/
theorem exists_least_endpoint79 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ Analysis.prime79Cap) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 79 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject (exists_prime_endpoint79 hn ho hc hGRH hL)

/-- Fixed 79 strictly beats both current sharp cutoffs on the specified closed band. -/
theorem endpoint79_strict {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n) (hL : 1261 / 100 ≤ Real.log n)
    (hU : Real.log n ≤ Analysis.prime79Cap) :
    (79 : ℝ) < sharpSelectedEnvelope n ∧ (79 : ℝ) < sharpPrimeEnvelope n := by
  have he : sharpSelectedEnvelope n = LLS.PaperStatements.pointwiseCutoff (Real.log n) := by
    rw [sharpSelected_eq_low hN
        (by
          norm_num only [Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat] at hU
          linarith only [hU]),
      lowFiniteSelected_eq_refined hn (by linarith only [hL]),
      refined_eq_pointwise_low hn (by linarith only [hL])
        (by
          norm_num only [Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat] at hU
          linarith only [hU])]
  have hb : (83 : ℝ) ≤ sharpSelectedEnvelope n := by
    rw [he]
    exact (LLS.PaperStatements.prime79_pointwise_lower hL).le
  have hp : Nat.Prime 83 := by decide +kernel
  have hr : (83 : ℝ) ≤ sharpPrimeEnvelope n := by
    rw [sharpPrimeEnvelope, sharp_eq_selected hn]
    exact prime_le_primeRound hp hb
  constructor <;> linarith only [hb, hr]

end PseudoPrime.PrimeTestBounds.MillerRabin
