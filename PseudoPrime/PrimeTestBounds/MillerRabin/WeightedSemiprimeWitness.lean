/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeProductFamilyTransfer
public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeLocalCounting

/-! # Semiprime witnesses from weighted repeated-prime products -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a distinct semiprime has a rejecting prime below `X` when a
weighted prime-multiset family meets the indicated size, count and local
envelope budgets. The local branch handles small `q`; otherwise its logarithm
forces both the product-size and subgroup-cardinality inequalities. -/
theorem exists_prime_reject_semiprime_weighted_cell {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q) (S : Finset ℕ)
    (F : Finset (Multiset ℕ)) (B budget : ℕ) (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d)
    (hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S) (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B)
    (hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / d) (hcost : ∀ T ∈ F, (T.map w).sum ≤ budget) {A D X : ℝ}
    (hA : (budget : ℝ) / d ≤ A) (hD : D ≤ Real.log (F.card : ℝ)) (hB : (B : ℝ) ≤ X)
    (hlocalBound : localFullEnvelope (max A (Real.log n - D)) ≤ X)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hdiv : q ∣ n := hprod ▸ dvd_mul_left q p
  have hbad : ¬q - 1 ∣ n - 1 := by
    rw [hprod]
    exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq
  by_cases hlocal : Real.log q ≤ max A (Real.log n - D)
  · obtain ⟨r, hr, hb, hf⟩ := exists_prime_reject_nonKorselt_local hn ho hq hdiv hbad hGRH hlocal
    exact ⟨r, hr, hb.trans hlocalBound, hf⟩
  · have hqbig : max A (Real.log n - D) < Real.log q := lt_of_not_ge hlocal
    have hsize : (budget : ℝ) / d < Real.log q := hA.trans_lt ((le_max_left _ _).trans_lt hqbig)
    have hlog : Real.log n = Real.log p + Real.log q := by
      rw [hprod, Nat.cast_mul,
        Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)]
    have hpLog : Real.log p < Real.log (F.card : ℝ) := by
      have hh := (le_max_right A (Real.log n - D)).trans_lt hqbig
      linarith only [hlog, hh, hD]
    have hFpos : 0 < F.card := by
      by_contra h
      have hz : F.card = 0 := Nat.eq_zero_of_not_pos h
      rw [hz, Nat.cast_zero, Real.log_zero] at hpLog
      exact (not_lt_of_ge (Real.log_natCast_nonneg p)) hpLog
    have hpCount : p < F.card := by
      exact_mod_cast
        (Real.log_lt_log_iff (Nat.cast_pos.mpr hp.pos) (Nat.cast_pos.mpr hFpos)).mp hpLog
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_semiprime_weighted hn ho hp hq hprod S F B budget w d hd hsub hprime
        hbound hw hcost hsize hpCount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
