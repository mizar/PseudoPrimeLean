/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.OddPrimeCutoff
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointEvenPolynomial

/-! # Prime rounding for arbitrary real witness cutoffs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Round a real cutoff down to its greatest prime, retaining two. Below two the
input is unchanged. This total function tightens actual prime witness bounds. -/
noncomputable def primeRound (R : ℝ) : ℝ :=
  if 2 ≤ R then (max 2 (AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE R) : ℕ) else R

/-- Every real cutoff dominates its rounded value. Split at two and use the
existing odd-prime floor bound; this proves non-worsening without a domain hypothesis. -/
theorem primeRound_le (R : ℝ) : primeRound R ≤ R := by
  unfold primeRound
  split_ifs with h
  · rw [Nat.cast_max, Nat.cast_ofNat]
    exact
      max_le h
        (AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE_cast_le
          (le_trans (by norm_num only : (0 : ℝ) ≤ 2) h))
  · exact le_rfl

/-- Any prime below a real cutoff remains below its rounding. Separate the
prime two from odd primes and use the finite greatest-odd-prime specification. -/
theorem prime_le_primeRound {p : ℕ} (hp : p.Prime) {R : ℝ} (hR : (p : ℝ) ≤ R) :
    (p : ℝ) ≤ primeRound R := by
  have htwo : (2 : ℝ) ≤ R := (Nat.cast_le.mpr hp.two_le).trans hR
  rw [primeRound, ite_eq_left htwo, Nat.cast_max, Nat.cast_ofNat]
  rcases hp.eq_two_or_odd' with he | ho
  · rw [he]
    exact le_max_left _ _
  · exact
      (Nat.cast_le.mpr (AnalyticNumberTheory.Arithmetic.le_greatestOddPrimeLE hp ho hR)).trans
        (le_max_right _ _)

/-- A prime cutoff is fixed by rounding, by the upper bound and prime inclusion.
This preserves every already integral prime certificate. -/
theorem primeRound_prime {p : ℕ} (hp : p.Prime) : primeRound (p : ℝ) = p := by
  exact le_antisymm (primeRound_le p) (prime_le_primeRound hp le_rfl)

/-- An actual rejecting prime under any real cutoff also lies under its rounded
cutoff. Prime inclusion transfers the bound without changing the witness. -/
theorem exists_prime_round {n : ℕ} {R : ℝ}
    (h : ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ R ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ primeRound R ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hr⟩ := h
  exact ⟨p, hp, prime_le_primeRound hp hb, hr⟩

/-- For a natural input above one, extract a least rejecting prime under the
rounded cutoff from any actual bounded witness. Use the existing least-prime API. -/
theorem exists_least_round {n : ℕ} (hn : 1 < n) {R : ℝ}
    (h : ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ R ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ primeRound R ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject (exists_prime_round h)

/-- An odd prime cutoff remains constant until the next possible prime.
Use its inclusion and the greatest-prime specification; the gap excludes larger candidates. -/
theorem primeRound_eq_odd_of_gap {b q : ℕ} (hb : b.Prime) (ho : Odd b) {R : ℝ} (hL : (b : ℝ) ≤ R)
    (hU : R < q) (hgap : ∀ k ∈ Finset.Ioo b q, ¬Nat.Prime k) : primeRound R = b := by
  classical
  have htwo : (2 : ℝ) ≤ R := (Nat.cast_le.mpr hb.two_le).trans hL
  have hg : (AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE R).Prime := by
    exact
      (Nat.findGreatest_spec (P := fun p : ℕ => p.Prime ∧ Odd p) (Nat.le_floor hL)
          (show b.Prime ∧ Odd b from ⟨hb, ho⟩)).1
  have hgR :=
    AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE_cast_le
      (le_trans (by norm_num only : (0 : ℝ) ≤ 2) htwo)
  have hgb : AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE R ≤ b := by
    by_contra hn
    have hgq : AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE R < q := by
      exact_mod_cast hgR.trans_lt hU
    exact hgap _ (Finset.mem_Ioo.mpr ⟨lt_of_not_ge hn, hgq⟩) hg
  apply le_antisymm _ (prime_le_primeRound hb hL)
  rw [primeRound, ite_eq_left htwo]
  exact Nat.cast_le.mpr (max_le hb.two_le hgb)

end PseudoPrime.PrimeTestBounds.MillerRabin
