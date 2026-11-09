/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS

/-! Least rejecting primes and their cumulative maximum. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The least rejecting prime for an odd composite above one, and zero otherwise.
The infimum ranges over primes rejecting the canonical strong MR test.
Under GRH the set is nonempty and its infimum is an actual least witness.
Zero outside the target domain makes cumulative maxima total, including empty ranges. -/
noncomputable def compositeLeastPrime (n : ℕ) : ℕ := by
  classical
    exact
    if 1 < n ∧ Odd n ∧ ¬n.Prime then
      sInf {p : ℕ | p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)}
    else 0

/-- Under GRH an odd composite has its canonical least rejecting prime below log squared.
Transfer the existing actual prime witness by the natural infimum property.
This supplies a safe bound for all inputs preceding any high-profile entrance. -/
theorem compositeLeastPrime_le_log_sq (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) :
    (compositeLeastPrime n : ℝ) ≤ Real.log n ^ 2 := by
  obtain ⟨p, hp, hb, hr⟩ := exists_prime_millerRabin_witness_le_log_sq hGRH hn ho hc
  have hfail : ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    PrimeTest.not_strongMillerRabinPass_iff.mpr hr
  simp only [compositeLeastPrime, ite_eq_left (show 1 < n ∧ Odd n ∧ ¬n.Prime from ⟨hn, ho, hc⟩)]
  have hm :=
    Nat.sInf_le (s := {q : ℕ | q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)})
      ⟨hp, hfail⟩
  exact (Nat.cast_le.mpr hm).trans hb

/-- The maximum of least rejecting primes over odd composites at most the upper bound.
Use the finite natural supremum of the total individual function, whose non-target values
are zero. Thus an empty target range has value zero without an extra nonemptiness premise.
This definition is mathematical and requires no generated exhaustive certificate. -/
noncomputable def cumulativeLeastPrime (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).sup compositeLeastPrime

/-- Under GRH the total individual value at an odd composite is an actual prime
rejecting strong MR and is least among all rejecting primes. Obtain nonemptiness
from the existing witness theorem and apply the natural infimum specification. -/
theorem compositeLeastPrime_spec (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) :
    (compositeLeastPrime n).Prime ∧
      ¬PrimeTest.StrongMillerRabinPass n (compositeLeastPrime n : ZMod n) ∧
      ∀ q : ℕ,
        q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → compositeLeastPrime n ≤ q := by
  obtain ⟨p, hp, _, hr⟩ := exists_prime_millerRabin_witness_le_log_sq hGRH hn ho hc
  have hfail : ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    PrimeTest.not_strongMillerRabinPass_iff.mpr hr
  have hs : {q : ℕ | q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)}.Nonempty :=
    ⟨p, hp, hfail⟩
  rw [compositeLeastPrime, ite_eq_left (show 1 < n ∧ Odd n ∧ ¬n.Prime from ⟨hn, ho, hc⟩)]
  exact
    ⟨(Nat.sInf_mem hs).1, (Nat.sInf_mem hs).2, fun q hq hqr ↦
      Nat.sInf_le (s := {q : ℕ | q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)})
        ⟨hq, hqr⟩⟩

/-- A real bound for every individual least-prime value through `N` also bounds their
cumulative maximum. The value at zero supplies nonnegativity of the bound. Passing each
individual bound through the natural floor and taking the finite supremum proves the claim;
this transfers pointwise witness estimates to cumulative bounds without a GRH assumption. -/
theorem cumulativeLeastPrime_le_of_pointwise {N : ℕ} {B : ℝ}
    (hB : ∀ n ≤ N, (compositeLeastPrime n : ℝ) ≤ B) : (cumulativeLeastPrime N : ℝ) ≤ B := by
  have h0 : 0 ≤ B := (Nat.cast_nonneg (compositeLeastPrime 0)).trans (hB 0 (Nat.zero_le N))
  have hb : cumulativeLeastPrime N ≤ ⌊B⌋₊ := by
    apply Finset.sup_le
    intro n hn
    exact (Nat.le_floor_iff h0).mpr (hB n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))
  exact (Nat.cast_le.mpr hb).trans (Nat.floor_le h0)

end PseudoPrime.PrimeTestBounds.MillerRabin
