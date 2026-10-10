/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Corollary12Reconstruction
public import PseudoPrime.NumberTheory.CertificateTree
public import PseudoPrime.NumberTheory.PrimeLookup

/-! Factor-list routes to the shared analytic intervals of Corollary 1.2. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Modulus and prime-count conditions covered by the five certified intervals.
Each disjunct selects a lower modulus endpoint and an upper distinct-prime count;
an upper modulus bound of 20000 is supplied separately to the consumer. -/
def smallResidueAnalyticCondition (q w : ℕ) : Prop :=
  (800 ≤ q ∧ w ≤ 1) ∨
    (1300 ≤ q ∧ w ≤ 2) ∨ (2100 ≤ q ∧ w ≤ 3) ∨ (3300 ≤ q ∧ w ≤ 4) ∨ (5700 ≤ q ∧ w ≤ 5)

/-- Decide the finite disjunction of endpoint and prime-count comparisons. -/
instance (q w : ℕ) : Decidable (smallResidueAnalyticCondition q w) :=
  inferInstanceAs
    (Decidable
      ((800 ≤ q ∧ w ≤ 1) ∨
        (1300 ≤ q ∧ w ≤ 2) ∨ (2100 ≤ q ∧ w ≤ 3) ∨ (3300 ≤ q ∧ w ≤ 4) ∨ (5700 ≤ q ∧ w ≤ 5)))

/-- Accept two or a successful lookup in the supplied prime tree.
The separate case for two allows an odd-prime catalog to certify factor lists. -/
def residueFactorPrimeCheck (primes : BinaryTree ℕ) (p : ℕ) : Bool :=
  (p == 2) || NumberTheory.primeTreeLookup primes p

/-- A positive factor lookup yields a prime when all tree labels are prime.
Split off two and otherwise apply the shared lookup soundness theorem.
This supplies primality without repeating trial division in each factor list. -/
theorem residueFactorPrimeCheck_prime {primes : BinaryTree ℕ}
    (hp : NumberTheory.primeTreeChecked primes) {p : ℕ}
    (hc : residueFactorPrimeCheck primes p = true) : p.Prime := by
  rcases Bool.or_eq_true_iff.mp hc with h2 | ht
  · have he : p = 2 := beq_iff_eq.mp h2
    exact he ▸ Nat.prime_two
  · exact NumberTheory.primeTreeLookup_prime hp ht

/-- Verify the factorization and analytic interval condition of a modulus entry.
Check primality in the shared tree, the product and the distinct entries' cardinality.
The checked list substitutes for direct reduction of the mathematical prime-factor set. -/
def residueFactorRouteCheck (primes : BinaryTree ℕ) (e : ℕ × List ℕ) : Bool :=
  e.2.all (residueFactorPrimeCheck primes) &&
    decide (e.2.prod = e.1 ∧ smallResidueAnalyticCondition e.1 e.2.toFinset.card)

/-- A checked factor route gives the actual modulus's analytic interval condition.
Reflect the product and numerical inequalities, identify the supplied factor set
with the prime factors and transfer the cardinality bounds.
This supplies the true prime count required by the analytic interval theorem. -/
theorem residueFactorRouteCheck_sound {primes : BinaryTree ℕ}
    (hp : NumberTheory.primeTreeChecked primes) {e : ℕ × List ℕ}
    (hc : residueFactorRouteCheck primes e = true) :
    smallResidueAnalyticCondition e.1 e.1.primeFactors.card := by
  have hb := Bool.and_eq_true_iff.mp hc
  have hv : e.2.prod = e.1 ∧ smallResidueAnalyticCondition e.1 e.2.toFinset.card :=
    of_decide_eq_true hb.2
  have hf : NumberTheory.primeFactorListCheck e.1 e.2 = true :=
    decide_eq_true
      ⟨hv.1, fun p hm ↦ residueFactorPrimeCheck_prime hp (List.all_eq_true.mp hb.1 p hm)⟩
  rw [NumberTheory.primeFactorListCheck_sound hf]
  exact hv.2

/-- Under GRH and the upper modulus bound, any of the five interval conditions
gives the least-prime estimate in every unit residue. Select the appropriate
certified interval and apply its common soundness theorem.
This is the analytic branch of the finite-range partition. -/
theorem leastPrime_of_smallResidueAnalyticCondition {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hu : q ≤ 20000) (hc : smallResidueAnalyticCondition q q.primeFactors.card)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  rcases hc with h1 | h2 | h3 | h4 | h5
  · exact Corollary12Reconstruction.leastPrime1 a h1.1 hu h1.2 hGRH
  · exact Corollary12Reconstruction.leastPrime2 a h2.1 hu h2.2 hGRH
  · exact Corollary12Reconstruction.leastPrime3 a h3.1 hu h3.2 hGRH
  · exact Corollary12Reconstruction.leastPrime4 a h4.1 hu h4.2 hGRH
  · exact Corollary12Reconstruction.leastPrime5 a h5.1 hu h5.2 hGRH

/-- Lookup in a checked factor-route tree yields the GRH least-prime bound.
Recover the queried modulus and its actual prime-count bound from the checked
factorization, then apply the shared interval theorem.
This connects generated factor data to the public finite-range proof. -/
theorem exists_least_prime_in_residue_le_of_factor_route_lookup {primes : BinaryTree ℕ}
    (hp : NumberTheory.primeTreeChecked primes) {routes : BinaryTree (ℕ × List ℕ)}
    (ht : NumberTheory.certificateTreeAllCheck (residueFactorRouteCheck primes) routes = true)
    {q : ℕ} [NeZero q] {e : ℕ × List ℕ}
    (hl : NumberTheory.certificateTreeLookup Prod.fst routes q = some e) (hu : q ≤ 20000)
    (a : (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  obtain ⟨he, hc⟩ := NumberTheory.certificateTreeAllCheck_lookup ht hl
  have hq : smallResidueAnalyticCondition q q.primeFactors.card :=
    he ▸ residueFactorRouteCheck_sound hp hc
  exact leastPrime_of_smallResidueAnalyticCondition a hu hq hGRH

end PseudoPrime.LLS.PaperStatements
