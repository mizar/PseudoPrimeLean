/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030NonuniformLog8

/-! # Factor-type 0.30 consequences from scale 8 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, each distinct odd semiprime with logarithm at least 8 has a
0.30 rejecting prime. Its larger prime factor cannot satisfy the Korselt
divisibility condition, so the nonuniform theorem applies. -/
theorem exists_prime_reject_03_semiprime_log8 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hc : ¬n.Prime := by
    rw [hprod]
    exact Nat.not_prime_mul hp.ne_one hq.ne_one
  have hu : ¬UniformKorseltTriple n := by
    intro h
    have hqn : q ∣ n := hprod ▸ dvd_mul_left q p
    have hdiv := h.2.2.1 q hq hqn
    rw [hprod] at hdiv
    exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq hdiv
  exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

/-- Under GRH, an odd composite divisible by a prime square has a 0.30
rejecting prime from logarithmic scale 8. Such an input cannot be squarefree,
so the nonuniform theorem applies. -/
theorem exists_prime_reject_03_square_log8 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hp : p.Prime) (hdiv : p ^ 2 ∣ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hu : ¬UniformKorseltTriple n := by
    intro h
    have hs := (Nat.squarefree_iff_prime_squarefree.mp h.1) p hp
    exact hs ((pow_two p).symm ▸ hdiv)
  exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
