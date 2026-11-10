/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInteriorWitness

/-! # Square-factor witnesses from 68 to 200 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd input with a prime-square divisor and logarithm between 68
and 200 has a quarter-square rejecting prime. Such an input is composite and
cannot be a squarefree uniform triple, so the nonuniform interval applies. -/
theorem quarter_square_68_200 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (68 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 200) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hsf : ¬Squarefree n := by
    intro hs
    exact (Nat.squarefree_iff_prime_squarefree.mp hs p hp) (by simpa only [pow_two] using hdiv)
  have hu : ¬UniformKorseltTriple n := fun h ↦ hsf h.1
  have hc : ¬n.Prime := by
    intro hprime
    have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
    have heq : p = n := Nat.dvd_prime hprime |>.mp hpn |>.resolve_left hp.ne_one
    subst p
    have hs : n ^ 2 ≤ n := Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv
    nlinarith only [hs, hn]
  exact quarter_common_nonuniform_mid hn ho hc hu hGRH hL hU le_rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
