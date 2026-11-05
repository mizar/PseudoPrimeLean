/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalLogSquareBounds

/-! # Combining local even-character and logarithmic witness bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and for local modulus `q ≥ 5`, the minimum of `s²` and the
finite even envelope bounds a prime rejecting odd `n > 1`, provided `q ∣ n`,
`log q ≤ s`, and a proper local subgroup contains all passing residues.
Select the smaller bound and use its corresponding actual witness. This is an
intermediate minimum before adding the other local-envelope candidates. -/
theorem exists_prime_reject_local_log_min {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hq : 5 ≤ q) (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s : ℝ} (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ min (s ^ 2) (localEvenEnvelope s) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (le_trans (by decide : 1 ≤ 5) hq)
  have hl : 0 ≤ Real.log q := Real.log_nonneg hqR
  have hsq : (Real.log q) ^ 2 ≤ s ^ 2 := (sq_le_sq₀ hl (hl.trans hs)).mpr hs
  by_cases h : s ^ 2 ≤ localEvenEnvelope s
  · obtain ⟨p, hp, hpB, hpF⟩ := exists_prime_witness_le_local_log_sq hn ho hq hqn H hH hpass hGRH
    refine ⟨p, hp, ?_, hpF⟩
    rw [min_eq_left h]
    exact hpB.trans hsq
  · obtain ⟨p, hp, hpB, hpF⟩ := exists_prime_reject_local_envelope hn ho hqn H hH hpass hGRH hs
    refine ⟨p, hp, ?_, hpF⟩
    rw [min_eq_right (le_of_not_ge h)]
    exact hpB

end PseudoPrime.PrimeTestBounds.MillerRabin
