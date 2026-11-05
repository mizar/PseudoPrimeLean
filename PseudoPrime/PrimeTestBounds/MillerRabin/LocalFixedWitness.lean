/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalAdaptiveEven
public import PseudoPrime.LLS.PaperStatements.FullEndpointEightyOneSubgroup

/-! # Fixed local witness bounds at moderate logarithmic scales -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, if `log q ≤ 9`, a proper local subgroup containing all passing
residues gives a rejecting prime at most 61. Transfer the existing subgroup
prime bound through the passing-residue containment. This is the fixed part of
the moderate-scale local envelope. -/
theorem exists_prime_reject_local_le_sixty_one {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : Real.log q ≤ 9) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 61 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.PaperStatements.exists_prime_outside_subgroup_le_sixty_one H hH hGRH hq
  exact ⟨p, hp, Nat.cast_le.mpr hb, fun h ↦ hout (hpass p h)⟩

/-- Under GRH, a proper local subgroup with `9 ≤ log q ≤ 26` containing all
passing residues gives a rejecting prime through `(81/100) * s²` for any
`s ≥ log q`. Transfer the existing subgroup bound and use square monotonicity.
This is the quadratic part of the moderate-scale local envelope. -/
theorem exists_prime_reject_local_eighty_one {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s : ℝ} (hlo : 9 ≤ Real.log q)
    (hhi : Real.log q ≤ 26) (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (81 / 100 : ℝ) * s ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.PaperStatements.exists_primeOutsideSubgroup_81_100_logSq_GRH H hH hGRH hlo hhi
  have hs0 : 0 ≤ Real.log q := by linarith only [hlo]
  have hsq : (Real.log q) ^ 2 ≤ s ^ 2 := (sq_le_sq₀ hs0 (hs0.trans hs)).mpr hs
  exact
    ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_left hsq (by norm_num only)), fun h ↦ hout (hpass p h)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
