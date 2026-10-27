/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ParameterizedPart1Saving
public import PseudoPrime.LLS.ExactFactorLossTheorem11S1

/-! # Part 1 root witnesses with variable reciprocal loss and factor cost -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a modulus and a real reciprocal-loss parameter r.
Output: the nonnegative part of 2 log log(q)-r minus the prime-factor reciprocal cost.
Role: share pointwise or uniform reciprocal estimates across Part 1 radius criteria. -/
noncomputable def reciprocalSavingAuxiliary (q : ℕ) (r : ℝ) : ℝ :=
  max 0 (2 * Real.log (Real.log q) - r - AnalyticNumberTheory.Arithmetic.primeFactorLogSum q)

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- Input: a root above log(q), q at least 3000, prime triviality, and a reciprocal lower bound.
Claim: the full-level reciprocal sum is at least the parameterized auxiliary saving.
Proof: use logarithm monotonicity before applying the generic exact-support lower bound.
Role: retain a variable reciprocal loss at the chosen root. -/
theorem characterReciprocalWeightedSum_re_ge_root_saving {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) {y r : ℝ} (hy : Real.log q ≤ y)
    (hR : Real.log (y ^ 2) - r ≤ reciprocalWeightedMangoldtSum (y ^ 2))
    (ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ y ^ 2 → χ p = 1) :
    reciprocalSavingAuxiliary q r ≤ (characterReciprocalWeightedSum (y ^ 2) χ).re := by
  have hL := Analysis.eight_lt_log_level hq
  have hy0 : 0 < y := by linarith only [hL, hy]
  have hl := Real.log_le_log (show 0 < Real.log (q : ℝ) by linarith only [hL]) hy
  have hmono :
    reciprocalSavingAuxiliary q r ≤ max 0 (Real.log (y ^ 2) - r - primeFactorLogSum q) := by
    dsimp only [reciprocalSavingAuxiliary]
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact max_le_max (le_refl _) (by linarith only [hl])
  exact
    hmono.trans
      (characterReciprocalWeightedSum_re_ge_of_reciprocal_lower χ (sq_pos_of_pos hy0) hR ht)

/-- Input: GRH, nonprincipality, an arbitrary reciprocal loss, and a nonnegative factor-cost cap.
The root increment satisfies the corresponding retained-saving inequality.
Claim: a coprime prime with non-one character value exists through the squared root.
Proof: combine the arbitrary-saving upper bound with the exact common-factor lower bound.
Role: support uniform or cutoff-dependent reciprocal refinements without new separation proofs. -/
theorem exists_prime_character_ne_one_of_reciprocal_saving_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y r w : ℝ} (hy : Real.log q ≤ y)
    (hR :
      Real.log (y ^ 2) - r ≤ AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (y ^ 2))
    (hw : 0 ≤ w)
    (hcost : AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum (y ^ 2) q / y ≤ w)
    (hB :
      2 * Real.log (Real.log q) + 7031 / 5000 + w - 2 * reciprocalSavingAuxiliary q r ≤
        y - Real.log q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ y ^ 2 := by
  by_contra hn
  have htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ y ^ 2 → χ p = 1 := by
    intro p hp hd hb
    by_contra hv
    exact hn ⟨p, hp, hd, hv, hb⟩
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim : χ.primitiveCharacter ≠ 1 :=
    AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hN : 2 ≤ χ.conductor :=
    Nat.succ_le_iff.mpr
      (Nat.lt_of_le_of_ne (NeZero.pos χ.conductor)
        (Ne.symm
          (AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one
            hprim)))
  have hL := Analysis.eight_lt_log_level hq
  have hy0 : 0 < y := by linarith only [hL, hy]
  have hx : (64 : ℝ) ≤ y ^ 2 := by nlinarith only [hL, hy]
  have hs : Real.sqrt (y ^ 2) = y := Real.sqrt_sq hy0.le
  have hrecip := characterReciprocalWeightedSum_re_ge_root_saving χ hq hy hR htrivial
  have hu :=
    characterLogWeightedSum_re_le_fullLevel_of_saving χ hN hprim hGRH hx hL
      (by
        rw [hs]; exact hy)
      (le_max_left _ _) hrecip
  rw [hs] at hu
  have hl := characterLogWeightedSum_re_ge_exact_factor_root χ hq hGRH hy htrivial
  have hm := mul_le_mul_of_nonneg_left hcost hy0.le
  have hl' :
    y ^ 2 - y * (2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass + w) -
        Real.log (2 * Real.pi) * Real.log (y ^ 2) -
        1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ).re := by
    nlinarith only [hl, hm]
  exact
    Analysis.refinedPart1_bounds_incompatible_retained_saving hL hy (le_max_left _ _) hw
      AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000
      (le_trans (by norm_num only : (57 / 50 : ℝ) ≤ 2096 / 1831) Analysis.log_pi_ge_2096_div_1831)
      Analysis.log_two_mul_pi_lt.le hB hu hl'

end PseudoPrime.LLS
