/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GeneralTwoPoleGammaWitness
public import PseudoPrime.LLS.TwoPolePrimeTrivialBounds2

/-! # Character-free two-pole bounds under full prime triviality -/

@[expose] public section

namespace PseudoPrime.LLS

/-- A character-free two-pole Gamma budget at a modulus, finite support and scale.
Discard the vanished exclusion defect and nonpositive local correction under full
prime triviality, then bound the conductor logarithm by the level logarithm.
This leaves one explicit scalar inequality for prime-base MR rejection. -/
noncomputable def twoPolePrimeTrivialUpper (q : ℕ) (S : Finset ℕ) (x : ℝ) : ℝ :=
  Real.log q / 2 + 419 / 50 -
      2 *
        (∑ n ∈ S,
          AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n) +
    64 / 9 +
    ((7 / 6 : ℝ) * Real.log (max 20000 q : ℕ) + 4) / Real.sqrt x +
    x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log q + 28) + 1)

/-- Twice the ramp lower bound minus the principal Gamma upper bound and the
character-free two-pole budget. Positivity contradicts full prime triviality.
This definition does not assert a numerical starting point. -/
noncomputable def twoPolePrimeTrivialSeparation (q : ℕ) (S : Finset ℕ) (x : ℝ) : ℝ :=
  2 *
      ((∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        gammaRampPairedErrorNumerator x / Real.sqrt x) -
    (Real.sqrt x +
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x) -
    twoPolePrimeTrivialUpper q S x

open AnalyticNumberTheory.Arithmetic in
/-- Under full prime triviality below the cutoff and positive scale, the general
character-dependent upper budget is at most the level-only budget. The finite
excluded defect vanishes and the local series is nonpositive; conductor monotonicity
controls the remaining positive factors. No RH or nonprincipality is needed. -/
theorem generalTwoPoleUpper_le_of_all_prime_trivial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) :
    generalTwoPoleGammaUpper χ S x ≤ twoPolePrimeTrivialUpper q S x := by
  have hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ.primitiveCharacter p = 1 :=
    fun p hprime hb ↦ PaperStatements.primitiveCharacter_apply_one_of_apply_one χ (ht p hprime hb)
  have hD :=
    excludedCharacterDefect_eq_zero_of_all_prime_trivial (N := q) χ.primitiveCharacter S
      (pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) hS
      (fun n _ hn ↦ pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero _ _ _ hn) hp
  have hC :=
    gammaLocalCorrection_nonpos_of_level_primes_above χ hx
      (fun p hmem ↦ (level_prime_above_cutoff_of_all_prime_trivial χ ht hmem).le)
  have hlog : Real.log χ.conductor ≤ Real.log q :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero))
      (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level))
  have hm := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx.le (-9 / 16 : ℝ))
  dsimp only [generalTwoPoleGammaUpper, twoPolePrimeTrivialUpper]
  rw [hD]
  nlinarith only [hC, hlog, hm]

/-- For any nonprincipal character under GRH, positive character-free separation
excludes value one at all primes through the cutoff. Insert the level-only upper
budget into the general-character contradiction. This avoids checking a separate
scalar condition for every character. -/
theorem prime_trivial_false_of_twoPolePrimeTrivialSeparation {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < twoPolePrimeTrivialSeparation q S x) :
    ¬(∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro ht
  have hU := generalTwoPoleUpper_le_of_all_prime_trivial χ (zero_lt_one.trans_le hx) S hS ht
  have hg : 0 < generalTwoPoleGammaSeparation χ S x := by
    dsimp only [generalTwoPoleGammaSeparation, twoPolePrimeTrivialSeparation] at *
    linarith only [hU, hgap]
  exact gamma_prime_trivial_false_generalTwoPole χ hne hGRH hx S hS hg (fun p hp _ hb ↦ ht p hp hb)

end PseudoPrime.LLS
