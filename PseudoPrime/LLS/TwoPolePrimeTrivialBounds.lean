/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GeneralTwoPoleGammaWitness

/-! # Character-free two-pole bounds under full prime triviality -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If every prime through the cutoff has character value one, every weighted
Mangoldt defect below that cutoff vanishes, for any exclusion modulus. Reduce each
nonzero term to a prime power. This eliminates a character-dependent exclusion
budget under the universal-prime-pass contradiction used for Miller-Rabin. -/
theorem excludedCharacterDefect_eq_zero_of_all_prime_trivial {q N : ℕ} (χ : DirichletCharacter ℂ q)
    {b : ℝ} (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hw : ∀ n ∈ S, ArithmeticFunction.vonMangoldt n = 0 → w n = 0)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) : excludedCharacterDefect χ N S w = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hmem := (Finset.mem_filter.mp hn).1
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · rw [hw n hmem hΛ, mul_zero]
  · have he :=
      character_apply_one_of_ambient_mangoldt_ne_zero (N := 1) χ (fun p hp hb _ ↦ ht p hp hb)
        (hS n hmem) (Nat.coprime_one_right n) hΛ
    rw [he, Complex.one_re, sub_self, zero_mul]

end PseudoPrime.AnalyticNumberTheory.Arithmetic

namespace PseudoPrime.LLS

/-- If every small prime has character value one, each prime dividing the character
level lies above the cutoff. A nonzero character value forces coprimality.
This removes level-prime contributions from the positive part of a ramp comparison. -/
theorem level_prime_above_cutoff_of_all_prime_trivial {q p : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (ht : ∀ r : ℕ, r.Prime → (r : ℝ) ≤ b → χ r = 1) (hp : p ∈ q.primeFactors) : b < (p : ℝ) := by
  apply lt_of_not_ge
  intro hb
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hv := ht p hprime hb
  have hz : χ p ≠ 0 := by
    rw [hv]
    exact one_ne_zero
  have hc := (ZMod.isUnit_iff_coprime p q).mp (MulChar.apply_ne_zero_iff.mp hz)
  exact (hprime.coprime_iff_not_dvd.mp hc) (Nat.mem_primeFactors.mp hp).2.1

/-- At positive scale, if each level prime lies beyond the ramp cutoff, its full
local correction is nonpositive for any complex character. All positive powers
remain beyond the cutoff, where unit-disk positivity gives the sign. Sum the local
terms without replacing them by absolute-value costs. -/
theorem gammaLocalCorrection_nonpos_of_level_primes_above {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (ht : ∀ p ∈ q.primeFactors, (99 / 40 : ℝ) * x ≤ p) :
    gammaQuadraticLocalCorrection χ x ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg ?_ (Real.sqrt_nonneg x)
  apply Finset.sum_nonpos
  intro p hp
  apply
    mul_nonpos_of_nonneg_of_nonpos
      (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
  apply tsum_nonpos
  intro k
  apply
    Analysis.exponentialRampLocalCorrection_tail_nonpos_of_norm_le_one
      (χ.primitiveCharacter.norm_le_one p)
  apply (le_div_iff₀ hx).mpr
  have hpow : (p : ℝ) ≤ (p : ℝ) ^ (k + 1) := by
    exact_mod_cast Nat.le_self_pow (Nat.succ_ne_zero k) p
  exact (ht p hp).trans hpow

end PseudoPrime.LLS

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
