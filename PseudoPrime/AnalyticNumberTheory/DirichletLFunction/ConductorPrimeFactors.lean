/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Conductor/quotient arithmetic and elementary prime-factor logarithm bounds

Generic elementary facts relating a Dirichlet character's level, conductor, and complementary
quotient, together with the elementary logarithm bounds on the number of distinct prime factors
of a natural number.  None of this depends on any specific `L`-function or contour construction.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The conductor of a character at a nonzero level is positive. -/
theorem conductor_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : 0 < χ.conductor :=
  χ.conductor_ne_zero.bot_lt

/-- The conductor is at most the level. -/
theorem conductor_le_level {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : χ.conductor ≤ q :=
  Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level

/-- The complementary level quotient is positive. -/
theorem quotient_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : 0 < q / χ.conductor :=
  Nat.div_pos (conductor_le_level χ) (conductor_pos χ)

/-- The complementary quotient is at most the original level. -/
theorem quotient_le_level {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : q / χ.conductor ≤ q :=
  Nat.div_le_self q χ.conductor

/-- The real logarithm of the conductor is at most the logarithm of the level. -/
theorem log_conductor_le_log_level {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Real.log χ.conductor ≤ Real.log q := by
  apply Real.log_le_log
  · exact_mod_cast conductor_pos χ
  · exact_mod_cast conductor_le_level χ

/-- The level is exactly the conductor times its complementary quotient. -/
theorem conductor_mul_quotient {q : ℕ} (χ : DirichletCharacter ℂ q) :
    χ.conductor * (q / χ.conductor) = q :=
  Nat.mul_div_cancel' χ.conductor_dvd_level

/-- The level logarithm splits exactly into conductor and complementary-quotient logarithms. -/
theorem log_level_eq_log_conductor_add_log_quotient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    Real.log q = Real.log χ.conductor + Real.log (q / χ.conductor : ℕ) := by
  have hconductor : (χ.conductor : ℝ) ≠ 0 := by exact_mod_cast (conductor_pos χ).ne'
  have hquotient : ((q / χ.conductor : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (quotient_pos χ).ne'
  rw [← Real.log_mul hconductor hquotient, ← Nat.cast_mul, conductor_mul_quotient χ]

/-- The quotient logarithm is the level logarithm minus the conductor logarithm. -/
theorem log_quotient_eq_log_level_sub_log_conductor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    Real.log (q / χ.conductor : ℕ) = Real.log q - Real.log χ.conductor := by
  rw [log_level_eq_log_conductor_add_log_quotient χ]
  rw [add_sub_cancel_left]

/-- The radical of a natural number is at least `2` to the number of its prime factors. -/
theorem two_pow_card_primeFactors_le_prod_primeFactors (m : ℕ) :
    2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod fun p hp ↦ (Nat.mem_primeFactors.mp hp).1.two_le

/-- A positive natural number is at least `2` to the number of its distinct prime factors. -/
theorem two_pow_card_primeFactors_le {m : ℕ} (hm : 0 < m) : 2 ^ m.primeFactors.card ≤ m := by
  exact
    (two_pow_card_primeFactors_le_prod_primeFactors m).trans
      (Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m))

/-- The number of distinct prime factors satisfies the elementary logarithmic bound. -/
theorem card_primeFactors_le_log_div_log_two {m : ℕ} (hm : 0 < m) :
    (m.primeFactors.card : ℝ) ≤ Real.log m / Real.log 2 := by
  have hpow : (0 : ℝ) < (2 : ℕ) ^ m.primeFactors.card := by
    exact_mod_cast Nat.pow_pos (by norm_num only : (0 : ℕ) < 2)
  have hlog : Real.log ((2 : ℕ) ^ m.primeFactors.card) ≤ Real.log m := by
    apply Real.log_le_log hpow
    exact_mod_cast two_pow_card_primeFactors_le hm
  rw [Real.log_pow] at hlog
  apply (le_div_iff₀ (Real.log_pos one_lt_two)).mpr
  norm_num only [Nat.cast_ofNat] at hlog
  simpa only [mul_comm] using hlog

/-- The complementary quotient satisfies the `ω ≤ log / log 2` estimate used in
downstream modules. -/
theorem card_primeFactors_quotient_le_log_div_log_two {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ((q / χ.conductor).primeFactors.card : ℝ) ≤ Real.log (q / χ.conductor : ℕ) / Real.log 2 :=
  card_primeFactors_le_log_div_log_two (quotient_pos χ)

/--
The affine tradeoff between a smaller conductor and the complementary prime-factor contribution.

Here `levelLog - conductorLog` bounds `log(q / conductor)`, `omega` is bounded by that difference
divided by `logTwo`, and `logWeight` represents `log X`.  The final hypothesis is exactly the
coefficient condition ensuring that moving the conductor up to the full level can only increase
the upper bound.
-/
theorem conductor_primeFactor_tradeoff
    {levelLog conductorLog omega root logWeight logTwo offset piLog : ℝ} (hlogTwo : 0 < logTwo)
    (hconductor : conductorLog ≤ levelLog) (homega : omega ≤ (levelLog - conductorLog) / logTwo)
    (hweight : logWeight ^ 2 ≤ logTwo * (2 * root + 2 + 2 * logWeight)) :
    (2 * root + 2 + logWeight) * (conductorLog / 2 + offset) +
        (conductorLog - piLog) * logWeight / 2 +
        omega * logWeight ^ 2 / 2 ≤
      (2 * root + 2 + logWeight) * (levelLog / 2 + offset) +
        (levelLog - piLog) * logWeight / 2 := by
  have homegaMul : omega * logWeight ^ 2 ≤ ((levelLog - conductorLog) / logTwo) * logWeight ^ 2 :=
    mul_le_mul_of_nonneg_right homega (sq_nonneg logWeight)
  have hweightDiv : logWeight ^ 2 / logTwo ≤ 2 * root + 2 + 2 * logWeight :=
    (div_le_iff₀ hlogTwo).mpr (by simpa only [mul_comm] using hweight)
  have hnonneg : 0 ≤ levelLog - conductorLog := sub_nonneg.mpr hconductor
  have hproduct :
    ((levelLog - conductorLog) / logTwo) * logWeight ^ 2 ≤
      (levelLog - conductorLog) * (2 * root + 2 + 2 * logWeight) := by
    calc
      ((levelLog - conductorLog) / logTwo) * logWeight ^ 2 =
          (levelLog - conductorLog) * (logWeight ^ 2 / logTwo) :=
        by rw [div_mul_eq_mul_div, mul_div_assoc]
      _ ≤ (levelLog - conductorLog) * (2 * root + 2 + 2 * logWeight) :=
        mul_le_mul_of_nonneg_left hweightDiv hnonneg
  have hhalf :
    omega * logWeight ^ 2 / 2 ≤ ((levelLog - conductorLog) * (2 * root + 2 + 2 * logWeight)) / 2 :=
    (div_le_div_of_nonneg_right homegaMul (by norm_num only : (0 : ℝ) ≤ 2)).trans
      (div_le_div_of_nonneg_right hproduct (by norm_num only : (0 : ℝ) ≤ 2))
  calc
    (2 * root + 2 + logWeight) * (conductorLog / 2 + offset) +
          (conductorLog - piLog) * logWeight / 2 +
          omega * logWeight ^ 2 / 2 ≤
        (2 * root + 2 + logWeight) * (conductorLog / 2 + offset) +
          (conductorLog - piLog) * logWeight / 2 +
          ((levelLog - conductorLog) * (2 * root + 2 + 2 * logWeight)) / 2 :=
      by
      simpa only [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hhalf
          ((2 * root + 2 + logWeight) * (conductorLog / 2 + offset) +
            (conductorLog - piLog) * logWeight / 2)
    _ = (2 * root + 2 + logWeight) * (levelLog / 2 + offset) + (levelLog - piLog) * logWeight / 2 :=
      by ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
