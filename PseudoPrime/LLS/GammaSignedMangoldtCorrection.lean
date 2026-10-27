/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaQuadraticLocalBudget
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CommonFactorPrimePowerReindex

/-! # Signed Mangoldt correction and its local prime-power series -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The signed Mangoldt correction vanishes on original-level units and retains
the local ramp discrepancy on nonunits, normalized by sqrt(x).
It is the arithmetic form of the prime-power local series. -/
noncomputable def gammaSignedMangoldtCorrection {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ)
    (n : ℕ) : ℝ :=
  if Nat.Coprime n q then 0
  else
    ArithmeticFunction.vonMangoldt n / Real.sqrt x *
      Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter n) ((n : ℝ) / x) 1

/-- On an original-level unit index, the signed Mangoldt correction vanishes.
The conditional definition isolates the missing-prime support. -/
theorem gammaSignedMangoldtCorrection_unit {q n : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ)
    (hn : Nat.Coprime n q) : gammaSignedMangoldtCorrection χ x n = 0 :=
  ite_eq_left hn

/-- Outside prime powers, the signed Mangoldt correction is zero.
Mangoldt vanishing supplies the support required for signed reindexing. -/
theorem gammaSignedMangoldtCorrection_not_prime_pow {q n : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ)
    (hn : ¬IsPrimePow n) : gammaSignedMangoldtCorrection χ x n = 0 := by
  simp only [gammaSignedMangoldtCorrection, ArithmeticFunction.vonMangoldt_apply, ite_eq_right hn,
    zero_div, zero_mul, ite_self]

/-- On a positive power of a level prime, the Mangoldt correction equals
the log(p)/sqrt(x)-weighted local power term. Evaluate Mangoldt and character powers.
This matches the arithmetic correction with the previously bounded local series. -/
theorem gammaSignedMangoldtCorrection_prime_power {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ)
    (z : q.primeFactors × ℕ) :
    gammaSignedMangoldtCorrection χ x
        (AnalyticNumberTheory.Arithmetic.commonFactorPrimePowerIndex q z) =
      Real.log (z.1 : ℕ) / Real.sqrt x *
        Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter (z.1 : ℕ))
          (((z.1 : ℕ) : ℝ) ^ (z.2 + 1) / x) (z.2 + 1) := by
  have hp := Nat.mem_primeFactors.mp z.1.property
  have hc : ¬Nat.Coprime ((z.1 : ℕ) ^ (z.2 + 1)) q := fun h ↦
    (hp.1.coprime_iff_not_dvd.mp ((Nat.coprime_pow_left_iff (Nat.succ_pos z.2) _ _).mp h)) hp.2.1
  rw [AnalyticNumberTheory.Arithmetic.commonFactorPrimePowerIndex, gammaSignedMangoldtCorrection,
    ite_eq_right hc, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero z.2),
    ArithmeticFunction.vonMangoldt_apply_prime hp.1]
  simp only [Analysis.exponentialRampLocalCorrection, Nat.cast_pow, map_pow, pow_one]

/-- For a quadratic character at nonzero level and positive scale, the signed
Mangoldt correction is absolutely summable. Reindex its support into finitely many
prime-power slices and use the proved exponential local-series convergence. -/
theorem summable_gammaSignedMangoldtCorrection {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x) :
    Summable (gammaSignedMangoldtCorrection χ x) := by
  have hprim := NumberTheory.isQuadratic_primitiveCharacter χ hquad
  have hslice (p : q.primeFactors) :
    Summable
      (fun k : ℕ ↦
        ‖gammaSignedMangoldtCorrection χ x
            (AnalyticNumberTheory.Arithmetic.commonFactorPrimePowerIndex q (p, k))‖) := by
    have hp := (Nat.prime_of_mem_primeFactors p.property).one_lt
    have hs :=
      Analysis.summable_exponentialRampLocalCorrection (hprim (p : ℕ)) hx
        (fun k ↦ ((p : ℕ) : ℝ) ^ (k + 1) / x) (Analysis.prime_power_div_scale_ge_linear hp hx)
    simpa only [gammaSignedMangoldtCorrection_prime_power] using
      (hs.mul_left (Real.log (p : ℕ) / Real.sqrt x)).norm
  have hnorm :
    Summable
      (fun z : q.primeFactors × ℕ ↦
        ‖gammaSignedMangoldtCorrection χ x
            (AnalyticNumberTheory.Arithmetic.commonFactorPrimePowerIndex q z)‖) := by
    apply (summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)).mpr
    exact ⟨hslice, (hasSum_fintype _).summable⟩
  have hsupp :=
    AnalyticNumberTheory.Arithmetic.commonFactorPrimePowerIndex_support_of_vanishing
      (gammaSignedMangoldtCorrection χ x) (NeZero.ne q)
      (fun n hn ↦ gammaSignedMangoldtCorrection_not_prime_pow χ x hn)
      (fun n hn ↦ gammaSignedMangoldtCorrection_unit χ x hn)
  have hout :
    ∀ n ∉ Set.range (AnalyticNumberTheory.Arithmetic.commonFactorPrimePowerIndex q),
      gammaSignedMangoldtCorrection χ x n = 0 :=
    fun n hn ↦ of_not_not (fun h ↦ hn (hsupp h))
  exact
    (AnalyticNumberTheory.Arithmetic.commonFactorPrimePowerIndex_injective q).summable_iff
        hout |>.mp
      hnorm.of_norm

/-- For quadratic data at positive scale, the signed Mangoldt correction series
equals the actual local correction over all original-level primes.
Use absolute summability and the exact prime-power reindexing and term identities.
This connects the local budget to the arithmetic no-witness comparison. -/
theorem tsum_gammaSignedMangoldtCorrection_eq_localCorrection {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, gammaSignedMangoldtCorrection χ x n) = gammaQuadraticLocalCorrection χ x := by
  have hs := summable_gammaSignedMangoldtCorrection χ hquad hx
  rw [AnalyticNumberTheory.Arithmetic.tsum_common_factor_eq_sum_prime_powers
      (gammaSignedMangoldtCorrection χ x) (NeZero.ne q) hs
      (fun n hn ↦ gammaSignedMangoldtCorrection_not_prime_pow χ x hn)
      (fun n hn ↦ gammaSignedMangoldtCorrection_unit χ x hn)]
  dsimp only [gammaQuadraticLocalCorrection]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have he (k : ℕ) := gammaSignedMangoldtCorrection_prime_power χ x (⟨p, hp⟩, k)
  dsimp only [AnalyticNumberTheory.Arithmetic.commonFactorPrimePowerIndex] at he
  rw [tsum_congr he, tsum_mul_left]
  ring

end PseudoPrime.LLS
