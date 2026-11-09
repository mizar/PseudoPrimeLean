/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ExponentialRampSummation
public import PseudoPrime.Analysis.ExponentialRampNormBounds
public import PseudoPrime.LLS.GammaQuadraticNoWitness
public import PseudoPrime.LLS.PaperStatements.GeneralGammaRampComparison

/-! # Gamma ramp no-witness comparison for general complex characters -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For every character at a nonzero level and positive scale, the signed Mangoldt
correction is absolutely summable. Reindex its support into finitely many prime-power
slices and use unit-disk local convergence. No quadratic hypothesis is required. -/
theorem summable_gammaSignedMangoldtCorrection_general {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    Summable (gammaSignedMangoldtCorrection χ x) := by
  have hslice (p : q.primeFactors) :
    Summable
      (fun k : ℕ ↦
        ‖gammaSignedMangoldtCorrection χ x
            (AnalyticNumberTheory.Arithmetic.commonFactorPrimePowerIndex q (p, k))‖) := by
    have hp := (Nat.prime_of_mem_primeFactors p.property).one_lt
    have hs :=
      Analysis.summable_expRampCorrection_of_norm_le_one (χ.primitiveCharacter.norm_le_one (p : ℕ))
        hx (fun k ↦ ((p : ℕ) : ℝ) ^ (k + 1) / x) (Analysis.prime_power_div_scale_ge_linear hp hx)
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
    AnalyticNumberTheory.Arithmetic.support_subset_common_prime_powers
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

/-- For every character at a nonzero level and positive scale, the signed Mangoldt
series equals its exact local prime-power correction. Reindex the absolutely
convergent series. The existing local-correction definition accepts general characters. -/
theorem tsum_gammaSignedCorrection_eq_local_general {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, gammaSignedMangoldtCorrection χ x n) = gammaQuadraticLocalCorrection χ x := by
  have hs := summable_gammaSignedMangoldtCorrection_general χ hx
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

namespace PseudoPrime.LLS

/-- Under eligible-prime triviality through the cutoff, the signed local term is
bounded by its original-level nonunit correction. Unit prime powers inside the
cutoff have value one; outside it the unit-disk tail is nonpositive.
This removes quadraticity from the pointwise no-witness inequality. -/
theorem signed_local_term_le_Mangoldt_correction_general {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt x *
        Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter n) ((n : ℝ) / x) 1 ≤
      gammaSignedMangoldtCorrection χ x n := by
  by_cases hcop : Nat.Coprime n q
  · rw [gammaSignedMangoldtCorrection_unit χ x hcop]
    by_cases hpow : IsPrimePow n
    · have hlocal :
        Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter n) ((n : ℝ) / x) 1 ≤ 0 := by
        by_cases hcut : (n : ℝ) ≤ (99 / 40 : ℝ) * x
        · have he := primitive_prime_power_one_of_prime_trivial χ hsmall hpow hcop hcut
          rw [he]
          exact Analysis.exponentialRampLocalCorrection_one _ _
        · have hu : 99 / 40 ≤ (n : ℝ) / x := by
            apply (le_div_iff₀ hx).mpr
            exact (lt_of_not_ge hcut).le
          exact
            Analysis.expRampCorrection_tail_nonpos_of_norm_le_one
              (χ.primitiveCharacter.norm_le_one n) hu 1
      exact
        mul_nonpos_of_nonneg_of_nonpos
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg x)) hlocal
    · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
      rw [hz, zero_div, zero_mul]
  · rw [gammaSignedMangoldtCorrection, ite_eq_right hcop]

/-- For any character under eligible-prime triviality, twice the normalized ramp
term is bounded by the principal and primitive Gamma terms and the nonunit correction.
Combine the exact identity with the signed discrepancy bound, without quadraticity. -/
theorem gamma_pair_summand_le_of_prime_trivial_general {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) (n : ℕ) :
    2 * normalizedRampMangoldtTerm x n ≤
      (PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
        (PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        gammaSignedMangoldtCorrection χ x n := by
  have h := signed_local_term_le_Mangoldt_correction_general χ hx hsmall n
  have he := PaperStatements.gamma_pair_summand_add_signed_term_general χ hx n
  dsimp only [normalizedRampMangoldtTerm]
  linarith only [h, he]

/-- At any nonzero level and positive scale, eligible-prime triviality gives the
full Gamma ramp comparison for an arbitrary complex character. Absolute convergence
justifies summation and prime-power reindexing. This supplies a general-character
consumer for paired Euler bounds and later MR subgroup comparisons. -/
theorem gamma_ramp_no_witness_comparison_general {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) :
    2 * (exponentialRampMangoldtSum x / Real.sqrt x) ≤
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
        (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        gammaQuadraticLocalCorrection χ x := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hA : Summable (fun n : ℕ ↦ 2 * normalizedRampMangoldtTerm x n) :=
    (summable_of_ne_finset_zero (normalizedRampMangoldtTerm_support hx)).mul_left 2
  have hP :=
    PaperStatements.MellinKernel.summable_summand PaperStatements.gammaMellinKernel
      (1 : DirichletCharacter ℂ 1) hx
  have hC :=
    PaperStatements.MellinKernel.summable_summand PaperStatements.gammaMellinKernel
      χ.primitiveCharacter hx
  have hE := summable_gammaSignedMangoldtCorrection_general χ hx
  have hrhs := (Complex.reCLM.summable hP).add (Complex.reCLM.summable hC) |>.add hE
  have h :=
    Summable.tsum_le_tsum (gamma_pair_summand_le_of_prime_trivial_general χ hx hsmall) hA hrhs
  erw [tsum_mul_left, normalizedRampMangoldtTerm_tsum hx,
    Summable.tsum_add ((Complex.reCLM.summable hP).add (Complex.reCLM.summable hC)) hE,
    Summable.tsum_add (Complex.reCLM.summable hP) (Complex.reCLM.summable hC), ←
    Complex.reCLM.map_tsum hP, ← Complex.reCLM.map_tsum hC,
    tsum_gammaSignedCorrection_eq_local_general χ hx] at h
  exact h

end PseudoPrime.LLS
