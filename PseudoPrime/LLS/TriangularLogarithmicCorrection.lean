/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularArithmeticCorrection
public import PseudoPrime.LLS.MellinKernelPrimitiveSupport
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CommonFactorPrimePowerReindex
public import PseudoPrime.Analysis.TriangularLogarithmicCorrection

/-! # Explicit logarithmic alpha-18 level corrections -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a nonzero level and positive scale, correction norms on powers of
one prime sum to at most 108 log p. Compare the summable series to its geometric majorant. -/
theorem triangular18_prime_power_correction_norm_sum_le {q p : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) (hp : p.Prime) :
    (∑' k : ℕ,
        ‖(triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ x (p ^ (k + 1)) -
            (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ.primitiveCharacter
              x (p ^ (k + 1))‖) ≤
      108 * Real.log p := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hs :=
    ((MellinKernel.summable_summand K χ hx).sub
        (MellinKernel.summable_summand K χ.primitiveCharacter hx)).norm
  have hi : Function.Injective (fun k : ℕ ↦ p ^ (k + 1)) := fun k l h ↦ (hp.pow_inj hp h).2
  have ht := (Analysis.hasSum_log_div_sqrt_prime_pow hp).mul_left 36
  have hb (k : ℕ) :
    ‖K.summand χ x (p ^ (k + 1)) - K.summand χ.primitiveCharacter x (p ^ (k + 1))‖ ≤
      36 * (Real.log p / Real.sqrt ((p : ℝ) ^ (k + 1))) := by
    have h :=
      (MellinKernel.norm_summand_sub_primitive_le K (n := p ^ (k + 1)) χ x).trans
        (triangular18_summand_norm_le χ.primitiveCharacter hx (Nat.ne_of_gt (Nat.pow_pos hp.pos)))
    simpa only [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
      ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow] using h
  have h := Summable.tsum_le_tsum hb (hs.comp_injective hi) ht.summable
  rw [ht.tsum_eq] at h
  have hl :=
    mul_le_mul_of_nonneg_left (Analysis.log_div_sqrt_prime_sub_one_le_three_log hp)
      (by norm_num only : (0 : ℝ) ≤ 36)
  exact h.trans (by nlinarith only [hl])

/-- For a nonzero level and positive scale, the sum of all primitive correction
norms is at most 108 log q. Reindex the support by level primes and positive powers. -/
theorem triangular18_primitive_correction_norm_sum_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ,
        ‖(triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ x n -
            (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ.primitiveCharacter
              x n‖) ≤
      108 * Real.log q := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let f := fun n : ℕ ↦ ‖K.summand χ x n - K.summand χ.primitiveCharacter x n‖
  have hs :=
    ((MellinKernel.summable_summand K χ hx).sub
        (MellinKernel.summable_summand K χ.primitiveCharacter hx)).norm
  have hprime (n : ℕ) (hn : ¬IsPrimePow n) : f n = 0 := by
    dsimp only [f]
    rw [MellinKernel.summand_eq_zero_of_not_primePow K χ x hn,
      MellinKernel.summand_eq_zero_of_not_primePow K χ.primitiveCharacter x hn, sub_self, norm_zero]
  have hunit (n : ℕ) (hn : Nat.Coprime n q) : f n = 0 := by
    dsimp only [f]
    rw [MellinKernel.summand_eq_primitive_of_coprime_quotient K χ x
        (Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd χ.conductor_dvd_level) hn),
      sub_self, norm_zero]
  have he :=
    AnalyticNumberTheory.Arithmetic.tsum_common_factor_eq_sum_prime_powers f (NeZero.ne q) hs hprime
      hunit
  change (∑' n : ℕ, f n) ≤ _
  rw [he]
  have hb :=
    Finset.sum_le_sum
      (fun p (hp : p ∈ q.primeFactors) ↦
        triangular18_prime_power_correction_norm_sum_le χ hx (Nat.prime_of_mem_primeFactors hp))
  have hl :=
    mul_le_mul_of_nonneg_left
      (AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log (NeZero.ne q))
      (by norm_num only : (0 : ℝ) ≤ 108)
  rw [Finset.mul_sum] at hl
  exact hb.trans hl

/-- For a nonzero level and positive scale, primitive arithmetic series differ
in norm by at most 108 log q. Summability permits subtraction and the norm sum bound. -/
theorem triangular18_primitive_arithmetic_difference_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    ‖(∑' n : ℕ, (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ x n) -
          (∑' n : ℕ,
            (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ.primitiveCharacter
              x n)‖ ≤
      108 * Real.log q := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h1 := MellinKernel.summable_summand K χ hx
  have h2 := MellinKernel.summable_summand K χ.primitiveCharacter hx
  rw [← h1.tsum_sub h2]
  exact
    (norm_tsum_le_tsum_norm (h1.sub h2).norm).trans
      (triangular18_primitive_correction_norm_sum_le χ hx)

/-- Under RH, for nonzero level and positive scale, the principal triangular
arithmetic sum is bounded below by the cutoff main term minus truncation error
and 108 log q. Transfer the level-one lower bound through its primitive source. -/
theorem triangular18_principal_arithmetic_lower_of_rh {q : ℕ} [NeZero q] (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) - 108 * Real.log q ≤
      (∑' n : ℕ,
          (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ q) x n).re := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have he := triangular18_primitive_arithmetic_difference_norm_le (1 : DirichletCharacter ℂ q) hx
  rw [tsum_congr (MellinKernel.principal_primitive_summand_eq_level_one K x)] at he
  have hr := (Complex.abs_re_le_norm _).trans he
  rw [Complex.sub_re] at hr
  have hl := (abs_le.mp hr).1
  have hb := triangular18_level_one_arithmetic_lower_of_rh hRH hx
  linarith only [hl, hb]

end PseudoPrime.LLS.PaperStatements
