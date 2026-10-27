/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularLogarithmicCorrection
public import PseudoPrime.LLS.TriangularPrimitiveRemainderBounds
public import PseudoPrime.LLS.MellinKernelPrimitiveSupport
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CommonFactorPrimePowerReindex

/-! # Precise alpha-18 quotient corrections and nonprincipal bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive scale at a nonzero level, correction norms on a prime's
positive powers sum to at most 36 log p/(sqrt p-1). Retain the exact geometric budget. -/
theorem triangular18_prime_power_correction_norm_sum_le_precise {q p : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) (hp : p.Prime) :
    (∑' k : ℕ,
        ‖(triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ x (p ^ (k + 1)) -
            (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ.primitiveCharacter
              x (p ^ (k + 1))‖) ≤
      36 * (Real.log p / (Real.sqrt p - 1)) := by
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
  exact h

/-- For positive scale at a nonzero level, the correction norm sum is bounded
by the geometric budgets of primes dividing the level-to-conductor quotient.
Reindex precisely on quotient nonunits, rather than all original-level primes. -/
theorem triangular18_primitive_correction_norm_sum_le_precise {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ,
        ‖(triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ x n -
            (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ.primitiveCharacter
              x n‖) ≤
      ∑ p ∈ (q / χ.conductor).primeFactors, 36 * (Real.log p / (Real.sqrt p - 1)) := by
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
  have hunit (n : ℕ) (hn : Nat.Coprime n (q / χ.conductor)) : f n = 0 := by
    dsimp only [f]
    rw [MellinKernel.summand_eq_primitive_of_coprime_quotient K χ x hn, sub_self, norm_zero]
  have he :=
    AnalyticNumberTheory.Arithmetic.tsum_common_factor_eq_sum_prime_powers f
      (Nat.ne_of_gt
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level)
          (Nat.pos_of_ne_zero χ.conductor_ne_zero)))
      hs hprime hunit
  change (∑' n : ℕ, f n) ≤ _
  rw [he]
  have hb :=
    Finset.sum_le_sum
      (fun p (hp : p ∈ (q / χ.conductor).primeFactors) ↦
        triangular18_prime_power_correction_norm_sum_le_precise χ hx
          (Nat.prime_of_mem_primeFactors hp))
  exact hb

/-- For positive scale at a nonzero level, the arithmetic series difference
from its primitive source has norm bounded by the quotient prime budgets.
Apply the norm triangle inequality to the summable correction. -/
theorem triangular18_primitive_arithmetic_difference_norm_le_precise {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    ‖(∑' n : ℕ, (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ x n) -
          (∑' n : ℕ,
            (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ.primitiveCharacter
              x n)‖ ≤
      ∑ p ∈ (q / χ.conductor).primeFactors, 36 * (Real.log p / (Real.sqrt p - 1)) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h1 := MellinKernel.summable_summand K χ hx
  have h2 := MellinKernel.summable_summand K χ.primitiveCharacter hx
  rw [← h1.tsum_sub h2]
  exact
    (norm_tsum_le_tsum_norm (h1.sub h2).norm).trans
      (triangular18_primitive_correction_norm_sum_le_precise χ hx)

/-- Under GRH, for a nonprincipal character at nonzero level and x >= 1,
the actual arithmetic sum is bounded by the primitive conductor estimate
plus the precise quotient prime correction. Derive all primitive hypotheses
from nonprincipality and keep the scale-decaying remainder for comparison. -/
theorem triangular18_nonprincipal_arithmetic_norm_le_precise {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    ‖∑' n : ℕ, (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ x n‖ ≤
      36 * Real.log χ.conductor + 1350000000000000 +
        (4000000000000 * (Real.log χ.conductor + 284) * x ^ (-9 / 16 : ℝ) + 55000) +
        ∑ p ∈ (q / χ.conductor).primeFactors, 36 * (Real.log p / (Real.sqrt p - 1)) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hn := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hq := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hp :=
    triangular18_primitive_arithmetic_norm_le_explicit ((by norm_num only : 2 ≤ 3).trans hq) hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hn (inv_ne_one.mpr hn) hx
  have hc :=
    triangular18_primitive_arithmetic_difference_norm_le_precise χ (zero_lt_one.trans_le hx)
  let S := ∑' n : ℕ, K.summand χ x n
  let P := ∑' n : ℕ, K.summand χ.primitiveCharacter x n
  have he : S = (S - P) + P := by ring
  have hb := (norm_add_le (S - P) P).trans (add_le_add hc hp)
  change ‖S‖ ≤ _
  rw [he]
  exact hb.trans_eq (by ring)

/-- Under RH at nonzero level and positive scale, the principal arithmetic
sum has the level-one cutoff lower bound minus the exact prime geometric budgets.
The principal conductor is one; use the primitive series identity and real-part bound. -/
theorem triangular18_principal_arithmetic_lower_of_rh_precise {q : ℕ} [NeZero q]
    (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
        (∑ p ∈ q.primeFactors, 36 * (Real.log p / (Real.sqrt p - 1))) ≤
      (∑' n : ℕ,
          (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ q) x n).re := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have he :=
    triangular18_primitive_arithmetic_difference_norm_le_precise (1 : DirichletCharacter ℂ q) hx
  rw [tsum_congr (MellinKernel.principal_primitive_summand_eq_level_one K x),
    DirichletCharacter.conductor_one, Nat.div_one] at he
  have hr := (Complex.abs_re_le_norm _).trans he
  rw [Complex.sub_re] at hr
  have hl := (abs_le.mp hr).1
  have hb := triangular18_level_one_arithmetic_lower_of_rh hRH hx
  linarith only [hl, hb]

end PseudoPrime.LLS.PaperStatements
