/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularQuotientCorrection
public import PseudoPrime.LLS.TriangularConductorComparison

/-! # Finite alpha-18 principal comparison and numerical witness gap -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At positive scale and nonzero level, any finite primitive arithmetic
difference has norm at most the quotient-prime geometric correction budget.
Bound the finite norm sum by the summable full correction series. -/
theorem triangular18_finite_primitive_difference_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) (s : Finset ℕ) :
    ‖(∑ n ∈ s, (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ x n) -
          (∑ n ∈ s,
            (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ.primitiveCharacter
              x n)‖ ≤
      ∑ p ∈ (q / χ.conductor).primeFactors, 36 * (Real.log p / (Real.sqrt p - 1)) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hs :=
    ((MellinKernel.summable_summand K χ hx).sub
        (MellinKernel.summable_summand K χ.primitiveCharacter hx)).norm
  have ht :=
    Summable.sum_le_tsum s
      (fun n _ ↦ norm_nonneg (K.summand χ x n - K.summand χ.primitiveCharacter x n)) hs
  rw [← Finset.sum_sub_distrib]
  exact
    (norm_sum_le _ _).trans (ht.trans (triangular18_primitive_correction_norm_sum_le_precise χ hx))

/-- Under RH at positive scale and nonzero level, the finite principal sum
through x has the level-one cutoff lower bound minus the exact level-prime budget.
Transfer the level-one lower bound through its primitive source and nonnegative terms. -/
theorem triangular18_finite_principal_lower_of_rh {q : ℕ} [NeZero q] (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
        (∑ p ∈ q.primeFactors, 36 * (Real.log p / (Real.sqrt p - 1))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ q) x n).re := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hsub : Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊x⌋₊ ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    intro n hn
    have hm := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt hm.1), hm.2⟩
  have hb :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := fun n ↦
      (K.summand (1 : DirichletCharacter ℂ 1) x n).re) hsub
      (fun n _ _ ↦ MellinKernel.principal_summand_re_nonneg (q := 1) K hx n)
  have hl := (triangular18_level_one_cutoff_sum_lower_of_rh hRH hx).trans hb
  have hc :=
    triangular18_finite_primitive_difference_norm_le (1 : DirichletCharacter ℂ q) hx
      (Finset.Icc 1 ⌊x⌋₊)
  rw [Finset.sum_congr rfl (fun n _ ↦ MellinKernel.principal_primitive_summand_eq_level_one K x n),
    DirichletCharacter.conductor_one, Nat.div_one] at hc
  have hr := (Complex.abs_re_le_norm _).trans hc
  change
    |Complex.reCLM
          ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, K.summand (1 : DirichletCharacter ℂ q) x n) -
            (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, K.summand (1 : DirichletCharacter ℂ 1) x n))| ≤
      _ at hr
  rw [map_sub, map_sum, map_sum] at hr
  change
    |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re) -
          (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re)| ≤
      _ at hr
  have hd := (abs_le.mp hr).1
  linarith only [hl, hd]

/-- Under GRH and no eligible outside prime through x >= 1, the index times
the explicit finite-principal lower budget is at most the numerical primitive
average upper budget. Combine both proved finite-sum inequalities. -/
theorem triangular18_finite_principal_comparison {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → residueInSubgroup q H p) :
    (H.index : ℝ) *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          (∑ p ∈ q.primeFactors, 36 * (Real.log p / (Real.sqrt p - 1)))) ≤
      300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) +
        (36 + 4000000000000 * x ^ (-9 / 16 : ℝ)) * subgroupConductorLogSum H +
        ((H.index : ℝ) - 1) *
          (1350000000000000 + 55000 + 4000000000000 * 284 * x ^ (-9 / 16 : ℝ)) := by
  have hl :=
    mul_le_mul_of_nonneg_left
      (triangular18_finite_principal_lower_of_rh (q := q) hGRH.riemann (zero_lt_one.trans_le hx))
      (Nat.cast_nonneg H.index)
  exact hl.trans (triangular18_principal_sum_le_conductor_sum_numeric H hGRH hx hsmall)

/-- Under GRH, nonzero level and x >= 1, a strict numerical alpha-18 gap
implies an eligible prime outside the subgroup through x.
Contradict the explicit finite comparison; the gap remains a separate numerical condition. -/
theorem exists_prime_outside_subgroup_of_triangular18_gap {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 ≤ x)
    (hgap :
      300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) +
          (36 + 4000000000000 * x ^ (-9 / 16 : ℝ)) * subgroupConductorLogSum H +
          ((H.index : ℝ) - 1) *
            (1350000000000000 + 55000 + 4000000000000 * 284 * x ^ (-9 / 16 : ℝ)) <
        (H.index : ℝ) *
          (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
            (∑ p ∈ q.primeFactors, 36 * (Real.log p / (Real.sqrt p - 1))))) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ x ∧ ¬residueInSubgroup q H p := by
  classical
  by_contra hnone
  have hsmall (p : ℕ) (hp : p.Prime) (hd : ¬p ∣ q) (hle : (p : ℝ) ≤ x) :
    residueInSubgroup q H p := by
    by_contra hout
    exact hnone ⟨p, hp, hd, hle, hout⟩
  exact (not_le_of_gt hgap) (triangular18_finite_principal_comparison H hGRH hx hsmall)

/-- For positive scale x <= 40000, the current cutoff lower budget with
error coefficient 1456 is nonpositive. Bound x^(1/4) by 15 and the cutoff
mass by 72. This identifies a quantitative obstacle to using this budget
at small scales, without making a claim about the actual arithmetic sum. -/
theorem triangular18_cutoff_lower_budget_nonpos_of_le_40000 {x : ℝ} (hx : 0 < x)
    (hsmall : x ≤ 40000) :
    Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) ≤ 0 := by
  have hb : x ≤ (15 : ℝ) ^ (4 : ℕ) :=
    hsmall.trans (by norm_num only : (40000 : ℝ) ≤ (15 : ℝ) ^ (4 : ℕ))
  have hq := Real.rpow_le_rpow hx.le hb (by norm_num only : (0 : ℝ) ≤ 1 / 4)
  rw [← Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 15) 4 (1 / 4)] at hq
  norm_num only [Real.rpow_one] at hq
  have he := Real.rpow_mul hx.le (1 / 4) 2
  norm_num only [Real.rpow_two] at he
  have hs : Real.sqrt x = (x ^ (1 / 4 : ℝ)) ^ 2 := by
    rw [Real.sqrt_eq_rpow]
    exact he
  have hp := Real.rpow_nonneg hx.le (1 / 4)
  have hm := mul_le_mul_of_nonneg_right hq hp
  have hE : Real.exp (-18 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num only)
  have hM : 68 + 4 * Real.exp (-18 : ℝ) ≤ 72 := by linarith only [hE]
  have ht := mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg x)
  rw [hs] at ht
  rw [hs]
  nlinarith only [ht, hm, hp]

end PseudoPrime.LLS.PaperStatements
