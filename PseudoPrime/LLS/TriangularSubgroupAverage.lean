/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularPrimitiveRemainderBounds
public import PseudoPrime.LLS.MellinKernelPrimitiveAverage
public import PseudoPrime.NumberTheory.DirichletCharacterSmallLevels

/-! # Explicit alpha-18 primitive subgroup averaging -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, if every eligible prime up to X lies in H, the subgroup index
times the finite alpha-18 principal sum is bounded by the primitive conductor
budgets, with the principal primitive series left exact. Signed aggregate
positivity removes absolute level-change corrections before applying the analytic bounds. -/
theorem triangular18_principal_sum_le_primitive_budgets_of_noSmallPrimes {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 1 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    letI := Classical.propDecidable;
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
              (1 : DirichletCharacter ℂ q) x n).re ≤
      ∑ χ : NumberTheory.subgroupAnnihilator H,
        if χ.val = 1 then
          (∑' n : ℕ,
              (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
                (1 : DirichletCharacter ℂ 1) x n).re
        else
          36 * Real.log χ.val.conductor + 1350000000000000 +
            (4000000000000 * (Real.log χ.val.conductor + 284) * x ^ (-9 / 16 : ℝ) + 55000) := by
  classical
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hc :=
    MellinKernel.principal_sum_le_primitive_average_of_noSmallPrimes K H (zero_lt_one.trans_le hx)
      hsmall
  apply hc.trans
  apply Finset.sum_le_sum
  intro χ _
  by_cases hn : χ.val = 1
  · rw [ite_eq_left hn, hn, tsum_congr (MellinKernel.principal_primitive_summand_eq_level_one K x)]
  · rw [ite_eq_right hn]
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    have hp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ.val hn
    have hq := NumberTheory.three_le_conductor_of_ne_one χ.val hn
    have hb :=
      triangular18_primitive_arithmetic_norm_le_explicit ((by norm_num only : 2 ≤ 3).trans hq) hGRH
        (DirichletCharacter.primitiveCharacter_isPrimitive χ.val) hp (inv_ne_one.mpr hp) hx
    exact (Complex.re_le_norm _).trans hb

/-- An annihilator budget sum splits into its unique principal term and
the sum over nonprincipal characters. Use the subgroup identity and finite sum splitting. -/
theorem triangular18_split_principal_budget_sum {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (P : ℝ)
    (R : NumberTheory.subgroupAnnihilator H → ℝ) :
    letI := Classical.propDecidable;
    (∑ χ : NumberTheory.subgroupAnnihilator H, if χ.val = 1 then P else R χ) =
      P +
        ∑ χ ∈ Finset.univ.filter (fun χ : NumberTheory.subgroupAnnihilator H ↦ χ.val ≠ 1), R χ := by
  classical
  let S := NumberTheory.subgroupAnnihilator H
  have he (χ : S) : χ.val = 1 ↔ χ = 1 := by
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  have hi (χ : S) :
    (if χ.val = 1 then P else R χ) = (if χ = 1 then P else 0) + (if χ.val ≠ 1 then R χ else 0) := by
    by_cases h : χ.val = 1
    · rw [ite_eq_left h, ite_eq_left ((he χ).mp h), ite_eq_right (not_not.mpr h), add_zero]
    · rw [ite_eq_right h, ite_eq_right (fun hc ↦ h ((he χ).mpr hc)), ite_eq_left h, zero_add]
  rw [Finset.sum_congr rfl (fun χ _ ↦ hi χ), Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_filter, ite_eq_left (Finset.mem_univ (1 : S))]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  by_cases h : χ.val ≠ 1
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

/-- Under GRH, if every eligible prime up to X lies in H and x >= 1,
the index times the finite principal sum is at most the level-one series
plus explicit nonprincipal conductor budgets. This is the alpha-18 finite
comparison interface for subsequent conductor aggregation and numerical refinement. -/
theorem triangular18_principal_sum_le_conductor_budgets_of_noSmallPrimes {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 1 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    letI := Classical.propDecidable;
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
              (1 : DirichletCharacter ℂ q) x n).re ≤
      (∑' n : ℕ,
            (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
              (1 : DirichletCharacter ℂ 1) x n).re +
        ∑ χ ∈ Finset.univ.filter (fun χ : NumberTheory.subgroupAnnihilator H ↦ χ.val ≠ 1),
          (36 * Real.log χ.val.conductor + 1350000000000000 +
            (4000000000000 * (Real.log χ.val.conductor + 284) * x ^ (-9 / 16 : ℝ) + 55000)) := by
  classical
  have h := triangular18_principal_sum_le_primitive_budgets_of_noSmallPrimes H hGRH hx hsmall
  rw [triangular18_split_principal_budget_sum] at h
  exact h

end PseudoPrime.LLS.PaperStatements
