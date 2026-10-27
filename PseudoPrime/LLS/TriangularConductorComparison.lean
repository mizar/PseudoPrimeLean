/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularSubgroupAverage
public import PseudoPrime.LLS.ConductorSumComparison
public import PseudoPrime.LLS.TriangularPrincipalUpperBounds

/-! # Explicit alpha-18 conductor-sum aggregation -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH and the no-small-outside-prime hypothesis, the alpha-18 finite
principal sum is bounded by the exact conductor logarithm sum, the count of
nonprincipal annihilator characters, and the level-one principal series.
Aggregate the scale-decaying primitive budgets without discarding conductor savings. -/
theorem triangular18_principal_sum_le_conductor_sum_explicit {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 1 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
              (1 : DirichletCharacter ℂ q) x n).re ≤
      (∑' n : ℕ,
            (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
              (1 : DirichletCharacter ℂ 1) x n).re +
        (36 + 4000000000000 * x ^ (-9 / 16 : ℝ)) * subgroupConductorLogSum H +
        ((H.index : ℝ) - 1) *
          (1350000000000000 + 55000 + 4000000000000 * 284 * x ^ (-9 / 16 : ℝ)) := by
  classical
  let _ := Classical.propDecidable
  let S := NumberTheory.subgroupAnnihilator H
  have hf : Finset.univ.filter (fun χ : S ↦ χ.val ≠ 1) = Finset.univ.erase (1 : S) := by
    have he (χ : S) : χ.val = 1 ↔ χ = 1 := by
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    apply Finset.ext
    intro χ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
      not_congr (he χ)]
  have hcard : ((Finset.univ.erase (1 : S)).card : ℝ) = (H.index : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))),
      Nat.cast_one, NumberTheory.card_subgroupAnnihilator]
  have hb := triangular18_principal_sum_le_conductor_budgets_of_noSmallPrimes H hGRH hx hsmall
  erw [hf] at hb
  have hs :
    (∑ χ ∈ Finset.univ.erase (1 : S),
        (36 * Real.log χ.val.conductor + 1350000000000000 +
          (4000000000000 * (Real.log χ.val.conductor + 284) * x ^ (-9 / 16 : ℝ) + 55000))) =
      (36 + 4000000000000 * x ^ (-9 / 16 : ℝ)) * subgroupConductorLogSum H +
        ((H.index : ℝ) - 1) *
          (1350000000000000 + 55000 + 4000000000000 * 284 * x ^ (-9 / 16 : ℝ)) := by
    calc
      _ =
          ∑ χ ∈ Finset.univ.erase (1 : S),
            ((36 + 4000000000000 * x ^ (-9 / 16 : ℝ)) * Real.log χ.val.conductor +
              (1350000000000000 + 55000 + 4000000000000 * 284 * x ^ (-9 / 16 : ℝ))) :=
        Finset.sum_congr rfl (fun χ _ ↦ by ring)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard]
        unfold subgroupConductorLogSum
        congr 2
        apply Finset.sum_congr
        · apply Finset.ext
          intro χ
          simp only [Finset.mem_erase, Finset.mem_univ]
        · intro χ _
          rfl
  rw [hs] at hb
  simpa only [add_assoc] using hb

/-- Under GRH and the no-small-outside-prime hypothesis, the index times
the finite principal sum has an entirely numerical alpha-18 upper estimate.
Replace the remaining full principal series by its explicit RH upper bound;
retain the exact conductor cost and the scale-decaying primitive remainder. -/
theorem triangular18_principal_sum_le_conductor_sum_numeric {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 1 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
              (1 : DirichletCharacter ℂ q) x n).re ≤
      300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) +
        (36 + 4000000000000 * x ^ (-9 / 16 : ℝ)) * subgroupConductorLogSum H +
        ((H.index : ℝ) - 1) *
          (1350000000000000 + 55000 + 4000000000000 * 284 * x ^ (-9 / 16 : ℝ)) := by
  have hb := triangular18_principal_sum_le_conductor_sum_explicit H hGRH hx hsmall
  have hp := triangular18_level_one_arithmetic_upper_of_rh hGRH.riemann (zero_lt_one.trans_le hx)
  linarith only [hb, hp]

end PseudoPrime.LLS.PaperStatements
