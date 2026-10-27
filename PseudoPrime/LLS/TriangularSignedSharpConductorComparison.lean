/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularSignedAverage
public import PseudoPrime.LLS.TriangularSignedGammaBounds
public import PseudoPrime.LLS.TriangularSignedComparison
public import PseudoPrime.LLS.TriangularConductorComparison

/-! # Triangular conductor comparison with arithmetic cancellation -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH and containment of eligible primes through X, the alpha-18
principal finite sum is bounded by the exact conductor logarithm sum, fixed
cost 5964 per nonprincipal character, and two level-one arithmetic sums.
The nonprincipal scale-one terms are removed using primitive aggregate
positivity. This eliminates the old absolute zero-mass constant from averaging. -/
theorem triangular18_principal_sum_le_signed_sharp_conductor_explicit {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 1 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (H.index : ℝ) * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re) ≤
      (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re +
        2 * (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 n).re +
        (36 + 4000000000000 * x ^ (-9 / 16 : ℝ)) * subgroupConductorLogSum H +
        ((H.index : ℝ) - 1) * (5964 + 4000000000000 * 284 * x ^ (-9 / 16 : ℝ)) := by
  classical
  let _ := Classical.propDecidable
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let S := NumberTheory.subgroupAnnihilator H
  let P := (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re
  let A := fun χ : S ↦
    (∑' n : ℕ, K.summand χ.val.primitiveCharacter 1 n).re +
      (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 n).re
  let B := fun χ : S ↦
    36 * Real.log χ.val.conductor - A χ + 5964 +
      4000000000000 * (Real.log χ.val.conductor + 284) * x ^ (-9 / 16 : ℝ)
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
  have hb := triangular18_principal_sum_le_signed_sharp_budgets_of_noSmallPrimes H hGRH hx hsmall
  simp only [sub_sub] at hb
  change
    (H.index : ℝ) * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re) ≤
      ∑ χ : S, if χ.val = 1 then P else B χ at hb
  rw [triangular18_split_principal_budget_sum H P B] at hb
  erw [hf] at hb
  have hs :
    (∑ χ ∈ Finset.univ.erase (1 : S), B χ) =
      (36 + 4000000000000 * x ^ (-9 / 16 : ℝ)) * subgroupConductorLogSum H +
          ((H.index : ℝ) - 1) * (5964 + 4000000000000 * 284 * x ^ (-9 / 16 : ℝ)) -
        ∑ χ ∈ Finset.univ.erase (1 : S), A χ := by
    calc
      _ =
          ∑ χ ∈ Finset.univ.erase (1 : S),
            (((36 + 4000000000000 * x ^ (-9 / 16 : ℝ)) * Real.log χ.val.conductor +
                (5964 + 4000000000000 * 284 * x ^ (-9 / 16 : ℝ))) -
              A χ) :=
        Finset.sum_congr rfl
          (fun χ _ ↦ by
            dsimp only [B]; ring)
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          nsmul_eq_mul, hcard]
        unfold subgroupConductorLogSum
        congr 3
        apply Finset.sum_congr
        · apply Finset.ext
          intro χ
          simp only [Finset.mem_erase, Finset.mem_univ]
        · intro χ _
          rfl
  rw [hs] at hb
  have ha := triangular18_nonprincipal_arithmetic_pair_sum_lower H (x := 1) (by norm_num only)
  change
    -(2 : ℝ) * (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 n).re ≤
      ∑ χ ∈ Finset.univ.erase (1 : S), A χ at ha
  change (H.index : ℝ) * _ ≤ _
  linarith only [hb, ha]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Under the same hypotheses, replace both level-one sums by numerical RH
bounds. The scale-one pair costs 602600000 independently of the subgroup index.
The per-character fixed cost is 5964, with the precise scale-decaying
remainder retained. This is the numerical entry point for the improved gap. -/
theorem triangular18_principal_sum_le_signed_sharp_conductor_numeric {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 1 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
              (1 : DirichletCharacter ℂ q) x n).re) ≤
      300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) + 602600000 +
        (36 + 4000000000000 * x ^ (-9 / 16 : ℝ)) * subgroupConductorLogSum H +
        ((H.index : ℝ) - 1) * (5964 + 4000000000000 * 284 * x ^ (-9 / 16 : ℝ)) := by
  have hb := triangular18_principal_sum_le_signed_sharp_conductor_explicit H hGRH hx hsmall
  have hp := triangular18_level_one_arithmetic_upper_of_rh hGRH.riemann (zero_lt_one.trans_le hx)
  have h1 := triangular18_level_one_arithmetic_upper_of_rh hGRH.riemann (x := 1) (by norm_num only)
  simp only [Real.sqrt_one, Real.one_rpow, mul_one] at h1
  linarith only [hb, hp, h1]

end PseudoPrime.LLS.PaperStatements
