/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularPrincipalCutoff
public import PseudoPrime.LLS.TriangularExplicitNumerics
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TriangularUpperMangoldtBounds

/-! # Explicit full alpha-18 principal-series upper bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- On the upper support interval at positive scale, a level-one triangular
term equals its upper logarithmic weight divided by sqrt x. Evaluate the profile. -/
theorem triangular18_level_one_upper_term {x : ℝ} (hx : 0 < x) {n : ℕ} (hl : x ≤ (n : ℝ))
    (hr : (n : ℝ) ≤ Real.exp 36 * x) :
    ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand (1 : DirichletCharacter ℂ 1)
          x n).re =
      ((36 - Real.log ((n : ℝ) / x)) * ((n : ℝ) / x) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt n /
        Real.sqrt x := by
  have hnpos : 0 < (n : ℝ) := hx.trans_le hl
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.cast_pos.mp hnpos)
  have hu := div_pos hnpos hx
  have hul : 1 ≤ (n : ℝ) / x := (one_le_div hx).mpr hl
  have hur : (n : ℝ) / x ≤ Real.exp 36 := (div_le_iff₀ hx).mpr hr
  have hlog := Real.log_le_log hu hur
  rw [Real.log_exp] at hlog
  have hlog0 := Real.log_nonneg hul
  have hprof : triangularKernelProfile 18 ((n : ℝ) / x) = 36 - Real.log ((n : ℝ) / x) := by
    unfold triangularKernelProfile
    rw [abs_of_nonneg hlog0]
    norm_num only
    exact max_eq_right (by linarith only [hlog])
  rw [triangular18_level_one_term hx hn, hprof, neg_div, Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow,
    Real.sqrt_div hnpos.le]
  field_simp [((Real.sqrt_pos.mpr hnpos).ne'), ((Real.sqrt_pos.mpr hx).ne')]

/-- The finite upper-support kernel sum equals the normalized upper Mangoldt sum.
Apply the term identity with the floor endpoint inequalities. -/
theorem triangular18_level_one_upper_sum {x : ℝ} (hx : 0 < x) :
    (∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp 36 * x⌋₊,
        ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) x k).re) =
      (∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp 36 * x⌋₊,
          ((36 - Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
            ArithmeticFunction.vonMangoldt k) /
        Real.sqrt x := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hm := Finset.mem_Ioc.mp hk
  have hl := (Nat.floor_lt hx.le).mp hm.1
  have hr : (k : ℝ) ≤ Real.exp 36 * x :=
    (Nat.cast_le.mpr hm.2).trans (Nat.floor_le (mul_pos (Real.exp_pos _) hx).le)
  exact triangular18_level_one_upper_term hx hl.le hr

/-- At a positive argument outside the closed exponential support, the
alpha-18 profile vanishes. Logarithmic monotonicity controls the absolute value. -/
theorem triangular18_profile_zero_outside_support {u : ℝ} (hu : 0 < u)
    (hout : u ≤ Real.exp (-36) ∨ Real.exp 36 ≤ u) : triangularKernelProfile 18 u = 0 := by
  unfold triangularKernelProfile
  rcases hout with hl | hr
  · have hlog := Real.log_le_log hu hl
    rw [Real.log_exp] at hlog
    have hn : Real.log u ≤ 0 := by linarith only [hlog]
    rw [abs_of_nonpos hn]
    norm_num only
    exact max_eq_left (by linarith only [hlog])
  · have hlog := Real.log_le_log (Real.exp_pos 36) hr
    rw [Real.log_exp] at hlog
    have hn : 0 ≤ Real.log u := by linarith only [hlog]
    rw [abs_of_nonneg hn]
    norm_num only
    exact max_eq_left (by linarith only [hlog])

/-- At positive scale, a level-one term outside the finite support interval
vanishes. Include the zero index and the two support boundaries. -/
theorem triangular18_level_one_term_zero_outside_support {x : ℝ} (hx : 0 < x) {n : ℕ}
    (hout : n ∉ Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊Real.exp 36 * x⌋₊) :
    ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand (1 : DirichletCharacter ℂ 1)
          x n).re =
      0 := by
  by_cases hn : n = 0
  · subst n
    simp only [MellinKernel.summand, ite_true, Complex.zero_re]
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hu := div_pos hnpos hx
    have he : (n : ℝ) / x ≤ Real.exp (-36) ∨ Real.exp 36 ≤ (n : ℝ) / x := by
      by_cases hl : n ≤ ⌊Real.exp (-36) * x⌋₊
      · exact
          Or.inl
            ((div_le_iff₀ hx).mpr
              ((Nat.cast_le.mpr hl).trans (Nat.floor_le (mul_pos (Real.exp_pos _) hx).le)))
      · have hnl := lt_of_not_ge hl
        have hnr : ⌊Real.exp 36 * x⌋₊ < n :=
          lt_of_not_ge (fun hr ↦ hout (Finset.mem_Ioc.mpr ⟨hnl, hr⟩))
        have ht := (Nat.floor_lt (mul_pos (Real.exp_pos 36) hx).le).mp hnr
        exact Or.inr ((le_div_iff₀ hx).mpr ht.le)
    rw [triangular18_level_one_term hx hn, triangular18_profile_zero_outside_support hu he,
      mul_zero]

/-- At positive scale, the whole level-one principal series equals the sum
of the normalized lower and upper finite Mangoldt sums. Use support vanishing,
absolute summability and the adjacent interval sum identity. -/
theorem triangular18_level_one_arithmetic_eq_split {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ,
          (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) x n).re =
      (∑ k ∈ Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊x⌋₊,
            ((36 + Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
              ArithmeticFunction.vonMangoldt k) /
          Real.sqrt x +
        (∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp 36 * x⌋₊,
            ((36 - Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
              ArithmeticFunction.vonMangoldt k) /
          Real.sqrt x := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hr :=
    Complex.hasSum_re (MellinKernel.summable_summand K (1 : DirichletCharacter ℂ 1) hx).hasSum
  have he :
    (∑' n : ℕ, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) =
      ∑ n ∈ Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊Real.exp 36 * x⌋₊,
        (K.summand (1 : DirichletCharacter ℂ 1) x n).re :=
    tsum_eq_sum (fun n hn ↦ triangular18_level_one_term_zero_outside_support hx hn)
  have ha : Real.exp (-36) * x ≤ x :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by norm_num only)) hx.le).trans_eq
      (one_mul x)
  have hb : x ≤ Real.exp 36 * x :=
    (one_mul x).symm.trans_le
      (mul_le_mul_of_nonneg_right (Real.one_le_exp_iff.mpr (by norm_num only)) hx.le)
  change (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re = _
  rw [← hr.tsum_eq, he, ←
    Finset.sum_Ioc_consecutive (fun n ↦ (K.summand (1 : DirichletCharacter ℂ 1) x n).re)
      (Nat.floor_le_floor ha) (Nat.floor_le_floor hb),
    triangular18_level_one_cutoff_sum hx, triangular18_level_one_upper_sum hx]

/-- Under RH, the whole level-one principal series is bounded by the exact
full mass times sqrt x and an explicit x^(1/4) error. Combine both finite
support bounds and normalize by the positive square root. -/
theorem triangular18_level_one_arithmetic_upper_precise_of_rh (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 0 < x) :
    (∑' n : ℕ,
          (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) x n).re ≤
      Real.sqrt x * (4 * Real.exp 18 + 4 * Real.exp (-18) - 8) +
        13 * (12 * Real.exp 9 + 64) * x ^ (1 / 4 : ℝ) := by
  have hl := triangular18_cutoff_mangoldt_error_le_of_rh hRH hx
  rw [Analysis.triangular18_cutoff_abel_main_term hx] at hl
  have hl' := (abs_le.mp hl).2
  have hu :=
    Analysis.triangular18_upper_mangoldt_sum_le hx (fun t ht ↦ psi_error_le_thirteen hRH ht)
  have hs := Real.sqrt_pos.mpr hx
  have hp : x ^ (1 / 4 : ℝ) * Real.sqrt x = x ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num only
  have he :
    (Real.sqrt x * (4 * Real.exp 18 + 4 * Real.exp (-18) - 8) +
          13 * (12 * Real.exp 9 + 64) * x ^ (1 / 4 : ℝ)) *
        Real.sqrt x =
      x * (4 * Real.exp 18 + 4 * Real.exp (-18) - 8) +
        13 * (12 * Real.exp 9 + 64) * x ^ (3 / 4 : ℝ) := by
    calc
      _ =
          (Real.sqrt x) ^ 2 * (4 * Real.exp 18 + 4 * Real.exp (-18) - 8) +
            13 * (12 * Real.exp 9 + 64) * (x ^ (1 / 4 : ℝ) * Real.sqrt x) :=
        by ring
      _ = _ := by rw [Real.sq_sqrt hx.le, hp]
  rw [triangular18_level_one_arithmetic_eq_split hx, ← add_div]
  apply (div_le_iff₀ hs).mpr
  rw [he]
  linarith only [hl', hu]

/-- The exact full alpha-18 mass equals its half-point value.
Expand the exponential square and cancel the reciprocal product. -/
theorem triangular18_full_mass_eq_half_value :
    4 * Real.exp 18 + 4 * Real.exp (-18) - 8 = 4 * (Real.exp 9 - Real.exp (-9)) ^ 2 := by
  have hp : Real.exp 9 ^ 2 = Real.exp 18 := by
    rw [pow_two, ← Real.exp_add]
    norm_num only
  have hm : Real.exp (-9) ^ 2 = Real.exp (-18) := by
    rw [pow_two, ← Real.exp_add]
    norm_num only
  have hz : Real.exp 9 * Real.exp (-9) = 1 := by
    rw [← Real.exp_add]
    norm_num only [Real.exp_zero]
  nlinarith only [hp, hm, hz]

/-- The full principal error coefficient is at most 1300000.
Bound exp 9 using the certified exp 1 upper bound and rational ninth power. -/
theorem triangular18_full_error_budget_le : 13 * (12 * Real.exp 9 + 64) ≤ (1300000 : ℝ) := by
  have he : Real.exp 1 < (68 / 25 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num only)
  have hp := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by decide : (9 : ℕ) ≠ 0)
  have hn := Real.exp_nat_mul 1 9
  norm_num only at hn
  rw [← hn] at hp
  have hnum : 13 * (12 * (68 / 25 : ℝ) ^ (9 : ℕ) + 64) < 1300000 := by norm_num only
  linarith only [hp, hnum]

/-- Under RH at positive scale, the whole alpha-18 level-one principal
series is at most 300000000 sqrt x plus 1300000 x^(1/4).
Use the exact full-series bound and the certified numerical budgets. -/
theorem triangular18_level_one_arithmetic_upper_of_rh (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 0 < x) :
    (∑' n : ℕ,
          (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) x n).re ≤
      300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) := by
  have h := triangular18_level_one_arithmetic_upper_precise_of_rh hRH hx
  rw [triangular18_full_mass_eq_half_value] at h
  have hm := mul_le_mul_of_nonneg_left triangular18_half_value_lt.le (Real.sqrt_nonneg x)
  have he :=
    mul_le_mul_of_nonneg_right triangular18_full_error_budget_le (Real.rpow_nonneg hx.le (1 / 4))
  exact h.trans (by nlinarith only [hm, he])

end PseudoPrime.LLS.PaperStatements
