/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularKernel
public import PseudoPrime.LLS.TriangularCutoffBounds
public import PseudoPrime.LLS.MellinKernelBounds
public import PseudoPrime.LLS.MellinKernelCharacterBounds

/-! # Finite alpha-18 principal cutoff identities -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At positive scale and nonzero index, the level-one triangular summand
is the real Mangoldt term times its profile. Evaluate the inverse transform. -/
theorem triangular18_level_one_term {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand (1 : DirichletCharacter ℂ 1)
          x n).re =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * triangularKernelProfile 18 (n / x) := by
  have hp : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx
  simp only [MellinKernel.summand, ite_eq_right hn,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [triangular_transform_of_function _ (by norm_num only : (0 : ℝ) < 18) rfl hp]

/-- On the positive cutoff interval, the level-one summand equals the
rescaled linear weight divided by sqrt x. Evaluate the profile and cancel square roots. -/
theorem triangular18_level_one_cutoff_term {x : ℝ} (hx : 0 < x) {n : ℕ}
    (hl : Real.exp (-36) * x ≤ (n : ℝ)) (hr : (n : ℝ) ≤ x) :
    ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand (1 : DirichletCharacter ℂ 1)
          x n).re =
      ((36 + Real.log ((n : ℝ) / x)) * ((n : ℝ) / x) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt n /
        Real.sqrt x := by
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hx) hl
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.cast_pos.mp hnpos)
  have hu := div_pos hnpos hx
  have hule : (n : ℝ) / x ≤ 1 := (div_le_one hx).mpr hr
  have hul : Real.exp (-36) ≤ (n : ℝ) / x := (le_div_iff₀ hx).mpr hl
  have hlog : -36 ≤ Real.log ((n : ℝ) / x) := by
    have h := Real.log_le_log (Real.exp_pos (-36)) hul
    simpa only [Real.log_exp] using h
  have hlog0 := Real.log_nonpos hu.le hule
  have hprof : triangularKernelProfile 18 ((n : ℝ) / x) = 36 + Real.log ((n : ℝ) / x) := by
    unfold triangularKernelProfile
    rw [abs_of_nonpos hlog0, sub_neg_eq_add]
    norm_num only
    exact max_eq_right (by linarith only [hlog])
  rw [triangular18_level_one_term hx hn, hprof, neg_div, Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow,
    Real.sqrt_div hnpos.le]
  field_simp [((Real.sqrt_pos.mpr hnpos).ne'), ((Real.sqrt_pos.mpr hx).ne')]

/-- The finite level-one cutoff sum equals the normalized Mangoldt cutoff sum.
Apply the term identity using the floor endpoint inequalities. -/
theorem triangular18_level_one_cutoff_sum {x : ℝ} (hx : 0 < x) :
    (∑ k ∈ Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊x⌋₊,
        ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) x k).re) =
      (∑ k ∈ Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊x⌋₊,
          ((36 + Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
            ArithmeticFunction.vonMangoldt k) /
        Real.sqrt x := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hm := Finset.mem_Ioc.mp hk
  have ha := mul_pos (Real.exp_pos (-36)) hx
  have hl := (Nat.floor_lt ha.le).mp hm.1
  have hr : (k : ℝ) ≤ x := (Nat.cast_le.mpr hm.2).trans (Nat.floor_le hx.le)
  exact triangular18_level_one_cutoff_term hx hl.le hr

/-- Under RH the actual finite level-one triangular kernel cutoff sum has
lower bound sqrt x times its cutoff mass minus 1456 x^(1/4).
Transfer the normalized Mangoldt bound through the finite-sum identity. -/
theorem triangular18_level_one_cutoff_sum_lower_of_rh (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 0 < x) :
    Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) ≤
      ∑ k ∈ Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊x⌋₊,
        ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) x k).re := by
  rw [triangular18_level_one_cutoff_sum hx]
  exact triangular18_cutoff_mangoldt_normalized_lower_of_rh hRH hx

/-- Under RH the full level-one triangular arithmetic sum is bounded below
by its explicit cutoff mass minus the normalized truncation error.
Summability and nonnegative principal terms transfer the finite cutoff lower bound. -/
theorem triangular18_level_one_arithmetic_lower_of_rh (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 0 < x) :
    Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) ≤
      (∑' n : ℕ,
          (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) x n).re := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hs := MellinKernel.summable_summand K (1 : DirichletCharacter ℂ 1) hx
  have hr := Complex.hasSum_re hs.hasSum
  have hb :=
    Summable.sum_le_tsum (Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊x⌋₊)
      (fun n _ ↦ MellinKernel.principal_summand_re_nonneg K hx n) hr.summable
  rw [hr.tsum_eq] at hb
  exact (triangular18_level_one_cutoff_sum_lower_of_rh hRH hx).trans hb

end PseudoPrime.LLS.PaperStatements
