/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleTripleArithmetic

/-! # Finite character sums in the translated triangle window -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At positive indices the real character summand is its character value's
real part times the Mangoldt weight and the translated triangle profile. -/
theorem triangle_window_term {q n : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (hn : 0 < n) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    (K.summand χ x n).re =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * (χ (n : ZMod q)).re *
        LLS.PaperStatements.triangularKernelProfile (5 / 4) (n / x) := by
  intro K
  have hu := div_pos (Nat.cast_pos.mpr hn : (0 : ℝ) < n) hx
  have hi : (K.transform (n / x)).im = 0 := K.mellin_real _ hu
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn.ne', Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hi, mul_zero,
    LLS.PaperStatements.triangular_transform_of_function K (by norm_num only : (0 : ℝ) < 5 / 4) rfl
        hu]

/-- At center exp(v+5/2) the positive triangle profile vanishes off the
integer window from exp(v) to exp(v+5), including its left endpoint. -/
private theorem triangle_window_off {v : ℝ} {n : ℕ} (hn : 0 < n)
    (hout : n ∉ Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊) :
    LLS.PaperStatements.triangularKernelProfile (5 / 4) (n / Real.exp (v + 5 / 2)) = 0 := by
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold LLS.PaperStatements.triangularKernelProfile
  rw [Real.log_div hp.ne' (Real.exp_pos _).ne', Real.log_exp]
  apply max_eq_left
  by_cases h : n ≤ ⌊Real.exp v⌋₊
  · have hl := Real.log_le_log hp ((Nat.le_floor_iff (Real.exp_pos _).le).mp h)
    rw [Real.log_exp] at hl
    linarith only [hl, neg_le_abs (Real.log n - (v + 5 / 2))]
  · have hr :=
      (Nat.floor_lt (Real.exp_pos (v + 5)).le).mp
        (lt_of_not_ge (fun he => hout (Finset.mem_Ioc.mpr ⟨lt_of_not_ge h, he⟩)))
    have hl := Real.log_lt_log (Real.exp_pos _) hr
    rw [Real.log_exp] at hl
    linarith only [hl, le_abs_self (Real.log n - (v + 5 / 2))]

/-- At center exp(v+5/2), the full real arithmetic series equals its
finite character-weighted Mangoldt sum over the translated support. -/
theorem triangle_window_series {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (v : ℝ) :
    let x := Real.exp (v + 5 / 2)
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    (∑' n : ℕ, K.summand χ x n).re =
      ∑ n ∈ Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * (χ (n : ZMod q)).re *
          LLS.PaperStatements.triangularKernelProfile (5 / 4) (n / x) := by
  intro x K
  change Complex.reCLM _ = _
  rw [Complex.reCLM.map_tsum (K.summable_summand χ (Real.exp_pos _))]
  apply Eq.trans (tsum_eq_sum (s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊) ?_)
  · apply Finset.sum_congr rfl
    intro n hn
    exact
      triangle_window_term χ (Real.exp_pos _) ((Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hn).1)
  · intro n hout
    change (K.summand χ x n).re = 0
    by_cases hn : n = 0
    · subst n
      simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re]
    rw [triangle_window_term χ (Real.exp_pos _) (Nat.pos_of_ne_zero hn),
      triangle_window_off (Nat.pos_of_ne_zero hn) hout, mul_zero]

/-- The three finite character-weighted window sums inherit the uniform triple bound. -/
theorem triangle_triple_window {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let x := Real.exp (2 * Real.log R + 5 / 2)
    let mass {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :=
      (2 / 5 : ℝ) *
        |∑ b ∈ Finset.Ioc ⌊Real.exp (2 * Real.log R)⌋₊ ⌊Real.exp (2 * Real.log R + 5)⌋₊,
            ArithmeticFunction.vonMangoldt b / Real.sqrt b * (χ (b : ZMod k)).re *
              LLS.PaperStatements.triangularKernelProfile (5 / 4) (b / x)|
    mass (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq)) +
        mass (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr)) +
        mass (NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr)) <
      2 * Real.log n - 84 / 5 + 3 / 250 := by
  have h := triangle_triple_arithmetic hn ho hs he hp hq hr hk hj hm hv hw hGRH hR hb
  dsimp only at h ⊢
  simpa only [triangle_window_series] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
