/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFiniteSupport
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FiniteRows

/-! # Rational upper rows for finite-support principal sums -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational upper von Mangoldt contribution associated with a certified
prime-power row, and zero for indices that are not prime powers. -/
def quarterPsiUpper (n : ℕ) (r : RefinedEulerAtom) : ℚ :=
  if IsPrimePow n then r.hi else 0

/-- A checked row bounds its von Mangoldt value above. For non-prime-powers
both sides vanish; otherwise the row's upper logarithm endpoint applies. -/
theorem quarter_psi_row_upper {n : ℕ} {r : RefinedEulerAtom}
    (hc : IsPrimePow n → refinedEulerAtomCheck 24 n r = true) :
    ArithmeticFunction.vonMangoldt n ≤ (quarterPsiUpper n r : ℝ) := by
  by_cases hn : IsPrimePow n
  · have h := hc hn
    simp only [refinedEulerAtomCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := Analysis.rationalLogIntervalCheck_sound h.2.1
    simp only [Rat.cast_natCast] at hl
    have hΛ : ArithmeticFunction.vonMangoldt n = Real.log r.p := by
      rw [← h.1.2.2.1, ArithmeticFunction.vonMangoldt_apply_pow h.1.2.1,
        ArithmeticFunction.vonMangoldt_apply_prime h.1.1]
    simpa only [quarterPsiUpper, ite_eq_left hn, hΛ] using hl.2
  · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    simp only [quarterPsiUpper, ite_eq_right hn, Rat.cast_zero, hz, le_refl]

/-- Checked upper logarithm and weight rows bound the full principal sum at
positive scale. The integer endpoint covers the kernel support, and each row
is compared using nonnegative von Mangoldt and rational weight bounds. -/
theorem quarter_principal_rows_upper {X : ℝ} (hX : 0 < X) (N : ℕ) (hN : ⌊14 * X⌋₊ ≤ N)
    (data : ℕ → RefinedEulerAtom) (w : ℕ → ℚ)
    (hc : ∀ n ∈ Finset.Ioc 0 N, IsPrimePow n → refinedEulerAtomCheck 24 n (data n) = true)
    (hw0 : ∀ n ∈ Finset.Ioc 0 N, 0 ≤ w n)
    (hw : ∀ n ∈ Finset.Ioc 0 N, IsPrimePow n → refinedScaledWeight X n ≤ (w n : ℝ)) :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re ≤
      ((∑ n ∈ Finset.Ioc 0 N, quarterPsiUpper n (data n) * w n : ℚ) : ℝ) := by
  have hsub : Finset.Ioc 0 ⌊14 * X⌋₊ ⊆ Finset.Ioc 0 N := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨hn'.1, hn'.2.trans hN⟩
  have hsum :
    (∑ n ∈ Finset.Ioc 0 ⌊14 * X⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) ≤
      ∑ n ∈ Finset.Ioc 0 N, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ ↦
        LLS.PaperStatements.MellinKernel.principal_summand_re_nonneg refinedSixPoleKernel hX n)
  apply (quarter_principal_support_upper hX).trans (hsum.trans ?_)
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [Rat.cast_mul, refined_principal_summand_eq hX (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1)]
  by_cases hpow : IsPrimePow n
  · calc
      ArithmeticFunction.vonMangoldt n * refinedScaledWeight X n ≤
          ArithmeticFunction.vonMangoldt n * (w n : ℝ) :=
        mul_le_mul_of_nonneg_left (hw n hn hpow) ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ (quarterPsiUpper n (data n) : ℝ) * (w n : ℝ) :=
        mul_le_mul_of_nonneg_right (quarter_psi_row_upper (hc n hn))
          (Rat.cast_nonneg.mpr (hw0 n hn))
  · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
    simp only [hz, quarterPsiUpper, ite_eq_right hpow, Rat.cast_zero, zero_mul, le_refl]

end PseudoPrime.PrimeTestBounds.MillerRabin
