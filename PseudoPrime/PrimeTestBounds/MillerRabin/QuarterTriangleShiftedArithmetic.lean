/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleZeroMass

/-! # Shifted triangle arithmetic outside the origin support -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Above the triangle support, the conductor profile and all reciprocal-scale
arithmetic terms vanish because every positive index is at least one. -/
theorem triangle_reciprocal_vanish {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (hl : 5 / 2 ≤ Real.log x) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    LLS.PaperStatements.triangularKernelProfile (5 / 4) x = 0 ∧
      (∑' n : ℕ, K.summand χ x⁻¹ n) = 0 := by
  intro K
  have hv {y : ℝ} (hy : 5 / 2 ≤ Real.log y) :
    LLS.PaperStatements.triangularKernelProfile (5 / 4) y = 0 := by
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [abs_of_nonneg (by linarith only [hy])]
    exact max_eq_left (by linarith only [hy])
  refine ⟨hv hl, (tsum_congr (g := fun _ : ℕ => (0 : ℂ)) ?_).trans tsum_zero⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true]
  have hn' := Nat.one_le_cast (α := ℝ).mpr (Nat.pos_of_ne_zero hn)
  have hy := mul_le_mul_of_nonneg_right hn' hx.le
  rw [one_mul] at hy
  have hpos := hx.trans_le hy
  have hr :=
    LLS.PaperStatements.triangular_transform_of_function K (by norm_num only : (0 : ℝ) < 5 / 4) rfl
      hpos
  have hz : K.transform ((n : ℝ) * x) = 0 :=
    Complex.ext (hr.trans (hv (hl.trans (Real.log_le_log hx hy)))) (K.mellin_real _ hpos)
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn, div_inv_eq_mul, hz,
    mul_zero]

/-- Outside the origin support, the arithmetic series differs from the two
central gamma integrals by at most the unshifted absolute zero mass. -/
theorem triangle_shifted_arithmetic_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hi : χ⁻¹ = χ) {x : ℝ} (hx : 1 ≤ x)
    (hl : 5 / 2 ≤ Real.log x) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    let G (y : ℝ) :=
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            (K.function (Complex.I * t) * (y : ℂ) ^ (Complex.I * t))
    ‖(∑' n : ℕ, K.summand χ x n) - (G x + G x⁻¹)‖ ≤ ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ := by
  intro K G
  have hx0 := zero_lt_one.trans_le hx
  obtain ⟨hz, ha⟩ := triangle_reciprocal_vanish χ hx0 hl
  have he :=
    LLS.PaperStatements.triangular_dual_signed_central (by norm_num only : (0 : ℝ) < 5 / 4) hq hGRH
      hp hne (inv_ne_one.mpr hne) hx
  dsimp only at he
  rw [hi, ha, hz, Complex.ofReal_zero, mul_zero, zero_add, add_zero] at he
  change (∑' n : ℕ, K.summand χ x n) + (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) = G x + G x⁻¹ at he
  rw [← he, sub_add_cancel_left, norm_neg]
  have hs := K.summable_oscillatingZeroTerm hq hGRH hp hne (inv_ne_one.mpr hne) hx0
  exact (norm_tsum_le_tsum_norm hs.norm).trans_eq (tsum_congr (K.norm_oscillatingZeroTerm χ hx0))

end PseudoPrime.PrimeTestBounds.MillerRabin
