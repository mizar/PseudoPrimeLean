/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# A right-half-plane growth bound for `ζ'/ζ`

Fully generic bound on `‖ζ'/ζ‖` on a vertical line `Re s = τ > 1` (the region of absolute
convergence, where no zero-density or growth theory is needed) by the value of the von Mangoldt
Dirichlet series at the real point `τ`. This general estimate is independent of any contour kernel,
so files needing only this growth bound need not import integrability machinery.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On `Re s = τ > 1`, the logarithmic derivative of `ζ` is bounded uniformly in the imaginary
part by the value of the von Mangoldt Dirichlet series at the real point `τ`. -/
theorem norm_deriv_riemannZeta_div_le {τ : ℝ} (hτ : 1 < τ) (y : ℝ) :
    ‖deriv riemannZeta ((τ : ℂ) + y * Complex.I) / riemannZeta ((τ : ℂ) + y * Complex.I)‖ ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ := by
  set s : ℂ := (τ : ℂ) + y * Complex.I with hs_def
  have hs : (1 : ℝ) < s.re := by
    rw [hs_def];
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hτ
  have heq := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hsumm := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  rw [LSeriesSummable, ← summable_norm_iff] at hsumm
  have hterm :
    ∀ n : ℕ,
      ‖LSeries.term (fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) s n‖ =
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, CharP.cast_eq_zero,
        zero_div]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      rw [LSeries.term_of_ne_zero hn0, norm_div,
        show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      have hcast : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ = ArithmeticFunction.vonMangoldt n := by
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rw [hcast, hs_def]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  calc
    ‖deriv riemannZeta s / riemannZeta s‖ =
        ‖LSeries (fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) s‖ :=
      by rw [heq, neg_div, norm_neg]
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) s n‖ := by
      rw [LSeries]
      exact norm_tsum_le_tsum_norm hsumm
    _ = ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ := tsum_congr hterm

/-- `Λ(n)/n^x` is summable for `x > 1`, via `ArithmeticFunction.LSeriesSummable_vonMangoldt`. -/
theorem summable_vonMangoldt_div_rpow {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ x) := by
  have hLS :
    Summable
      (fun n : ℕ ↦ ‖LSeries.term (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) (x : ℂ) n‖) :=
    summable_norm_iff.mpr
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (x : ℂ))
        (by simpa only [Complex.ofReal_re] using hx))
  refine hLS.congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, CharP.cast_eq_zero,
      zero_div]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.term_def]
    simp only [hn, ite_false]
    rw [norm_div, show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.ofReal_re, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- `∑' n, Λ(n)/n^y ≤ ∑' n, Λ(n)/n^x` for `1 < x ≤ y`: each term is antitone in the exponent
since `n ≥ 1` (for `n = 0`, both sides vanish termwise). -/
theorem tsum_vonMangoldt_div_rpow_antitone {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ y ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ x := by
  have hy : 1 < y := lt_of_lt_of_le hx hxy
  apply
    Summable.tsum_le_tsum _ (summable_vonMangoldt_div_rpow hy) (summable_vonMangoldt_div_rpow hx)
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_div, Std.le_refl]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hxy' : (n : ℝ) ^ x ≤ (n : ℝ) ^ y := Real.rpow_le_rpow_of_exponent_le hn1 hxy
    exact
      div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_pos_of_pos hnpos x)
        hxy'

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
