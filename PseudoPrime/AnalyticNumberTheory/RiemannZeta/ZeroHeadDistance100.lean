/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocal100Brackets
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroEnumerationCount
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Numerics

/-! # Weighted distance of the low zeros from one -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For 29 nonnegative ordinates satisfying the upper brackets, twice their
sum is below 3611. Subtract the 29 unit terms from the certified linear
bound used in the midpoint remainder. -/
theorem lowZero100_phase_curvature (g : Fin 29 → ℝ) (hpos : ∀ i, 0 ≤ g i)
    (hu : LowZero100UpperBounds g) : 2 * ∑ i, |g i| < 3611 := by
  have h := lowZero100_linear_lt g hu
  have he : (∑ i : Fin 29, ((2 : ℝ) * g i + 1)) = 2 * ∑ i, |g i| + 29 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, abs_of_nonneg (hpos _), Nat.cast_ofNat]
  linarith only [h, he]

/-- Under RH, 29 ordered positive zeros satisfying the upper ordinate
brackets and a count of at most 58 give a weighted distance sum below
3640. The count makes the enumeration simple and complete; conjugation
pairs the negative and positive zeros. -/
theorem zero_head_distance100_lt (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hu : LowZero100UpperBounds g) :
    (∑ ρ ∈ zerosUpTo 100, (riemannZetaZeroMultiplicity ρ : ℝ) * ‖ρ - 1‖) < 3640 := by
  let z : Fin 29 → ℂ := fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I
  have hinj : Function.Injective z := critical_points_injective g hmono.injective
  have him : ∀ i, (z i).im = g i := by
    intro i
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hz : ∀ i, z i ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) := by
    intro i
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).2
      refine ⟨hzero i, ?_, ?_⟩
      · simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        norm_num only
      · rw [him, abs_of_pos (hpos i)]
        exact hheight i
    · rw [him]
      exact hpos i
  have hc : zeroCount 100 ≤ 2 * (29 : ℕ) := by
    norm_num only [Nat.cast_ofNat]
    exact hcount
  have hp := positive_ledger_of_count (by norm_num only : (0 : ℝ) ≤ 100) hRH z hinj hz hc
  have hledger := hp.1.symm
  have hm : ∀ i, riemannZetaZeroMultiplicity (z i) = 1 := fun i ↦ hp.2 (z i) (hz i)
  have h :=
    zero_sum_eq_two_positive hRH (show (0 : ℝ) ≤ 100 by norm_num only)
      (fun ρ ↦ (riemannZetaZeroMultiplicity ρ : ℝ) * ‖ρ - 1‖)
      (by
        intro ρ hρ
        have hz' := (mem_zerosUpTo (show (0 : ℝ) ≤ 100 by norm_num only)).1 hρ
        have hr :=
          RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH
            (RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz'.1 hz'.2.1)
        have hne : ρ ≠ 1 := by
          intro he
          rw [he, Complex.one_re] at hr
          norm_num only at hr
        rw [multiplicity_conj hne]
        have he : (starRingEnd ℂ) ρ - 1 = (starRingEnd ℂ) (ρ - 1) := by simp only [map_sub, map_one]
        rw [he, Complex.norm_conj])
  rw [h, hledger, Finset.sum_image]
  · rw [Finset.mul_sum]
    have he :
      (∑ i, (2 : ℝ) * ((riemannZetaZeroMultiplicity (z i) : ℝ) * ‖z i - 1‖)) =
        ∑ i, (2 : ℝ) * ‖z i - 1‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hm i]
      norm_num only [Nat.cast_one, one_mul]
    rw [he]
    exact lowZero100_distance_sum_lt g (fun i ↦ (hpos i).le) hu
  · intro a ha b hb hab
    exact hinj hab

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
