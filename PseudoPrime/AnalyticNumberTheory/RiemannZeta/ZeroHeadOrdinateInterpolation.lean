/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhaseDerivative
import PseudoPrime.Analysis.SecondDerivativeInterpolation

/-! # Interpolation of signed zero terms in the ordinate -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The complex signed zero term as a function of ordinate and fixed log height. -/
@[expose]
noncomputable def ordinatePhase (v g : ℝ) : ℂ :=
  Complex.exp (Complex.I * (v : ℂ) * (g : ℂ)) / (((1 / 2 : ℝ) : ℂ) + Complex.I * (g : ℂ))

/-- The first ordinate derivative of the complex zero term. -/
@[expose]
noncomputable def ordinatePhaseFirst (v g : ℝ) : ℂ :=
  (Complex.I * (v : ℂ)) * Complex.exp (Complex.I * (v : ℂ) * (g : ℂ)) /
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (g : ℂ)) -
    Complex.I * Complex.exp (Complex.I * (v : ℂ) * (g : ℂ)) /
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (g : ℂ)) ^ 2

/-- The critical-line denominator has real part one half and is nonzero. -/
theorem ordinateDen_ne (g : ℝ) : (((1 / 2 : ℝ) : ℂ) + Complex.I * (g : ℂ)) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.zero_re] at hr
  norm_num only at hr

/-- Differentiate the complex zero term with respect to its ordinate. -/
theorem hasDerivAt_ordinatePhase (v g : ℝ) :
    HasDerivAt (ordinatePhase v) (ordinatePhaseFirst v g) g := by
  have hi := (hasDerivAt_id g).ofReal_comp
  have hd := ((hi.const_mul Complex.I).const_add ((1 / 2 : ℝ) : ℂ))
  have he := ((hi.const_mul (Complex.I * (v : ℂ))).cexp)
  have h := he.div hd (ordinateDen_ne g)
  convert h using 1
  · rfl
  · dsimp only [ordinatePhaseFirst]
    simp only [id_eq, Complex.ofReal_one, mul_one]
    have hc := mul_inv_cancel₀ (ordinateDen_ne g)
    generalize hd0 : (((1 / 2 : ℝ) : ℂ) + Complex.I * (g : ℂ)) = z at *
    simp only [div_eq_mul_inv, ← inv_pow]
    linear_combination
      -(Complex.I * (v : ℂ) * Complex.exp (Complex.I * (v : ℂ) * (g : ℂ)) * z⁻¹) * hc

/-- The second ordinate derivative of the complex zero term. -/
@[expose]
noncomputable def ordinatePhaseSecond (v g : ℝ) : ℂ :=
  (Complex.I * (v : ℂ)) ^ 2 * Complex.exp (Complex.I * (v : ℂ) * (g : ℂ)) /
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (g : ℂ)) -
      2 * (Complex.I * (v : ℂ)) * Complex.I * Complex.exp (Complex.I * (v : ℂ) * (g : ℂ)) /
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (g : ℂ)) ^ 2 +
    2 * Complex.I ^ 2 * Complex.exp (Complex.I * (v : ℂ) * (g : ℂ)) /
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (g : ℂ)) ^ 3

/-- Differentiate the first ordinate derivative of the complex zero term. -/
theorem hasDerivAt_ordinatePhaseFirst (v g : ℝ) :
    HasDerivAt (ordinatePhaseFirst v) (ordinatePhaseSecond v g) g := by
  have hi := (hasDerivAt_id g).ofReal_comp
  have hd := ((hi.const_mul Complex.I).const_add ((1 / 2 : ℝ) : ℂ))
  have he := ((hi.const_mul (Complex.I * (v : ℂ))).cexp)
  have h1 := (he.const_mul (Complex.I * (v : ℂ))).div hd (ordinateDen_ne g)
  have h2 := (he.const_mul Complex.I).div (hd.pow 2) (pow_ne_zero 2 (ordinateDen_ne g))
  have h := h1.sub h2
  convert h using 1
  · rfl
  · dsimp only [ordinatePhaseSecond]
    simp only [id_eq, Complex.ofReal_one, mul_one, Nat.cast_ofNat, Pi.pow_apply, Nat.reduceSub,
      pow_one]
    have hc := mul_inv_cancel₀ (ordinateDen_ne g)
    generalize hd0 : (((1 / 2 : ℝ) : ℂ) + Complex.I * (g : ℂ)) = z at *
    simp only [div_eq_mul_inv, ← inv_pow]
    linear_combination
      -(Complex.I * (v : ℂ)) ^ 2 * Complex.exp (Complex.I * (v : ℂ) * (g : ℂ)) * z⁻¹ * hc +
        2 * Complex.I * (Complex.I * (v : ℂ)) * Complex.exp (Complex.I * (v : ℂ) * (g : ℂ)) *
          z⁻¹ ^ 2 *
          hc +
        (Complex.I * (Complex.I * (v : ℂ)) * Complex.exp (Complex.I * (v : ℂ) * (g : ℂ)) * z⁻¹ ^ 2 *
              (z * z⁻¹ - 1) -
            2 * Complex.I ^ 2 * Complex.exp (Complex.I * (v : ℂ) * (g : ℂ)) * z⁻¹ ^ 3) *
          hc

/-- For positive a ≤ g and |v| ≤ V, bound the second ordinate derivative
by the explicit inverse-height budget. -/
theorem norm_ordinatePhaseSecond_le (v g a V : ℝ) (ha : 0 < a) (hg : a ≤ g) (hv : |v| ≤ V) :
    ‖ordinatePhaseSecond v g‖ ≤ V ^ 2 / a + 2 * V / a ^ 2 + 2 / a ^ 3 := by
  let d : ℂ := ((1 / 2 : ℝ) : ℂ) + Complex.I * (g : ℂ)
  let e : ℂ := Complex.exp (Complex.I * (v : ℂ) * (g : ℂ))
  let A : ℂ := Complex.I * (v : ℂ)
  have hden : a ≤ ‖d‖ := by
    have h := Complex.abs_im_le_norm d
    have he : d.im = g := by
      simp only [d, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.ofReal_re, Complex.I_im, zero_mul, one_mul, zero_add]
    rw [he, abs_of_pos (ha.trans_le hg)] at h
    exact hg.trans h
  have he : ‖e‖ = 1 := by
    dsimp only [e]
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero, zero_add, Real.exp_zero]
  have hA : ‖A‖ = |v| := by
    simp only [A, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  have hn :=
    norm_add_le (A ^ 2 * e / d - 2 * A * Complex.I * e / d ^ 2) (2 * Complex.I ^ 2 * e / d ^ 3)
  have hs := norm_sub_le (A ^ 2 * e / d) (2 * A * Complex.I * e / d ^ 2)
  have hbase : ‖ordinatePhaseSecond v g‖ ≤ |v| ^ 2 / ‖d‖ + 2 * |v| / ‖d‖ ^ 2 + 2 / ‖d‖ ^ 3 := by
    change ‖A ^ 2 * e / d - 2 * A * Complex.I * e / d ^ 2 + 2 * Complex.I ^ 2 * e / d ^ 3‖ ≤ _
    simp only [norm_div, norm_mul, norm_pow, hA, he, Complex.norm_I, mul_one, one_pow,
      Complex.norm_ofNat] at hn hs
    linarith only [hn, hs]
  have hV : 0 ≤ V := (abs_nonneg v).trans hv
  have h1 := div_le_div₀ (sq_nonneg V) (pow_le_pow_left₀ (abs_nonneg v) hv 2) ha hden
  have h2 :=
    div_le_div₀ (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hV)
      (mul_le_mul_of_nonneg_left hv (by norm_num only : (0 : ℝ) ≤ 2)) (pow_pos ha 2)
      (pow_le_pow_left₀ ha.le hden 2)
  have h3 :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 2) (pow_pos ha 3)
      (pow_le_pow_left₀ ha.le hden 3)
  linarith only [hbase, h1, h2, h3]

/-- Twice the real part of the complex zero term. -/
@[expose]
noncomputable def ordinateTerm (v g : ℝ) : ℝ :=
  2 * (ordinatePhase v g).re

/-- The first ordinate derivative of the real zero term. -/
@[expose]
noncomputable def ordinateTermFirst (v g : ℝ) : ℝ :=
  2 * (ordinatePhaseFirst v g).re

/-- The second ordinate derivative of the real zero term. -/
@[expose]
noncomputable def ordinateTermSecond (v g : ℝ) : ℝ :=
  2 * (ordinatePhaseSecond v g).re

/-- The real zero term has the stated first derivative with respect to its ordinate. -/
theorem hasDerivAt_ordinateTerm (v g : ℝ) :
    HasDerivAt (ordinateTerm v) (ordinateTermFirst v g) g := by
  have h := (hasDerivAt_const g Complex.reCLM).clm_apply (hasDerivAt_ordinatePhase v g)
  have h' := h.const_mul 2
  convert h' using 1
  · funext y
    rfl
  · simp only [ordinateTermFirst, zero_apply, zero_add, Complex.reCLM_apply]

/-- The first real ordinate derivative has the stated second derivative. -/
theorem hasDerivAt_ordinateTermFirst (v g : ℝ) :
    HasDerivAt (ordinateTermFirst v) (ordinateTermSecond v g) g := by
  have h := (hasDerivAt_const g Complex.reCLM).clm_apply (hasDerivAt_ordinatePhaseFirst v g)
  have h' := h.const_mul 2
  convert h' using 1
  · funext y
    rfl
  · simp only [ordinateTermSecond, zero_apply, zero_add, Complex.reCLM_apply]

/-- Bound the real second ordinate derivative by twice the complex derivative budget. -/
theorem abs_ordinateTermSecond_le (v g a V : ℝ) (ha : 0 < a) (hg : a ≤ g) (hv : |v| ≤ V) :
    |ordinateTermSecond v g| ≤ 2 * (V ^ 2 / a + 2 * V / a ^ 2 + 2 / a ^ 3) := by
  have h :=
    (Complex.abs_re_le_norm (ordinatePhaseSecond v g)).trans
      (norm_ordinatePhaseSecond_le v g a V ha hg hv)
  simp only [ordinateTermSecond, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left h (by norm_num only)

/-- On an ordinate interval above a positive anchor, endpoint bounds extend
to the whole interval with the quadratic curvature error. -/
theorem ordinateTerm_interpolate (v a l r g V lo hi : ℝ) (ha : 0 < a) (hal : a ≤ l) (hab : l < r)
    (hg : g ∈ Set.Icc l r) (hv : |v| ≤ V) (hla : lo ≤ ordinateTerm v l)
    (hlb : lo ≤ ordinateTerm v r) (hua : ordinateTerm v l ≤ hi) (hub : ordinateTerm v r ≤ hi) :
    let M := 2 * (V ^ 2 / a + 2 * V / a ^ 2 + 2 / a ^ 3)
    lo - M * (r - l) ^ 2 / 8 ≤ ordinateTerm v g ∧ ordinateTerm v g ≤ hi + M * (r - l) ^ 2 / 8 := by
  let M := 2 * (V ^ 2 / a + 2 * V / a ^ 2 + 2 / a ^ 3)
  have hV : 0 ≤ V := (abs_nonneg v).trans hv
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact
      mul_nonneg (by norm_num only)
        (add_nonneg
          (add_nonneg (div_nonneg (sq_nonneg V) ha.le)
            (div_nonneg (mul_nonneg (by norm_num only) hV) (pow_nonneg ha.le 2)))
          (div_nonneg (by norm_num only) (pow_nonneg ha.le 3)))
  have hf : ∀ x ∈ Set.Icc l r, HasDerivAt (ordinateTerm v) (ordinateTermFirst v x) x := fun x _ ↦
    hasDerivAt_ordinateTerm v x
  have hd : ∀ x ∈ Set.Icc l r, HasDerivAt (ordinateTermFirst v) (ordinateTermSecond v x) x :=
    fun x _ ↦ hasDerivAt_ordinateTermFirst v x
  have hb : ∀ x ∈ Set.Icc l r, |ordinateTermSecond v x| ≤ M := by
    intro x hx
    exact abs_ordinateTermSecond_le v x a V ha (hal.trans hx.1) hv
  have hlow :=
    Analysis.lower_bound_on_interval_of_second_deriv_le hab hM hf hd
      (fun x hx ↦ (abs_le.mp (hb x hx)).2) hla hlb hg
  have hupp :=
    Analysis.lower_bound_on_interval_of_second_deriv_le hab hM (fun x hx ↦ (hf x hx).neg)
      (fun x hx ↦ (hd x hx).neg)
      (fun x hx ↦ by simpa only [neg_neg] using neg_le_neg (abs_le.mp (hb x hx)).1) (neg_le_neg hua)
      (neg_le_neg hub) hg
  simp only [Pi.neg_apply] at hupp
  dsimp only
  constructor <;> linarith only [hlow, hupp]

/-- The signed head is the sum of the real ordinate terms. -/
theorem zeroHeadPhase_eq_sum_terms {n : ℕ} (g : Fin n → ℝ) (v : ℝ) :
    zeroHeadPhase g v = ∑ i, ordinateTerm v (g i) := by
  simp only [zeroHeadPhase, ordinateTerm, ordinatePhase, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (((g i * v : ℝ) : ℂ) * Complex.I) = Complex.I * (v : ℂ) * (g i : ℂ) := by
    rw [Complex.ofReal_mul]
    ring
  have hd :
    (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = (((1 / 2 : ℝ) : ℂ) + Complex.I * (g i : ℂ)) := by
    ring
  rw [he, hd]

/-- Five ordinate samples bound the real zero term uniformly on the bracket,
including the quadratic interpolation error. -/
theorem ordinateTerm_four_cells (v a b g V lo hi : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : g ∈ Set.Icc a b) (hv : |v| ≤ V)
    (hnodes :
      ∀ j : ℕ,
        j ≤ 4 →
          lo ≤ ordinateTerm v (a + (j : ℝ) * (b - a) / 4) ∧
            ordinateTerm v (a + (j : ℝ) * (b - a) / 4) ≤ hi) :
    let M := 2 * (V ^ 2 / a + 2 * V / a ^ 2 + 2 / a ^ 3)
    lo - M * (b - a) ^ 2 / 128 ≤ ordinateTerm v g ∧
      ordinateTerm v g ≤ hi + M * (b - a) ^ 2 / 128 := by
  let w := (b - a) / 4
  let M := 2 * (V ^ 2 / a + 2 * V / a ^ 2 + 2 / a ^ 3)
  have hw : 0 < w := by
    dsimp only [w]; linarith only [hab]
  have hV : 0 ≤ V := (abs_nonneg v).trans hv
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact
      mul_nonneg (by norm_num only)
        (add_nonneg
          (add_nonneg (div_nonneg (sq_nonneg V) ha.le)
            (div_nonneg (mul_nonneg (by norm_num only) hV) (pow_nonneg ha.le 2)))
          (div_nonneg (by norm_num only) (pow_nonneg ha.le 3)))
  have hcell :
    ∀ j : ℕ,
      j < 4 →
        g ∈ Set.Icc (a + (j : ℝ) * w) (a + (j + 1 : ℕ) * w) →
        lo - M * (b - a) ^ 2 / 128 ≤ ordinateTerm v g ∧
          ordinateTerm v g ≤ hi + M * (b - a) ^ 2 / 128 := by
    intro j hj hgj
    have hj' : j ≤ 4 := hj.le
    have hs : j + 1 ≤ 4 := Nat.succ_le_iff.mpr hj
    have hn1 := hnodes j hj'
    have hn2 := hnodes (j + 1) hs
    dsimp only [w] at hgj
    simp only [Nat.cast_add, Nat.cast_one] at hgj hn2
    have hl : a ≤ a + (j : ℝ) * (b - a) / 4 := by
      have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      have hmul := mul_nonneg hj0 (sub_nonneg.mpr hab.le)
      linarith only [hmul]
    have hr : a + (j : ℝ) * (b - a) / 4 < a + ((j : ℝ) + 1) * (b - a) / 4 := by nlinarith only [hab]
    have hgj' : g ∈ Set.Icc (a + (j : ℝ) * (b - a) / 4) (a + ((j : ℝ) + 1) * (b - a) / 4) := by
      simpa only [mul_div_assoc] using hgj
    have h :=
      ordinateTerm_interpolate v a (a + (j : ℝ) * (b - a) / 4) (a + ((j : ℝ) + 1) * (b - a) / 4) g V
        lo hi ha hl hr hgj' hv hn1.1 hn2.1 hn1.2 hn2.2
    have he :
      (a + ((j : ℝ) + 1) * (b - a) / 4 - (a + (j : ℝ) * (b - a) / 4)) ^ 2 / 8 =
        (b - a) ^ 2 / 128 := by
      ring
    dsimp only at h
    constructor <;> nlinarith only [h.1, h.2, he]
  by_cases h1 : g ≤ a + w
  · apply hcell 0 (by norm_num only)
    constructor
    · norm_num only [Nat.cast_zero, zero_mul, add_zero]
      exact hg.1
    · norm_num only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, one_mul]
      exact h1
  · by_cases h2 : g ≤ a + 2 * w
    · apply hcell 1 (by norm_num only)
      constructor
      · simpa only [Nat.cast_one, one_mul] using (le_of_not_ge h1)
      · norm_num only [Nat.cast_add, Nat.cast_one]
        exact h2
    · by_cases h3 : g ≤ a + 3 * w
      · apply hcell 2 (by norm_num only)
        constructor
        · norm_num only
          exact le_of_not_ge h2
        · norm_num only
          exact h3
      · apply hcell 3 (by norm_num only)
        constructor
        · norm_num only
          exact le_of_not_ge h3
        · norm_num only
          dsimp only [w]
          linarith only [hg.2]

/-- Coordinatewise five-node bounds and curvature errors bound the entire
signed head uniformly over the ordinate brackets. -/
theorem zeroHeadPhase_four_cells {n : ℕ} (g a b lo hi : Fin n → ℝ) (v V : ℝ) (ha : ∀ i, 0 < a i)
    (hab : ∀ i, a i < b i) (hg : ∀ i, g i ∈ Set.Icc (a i) (b i)) (hv : |v| ≤ V)
    (hnodes :
      ∀ i (j : ℕ),
        j ≤ 4 →
          lo i ≤ ordinateTerm v (a i + (j : ℝ) * (b i - a i) / 4) ∧
            ordinateTerm v (a i + (j : ℝ) * (b i - a i) / 4) ≤ hi i) :
    (∑ i,
          (lo i -
            (2 * (V ^ 2 / a i + 2 * V / (a i) ^ 2 + 2 / (a i) ^ 3)) * (b i - a i) ^ 2 / 128)) ≤
        zeroHeadPhase g v ∧
      zeroHeadPhase g v ≤
        (∑ i,
          (hi i +
            (2 * (V ^ 2 / a i + 2 * V / (a i) ^ 2 + 2 / (a i) ^ 3)) * (b i - a i) ^ 2 / 128)) := by
  rw [zeroHeadPhase_eq_sum_terms]
  constructor
  · apply Finset.sum_le_sum
    intro i hi'
    exact
      (ordinateTerm_four_cells v (a i) (b i) (g i) V (lo i) (hi i) (ha i) (hab i) (hg i) hv
          (hnodes i)).1
  · apply Finset.sum_le_sum
    intro i hi'
    exact
      (ordinateTerm_four_cells v (a i) (b i) (g i) V (lo i) (hi i) (ha i) (hab i) (hg i) hv
          (hnodes i)).2

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
