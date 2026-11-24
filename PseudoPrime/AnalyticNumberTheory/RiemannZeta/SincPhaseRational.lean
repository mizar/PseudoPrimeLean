/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincPhaseEndpoints
public import PseudoPrime.Analysis.ScaledRationalPhase

/-! # Rational certificates for centered phase contributions -/

public section

namespace PseudoPrime.Analysis

/-- For phases up to 4096, 24 Taylor terms and twelve rounded squares on the
decimal grid of denominator 10^20 enclose both real trigonometric components. -/
theorem scaledPhase_trig_bounds (v : ℚ) (hv : |(v : ℝ)| ≤ 4096) :
    let w := rationalScaledPhase (10 ^ 20) v 24 12
    let ε : ℝ := 2125763 / 10 ^ 20
    |Real.cos (v : ℝ) - (w.1 : ℝ)| ≤ ε ∧ |Real.sin (v : ℝ) - (w.2 : ℝ)| ≤ ε := by
  have hred : |((v / (2 : ℚ) ^ 12 : ℚ) : ℝ)| ≤ 1 := by
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, abs_div, abs_of_pos]
    linarith only [hv]
  have hp := pow_le_pow_left₀ (abs_nonneg _) hred 24
  have h :=
    norm_scaled_phase_error (by norm_num only : 0 < 10 ^ 20) v 24 12
      (by
        norm_num only; linarith only [hred])
      (by
        norm_num only [Nat.factorial] at hp ⊢; nlinarith only [hp])
      (by
        intro j hj
        interval_cases j <;>
          norm_num only [roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
            Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast])
  norm_num only [roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_natCast] at h
  have hr := (Complex.abs_re_le_norm _).trans h
  have hi := (Complex.abs_im_le_norm _).trans h
  rw [mul_comm Complex.I, Complex.exp_mul_I] at hr hi
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_I_re,
    Complex.mul_I_im, ← Complex.ofReal_ratCast, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.ofReal_re, Complex.ofReal_im, zero_add, neg_zero, add_zero,
    rationalComplexCast] at hr hi
  dsimp only
  norm_num only
  exact ⟨hr, hi⟩

end PseudoPrime.Analysis

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Compute the upper value and absolute slope enclosures from a single rational phase
evaluation. Both are inputs to the Taylor estimate on the ordinate bracket. -/
@[expose]
def centerPhaseBudget (v g : ℚ) : ℚ × ℚ :=
  let w := Analysis.rationalScaledPhase (10 ^ 20) (g * v) 24 12
  let ε : ℚ := 2125763 / 10 ^ 20
  let d := 1 / 4 + g ^ 2
  let p := 2 * g * (v / d - 1 / d ^ 2)
  let q := -v / d + 2 * (1 / 4 - g ^ 2) / d ^ 2
  let box := fun a b : ℚ ↦ max (a * (w.1 - ε)) (a * (w.1 + ε)) + max (b * (w.2 - ε)) (b * (w.2 + ε))
  (box (1 / d) (2 * g / d), max (box p q) (box (-p) (-q)))

/-- The rational checker encloses the actual center term and absolute derivative for
every input in the supported phase range. -/
theorem centerPhaseBudget_sound (v g : ℚ) (hphase : |((g * v : ℚ) : ℝ)| ≤ 4096) :
    ordinateTerm (v : ℝ) (g : ℝ) ≤ ((centerPhaseBudget v g).1 : ℝ) ∧
      |ordinateTermFirst (v : ℝ) (g : ℝ)| ≤ ((centerPhaseBudget v g).2 : ℝ) := by
  have ht := Analysis.scaledPhase_trig_bounds (g * v) hphase
  rw [Rat.cast_mul] at ht
  let ε : ℝ := 2125763 / 10 ^ 20
  have inside {x y : ℝ} (h : |x - y| ≤ ε) : x ∈ Set.Icc (y - ε) (y + ε) :=
    ⟨by linarith only [(abs_le.mp h).1], by linarith only [(abs_le.mp h).2]⟩
  apply ordinate_center_bounds (inside ht.1) (inside ht.2)
  simp only [centerPhaseBudget, Rat.cast_max, Rat.cast_add, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one]
  exact ⟨le_rfl, le_max_left _ _, le_max_right _ _⟩

/-- The contribution of one true zero in the bracket starting at a is bounded by
the computed center value, linear uncertainty and quadratic remainder. -/
@[expose]
def phaseBoxUpper (v a : ℚ) : ℚ :=
  let r : ℚ := 1 / 200
  let z := centerPhaseBudget v (a + r)
  z.1 + r * z.2 + r ^ 2 * (v ^ 2 / a + 2 * v / a ^ 2 + 2 / a ^ 3)

/-- The rational upper bound applies to every ordinate in the closed bracket of width 1/100. -/
theorem phaseBoxUpper_sound {v a : ℚ} {g : ℝ} (hv : 0 ≤ (v : ℝ)) (ha : 0 < (a : ℝ))
    (hg : g ∈ Set.Icc (a : ℝ) ((a : ℝ) + 1 / 100))
    (hphase : |(((a + 1 / 200) * v : ℚ) : ℝ)| ≤ 4096) :
    ordinateTerm (v : ℝ) g ≤ (phaseBoxUpper v a : ℝ) := by
  have hs := centerPhaseBudget_sound v (a + 1 / 200) hphase
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hs
  unfold phaseBoxUpper
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat]
  apply
    ordinateTerm_le_center ha (by norm_num only : (0 : ℝ) ≤ 1 / 200) _ _
      (le_of_eq (abs_of_nonneg hv)) hs.1 hs.2
  · linarith only
  · exact abs_le.mpr ⟨by linarith only [hg.1], by linarith only [hg.2]⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
