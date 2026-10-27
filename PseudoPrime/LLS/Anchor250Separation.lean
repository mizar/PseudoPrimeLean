/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CertifiedRampPrincipalBounds

/-! # Uniform finite-scale separation from logarithmic level 250 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The exact joint arithmetic error numerator at square-root scale r and stencil
width x/10. Rational coefficients separate the quadratic, linear, logarithmic and
constant costs. This scalar form is used on an unbounded logarithmic half-line. -/
noncomputable def tenthWidthErrorNumerator (r : ℝ) : ℝ :=
  (441 / 24700 : ℝ) * r ^ 2 + (4090897 / 3952000 : ℝ) * r +
    (484534203 / 12350000 : ℝ) * Real.log r +
    (31263 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
    (3977757 / 247000 : ℝ) * Real.log (139 / 40 : ℝ) +
    10033833 / 790400

/-- For positive r, the actual variable-width arithmetic budget at x=r^2,h=x/10
equals the displayed rational-logarithmic numerator. Expand the budget, use the
positive square-root and logarithm identities, and normalize. This prevents numerical
separation from using a detached surrogate. -/
theorem variableRampError_tenth_width_eq {r : ℝ} (hr : 0 < r) :
    variableRampPrincipalErrorNumerator (r ^ 2) (r ^ 2 / 10) = tenthWidthErrorNumerator r := by
  dsimp only [variableRampPrincipalErrorNumerator, variableRampIncrement, variableRampEnvelope,
    tenthWidthErrorNumerator]
  rw [Real.sqrt_sq hr.le,
    Real.log_mul (pow_ne_zero 2 hr.ne') (by norm_num only : (99 / 40 : ℝ) ≠ 0),
    Real.log_mul (by norm_num only : (139 / 40 : ℝ) ≠ 0) (pow_ne_zero 2 hr.ne'), Real.log_pow]
  field_simp [hr.ne']
  ring

/-- The three logarithms at the lower square-root scale and ramp endpoints have
the stated rational upper bounds. Kernel-check Taylor certificates and apply their
soundness. This supplies uniform logarithmic error caps. -/
theorem anchor250_log_bounds :
    Real.log (315 / 2 : ℝ) ≤ (253 / 50 : ℝ) ∧
      Real.log (99 / 40 : ℝ) ≤ (907 / 1000 : ℝ) ∧ Real.log (139 / 40 : ℝ) ≤ (1246 / 1000 : ℝ) := by
  have h1 :=
    Analysis.rationalLogIntervalCheck_sound
      (by decide +kernel : Analysis.rationalLogIntervalCheck (315 / 2) 8 32 0 (253 / 50) = true)
  have h2 :=
    Analysis.rationalLogIntervalCheck_sound
      (by decide +kernel : Analysis.rationalLogIntervalCheck (99 / 40) 2 32 0 (907 / 1000) = true)
  have h3 :=
    Analysis.rationalLogIntervalCheck_sound
      (by decide +kernel : Analysis.rationalLogIntervalCheck (139 / 40) 2 32 0 (1246 / 1000) = true)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2 h3
  exact ⟨h1.2, h2.2, by linarith only [h3.2]⟩

/-- For r at least 315/2, log r/r is at most 253/7875. Use the logarithm tangent
at 315/2 and its certified upper endpoint. This controls the logarithmic cost on
the whole half-line without interval subdivision. -/
theorem log_div_self_le_anchor250 {r : ℝ} (hr : (315 / 2 : ℝ) ≤ r) :
    Real.log r / r ≤ (253 / 7875 : ℝ) := by
  have hr0 : 0 < r := by linarith only [hr]
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 315 / 2) hr0
  apply (div_le_iff₀ hr0).mpr
  linarith only [ht, anchor250_log_bounds.1, hr]

/-- For r at least 315/2, the three remainder powers have the displayed rational
upper caps. Use monotonic natural powers and kernel rational inequalities to enclose
the negative real powers. This controls every nonlogarithmic tail uniformly. -/
theorem anchor250_tail_caps {r : ℝ} (hr : (315 / 2 : ℝ) ≤ r) :
    r ^ (-9 / 8 : ℝ) ≤ (17 / 5000 : ℝ) ∧
      1 / r ^ 3 ≤ (1 / 1000000 : ℝ) ∧ ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ) ≤ (8 / 125 : ℝ) := by
  have hr0 : 0 < r := by linarith only [hr]
  have h1 : r ^ (-9 / 8 : ℝ) ≤ (17 / 5000 : ℝ) := by
    apply
      Analysis.negRationalPower_le_of_one_le_mul_pow hr0 (by norm_num only) 9
        (by norm_num only : (8 : ℕ) ≠ 0)
    have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 315 / 2) hr 9
    have hc : (1 : ℝ) ≤ (17 / 5000 : ℝ) ^ 8 * (315 / 2 : ℝ) ^ 9 := by norm_num only
    exact hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num only))
  have h2 : 1 / r ^ 3 ≤ (1 / 1000000 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hr0 3)).mpr
    have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 315 / 2) hr 3
    nlinarith only [hp]
  have h3 : ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ) ≤ (8 / 125 : ℝ) := by
    have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 315 / 2) hr 2
    have hc : (1 : ℝ) ≤ (8 / 125 : ℝ) ^ 4 * ((99 / 40 : ℝ) * r ^ 2) ^ 1 := by nlinarith only [hp]
    have he :=
      Analysis.negRationalPower_le_of_one_le_mul_pow
        (mul_pos (by norm_num only : (0 : ℝ) < 99 / 40) (sq_pos_of_pos hr0)) (hi := (8 / 125 : ℝ))
        (by norm_num only) 1 (by norm_num only : (4 : ℕ) ≠ 0) hc
    simpa only [Nat.cast_one, Nat.cast_ofNat] using he
  exact ⟨h1, h2, h3⟩

/-- For r at least 315/2, the normalized logarithmic and constant numerator is at
most 1513/1000. Combine log r/r, the two fixed log caps and reciprocal monotonicity.
This is the uniform error input in the scalar separation. -/
theorem tenthWidth_log_cost_le_anchor250 {r : ℝ} (hr : (315 / 2 : ℝ) ≤ r) :
    ((484534203 / 12350000 : ℝ) * Real.log r + (31263 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
          (3977757 / 247000 : ℝ) * Real.log (139 / 40 : ℝ) +
          10033833 / 790400 +
          4) /
        r ≤
      (1513 / 1000 : ℝ) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hl :=
    mul_le_mul_of_nonneg_left (log_div_self_le_anchor250 hr)
      (by norm_num only : (0 : ℝ) ≤ 484534203 / 12350000)
  have hC :
    (31263 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
        (3977757 / 247000 : ℝ) * Real.log (139 / 40 : ℝ) +
        10033833 / 790400 +
        4 ≤
      (31263 / 10000 : ℝ) * (907 / 1000) + (3977757 / 247000 : ℝ) * (1246 / 1000) +
        10033833 / 790400 +
        4 := by
    linarith only [anchor250_log_bounds.2.1, anchor250_log_bounds.2.2]
  have hd :=
    (div_le_div_of_nonneg_right hC hr0.le).trans
      (div_le_div_of_nonneg_left (by norm_num only) (by norm_num only : (0 : ℝ) < 315 / 2) hr)
  have he :
    ((484534203 / 12350000 : ℝ) * Real.log r + (31263 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
          (3977757 / 247000 : ℝ) * Real.log (139 / 40 : ℝ) +
          10033833 / 790400 +
          4) /
        r =
      (484534203 / 12350000 : ℝ) * (Real.log r / r) +
        ((31263 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
            (3977757 / 247000 : ℝ) * Real.log (139 / 40 : ℝ) +
            10033833 / 790400 +
            4) /
          r := by
    ring
  rw [he]
  linarith only [hl, hd]

/-- The explicit split-remainder witness gap with r=63L/100 and h=r^2/10.
It uses mass 133/160, anchor constant 3643/1000 and the universal Gamma cap 523/100.
All terms are retained as rational coefficients, logs and real powers. -/
noncomputable def anchor250ScalarGap (L : ℝ) : ℝ :=
  let r := (63 / 100 : ℝ) * L
  ((133 / 160 : ℝ) - 441 / 24700) * r - L / 2 + 3643 / 500 - 523 / 100 - 4090897 / 3952000 -
    50 / 27 -
    ((484534203 / 12350000 : ℝ) * Real.log r + (31263 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
        (3977757 / 247000 : ℝ) * Real.log (139 / 40 : ℝ) +
        10033833 / 790400 +
        4) /
      r -
    (35 / 2 : ℝ) * r ^ (-9 / 8 : ℝ) -
    1 / r ^ 3 -
    10 * ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ)

/-- At every real L at least 250, the explicit scalar witness gap exceeds 3/50.
Bound all decreasing errors at the lower square-root scale while retaining the
positive linear term. This proves the entire half-line analytically. -/
theorem anchor250ScalarGap_gt {L : ℝ} (hL : 250 ≤ L) : (3 / 50 : ℝ) < anchor250ScalarGap L := by
  let r := (63 / 100 : ℝ) * L
  have hr : (315 / 2 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hL]
  have hl := tenthWidth_log_cost_le_anchor250 hr
  have ht := anchor250_tail_caps hr
  have hlead :
    ((133 / 160 : ℝ) - 441 / 24700) * (315 / 2 : ℝ) - (250 : ℝ) / 2 ≤
      ((133 / 160 : ℝ) - 441 / 24700) * r - L / 2 := by
    dsimp only [r]
    linarith only [hL]
  change
    (3 / 50 : ℝ) <
      ((133 / 160 : ℝ) - 441 / 24700) * r - L / 2 + 3643 / 500 - 523 / 100 - 4090897 / 3952000 -
        50 / 27 -
        ((484534203 / 12350000 : ℝ) * Real.log r + (31263 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
            (3977757 / 247000 : ℝ) * Real.log (139 / 40 : ℝ) +
            10033833 / 790400 +
            4) /
          r -
        (35 / 2 : ℝ) * r ^ (-9 / 8 : ℝ) -
        1 / r ^ 3 -
        10 * ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ)
  linarith only [hl, ht.1, ht.2.1, ht.2.2, hlead]

/-- A natural ambient level whose logarithm is at least 250 exceeds 20000, so its
auxiliary maximum equals itself. Bound log 20000 by log(2^15) and contradict the
logarithmic hypothesis. This removes the auxiliary ambient cost in the actual gap. -/
theorem ambient_max_eq_of_log_ge_250 {A : ℕ} (hL : 250 ≤ Real.log A) : max 20000 A = A := by
  have hA : A ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL
  have hA0 : (0 : ℝ) < A := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hA)
  have hlog : Real.log (20000 : ℝ) ≤ 15 := by
    have hm :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 20000) (by norm_num only : (20000 : ℝ) ≤ 2 ^ 15)
    rw [Real.log_pow] at hm
    norm_num only [Nat.cast_ofNat] at hm
    have h2 := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
    linarith only [hm, h2]
  have ha : 20000 ≤ A := by
    by_contra hn
    have hlt : A ≤ 20000 := (Nat.lt_of_not_ge hn).le
    have hl := Real.log_le_log hA0 (Nat.cast_le.mpr hlt)
    norm_num only [Nat.cast_ofNat] at hl
    linarith only [hl, hlog, hL]
  exact max_eq_right ha

/-- For natural ambient level with log at least 250, the actual variable-width gap
at r=63log(A)/100 is positive with the certified anchor saving and Gamma cap.
Identify its arithmetic numerator and real powers with the scalar gap proved above.
This connects uniform numerical separation to the actual witness interface. -/
theorem anchor250_actual_gap_positive {A : ℕ} (hL : 250 ≤ Real.log A) :
    let r := (63 / 100 : ℝ) * Real.log A
    0 <
      (133 / 160 : ℝ) * Real.sqrt (r ^ 2) -
          variableRampPrincipalErrorNumerator (r ^ 2) (r ^ 2 / 10) / Real.sqrt (r ^ 2) -
          reflectedSplitUpper A (523 / 100) (r ^ 2) +
        2 * ((3643 / 1000 : ℝ) - 5 * ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ)) := by
  let r := (63 / 100 : ℝ) * Real.log A
  have hlog0 : 0 < Real.log A := by linarith only [hL]
  have hr0 : 0 < r := mul_pos (by norm_num only) hlog0
  have hpow : (r ^ 2) ^ (-9 / 16 : ℝ) = r ^ (-9 / 8 : ℝ) := by
    have h := (Real.rpow_mul hr0.le (2 : ℝ) (-9 / 16 : ℝ)).symm
    norm_num only [Real.rpow_two] at h
    simpa only [neg_div] using h
  have he :
    (133 / 160 : ℝ) * r - tenthWidthErrorNumerator r / r -
          (Real.log A / 2 + 523 / 100 + ((7 / 6 : ℝ) * Real.log A + 4) / r +
            (35 / 2 : ℝ) * r ^ (-9 / 8 : ℝ) +
            1 / (r ^ 2 * r)) +
        2 * ((3643 / 1000 : ℝ) - 5 * ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ)) =
      anchor250ScalarGap (Real.log A) := by
    dsimp only [anchor250ScalarGap, tenthWidthErrorNumerator, r]
    field_simp [hlog0.ne']
    ring
  have hs := anchor250ScalarGap_gt hL
  change
    0 <
      (133 / 160 : ℝ) * Real.sqrt (r ^ 2) -
          variableRampPrincipalErrorNumerator (r ^ 2) (r ^ 2 / 10) / Real.sqrt (r ^ 2) -
          reflectedSplitUpper A (523 / 100) (r ^ 2) +
        2 * ((3643 / 1000 : ℝ) - 5 * ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ))
  rw [Real.sqrt_sq hr0.le, variableRampError_tenth_width_eq hr0]
  dsimp only [reflectedSplitUpper]
  rw [ambient_max_eq_of_log_ge_250 hL, Real.sqrt_sq hr0.le, hpow, he]
  linarith only [hs]

/-- At logarithmic level at least 250, the chosen square scale is at least two,
its Euler cutoff is at least 128, and that cutoff equals (392931/400000)L^2.
Use elementary square monotonicity and exact rational algebra. This discharges
the analytic and finite-anchor side conditions. -/
theorem anchor250_root_data {A : ℕ} (hL : 250 ≤ Real.log A) :
    let r := (63 / 100 : ℝ) * Real.log A
    2 ≤ r ^ 2 ∧
      128 ≤ (99 / 40 : ℝ) * r ^ 2 ∧
      (99 / 40 : ℝ) * r ^ 2 = (392931 / 400000 : ℝ) * (Real.log A) ^ 2 := by
  let r := (63 / 100 : ℝ) * Real.log A
  have hr : (315 / 2 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hL]
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 315 / 2) hr 2
  change
    2 ≤ r ^ 2 ∧
      128 ≤ (99 / 40 : ℝ) * r ^ 2 ∧ (99 / 40 : ℝ) * r ^ 2 = (392931 / 400000 : ℝ) * (Real.log A) ^ 2
  refine ⟨by nlinarith only [hs], by nlinarith only [hs], ?_⟩
  dsimp only [r]
  ring

/-- For a nonprincipal character under GRH, ambient level at least its level and
ambient logarithm at least 250, not all primes through (392931/400000)log(A)^2
have value one. Supply the actual positive gap, root data and universal Gamma cap.
This is the character consumer for the new finite-scale bound. -/
theorem prime_trivial_false_le_anchor250 {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 250 ≤ Real.log A) :
    ¬(∀ p : ℕ, p.Prime → (p : ℝ) ≤ (392931 / 400000 : ℝ) * (Real.log A) ^ 2 → χ p = 1) := by
  let r := (63 / 100 : ℝ) * Real.log A
  have hd := anchor250_root_data hL
  have hx2 : 2 ≤ r ^ 2 := hd.1
  have hx0 : 0 < r ^ 2 := by linarith only [hx2]
  have hf :=
    prime_trivial_false_of_anchor128_mass133 χ hne hqA hGRH hd.1
      (show 0 < r ^ 2 / 10 by exact div_pos hx0 (by norm_num only))
      (show r ^ 2 / 10 ≤ r ^ 2 by linarith only [hx0]) hd.2.1 (le_refl _)
      (AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed _)
      (anchor250_actual_gap_positive hL)
  intro ht
  apply hf
  intro p hp hb
  exact ht p hp (hb.trans_eq hd.2.2)

/-- Under the same nonprincipal GRH and ambient-level hypotheses, a prime with
character value different from one lies through (392931/400000)log(A)^2.
Extract a prime from the proved nontriviality statement. Nonunit primes are allowed;
odd-prime and negative-value conclusions require their own exclusion budgets. -/
theorem exists_prime_ne_one_le_anchor250 {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 250 ≤ Real.log A) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (392931 / 400000 : ℝ) * (Real.log A) ^ 2 ∧ χ p ≠ 1 := by
  classical
  by_contra hn
  apply prime_trivial_false_le_anchor250 χ hne hqA hGRH hL
  intro p hp hb
  exact Classical.byContradiction (fun hv ↦ hn ⟨p, hp, hb, hv⟩)

end PseudoPrime.LLS
