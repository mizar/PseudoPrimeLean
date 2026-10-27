/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReflectedSplitConductorBounds
public import PseudoPrime.LLS.TwoPoleConductorPrefixNegativeBounds
public import PseudoPrime.LLS.Anchor250Separation

/-! # A fixed-width negative-prime root from the certified anchor-128 saving -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For every scale x, the certified mass 133/160 gives a lower cap on the fixed-width
principal comparison. Multiply the mass inequality by sqrt x and retain the actual error.
This supplies the fixed-width negative-witness criterion. -/
theorem jointRampPrincipalLower_ge_133_160 (x : ℝ) :
    (133 / 160 : ℝ) * Real.sqrt x - jointRampPrincipalErrorNumerator x / Real.sqrt x ≤
      jointRampPrincipalLower x := by
  have hm :=
    mul_le_mul_of_nonneg_right Analysis.ramp_mass_coefficient_ge_133_160 (Real.sqrt_nonneg x)
  dsimp only [jointRampPrincipalLower]
  linarith only [hm]

/-- Under GRH and an admissible conductor allocation, a fixed-width principal gap
above the level-prime cost yields a unit-prime witness of value minus one. Assume an
a certified lower saving g on the full Euler prefix minus d.
Combine the split reflected upper cap with the actual principal lower bound, then exclude
zero by coprimality and one by contradiction. This connects both error improvements to
the negative-witness consumer. -/
theorem exists_prime_neg_one_of_fixedRamp_reflectedSplit_conductor_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C Y g a d : ℝ} (hx : 2 ≤ x)
    (hY : 1 ≤ Y) (ha : 0 ≤ a) (hd : 0 ≤ d) (hscale : 1 ≤ (1 / 2 - a) * Real.sqrt x)
    (hprime :
      ∀ p : ℕ,
        p.Prime →
          AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) p ≤
            a * Real.log p + if p = 2 then d else 0)
    (hYcut : ∀ n ∈ Finset.Ioc 0 ⌊Y⌋₊, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hg : g ≤ twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊Y⌋₊) - d)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        jointRampPrincipalLower x - reflectedSplitUpper A (C - g) x) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
    by_contra hnone
    have ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1 := fun p hp hd hb ↦
      Classical.byContradiction (fun hv ↦ hnone ⟨p, hp, hd, hb, hv⟩)
    have hb :=
      gamma_primitive_add_local_le_reflectedSplit_conductor_prefix χ hquad hne hqA hGRH hx hY ha hd
        hscale hprime hYcut hC ht
    have hJ := jointRampPrincipalLower_le_actual hGRH.riemann (by linarith only [hx] : 1 ≤ x)
    have hN := gamma_ramp_no_witness_comparison χ hquad (by linarith only [hx] : 0 < x) ht
    dsimp only [reflectedSplitUpper] at hgap hb
    linarith only [hb, hJ, hN, hgap, hg]
  obtain ⟨p, hp, hd, hb, hv⟩ := hex
  have hz : χ p ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr
      ((ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd))
  refine ⟨p, hp, hd, hb, ?_⟩
  rcases hquad (p : ZMod q) with h0 | h1 | hm
  · exact False.elim (hz h0)
  · exact False.elim (hv h1)
  · exact hm

/-- Under GRH, a quadratic nonprincipal character has a negative unit-prime witness when
the explicit fixed-width gap exceeds its level-prime cost. Assume x at least 25, an
Euler cutoff b at least 128 below the witness cutoff. Use the
certified anchor, the prime cost 3/10 with its prime-two allowance, and the mass 133/160.
This removes all unverified prefix and conductor-allocation premises from the consumer. -/
theorem exists_prime_neg_one_of_fixedAnchor128_mass133 {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C b : ℝ} (hx : 25 ≤ x)
    (hb : 128 ≤ b) (hcut : b ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        (133 / 160 : ℝ) * Real.sqrt x - jointRampPrincipalErrorNumerator x / Real.sqrt x -
              reflectedSplitUpper A C x +
            ((3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ)) -
          (1 / 5 : ℝ) * Real.log 2) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hs : 5 ≤ Real.sqrt x := by nlinarith only [hx, Real.sq_sqrt hx0, Real.sqrt_nonneg x]
  have hp := pairedEulerPrefix_ge_anchor128 hGRH.riemann hb
  have hl := jointRampPrincipalLower_ge_133_160 x
  apply
    exists_prime_neg_one_of_fixedRamp_reflectedSplit_conductor_prefix χ hquad hne hqA hGRH
      (by linarith only [hx]) (Y := b) (by linarith only [hb]) (a := 3 / 10) (d :=
      (1 / 5 : ℝ) * Real.log 2) (by norm_num only)
      (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg 2)) (by linarith only [hs])
      (fun p hp ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_upper_three_tenths hp)
      (fun n hn ↦
        (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans
          ((Nat.floor_le (by linarith only [hb] : 0 ≤ b)).trans hcut))
      hC (g := (3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ) - (1 / 5 : ℝ) * Real.log 2)
      (by linarith only [hp])
  dsimp only [reflectedSplitUpper]
  dsimp only [reflectedSplitUpper] at hgap
  linarith only [hgap, hl]

/-- The exact fixed-width joint error at square-root scale r, with its quadratic,
linear and logarithmic terms separated. It is used to bound the normalized error uniformly
on an unbounded half-line rather than by a finite collection of input certificates. -/
noncomputable def fixedRampErrorNumerator (r : ℝ) : ℝ :=
  (231 / 24700 : ℝ) * r ^ 2 + (6059857 / 3952000 : ℝ) * r +
    (866862303 / 12350000 : ℝ) * Real.log r +
    (31263 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
    (3900519 / 123500 : ℝ) * Real.log (101 / 40 : ℝ) +
    17019273 / 790400

/-- For r positive, the actual joint arithmetic error at scale r squared equals the
rational-logarithmic numerator. Expand the definitions and the logarithms of products.
This identifies the scalar comparison with the proved arithmetic error. -/
theorem jointRampError_fixed_eq {r : ℝ} (hr : 0 < r) :
    jointRampPrincipalErrorNumerator (r ^ 2) = fixedRampErrorNumerator r := by
  dsimp only [jointRampPrincipalErrorNumerator, rampSmoothedIncrementError,
    rampExtendedSmoothedError, fixedRampErrorNumerator]
  rw [Real.sqrt_sq hr.le,
    Real.log_mul (pow_ne_zero 2 hr.ne') (by norm_num only : (99 / 40 : ℝ) ≠ 0),
    Real.log_mul (by norm_num only : (101 / 40 : ℝ) ≠ 0) (pow_ne_zero 2 hr.ne'), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  ring

/-- The three fixed logarithms have the displayed rational upper bounds.
Kernel-check Taylor interval certificates and apply their soundness. These constants
control the error on the whole half-line r at least 320. -/
theorem fixedAnchor_log_caps :
    Real.log (320 : ℝ) ≤ (577 / 100 : ℝ) ∧
      Real.log (99 / 40 : ℝ) ≤ (907 / 1000 : ℝ) ∧ Real.log (101 / 40 : ℝ) ≤ (927 / 1000 : ℝ) := by
  have h1 :=
    Analysis.rationalLogIntervalCheck_sound
      (by decide +kernel : Analysis.rationalLogIntervalCheck 320 9 32 0 (577 / 100) = true)
  have h2 :=
    Analysis.rationalLogIntervalCheck_sound
      (by decide +kernel : Analysis.rationalLogIntervalCheck (99 / 40) 2 32 0 (907 / 1000) = true)
  have h3 :=
    Analysis.rationalLogIntervalCheck_sound
      (by decide +kernel : Analysis.rationalLogIntervalCheck (101 / 40) 2 32 0 (927 / 1000) = true)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] at h1 h2 h3
  exact ⟨h1.2, h2.2, h3.2⟩

/-- For r at least 320, the normalized fixed-width joint error is at most
(231/24700)r+3. Use a logarithmic tangent at 320 and monotonic reciprocal bounds.
This retains the smaller quadratic stencil cost of the fixed-width envelope. -/
theorem fixedRampError_normalized_le {r : ℝ} (hr : 320 ≤ r) :
    jointRampPrincipalErrorNumerator (r ^ 2) / r ≤ (231 / 24700 : ℝ) * r + 3 := by
  have hr0 : 0 < r := by linarith only [hr]
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 320) hr0
  have hl : Real.log r / r ≤ (577 / 32000 : ℝ) := by
    apply (div_le_iff₀ hr0).mpr
    linarith only [ht, fixedAnchor_log_caps.1, hr]
  have hm := mul_le_mul_of_nonneg_left hl (by norm_num only : (0 : ℝ) ≤ 866862303 / 12350000)
  have hc :
    (31263 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
        (3900519 / 123500 : ℝ) * Real.log (101 / 40 : ℝ) +
        17019273 / 790400 ≤
      (31263 / 10000 : ℝ) * (907 / 1000) + (3900519 / 123500 : ℝ) * (927 / 1000) +
        17019273 / 790400 := by
    linarith only [fixedAnchor_log_caps.2.1, fixedAnchor_log_caps.2.2]
  have hd :=
    (div_le_div_of_nonneg_right hc hr0.le).trans
      (div_le_div_of_nonneg_left (by norm_num only) (by norm_num only : (0 : ℝ) < 320) hr)
  rw [jointRampError_fixed_eq hr0]
  have he :
    fixedRampErrorNumerator r / r =
      (231 / 24700 : ℝ) * r + 6059857 / 3952000 + (866862303 / 12350000 : ℝ) * (Real.log r / r) +
        ((31263 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
            (3900519 / 123500 : ℝ) * Real.log (101 / 40 : ℝ) +
            17019273 / 790400) /
          r := by
    dsimp only [fixedRampErrorNumerator]
    field_simp [hr0.ne']
    ring
  rw [he]
  linarith only [hm, hd]

/-- For r at least 320, the three decreasing power errors satisfy the displayed
rational caps. Reduce real-power bounds to exact natural-power inequalities.
These caps control the reflected remainder and the Euler-prefix tail. -/
theorem fixedAnchor_tail_caps {r : ℝ} (hr : 320 ≤ r) :
    r ^ (-9 / 8 : ℝ) ≤ (1 / 650 : ℝ) ∧
      1 / r ^ 3 ≤ (1 / 1000000 : ℝ) ∧ ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ) ≤ (1 / 20 : ℝ) := by
  have hr0 : 0 < r := by linarith only [hr]
  have h1 : r ^ (-9 / 8 : ℝ) ≤ (1 / 650 : ℝ) := by
    apply
      Analysis.negRationalPower_le_of_one_le_mul_pow hr0 (by norm_num only) 9
        (by norm_num only : (8 : ℕ) ≠ 0)
    have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 320) hr 9
    have hc : (1 : ℝ) ≤ (1 / 650 : ℝ) ^ 8 * (320 : ℝ) ^ 9 := by norm_num only
    exact hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num only))
  have h2 : 1 / r ^ 3 ≤ (1 / 1000000 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hr0 3)).mpr
    have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 320) hr 3
    nlinarith only [hp]
  have h3 : ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ) ≤ (1 / 20 : ℝ) := by
    have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 320) hr 2
    have hc : (1 : ℝ) ≤ (1 / 20 : ℝ) ^ 4 * ((99 / 40 : ℝ) * r ^ 2) ^ 1 := by nlinarith only [hp]
    have he :=
      Analysis.negRationalPower_le_of_one_le_mul_pow
        (mul_pos (by norm_num only : (0 : ℝ) < 99 / 40) (sq_pos_of_pos hr0)) (hi := (1 / 20 : ℝ))
        (by norm_num only) 1 (by norm_num only : (4 : ℕ) ≠ 0) hc
    simpa only [Nat.cast_one, Nat.cast_ofNat] using he
  exact ⟨h1, h2, h3⟩

/-- For r at least 320, all constant costs after the normalized error bound,
including the reflected remainder, Euler tail and prime-two allowance, total at most 43/10.
Combine the rational power caps and log two. This leaves only the conductor and level-prime
logarithmic costs in the polynomial separation. -/
theorem fixedAnchor_constant_cost_le {r : ℝ} (hr : 320 ≤ r) :
    3 + (112 / 25 : ℝ) + 4 / r + (35 / 2 : ℝ) * r ^ (-9 / 8 : ℝ) + 1 / r ^ 3 - 3643 / 1000 +
        5 * ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ) +
        (1 / 5 : ℝ) * Real.log 2 ≤
      (43 / 10 : ℝ) := by
  have ht := fixedAnchor_tail_caps hr
  have hd : 4 / r ≤ (1 / 80 : ℝ) := by
    apply (div_le_iff₀ (by linarith only [hr] : 0 < r)).mpr
    linarith only [hr]
  linarith only [ht.1, ht.2.1, ht.2.2, hd, Real.log_two_lt_d9]

/-- The negative-witness root (500/821)L+(33/20)log L+6.
It replaces additive constant nine while retaining the same analytic starting logarithm.
The character theorem and common-ambient Jacobi bounds use this root. -/
noncomputable def fixedAnchorNegativeRoot (L : ℝ) : ℝ :=
  (500 / 821 : ℝ) * L + (33 / 20 : ℝ) * Real.log L + 6

/-- For L at least 500, the root is at least 320 and its witness cutoff logarithm
is at most 2 log L+1/20. Compare with the existing root of constant nine.
This discharges all scale and logarithmic side conditions of the new separation. -/
theorem fixedAnchorNegativeRoot_data {L : ℝ} (hL : 500 ≤ L) :
    320 ≤ fixedAnchorNegativeRoot L ∧
      Real.log ((99 / 40 : ℝ) * fixedAnchorNegativeRoot L ^ 2) ≤ 2 * Real.log L + 1 / 20 := by
  have hu := conductorPrefix_log_lower hL
  have hr : 320 ≤ fixedAnchorNegativeRoot L := by
    dsimp only [fixedAnchorNegativeRoot]
    linarith only [hL, hu]
  have hd := conductorPrefixNegativeLogRoot_data hL
  have hs :=
    mul_self_le_mul_self (by linarith only [hr] : 0 ≤ fixedAnchorNegativeRoot L)
      (show fixedAnchorNegativeRoot L ≤ conductorPrefixNegativeLogRoot L
        by
        dsimp only [fixedAnchorNegativeRoot, conductorPrefixNegativeLogRoot]
        linarith only)
  have ht :=
    Real.log_le_log
      (by nlinarith only [hr, sq_nonneg (fixedAnchorNegativeRoot L - 320)] :
        0 < (99 / 40 : ℝ) * fixedAnchorNegativeRoot L ^ 2)
      (show
        (99 / 40 : ℝ) * fixedAnchorNegativeRoot L ^ 2 ≤
          (99 / 40 : ℝ) * conductorPrefixNegativeLogRoot L ^ 2
        by nlinarith only [hs])
  exact ⟨hr, ht.trans hd.2.1⟩

/-- For L at least 500 and u at least six, the explicit quadratic numerator
exceeds the affine factor-count cost. Expand at the lower corner and use nonnegative
shifted products. This proves a whole-half-line margin without interval subdivision. -/
theorem fixedAnchorNegative_polynomial_margin {L u : ℝ} (hL : 500 ≤ L) (hu : 6 ≤ u) :
    let r := (500 / 821 : ℝ) * L + (33 / 20 : ℝ) * u + 6
    (5 / 2 + (3 / 8 : ℝ) * L) * (2 * u + 1 / 20) <
      ((162407 / 197600 : ℝ) * r - L / 2 - 43 / 10) * r - (7 / 6 : ℝ) * L := by
  dsimp only
  nlinarith only [hL, hu, sq_nonneg (L - 500), sq_nonneg (u - 6),
    mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hu)]

/-- For an ambient logarithm at least 500, the actual fixed-width scalar gap at
the root of constant six exceeds the uniform level-prime cost. Combine the exact error
identity, decreasing tail caps and polynomial margin. This is the quantitative input to
negative-witness extraction; the statement retains the actual arithmetic upper cap. -/
theorem fixedAnchor_negative_gap_positive {A : ℕ} (hL : 500 ≤ Real.log A) :
    let r := fixedAnchorNegativeRoot (Real.log A)
    (5 / 2 + (3 / 8 : ℝ) * Real.log A) * Real.log ((99 / 40 : ℝ) * r ^ 2) / Real.sqrt (r ^ 2) <
      (133 / 160 : ℝ) * Real.sqrt (r ^ 2) -
            jointRampPrincipalErrorNumerator (r ^ 2) / Real.sqrt (r ^ 2) -
            reflectedSplitUpper A (112 / 25) (r ^ 2) +
          ((3643 / 1000 : ℝ) - 5 * ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ)) -
        (1 / 5 : ℝ) * Real.log 2 := by
  let r := fixedAnchorNegativeRoot (Real.log A)
  have hd := fixedAnchorNegativeRoot_data hL
  have hr : 320 ≤ r := hd.1
  have hr0 : 0 < r := by linarith only [hr]
  have hE := fixedRampError_normalized_le hr
  have hC := fixedAnchor_constant_cost_le hr
  have hp := fixedAnchorNegative_polynomial_margin hL (conductorPrefix_log_lower hL)
  have hc :=
    mul_le_mul_of_nonneg_left hd.2 (show 0 ≤ 5 / 2 + (3 / 8 : ℝ) * Real.log A by linarith only [hL])
  have hsep :
    (5 / 2 + (3 / 8 : ℝ) * Real.log A) * Real.log ((99 / 40 : ℝ) * r ^ 2) / r +
        (7 / 6 : ℝ) * Real.log A / r <
      (162407 / 197600 : ℝ) * r - Real.log A / 2 - 43 / 10 := by
    rw [← add_div]
    apply (div_lt_iff₀ hr0).mpr
    dsimp only [r, fixedAnchorNegativeRoot] at hc ⊢
    dsimp only at hp
    nlinarith only [hp, hc]
  have hpow : (r ^ 2) ^ (-9 / 16 : ℝ) = r ^ (-9 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    norm_num only [Nat.cast_ofNat]
  have hmax := ambient_max_eq_of_log_ge_250 (by linarith only [hL] : 250 ≤ Real.log A)
  change _ < _
  dsimp only [reflectedSplitUpper]
  rw [Real.sqrt_sq hr0.le, hpow, hmax, add_div]
  have he : 1 / (r ^ 2 * r) = 1 / r ^ 3 := by ring
  rw [he]
  linarith only [hsep, hE, hC]

/-- Under GRH, an even quadratic nonprincipal character of level at most A has
a negative unit-prime witness below (99/40) times the new root squared when log A is at
least 500. Use the certified anchor-128 criterion and the uniform factor-count bound.
This improves the previous additive constant nine to six without finite input enumeration. -/
theorem exists_prime_neg_one_le_fixedAnchor_log_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (heven : χ.Even) (hne : χ ≠ 1)
    (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * fixedAnchorNegativeRoot (Real.log A) ^ 2 ∧ χ p = -1 := by
  let r := fixedAnchorNegativeRoot (Real.log A)
  have hd := fixedAnchorNegativeRoot_data hL
  have hx : 25 ≤ r ^ 2 := by nlinarith only [hd.1, sq_nonneg (r - 320)]
  have hc :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      χ.primitiveCharacter ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven)
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_five_halves_add_three_eighths_log
      (Nat.pos_of_ne_zero (NeZero.ne q)) hqA
  have hlog : 0 ≤ Real.log ((99 / 40 : ℝ) * r ^ 2) := Real.log_nonneg (by linarith only [hx])
  have hcost :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hlog) (Real.sqrt_nonneg (r ^ 2))
  have hgap := fixedAnchor_negative_gap_positive hL
  apply
    exists_prime_neg_one_of_fixedAnchor128_mass133 χ hquad hne hqA hGRH hx (b :=
      (99 / 40 : ℝ) * r ^ 2) _ le_rfl hc (hcost.trans_lt hgap)
  nlinarith only [hd.1, sq_nonneg (r - 320)]

end PseudoPrime.LLS
