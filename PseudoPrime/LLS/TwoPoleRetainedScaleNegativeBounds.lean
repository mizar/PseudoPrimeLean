/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleRetainedScaleBounds
public import PseudoPrime.LLS.TwoPoleSignedSharpNegativeBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorAmbientBounds

/-! # Negative prime witnesses from the scale-dependent two-pole numerator -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The negative root (500/821)L+(33/20)log L+21/2. It retains the logarithmic local cost and uses
the scale-dependent error numerator. Applying it at log B+7/5 gives a common Jacobi radius for
inputs at most B. -/
noncomputable def retainedScaleTwoPoleNegativeLogRoot (L : ℝ) : ℝ :=
  (500 / 821 : ℝ) * L + (33 / 20 : ℝ) * Real.log L + 21 / 2

/-- The negative root is monotone on positive inputs. Use logarithmic monotonicity and positive
coefficients; this transfers the common ambient logarithm to an explicit input logarithm. -/
theorem retainedScaleTwoPoleNegativeLogRoot_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    retainedScaleTwoPoleNegativeLogRoot x ≤ retainedScaleTwoPoleNegativeLogRoot y := by
  have h := Real.log_le_log hx hxy
  dsimp only [retainedScaleTwoPoleNegativeLogRoot]
  linarith only [h, hxy]

/-- For L at least 800, log L is at least six. Compare L with 512 and use the certified lower
bound on log two. This supplies the lower corner for the retained polynomial. -/
theorem retainedScale_log_lower {L : ℝ} (hL : 800 ≤ L) : 6 ≤ Real.log L := by
  have h :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 512) (show (512 : ℝ) ≤ L by linarith only [hL])
  rw [show (512 : ℝ) = 2 ^ 9 by norm_num only, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_gt_d9]

/-- For L at least 800, the root is at least two and both cutoff logarithms satisfy the
displayed caps. Bound the root by 16L/25 using a global logarithmic tangent, then compare
squared endpoints. These data retain the small positive endpoint allowances in the local cost. -/
theorem retainedScaleTwoPoleNegativeLogRoot_data {L : ℝ} (hL : 800 ≤ L) :
    2 ≤ retainedScaleTwoPoleNegativeLogRoot L ∧
      Real.log ((99 / 40 : ℝ) * retainedScaleTwoPoleNegativeLogRoot L ^ 2) ≤
        2 * Real.log L + 1 / 40 ∧
      Real.log ((101 / 40 : ℝ) * retainedScaleTwoPoleNegativeLogRoot L ^ 2) ≤
        2 * Real.log L + 1 / 20 := by
  let r := retainedScaleTwoPoleNegativeLogRoot L
  have hl := retainedScale_log_lower hL
  have hp : 0 < L := by linarith only [hL]
  have ht := sharpSigned_log_tangent hp
  have hr : 2 ≤ r := by
    dsimp only [r, retainedScaleTwoPoleNegativeLogRoot]; linarith only [hL, hl]
  have hu : r ≤ (16 / 25 : ℝ) * L := by
    dsimp only [r, retainedScaleTwoPoleNegativeLogRoot]
    linarith only [ht, hL]
  have hs := mul_self_le_mul_self (by linarith only [hr] : 0 ≤ r) hu
  have ha :=
    Real.log_le_log (by nlinarith only [hr, sq_nonneg (r - 2)] : 0 < (99 / 40 : ℝ) * r ^ 2)
      (show (99 / 40 : ℝ) * r ^ 2 ≤ (41 / 40 : ℝ) * L ^ 2 by nlinarith only [hs])
  rw [Real.log_mul (by norm_num only : (41 / 40 : ℝ) ≠ 0) (pow_ne_zero 2 hp.ne'),
    Real.log_pow] at ha
  norm_num only [Nat.cast_ofNat] at ha
  have hca := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 41 / 40)
  have hb :=
    Real.log_le_log (by nlinarith only [hr, sq_nonneg (r - 2)] : 0 < (101 / 40 : ℝ) * r ^ 2)
      (show (101 / 40 : ℝ) * r ^ 2 ≤ (21 / 20 : ℝ) * L ^ 2 by nlinarith only [hs])
  rw [Real.log_mul (by norm_num only : (21 / 20 : ℝ) ≠ 0) (pow_ne_zero 2 hp.ne'),
    Real.log_pow] at hb
  norm_num only [Nat.cast_ofNat] at hb
  have hcb := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 21 / 20)
  exact ⟨hr, by linarith only [ha, hca], by linarith only [hb, hcb]⟩

/-- For L at least 800 and u at least six, the retained numerator exceeds (4/5)Lu+L/100 at the
negative root. Use rational polynomial positivity with L-800, u-6 and the square of u-10.
The scalar separation includes the prime-factor exclusion budget. -/
theorem twoPoleRetainedNumerator_negative_margin {L u : ℝ} (hL : 800 ≤ L) (hu : 6 ≤ u) :
    (4 / 5 : ℝ) * L * u + L / 100 <
      twoPoleRetainedNumerator L (112 / 25) ((500 / 821 : ℝ) * L + (33 / 20 : ℝ) * u + 21 / 2)
        (2 * u + 1 / 20) := by
  dsimp only [twoPoleRetainedNumerator]
  nlinarith only [hL, hu, sq_nonneg (L - 800), sq_nonneg (u - 10),
    mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hu)]

/-- For a positive level q at most A with log A at least 800, the retained numerator dominates
the actual prime-factor cost. Bound the number of factors by 2log(A)/5 and keep the cutoff
allowance 1/40. This supplies the negative-witness extraction hypothesis. -/
theorem retainedScaleTwoPoleNegative_numerator_dominates_cost {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A)
    (hL : 800 ≤ Real.log A) :
    (q.primeFactors.card : ℝ) *
        Real.log ((99 / 40 : ℝ) * retainedScaleTwoPoleNegativeLogRoot (Real.log A) ^ 2) <
      twoPoleRetainedNumerator (Real.log A) (112 / 25)
        (retainedScaleTwoPoleNegativeLogRoot (Real.log A))
        (2 * Real.log (Real.log A) + 1 / 20) := by
  have hd := retainedScaleTwoPoleNegativeLogRoot_data hL
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_two_fifths_ambient_log hq hqA
      (by linarith only [hL] : 640 ≤ Real.log A)
  have hr : 2 ≤ retainedScaleTwoPoleNegativeLogRoot (Real.log A) := hd.1
  have hs := sq_nonneg (retainedScaleTwoPoleNegativeLogRoot (Real.log A) - 2)
  have hlog0 :
    0 ≤ Real.log ((99 / 40 : ℝ) * retainedScaleTwoPoleNegativeLogRoot (Real.log A) ^ 2) :=
    Real.log_nonneg (by nlinarith only [hr, hs])
  have hp := mul_le_mul hcard hd.2.1 hlog0 (show 0 ≤ (2 / 5 : ℝ) * Real.log A by linarith only [hL])
  have hn := twoPoleRetainedNumerator_negative_margin hL (retainedScale_log_lower hL)
  dsimp only [retainedScaleTwoPoleNegativeLogRoot] at hp ⊢
  nlinarith only [hp, hn]

/-- Under GRH, an even quadratic nonprincipal character of level at most A with log A at least
800 has a unit prime of value minus one through the displayed cutoff. Insert the even Gamma cap
and retained local-cost separation into the generic extraction. The common scale covers small
conductors. -/
theorem exists_prime_neg_one_le_retainedScaleTwoPole_log_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (heven : χ.Even) (hne : χ ≠ 1)
    (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 800 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * retainedScaleTwoPoleNegativeLogRoot (Real.log A) ^ 2 ∧
        χ p = -1 := by
  have hd := retainedScaleTwoPoleNegativeLogRoot_data hL
  have hc :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      χ.primitiveCharacter ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven)
  exact
    exists_prime_neg_one_of_twoPoleRetainedNumerator χ hquad hne hqA hGRH hd.1 hd.2.2 hc
      (retainedScaleTwoPoleNegative_numerator_dominates_cost (Nat.pos_of_ne_zero (NeZero.ne q)) hqA
        hL)

end PseudoPrime.LLS
