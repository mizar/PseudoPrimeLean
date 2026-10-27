/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleSignedSharpBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorAmbientBounds

/-! # Negative witnesses with a half-logarithmic prime-count budget -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For positive real L, log L is at most L/1500+32/5. A fourteen-term positive
Taylor sum bounds log 1500 by 37/5, and the global logarithmic tangent completes
the estimate. This controls finite-scale nonlinear witness roots. -/
theorem sharpSigned_log_tangent {L : ℝ} (hL : 0 < L) : Real.log L ≤ L / 1500 + 32 / 5 := by
  have h1500 : Real.log (1500 : ℝ) ≤ 37 / 5 := by
    apply (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 1500)).mpr
    have h : (1500 : ℝ) ≤ ∑ k ∈ Finset.range 14, (37 / 5 : ℝ) ^ k / (k.factorial : ℝ) := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    exact h.trans (Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 37 / 5) 14)
  have h := Real.log_le_sub_one_of_pos (div_pos hL (by norm_num only : (0 : ℝ) < 1500))
  rw [Real.log_div hL.ne' (by norm_num only : (1500 : ℝ) ≠ 0)] at h
  linarith only [h, h1500]

/-- The negative root (500/821)L+(41/20)log L+1821/100. The smaller logarithmic
coefficient uses the ambient prime-count bound log(A)/2, and the additive constant
uses the direct signed error bound. Apply at log B+7/5 for Jacobi witnesses. -/
noncomputable def sharpSignedTwoPoleNegativeLogRoot (L : ℝ) : ℝ :=
  (500 / 821 : ℝ) * L + (41 / 20 : ℝ) * Real.log L + 1821 / 100

/-- The sharp negative root is monotone on positive real inputs. Use log
monotonicity and the positive coefficients. This transfers ambient logarithms. -/
theorem sharpSignedTwoPoleNegativeLogRoot_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    sharpSignedTwoPoleNegativeLogRoot x ≤ sharpSignedTwoPoleNegativeLogRoot y := by
  have h := Real.log_le_log hx hxy
  dsimp only [sharpSignedTwoPoleNegativeLogRoot]
  linarith only [h, hxy]

/-- For L at least 1500, the sharp negative root is at most 3159L/5000.
Apply the global tangent to the logarithmic correction. This bounds the endpoints
and compares the resulting witness radius with the logarithmic square. -/
theorem sharpSignedTwoPoleNegativeLogRoot_le_linear {L : ℝ} (hL : 1500 ≤ L) :
    sharpSignedTwoPoleNegativeLogRoot L ≤ (3159 / 5000 : ℝ) * L := by
  have ht := sharpSigned_log_tangent (by linarith only [hL] : 0 < L)
  dsimp only [sharpSignedTwoPoleNegativeLogRoot]
  linarith only [ht, hL]

/-- For L at least 1500, the sharp negative root gives scale at least four,
lower root 3L/5+18, cutoff log at most 2log L and second endpoint log at most L/40.
Use a rational root enclosure and the global tangent on the entire half-line. -/
theorem sharpSignedTwoPoleNegativeLogRoot_data {L : ℝ} (hL : 1500 ≤ L) :
    4 ≤ sharpSignedTwoPoleNegativeLogRoot L ^ 2 ∧
      (3 / 5 : ℝ) * L + 18 ≤ sharpSignedTwoPoleNegativeLogRoot L ∧
      Real.log ((99 / 40 : ℝ) * sharpSignedTwoPoleNegativeLogRoot L ^ 2) ≤ 2 * Real.log L ∧
      Real.log ((101 / 40 : ℝ) * sharpSignedTwoPoleNegativeLogRoot L ^ 2) ≤ L / 40 := by
  have hl0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hL])
  have ht := sharpSigned_log_tangent (by linarith only [hL] : 0 < L)
  have hlo : (3 / 5 : ℝ) * L + 18 ≤ sharpSignedTwoPoleNegativeLogRoot L := by
    dsimp only [sharpSignedTwoPoleNegativeLogRoot]
    linarith only [hL, hl0]
  have hhi := sharpSignedTwoPoleNegativeLogRoot_le_linear hL
  have hr : 0 ≤ sharpSignedTwoPoleNegativeLogRoot L := by linarith only [hlo, hL]
  have hx : 4 ≤ sharpSignedTwoPoleNegativeLogRoot L ^ 2 := by
    nlinarith only [hlo, hL, sq_nonneg (sharpSignedTwoPoleNegativeLogRoot L - 2)]
  have hs := mul_self_le_mul_self hr hhi
  have hLp : 0 < L := by linarith only [hL]
  have ha :
    Real.log ((99 / 40 : ℝ) * sharpSignedTwoPoleNegativeLogRoot L ^ 2) ≤ 2 * Real.log L := by
    have h :=
      Real.log_le_log
        (by nlinarith only [hx] : 0 < (99 / 40 : ℝ) * sharpSignedTwoPoleNegativeLogRoot L ^ 2)
        (show (99 / 40 : ℝ) * sharpSignedTwoPoleNegativeLogRoot L ^ 2 ≤ L ^ 2 by
          nlinarith only [hs])
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hb : Real.log ((101 / 40 : ℝ) * sharpSignedTwoPoleNegativeLogRoot L ^ 2) ≤ L / 40 := by
    have h :=
      Real.log_le_log
        (by nlinarith only [hx] : 0 < (101 / 40 : ℝ) * sharpSignedTwoPoleNegativeLogRoot L ^ 2)
        (show (101 / 40 : ℝ) * sharpSignedTwoPoleNegativeLogRoot L ^ 2 ≤ (101 / 100 : ℝ) * L ^ 2 by
          nlinarith only [hs])
    rw [Real.log_mul (by norm_num only : (101 / 100 : ℝ) ≠ 0) (pow_ne_zero 2 hLp.ne'),
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have hc := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 101 / 100)
    linarith only [h, hc, ht, hL]
  exact ⟨hx, hlo, ha, hb⟩

/-- For positive q at most A with log A at least 1500, the signed gap at the
sharp negative root exceeds the actual prime-count local cost. Bound omega(q) by
log(A)/2 and the cost by (5/3)log log A, then use the direct signed-gap lower bound.
No RH is required for this scalar separation. -/
theorem sharpSignedTwoPoleGap_negative_log_dominates_cost {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A)
    (hL : 1500 ≤ Real.log A) :
    (q.primeFactors.card : ℝ) *
          Real.log ((99 / 40 : ℝ) * sharpSignedTwoPoleNegativeLogRoot (Real.log A) ^ 2) /
        Real.sqrt (sharpSignedTwoPoleNegativeLogRoot (Real.log A) ^ 2) <
      signedTwoPoleGap A (sharpSignedTwoPoleNegativeLogRoot (Real.log A) ^ 2) := by
  let L := Real.log A
  let r := sharpSignedTwoPoleNegativeLogRoot L
  have hd := sharpSignedTwoPoleNegativeLogRoot_data hL
  have hL0 : 0 ≤ L := by
    dsimp only [L]; linarith only [hL]
  have hl0 : 0 ≤ Real.log L :=
    Real.log_nonneg
      (by
        dsimp only [L]; linarith only [hL])
  have hroot : (3 / 5 : ℝ) * L + 18 ≤ r := hd.2.1
  have hr : 0 < r := by linarith only [hroot, hL0]
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_half_ambient_log hq hqA
      (by linarith only [hL] : 128 ≤ Real.log A)
  have hlog : Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ 2 * Real.log L := hd.2.2.1
  have hx4 : 4 ≤ r ^ 2 := hd.1
  have hlog0 : 0 ≤ Real.log ((99 / 40 : ℝ) * r ^ 2) := Real.log_nonneg (by nlinarith only [hx4])
  have hp := mul_le_mul hcard hlog hlog0 (show 0 ≤ L / 2 by linarith only [hL0])
  have hcost :
    (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * r ^ 2) / r ≤
      (5 / 3 : ℝ) * Real.log L := by
    apply (div_le_iff₀ hr).mpr
    have ht := mul_le_mul_of_nonneg_right hroot hl0
    nlinarith only [hp, ht, hl0]
  have ht :=
    sharpSigned_log_tangent
      (by
        dsimp only [L]; linarith only [hL] : 0 < L)
  have hlow :=
    signedTwoPoleGap_lower_sharp (by linarith only [hL] : 1000 ≤ Real.log A) hroot
      (show Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ Real.log A / 40 by linarith only [hlog, ht, hL])
      hd.2.2.2
  have he : (821 / 1000 : ℝ) * r - L / 2 = (33661 / 20000 : ℝ) * Real.log L + 1495041 / 100000 := by
    dsimp only [r, sharpSignedTwoPoleNegativeLogRoot]
    ring
  change
    (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * r ^ 2) / Real.sqrt (r ^ 2) <
      signedTwoPoleGap A (r ^ 2)
  rw [Real.sqrt_sq hr.le]
  linarith only [hlow, hcost, he, hl0]

/-- Under GRH, a nonprincipal quadratic character of level q at most A with
log A at least 1500 has a prime not dividing q below the sharp logarithmic cutoff
with value minus one. Apply the generic signed-gap extraction with the half-count
budget. The common ambient scale covers small conductors. -/
theorem exists_prime_neg_one_le_sharpSignedTwoPole_log_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1500 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * sharpSignedTwoPoleNegativeLogRoot (Real.log A) ^ 2 ∧
        χ p = -1 := by
  have hd := sharpSignedTwoPoleNegativeLogRoot_data hL
  exact
    exists_prime_neg_one_of_signedTwoPoleGap χ hquad hne hqA hGRH hd.1
      (sharpSignedTwoPoleGap_negative_log_dominates_cost (Nat.pos_of_ne_zero (NeZero.ne q)) hqA hL)

end PseudoPrime.LLS
