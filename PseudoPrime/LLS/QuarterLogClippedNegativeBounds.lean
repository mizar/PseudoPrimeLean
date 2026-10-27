/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FixedRampAnchor128Bounds
public import PseudoPrime.LLS.ClippedAffineWitnessBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.QuarterLogPrimeFactorBounds

/-! # A negative-prime radius retaining the clipped correction and quarter-log local cost -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The root (500/821)L+(11/10)log L+6 for negative unit-prime witnesses.
It retains the clipped principal correction, certified Euler anchor and quarter-log factor cost.
The logarithmic coefficient improves the previous 33/20 while preserving the entrance 500. -/
noncomputable def quarterClippedNegativeRoot (L : ℝ) : ℝ :=
  (500 / 821 : ℝ) * L + (11 / 10 : ℝ) * Real.log L + 6

/-- For L at least 500, the new root is at least 185 and its cutoff logarithm
is at most 2log L+1/20. Compare the root with the earlier fixed-anchor root.
These inequalities discharge the analytic scale and endpoint conditions. -/
theorem quarterClippedNegativeRoot_data {L : ℝ} (hL : 500 ≤ L) :
    185 ≤ quarterClippedNegativeRoot L ∧
      Real.log ((99 / 40 : ℝ) * quarterClippedNegativeRoot L ^ 2) ≤ 2 * Real.log L + 1 / 20 := by
  have hu := conductorPrefix_log_lower hL
  have hr : 185 ≤ quarterClippedNegativeRoot L := by
    dsimp only [quarterClippedNegativeRoot]
    linarith only [hL, hu]
  have hd := fixedAnchorNegativeRoot_data hL
  have hs :=
    mul_self_le_mul_self (by linarith only [hr] : 0 ≤ quarterClippedNegativeRoot L)
      (show quarterClippedNegativeRoot L ≤ fixedAnchorNegativeRoot L
        by
        dsimp only [quarterClippedNegativeRoot, fixedAnchorNegativeRoot]
        linarith only [hu])
  have ht :=
    Real.log_le_log
      (by nlinarith only [hr, sq_nonneg (quarterClippedNegativeRoot L - 185)] :
        0 < (99 / 40 : ℝ) * quarterClippedNegativeRoot L ^ 2)
      (show
        (99 / 40 : ℝ) * quarterClippedNegativeRoot L ^ 2 ≤
          (99 / 40 : ℝ) * fixedAnchorNegativeRoot L ^ 2
        by nlinarith only [hs])
  exact ⟨hr, ht.trans hd.2⟩

/-- For r at least 185, all normalized constant costs total at most 7/2.
Use the proved clipped numerator cap, decreasing power caps and log two.
This leaves only the ambient logarithm and local factor-count term for separation. -/
theorem quarterClipped_constant_cost_le {r : ℝ} (hr : 185 ≤ r) :
    (7417297 / 3952000 : ℝ) + 27 / r + 112 / 25 + (35 / 2 : ℝ) * r ^ (-9 / 8 : ℝ) + 1 / r ^ 3 -
          3643 / 1000 +
        5 * ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ) +
        (1 / 5 : ℝ) * Real.log 2 ≤
      (7 / 2 : ℝ) := by
  have ht := clippedAffine_tail_caps hr
  have hd :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 27) (by norm_num only : (0 : ℝ) < 185)
      hr
  linarith only [ht.1, ht.2.1, ht.2.2, hd, Real.log_two_lt_d9]

/-- For L at least 500 and u at least six, the new quadratic numerator exceeds
the quarter-logarithm local cost. Use nonnegative shifted squares and products.
This proves the full half-line comparison without finite input enumeration. -/
theorem quarterClipped_polynomial_margin {L u : ℝ} (hL : 500 ≤ L) (hu : 6 ≤ u) :
    let r := (500 / 821 : ℝ) * L + (11 / 10 : ℝ) * u + 6
    (13 / 2 + (1 / 4 : ℝ) * L) * (2 * u + 1 / 20) <
      ((162407 / 197600 : ℝ) * r - L / 2 - 7 / 2) * r - (7 / 6 : ℝ) * L := by
  dsimp only
  nlinarith only [hL, hu, sq_nonneg (L - 500), sq_nonneg (u - 6),
    mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hu)]

/-- For ambient logarithm at least 500, the corrected principal lower cap with
the full certified anchor saving exceeds the quarter-logarithm level-prime cost.
Combine the polynomial margin, endpoint estimate and decreasing error caps.
This is the scalar input to actual negative unit-prime witness extraction. -/
theorem quarterClipped_negative_gap_positive {A : ℕ} (hL : 500 ≤ Real.log A) :
    let r := quarterClippedNegativeRoot (Real.log A)
    (13 / 2 + (1 / 4 : ℝ) * Real.log A) * Real.log ((99 / 40 : ℝ) * r ^ 2) / Real.sqrt (r ^ 2) <
      clippedShiftPrincipalLower (r ^ 2) (r ^ 2 / 20) - reflectedSplitUpper A (112 / 25) (r ^ 2) +
          ((3643 / 1000 : ℝ) - 5 * ((99 / 40 : ℝ) * r ^ 2) ^ (-1 / 4 : ℝ)) -
        (1 / 5 : ℝ) * Real.log 2 := by
  let r := quarterClippedNegativeRoot (Real.log A)
  have hd := quarterClippedNegativeRoot_data hL
  have hr : 185 ≤ r := hd.1
  have hr0 : 0 < r := by linarith only [hr]
  have hm := clippedShiftPrincipalLower_ge_mass133 (r ^ 2) (r ^ 2 / 20)
  rw [Real.sqrt_sq hr0.le] at hm
  have hE := div_le_div_of_nonneg_right (clippedShiftError_twentieth_width_cap hr0) hr0.le
  have heq :
    ((231 / 24700 : ℝ) * r ^ 2 + (7417297 / 3952000 : ℝ) * r + 27) / r =
      (231 / 24700 : ℝ) * r + 7417297 / 3952000 + 27 / r := by
    field_simp (disch := exact hr0.ne')
  rw [heq, add_div] at hE
  have hC := quarterClipped_constant_cost_le hr
  have hp := quarterClipped_polynomial_margin hL (conductorPrefix_log_lower hL)
  have hc :=
    mul_le_mul_of_nonneg_left hd.2
      (show 0 ≤ 13 / 2 + (1 / 4 : ℝ) * Real.log A by linarith only [hL])
  have hsep :
    (13 / 2 + (1 / 4 : ℝ) * Real.log A) * Real.log ((99 / 40 : ℝ) * r ^ 2) / r +
        (7 / 6 : ℝ) * Real.log A / r <
      (162407 / 197600 : ℝ) * r - Real.log A / 2 - 7 / 2 := by
    rw [← add_div]
    apply (div_lt_iff₀ hr0).mpr
    dsimp only [r, quarterClippedNegativeRoot] at hc ⊢
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
  linarith only [hsep, hE, hC, hm]

/-- For quadratic nonprincipal GRH data, scale at least 25 and Euler cutoff b
at least 128 below the witness cutoff, a certified principal cap with the displayed
positive anchor gap gives a negative unit-prime witness. Insert the certified anchor
into the generic conductor comparison. This separates the principal profile from extraction. -/
theorem exists_prime_neg_one_of_principalLower_anchor128 {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C b P : ℝ} (hx : 25 ≤ x)
    (hb : 128 ≤ b) (hcut : b ≤ (99 / 40 : ℝ) * x)
    (hP :
      P ≤
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        P - reflectedSplitUpper A C x + ((3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ)) -
          (1 / 5 : ℝ) * Real.log 2) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hs : 5 ≤ Real.sqrt x := by nlinarith only [hx, Real.sq_sqrt hx0, Real.sqrt_nonneg x]
  have hp := pairedEulerPrefix_ge_anchor128 hGRH.riemann hb
  apply
    exists_prime_neg_one_of_principalLower_conductor_prefix χ hquad hne hqA hGRH
      (by linarith only [hx]) hP (Y := b) (by linarith only [hb]) (a := 3 / 10) (d :=
      (1 / 5 : ℝ) * Real.log 2) (by norm_num only)
      (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg 2)) (by linarith only [hs])
      (fun p hp ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_upper_three_tenths hp)
      (fun n hn ↦
        (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans
          ((Nat.floor_le (by linarith only [hb] : 0 ≤ b)).trans hcut))
      hC (g := (3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ) - (1 / 5 : ℝ) * Real.log 2)
      (by linarith only [hp])
  dsimp only [principalLowerGap, reflectedSplitUpper]
  dsimp only [reflectedSplitUpper] at hgap
  linarith only [hgap]

/-- Under GRH, an even quadratic nonprincipal character of level at most A has
a negative unit-prime witness through the new root cutoff when log A is at least 500.
Use the certified anchor, corrected principal cap and quarter-logarithm factor bound.
No separate numerical gap premise or finite input-range certificate remains. -/
theorem exists_prime_neg_one_le_quarterClipped_log_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (heven : χ.Even) (hne : χ ≠ 1)
    (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * quarterClippedNegativeRoot (Real.log A) ^ 2 ∧ χ p = -1 := by
  let r := quarterClippedNegativeRoot (Real.log A)
  have hd := quarterClippedNegativeRoot_data hL
  have hx : 25 ≤ r ^ 2 := by nlinarith only [hd.1, sq_nonneg (r - 185)]
  have hr0 : 0 < r ^ 2 := by linarith only [hx]
  have hP :=
    clippedShiftPrincipalLower_le_actual hGRH.riemann (by linarith only [hx] : 1 ≤ r ^ 2)
      (div_pos hr0 (by norm_num only : (0 : ℝ) < 20)) (by linarith only [hr0])
  have hc :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      χ.primitiveCharacter ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven)
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_thirteen_halves_add_quarter_log
      (Nat.pos_of_ne_zero (NeZero.ne q)) hqA
  have hlog : 0 ≤ Real.log ((99 / 40 : ℝ) * r ^ 2) := Real.log_nonneg (by linarith only [hx])
  have hcost :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hlog) (Real.sqrt_nonneg (r ^ 2))
  have hgap := quarterClipped_negative_gap_positive hL
  apply
    exists_prime_neg_one_of_principalLower_anchor128 χ hquad hne hqA hGRH hx (b :=
      (99 / 40 : ℝ) * r ^ 2) _ le_rfl hP hc (hcost.trans_lt hgap)
  nlinarith only [hd.1, sq_nonneg (r - 185)]

/-- The new root is monotone on positive real inputs. Apply logarithmic monotonicity.
This transfers the original quadratic level 4n to a common ambient input bound. -/
theorem quarterClippedNegativeRoot_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    quarterClippedNegativeRoot x ≤ quarterClippedNegativeRoot y := by
  have h := Real.log_le_log hx hxy
  dsimp only [quarterClippedNegativeRoot]
  linarith only [h, hxy]

/-- For L at least 500, the new root is strictly smaller than the old fixed-anchor root.
Keep the positive logarithm and compare its coefficients. This supplies the strict
dominance proof for the public negative-witness formula. -/
theorem quarterClippedNegativeRoot_lt_fixed {L : ℝ} (hL : 500 ≤ L) :
    quarterClippedNegativeRoot L < fixedAnchorNegativeRoot L := by
  have h := conductorPrefix_log_lower hL
  dsimp only [quarterClippedNegativeRoot, fixedAnchorNegativeRoot]
  linarith only [h]

end PseudoPrime.LLS
