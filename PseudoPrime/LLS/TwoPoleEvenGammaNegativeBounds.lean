/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleConstantBounds
public import PseudoPrime.LLS.TwoPoleSignedSharpNegativeBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorAmbientBounds

/-! # Negative witnesses with a half-logarithmic prime-count budget -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The negative root (500/821)L+(41/20)log L+1349/100. The smaller logarithmic
coefficient uses the ambient prime-count bound log(A)/2, and the additive constant
uses the direct signed error bound. Apply at log B+7/5 for Jacobi witnesses. -/
noncomputable def evenGammaTwoPoleNegativeLogRoot (L : ℝ) : ℝ :=
  (500 / 821 : ℝ) * L + (41 / 20 : ℝ) * Real.log L + 1349 / 100

/-- The sharp negative root is monotone on positive real inputs. Use log
monotonicity and the positive coefficients. This transfers ambient logarithms. -/
theorem evenGammaTwoPoleNegativeLogRoot_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    evenGammaTwoPoleNegativeLogRoot x ≤ evenGammaTwoPoleNegativeLogRoot y := by
  have h := Real.log_le_log hx hxy
  dsimp only [evenGammaTwoPoleNegativeLogRoot]
  linarith only [h, hxy]

/-- For L at least 1250, the sharp negative root is at most 6317L/10000.
Apply the global tangent to the logarithmic correction. This bounds the endpoints
and compares the resulting witness radius with the logarithmic square. -/
theorem evenGammaTwoPoleNegativeLogRoot_le_linear {L : ℝ} (hL : 1250 ≤ L) :
    evenGammaTwoPoleNegativeLogRoot L ≤ (6317 / 10000 : ℝ) * L := by
  have ht := sharpSigned_log_tangent (by linarith only [hL] : 0 < L)
  dsimp only [evenGammaTwoPoleNegativeLogRoot]
  linarith only [ht, hL]

/-- For L at least 1250, the sharp negative root gives scale at least four,
lower root 3L/5+18, cutoff log at most 2log L and second endpoint log at most L/40.
Use a rational root enclosure and the global tangent on the entire half-line. -/
theorem evenGammaTwoPoleNegativeLogRoot_data {L : ℝ} (hL : 1250 ≤ L) :
    4 ≤ evenGammaTwoPoleNegativeLogRoot L ^ 2 ∧
      (3 / 5 : ℝ) * L + 18 ≤ evenGammaTwoPoleNegativeLogRoot L ∧
      Real.log ((99 / 40 : ℝ) * evenGammaTwoPoleNegativeLogRoot L ^ 2) ≤ 2 * Real.log L ∧
      Real.log ((101 / 40 : ℝ) * evenGammaTwoPoleNegativeLogRoot L ^ 2) ≤ L / 40 := by
  have hl0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hL])
  have ht := sharpSigned_log_tangent (by linarith only [hL] : 0 < L)
  have hlo : (3 / 5 : ℝ) * L + 18 ≤ evenGammaTwoPoleNegativeLogRoot L := by
    dsimp only [evenGammaTwoPoleNegativeLogRoot]
    linarith only [hL, hl0]
  have hhi := evenGammaTwoPoleNegativeLogRoot_le_linear hL
  have hr : 0 ≤ evenGammaTwoPoleNegativeLogRoot L := by linarith only [hlo, hL]
  have hx : 4 ≤ evenGammaTwoPoleNegativeLogRoot L ^ 2 := by
    nlinarith only [hlo, hL, sq_nonneg (evenGammaTwoPoleNegativeLogRoot L - 2)]
  have hs := mul_self_le_mul_self hr hhi
  have hLp : 0 < L := by linarith only [hL]
  have ha : Real.log ((99 / 40 : ℝ) * evenGammaTwoPoleNegativeLogRoot L ^ 2) ≤ 2 * Real.log L := by
    have h :=
      Real.log_le_log
        (by nlinarith only [hx] : 0 < (99 / 40 : ℝ) * evenGammaTwoPoleNegativeLogRoot L ^ 2)
        (show (99 / 40 : ℝ) * evenGammaTwoPoleNegativeLogRoot L ^ 2 ≤ L ^ 2 by nlinarith only [hs])
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hb : Real.log ((101 / 40 : ℝ) * evenGammaTwoPoleNegativeLogRoot L ^ 2) ≤ L / 40 := by
    have h :=
      Real.log_le_log
        (by nlinarith only [hx] : 0 < (101 / 40 : ℝ) * evenGammaTwoPoleNegativeLogRoot L ^ 2)
        (show (101 / 40 : ℝ) * evenGammaTwoPoleNegativeLogRoot L ^ 2 ≤ (101 / 100 : ℝ) * L ^ 2 by
          nlinarith only [hs])
    rw [Real.log_mul (by norm_num only : (101 / 100 : ℝ) ≠ 0) (pow_ne_zero 2 hLp.ne'),
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have hc := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 101 / 100)
    linarith only [h, hc, ht, hL]
  exact ⟨hx, hlo, ha, hb⟩

/-- For positive q at most A with log A at least 1250, the signed gap at the
sharp negative root exceeds the actual prime-count local cost. Bound omega(q) by
log(A)/2 and the cost by (5/3)log log A, then use the direct signed-gap lower bound.
No RH is required for this scalar separation. -/
theorem evenGammaTwoPoleGap_negative_log_dominates_cost {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A)
    (hL : 1250 ≤ Real.log A) :
    (q.primeFactors.card : ℝ) *
          Real.log ((99 / 40 : ℝ) * evenGammaTwoPoleNegativeLogRoot (Real.log A) ^ 2) /
        Real.sqrt (evenGammaTwoPoleNegativeLogRoot (Real.log A) ^ 2) <
      twoPoleConstantGap A (112 / 25) (evenGammaTwoPoleNegativeLogRoot (Real.log A) ^ 2) := by
  let L := Real.log A
  let r := evenGammaTwoPoleNegativeLogRoot L
  have hd := evenGammaTwoPoleNegativeLogRoot_data hL
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
    twoPoleConstantGap_lower (C := 112 / 25) (by linarith only [hL] : 800 ≤ Real.log A) hroot
      (show Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ Real.log A / 40 by linarith only [hlog, ht, hL])
      hd.2.2.2
  have he : (821 / 1000 : ℝ) * r - L / 2 = (33661 / 20000 : ℝ) * Real.log L + 1107529 / 100000 := by
    dsimp only [r, evenGammaTwoPoleNegativeLogRoot]
    ring
  change
    (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * r ^ 2) / Real.sqrt (r ^ 2) <
      twoPoleConstantGap A (112 / 25) (r ^ 2)
  rw [Real.sqrt_sq hr.le]
  linarith only [hlow, hcost, he, hl0]

/-- Under GRH, a nonprincipal quadratic character of level q at most A with
log A at least 1250 has a prime not dividing q below the sharp logarithmic cutoff
with value minus one. Apply the generic signed-gap extraction with the half-count
budget. The common ambient scale covers small conductors. -/
theorem exists_prime_neg_one_le_evenGammaTwoPole_log_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (heven : χ.Even) (hne : χ ≠ 1)
    (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 1250 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * evenGammaTwoPoleNegativeLogRoot (Real.log A) ^ 2 ∧ χ p = -1 := by
  have hd := evenGammaTwoPoleNegativeLogRoot_data hL
  exact
    exists_prime_neg_one_of_twoPoleConstantGap χ hquad hne hqA hGRH hd.1
      (AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
        χ.primitiveCharacter ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven))
      (evenGammaTwoPoleGap_negative_log_dominates_cost (Nat.pos_of_ne_zero (NeZero.ne q)) hqA hL)

end PseudoPrime.LLS
