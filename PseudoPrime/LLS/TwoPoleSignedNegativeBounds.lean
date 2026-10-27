/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleSignedBounds

/-! # Negative logarithmic witnesses from the signed two-pole budget -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The signed negative-witness root is the preceding logarithmic root minus eight.
Equivalently it is (500/821)L+(11/4)log L+22. The smaller constant is supplied by
the nonpositive archimedean contribution and conductor-free left allowance. -/
noncomputable def signedTwoPoleNegativeLogRoot (L : ℝ) : ℝ :=
  twoPoleNegativeLogRoot L - 8

/-- On positive real inputs, the signed negative root is monotone. Subtract eight
from the monotone preceding root. This transfers a common ambient logarithm. -/
theorem signedTwoPoleNegativeLogRoot_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    signedTwoPoleNegativeLogRoot x ≤ signedTwoPoleNegativeLogRoot y := by
  exact sub_le_sub_right (twoPoleNegativeLogRoot_mono hx hxy) 8

/-- At real L at least 2000, the signed negative root is at most 631L/1000.
Use the global logarithmic tangent. This supplies endpoint and radius enclosures. -/
theorem signedTwoPoleNegativeLogRoot_le_linear {L : ℝ} (hL : 2000 ≤ L) :
    signedTwoPoleNegativeLogRoot L ≤ (631 / 1000 : ℝ) * L := by
  have ht := twoPole_log_tangent (by linarith only [hL] : 0 < L)
  dsimp only [signedTwoPoleNegativeLogRoot, twoPoleNegativeLogRoot]
  linarith only [ht, hL]

/-- At L at least 2000, the signed negative logarithmic root gives scale at least
four, lower root 3L/5+18, cutoff log at most 2log L and second endpoint log at most
L/40. These continuous bounds control both principal errors and prime-count cost. -/
theorem signedTwoPoleNegativeLogRoot_data {L : ℝ} (hL : 2000 ≤ L) :
    4 ≤ signedTwoPoleNegativeLogRoot L ^ 2 ∧
      (3 / 5 : ℝ) * L + 18 ≤ signedTwoPoleNegativeLogRoot L ∧
      Real.log ((99 / 40 : ℝ) * signedTwoPoleNegativeLogRoot L ^ 2) ≤ 2 * Real.log L ∧
      Real.log ((101 / 40 : ℝ) * signedTwoPoleNegativeLogRoot L ^ 2) ≤ L / 40 := by
  have hl0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hL])
  have ht := twoPole_log_tangent (by linarith only [hL] : 0 < L)
  have hlo : (3 / 5 : ℝ) * L + 18 ≤ signedTwoPoleNegativeLogRoot L := by
    dsimp only [signedTwoPoleNegativeLogRoot, twoPoleNegativeLogRoot]
    linarith only [hL, hl0]
  have hhi := signedTwoPoleNegativeLogRoot_le_linear hL
  have hr : 0 ≤ signedTwoPoleNegativeLogRoot L := by linarith only [hlo, hL]
  have hx : 4 ≤ signedTwoPoleNegativeLogRoot L ^ 2 := by
    nlinarith only [hlo, hL, sq_nonneg (signedTwoPoleNegativeLogRoot L - 2)]
  have hs := mul_self_le_mul_self hr hhi
  have hLp : 0 < L := by linarith only [hL]
  have ha : Real.log ((99 / 40 : ℝ) * signedTwoPoleNegativeLogRoot L ^ 2) ≤ 2 * Real.log L := by
    have h :=
      Real.log_le_log
        (by nlinarith only [hx] : 0 < (99 / 40 : ℝ) * signedTwoPoleNegativeLogRoot L ^ 2)
        (show (99 / 40 : ℝ) * signedTwoPoleNegativeLogRoot L ^ 2 ≤ L ^ 2 by nlinarith only [hs])
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hb : Real.log ((101 / 40 : ℝ) * signedTwoPoleNegativeLogRoot L ^ 2) ≤ L / 40 := by
    have h :=
      Real.log_le_log
        (by nlinarith only [hx] : 0 < (101 / 40 : ℝ) * signedTwoPoleNegativeLogRoot L ^ 2)
        (show (101 / 40 : ℝ) * signedTwoPoleNegativeLogRoot L ^ 2 ≤ (101 / 100 : ℝ) * L ^ 2 by
          nlinarith only [hs])
    rw [Real.log_mul (by norm_num only : (101 / 100 : ℝ) ≠ 0) (pow_ne_zero 2 hLp.ne'),
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have hc := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 101 / 100)
    linarith only [h, hc, ht, hL]
  exact ⟨hx, hlo, ha, hb⟩

/-- For positive q at most A with log A at least 2000, the signed gap at the
negative logarithmic root exceeds the original level's prime-count local cost.
Retain cost (20/9)log log A and the positive signed-gap margin. This is unconditional. -/
theorem signedTwoPoleGap_negative_log_dominates_cost {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A)
    (hL : 2000 ≤ Real.log A) :
    (q.primeFactors.card : ℝ) *
          Real.log ((99 / 40 : ℝ) * signedTwoPoleNegativeLogRoot (Real.log A) ^ 2) /
        Real.sqrt (signedTwoPoleNegativeLogRoot (Real.log A) ^ 2) <
      signedTwoPoleGap A (signedTwoPoleNegativeLogRoot (Real.log A) ^ 2) := by
  let L := Real.log A
  let r := signedTwoPoleNegativeLogRoot L
  have hd := signedTwoPoleNegativeLogRoot_data hL
  have hL0 : 0 ≤ L := by
    dsimp only [L]; linarith only [hL]
  have hl0 : 0 ≤ Real.log L :=
    Real.log_nonneg
      (by
        dsimp only [L]; linarith only [hL])
  have hroot : (3 / 5 : ℝ) * L + 18 ≤ r := hd.2.1
  have hr : 0 < r := by linarith only [hroot, hL0]
  have hcard := twoPole_prime_count_ambient hq hqA (by linarith only [hL] : 45 ≤ Real.log A)
  have hlog : Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ 2 * Real.log L := hd.2.2.1
  have hx4 : 4 ≤ r ^ 2 := hd.1
  have hlog0 : 0 ≤ Real.log ((99 / 40 : ℝ) * r ^ 2) := Real.log_nonneg (by nlinarith only [hx4])
  have hp := mul_le_mul hcard hlog hlog0 (show 0 ≤ (2 / 3 : ℝ) * L by linarith only [hL0])
  have hcost :
    (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * r ^ 2) / r ≤
      (20 / 9 : ℝ) * Real.log L := by
    apply (div_le_iff₀ hr).mpr
    have ht := mul_le_mul_of_nonneg_right hroot hl0
    nlinarith only [hp, ht, hl0]
  have ht :=
    twoPole_log_tangent
      (by
        dsimp only [L]; linarith only [hL] : 0 < L)
  have hlow :=
    signedTwoPoleGap_lower (by linarith only [hL] : 1500 ≤ Real.log A) hroot
      (show Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ Real.log A / 40 by linarith only [hlog, ht, hL])
      hd.2.2.2
  have he : (821 / 1000 : ℝ) * r - L / 2 = (9031 / 4000 : ℝ) * Real.log L + 9031 / 500 := by
    dsimp only [r, signedTwoPoleNegativeLogRoot, twoPoleNegativeLogRoot]
    ring
  change
    (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * r ^ 2) / Real.sqrt (r ^ 2) <
      signedTwoPoleGap A (r ^ 2)
  rw [Real.sqrt_sq hr.le]
  linarith only [hlow, hcost, he, hl0]

/-- Under GRH, a nonprincipal quadratic character of level q at most A with
log A at least 2000 has a prime not dividing q below the signed logarithmic cutoff
with value minus one. Insert the certified cost comparison into witness extraction. -/
theorem exists_prime_neg_one_le_signedTwoPole_log_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 2000 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * signedTwoPoleNegativeLogRoot (Real.log A) ^ 2 ∧ χ p = -1 := by
  have hd := signedTwoPoleNegativeLogRoot_data hL
  exact
    exists_prime_neg_one_of_signedTwoPoleGap χ hquad hne hqA hGRH hd.1
      (signedTwoPoleGap_negative_log_dominates_cost (Nat.pos_of_ne_zero (NeZero.ne q)) hqA hL)

end PseudoPrime.LLS
