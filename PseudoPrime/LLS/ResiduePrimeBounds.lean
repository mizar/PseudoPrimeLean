/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ResidueGapNumerics

/-!
# Least-prime bound in large reduced residue classes

At the totient-logarithm cutoff, absorb principal and nonprincipal errors into the
strict arithmetic-progression gap. This proves the large-modulus part of Corollary 1.2.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a modulus at least twenty thousand, its prime-factor count is at most
its real logarithm. Take logarithms in the proved three-sevenths power estimate
and use the logarithm-of-two lower bound. This controls the principal correction. -/
private theorem card_primeFactors_le_log_of_large {q : ℕ} (hq : 20000 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ Real.log q := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide) hq)
  have hb :=
    Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 2) _)
      (NumberTheory.two_pow_card_primeFactors_le_rpow hq)
  rw [Real.log_pow, Real.log_rpow hq0] at hb
  have hk :=
    mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ Real.log 2 by linarith only [Real.log_two_gt_d9])
      (Nat.cast_nonneg q.primeFactors.card : (0 : ℝ) ≤ _)
  have hl : 0 ≤ Real.log q :=
    Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 20000).trans (Nat.cast_le.mpr hq))
  linarith only [hb, hk, hl]

/-- For a modulus at least twenty thousand, its logarithm is at most thirteen
over five thousand times its totient. Combine the uniform logarithm-to-power
ratio with the totient power bound. This scales the cutoff logarithm errors. -/
private theorem log_modulus_le_totient_fraction {q : ℕ} (hq : 20000 ≤ q) :
    Real.log q ≤ (13 / 5000 : ℝ) * q.totient := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide) hq)
  have hb :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hq0 (5 / 6 : ℝ))).mp
      (log_div_rpow_five_sixths_le (Nat.cast_le.mpr hq))
  exact
    hb.trans
      (mul_le_mul_of_nonneg_left (NumberTheory.rpow_five_sixths_le_totient hq)
        (by norm_num only : (0 : ℝ) ≤ 13 / 5000))

/-- For a totient scale at least 4156 and a nonnegative square-root cutoff
equal to that scale times the modulus logarithm, absorb a common error of four
over 125 into the main nonprincipal term. The endpoint coefficient leaves the
explicit saving 987 over 1000. This supplies the first part of the norm majorant. -/
private theorem nonprincipal_main_scaled_bound {h s L E : ℝ} (hh : 4156 ≤ h) (hs : 0 ≤ s)
    (hL : 0 ≤ L) (hsL : s = h * L) (hE : E ≤ (4 / 125 : ℝ) * s) :
    (h - 1) * ((s + 19 / 6) * (L - 51 / 50) + E) ≤ (h - 1) * s * L - (987 / 1000 : ℝ) * h * s := by
  have hh1 : 0 ≤ h - 1 := by linarith only [hh]
  have he := mul_le_mul_of_nonneg_left hE hh1
  have hep : (h - 1) * (19 / 6 : ℝ) * (L - 51 / 50) ≤ (19 / 6 : ℝ) * s := by
    have h1 : (h - 1) * L ≤ s := by
      rw [hsL]; nlinarith only [hL]
    have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num only : (0 : ℝ) ≤ 19 / 6)
    nlinarith only [h2, hh1]
  have hc : (247 / 250 + 19 / 6 : ℝ) ≤ (1 / 1000 : ℝ) * h := by linarith only [hh]
  have hsmall := mul_le_mul_of_nonneg_right hc hs
  nlinarith only [he, hep, hsmall]

/-- For the certified totient and cutoff scales, a bounded cutoff logarithm,
nonnegative Euler constant and small endpoint correction, the reciprocal term
is at most seven over five hundred times the product of the scales.
This bounds the remaining nonprincipal contribution. -/
private theorem reciprocal_scaled_bound {h s L t g u : ℝ} (hh : 4156 ≤ h) (hs : 37404 ≤ s)
    (hL : L ≤ (13 / 5000 : ℝ) * h) (ht : t ≤ (5 / 2 : ℝ) * L) (hg : 0 ≤ g) (hu : u ≤ 1 / 100000) :
    2 * (s + 19 / 6) * (t - (1 + g) + u) ≤ (7 / 500 : ℝ) * h * s := by
  have hs0 : 0 ≤ s := by linarith only [hs]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hi : t - (1 + g) + u ≤ (651 / 100000 : ℝ) * h := by linarith only [ht, hL, hg, hu, hh]
  have hp : s + 19 / 6 ≤ (10001 / 10000 : ℝ) * s := by linarith only [hs]
  have ha := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * (s + 19 / 6) by linarith only [hs])
  have hb :=
    mul_le_mul_of_nonneg_right hp (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 651 / 100000) hh0)
  nlinarith only [ha, hb, mul_nonneg hh0 hs0]

/-- At the totient-logarithm cutoff for a nonzero modulus at least twenty thousand,
the nonprincipal majorant is below its leading term by 97 over 100 times the totient
and square-root scale. Absorb the common norm and reciprocal errors using the
proved numerical certificates. This supplies the upper side of the final residue gap. -/
theorem residue_cutoff_nonprincipal_upper_le {q : ℕ} [NeZero q] (hq : 20000 ≤ q) :
    cosetNonprincipalUpper q ⊥ (((q.totient : ℝ) * Real.log q) ^ 2) ≤
      ((q.totient : ℝ) - 1) * ((q.totient : ℝ) * Real.log q) * Real.log q -
        (97 / 100 : ℝ) * (q.totient : ℝ) * ((q.totient : ℝ) * Real.log q) := by
  let h : ℝ := q.totient
  let L : ℝ := Real.log q
  let s : ℝ := h * L
  let X : ℝ := s ^ 2
  have hh : (4156 : ℝ) ≤ h := Nat.cast_le.mpr (NumberTheory.totient_ge_4156 hq)
  have hl : (9 : ℝ) ≤ L :=
    log_twenty_thousand_bounds.1.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hq))
  have hh0 : 0 ≤ h := (by norm_num only : (0 : ℝ) ≤ 4156).trans hh
  have hl0 : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 9).trans hl
  have hs : (37404 : ℝ) ≤ s := by
    have hb := mul_le_mul hh hl (by norm_num only : (0 : ℝ) ≤ 9) hh0
    norm_num only at hb
    exact hb
  have hs0 : 0 ≤ s := (by norm_num only : (0 : ℝ) ≤ 37404).trans hs
  have hx : (1000000000 : ℝ) ≤ X := residue_cutoff_ge_billion hq
  have hx0 : 0 < X := lt_of_lt_of_le (by norm_num only) hx
  have hE : cosetCharacterNormError q X ≤ (4 / 125 : ℝ) * s := by
    have he := residue_cutoff_character_norm_error_le hq
    change cosetCharacterNormError q X ≤ (4 / 125 : ℝ) * Real.sqrt (s ^ 2) at he
    rwa [Real.sqrt_sq hs0] at he
  have hu1 : Real.log (2 * Real.pi) / X ≤ 2 / 1000000000 :=
    (div_le_div_of_nonneg_right
          (show Real.log (2 * Real.pi) ≤ (2 : ℝ) by linarith only [Analysis.log_two_mul_pi_lt])
          hx0.le).trans
      (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 2)
        (by norm_num only : (0 : ℝ) < 1000000000) hx)
  have hu2 : 1 / (20 * s) ≤ (1 / 748080 : ℝ) :=
    div_le_div_of_nonneg_left zero_le_one (by norm_num only)
      (by linarith only [hs] : (748080 : ℝ) ≤ 20 * s)
  have hu : Real.log (2 * Real.pi) / X + 1 / (20 * s) ≤ (1 / 100000 : ℝ) := by
    linarith only [hu1, hu2]
  have hg : 0 ≤ Real.eulerMascheroniConstant := by
    linarith only [Analysis.twentyThree_fortieths_lt_eulerMascheroniConstant]
  have hmain := nonprincipal_main_scaled_bound hh hs0 hl0 rfl hE
  have hrec :=
    reciprocal_scaled_bound hh hs (log_modulus_le_totient_fraction hq) (residue_cutoff_log_le hq) hg
      hu
  have hi : (⊥ : Subgroup (ZMod q)ˣ).index = q.totient := by
    rw [Subgroup.index_bot, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  unfold cosetNonprincipalUpper
  rw [hi, Real.sqrt_sq hs0]
  change
    (h - 1) * ((s + 19 / 6) * (L - 51 / 50) + cosetCharacterNormError q X) +
        2 * (s + 19 / 6) *
          (Real.log X - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / X +
            1 / (20 * s)) ≤
      (h - 1) * s * L - (97 / 100 : ℝ) * h * s
  nlinarith only [hmain, hrec, mul_nonneg hh0 hs0]

/-- For the certified totient and cutoff scales, the principal correction is
at most one thousandth of their product. Bound the endpoint terms linearly and
the prime-factor squared-logarithm term by the cubed modulus logarithm.
The logarithm-to-totient ratio absorbs that cubic term. -/
private theorem principal_error_scaled_bound {h s L t k P : ℝ} (hh : 4156 ≤ h) (hs : 37404 ≤ s)
    (hL0 : 0 ≤ L) (hsL : s = h * L) (hL : L ≤ (13 / 5000 : ℝ) * h) (ht0 : 0 ≤ t)
    (ht : t ≤ (5 / 2 : ℝ) * L) (hk : k ≤ L) (hP : P ≤ 2) :
    P * t + 1 + (s + 1) / 20 + (1 / 2 : ℝ) * k * t ^ 2 ≤ (1 / 1000 : ℝ) * h * s := by
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hs0 : 0 ≤ s := by linarith only [hs]
  have hpt := mul_le_mul hP ht ht0 (by norm_num only : (0 : ℝ) ≤ 2)
  have h500 := mul_le_mul_of_nonneg_right (show (500 : ℝ) ≤ h by linarith only [hh]) hL0
  rw [← hsL] at h500
  have hsmall : P * t + 1 + (s + 1) / 20 ≤ (11 / 100 : ℝ) * s := by linarith only [hpt, h500, hs]
  have hsmallScaled :=
    mul_le_mul_of_nonneg_right (show (11 / 100 : ℝ) ≤ (1 / 10000 : ℝ) * h by linarith only [hh]) hs0
  have hT2 : t ^ 2 ≤ ((5 / 2 : ℝ) * L) ^ 2 := by
    simpa only [← pow_two] using mul_self_le_mul_self ht0 ht
  have hkT := mul_le_mul hk hT2 (sq_nonneg t) hL0
  have hLL : L ^ 2 ≤ ((13 / 5000 : ℝ) * h) ^ 2 := by
    simpa only [← pow_two] using mul_self_le_mul_self hL0 hL
  have hcubic := mul_le_mul_of_nonneg_right hLL hL0
  have hhs : h * s = h ^ 2 * L := by
    rw [hsL]; ring
  have hkBound : (1 / 2 : ℝ) * k * t ^ 2 ≤ (1 / 10000 : ℝ) * h * s := by
    rw [mul_assoc (1 / 10000 : ℝ) h s, hhs]
    nlinarith only [hkT, hcubic, mul_nonneg (sq_nonneg h) hL0]
  nlinarith only [hsmall, hsmallScaled, hkBound, mul_nonneg hh0 hs0]

/-- At the totient-logarithm cutoff for a modulus at least twenty thousand,
the principal lower majorant loses at most one thousandth of the totient times
the square-root scale. Insert the certified scales and prime-factor count into
the scaled error estimate. This supplies the lower side of the final residue gap. -/
theorem residue_cutoff_principal_lower_ge {q : ℕ} (hq : 20000 ≤ q) :
    ((q.totient : ℝ) * Real.log q) ^ 2 -
        (1 / 1000 : ℝ) * (q.totient : ℝ) * ((q.totient : ℝ) * Real.log q) ≤
      cosetPrincipalLower q (((q.totient : ℝ) * Real.log q) ^ 2) := by
  let h : ℝ := q.totient
  let L : ℝ := Real.log q
  let s : ℝ := h * L
  let X : ℝ := s ^ 2
  have hh : (4156 : ℝ) ≤ h := Nat.cast_le.mpr (NumberTheory.totient_ge_4156 hq)
  have hl : (9 : ℝ) ≤ L :=
    log_twenty_thousand_bounds.1.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hq))
  have hh0 : 0 ≤ h := (by norm_num only : (0 : ℝ) ≤ 4156).trans hh
  have hl0 : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 9).trans hl
  have hs : (37404 : ℝ) ≤ s := by
    have hb := mul_le_mul hh hl (by norm_num only : (0 : ℝ) ≤ 9) hh0
    norm_num only at hb
    exact hb
  have hs0 : 0 ≤ s := (by norm_num only : (0 : ℝ) ≤ 37404).trans hs
  have ht0 : 0 ≤ Real.log X :=
    Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 1000000000).trans (residue_cutoff_ge_billion hq))
  have hP : Real.log (2 * Real.pi) ≤ (2 : ℝ) := by linarith only [Analysis.log_two_mul_pi_lt]
  have he :=
    principal_error_scaled_bound hh hs hl0 rfl (log_modulus_le_totient_fraction hq) ht0
      (residue_cutoff_log_le hq) (card_primeFactors_le_log_of_large hq) hP
  unfold cosetPrincipalLower
  rw [Real.sqrt_sq hs0]
  change
    X - (1 / 1000 : ℝ) * h * s ≤
      X - Real.log (2 * Real.pi) * Real.log X - 1 - (s + 1) / 20 -
        (1 / 2 : ℝ) * (q.primeFactors.card : ℝ) * (Real.log X) ^ 2
  linarith only [he]

/-- Under GRH, every unit residue class of a nonzero modulus at least twenty thousand
has its least prime at most the square of the totient times the modulus logarithm.
At this cutoff the normalized square and odd-prime-power upper bounds, together
with the nonprincipal estimate, lie strictly below the principal lower estimate.
Apply the proved residue gap criterion. This proves the large-modulus part of Corollary 1.2. -/
theorem exists_least_prime_in_residue_le_totient_log_sq_of_large {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hq : 20000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  let h : ℝ := q.totient
  let L : ℝ := Real.log q
  let s : ℝ := h * L
  let X : ℝ := s ^ 2
  have hh : (4156 : ℝ) ≤ h := Nat.cast_le.mpr (NumberTheory.totient_ge_4156 hq)
  have hl : (9 : ℝ) ≤ L :=
    log_twenty_thousand_bounds.1.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hq))
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num only) hh
  have hl0 : 0 < L := lt_of_lt_of_le (by norm_num only) hl
  have hs0 : 0 < s := mul_pos hh0 hl0
  apply exists_least_prime_in_residue_le_of_rpow_gap a hq hGRH (residue_cutoff_ge_billion hq)
  have hU := residue_cutoff_square_prime_power_normalized_le hq
  have hm := mul_le_mul_of_nonneg_right hU hs0.le
  have hcancel : (s / (q : ℝ) + 1) = (1 / (q : ℝ) + 1 / s) * s := by
    rw [add_mul, div_mul_cancel₀ _ hs0.ne']
    ring
  have hSquare :
    (q : ℝ) ^ (3 / 7 : ℝ) * (Real.log X) ^ 2 / 4 * (s / q + 1) ≤ (263 / 320 : ℝ) * s := by
    rw [hcancel]
    rw [← mul_assoc]
    exact hm
  have hUp := mul_le_mul_of_nonneg_left hSquare hh0.le
  have hNon := residue_cutoff_nonprincipal_upper_le hq
  have hPri := residue_cutoff_principal_lower_ge hq
  have hMain : (h - 1) * s * L ≤ X := by
    change (h - 1) * (h * L) * L ≤ (h * L) ^ 2
    nlinarith only [mul_pos hh0 hl0, hl0]
  rw [Real.sqrt_sq hs0.le]
  change
    h * ((q : ℝ) ^ (3 / 7 : ℝ) * (Real.log X) ^ 2 / 4 * (s / q + 1) + s / 7) +
        cosetNonprincipalUpper q ⊥ X <
      cosetPrincipalLower q X
  change cosetNonprincipalUpper q ⊥ X ≤ (h - 1) * s * L - (97 / 100 : ℝ) * h * s at hNon
  change X - (1 / 1000 : ℝ) * h * s ≤ cosetPrincipalLower q X at hPri
  nlinarith only [hUp, hNon, hPri, hMain, mul_pos hh0 hs0]

end PseudoPrime.LLS.PaperStatements
