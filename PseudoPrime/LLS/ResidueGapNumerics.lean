/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import PseudoPrime.Analysis.NumericalLogBounds
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.NumberTheory.TotientComputation
public import PseudoPrime.LLS.ResidueWeightedBounds

/-!
# Numerical certificates for the arithmetic-progression gap

Transfer logarithmic and fractional-power base certificates at modulus twenty thousand
to the uniform normalized error bounds used in LLS Section 4.1.
For smaller moduli, certify the finite exponent range and replace logarithms,
square roots and character errors by rational interval bounds. A strict rational
gap then implies the least-prime bound through the root-certificate criterion.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The logarithm of twenty thousand lies between nine and 991 over 100.
Use the logarithm of three to evaluate the nearby ninth power 19683 and the tangent
upper bound for the remaining difference. This certifies the modulus base. -/
theorem log_twenty_thousand_bounds : (9 : ℝ) ≤ Real.log 20000 ∧ Real.log 20000 ≤ 991 / 100 := by
  have hl :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 19683) (by norm_num only : (19683 : ℝ) ≤ 20000)
  have hu :=
    Analysis.log_le_log_add_sub_div (a := (19683 : ℝ)) (y := 20000) (by norm_num only)
      (by norm_num only)
  rw [show (19683 : ℝ) = 3 ^ 9 by norm_num only, Real.log_pow] at hl hu
  norm_num only at hl hu
  constructor <;> linarith only [hl, hu, Real.log_three_gt_d9, Real.log_three_lt_d9]

/-- The four-sevenths power of twenty thousand is at least 286.
Raise both nonnegative sides to the seventh power and check an integer inequality.
This supplies the denominator certificate for the squared-logarithm error. -/
theorem twenty_thousand_rpow_four_sevenths_ge : (286 : ℝ) ≤ (20000 : ℝ) ^ (4 / 7 : ℝ) := by
  apply
    (Real.rpow_le_rpow_iff (by norm_num only : (0 : ℝ) ≤ 286)
        (Real.rpow_nonneg (by norm_num only) _) (by norm_num only : (0 : ℝ) < 7)).mp
  rw [← Real.rpow_mul (by norm_num only : (0 : ℝ) ≤ 20000)]
  norm_num only

/-- The seventeen-fortyseconds power of twenty thousand is at least 55.
Raise both sides to the forty-second power and check the integer inequality.
This supplies the denominator certificate for the mixed prime-power error. -/
theorem twenty_thousand_rpow_seventeen_fortyseconds_ge :
    (55 : ℝ) ≤ (20000 : ℝ) ^ (17 / 42 : ℝ) := by
  apply
    (Real.rpow_le_rpow_iff (by norm_num only : (0 : ℝ) ≤ 55) (Real.rpow_nonneg (by norm_num only) _)
        (by norm_num only : (0 : ℝ) < 42)).mp
  rw [← Real.rpow_mul (by norm_num only : (0 : ℝ) ≤ 20000)]
  norm_num only

/-- The five-sixths power of twenty thousand is at least 3830.
Raise both sides to the sixth power and check the integer inequality.
This supplies the denominator certificate for the character-average error. -/
theorem twenty_thousand_rpow_five_sixths_ge : (3830 : ℝ) ≤ (20000 : ℝ) ^ (5 / 6 : ℝ) := by
  apply
    (Real.rpow_le_rpow_iff (by norm_num only : (0 : ℝ) ≤ 3830)
        (Real.rpow_nonneg (by norm_num only) _) (by norm_num only : (0 : ℝ) < 6)).mp
  rw [← Real.rpow_mul (by norm_num only : (0 : ℝ) ≤ 20000)]
  norm_num only

/-- For a positive exponent whose reciprocal is at most nine and a real modulus
at least twenty thousand, a positive lower bound for the base power gives an upper
bound for the logarithm divided by that power. Use antitonicity beyond the base
and the certified logarithm upper bound. This transfers the two linear-log errors. -/
private theorem log_div_rpow_le_base_certificate {a q B : ℝ} (ha : 0 < a) (ha9 : a⁻¹ ≤ 9)
    (hq : 20000 ≤ q) (hB : 0 < B) (hb : B ≤ (20000 : ℝ) ^ a) :
    Real.log q / q ^ a ≤ (991 / 100 : ℝ) / B := by
  have he : Real.exp a⁻¹ ≤ 20000 :=
    (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 20000)).mp
      (ha9.trans log_twenty_thousand_bounds.1)
  have ht := Real.log_div_self_rpow_antitoneOn ha he (he.trans hq) hq
  exact
    ht.trans
      ((div_le_div_of_nonneg_left
            ((by norm_num only : (0 : ℝ) ≤ 9).trans log_twenty_thousand_bounds.1) hB hb).trans
        (div_le_div_of_nonneg_right log_twenty_thousand_bounds.2 hB.le))

/-- Above modulus twenty thousand, the logarithm divided by the seventeen-fortyseconds
power is at most 181 over 1000. Transfer the base certificates by antitonicity.
This controls the square-prime-power term relative to the totient cutoff. -/
theorem log_div_rpow_seventeen_fortyseconds_le {q : ℝ} (hq : 20000 ≤ q) :
    Real.log q / q ^ (17 / 42 : ℝ) ≤ 181 / 1000 := by
  exact
    (log_div_rpow_le_base_certificate (by norm_num only : (0 : ℝ) < 17 / 42) (by norm_num only) hq
          (by norm_num only) twenty_thousand_rpow_seventeen_fortyseconds_ge).trans
      (by norm_num only)

/-- Above modulus twenty thousand, the logarithm divided by the five-sixths power
is at most thirteen over five thousand. Transfer the base certificates by antitonicity.
This controls the nonprincipal error relative to the totient cutoff. -/
theorem log_div_rpow_five_sixths_le {q : ℝ} (hq : 20000 ≤ q) :
    Real.log q / q ^ (5 / 6 : ℝ) ≤ 13 / 5000 := by
  exact
    (log_div_rpow_le_base_certificate (by norm_num only : (0 : ℝ) < 5 / 6) (by norm_num only) hq
          (by norm_num only) twenty_thousand_rpow_five_sixths_ge).trans
      (by norm_num only)

/-- Above modulus twenty thousand, the squared logarithm divided by the four-sevenths
power is at most 69 over 200. Square the nonnegative antitone two-sevenths ratio
and apply the base certificates. This controls the square-root-count term. -/
theorem log_sq_div_rpow_four_sevenths_le {q : ℝ} (hq : 20000 ≤ q) :
    (Real.log q) ^ 2 / q ^ (4 / 7 : ℝ) ≤ 69 / 200 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num only) hq
  have hl0 : 0 ≤ Real.log 20000 :=
    (by norm_num only : (0 : ℝ) ≤ 9).trans log_twenty_thousand_bounds.1
  have he : Real.exp ((2 / 7 : ℝ)⁻¹) ≤ 20000 :=
    (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 20000)).mp
      ((by norm_num only : (2 / 7 : ℝ)⁻¹ ≤ 9).trans log_twenty_thousand_bounds.1)
  have ht :=
    Real.log_div_self_rpow_antitoneOn (by norm_num only : (0 : ℝ) < 2 / 7) he (he.trans hq) hq
  have hn : 0 ≤ Real.log q / q ^ (2 / 7 : ℝ) :=
    div_nonneg (hl0.trans (Real.log_le_log (by norm_num only) hq)) (Real.rpow_nonneg hq0.le _)
  have hs := mul_self_le_mul_self hn ht
  have hp (y : ℝ) (hy : 0 ≤ y) : (y ^ (2 / 7 : ℝ)) ^ 2 = y ^ (4 / 7 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num only
  have htransfer :
    (Real.log q) ^ 2 / q ^ (4 / 7 : ℝ) ≤ (Real.log 20000) ^ 2 / (20000 : ℝ) ^ (4 / 7 : ℝ) := by
    simpa only [← pow_two, div_pow, hp q hq0.le, hp 20000 (by norm_num only)] using hs
  have hlogSq : (Real.log 20000) ^ 2 ≤ (991 / 100 : ℝ) ^ 2 := by
    simpa only [← pow_two] using mul_self_le_mul_self hl0 log_twenty_thousand_bounds.2
  exact
    htransfer.trans
      ((div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num only : (0 : ℝ) < 286)
            twenty_thousand_rpow_four_sevenths_ge).trans
        ((div_le_div_of_nonneg_right hlogSq (by norm_num only : (0 : ℝ) ≤ 286)).trans
          (by norm_num only)))

/-- For a real modulus at least twenty thousand, a square-root scale above the
five-sixths power times the logarithm, and a nonnegative cutoff logarithm at most
five halves the modulus logarithm, the normalized square-prime-power majorant
is at most 263 over 320. Separate its two terms and use the uniform logarithmic
ratio certificates. This supplies the main numerical margin for Corollary 1.2. -/
theorem normalized_square_prime_power_le {q s t : ℝ} (hq : 20000 ≤ q)
    (hs : q ^ (5 / 6 : ℝ) * Real.log q ≤ s) (ht0 : 0 ≤ t) (ht : t ≤ (5 / 2 : ℝ) * Real.log q) :
    q ^ (3 / 7 : ℝ) * t ^ 2 / 4 * (1 / q + 1 / s) ≤ 263 / 320 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num only) hq
  have hl : (9 : ℝ) ≤ Real.log q :=
    log_twenty_thousand_bounds.1.trans (Real.log_le_log (by norm_num only) hq)
  have hl0 : 0 < Real.log q := lt_of_lt_of_le (by norm_num only) hl
  have hB : 0 < q ^ (5 / 6 : ℝ) * Real.log q := mul_pos (Real.rpow_pos_of_pos hq0 _) hl0
  have hs0 : 0 < s := hB.trans_le hs
  have hT : t ^ 2 ≤ ((5 / 2 : ℝ) * Real.log q) ^ 2 := by
    simpa only [← pow_two] using mul_self_le_mul_self ht0 ht
  have hrec : 1 / s ≤ 1 / (q ^ (5 / 6 : ℝ) * Real.log q) :=
    div_le_div_of_nonneg_left zero_le_one hB hs
  have h1 : q ^ (3 / 7 : ℝ) / q = 1 / q ^ (4 / 7 : ℝ) := by
    calc
      _ = q ^ ((3 / 7 : ℝ) - 1) := by rw [Real.rpow_sub hq0, Real.rpow_one]
      _ = _ := by
        norm_num only; rw [Real.rpow_neg hq0.le, one_div]
  have h2 : q ^ (3 / 7 : ℝ) / q ^ (5 / 6 : ℝ) = 1 / q ^ (17 / 42 : ℝ) := by
    calc
      _ = q ^ ((3 / 7 : ℝ) - 5 / 6) := (Real.rpow_sub hq0 _ _).symm
      _ = _ := by
        norm_num only; rw [Real.rpow_neg hq0.le, one_div]
  have hL : (Real.log q) ^ 2 / Real.log q = Real.log q := by
    rw [pow_two, mul_div_cancel_right₀ _ hl0.ne']
  calc
    _ ≤ q ^ (3 / 7 : ℝ) * ((5 / 2 : ℝ) * Real.log q) ^ 2 / 4 * (1 / q + 1 / s) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT (Real.rpow_nonneg hq0.le _))
          (by norm_num only : (0 : ℝ) ≤ 4))
        (add_nonneg (div_nonneg zero_le_one hq0.le) (div_nonneg zero_le_one hs0.le))
    _ ≤
        q ^ (3 / 7 : ℝ) * ((5 / 2 : ℝ) * Real.log q) ^ 2 / 4 *
          (1 / q + 1 / (q ^ (5 / 6 : ℝ) * Real.log q)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hrec)
        (div_nonneg (mul_nonneg (Real.rpow_nonneg hq0.le _) (sq_nonneg _)) (by norm_num only))
    _ = (25 / 16 : ℝ) * ((Real.log q) ^ 2 / q ^ (4 / 7 : ℝ) + Real.log q / q ^ (17 / 42 : ℝ)) := by
      calc
        _ =
            (25 / 16 : ℝ) *
              ((Real.log q) ^ 2 * (q ^ (3 / 7 : ℝ) / q) +
                ((Real.log q) ^ 2 / Real.log q) * (q ^ (3 / 7 : ℝ) / q ^ (5 / 6 : ℝ))) :=
          by
          simp only [div_mul_eq_div_div]
          ring
        _ = _ := by
          rw [h1, h2, hL]; ring
    _ ≤ (25 / 16 : ℝ) * (69 / 200 + 181 / 1000) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (log_sq_div_rpow_four_sevenths_le hq)
          (log_div_rpow_seventeen_fortyseconds_le hq))
        (by norm_num only)
    _ = 263 / 320 := by norm_num only

/-- For a modulus at least twenty thousand, the logarithm of the squared
totient-logarithm cutoff is at most five halves the modulus logarithm.
Use the totient upper bound and a tangent estimate for the logarithm of the
modulus logarithm. This discharges the cutoff-logarithm input of the gap estimates. -/
theorem residue_cutoff_log_le {q : ℕ} (hq : 20000 ≤ q) :
    Real.log (((q.totient : ℝ) * Real.log q) ^ 2) ≤ (5 / 2 : ℝ) * Real.log q := by
  have hl : (9 : ℝ) ≤ Real.log q :=
    log_twenty_thousand_bounds.1.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hq))
  have hl0 : 0 < Real.log q := lt_of_lt_of_le (by norm_num only) hl
  have hp0 : (0 : ℝ) < q.totient :=
    lt_of_lt_of_le (by norm_num only) (Nat.cast_le.mpr (NumberTheory.totient_ge_4156 hq))
  have hphiLog := Real.log_le_log hp0 (Nat.cast_le.mpr (Nat.totient_le q))
  have hlogL :=
    Analysis.log_le_log_add_sub_div (a := (9 : ℝ)) (y := Real.log q) (by norm_num only) hl0
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num only, Real.log_pow] at hlogL
  norm_num only at hlogL
  have hLL : Real.log (Real.log q) ≤ Real.log q / 4 := by
    linarith only [hlogL, hl, Real.log_three_lt_d9]
  rw [Real.log_pow, Real.log_mul hp0.ne' hl0.ne']
  norm_num only
  linarith only [hphiLog, hLL]

/-- At the corollary's cutoff for a modulus at least twenty thousand,
the square-prime-power majorant divided by the cutoff square root is at most 263 over 320.
Apply the normalized real estimate using the proved totient power bound and cutoff
logarithm bound. This connects the numerical certificate to the actual Section 4.1 cutoff. -/
theorem residue_cutoff_square_prime_power_normalized_le {q : ℕ} (hq : 20000 ≤ q) :
    (q : ℝ) ^ (3 / 7 : ℝ) * (Real.log (((q.totient : ℝ) * Real.log q) ^ 2)) ^ 2 / 4 *
        (1 / (q : ℝ) + 1 / ((q.totient : ℝ) * Real.log q)) ≤
      263 / 320 := by
  have hqR : (20000 : ℝ) ≤ q := Nat.cast_le.mpr hq
  have hl : 0 ≤ Real.log q :=
    (by norm_num only : (0 : ℝ) ≤ 9).trans
      (log_twenty_thousand_bounds.1.trans (Real.log_le_log (by norm_num only) hqR))
  apply
    normalized_square_prime_power_le hqR
      (mul_le_mul_of_nonneg_right (NumberTheory.rpow_five_sixths_le_totient hq) hl)
  · exact
      Real.log_nonneg
        ((by norm_num only : (1 : ℝ) ≤ 1000000000).trans (residue_cutoff_ge_billion hq))
  · exact residue_cutoff_log_le hq

/-- At a modulus at least twenty thousand, the squared totient-logarithm cutoff
is at least the modulus. The five-sixths totient bound implies a square-root lower
bound, and the modulus logarithm is at least one. This locates the parity maximum. -/
theorem modulus_le_residue_cutoff {q : ℕ} (hq : 20000 ≤ q) :
    (q : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  have hq1 : (1 : ℝ) ≤ q := (by norm_num only : (1 : ℝ) ≤ 20000).trans (Nat.cast_le.mpr hq)
  have hh :=
    (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num only : (1 / 2 : ℝ) ≤ 5 / 6)).trans
      (NumberTheory.rpow_five_sixths_le_totient hq)
  have hb := mul_self_le_mul_self (Real.rpow_nonneg (Nat.cast_nonneg q) (1 / 2)) hh
  have hp : ((q : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
    norm_num only [Real.rpow_one]
  have hqPhi : (q : ℝ) ≤ (q.totient : ℝ) ^ 2 := by simpa only [← pow_two, hp] using hb
  have hl : (1 : ℝ) ≤ Real.log q :=
    (by norm_num only : (1 : ℝ) ≤ 9).trans
      (log_twenty_thousand_bounds.1.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hq)))
  have hLsq : (1 : ℝ) ≤ (Real.log q) ^ 2 := by
    simpa only [one_mul, ← pow_two, one_pow] using mul_self_le_mul_self zero_le_one hl
  exact
    hqPhi.trans
      (by
        have hm := mul_le_mul_of_nonneg_left hLsq (sq_nonneg (q.totient : ℝ))
        simpa only [mul_one, mul_pow] using hm)

/-- At the corollary's cutoff, the logarithm of the parity maximum is at most
one plus the cutoff logarithm. The modulus term is below the cutoff, and the maximum
is twice the cutoff. This supplies the common norm-error estimate. -/
theorem residue_cutoff_log_max_le {q : ℕ} (hq : 20000 ≤ q) :
    Real.log (max ((q : ℝ) / Real.pi) (2 * ((q.totient : ℝ) * Real.log q) ^ 2)) ≤
      1 + Real.log (((q.totient : ℝ) * Real.log q) ^ 2) := by
  have hx0 : 0 < ((q.totient : ℝ) * Real.log q) ^ 2 :=
    lt_of_lt_of_le (by norm_num only) (residue_cutoff_ge_billion hq)
  have hqX :=
    (div_le_self (Nat.cast_nonneg q)
          (by linarith only [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)).trans
      (modulus_le_residue_cutoff hq)
  have hb : (q : ℝ) / Real.pi ≤ 2 * ((q.totient : ℝ) * Real.log q) ^ 2 := by
    linarith only [hqX, hx0]
  rw [max_eq_right hb, Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hx0.ne']
  linarith only [Real.log_two_lt_d9]

/-- At the corollary's cutoff for a modulus at least twenty thousand, the common
nonprincipal norm error is at most four over 125 times the square-root cutoff.
Bound the cutoff logarithm, the parity maximum and the three quadratic terms,
then use the uniform logarithmic ratios and the totient lower bound.
This absorbs the common error in the final character-average gap. -/
theorem residue_cutoff_character_norm_error_le {q : ℕ} (hq : 20000 ≤ q) :
    cosetCharacterNormError q (((q.totient : ℝ) * Real.log q) ^ 2) ≤
      (4 / 125 : ℝ) * Real.sqrt (((q.totient : ℝ) * Real.log q) ^ 2) := by
  let X : ℝ := ((q.totient : ℝ) * Real.log q) ^ 2
  let L : ℝ := Real.log q
  let s : ℝ := (q.totient : ℝ) * L
  have hqR : (20000 : ℝ) ≤ q := Nat.cast_le.mpr hq
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num only) hqR
  have hl : (9 : ℝ) ≤ L :=
    log_twenty_thousand_bounds.1.trans (Real.log_le_log (by norm_num only) hqR)
  have hl0 : 0 < L := lt_of_lt_of_le (by norm_num only) hl
  have ht0 : 0 ≤ Real.log X :=
    Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 1000000000).trans (residue_cutoff_ge_billion hq))
  have ht : Real.log X ≤ (5 / 2 : ℝ) * L := residue_cutoff_log_le hq
  have hT2 : (Real.log X) ^ 2 ≤ ((5 / 2 : ℝ) * L) ^ 2 := by
    simpa only [← pow_two] using mul_self_le_mul_self ht0 ht
  have hA : Real.log ((q : ℝ) / Real.pi) ≤ L := by
    rw [Real.log_div hq0.ne' Real.pi_pos.ne']
    have hp := Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ Real.pi)
    change Real.log q - Real.log Real.pi ≤ Real.log q
    linarith only [hp]
  have hB :=
    mul_le_mul
      (show (2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4 ≤ (2 / 3 : ℝ) * L + 4 by
        linarith only [hA])
      ht ht0 (show 0 ≤ (2 / 3 : ℝ) * L + 4 by linarith only [hl])
  have hmax : Real.log (max ((q : ℝ) / Real.pi) (2 * X)) ≤ 1 + (5 / 2 : ℝ) * L :=
    (residue_cutoff_log_max_le hq).trans (by linarith only [ht])
  have hmax0 : 0 ≤ Real.log (max ((q : ℝ) / Real.pi) (2 * X)) := by
    apply Real.log_nonneg
    have hx := residue_cutoff_ge_billion hq
    have hh : (1 : ℝ) ≤ 2 * X := by
      change (1000000000 : ℝ) ≤ X at hx; linarith only [hx]
    exact hh.trans (le_max_right _ _)
  have hC :=
    mul_le_mul (show Real.log X / 2 ≤ (5 / 4 : ℝ) * L by linarith only [ht]) hmax hmax0
      (show 0 ≤ (5 / 4 : ℝ) * L by linarith only [hl])
  have hE : cosetCharacterNormError q X ≤ (265 / 24 : ℝ) * L ^ 2 + (45 / 4 : ℝ) * L := by
    unfold cosetCharacterNormError
    nlinarith only [hT2, hB, hC]
  have hs : (q : ℝ) ^ (5 / 6 : ℝ) * L ≤ s :=
    mul_le_mul_of_nonneg_right (NumberTheory.rpow_five_sixths_le_totient hq) hl0.le
  have hQ : (3830 : ℝ) ≤ (q : ℝ) ^ (5 / 6 : ℝ) :=
    twenty_thousand_rpow_five_sixths_ge.trans
      (Real.rpow_le_rpow (by norm_num only) hqR (by norm_num only))
  have hLL : L ^ 2 ≤ (13 / 5000 : ℝ) * s := by
    have hr :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hq0 (5 / 6 : ℝ))).mp (log_div_rpow_five_sixths_le hqR)
    have hm := mul_le_mul_of_nonneg_right hr hl0.le
    have hn := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 13 / 5000)
    change L ≤ (13 / 5000 : ℝ) * (q : ℝ) ^ (5 / 6 : ℝ) at hr
    nlinarith only [hm, hn]
  have hLs : (3830 : ℝ) * L ≤ s := (mul_le_mul_of_nonneg_right hQ hl0.le).trans hs
  have hs0 : 0 ≤ s := (mul_nonneg (Real.rpow_nonneg hq0.le _) hl0.le).trans hs
  have hfinal : cosetCharacterNormError q X ≤ (4 / 125 : ℝ) * s := by
    nlinarith only [hE, hLL, hLs, hs0]
  rw [Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg q.totient) hl0.le)]
  exact hfinal

/-- The logarithm of forty billion is at most `49/2`. Apply the tangent bound
at the nearby thirty-fifth power of two and use its certified logarithm.
This bounds the exponent range for every small-modulus residue cutoff. -/
private theorem log_forty_billion_le : Real.log (40000000000 : ℝ) ≤ 49 / 2 := by
  have ht :=
    Analysis.log_le_log_add_sub_div (a := (2 : ℝ) ^ (35 : ℕ)) (y := 40000000000) (by norm_num only)
      (by norm_num only)
  rw [Real.log_pow] at ht
  norm_num only at ht
  linarith only [ht, Real.log_two_lt_d9]

/-- For moduli from four through twenty thousand, the squared totient-logarithm
cutoff is at most forty billion. Bound the totient by the modulus and the
modulus logarithm by ten, then square the nonnegative product. This is the
common upper cutoff for the finite part of Corollary 1.2. -/
theorem residue_cutoff_le_forty_billion {q : ℕ} (hq : 4 ≤ q) (hu : q ≤ 20000) :
    ((q.totient : ℝ) * Real.log q) ^ 2 ≤ (40000000000 : ℝ) := by
  have hqR : (q : ℝ) ≤ 20000 := Nat.cast_le.mpr hu
  have hL0 : 0 ≤ Real.log q :=
    Real.log_nonneg (Nat.one_le_cast.mpr ((by norm_num only : (1 : ℕ) ≤ 4).trans hq))
  have hL : Real.log q ≤ 10 :=
    (Real.log_le_log (Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num only) hq)) hqR).trans
      (log_twenty_thousand_bounds.2.trans (by norm_num only))
  have hphi : (q.totient : ℝ) ≤ 20000 := (Nat.cast_le.mpr (Nat.totient_le q)).trans hqR
  have hs := mul_le_mul hphi hL hL0 (by norm_num only : (0 : ℝ) ≤ 20000)
  have hp := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg q.totient) hL0) hs 2
  norm_num only at hp
  exact hp

/-- For moduli from four through twenty thousand, the prime-power exponent
bound at the squared totient-logarithm cutoff is at most thirty-five.
Use the forty-billion cutoff bound and certified logarithms, then take the
natural floor. Only the seventeen odd exponents from three through thirty-five
are needed in every finite root certificate for Corollary 1.2. -/
theorem residue_cutoff_exponentBound_le_thirtyFive {q : ℕ} (hq : 4 ≤ q) (hu : q ≤ 20000) :
    ⌊Real.log (((q.totient : ℝ) * Real.log q) ^ 2) / Real.log 2⌋₊ ≤ 35 := by
  have hq1 : (1 : ℝ) < q := Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num only : 1 < 4) hq)
  have hphi : (0 : ℝ) < q.totient :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (lt_of_lt_of_le (by norm_num only : 0 < 4) hq))
  have hx0 := sq_pos_of_pos (mul_pos hphi (Real.log_pos hq1))
  have hl :=
    (Real.log_le_log hx0 (residue_cutoff_le_forty_billion hq hu)).trans log_forty_billion_le
  apply Nat.le_of_lt_succ
  apply (Nat.floor_lt' (by norm_num only : (36 : ℕ) ≠ 0)).mpr
  apply (div_lt_iff₀ (Real.log_pos (by norm_num only : (1 : ℝ) < 2))).mpr
  norm_num only
  linarith only [hl, Real.log_two_gt_d9]

/-- The logarithm of pi is at least `1144/1000`. Use the affine lower bound
at three and certified bounds for pi. This fixes the ambient endpoint constant
in the rational interval comparison. -/
private theorem log_pi_lower_for_gap : (1144 / 1000 : ℝ) ≤ Real.log Real.pi := by
  have hpi : Real.pi ≤ (22 / 7 : ℝ) := Real.pi_lt_d4.le.trans (by norm_num only)
  have hl :=
    Analysis.log_gt_affine_of_anchor (a := (3 : ℝ)) (b := 22 / 7) (y := Real.pi) (L := 1.0986122885)
      (by norm_num only) (by norm_num only) Real.pi_gt_three.le hpi Real.log_three_gt_d9
  linarith only [hl, Real.pi_gt_d4]

/-- For modulus from `64` through `20000` and cutoff at least `65536`, upper
bounds for the modulus and cutoff logarithms give a rational polynomial bound
for the common character error. The parity maximum equals twice the cutoff;
use certified logarithms of two and pi. This removes transcendental terms
from the nonprincipal error certificate. -/
theorem cosetCharacterNormError_le_log_interval {q : ℕ} (hq : 64 ≤ q) (hu : q ≤ 20000) {x L T : ℝ}
    (hx : 65536 ≤ x) (hL : Real.log q ≤ L) (hT : Real.log x ≤ T) :
    cosetCharacterNormError q x ≤
      T ^ 2 + ((2 / 3 : ℝ) * (L - 1144 / 1000) + 4) * T + T / 2 * (693148 / 1000000 + T) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hxlog : 0 ≤ Real.log x := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 65536).trans hx)
  have hT0 := hxlog.trans hT
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr ((by norm_num only : (1 : ℕ) ≤ 64).trans hq)
  have hL0 := (Real.log_nonneg hq1).trans hL
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hpi1 : (1 : ℝ) ≤ Real.pi := (by norm_num only : (1 : ℝ) ≤ 3).trans Real.pi_gt_three.le
  have hdiv := div_le_self (Nat.cast_nonneg q : (0 : ℝ) ≤ q) hpi1
  have hqR : (q : ℝ) ≤ 20000 := Nat.cast_le.mpr hu
  have hm : (q : ℝ) / Real.pi ≤ 2 * x := by linarith only [hdiv, hqR, hx]
  have hc :
    (2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4 ≤ (2 / 3 : ℝ) * (L - 1144 / 1000) + 4 := by
    rw [Real.log_div hq0.ne' Real.pi_pos.ne']
    linarith only [hL, log_pi_lower_for_gap]
  have hc0 : 0 ≤ (2 / 3 : ℝ) * (L - 1144 / 1000) + 4 := by linarith only [hL0]
  have hs := mul_self_le_mul_self hxlog hT
  have he := mul_le_mul hc hT hxlog hc0
  have htwo : Real.log 2 ≤ (693148 / 1000000 : ℝ) := by linarith only [Real.log_two_lt_d9]
  have hsum := add_le_add htwo hT
  have hsum0 := add_nonneg (Real.log_pos (by norm_num only : (1 : ℝ) < 2)).le hxlog
  have hp :=
    mul_le_mul (div_le_div_of_nonneg_right hT (by norm_num only : (0 : ℝ) ≤ 2)) hsum hsum0
      (div_nonneg hT0 (by norm_num only : (0 : ℝ) ≤ 2))
  unfold cosetCharacterNormError
  rw [max_eq_right hm, Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hx0.ne']
  nlinarith only [hs, he, hp]

/-- For cutoff at least `65536`, a lower cutoff bound and upper square-root
and logarithm bounds give a rational lower bound for the principal contribution.
Apply the certified upper logarithm of twice pi and retain the exact prime-factor
count. This supplies the lower side of the interval gap certificate. -/
theorem cosetPrincipalLower_ge_interval {q : ℕ} {x X S T : ℝ} (hx : 65536 ≤ x) (hX : X ≤ x)
    (hS : Real.sqrt x ≤ S) (hT : Real.log x ≤ T) :
    X - (1839 / 1000 : ℝ) * T - 1 - (S + 1) / 20 - (1 / 2 : ℝ) * q.primeFactors.card * T ^ 2 ≤
      cosetPrincipalLower q x := by
  have ht0 : 0 ≤ Real.log x := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 65536).trans hx)
  have hs := mul_self_le_mul_self ht0 hT
  have hp :=
    mul_le_mul Analysis.log_two_mul_pi_lt.le hT ht0 (by norm_num only : (0 : ℝ) ≤ 1839 / 1000)
  have hw :=
    mul_le_mul_of_nonneg_left hs
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)
        (Nat.cast_nonneg q.primeFactors.card : (0 : ℝ) ≤ q.primeFactors.card))
  unfold cosetPrincipalLower
  nlinarith only [hX, hS, hp, hw]

/-- Positive lower bounds for the cutoff and its square root and an upper
logarithm bound control the reciprocal main term. Use the lower Euler-constant
bound and the upper logarithm of twice pi; positive denominator comparisons
bound both reciprocal terms. This supplies the nonprincipal correction. -/
theorem reciprocalMainTerm_le_interval {x X s T : ℝ} (hX0 : 0 < X) (hX : X ≤ x) (hs0 : 0 < s)
    (hs : s ≤ Real.sqrt x) (hT : Real.log x ≤ T) :
    Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x +
        1 / (20 * Real.sqrt x) ≤
      T - (1 + 23 / 40) + (1839 / 1000 : ℝ) / X + 1 / (20 * s) := by
  have hpi0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith only [Real.pi_gt_three])
  have hp :=
    (div_le_div_of_nonneg_left hpi0 hX0 hX).trans
      (div_le_div_of_nonneg_right Analysis.log_two_mul_pi_lt.le hX0.le)
  have hr :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 1)
      (mul_pos (by norm_num only : (0 : ℝ) < 20) hs0)
      (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 20))
  linarith only [hT, hp, hr, Analysis.twentyThree_fortieths_lt_eulerMascheroniConstant]

/-- For cutoff at least `65536`, the reciprocal main term is nonnegative.
The logarithm is already greater than two above eight, while the Euler constant
is below two thirds; the remaining quotients are nonnegative. This permits
multiplying its upper bound by an upper square-root coefficient. -/
theorem reciprocalMainTerm_nonneg {x : ℝ} (hx : 65536 ≤ x) :
    0 ≤
      Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x +
        1 / (20 * Real.sqrt x) := by
  have hl :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 8) ((by norm_num only : (8 : ℝ) ≤ 65536).trans hx)
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num only, Real.log_pow] at hl
  norm_num only at hl
  have hm : 0 ≤ Real.log x - (1 + Real.eulerMascheroniConstant) := by
    linarith only [hl, Real.log_two_gt_d9, Real.eulerMascheroniConstant_lt_two_thirds]
  have hp :=
    div_nonneg (Real.log_nonneg (by linarith only [Real.pi_gt_three] : (1 : ℝ) ≤ 2 * Real.pi))
      ((by norm_num only : (0 : ℝ) ≤ 65536).trans hx)
  exact
    add_nonneg (add_nonneg hm hp)
      (div_nonneg zero_le_one (mul_nonneg (by norm_num only) (Real.sqrt_nonneg x)))

/-- Under the small-modulus and cutoff lower bounds, interval bounds for
the cutoff, square root and two logarithms bound the full nonprincipal majorant.
Combine the common-error and reciprocal-term certificates with nonnegative
coefficients and the identity subgroup's totient index. The resulting expression
uses rational operations when all interval endpoints are rational. -/
theorem cosetNonprincipalUpper_le_interval {q : ℕ} [NeZero q] (hq : 64 ≤ q) (hu : q ≤ 20000)
    {x X s S L T : ℝ} (hx : 65536 ≤ x) (hX0 : 0 < X) (hX : X ≤ x) (hs0 : 0 < s)
    (hs : s ≤ Real.sqrt x) (hS : Real.sqrt x ≤ S) (hL : Real.log q ≤ L) (hT : Real.log x ≤ T) :
    cosetNonprincipalUpper q ⊥ x ≤
      ((q.totient : ℝ) - 1) *
          ((S + 19 / 6) * (L - 51 / 50) +
            (T ^ 2 + ((2 / 3 : ℝ) * (L - 1144 / 1000) + 4) * T + T / 2 * (693148 / 1000000 + T))) +
        2 * (S + 19 / 6) * (T - (1 + 23 / 40) + (1839 / 1000 : ℝ) / X + 1 / (20 * s)) := by
  classical
  have hA := add_le_add hS (le_refl (19 / 6 : ℝ))
  have hA0 : 0 ≤ S + 19 / 6 := add_nonneg ((Real.sqrt_nonneg x).trans hS) (by norm_num only)
  have hl :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 4)
      (Nat.cast_le.mpr ((by norm_num only : (4 : ℕ) ≤ 64).trans hq))
  rw [Real.log_four_eq] at hl
  have hC0 : 0 ≤ Real.log q - 51 / 50 := by linarith only [hl, Real.log_two_gt_d9]
  have hC := sub_le_sub_right hL (51 / 50 : ℝ)
  have hprod := mul_le_mul hA hC hC0 hA0
  have herror := cosetCharacterNormError_le_log_interval hq hu hx hL hT
  have ht0 : (0 : ℕ) < q.totient :=
    Nat.totient_pos.mpr (lt_of_lt_of_le (by norm_num only : 0 < 64) hq)
  have hphi : (0 : ℝ) ≤ (q.totient : ℝ) - 1 := sub_nonneg.mpr (Nat.one_le_cast.mpr ht0)
  have hn := mul_le_mul_of_nonneg_left (add_le_add hprod herror) hphi
  have hrec := reciprocalMainTerm_le_interval hX0 hX hs0 hs hT
  have hp := mul_le_mul hA hrec (reciprocalMainTerm_nonneg hx) hA0
  have hp2 := mul_le_mul_of_nonneg_left hp (by norm_num only : (0 : ℝ) ≤ 2)
  unfold cosetNonprincipalUpper
  rw [Subgroup.index_bot, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  nlinarith only [hn, hp2]

/-- For cutoff at least `65536`, upper square-root and logarithm bounds
control the square-residue majorant. Square the nonnegative logarithm bound
and compare the nonnegative product factors. This retains the exact prime-factor
count while replacing the remaining real quantities by interval endpoints. -/
theorem squareResidueMajorant_le_interval {q : ℕ} {x S T : ℝ} (hx : 65536 ≤ x)
    (hS : Real.sqrt x ≤ S) (hT : Real.log x ≤ T) :
    (2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) ≤
      (2 : ℝ) ^ q.primeFactors.card * T ^ 2 / 4 * (S / q + 1) := by
  have ht0 : 0 ≤ Real.log x := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 65536).trans hx)
  have hs := mul_self_le_mul_self ht0 hT
  simp only [← pow_two] at hs
  have hcoef : 0 ≤ (2 : ℝ) ^ q.primeFactors.card := pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) _
  have hprod :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hcoef) (by norm_num only : (0 : ℝ) ≤ 4)
  have hfac :=
    add_le_add (div_le_div_of_nonneg_right hS (Nat.cast_nonneg q : (0 : ℝ) ≤ q)) (le_refl (1 : ℝ))
  have hfac0 : 0 ≤ Real.sqrt x / q + 1 :=
    add_nonneg (div_nonneg (Real.sqrt_nonneg x) (Nat.cast_nonneg q)) zero_le_one
  have hupper0 : 0 ≤ (2 : ℝ) ^ q.primeFactors.card * T ^ 2 / 4 :=
    div_nonneg (mul_nonneg hcoef (sq_nonneg T)) (by norm_num only)
  exact mul_le_mul hprod hfac hfac0 hupper0

open Classical in
/-- Under GRH, for modulus from `64` through `20000` and cutoff at least
`65536`, interval bounds and natural-power certificates imply the least-prime
bound whenever the resulting rational upper majorant is below the rational
principal lower bound. Substitute the interval estimates into the root-certificate
criterion. This is the checked interface for excluding moduli from finite coverage. -/
theorem exists_least_prime_in_residue_le_of_interval_certificates {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hq : 64 ≤ q) (hu : q ≤ 20000) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X s S L T : ℝ} (hx : 65536 ≤ x) (hX0 : 0 < X) (hX : X ≤ x) (hs0 : 0 < s)
    (hs : s ≤ Real.sqrt x) (hS : Real.sqrt x ≤ S) (hL : Real.log q ≤ L) (hT : Real.log x ≤ T)
    {K : ℕ} (hK : ⌊Real.log x / Real.log 2⌋₊ ≤ K) (b c : ℕ → ℝ)
    (hb : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ b k)
    (hc : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ c k)
    (hpow : ∀ k ∈ (Finset.Icc 3 K).filter Odd, x ≤ b k ^ k)
    (hsq : ∀ k ∈ (Finset.Icc 3 K).filter Odd, b k ≤ c k ^ 2)
    (hgap :
      (q.totient : ℝ) *
            ((2 : ℝ) ^ q.primeFactors.card * T ^ 2 / 4 * (S / q + 1) +
              ∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℝ) * (b k + c k / 20)) +
          (((q.totient : ℝ) - 1) *
              ((S + 19 / 6) * (L - 51 / 50) +
                (T ^ 2 + ((2 / 3 : ℝ) * (L - 1144 / 1000) + 4) * T +
                  T / 2 * (693148 / 1000000 + T))) +
            2 * (S + 19 / 6) * (T - (1 + 23 / 40) + (1839 / 1000 : ℝ) / X + 1 / (20 * s))) <
        X - (1839 / 1000 : ℝ) * T - 1 - (S + 1) / 20 - (1 / 2 : ℝ) * q.primeFactors.card * T ^ 2) :
    ∃ p : ℕ, IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ x := by
  have hn := cosetNonprincipalUpper_le_interval hq hu hx hX0 hX hs0 hs hS hL hT
  have hp := cosetPrincipalLower_ge_interval (q := q) hx hX hS hT
  have hsqb := squareResidueMajorant_le_interval (q := q) hx hS hT
  have hm :=
    mul_le_mul_of_nonneg_left
      (add_le_add hsqb (le_refl (∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℝ) * (b k + c k / 20))))
      (Nat.cast_nonneg q.totient : (0 : ℝ) ≤ q.totient)
  exact
    exists_least_prime_in_residue_le_of_power_certificates a hq hGRH hx hK b c hb hc hpow hsq
      ((lt_of_le_of_lt (add_le_add hm hn) hgap).trans_le hp)

/-- Check the strict rational gap between the principal lower estimate and
the square-residue, odd-root and nonprincipal upper estimates. The parameters
give the modulus, totient, distinct-prime count, exponent limit and interval
endpoints. The natural root data avoid real evaluation in finite certificates. -/
def residueIntervalGapCheck (q t w K : ℕ) (X s S L T : ℚ) (b c : ℕ → ℕ) : Bool :=
  decide
    ((t : ℚ) *
          ((2 : ℚ) ^ w * T ^ 2 / 4 * (S / q + 1) +
            ∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℚ) * ((b k : ℚ) + (c k : ℚ) / 20)) +
        (((t : ℚ) - 1) *
            ((S + 19 / 6) * (L - 51 / 50) +
              (T ^ 2 + ((2 / 3 : ℚ) * (L - 1144 / 1000) + 4) * T +
                T / 2 * (693148 / 1000000 + T))) +
          2 * (S + 19 / 6) * (T - (1 + 23 / 40) + (1839 / 1000 : ℚ) / X + 1 / (20 * s))) <
      X - (1839 / 1000 : ℚ) * T - 1 - (S + 1) / 20 - (1 / 2 : ℚ) * w * T ^ 2)

/-- A successful rational gap check implies the real inequality required by
the interval certificate criterion. Reflect the Boolean comparison, commute
casts with the finite root sum and preserve strict order. Arithmetic identities
for the totient and prime-factor count are supplied separately by the caller. -/
theorem residueIntervalGapCheck_sound {q t w K : ℕ} {X s S L T : ℚ} {b c : ℕ → ℕ}
    (h : residueIntervalGapCheck q t w K X s S L T b c = true) :
    (t : ℝ) *
          ((2 : ℝ) ^ w * (T : ℝ) ^ 2 / 4 * ((S : ℝ) / q + 1) +
            ∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℝ) * ((b k : ℝ) + (c k : ℝ) / 20)) +
        (((t : ℝ) - 1) *
            (((S : ℝ) + 19 / 6) * ((L : ℝ) - 51 / 50) +
              ((T : ℝ) ^ 2 + ((2 / 3 : ℝ) * ((L : ℝ) - 1144 / 1000) + 4) * (T : ℝ) +
                (T : ℝ) / 2 * (693148 / 1000000 + (T : ℝ)))) +
          2 * ((S : ℝ) + 19 / 6) *
            ((T : ℝ) - (1 + 23 / 40) + (1839 / 1000 : ℝ) / (X : ℝ) + 1 / (20 * (s : ℝ)))) <
      (X : ℝ) - (1839 / 1000 : ℝ) * (T : ℝ) - 1 - ((S : ℝ) + 1) / 20 -
        (1 / 2 : ℝ) * w * (T : ℝ) ^ 2 := by
  have hr :
    (t : ℚ) *
          ((2 : ℚ) ^ w * T ^ 2 / 4 * (S / q + 1) +
            ∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℚ) * ((b k : ℚ) + (c k : ℚ) / 20)) +
        (((t : ℚ) - 1) *
            ((S + 19 / 6) * (L - 51 / 50) +
              (T ^ 2 + ((2 / 3 : ℚ) * (L - 1144 / 1000) + 4) * T +
                T / 2 * (693148 / 1000000 + T))) +
          2 * (S + 19 / 6) * (T - (1 + 23 / 40) + (1839 / 1000 : ℚ) / X + 1 / (20 * s))) <
      X - (1839 / 1000 : ℚ) * T - 1 - (S + 1) / 20 - (1 / 2 : ℚ) * w * T ^ 2 :=
    of_decide_eq_true h
  have hc := (Rat.cast_lt (K := ℝ)).mpr hr
  have hsum :
    ((∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℚ) * ((b k : ℚ) + (c k : ℚ) / 20) : ℚ) : ℝ) =
      ∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℝ) * ((b k : ℝ) + (c k : ℝ) / 20) := by
    change
      (Rat.castHom ℝ) (∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℚ) * ((b k : ℚ) + (c k : ℚ) / 20)) =
        _
    rw [map_sum]
    simp only [Rat.coe_castHom, Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat]
  simpa only [hsum, Rat.cast_one, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using hc

/-- Rational data for the totient-logarithm residue bound.
The totient and distinct-prime count specify the arithmetic values to be proved
separately. The lower and upper modulus logarithms determine the radius interval;
the cutoff logarithm bounds the exponent range. Each scale and term count selects
a Taylor certificate, and the two natural-valued functions bound the odd roots
and their square roots. The Boolean check enforces all analytic conditions;
successful data yield the Corollary 1.2 bound for every unit residue under GRH. -/
structure TotientLogResidueCertificate where
  totient : ℕ
  primeFactorCount : ℕ
  logLower : ℚ
  logUpper : ℚ
  cutoffLogUpper : ℚ
  logScale : ℕ
  logTerms : ℕ
  cutoffLogScale : ℕ
  cutoffLogTerms : ℕ
  exponentBound : ℕ
  rootUpper : ℕ → ℕ
  sqrtRootUpper : ℕ → ℕ

/-- Check the modulus range, positive radius, minimum cutoff, two logarithm
intervals, exponent limit, root powers and strict final gap for the supplied data.
The arithmetic values are parameters rather than recomputed totients or factors.
This finite rational test is reflected by the least-prime theorem below. -/
def TotientLogResidueCertificate.check (d : TotientLogResidueCertificate) (q : ℕ) : Bool :=
  decide
    (64 ≤ q ∧
      q ≤ 20000 ∧
      0 < (d.totient : ℚ) * d.logLower ∧
      65536 ≤ ((d.totient : ℚ) * d.logLower) ^ 2 ∧
      Analysis.rationalLogIntervalCheck q d.logScale d.logTerms d.logLower d.logUpper = true ∧
      Analysis.rationalLogIntervalCheck (((d.totient : ℚ) * d.logUpper) ^ 2) d.cutoffLogScale
          d.cutoffLogTerms 0 d.cutoffLogUpper =
        true ∧
      d.cutoffLogUpper < (d.exponentBound + 1) * (6931471803 / 10000000000 : ℚ) ∧
      oddRootPowerCheck (((d.totient : ℚ) * d.logUpper) ^ 2) d.exponentBound d.rootUpper
          d.sqrtRootUpper =
        true ∧
      residueIntervalGapCheck q d.totient d.primeFactorCount d.exponentBound
          (((d.totient : ℚ) * d.logLower) ^ 2) ((d.totient : ℚ) * d.logLower)
          ((d.totient : ℚ) * d.logUpper) d.logUpper d.cutoffLogUpper d.rootUpper d.sqrtRootUpper =
        true)

/-- Under GRH, a successful rational certificate with the correct totient and
distinct-prime count bounds the least prime in every unit residue by the squared
totient-logarithm cutoff. Enclose the cutoff and its square root, bound its exponent
range, and reflect the root and gap checks into the interval criterion.
This shared theorem replaces separate real-arithmetic proofs for each modulus. -/
theorem TotientLogResidueCertificate.exists_least_prime {q : ℕ} [NeZero q]
    (d : TotientLogResidueCertificate) (htot : q.totient = d.totient)
    (hfac : q.primeFactors.card = d.primeFactorCount) (hcheck : d.check q = true)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : (ZMod q)ˣ) :
    ∃ p : ℕ,
      IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  have hc := of_decide_eq_true (show decide _ = true from hcheck)
  obtain ⟨hq, hu, hs0, hxMin, hl, hxlog, hK, hroots, hgap⟩ := hc
  have hlog := Analysis.rationalLogIntervalCheck_sound hl
  have hsl : (d.totient : ℝ) * (d.logLower : ℝ) ≤ (d.totient : ℝ) * Real.log q := by
    simpa only [Rat.cast_natCast] using
      mul_le_mul_of_nonneg_left hlog.1 (Nat.cast_nonneg d.totient : (0 : ℝ) ≤ d.totient)
  have hsu : (d.totient : ℝ) * Real.log q ≤ (d.totient : ℝ) * (d.logUpper : ℝ) := by
    simpa only [Rat.cast_natCast] using
      mul_le_mul_of_nonneg_left hlog.2 (Nat.cast_nonneg d.totient : (0 : ℝ) ≤ d.totient)
  have hs0R : 0 < (d.totient : ℝ) * (d.logLower : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_zero] using (Rat.cast_pos (K := ℝ)).mpr hs0
  have hrad0 := hs0R.le.trans hsl
  have hxl := pow_le_pow_left₀ hs0R.le hsl 2
  have hxu := pow_le_pow_left₀ hrad0 hsu 2
  let x : ℝ := ((d.totient : ℝ) * Real.log q) ^ 2
  have hxMinR : 65536 ≤ x := by
    have hn := (Rat.cast_le (K := ℝ)).mpr hxMin
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] at hn
    exact hn.trans hxl
  have hxS : Real.sqrt x = (d.totient : ℝ) * Real.log q := Real.sqrt_sq hrad0
  have hXlog := (Analysis.rationalLogIntervalCheck_sound hxlog).2
  simp only [Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast] at hXlog
  have hT : Real.log x ≤ (d.cutoffLogUpper : ℝ) :=
    (Real.log_le_log (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 65536) hxMinR) hxu).trans hXlog
  have hKcast := (Rat.cast_lt (K := ℝ)).mpr hK
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_div,
    Rat.cast_ofNat] at hKcast
  have hKreal : ⌊Real.log x / Real.log 2⌋₊ ≤ d.exponentBound := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt' (Nat.succ_ne_zero d.exponentBound)).mpr
    apply (div_lt_iff₀ (Real.log_pos (by norm_num only : (1 : ℝ) < 2))).mpr
    have hmult :
      (d.exponentBound + 1 : ℝ) * (6931471803 / 10000000000) ≤
        (d.exponentBound + 1 : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith only [Real.log_two_gt_d9])
        (add_nonneg (Nat.cast_nonneg d.exponentBound) zero_le_one)
    simpa only [Nat.cast_succ] using lt_of_le_of_lt hT (hKcast.trans_le hmult)
  have hr := oddRootPowerCheck_sound hroots
  simp only [Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast] at hr
  have hg := residueIntervalGapCheck_sound hgap
  simp only [Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast] at hg
  rw [htot]
  exact
    exists_least_prime_in_residue_le_of_interval_certificates a hq hu hGRH hxMinR
      (sq_pos_of_pos hs0R) hxl hs0R (hxS.symm ▸ hsl) (hxS.symm ▸ hsu) hlog.2 hT hKreal
      (fun k ↦ (d.rootUpper k : ℝ)) (fun k ↦ (d.sqrtRootUpper k : ℝ)) (fun k _ ↦ Nat.cast_nonneg _)
      (fun k _ ↦ Nat.cast_nonneg _) (fun k hk ↦ hxu.trans (hr k hk).1) (fun k hk ↦ (hr k hk).2)
      (by simpa only [htot, hfac] using hg)

/-- Check both the analytic interval data and the arithmetic values from a full
prime-factor list. Successful data need no separately supplied totient or
distinct-prime-count identities. This is the complete finite certificate entry. -/
def TotientLogResidueCertificate.checkWithFactors (d : TotientLogResidueCertificate) (q : ℕ)
    (factors : List ℕ) : Bool :=
  decide
    (d.check q = true ∧
      NumberTheory.factorListArithmeticCheck q d.totient d.primeFactorCount factors = true)

/-- Under GRH, a certificate whose analytic data and supplied prime-factor list
both pass bounds the least prime in every unit residue by the totient-logarithm
cutoff. Reflect the arithmetic identities and apply the common analytic theorem.
This is the shared consumer for generated bounded-modulus certificates. -/
theorem TotientLogResidueCertificate.exists_least_prime_of_factor_list {q : ℕ} [NeZero q]
    (d : TotientLogResidueCertificate) (factors : List ℕ)
    (hcheck : d.checkWithFactors q factors = true)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : (ZMod q)ˣ) :
    ∃ p : ℕ,
      IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  have hc :
    d.check q = true ∧
      NumberTheory.factorListArithmeticCheck q d.totient d.primeFactorCount factors = true :=
    of_decide_eq_true hcheck
  have ha := NumberTheory.factorListArithmeticCheck_sound hc.2
  exact d.exists_least_prime ha.1 ha.2 hc.1 hGRH a

/-- Under GRH, a checked analytic certificate and a certified prime-factor list
give the totient-logarithm least-prime bound. Check the factor product, totient and
distinct-prime count separately from primality, then apply the shared analytic theorem.
This reuses common prime proofs without evaluating primality in each certificate. -/
theorem TotientLogResidueCertificate.exists_least_prime_of_factor_values {q : ℕ} [NeZero q]
    (d : TotientLogResidueCertificate) (factors : List ℕ) (hp : ∀ p ∈ factors, p.Prime)
    (hv : NumberTheory.factorListValueCheck q d.totient d.primeFactorCount factors = true)
    (hc : d.check q = true) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (a : (ZMod q)ˣ) :
    ∃ p : ℕ,
      IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  have ha :=
    NumberTheory.factorListArithmeticCheck_sound
      (NumberTheory.factorListArithmeticCheck_of_values hp hv)
  exact d.exists_least_prime ha.1 ha.2 hc hGRH a

/-- Under GRH, checked analytic certificates for consecutive moduli give the
totient-logarithm least-prime bound throughout their interval. Subtract the initial
modulus to select the finite index and apply that certificate's soundness theorem.
This joins certificate blocks without repeating the real-analytic argument. -/
theorem exists_least_prime_in_residue_le_of_analytic_certificate_block {s n q : ℕ} [NeZero q]
    (d : Fin n → TotientLogResidueCertificate) (factors : Fin n → List ℕ)
    (h : ∀ i : Fin n, (d i).checkWithFactors (s + i.val) (factors i) = true) (hs : s ≤ q)
    (hb : q < s + n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (a : (ZMod q)ˣ) :
    ∃ p : ℕ,
      IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  have hsub : q - s < n := Nat.sub_lt_left_of_lt_add hs hb
  let i : Fin n := ⟨q - s, hsub⟩
  have he : s + i.val = q := Nat.add_sub_of_le hs
  have hc := h i
  rw [he] at hc
  exact (d i).exists_least_prime_of_factor_list (factors i) hc hGRH a

/-- Build certificate data from millionth-scaled logarithm endpoints and a
list of natural upper bounds for exponents three, five, seven and so on.
The parameters give the totient, prime-factor count, logarithm endpoints,
Taylor scales and term counts, and exponent limit. The square-root bounds are
computed by rounding the natural square root upward. Missing root entries return
zero and are rejected by the power check at a positive cutoff.
This constructor keeps generated certificate data compact; the checks establish
all required inequalities rather than assuming the supplied data are correct. -/
def TotientLogResidueCertificate.ofScaledData (t w lo hi upper j jx n nx K : ℕ) (roots : List ℕ) :
    TotientLogResidueCertificate
    where
  totient := t
  primeFactorCount := w
  logLower := (lo : ℚ) / 1000000
  logUpper := (hi : ℚ) / 1000000
  cutoffLogUpper := (upper : ℚ) / 1000000
  logScale := j
  logTerms := n
  cutoffLogScale := jx
  cutoffLogTerms := nx
  exponentBound := K
  rootUpper := fun k ↦ roots.getD ((k - 3) / 2) 0
  sqrtRootUpper := fun k ↦
    let b := roots.getD ((k - 3) / 2) 0
    let r := Nat.sqrt b
    if b ≤ r ^ 2 then r else r + 1

/-- For a character count at least two, an upper cutoff logarithm and the
certified upper Euler constant bound the parity correction numerator.
Both parity counts are nonnegative, so each correction can be bounded separately.
This supplies the numerator used by small-modulus rational certificates. -/
theorem reciprocalParityNumerator_le_interval {h x T : ℝ} (hh : 2 ≤ h) (hT : Real.log x ≤ T) :
    (h - 1) / 20 + (h - 2) * (Real.log x + 1 + Real.eulerMascheroniConstant / 2) +
        h * (Real.log 2 + Real.eulerMascheroniConstant / 2) ≤
      (h - 1) / 20 + (h - 2) * (T + 1 + 29 / 100) + h * (693148 / 1000000 + 29 / 100) := by
  have hgamma := Analysis.eulerMascheroniConstant_lt_twentyNine_fiftieths.le
  have he : Real.log x + 1 + Real.eulerMascheroniConstant / 2 ≤ T + 1 + 29 / 100 := by
    linarith only [hT, hgamma]
  have ho : Real.log 2 + Real.eulerMascheroniConstant / 2 ≤ (693148 / 1000000 : ℝ) + 29 / 100 := by
    linarith only [Real.log_two_lt_d9, hgamma]
  have hE := mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hh)
  have hO := mul_le_mul_of_nonneg_left ho (le_trans (by norm_num only) hh)
  linarith only [hE, hO]

/-- Lower cutoff and upper logarithm bounds control the averaged character
coefficient for any real count at least two. The supplied rational numerator
must be nonnegative, so replacing the cutoff denominator preserves the bound.
Use lower bounds for log pi and the Euler constant in the main term and the
parity numerator estimate for the reciprocal term. This is the coefficient
comparison needed before replacing its square-root multiplier. -/
theorem residueParityCoefficient_le_interval {h Q x X L T : ℝ} (hh : 2 ≤ h) (hX0 : 0 < X)
    (hX : X ≤ x) (hL : Real.log Q ≤ L) (hT : Real.log x ≤ T)
    (hD : 0 ≤ (h - 1) / 20 + (h - 2) * (T + 1 + 29 / 100) + h * (693148 / 1000000 + 29 / 100)) :
    (h - 1) * (Real.log Q - Real.log Real.pi - Real.eulerMascheroniConstant) + Real.log 2 +
        ((h - 1) / 20 + (h - 2) * (Real.log x + 1 + Real.eulerMascheroniConstant / 2) +
            h * (Real.log 2 + Real.eulerMascheroniConstant / 2)) /
          x ≤
      (h - 1) * (L - 1719 / 1000) + 693148 / 1000000 +
        ((h - 1) / 20 + (h - 2) * (T + 1 + 29 / 100) + h * (693148 / 1000000 + 29 / 100)) / X := by
  have hx0 := hX0.trans_le hX
  have hm : Real.log Q - Real.log Real.pi - Real.eulerMascheroniConstant ≤ L - 1719 / 1000 := by
    linarith only [hL, log_pi_lower_for_gap,
      Analysis.twentyThree_fortieths_lt_eulerMascheroniConstant]
  have hM := mul_le_mul_of_nonneg_left hm (by linarith only [hh] : 0 ≤ h - 1)
  have hn := reciprocalParityNumerator_le_interval hh hT
  have hd := (div_le_div_of_nonneg_right hn hx0.le).trans (div_le_div_of_nonneg_left hD hX0 hX)
  linarith only [hM, hd, Real.log_two_lt_d9]

/-- Rational interval majorant for the parity-averaged character coefficient.
The count h is at least two in applications; X bounds the cutoff from below,
while L and T bound the modulus and cutoff logarithms from above.
The constant 1719/1000 combines certified lower bounds for log pi and gamma.
Its nonnegativity is checked before replacing the square-root multiplier. -/
noncomputable def residueParityIntervalCoefficient (h X L T : ℝ) : ℝ :=
  (h - 1) * (L - 1719 / 1000) + 693148 / 1000000 +
    ((h - 1) / 20 + (h - 2) * (T + 1 + 29 / 100) + h * (693148 / 1000000 + 29 / 100)) / X

/-- Rational interval upper bound for the nonprincipal residue-character norms.
Use cutoff lower bound X, square-root bounds s and S, and upper logarithms L and T.
The three terms bound the parity average, common character error, and principal
reciprocal correction respectively. Numerical certificates check this expression
against the principal lower bound and the composite prime-power contribution. -/
noncomputable def residueParityIntervalUpper (h X s S L T : ℝ) : ℝ :=
  (S + 19 / 6) * residueParityIntervalCoefficient h X L T +
    (h - 1) * (T ^ 2 + ((2 / 3 : ℝ) * (L - 1144 / 1000) + 4) * T + T / 2 * (693148 / 1000000 + T)) +
    2 * (S + 19 / 6) * (T - (1 + 23 / 40) + (1839 / 1000 : ℝ) / X + 1 / (20 * s))

/-- For moduli from 64 through 20000 and cutoff at least 65536, interval bounds
majorize the full parity upper bound. Assume the totient is at least two and
both supplied rational coefficients are nonnegative. Bound the parity coefficient,
common endpoint error, and principal reciprocal correction separately; then
replace square-root multipliers using the nonnegative rational coefficients.
This connects the analytic parity average to a rational gap certificate. -/
theorem residueNonprincipalParityUpper_le_interval {q : ℕ} (hq : 64 ≤ q) (hu : q ≤ 20000)
    {x X s S L T : ℝ} (hh : (2 : ℝ) ≤ q.totient) (hx : 65536 ≤ x) (hX0 : 0 < X) (hX : X ≤ x)
    (hs0 : 0 < s) (hs : s ≤ Real.sqrt x) (hS : Real.sqrt x ≤ S) (hL : Real.log q ≤ L)
    (hT : Real.log x ≤ T) (hC0 : 0 ≤ residueParityIntervalCoefficient q.totient X L T)
    (hR0 : 0 ≤ T - (1 + 23 / 40) + (1839 / 1000 : ℝ) / X + 1 / (20 * s)) :
    residueNonprincipalParityUpper q x ≤ residueParityIntervalUpper q.totient X s S L T := by
  have hh1 : 0 ≤ (q.totient : ℝ) - 1 := by linarith only [hh]
  have hh0 : (0 : ℝ) ≤ q.totient := by linarith only [hh]
  have ht0 : 0 ≤ T := (Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 65536).trans hx)).trans hT
  have hD :=
    add_nonneg
      (add_nonneg (div_nonneg hh1 (by norm_num only : (0 : ℝ) ≤ 20))
        (mul_nonneg (sub_nonneg.mpr hh) (by linarith only [ht0] : 0 ≤ T + 1 + 29 / 100)))
      (mul_nonneg hh0 (by norm_num only : (0 : ℝ) ≤ 693148 / 1000000 + 29 / 100))
  have hc := residueParityCoefficient_le_interval hh hX0 hX hL hT hD
  have hA : 0 ≤ Real.sqrt x + (19 / 6 : ℝ) := add_nonneg (Real.sqrt_nonneg x) (by norm_num only)
  have hmain :=
    (mul_le_mul_of_nonneg_left hc hA).trans
      (mul_le_mul_of_nonneg_right (add_le_add hS (le_refl (19 / 6))) hC0)
  have he := mul_le_mul_of_nonneg_left (cosetCharacterNormError_le_log_interval hq hu hx hL hT) hh1
  have hr := reciprocalMainTerm_le_interval hX0 hX hs0 hs hT
  have htwo : 0 ≤ 2 * (Real.sqrt x + (19 / 6 : ℝ)) := mul_nonneg (by norm_num only) hA
  have hrec :=
    (mul_le_mul_of_nonneg_left hr htwo).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hS (le_refl (19 / 6)))
          (by norm_num only : (0 : ℝ) ≤ 2))
        hR0)
  dsimp only [residueNonprincipalParityUpper, residueParityIntervalUpper,
    residueParityIntervalCoefficient] at hmain ⊢
  linarith only [hmain, he, hrec]

/-- A lower logarithm of a half-period endpoint and an upper cutoff logarithm
bound its positive square-weight majorant. Assume the lower endpoint logarithm
is nonnegative and already lies in the decreasing part of the quadratic weight.
Compare the two quadratic values algebraically, then apply monotonicity of max.
This turns half-period weights into rational interval expressions. -/
theorem logSquareEndpointWeight_le_interval {x z l T : ℝ} (hl : l ≤ Real.log z) (hl0 : 0 ≤ l)
    (hT : Real.log x ≤ T) (hbase : T ≤ 4 * l) :
    max 0 (Real.log z * (Real.log x - 2 * Real.log z)) ≤ max 0 (l * (T - 2 * l)) := by
  have hz0 := hl0.trans hl
  have hp := mul_le_mul_of_nonneg_left hT hz0
  have hm := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hbase)
  have hquad : Real.log z * (T - 2 * Real.log z) ≤ l * (T - 2 * l) := by
    nlinarith only [hm, sq_nonneg (Real.log z - l)]
  have hw : Real.log z * (Real.log x - 2 * Real.log z) ≤ l * (T - 2 * l) := by
    nlinarith only [hp, hquad]
  exact max_le_max (le_refl 0) hw

open Classical in
/-- Interval logarithm bounds give a numerical upper bound for the square-index
Mangoldt contribution in a unit residue. Supply a root-count bound, upper cutoff
logarithm, upper half-period index, and nonnegative lower endpoint logarithms.
Require every endpoint to lie beyond the maximum of the quadratic weight.
Apply the analytic half-period bound and compare each endpoint weight separately.
This supplies the square contribution in refined residue-gap certificates. -/
theorem square_residue_sum_le_half_period_intervals {q r : ℕ} [NeZero q] (hq : 2 < q)
    (a : (ZMod q)ˣ) (hroot : Nat.card { z : ZMod q // z ^ 2 = (a : ZMod q) } ≤ r) {x T : ℝ}
    (hx : 1 < x) (hT : Real.log x ≤ T) (J : ℕ) (hJ : (2 * ⌊Real.sqrt x⌋₊) / q ≤ J)
    (hbase : Real.log x ≤ 4 * Real.log ((q : ℝ) / 2)) (l : ℕ → ℝ)
    (hl : ∀ j ∈ Finset.range (J + 1), j ≠ 0 → l j ≤ Real.log ((j : ℝ) * q / 2))
    (hl0 : ∀ j ∈ Finset.range (J + 1), j ≠ 0 → 0 ≤ l j)
    (ht : ∀ j ∈ Finset.range (J + 1), j ≠ 0 → T ≤ 4 * l j) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ IsSquare n ∧ (n : ZMod q) = (a : ZMod q)),
        ArithmeticFunction.vonMangoldt n * Real.log (x / (n : ℝ))) ≤
      (r : ℝ) / 2 *
        ∑ j ∈ Finset.range (J + 1), if j = 0 then T ^ 2 / 8 else max 0 (l j * (T - 2 * l j)) := by
  have hs :=
    AnalyticNumberTheory.Arithmetic.square_residue_sum_le_half_periods hq a hroot
      (zero_lt_one.trans hx) J hJ hbase
  apply hs.trans
  apply
    mul_le_mul_of_nonneg_left _ (div_nonneg (Nat.cast_nonneg r) (by norm_num only : (0 : ℝ) ≤ 2))
  apply Finset.sum_le_sum
  intro j hj
  by_cases hj0 : j = 0
  · rw [ite_eq_left hj0, ite_eq_left hj0]
    simpa only [pow_two] using
      div_le_div_of_nonneg_right (mul_self_le_mul_self (Real.log_nonneg hx.le) hT)
        (by norm_num only : (0 : ℝ) ≤ 8)
  · rw [ite_eq_right hj0, ite_eq_right hj0]
    exact logSquareEndpointWeight_le_interval (hl j hj hj0) (hl0 j hj hj0) hT (ht j hj hj0)

open Classical in
/-- Under GRH, a refined rational interval gap bounds the least prime in a unit
residue modulo a modulus from 64 through 20000. Supply cutoff and logarithm bounds,
half-period root-count data, corrected odd-root certificates, and nonnegative
rational character coefficients. The cutoff is at least 65536.
Combine the half-period square bound, corrected odd-power sum, and parity-averaged
character estimate; the strict gap contradicts a prime-free residue class.
This is the common soundness theorem for refined small-modulus certificates. -/
theorem exists_least_prime_in_residue_le_of_refined_interval_gap {q r K J : ℕ} [NeZero q]
    (a : (ZMod q)ˣ) (hq : 64 ≤ q) (hu : q ≤ 20000)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X s S L T t : ℝ}
    (hh : (2 : ℝ) ≤ q.totient) (hx : 65536 ≤ x) (hX0 : 0 < X) (hX : X ≤ x) (hs0 : 0 < s)
    (hs : s ≤ Real.sqrt x) (hS : Real.sqrt x ≤ S) (hL : Real.log q ≤ L) (hT : Real.log x ≤ T)
    (ht : t ≤ Real.log x) (hC0 : 0 ≤ residueParityIntervalCoefficient q.totient X L T)
    (hR0 : 0 ≤ T - (1 + 23 / 40) + (1839 / 1000 : ℝ) / X + 1 / (20 * s))
    (hroot : Nat.card { z : ZMod q // z ^ 2 = (a : ZMod q) } ≤ r)
    (hJ : (2 * ⌊Real.sqrt x⌋₊) / q ≤ J) (hbase : Real.log x ≤ 4 * Real.log ((q : ℝ) / 2))
    (l : ℕ → ℝ) (hl : ∀ j ∈ Finset.range (J + 1), j ≠ 0 → l j ≤ Real.log ((j : ℝ) * q / 2))
    (hl0 : ∀ j ∈ Finset.range (J + 1), j ≠ 0 → 0 ≤ l j)
    (hperiod : ∀ j ∈ Finset.range (J + 1), j ≠ 0 → T ≤ 4 * l j)
    (hK : ⌊Real.log x / Real.log 2⌋₊ ≤ K) (b c : ℕ → ℝ)
    (hb : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ b k)
    (hc : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ c k)
    (hpow : ∀ k ∈ (Finset.Icc 3 K).filter Odd, x ≤ b k ^ k)
    (hsq : ∀ k ∈ (Finset.Icc 3 K).filter Odd, b k ≤ c k ^ 2)
    (hpos :
      ∀ k ∈ (Finset.Icc 3 K).filter Odd,
        0 ≤ (k : ℝ) * (b k + c k / 20) - 183 / 100 * t - (k : ℝ) / 2)
    (hgap :
      (q.totient : ℝ) *
            ((r : ℝ) / 2 *
                (∑ j ∈ Finset.range (J + 1),
                  if j = 0 then T ^ 2 / 8 else max 0 (l j * (T - 2 * l j))) +
              ∑ k ∈ (Finset.Icc 3 K).filter Odd,
                ((k : ℝ) * (b k + c k / 20) - 183 / 100 * t - (k : ℝ) / 2)) +
          residueParityIntervalUpper q.totient X s S L T <
        X - (1839 / 1000 : ℝ) * T - 1 - (S + 1) / 20 - (1 / 2 : ℝ) * q.primeFactors.card * T ^ 2) :
    ∃ p : ℕ, IsLeast {v : ℕ | v.Prime ∧ (v : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ x := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only) hx
  have hq2 : 2 < q := lt_of_lt_of_le (by norm_num only) hq
  have hsquare :=
    square_residue_sum_le_half_period_intervals hq2 a hroot hx1 hT J hJ hbase l hl hl0 hperiod
  have hodd :=
    (AnalyticNumberTheory.Arithmetic.nonsquareCompositeLogWeightedSum_le_odd_powers
          (zero_lt_one.trans hx1)).trans
      (oddPrimePowerLogWeightedSum_le_corrected_power_certificates hGRH.riemann hx1 ht hK b c hb hc
        hpow hsq hpos)
  have hn :=
    (nonprincipal_residue_logWeightedNorm_sum_le_parity_explicit hq hGRH hx).trans
      (residueNonprincipalParityUpper_le_interval hq hu hh hx hX0 hX hs0 hs hS hL hT hC0 hR0)
  exact
    exists_least_prime_in_residue_le_of_weighted_gap a hGRH.riemann hx1
      (fun hno ↦
        (AnalyticNumberTheory.Arithmetic.residue_logWeightedSum_le_square_add_nonsquare (a : ZMod q)
              (zero_lt_one.trans hx1) hno).trans
          (add_le_add hsquare hodd))
      hn (hgap.trans_le (cosetPrincipalLower_ge_interval hx hX hS hT))

/-- Check nonnegativity of each rational corrected odd-power majorant up to `K`.
Supply a lower cutoff logarithm and natural root bounds. The finite test prevents
negative extra terms when extending the exponent range in residue certificates. -/
def correctedOddRootNonnegCheck (K : ℕ) (t : ℚ) (b c : ℕ → ℕ) : Bool :=
  @decide
    (∀ k ∈ (Finset.Icc 3 K).filter Odd,
      0 ≤ (k : ℚ) * (b k + c k / 20) - 183 / 100 * t - (k : ℚ) / 2)
    Finset.decidableDforallFinset

/-- A successful finite rational check gives the real nonnegativity hypotheses
for the corrected odd-power estimate. Reflect the bounded test and commute rational
casts with arithmetic. This supplies a guard for refined residue certificates. -/
theorem correctedOddRootNonnegCheck_sound {K : ℕ} {t : ℚ} {b c : ℕ → ℕ}
    (h : correctedOddRootNonnegCheck K t b c = true) :
    ∀ k ∈ (Finset.Icc 3 K).filter Odd,
      0 ≤ (k : ℝ) * ((b k : ℝ) + (c k : ℝ) / 20) - 183 / 100 * (t : ℝ) - (k : ℝ) / 2 := by
  let :
    Decidable
      (∀ k ∈ (Finset.Icc 3 K).filter Odd,
        0 ≤ (k : ℚ) * (b k + c k / 20) - 183 / 100 * t - (k : ℚ) / 2) :=
    Finset.decidableDforallFinset
  have hc := of_decide_eq_true h
  intro k hk
  have hr : (0 : ℝ) ≤ (((k : ℚ) * (b k + c k / 20) - 183 / 100 * t - (k : ℚ) / 2 : ℚ) : ℝ) :=
    Rat.cast_nonneg.mpr (hc k hk)
  simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_ofNat] using hr

/-- Under RH, two successful rational checks bound the odd prime-power contribution.
Supply an upper cutoff, a lower cutoff logarithm, and an upper exponent limit.
The power check bounds the roots; the sign check justifies extending the exponent sum.
Apply the corrected analytic estimate with these reflected conditions. This connects
finite certificate data to the odd contribution in the refined residue gap. -/
theorem oddPrimePowerLogWeightedSum_le_of_corrected_checks (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 1 < x) {X t : ℚ} (hX : x ≤ (X : ℝ)) (ht : (t : ℝ) ≤ Real.log x) {K : ℕ}
    (hK : ⌊Real.log x / Real.log 2⌋₊ ≤ K) (b c : ℕ → ℕ) (hp : oddRootPowerCheck X K b c = true)
    (hn : correctedOddRootNonnegCheck K t b c = true) :
    (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x (p ^ k)) ≤
      ∑ k ∈ (Finset.Icc 3 K).filter Odd,
        ((k : ℝ) * ((b k : ℝ) + (c k : ℝ) / 20) - 183 / 100 * (t : ℝ) - (k : ℝ) / 2) := by
  have hr := oddRootPowerCheck_sound hp
  exact
    oddPrimePowerLogWeightedSum_le_corrected_power_certificates hRH hx ht hK (fun k ↦ (b k : ℝ))
      (fun k ↦ (c k : ℝ)) (fun k _ ↦ Nat.cast_nonneg _) (fun k _ ↦ Nat.cast_nonneg _)
      (fun k hk ↦ hX.trans (hr k hk).1) (fun k hk ↦ (hr k hk).2)
      (correctedOddRootNonnegCheck_sound hn)

/-- Check the endpoint sign conditions and a rational upper bound for the sum of
half-period square weights. The supplied root-count bound and logarithm data determine
the finite sum. Successful checks feed the refined square-contribution estimate. -/
def halfPeriodWeightCheck (r J : ℕ) (T V : ℚ) (l : ℕ → ℚ) : Bool :=
  (@decide (∀ j ∈ Finset.range (J + 1), j ≠ 0 → 0 ≤ l j ∧ T ≤ 4 * l j)
      Finset.decidableDforallFinset) &&
    decide
      ((r : ℚ) / 2 *
          (∑ j ∈ Finset.range (J + 1), if j = 0 then T ^ 2 / 8 else max 0 (l j * (T - 2 * l j))) ≤
        V)

/-- Successful rational half-period checks imply the corresponding real sign
conditions and weight-sum bound. Reflect the finite tests and commute the rational
cast with the sum, maximum, and arithmetic. This supplies the square certificate. -/
theorem halfPeriodWeightCheck_sound {r J : ℕ} {T V : ℚ} {l : ℕ → ℚ}
    (h : halfPeriodWeightCheck r J T V l = true) :
    (∀ j ∈ Finset.range (J + 1), j ≠ 0 → 0 ≤ (l j : ℝ) ∧ (T : ℝ) ≤ 4 * (l j : ℝ)) ∧
      (r : ℝ) / 2 *
          (∑ j ∈ Finset.range (J + 1),
            if j = 0 then (T : ℝ) ^ 2 / 8 else max 0 ((l j : ℝ) * ((T : ℝ) - 2 * (l j : ℝ)))) ≤
        (V : ℝ) := by
  let : Decidable (∀ j ∈ Finset.range (J + 1), j ≠ 0 → 0 ≤ l j ∧ T ≤ 4 * l j) :=
    Finset.decidableDforallFinset
  have hh := Bool.and_eq_true_iff.mp h
  have hc :
    (∀ j ∈ Finset.range (J + 1), j ≠ 0 → 0 ≤ l j ∧ T ≤ 4 * l j) ∧
      (r : ℚ) / 2 *
          (∑ j ∈ Finset.range (J + 1), if j = 0 then T ^ 2 / 8 else max 0 (l j * (T - 2 * l j))) ≤
        V :=
    ⟨of_decide_eq_true hh.1, of_decide_eq_true hh.2⟩
  constructor
  · intro j hj hj0
    have hn := Rat.cast_nonneg (K := ℝ) |>.mpr (hc.1 j hj hj0).1
    have ht := (Rat.cast_le (K := ℝ)).mpr (hc.1 j hj hj0).2
    exact ⟨hn, by simpa only [Rat.cast_mul, Rat.cast_ofNat] using ht⟩
  · have hv := (Rat.cast_le (K := ℝ)).mpr hc.2
    have hs :
      ((∑ j ∈ Finset.range (J + 1), if j = 0 then T ^ 2 / 8 else max 0 (l j * (T - 2 * l j)) : ℚ) :
          ℝ) =
        ∑ j ∈ Finset.range (J + 1),
          if j = 0 then (T : ℝ) ^ 2 / 8 else max 0 ((l j : ℝ) * ((T : ℝ) - 2 * (l j : ℝ))) := by
      change
        (Rat.castHom ℝ)
            (∑ j ∈ Finset.range (J + 1), if j = 0 then T ^ 2 / 8 else max 0 (l j * (T - 2 * l j))) =
          _
      rw [map_sum]
      simp only [Rat.coe_castHom, apply_ite, Rat.cast_div, Rat.cast_pow, Rat.cast_zero,
        Rat.cast_ofNat, Rat.cast_mul, Rat.cast_sub, Rat.cast_max]
    simpa only [hs, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hv

/-- Bound the square-index Mangoldt contribution by a checked rational value.
Supply a root-count bound, endpoint logarithm bounds, and enough half-periods to
cover the square-root cutoff. Apply the interval estimate and the checked weight sum.
This connects rational half-period data to the refined residue-gap criterion. -/
theorem square_residue_sum_le_of_half_period_check {q r J : ℕ} [NeZero q] (hq : 2 < q)
    (a : (ZMod q)ˣ) (hroot : Nat.card { z : ZMod q // z ^ 2 = (a : ZMod q) } ≤ r) {x : ℝ} {T V : ℚ}
    (hx : 1 < x) (hT : Real.log x ≤ (T : ℝ)) (hJ : (2 * ⌊Real.sqrt x⌋₊) / q ≤ J)
    (hbase : Real.log x ≤ 4 * Real.log ((q : ℝ) / 2)) (l : ℕ → ℚ)
    (hl : ∀ j ∈ Finset.range (J + 1), j ≠ 0 → (l j : ℝ) ≤ Real.log ((j : ℝ) * q / 2))
    (hc : halfPeriodWeightCheck r J T V l = true) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ IsSquare n ∧ (n : ZMod q) = (a : ZMod q)),
        ArithmeticFunction.vonMangoldt n * Real.log (x / (n : ℝ))) ≤
      (V : ℝ) := by
  have hg := halfPeriodWeightCheck_sound hc
  exact
    (square_residue_sum_le_half_period_intervals hq a hroot hx hT J hJ hbase (fun j ↦ (l j : ℝ)) hl
          (fun j hj hj0 ↦ (hg.1 j hj hj0).1) (fun j hj hj0 ↦ (hg.1 j hj hj0).2)).trans
      hg.2

/-- Check the nonnegative rational coefficients used in the parity interval bound.
Supply the totient, cutoff and square-root lower bounds, and logarithm upper bounds.
The two signs permit enlarging square-root multipliers in the character estimate. -/
def residueParitySignCheck (h : ℕ) (X s L T : ℚ) : Bool :=
  decide
    (0 ≤
        ((h : ℚ) - 1) * (L - 1719 / 1000) + 693148 / 1000000 +
          (((h : ℚ) - 1) / 20 + ((h : ℚ) - 2) * (T + 1 + 29 / 100) +
              (h : ℚ) * (693148 / 1000000 + 29 / 100)) /
            X ∧
      0 ≤ T - (1 + 23 / 40) + 1839 / 1000 / X + 1 / (20 * s))

/-- Successful rational sign checks imply the real coefficient conditions.
Reflect the two inequalities and commute casts with arithmetic. This supplies the
nonnegativity guards required by the parity-averaged interval comparison. -/
theorem residueParitySignCheck_sound {h : ℕ} {X s L T : ℚ}
    (hc : residueParitySignCheck h X s L T = true) :
    0 ≤ residueParityIntervalCoefficient h X L T ∧
      0 ≤ (T : ℝ) - (1 + 23 / 40) + (1839 / 1000 : ℝ) / X + 1 / (20 * s) := by
  have hr :
    (0 ≤
        ((h : ℚ) - 1) * (L - 1719 / 1000) + 693148 / 1000000 +
          (((h : ℚ) - 1) / 20 + ((h : ℚ) - 2) * (T + 1 + 29 / 100) +
              (h : ℚ) * (693148 / 1000000 + 29 / 100)) /
            X ∧
      0 ≤ T - (1 + 23 / 40) + 1839 / 1000 / X + 1 / (20 * s)) :=
    of_decide_eq_true hc
  have hC := Rat.cast_nonneg (K := ℝ) |>.mpr hr.1
  have hR := Rat.cast_nonneg (K := ℝ) |>.mpr hr.2
  constructor
  · simpa only [residueParityIntervalCoefficient, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
      Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using hC
  · simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_one] using hR

/-- A checked sign certificate permits the parity interval comparison.
For moduli from 64 to 20000 and cutoff at least 65536, supply logarithm and
square-root intervals. Reflect the signs and apply the analytic interval bound.
This connects finite sign checks to the nonprincipal residue-character estimate. -/
theorem residueNonprincipalParityUpper_le_of_sign_check {q : ℕ} (hq : 64 ≤ q) (hu : q ≤ 20000)
    {x : ℝ} (hh : (2 : ℝ) ≤ q.totient) (hx : 65536 ≤ x) {X s S L T : ℚ} (hX0 : (0 : ℝ) < X)
    (hX : (X : ℝ) ≤ x) (hs0 : (0 : ℝ) < s) (hs : (s : ℝ) ≤ Real.sqrt x) (hS : Real.sqrt x ≤ (S : ℝ))
    (hL : Real.log q ≤ (L : ℝ)) (hT : Real.log x ≤ (T : ℝ))
    (hc : residueParitySignCheck q.totient X s L T = true) :
    residueNonprincipalParityUpper q x ≤ residueParityIntervalUpper q.totient X s S L T := by
  have hg := residueParitySignCheck_sound hc
  exact residueNonprincipalParityUpper_le_interval hq hu hh hx hX0 hX hs0 hs hS hL hT hg.1 hg.2

/-- Check that rational composite and character majorants lie strictly below
the principal interval lower bound. Supply the totient, distinct-prime count,
cutoff intervals, and the two majorants. This is the final arithmetic gap test. -/
def refinedResidueGapCheck (h w : ℕ) (X S T U N : ℚ) : Bool :=
  decide ((h : ℚ) * U + N < X - 1839 / 1000 * T - 1 - (S + 1) / 20 - (w : ℚ) * T ^ 2 / 2)

/-- A successful rational gap test gives the real strict comparison.
Reflect the inequality, commute rational casts, and normalize the prime-factor term.
This supplies the strict gap in the least-prime residue criterion. -/
theorem refinedResidueGapCheck_sound {h w : ℕ} {X S T U N : ℚ}
    (hc : refinedResidueGapCheck h w X S T U N = true) :
    (h : ℝ) * (U : ℝ) + (N : ℝ) <
      (X : ℝ) - 1839 / 1000 * (T : ℝ) - 1 - ((S : ℝ) + 1) / 20 - (1 / 2 : ℝ) * w * (T : ℝ) ^ 2 := by
  have hr : (h : ℚ) * U + N < X - 1839 / 1000 * T - 1 - (S + 1) / 20 - (w : ℚ) * T ^ 2 / 2 :=
    of_decide_eq_true hc
  have hs := (Rat.cast_lt (K := ℝ)).mpr hr
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_one] at hs
  convert hs using 1
  ring

open Classical in
/-- Under RH, a successful rational gap test bounds the least prime in a unit residue.
Supply certified upper bounds for a prime-free residue sum and the nonprincipal
character norms, along with cutoff intervals and cutoff at least 65536.
Combine the checked strict gap with the principal lower bound. This is the final
connection from refined certificate components to a least-prime bound. -/
theorem exists_least_prime_in_residue_le_of_interval_gap_check {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hRH : RiemannHypothesis) {x : ℝ} {X S T U N : ℚ} (hx : 65536 ≤ x) (hX : (X : ℝ) ≤ x)
    (hS : Real.sqrt x ≤ (S : ℝ)) (hT : Real.log x ≤ (T : ℝ))
    (hu :
      (∀ p : ℕ, p.Prime → (p : ZMod q) = (a : ZMod q) → ¬(p : ℝ) ≤ x) →
        (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = (a : ZMod q)),
            AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) ≤
          (U : ℝ))
    (hn :
      (∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator (⊥ : Subgroup (ZMod q)ˣ)),
          ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.val‖) ≤
        (N : ℝ))
    (hc : refinedResidueGapCheck q.totient q.primeFactors.card X S T U N = true) :
    ∃ p : ℕ, IsLeast {v : ℕ | v.Prime ∧ (v : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ x := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only) hx
  exact
    exists_least_prime_in_residue_le_of_weighted_gap a hRH hx1 hu hn
      ((refinedResidueGapCheck_sound hc).trans_le (cosetPrincipalLower_ge_interval hx hX hS hT))

/-- Check a rational upper bound for the parity-averaged character interval expression.
Supply the totient, cutoff and square-root intervals, logarithm upper bounds,
and a proposed character majorant. Successful checks provide the character term
for the final refined residue-gap comparison. -/
def residueParityUpperCheck (h : ℕ) (X s S L T N : ℚ) : Bool :=
  decide
    ((S + 19 / 6) *
          (((h : ℚ) - 1) * (L - 1719 / 1000) + 693148 / 1000000 +
            (((h : ℚ) - 1) / 20 + ((h : ℚ) - 2) * (T + 1 + 29 / 100) +
                (h : ℚ) * (693148 / 1000000 + 29 / 100)) /
              X) +
        ((h : ℚ) - 1) *
          (T ^ 2 + (2 / 3 * (L - 1144 / 1000) + 4) * T + T / 2 * (693148 / 1000000 + T)) +
        2 * (S + 19 / 6) * (T - (1 + 23 / 40) + 1839 / 1000 / X + 1 / (20 * s)) ≤
      N)

/-- A successful rational character-bound check bounds the real interval expression.
Reflect the inequality and commute rational casts with its arithmetic.
This supplies a rational upper bound usable in the final residue-gap test. -/
theorem residueParityUpperCheck_sound {h : ℕ} {X s S L T N : ℚ}
    (hc : residueParityUpperCheck h X s S L T N = true) :
    residueParityIntervalUpper h X s S L T ≤ (N : ℝ) := by
  have hr :
    (S + 19 / 6) *
          (((h : ℚ) - 1) * (L - 1719 / 1000) + 693148 / 1000000 +
            (((h : ℚ) - 1) / 20 + ((h : ℚ) - 2) * (T + 1 + 29 / 100) +
                (h : ℚ) * (693148 / 1000000 + 29 / 100)) /
              X) +
        ((h : ℚ) - 1) *
          (T ^ 2 + (2 / 3 * (L - 1144 / 1000) + 4) * T + T / 2 * (693148 / 1000000 + T)) +
        2 * (S + 19 / 6) * (T - (1 + 23 / 40) + 1839 / 1000 / X + 1 / (20 * s)) ≤
      N :=
    of_decide_eq_true hc
  have hs := (Rat.cast_le (K := ℝ)).mpr hr
  simpa only [residueParityIntervalUpper, residueParityIntervalCoefficient, Rat.cast_add,
    Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one] using hs

open Classical in
/-- Under GRH, checked parity signs and a checked rational majorant bound the
nonprincipal residue-character norms. For moduli from 64 to 20000 and cutoff at
least 65536, supply certified logarithm and square-root intervals.
Combine the parity-averaged estimate, sign-checked interval comparison, and rational
majorant check. This provides the character input to the least-prime gap criterion. -/
theorem nonprincipal_residue_logWeightedNorm_sum_le_of_parity_checks {q : ℕ} [NeZero q]
    (hq : 64 ≤ q) (hu : q ≤ 20000) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hh : (2 : ℝ) ≤ q.totient) (hx : 65536 ≤ x) {X s S L T N : ℚ} (hX0 : (0 : ℝ) < X)
    (hX : (X : ℝ) ≤ x) (hs0 : (0 : ℝ) < s) (hs : (s : ℝ) ≤ Real.sqrt x) (hS : Real.sqrt x ≤ (S : ℝ))
    (hL : Real.log q ≤ (L : ℝ)) (hT : Real.log x ≤ (T : ℝ))
    (hc : residueParitySignCheck q.totient X s L T = true)
    (hN : residueParityUpperCheck q.totient X s S L T N = true) :
    (∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator (⊥ : Subgroup (ZMod q)ˣ)),
        ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.val‖) ≤
      (N : ℝ) := by
  have hi := residueNonprincipalParityUpper_le_of_sign_check hq hu hh hx hX0 hX hs0 hs hS hL hT hc
  exact
    (nonprincipal_residue_logWeightedNorm_sum_le_parity_explicit hq hGRH hx).trans
      (hi.trans (residueParityUpperCheck_sound hN))

/-- Check a rational upper bound for the finite corrected odd-root sum.
Supply the exponent limit, lower cutoff logarithm, and natural root bounds.
This check supplies the odd contribution to the final residue-gap comparison. -/
def correctedOddRootSumCheck (K : ℕ) (t O : ℚ) (b c : ℕ → ℕ) : Bool :=
  decide
    ((∑ k ∈ (Finset.Icc 3 K).filter Odd,
        ((k : ℚ) * (b k + c k / 20) - 183 / 100 * t - (k : ℚ) / 2)) ≤
      O)

/-- A successful rational odd-sum check bounds the corresponding real sum.
Reflect the inequality and commute the rational cast with the finite sum.
Combine this with the power and sign checks to bound actual odd prime powers. -/
theorem correctedOddRootSumCheck_sound {K : ℕ} {t O : ℚ} {b c : ℕ → ℕ}
    (hc : correctedOddRootSumCheck K t O b c = true) :
    (∑ k ∈ (Finset.Icc 3 K).filter Odd,
        ((k : ℝ) * ((b k : ℝ) + (c k : ℝ) / 20) - 183 / 100 * (t : ℝ) - (k : ℝ) / 2)) ≤
      (O : ℝ) := by
  have hr :
    (∑ k ∈ (Finset.Icc 3 K).filter Odd,
        ((k : ℚ) * (b k + c k / 20) - 183 / 100 * t - (k : ℚ) / 2)) ≤
      O :=
    of_decide_eq_true hc
  have hs := (Rat.cast_le (K := ℝ)).mpr hr
  change (Rat.castHom ℝ) _ ≤ _ at hs
  rw [map_sum] at hs
  simpa only [Rat.coe_castHom, Rat.cast_sub, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_ofNat] using hs

open Classical in
/-- Under GRH, seven successful rational checks bound the least prime in a unit residue.
For moduli from 64 to 20000 and cutoff at least 65536, supply cutoff and logarithm
intervals, a square-root count bound, half-period endpoint logarithm bounds, and
a certified exponent limit. The checks bound the square and odd contributions,
the character norms, and the final strict gap.
Combine the checked analytic estimates and contradict a prime-free residue.
This is the common soundness theorem for refined small-modulus certificate data. -/
theorem exists_least_prime_in_residue_le_of_refined_checks {q r J K : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hq : 64 ≤ q) (hu : q ≤ 20000) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} {X P s S L T t V O N : ℚ} (hh : (2 : ℝ) ≤ q.totient) (hx : 65536 ≤ x)
    (hX0 : (0 : ℝ) < X) (hX : (X : ℝ) ≤ x) (hP : x ≤ (P : ℝ)) (hs0 : (0 : ℝ) < s)
    (hs : (s : ℝ) ≤ Real.sqrt x) (hS : Real.sqrt x ≤ (S : ℝ)) (hL : Real.log q ≤ (L : ℝ))
    (hT : Real.log x ≤ (T : ℝ)) (ht : (t : ℝ) ≤ Real.log x)
    (hroot : Nat.card { z : ZMod q // z ^ 2 = (a : ZMod q) } ≤ r)
    (hJ : (2 * ⌊Real.sqrt x⌋₊) / q ≤ J) (hbase : Real.log x ≤ 4 * Real.log ((q : ℝ) / 2))
    (l : ℕ → ℚ) (hl : ∀ j ∈ Finset.range (J + 1), j ≠ 0 → (l j : ℝ) ≤ Real.log ((j : ℝ) * q / 2))
    (hK : ⌊Real.log x / Real.log 2⌋₊ ≤ K) (b c : ℕ → ℕ)
    (hweights : halfPeriodWeightCheck r J T V l = true) (hpowers : oddRootPowerCheck P K b c = true)
    (hpositive : correctedOddRootNonnegCheck K t b c = true)
    (hodd : correctedOddRootSumCheck K t O b c = true)
    (hsigns : residueParitySignCheck q.totient X s L T = true)
    (hnorm : residueParityUpperCheck q.totient X s S L T N = true)
    (hgap : refinedResidueGapCheck q.totient q.primeFactors.card X S T (V + O) N = true) :
    ∃ p : ℕ, IsLeast {v : ℕ | v.Prime ∧ (v : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ x := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only) hx
  have hq2 : 2 < q := lt_of_lt_of_le (by norm_num only) hq
  have hsq := square_residue_sum_le_of_half_period_check hq2 a hroot hx1 hT hJ hbase l hl hweights
  have ho :=
    (AnalyticNumberTheory.Arithmetic.nonsquareCompositeLogWeightedSum_le_odd_powers
          (zero_lt_one.trans hx1)).trans
      ((oddPrimePowerLogWeightedSum_le_of_corrected_checks hGRH.riemann hx1 hP ht hK b c hpowers
            hpositive).trans
        (correctedOddRootSumCheck_sound hodd))
  have hn :=
    nonprincipal_residue_logWeightedNorm_sum_le_of_parity_checks hq hu hGRH hh hx hX0 hX hs0 hs hS
      hL hT hsigns hnorm
  apply exists_least_prime_in_residue_le_of_interval_gap_check a hGRH.riemann hx hX hS hT _ hn hgap
  intro hno
  have hc :=
    (AnalyticNumberTheory.Arithmetic.residue_logWeightedSum_le_square_add_nonsquare (a : ZMod q)
          (zero_lt_one.trans hx1) hno).trans
      (add_le_add hsq ho)
  simpa only [Rat.cast_add] using hc

/-- Lower bounds for the modulus and index logarithms, together with an upper
bound for log two, bound a half-period endpoint logarithm. Require positive natural
modulus and index. Expand the logarithm of the quotient and product and combine
the three interval inequalities. This constructs endpoint bounds from shared data. -/
theorem halfPeriodEndpointLog_lower {q j : ℕ} (hq : 0 < q) (hj : 0 < j) {Q D B : ℝ}
    (hQ : Q ≤ Real.log q) (hD : D ≤ Real.log j) (hB : Real.log 2 ≤ B) :
    Q + D - B ≤ Real.log ((j : ℝ) * q / 2) := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  rw [Real.log_div (mul_ne_zero hj0 hq0) (by norm_num only), Real.log_mul hj0 hq0]
  linarith only [hQ, hD, hB]

/-- Shared logarithm intervals and a checked half-period weight sum bound square
Mangoldt contributions. Supply a modulus logarithm lower bound, a log-two upper bound,
and index logarithm lower bounds over the required half-periods. Construct each
endpoint bound from these intervals and apply the checked square estimate.
This avoids supplying a separate analytic proof for every endpoint of every modulus. -/
theorem square_residue_sum_le_of_log_interval_checks {q r J : ℕ} [NeZero q] (hq : 2 < q)
    (a : (ZMod q)ˣ) (hroot : Nat.card { z : ZMod q // z ^ 2 = (a : ZMod q) } ≤ r) {x : ℝ}
    {T V Q B : ℚ} (hx : 1 < x) (hT : Real.log x ≤ (T : ℝ)) (hJ : (2 * ⌊Real.sqrt x⌋₊) / q ≤ J)
    (hbase : Real.log x ≤ 4 * Real.log ((q : ℝ) / 2)) (D : ℕ → ℚ) (hQ : (Q : ℝ) ≤ Real.log q)
    (hB : Real.log 2 ≤ (B : ℝ)) (hD : ∀ j ∈ Finset.range (J + 1), j ≠ 0 → (D j : ℝ) ≤ Real.log j)
    (hc : halfPeriodWeightCheck r J T V (fun j ↦ Q + D j - B) = true) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ IsSquare n ∧ (n : ZMod q) = (a : ZMod q)),
        ArithmeticFunction.vonMangoldt n * Real.log (x / (n : ℝ))) ≤
      (V : ℝ) := by
  apply
    square_residue_sum_le_of_half_period_check hq a hroot hx hT hJ hbase (fun j ↦ Q + D j - B) _ hc
  intro j hj hj0
  simpa only [Rat.cast_add, Rat.cast_sub] using
    halfPeriodEndpointLog_lower (Nat.zero_lt_of_lt hq) (Nat.pos_of_ne_zero hj0) hQ (hD j hj hj0) hB

/-- A square-root upper bound and a strict rationalizable endpoint comparison
bound the last occupied half-period index. Require a positive modulus.
Bound the natural floor by the square root, then use natural division.
This certifies the number of half-period blocks in refined residue data. -/
theorem halfPeriodIndex_le_of_sqrt_upper {q J : ℕ} (hq : 0 < q) {x S : ℝ} (hS : Real.sqrt x ≤ S)
    (hJ : 2 * S < (J + 1 : ℝ) * q) : (2 * ⌊Real.sqrt x⌋₊) / q ≤ J := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hq).mpr
  apply (Nat.cast_lt (α := ℝ)).mp
  have hf := Nat.floor_le (Real.sqrt_nonneg x)
  have hi : 2 * (⌊Real.sqrt x⌋₊ : ℝ) < (J + 1 : ℝ) * q := by linarith only [hf, hS, hJ]
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ] using hi

/-- An upper cutoff logarithm below the certified log-two multiple bounds
the natural exponent limit. Use the fixed lower bound for log two and the floor
comparison. This replaces a real exponent-range proof by a rational inequality
in refined residue certificates. -/
theorem logCutoff_exponentBound_of_rational_upper {x : ℝ} {T : ℚ} {K : ℕ}
    (hT : Real.log x ≤ (T : ℝ)) (hK : T < (K + 1) * (6931471803 / 10000000000 : ℚ)) :
    ⌊Real.log x / Real.log 2⌋₊ ≤ K := by
  have hk := (Rat.cast_lt (K := ℝ)).mpr hK
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_div,
    Rat.cast_ofNat] at hk
  apply Nat.le_of_lt_succ
  apply (Nat.floor_lt' (Nat.succ_ne_zero K)).mpr
  apply (div_lt_iff₀ (Real.log_pos (by norm_num only : (1 : ℝ) < 2))).mpr
  have hm : (K + 1 : ℝ) * (6931471803 / 10000000000) ≤ (K + 1 : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by linarith only [Real.log_two_gt_d9])
      (add_nonneg (Nat.cast_nonneg K) zero_le_one)
  simpa only [Nat.cast_succ] using hT.trans_lt (hk.trans_le hm)

/-- A checked modulus logarithm interval encloses the squared totient-log cutoff.
The positive rational lower radius and its minimum square give positivity, the cutoff
threshold, and both square-root bounds. Multiply by the supplied totient, square the
nonnegative bounds, and evaluate the square root of the squared radius.
These bounds supply the geometric hypotheses of refined residue certificates. -/
theorem totientLogCutoff_interval_bounds {q h j n : ℕ} {lo hi : ℚ}
    (hc : Analysis.rationalLogIntervalCheck q j n lo hi = true) (hs : 0 < (h : ℚ) * lo)
    (hm : 65536 ≤ ((h : ℚ) * lo) ^ 2) :
    0 < (h : ℝ) * (lo : ℝ) ∧
      65536 ≤ ((h : ℝ) * Real.log q) ^ 2 ∧
      ((h : ℝ) * (lo : ℝ)) ^ 2 ≤ ((h : ℝ) * Real.log q) ^ 2 ∧
      ((h : ℝ) * Real.log q) ^ 2 ≤ ((h : ℝ) * (hi : ℝ)) ^ 2 ∧
      (h : ℝ) * (lo : ℝ) ≤ Real.sqrt (((h : ℝ) * Real.log q) ^ 2) ∧
      Real.sqrt (((h : ℝ) * Real.log q) ^ 2) ≤ (h : ℝ) * (hi : ℝ) := by
  have hl := Analysis.rationalLogIntervalCheck_sound hc
  simp only [Rat.cast_natCast] at hl
  have hsl := mul_le_mul_of_nonneg_left hl.1 (Nat.cast_nonneg h : (0 : ℝ) ≤ h)
  have hsu := mul_le_mul_of_nonneg_left hl.2 (Nat.cast_nonneg h : (0 : ℝ) ≤ h)
  have hs0 := (Rat.cast_pos (K := ℝ)).mpr hs
  simp only [Rat.cast_mul, Rat.cast_natCast] at hs0
  have hr0 := hs0.le.trans hsl
  have hxl := pow_le_pow_left₀ hs0.le hsl 2
  have hxu := pow_le_pow_left₀ hr0 hsu 2
  have hmR := (Rat.cast_le (K := ℝ)).mpr hm
  simp only [Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at hmR
  have hsq := Real.sqrt_sq hr0
  exact ⟨hs0, hmR.trans hxl, hxl, hxu, hsq.symm ▸ hsl, hsq.symm ▸ hsu⟩

/-- Checked logarithms at positive rational cutoff endpoints enclose the cutoff logarithm.
The lower and upper checks may use independent binary scales and Taylor lengths.
Monotonicity of the real logarithm transports their bounds to the actual cutoff.
The resulting interval controls the odd-power correction and character error terms. -/
theorem cutoffLog_interval_bounds_of_checks {x : ℝ} {X P t T R : ℚ} {jl nl ju nu : ℕ}
    (hX0 : (0 : ℝ) < X) (hX : (X : ℝ) ≤ x) (hP : x ≤ (P : ℝ))
    (hl : Analysis.rationalLogIntervalCheck X jl nl t R = true)
    (hu : Analysis.rationalLogIntervalCheck P ju nu 0 T = true) :
    (t : ℝ) ≤ Real.log x ∧ Real.log x ≤ (T : ℝ) := by
  have hlow := (Analysis.rationalLogIntervalCheck_sound hl).1
  have hupp := (Analysis.rationalLogIntervalCheck_sound hu).2
  exact ⟨hlow.trans (Real.log_le_log hX0 hX), (Real.log_le_log (hX0.trans_le hX) hP).trans hupp⟩

/-- Modulus and cutoff logarithm bounds certify decreasing square weights after the
first half-period. Assume a positive modulus, a lower modulus logarithm bound, an upper
log-two bound, and a cutoff logarithm bound satisfying the rational base threshold.
The endpoint logarithm identity and linear comparison give the required base condition
for the half-period square estimate. -/
theorem halfPeriodBase_of_log_interval_bounds {q : ℕ} (hq : 0 < q) {x : ℝ} {Q B T : ℝ}
    (hQ : Q ≤ Real.log q) (hB : Real.log 2 ≤ B) (hT : Real.log x ≤ T) (hb : T ≤ 4 * (Q - B)) :
    Real.log x ≤ 4 * Real.log ((q : ℝ) / 2) := by
  have he :=
    halfPeriodEndpointLog_lower (j := 1) (D := 0) hq (by decide +kernel) hQ
      (by norm_num only [Nat.cast_one, Real.log_one]) hB
  simp only [Nat.cast_one, one_mul, add_zero] at he
  linarith only [he, hT, hb]

end PseudoPrime.LLS.PaperStatements
