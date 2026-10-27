/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleRetainedScaleBounds
public import PseudoPrime.LLS.PairedEulerExcludedBounds

/-! # Rational small-prime Euler savings and the resulting affine gap -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For nonnegative a and b, the rational power bound a^(5/4) at most b follows from a^5 at most
b^4. Raise both sides to the positive fourth power and use real-power multiplication. This gives
kernel-checked rational envelopes for small Euler terms. -/
theorem rpow_five_fourths_le_of_pow_four {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 5 ≤ b ^ 4) :
    a ^ (5 / 4 : ℝ) ≤ b := by
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg ha _) hb (by norm_num only : (0 : ℝ) < 4)).mp
  rw [← Real.rpow_mul ha]
  norm_num only [show (5 / 4 : ℝ) * 4 = 5 by norm_num only, Real.rpow_ofNat]
  exact h

/-- For a prime p, a positive denominator cap b and logarithmic lower bound t, the displayed
rational number bounds the paired Euler weight below. Use the fourth-power envelope and discard
only the nonnegative logarithmic weight. This parametrizes finite Euler-prefix certificates. -/
theorem pairedEulerPrefixWeight_prime_ge_rational {p : ℕ} (hp : p.Prime) {b t : ℝ} (hb : 0 < b)
    (hpow : (p : ℝ) ^ 5 ≤ b ^ 4) (ht : t ≤ Real.log p) :
    t / b ≤ pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) p := by
  have hden := rpow_five_fourths_le_of_pow_four (Nat.cast_nonneg p) hb.le hpow
  have hp0 := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.pos) (5 / 4 : ℝ)
  have hdiv :=
    (div_le_div_of_nonneg_right ht hb.le).trans
      (div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) hp0 hden)
  have htail :
    0 ≤ (3 / 4 : ℝ) * Real.log p * ArithmeticFunction.vonMangoldt p / (p : ℝ) ^ (11 / 4 : ℝ) :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg p))
        ArithmeticFunction.vonMangoldt_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  dsimp only [pairedEulerPrefixWeight]
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp] at htail
  linarith only [hdiv, htail]

/-- The four Euler weights at primes two, three, five and seven have the displayed rational
lower bounds. Combine certified logarithms with elementary fourth-power inequalities. The
constants certify savings for both full-prime and odd-prime contradictions. -/
theorem pairedEuler_small_prime_lower :
    (4 / 15 : ℝ) ≤ pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) 2 ∧
      (1 / 4 : ℝ) ≤ pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) 3 ∧
      (3 / 16 : ℝ) ≤ pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) 5 ∧
      (1 / 8 : ℝ) ≤ pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) 7 := by
  have h2 :=
    pairedEulerPrefixWeight_prime_ge_rational Nat.prime_two (b := 5 / 2) (t := 2 / 3)
      (by norm_num only) (by norm_num only [Nat.cast_ofNat])
      (by
        norm_num only [Nat.cast_ofNat]; linarith only [Real.log_two_gt_d9])
  have h3 :=
    pairedEulerPrefixWeight_prime_ge_rational Nat.prime_three (b := 4) (t := 1) (by norm_num only)
      (by norm_num only [Nat.cast_ofNat])
      (by
        norm_num only [Nat.cast_ofNat]; linarith only [Real.log_three_gt_d9])
  have h5 :=
    pairedEulerPrefixWeight_prime_ge_rational (by norm_num only : Nat.Prime 5) (b := 8) (t := 3 / 2)
      (by norm_num only) (by norm_num only [Nat.cast_ofNat])
      (by
        norm_num only [Nat.cast_ofNat]; linarith only [Real.log_five_gt_d9])
  have hl7 := Real.log_le_log (by norm_num only : (0 : ℝ) < 5) (show (5 : ℝ) ≤ 7 by norm_num only)
  have h7 :=
    pairedEulerPrefixWeight_prime_ge_rational (by norm_num only : Nat.Prime 7) (b := 12) (t :=
      3 / 2) (by norm_num only) (by norm_num only [Nat.cast_ofNat])
      (by
        norm_num only [Nat.cast_ofNat]; linarith only [hl7, Real.log_five_gt_d9])
  norm_num only at h2 h3 h5 h7
  exact ⟨h2, h3, h5, h7⟩

/-- The support consisting of two, three, five and seven saves at least 8/5 in twice the
principal Euler prefix. Sum four rational lower bounds. This support is used only under full
small-prime triviality in the MR argument. -/
theorem pairedEuler_prefix_2357_saving :
    (8 / 5 : ℝ) ≤
      2 * ∑ n ∈ ({2,3,5,7} : Finset ℕ), pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n := by
  have h := pairedEuler_small_prime_lower
  rw [Finset.sum_insert (by decide : (2 : ℕ) ∉ {3,5,7}),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ {5,7}), Finset.sum_insert (by decide : (5 : ℕ) ∉ {7}),
    Finset.sum_singleton]
  linarith only [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- The odd support consisting of three and five saves at least 7/8 in twice the principal Euler
prefix. Sum two rational lower bounds. This avoids imposing a value at prime two in the odd
non-one comparison. -/
theorem pairedEuler_prefix_35_saving :
    (7 / 8 : ℝ) ≤
      2 * ∑ n ∈ ({3,5} : Finset ℕ), pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n := by
  have h := pairedEuler_small_prime_lower
  rw [Finset.sum_insert (by decide : (3 : ℕ) ∉ {5}), Finset.sum_singleton]
  linarith only [h.2.1, h.2.2.1]

end PseudoPrime.AnalyticNumberTheory.Arithmetic

namespace PseudoPrime.LLS

/-- For logarithmic input L at least 500, the affine root with additive constant eleven gives
scale at least four and the required endpoint cap. Compare it with the previously certified root
of additive constant twelve. These data support the saved-gap estimate. -/
theorem twoPolePrefix_root_data {L : ℝ} (hL : 500 ≤ L) :
    let r := (500 / 821 : ℝ) * L + 11;
    2 ≤ r ∧ 4 ≤ r ^ 2 ∧ Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ L / 250 + 211 / 20 := by
  let r := (500 / 821 : ℝ) * L + 11
  have hr : 2 ≤ r := by
    dsimp only [r]; linarith only [hL]
  have h0 : 0 ≤ r := by linarith only [hr]
  have hx : 4 ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 2)]
  have hd := twoPoleRetained_root_data hL (c := 12) (by norm_num only) (by norm_num only)
  have hs :=
    mul_self_le_mul_self h0
      (show r ≤ (500 / 821 : ℝ) * L + 12 by
        dsimp only [r]; linarith only)
  have ht :=
    Real.log_le_log (by nlinarith only [hx] : 0 < (101 / 40 : ℝ) * r ^ 2)
      (show (101 / 40 : ℝ) * r ^ 2 ≤ (101 / 40 : ℝ) * ((500 / 821 : ℝ) * L + 12) ^ 2 by
        nlinarith only [hs])
  exact ⟨hr, hx, ht.trans hd.2.2⟩

/-- For L at least 500 and effective Gamma cost at most 363/100, the retained numerator is at
least one tenth of the affine root. Use rational polynomial positivity in L-500. The effective
cost is justified by a prefix saving under a no-witness contradiction. -/
theorem twoPolePrefix_numerator_margin {L C : ℝ} (hL : 500 ≤ L) (hC : C ≤ 363 / 100) :
    let r := (500 / 821 : ℝ) * L + 11;
    r / 10 ≤ twoPoleRetainedNumerator L C r (L / 250 + 211 / 20) := by
  have hr : 0 ≤ (500 / 821 : ℝ) * L + 11 := by linarith only [hL]
  have hCr := mul_le_mul_of_nonneg_right hC hr
  dsimp only [twoPoleRetainedNumerator]
  nlinarith only [hL, hCr, sq_nonneg (L - 500)]

/-- For logarithmic ambient level at least 500 and effective cost at most 363/100, the
affine-root comparison gap is at least one tenth. Combine the numerator margin with its
positive-root lower bound. This is a scalar criterion for retained-prefix witnesses. -/
theorem twoPolePrefix_gap_margin {A : ℕ} {C : ℝ} (hL : 500 ≤ Real.log A) (hC : C ≤ 363 / 100) :
    (1 / 10 : ℝ) ≤ twoPoleConstantGap A C (((500 / 821 : ℝ) * Real.log A + 11) ^ 2) := by
  have hd := twoPolePrefix_root_data hL
  have hn := twoPolePrefix_numerator_margin hL hC
  have hg :=
    twoPoleConstantGap_mul_root_lower (A := A) (C := C)
      (by linarith only [hd.1] : 1 ≤ (500 / 821 : ℝ) * Real.log A + 11) hd.2.2
  have hr : 0 < (500 / 821 : ℝ) * Real.log A + 11 := by linarith only [hL]
  nlinarith only [hn, hg, hr]

/-- For logarithmic ambient level at least 500, the prime-two allowance is at most one twentieth
at the affine root. Bound the cutoff logarithm by the endpoint cap and use the certified
logarithm of two. This leaves a strict margin for odd non-one witnesses. -/
theorem twoPolePrefix_prime_two_allowance {A : ℕ} (hL : 500 ≤ Real.log A) :
    let x := ((500 / 821 : ℝ) * Real.log A + 11) ^ 2;
    (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x ≤ 1 / 20 := by
  let r := (500 / 821 : ℝ) * Real.log A + 11
  have hd := twoPolePrefix_root_data hL
  have hx : 4 ≤ r ^ 2 := hd.2.1
  have hr : 0 < r := by
    dsimp only [r]; linarith only [hL]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by nlinarith only [hx] : 0 < r ^ 2))).mpr
  rw [Real.sqrt_sq hr.le]
  have hlog :=
    (Real.log_le_log (by nlinarith only [hx] : 0 < (99 / 40 : ℝ) * r ^ 2)
          (show (99 / 40 : ℝ) * r ^ 2 ≤ (101 / 40 : ℝ) * r ^ 2 by nlinarith only [hx])).trans
      hd.2.2
  have ht := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
  dsimp only [r]
  linarith only [hL, hlog, ht]

end PseudoPrime.LLS
