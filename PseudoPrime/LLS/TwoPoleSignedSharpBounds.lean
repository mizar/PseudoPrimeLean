/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleSignedBounds

/-! # Direct signed two-pole error bounds and variable affine margins -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For every natural level q, log(max(20000,q)) is at most log q+15.
Split the maximum and bound log 20000 using log 100. This removes a superfluous
large-log hypothesis from ambient pole estimates. -/
theorem twoPole_log_max_le_unconditional (q : ℕ) :
    Real.log (max 20000 q : ℕ) ≤ Real.log q + 15 := by
  have hb : Real.log (20000 : ℝ) ≤ 15 := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 20000)
        (by norm_num only : (20000 : ℝ) ≤ 100 ^ 3)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h, twoPole_log_hundred_le_nineteen_fourths]
  by_cases hq : 20000 ≤ q
  · rw [max_eq_right hq]
    linarith only
  · rw [max_eq_left (le_of_not_ge hq)]
    norm_num only [Nat.cast_ofNat]
    linarith only [hb, Real.log_natCast_nonneg q]

/-- For L at least 1000, root at least 3L/5 and endpoint logs at most L/40,
the paired ramp numerator is at most s(s/200+2). Rational polynomial arithmetic
proves the bound without interval certificates. This lowers the common error gate. -/
theorem twoPole_error_algebra_sharp {L s A B : ℝ} (hL : 1000 ≤ L) (hs : (3 / 5 : ℝ) * L ≤ s)
    (hA : A ≤ L / 40) (hB : B ≤ L / 40) :
    (3 / 2 : ℝ) * (s / 20 * (63 / 40) + (1839 / 1000) * A + 21 / 20) +
        42 *
          (((11 / 200 : ℝ) * s ^ 2 + 101 * ((2 / 25 : ℝ) * s + (1839 / 1000) * B + 21 / 20)) /
            494) ≤
      s * (s / 200 + 2) := by
  nlinarith only [hL, hs, hA, hB, sq_nonneg s]

/-- At log q at least 1000, every admissible controlled root gives signed gap at
least (821/1000)r-log(q)/2-299/20. Bound the actual left allowance by 7/100, alongside
the principal, pole and paired-ramp errors. No RH is needed for the scalar bound. -/
theorem signedTwoPoleGap_lower_sharp {q : ℕ} (hL : 1000 ≤ Real.log q) {r : ℝ}
    (hrange : (3 / 5 : ℝ) * Real.log q + 18 ≤ r)
    (hA : Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ Real.log q / 40)
    (hB : Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ Real.log q / 40) :
    (821 / 1000 : ℝ) * r - Real.log q / 2 - 299 / 20 ≤ signedTwoPoleGap q (r ^ 2) := by
  let L := Real.log q
  let x := r ^ 2
  let s := Real.sqrt x
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hrange, hL, sq_nonneg (r - 1)]
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hspos : 0 < s := Real.sqrt_pos.mpr hxpos
  have hs2 : s ^ 2 = x := Real.sq_sqrt hxpos.le
  have hr : 0 < r := by linarith only [hrange, hL]
  have hs : s = r := Real.sqrt_sq hr.le
  have hroot : (3 / 5 : ℝ) * L + 18 ≤ s := by
    rw [hs]; exact hrange
  have hlogx : Real.log x ≤ L / 40 :=
    (Real.log_le_log hxpos (show x ≤ (99 / 40 : ℝ) * x by linarith only [hxpos])).trans hA
  have hEa :=
    twoPole_error_algebra_sharp hL (show (3 / 5 : ℝ) * L ≤ s by linarith only [hroot]) hA hB
  rw [hs2] at hEa
  have hE : gammaRampPairedErrorNumerator x / s ≤ s / 200 + 2 := by
    apply (div_le_iff₀ hspos).mpr
    dsimp only [gammaRampPairedErrorNumerator, rampSmoothedIncrementError,
      rampExtendedSmoothedError]
    rw [mul_comm x (99 / 40 : ℝ)]
    exact hEa.trans_eq (mul_comm _ _)
  have hP : (s / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / s ≤ 1 / 2 := by
    apply (div_le_iff₀ hspos).mpr
    nlinarith only [hlogx, hroot, hL]
  have hQ := twoPole_log_max_le_unconditional q
  have hPole : ((7 / 6 : ℝ) * Real.log (max 20000 q : ℕ) + 4) / s ≤ 2 := by
    apply (div_le_iff₀ hspos).mpr
    nlinarith only [hQ, hroot, hL]
  have hpow : x ^ (-9 / 16 : ℝ) ≤ s⁻¹ := by
    have h :=
      Real.rpow_le_rpow_of_exponent_le hx (show (-9 / 16 : ℝ) ≤ -(1 / 2 : ℝ) by norm_num only)
    rw [Real.rpow_neg hxpos.le, ← Real.sqrt_eq_rpow] at h
    exact h
  have hLeft : 43 * x ^ (-9 / 16 : ℝ) ≤ 7 / 100 := by
    calc
      _ ≤ 43 * s⁻¹ := mul_le_mul_of_nonneg_left hpow (by norm_num only : (0 : ℝ) ≤ 43)
      _ = 43 / s := by rw [div_eq_mul_inv]
      _ ≤ 7 / 100 := (div_le_iff₀ hspos).mpr (by nlinarith only [hroot, hL])
  have hmass :
    (831 / 1000 : ℝ) * s ≤
      (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * s :=
    mul_le_mul_of_nonneg_right
      ((by norm_num only : (831 / 1000 : ℝ) ≤ 83125234337 / 100000000000).trans
        Analysis.gamma_ramp_mass_lower)
      hspos.le
  dsimp only [signedTwoPoleGap, signedTwoPoleUpper]
  nlinarith only [hE, hP, hPole, hLeft, hmass, hs, hL]

/-- For L at least 1000 and root (500/821)L+c with 18<=c<=19, the scale is
at least four and both endpoint logs are at most L/40. A global tangent and one
rational root enclosure control the full half-line without scale-specific rows. -/
theorem signedTwoPole_sharp_root_data {L c : ℝ} (hL : 1000 ≤ L) (hc : 18 ≤ c) (hc' : c ≤ 19) :
    let r := (500 / 821 : ℝ) * L + c;
    4 ≤ r ^ 2 ∧
      (3 / 5 : ℝ) * L + 18 ≤ r ∧
      Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ L / 40 ∧ Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ L / 40 := by
  let r := (500 / 821 : ℝ) * L + c
  have hr : 0 < r := by
    dsimp only [r]; linarith only [hL, hc]
  have hlo : (3 / 5 : ℝ) * L + 18 ≤ r := by
    dsimp only [r]; linarith only [hL, hc]
  have hhi : r ≤ (63 / 100 : ℝ) * L := by
    dsimp only [r]; linarith only [hL, hc']
  have hs := mul_self_le_mul_self hr.le hhi
  have hx : 4 ≤ r ^ 2 := by nlinarith only [hlo, hL, sq_nonneg (r - 2)]
  have hLp : 0 < L := by linarith only [hL]
  have ht := twoPole_log_tangent hLp
  have hb : Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ L / 40 := by
    have h :=
      Real.log_le_log (by nlinarith only [hx] : 0 < (101 / 40 : ℝ) * r ^ 2)
        (show (101 / 40 : ℝ) * r ^ 2 ≤ (101 / 100 : ℝ) * L ^ 2 by nlinarith only [hs])
    rw [Real.log_mul (by norm_num only : (101 / 100 : ℝ) ≠ 0) (pow_ne_zero 2 hLp.ne'),
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have hc0 := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 101 / 100)
    linarith only [h, hc0, ht, hL]
  have ha :=
    Real.log_le_log (by nlinarith only [hx] : 0 < (99 / 40 : ℝ) * r ^ 2)
      (show (99 / 40 : ℝ) * r ^ 2 ≤ (101 / 40 : ℝ) * r ^ 2 by nlinarith only [hx])
  exact ⟨hx, hlo, ha.trans hb, hb⟩

/-- At log A at least 1000 and additive root constant between eighteen and
nineteen, the signed gap is at least (821/1000)c-299/20. Retain c as a parameter
so witness constants can be selected without repeating the analytic proof. -/
theorem signedTwoPoleGap_affine_margin {A : ℕ} (hL : 1000 ≤ Real.log A) {c : ℝ} (hc : 18 ≤ c)
    (hc' : c ≤ 19) :
    (821 / 1000 : ℝ) * c - 299 / 20 ≤
      signedTwoPoleGap A (((500 / 821 : ℝ) * Real.log A + c) ^ 2) := by
  have hd := signedTwoPole_sharp_root_data hL hc hc'
  have h := signedTwoPoleGap_lower_sharp hL hd.2.1 hd.2.2.1 hd.2.2.2
  linarith only [h]

theorem exists_odd_prime_ne_one_le_signedTwoPole_sharp {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1000 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log A + 457 / 25) ^ 2 ∧ χ p ≠ 1 := by
  let r := (500 / 821 : ℝ) * Real.log A + 457 / 25
  let x := r ^ 2
  have hd := signedTwoPole_sharp_root_data hL (c := 457 / 25) (by norm_num only) (by norm_num only)
  have hx4 : 4 ≤ x := hd.1
  have hx : 2 ≤ x := by linarith only [hx4]
  have hxpos : 0 < x := by linarith only [hx]
  have hr : 0 < r := by
    dsimp only [r]; linarith only [hL]
  have hlocal : (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x ≤ 1 / 20 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hxpos)).mpr
    rw [Real.sqrt_sq hr.le]
    have hroot : (3 / 5 : ℝ) * Real.log A + 18 ≤ r := hd.2.1
    have hlog : Real.log ((99 / 40 : ℝ) * x) ≤ Real.log A / 40 := hd.2.2.1
    have ht := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
    linarith only [hroot, hlog, ht, hL]
  have hsep :=
    signedTwoPoleGap_affine_margin hL (c := 457 / 25) (by norm_num only) (by norm_num only)
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hC := gamma_primitive_sum_re_le_signedTwoPole_ambient χ hne hqA hGRH hx
  apply
    exists_odd_prime_ne_one_of_gamma_ramp_gap χ hquad h2 hxpos
      (show 1 ≤ (99 / 40 : ℝ) * x by nlinarith only [hx])
  dsimp only [signedTwoPoleGap] at hsep
  nlinarith only [hP, hT, hC, hsep, hlocal]

end PseudoPrime.LLS
