/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPolePrimeTrivialBounds

/-! # Continuous affine two-pole separation from logarithm 1500 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- A nine-term positive Taylor sum proves log(100) at most nineteen fourths.
This supplies a rational constant in the continuous logarithmic scale bounds. -/
theorem twoPole_log_hundred_le_nineteen_fourths : Real.log (100 : ℝ) ≤ 19 / 4 := by
  apply (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 100)).mpr
  have ht : (100 : ℝ) ≤ ∑ k ∈ Finset.range 9, (19 / 4 : ℝ) ^ k / (k.factorial : ℝ) := by
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  exact ht.trans (Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 19 / 4) 9)

/-- For real L at least 1500, log L is at most L/80. Apply the logarithmic tangent
bound to L/100 and the certified bound for log 100. This controls scale logarithms
without partitioning the analytic half-line into numerical cells. -/
theorem twoPole_log_le_eightieth {L : ℝ} (hL : 1500 ≤ L) : Real.log L ≤ L / 80 := by
  have hp : 0 < L := by linarith only [hL]
  have h := Real.log_le_sub_one_of_pos (div_pos hp (by norm_num only : (0 : ℝ) < 100))
  rw [Real.log_div hp.ne' (by norm_num only : (100 : ℝ) ≠ 0)] at h
  linarith only [h, twoPole_log_hundred_le_nineteen_fourths, hL]

/-- When log q is at least 1500, the auxiliary ambient logarithm is at most log q+15.
Split the maximum and bound log 20000 through log(100 cubed). This controls the
small-conductor pole allowance uniformly. -/
theorem twoPole_log_max_le {q : ℕ} (hL : 1500 ≤ Real.log q) :
    Real.log (max 20000 q : ℕ) ≤ Real.log q + 15 := by
  have h100 := twoPole_log_hundred_le_nineteen_fourths
  have hb : Real.log (20000 : ℝ) ≤ 15 := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 20000)
        (by norm_num only : (20000 : ℝ) ≤ 100 ^ 3)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h, h100]
  by_cases hq : 20000 ≤ q
  · rw [max_eq_right hq]
    linarith only
  · rw [max_eq_left (le_of_not_ge hq)]
    norm_num only [Nat.cast_ofNat]
    linarith only [hb, hL]

/-- For L at least 1500, root s at least 3L/5 and endpoint logarithms at most L/40,
the paired-ramp error is at most s(s/200+2). Rational polynomial arithmetic proves
the comparison. This is the reusable scalar error bound for variable roots. -/
theorem twoPole_error_algebra_general {L s A B : ℝ} (hL : 1500 ≤ L) (hs : (3 / 5 : ℝ) * L ≤ s)
    (hA : A ≤ L / 40) (hB : B ≤ L / 40) :
    (3 / 2 : ℝ) * (s / 20 * (63 / 40) + (1839 / 1000) * A + 21 / 20) +
        42 *
          (((11 / 200 : ℝ) * s ^ 2 + 101 * ((2 / 25 : ℝ) * s + (1839 / 1000) * B + 21 / 20)) /
            494) ≤
      s * (s / 200 + 2) := by
  nlinarith only [hL, hs, hA, hB, sq_nonneg s]

/-- At r=(500/821)L+30 and L at least 1500, r squared is at least one, r is at least
3L/5+18 and both endpoint logarithms are at most L/40. Bound r above by 6291L/10000,
then use logarithmic monotonicity and the global tangent estimate.
This supplies uniform data for the affine two-pole scale. -/
theorem twoPole_affine_data {L : ℝ} (hL : 1500 ≤ L) :
    let r := (500 / 821 : ℝ) * L + 30;
    1 ≤ r ^ 2 ∧
      (3 / 5 : ℝ) * L + 18 ≤ r ∧
      Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ L / 40 ∧ Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ L / 40 := by
  let r := (500 / 821 : ℝ) * L + 30
  have hr : 0 < r := by
    dsimp only [r]; linarith only [hL]
  have hlow : (3 / 5 : ℝ) * L + 18 ≤ r := by
    dsimp only [r]; linarith only [hL]
  have hhi : r ≤ (6291 / 10000 : ℝ) * L := by
    dsimp only [r]; linarith only [hL]
  have hs := mul_self_le_mul_self hr.le hhi
  have hx : 1 ≤ r ^ 2 := by nlinarith only [hlow, hL, sq_nonneg (r - 1)]
  have ha :=
    Real.log_le_log (mul_pos (by norm_num only : (0 : ℝ) < 99 / 40) (zero_lt_one.trans_le hx))
      (show (99 / 40 : ℝ) * r ^ 2 ≤ L ^ 2 by nlinarith only [hs])
  have hb :=
    Real.log_le_log (mul_pos (by norm_num only : (0 : ℝ) < 101 / 40) (zero_lt_one.trans_le hx))
      (show (101 / 40 : ℝ) * r ^ 2 ≤ L ^ 2 by nlinarith only [hs])
  rw [Real.log_pow] at ha hb
  norm_num only [Nat.cast_ofNat] at ha hb
  have hlog : 2 * Real.log L ≤ L / 40 := by linarith only [twoPole_log_le_eightieth hL]
  exact ⟨hx, hlow, ha.trans hlog, hb.trans hlog⟩

/-- At log level at least 1500, any root above 3log(q)/5+18 with controlled
endpoint logarithms has an explicit lower bound for the character-free separation.
Retain the affine root instead of choosing its additive constant. The principal,
pole and left-integral bounds give the common cost 11021/450, without GRH. -/
theorem twoPolePrimeTrivialSeparation_lower {q : ℕ} (hL : 1500 ≤ Real.log q) {r : ℝ}
    (hrange : (3 / 5 : ℝ) * Real.log q + 18 ≤ r)
    (hA : Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ Real.log q / 40)
    (hB : Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ Real.log q / 40) :
    (821 / 1000 : ℝ) * r - Real.log q / 2 - 11021 / 450 ≤
      twoPolePrimeTrivialSeparation q ∅ (r ^ 2) := by
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
    twoPole_error_algebra_general hL (show (3 / 5 : ℝ) * L ≤ s by linarith only [hroot]) hA hB
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
  have hQ := twoPole_log_max_le hL
  have hPole : ((7 / 6 : ℝ) * Real.log (max 20000 q : ℕ) + 4) / s ≤ 2 := by
    apply (div_le_iff₀ hspos).mpr
    nlinarith only [hQ, hroot, hL]
  have hpow : x ^ (-9 / 16 : ℝ) ≤ s⁻¹ := by
    have h :=
      Real.rpow_le_rpow_of_exponent_le hx (show (-9 / 16 : ℝ) ≤ -(1 / 2 : ℝ) by norm_num only)
    rw [Real.rpow_neg hxpos.le, ← Real.sqrt_eq_rpow] at h
    exact h
  have hC : 0 ≤ (3 / 2 : ℝ) * (L + 28) + 1 := by linarith only [hL]
  have hLeft : x ^ (-9 / 16 : ℝ) * ((3 / 2 : ℝ) * (L + 28) + 1) ≤ 5 / 2 := by
    calc
      _ ≤ s⁻¹ * ((3 / 2 : ℝ) * (L + 28) + 1) := mul_le_mul_of_nonneg_right hpow hC
      _ = ((3 / 2 : ℝ) * (L + 28) + 1) / s := by
        rw [div_eq_mul_inv]; ring
      _ ≤ 5 / 2 := (div_le_iff₀ hspos).mpr (by nlinarith only [hroot, hL])
  have hmass :
    (831 / 1000 : ℝ) * s ≤
      (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * s :=
    mul_le_mul_of_nonneg_right
      ((by norm_num only : (831 / 1000 : ℝ) ≤ 83125234337 / 100000000000).trans
        Analysis.gamma_ramp_mass_lower)
      hspos.le
  dsimp only [twoPolePrimeTrivialSeparation, twoPolePrimeTrivialUpper]
  simp only [Finset.sum_empty, mul_zero, sub_zero]
  nlinarith only [hE, hP, hPole, hLeft, hmass, hs, hL]

/-- For any natural level with log q at least 1500, the character-free separation
is positive at scale ((500/821)log q+30) squared and empty Euler support. Bound
paired error, principal, pole and sharp left-integral costs and use the ramp mass.
The remaining margin is positive on the whole half-line, without input certificates. -/
theorem twoPolePrimeTrivialSeparation_affine_pos {q : ℕ} (hL : 1500 ≤ Real.log q) :
    0 < twoPolePrimeTrivialSeparation q ∅ (((500 / 821 : ℝ) * Real.log q + 30) ^ 2) := by
  have hD := twoPole_affine_data hL
  have h := twoPolePrimeTrivialSeparation_lower hL hD.2.1 hD.2.2.1 hD.2.2.2
  linarith only [h]

/-- For L at least 1700 and additive shift between thirty and thirty-two,
the affine root gives scale at least one and controls both endpoint logarithms.
Use one rational root enclosure for every shift in this interval. This shares
analytic data between MR and odd non-one witnesses. -/
theorem twoPole_shifted_root_data {L c : ℝ} (hL : 1700 ≤ L) (hc : 30 ≤ c) (hc' : c ≤ 32) :
    let r := (500 / 821 : ℝ) * L + c;
    1 ≤ r ^ 2 ∧
      (3 / 5 : ℝ) * L + 18 ≤ r ∧
      Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ L / 40 ∧ Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ L / 40 := by
  let r := (500 / 821 : ℝ) * L + c
  have hr : 0 < r := by
    dsimp only [r]; linarith only [hL, hc]
  have hlow : (3 / 5 : ℝ) * L + 18 ≤ r := by
    dsimp only [r]; linarith only [hL, hc]
  have hhi : r ≤ (6291 / 10000 : ℝ) * L := by
    dsimp only [r]; linarith only [hL, hc']
  have hs := mul_self_le_mul_self hr.le hhi
  have hx : 1 ≤ r ^ 2 := by nlinarith only [hlow, hL, sq_nonneg (r - 1)]
  have ha :=
    Real.log_le_log (mul_pos (by norm_num only : (0 : ℝ) < 99 / 40) (zero_lt_one.trans_le hx))
      (show (99 / 40 : ℝ) * r ^ 2 ≤ L ^ 2 by nlinarith only [hs])
  have hb :=
    Real.log_le_log (mul_pos (by norm_num only : (0 : ℝ) < 101 / 40) (zero_lt_one.trans_le hx))
      (show (101 / 40 : ℝ) * r ^ 2 ≤ L ^ 2 by nlinarith only [hs])
  rw [Real.log_pow] at ha hb
  norm_num only [Nat.cast_ofNat] at ha hb
  have hlog : 2 * Real.log L ≤ L / 40 := by
    linarith only [twoPole_log_le_eightieth (by linarith only [hL] : 1500 ≤ L)]
  exact ⟨hx, hlow, ha.trans hlog, hb.trans hlog⟩

/-- At log level at least 1700, additive shift thirty-two leaves separation
strictly greater than one. Insert the common root data into the quantitative
separation bound. The spare unit absorbs the odd-witness prime-two cost. -/
theorem twoPolePrimeTrivialSeparation_shift32_gt_one {q : ℕ} (hL : 1700 ≤ Real.log q) :
    1 < twoPolePrimeTrivialSeparation q ∅ (((500 / 821 : ℝ) * Real.log q + 32) ^ 2) := by
  have hD := twoPole_shifted_root_data hL (c := 32) (by norm_num only) (by norm_num only)
  have h :=
    twoPolePrimeTrivialSeparation_lower (by linarith only [hL] : 1500 ≤ Real.log q) hD.2.1 hD.2.2.1
      hD.2.2.2
  linarith only [h]

end PseudoPrime.LLS
