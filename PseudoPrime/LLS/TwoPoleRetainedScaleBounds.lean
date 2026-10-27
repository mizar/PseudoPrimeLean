/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleConstantBounds

/-! # Scale-dependent polynomial numerators for the two-pole witness gap -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The retained numerator at logarithmic level L, Gamma cost C, root r and endpoint log cap K.
It keeps all rational paired, principal and pole costs and bounds the left-line term by 43/r.
Multiplying the gap by its root permits polynomial comparisons at finite scales. -/
noncomputable def twoPoleRetainedNumerator (L C r K : ℝ) : ℝ :=
  (831 / 1000 : ℝ) * r ^ 2 - (L / 2 + C) * r -
    2 *
      ((3 / 2 : ℝ) * (r / 20 * (63 / 40) + (1839 / 1000) * K + 21 / 20) +
        42 *
          (((11 / 200 : ℝ) * r ^ 2 + 101 * ((2 / 25 : ℝ) * r + (1839 / 1000) * K + 21 / 20)) /
            494)) -
    (r / 8 + (1839 / 1000 : ℝ) * (2 * K + 3) + 21 / 10) -
    ((7 / 6 : ℝ) * (L + 15) + 4) -
    43

/-- For a root at least one and a common endpoint log cap, the retained numerator bounds the
parameterized gap times the root. Bound the zero mass below and all error terms above without
replacing their scale dependence by constants. This is the common scalar input for finite-scale
witness bounds. -/
theorem twoPoleConstantGap_mul_root_lower {A : ℕ} {C r K : ℝ} (hr : 1 ≤ r)
    (hK : Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ K) :
    twoPoleRetainedNumerator (Real.log A) C r K ≤ twoPoleConstantGap A C (r ^ 2) * r := by
  have hr0 : 0 < r := by linarith only [hr]
  have hx : 1 ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 1)]
  have hx0 : 0 < r ^ 2 := zero_lt_one.trans_le hx
  have hs : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr0.le
  have hA :=
    (Real.log_le_log (mul_pos hx0 (by norm_num only : (0 : ℝ) < 99 / 40))
          (show r ^ 2 * (99 / 40 : ℝ) ≤ (101 / 40 : ℝ) * r ^ 2 by
            nlinarith only [sq_nonneg r])).trans
      hK
  have hX :=
    (Real.log_le_log hx0
          (show r ^ 2 ≤ (101 / 40 : ℝ) * r ^ 2 by nlinarith only [sq_nonneg r])).trans
      hK
  have hpow : (r ^ 2) ^ (-9 / 16 : ℝ) ≤ r⁻¹ := by
    have h :=
      Real.rpow_le_rpow_of_exponent_le hx (show (-9 / 16 : ℝ) ≤ -(1 / 2 : ℝ) by norm_num only)
    rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, hs] at h
    exact h
  have hleft : 43 * (r ^ 2) ^ (-9 / 16 : ℝ) * r ≤ 43 := by
    have h := mul_le_mul_of_nonneg_right hpow hr0.le
    rw [inv_mul_cancel₀ hr0.ne'] at h
    linarith only [h]
  have hm :=
    mul_le_mul_of_nonneg_right
      ((by norm_num only : (831 / 1000 : ℝ) ≤ 83125234337 / 100000000000).trans
        Analysis.gamma_ramp_mass_lower)
      (sq_nonneg r)
  have hQ := twoPole_log_max_le_unconditional A
  dsimp only [twoPoleRetainedNumerator, twoPoleConstantGap, signedTwoPoleGap, signedTwoPoleUpper,
    gammaRampPairedErrorNumerator, rampSmoothedIncrementError, rampExtendedSmoothedError]
  rw [hs]
  simp only [mul_assoc, sub_mul, add_mul, div_mul_cancel₀ _ hr0.ne']
  nlinarith only [hm, hleft, hA, hX, hK, hQ]

/-- For every positive real L, bound log L by L/500+21/4. A positive sixteen-term exponential
sum bounds log 500, and the logarithmic tangent gives the global estimate. This controls
endpoint logs without enumerating integer inputs. -/
theorem twoPoleRetained_log_tangent {L : ℝ} (hL : 0 < L) : Real.log L ≤ L / 500 + 21 / 4 := by
  have hn : Real.log (500 : ℝ) ≤ 25 / 4 := by
    apply (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 500)).mpr
    have h : (500 : ℝ) ≤ ∑ k ∈ Finset.range 16, (25 / 4 : ℝ) ^ k / (k.factorial : ℝ) := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    exact h.trans (Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 25 / 4) 16)
  have ht := Real.log_le_sub_one_of_pos (div_pos hL (by norm_num only : (0 : ℝ) < 500))
  rw [Real.log_div hL.ne' (by norm_num only : (500 : ℝ) ≠ 0)] at ht
  linarith only [ht, hn]

/-- For L at least 500 and additive constant between 12 and 13, the affine root gives scale at
least four and the stated endpoint log cap. Compare the squared root with 41L squared over 40
and apply the logarithmic tangent. These data feed the retained gap estimate. -/
theorem twoPoleRetained_root_data {L c : ℝ} (hL : 500 ≤ L) (hc : 12 ≤ c) (hc' : c ≤ 13) :
    let r := (500 / 821 : ℝ) * L + c;
    1 ≤ r ∧ 4 ≤ r ^ 2 ∧ Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ L / 250 + 211 / 20 := by
  let r := (500 / 821 : ℝ) * L + c
  have hr : 1 ≤ r := by
    dsimp only [r]; linarith only [hL, hc]
  have hu : r ≤ (159 / 250 : ℝ) * L := by
    dsimp only [r]; linarith only [hL, hc']
  have hs := mul_self_le_mul_self (by linarith only [hr] : 0 ≤ r) hu
  have hx : 4 ≤ r ^ 2 := by
    dsimp only [r]; nlinarith only [hL, hc, sq_nonneg L]
  have hp : 0 < L := by linarith only [hL]
  have ht := twoPoleRetained_log_tangent hp
  have hb :=
    Real.log_le_log (by nlinarith only [hx] : 0 < (101 / 40 : ℝ) * r ^ 2)
      (show (101 / 40 : ℝ) * r ^ 2 ≤ (41 / 40 : ℝ) * L ^ 2 by nlinarith only [hs])
  rw [Real.log_mul (by norm_num only : (41 / 40 : ℝ) ≠ 0) (pow_ne_zero 2 hp.ne'),
    Real.log_pow] at hb
  norm_num only [Nat.cast_ofNat] at hb
  have ht0 := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 41 / 40)
  exact ⟨hr, hx, by linarith only [hb, ht, ht0]⟩

/-- For L at least 500, additive constant at least 12 and the stated scalar Gamma cap, the
retained numerator is at least one tenth of its root. Rational polynomial positivity in L-500
and c-12 proves the claim. This separates the numerical margin from the analytic character
input. -/
theorem twoPoleRetainedNumerator_affine_margin {L c C : ℝ} (hL : 500 ≤ L) (hc : 12 ≤ c)
    (hC : C ≤ (821 / 1000 : ℝ) * c - 27 / 5) :
    let r := (500 / 821 : ℝ) * L + c;
    r / 10 ≤ twoPoleRetainedNumerator L C r (L / 250 + 211 / 20) := by
  have hr : 0 ≤ (500 / 821 : ℝ) * L + c := by linarith only [hL, hc]
  have hCr := mul_le_mul_of_nonneg_right hC hr
  dsimp only [twoPoleRetainedNumerator]
  nlinarith only [hCr, hL, hc, sq_nonneg (L - 500), sq_nonneg (c - 12),
    mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hc)]

/-- For logarithmic level at least 500 and additive constant between 12 and 13, the scalar Gamma
cap implies gap at least one tenth. Combine the retained numerator margin with the positive-root
comparison. This is the reusable finite-scale witness criterion. -/
theorem twoPoleRetainedGap_affine_margin {A : ℕ} {c C : ℝ} (hL : 500 ≤ Real.log A) (hc : 12 ≤ c)
    (hc' : c ≤ 13) (hC : C ≤ (821 / 1000 : ℝ) * c - 27 / 5) :
    (1 / 10 : ℝ) ≤ twoPoleConstantGap A C (((500 / 821 : ℝ) * Real.log A + c) ^ 2) := by
  have hd := twoPoleRetained_root_data hL hc hc'
  have hn := twoPoleRetainedNumerator_affine_margin hL hc hC
  have hg := twoPoleConstantGap_mul_root_lower (A := A) (C := C) hd.1 hd.2.2
  have hr : 0 < (500 / 821 : ℝ) * Real.log A + c := by linarith only [hL, hc]
  nlinarith only [hn, hg, hr]

/-- For an even quadratic nonprincipal character of even level under GRH, an ambient logarithmic
level at least 500 yields an odd non-one prime through the stated cutoff. Use the even Gamma
cap, retained gap and prime-two cost. This connects the finite-scale comparison to quadratic
witnesses. -/
theorem exists_odd_prime_ne_one_le_twoPoleRetained_even {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (heven : χ.Even) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log A + 61 / 5) ^ 2 ∧ χ p ≠ 1 := by
  let r := (500 / 821 : ℝ) * Real.log A + 61 / 5
  let x := r ^ 2
  have hd := twoPoleRetained_root_data hL (c := 61 / 5) (by norm_num only) (by norm_num only)
  have hx4 : 4 ≤ x := hd.2.1
  have hx : 2 ≤ x := by linarith only [hx4]
  have hxpos : 0 < x := by linarith only [hx]
  have hr : 0 < r := by
    dsimp only [r]; linarith only [hL]
  have hlocal : (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x ≤ 1 / 20 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hxpos)).mpr
    rw [Real.sqrt_sq hr.le]
    have hlog :=
      (Real.log_le_log (show 0 < (99 / 40 : ℝ) * x by nlinarith only [hxpos])
            (show (99 / 40 : ℝ) * x ≤ (101 / 40 : ℝ) * x by nlinarith only [hxpos])).trans
        hd.2.2
    have ht := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
    dsimp only [r]
    linarith only [hlog, ht, hL]
  have hc :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      χ.primitiveCharacter ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven)
  have hsep :=
    twoPoleRetainedGap_affine_margin hL (c := 61 / 5) (C := 112 / 25) (by norm_num only)
      (by norm_num only) (by norm_num only)
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hb := gamma_primitive_re_le_twoPoleConstant_ambient χ hne hqA hGRH hx hc
  apply
    exists_odd_prime_ne_one_of_gamma_ramp_gap χ hquad h2 hxpos
      (show 1 ≤ (99 / 40 : ℝ) * x by nlinarith only [hx])
  dsimp only [twoPoleConstantGap, signedTwoPoleGap] at hsep
  dsimp only [twoPoleConstantUpper] at hb
  nlinarith only [hP, hT, hb, hsep, hlocal]

/-- For a quadratic nonprincipal character under GRH, a retained numerator exceeding the
prime-factor exclusion cost yields a unit prime of value minus one. Assume root at least two,
a common endpoint log cap and a primitive Gamma cap. Multiply the gap comparison by its
positive root and apply the generic negative-witness extraction; the local cost is retained. -/
theorem exists_prime_neg_one_of_twoPoleRetainedNumerator {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r K C : ℝ} (hr : 2 ≤ r)
    (hK : Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ K)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hN :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * r ^ 2) <
        twoPoleRetainedNumerator (Real.log A) C r K) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * r ^ 2 ∧ χ p = -1 := by
  have hr0 : 0 < r := by linarith only [hr]
  have hx : 4 ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 2)]
  have hg := twoPoleConstantGap_mul_root_lower (A := A) (C := C) (by linarith only [hr] : 1 ≤ r) hK
  apply exists_prime_neg_one_of_twoPoleConstantGap χ hquad hne hqA hGRH hx hC
  rw [Real.sqrt_sq hr0.le]
  apply (div_lt_iff₀ hr0).mpr
  linarith only [hN, hg]

end PseudoPrime.LLS
