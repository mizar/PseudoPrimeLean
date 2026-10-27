/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.JointRampPrincipalWitnessBounds

/-! # A smaller affine witness root from the joint principal bound -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For L at least 500, the affine root with additive constant 213/20 is at least two and its
endpoint logarithm satisfies the retained cap. Compare with the previous root of constant
eleven. These data supply the scale and endpoint inputs for the signed principal comparison. -/
theorem twoPolePrincipalPrefix_root_data {L : ℝ} (hL : 500 ≤ L) :
    let r := (500 / 821 : ℝ) * L + 213 / 20;
    2 ≤ r ∧ 4 ≤ r ^ 2 ∧ Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ L / 250 + 211 / 20 := by
  let r := (500 / 821 : ℝ) * L + 213 / 20
  have hr : 2 ≤ r := by
    dsimp only [r]; linarith only [hL]
  have hx : 4 ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 2)]
  have hd := twoPolePrefix_root_data hL
  have hs :=
    mul_self_le_mul_self (by linarith only [hr] : 0 ≤ r)
      (show r ≤ (500 / 821 : ℝ) * L + 11 by
        dsimp only [r]; linarith only)
  have ht :=
    Real.log_le_log (by nlinarith only [hx] : 0 < (101 / 40 : ℝ) * r ^ 2)
      (show (101 / 40 : ℝ) * r ^ 2 ≤ (101 / 40 : ℝ) * ((500 / 821 : ℝ) * L + 11) ^ 2 by
        nlinarith only [hs])
  exact ⟨hr, hx, ht.trans hd.2.2⟩

/-- For L at least 500 and effective Gamma cost at most 363/100, the retained numerator plus
one fifth of the root is at least one hundredth of the root. Use rational polynomial
positivity at L-500. The extra term records the certified joint principal saving. -/
theorem twoPolePrincipalPrefix_numerator_margin {L C : ℝ} (hL : 500 ≤ L) (hC : C ≤ 363 / 100) :
    let r := (500 / 821 : ℝ) * L + 213 / 20;
    r / 100 ≤ twoPoleRetainedNumerator L C r (L / 250 + 211 / 20) + (1 / 5 : ℝ) * r := by
  have hr : 0 ≤ (500 / 821 : ℝ) * L + 213 / 20 := by linarith only [hL]
  have hCr := mul_le_mul_of_nonneg_right hC hr
  dsimp only [twoPoleRetainedNumerator]
  nlinarith only [hL, hCr, sq_nonneg (L - 500)]

/-- For ambient logarithm at least 500 and the displayed effective cost, the old gap plus
one fifth is at least one hundredth. Combine the retained numerator margin with its
positive-root comparison. This leaves the logarithmic principal saving available for prime two. -/
theorem twoPolePrincipalPrefix_base_gap_margin {A : ℕ} {C : ℝ} (hL : 500 ≤ Real.log A)
    (hC : C ≤ 363 / 100) :
    (1 / 100 : ℝ) ≤
      twoPoleConstantGap A C (((500 / 821 : ℝ) * Real.log A + 213 / 20) ^ 2) + 1 / 5 := by
  have hd := twoPolePrincipalPrefix_root_data hL
  have hn := twoPolePrincipalPrefix_numerator_margin hL hC
  have hg :=
    twoPoleConstantGap_mul_root_lower (A := A) (C := C)
      (by linarith only [hd.1] : 1 ≤ (500 / 821 : ℝ) * Real.log A + 213 / 20) hd.2.2
  have hr : 0 < (500 / 821 : ℝ) * Real.log A + 213 / 20 := by linarith only [hL]
  nlinarith only [hn, hg, hr]

/-- At every scale at least one, the logarithmic tail of the principal saving exceeds the
prime-two allowance. Expand the cutoff logarithm and use its tangent bound and the certified
logarithm of two. This pays for odd-prime extraction and retains the constant principal saving. -/
theorem principalSaving_tail_gt_prime_two_allowance {x : ℝ} (hx : 1 ≤ x) :
    (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
      ((1839 / 800 : ℝ) * Real.log x + 18123 / 4000) / Real.sqrt x := by
  apply (div_lt_div_iff_of_pos_right (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx))).mpr
  rw [Real.log_mul (by norm_num only : (99 / 40 : ℝ) ≠ 0) (zero_lt_one.trans_le hx).ne']
  have ht := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 99 / 40)
  linarith only [ht, Real.log_two_lt_d9, Real.log_nonneg hx]

/-- For ambient logarithm at least 500 and effective cost at most 363/100, the signed
principal gap is positive at the root of constant 213/20. Add the positive logarithmic saving to
the certified base-gap margin. This supplies the MR separation criterion. -/
theorem twoPolePrincipalPrefix_gap_positive {A : ℕ} {C : ℝ} (hL : 500 ≤ Real.log A)
    (hC : C ≤ 363 / 100) :
    0 < jointRampPrincipalGap A C (((500 / 821 : ℝ) * Real.log A + 213 / 20) ^ 2) := by
  have hd := twoPolePrincipalPrefix_root_data hL
  have hm := twoPolePrincipalPrefix_base_gap_margin hL hC
  have hg0 :=
    twoPoleSignedVariationGap_gt_constant (A := A) (C := C)
      (show 1 ≤ ((500 / 821 : ℝ) * Real.log A + 213 / 20) ^ 2 by linarith only [hd.2.1])
  have hg :=
    jointRampPrincipalGap_gt_signed (A := A) (C := C)
      (show 1 ≤ ((500 / 821 : ℝ) * Real.log A + 213 / 20) ^ 2 by linarith only [hd.2.1])
  linarith only [hm, hg0, hg]

/-- Under the same ambient and Gamma-cost assumptions, the joint principal gap exceeds the
prime-two allowance. Pay that allowance from the logarithmic principal saving and retain the
positive base margin. This is the odd non-one separation criterion. -/
theorem twoPolePrincipalPrefix_gap_gt_odd_allowance {A : ℕ} {C : ℝ} (hL : 500 ≤ Real.log A)
    (hC : C ≤ 363 / 100) :
    let x := ((500 / 821 : ℝ) * Real.log A + 213 / 20) ^ 2;
    (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x < jointRampPrincipalGap A C x := by
  have hd := twoPolePrincipalPrefix_root_data hL
  have hx : 1 ≤ ((500 / 821 : ℝ) * Real.log A + 213 / 20) ^ 2 := by linarith only [hd.2.1]
  have hm := twoPolePrincipalPrefix_base_gap_margin hL hC
  have ht := principalSaving_tail_gt_prime_two_allowance hx
  dsimp only
  have hj := jointRampPrincipalGap_gt_signed (A := A) (C := C) hx
  rw [twoPoleSignedVariationGap_eq_saved (zero_lt_one.trans_le hx)] at hj
  linarith only [hm, ht, hj]

/-- Under GRH, an even nonprincipal quadratic character of even level at most A, with log A
at least 500, has an odd non-one prime below the affine two-pole cutoff of constant 213/20.
Retain the Euler saving 7/8 on three and five and use the joint principal bound. This is the
character theorem used by the improved pointwise and finite-maximum Jacobi bounds. -/
theorem exists_odd_prime_ne_one_le_twoPolePrincipalPrefix_even {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (heven : χ.Even) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log A + 213 / 20) ^ 2 ∧ χ p ≠ 1 := by
  let x := ((500 / 821 : ℝ) * Real.log A + 213 / 20) ^ 2
  have hd := twoPolePrincipalPrefix_root_data hL
  have hx4 : 4 ≤ x := hd.2.1
  have hc :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      χ.primitiveCharacter ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven)
  have hm :=
    twoPolePrincipalPrefix_gap_gt_odd_allowance hL (C := 112 / 25 - 7 / 8) (by norm_num only)
  apply
    exists_odd_prime_ne_one_of_jointRampPrincipal_prefix χ hquad hne h2 hqA hGRH
      (by linarith only [hx4] : 2 ≤ x) hc ({3,5} : Finset ℕ)
  · intro n hn
    have hs : ∀ m ∈ ({3,5} : Finset ℕ), m ≤ 5 := by decide
    exact (Nat.cast_le.mpr (hs n hn)).trans (by linarith only [hx4])
  · exact (by decide : ∀ n ∈ ({3,5} : Finset ℕ), Odd n)
  · exact AnalyticNumberTheory.Arithmetic.pairedEuler_prefix_35_saving
  · exact hm

end PseudoPrime.LLS
