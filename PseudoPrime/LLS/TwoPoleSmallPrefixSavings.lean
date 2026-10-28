/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleRetainedScaleBounds
public import PseudoPrime.LLS.PairedEulerExcludedBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TwoPoleSmallPrefixSavings

/-! # Rational small-prime Euler savings and the resulting affine gap -/

@[expose] public section

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
