/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularTunedProfiles

/-! # Roots for a scale-dependent triangular profile

The explicit positive quadratic root and the eighth root used by the profile have exact
algebraic identities. These estimates avoid enumerating scale-dependent certificates.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The nonnegative eighth root of `(5313 / 10000) * L`, expressed as three square
roots. For nonnegative `L`, its eighth power is the argument. It supplies the
sixteenth-root floor of the scale-dependent triangular profile. -/
noncomputable def triangularEighthRoot (L : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (Real.sqrt ((5313 / 10000 : ℝ) * L)))

/-- For `L ≥ 0`, the triangular eighth root is nonnegative and its eighth power is
`(5313 / 10000) * L`. Apply the square-root identity three times. This is the
root certificate for the adaptive profile. -/
theorem triangularEighthRoot_pow {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ triangularEighthRoot L ∧ (triangularEighthRoot L) ^ 8 = (5313 / 10000 : ℝ) * L := by
  let x := (5313 / 10000 : ℝ) * L
  have hx : 0 ≤ x := mul_nonneg (by norm_num only) hL
  have h0 := Real.sq_sqrt hx
  have h1 := Real.sq_sqrt (Real.sqrt_nonneg x)
  have h2 := Real.sq_sqrt (Real.sqrt_nonneg (Real.sqrt x))
  constructor
  · exact Real.sqrt_nonneg _
  · change (Real.sqrt (Real.sqrt (Real.sqrt x))) ^ 8 = x
    rw [show
        (Real.sqrt (Real.sqrt (Real.sqrt x))) ^ 8 =
          (((Real.sqrt (Real.sqrt (Real.sqrt x))) ^ 2) ^ 2) ^ 2
        by ring,
      h2, h1, h0]

/-- For `L ≥ 3 * 10 ^ 10`, the triangular eighth root is at least 18.
Compare eighth powers using the exact root identity. This supplies a uniform denominator
bound for the initial adaptive profile budget. -/
theorem triangularEighthRoot_ge_18 {L : ℝ} (hL : 30000000000 ≤ L) :
    18 ≤ triangularEighthRoot L := by
  have h := triangularEighthRoot_pow (by linarith only [hL] : 0 ≤ L)
  apply
    (pow_le_pow_iff_left₀ (by norm_num only : (0 : ℝ) ≤ 18) h.1 (by norm_num only : (8 : ℕ) ≠ 0)).mp
  rw [h.2]
  norm_num only
  linarith only [hL]

/-- The nonnegative quadratic root `(A + sqrt (A ^ 2 + 4 * K * d)) / (2 * K)`.
For positive `K` and `A` and nonnegative `d), it is positive and solves
`K * r ^ 2 = A * r + d). This is the variable triangular radius coefficient. -/
noncomputable def triangularPositiveRoot (K A d : ℝ) : ℝ :=
  (A + Real.sqrt (A ^ 2 + 4 * K * d)) / (2 * K)

/-- If `K > 0`, `A > 0`, and `d ≥ 0`, the positive triangular root is positive and
solves its quadratic equation. Square the defining expression and cancel the nonzero
coefficient `K`. This provides the profile's exact margin identity. -/
theorem triangularPositiveRoot_spec {K A d : ℝ} (hK : 0 < K) (hA : 0 < A) (hd : 0 ≤ d) :
    0 < triangularPositiveRoot K A d ∧
      K * (triangularPositiveRoot K A d) ^ 2 = A * triangularPositiveRoot K A d + d := by
  let S := Real.sqrt (A ^ 2 + 4 * K * d)
  let r := (A + S) / (2 * K)
  have hdisc : 0 ≤ A ^ 2 + 4 * K * d := by
    have hm := mul_nonneg hK.le hd
    nlinarith only [sq_nonneg A, hm]
  have hs : 0 ≤ S := Real.sqrt_nonneg _
  have hs2 : S ^ 2 = A ^ 2 + 4 * K * d := Real.sq_sqrt hdisc
  have hr : 0 < r := div_pos (add_pos_of_pos_of_nonneg hA hs) (by linarith only [hK])
  have he : (2 * K) * r = A + S := by
    dsimp only [r]
    rw [mul_comm, div_mul_cancel₀ _ (by linarith only [hK] : 2 * K ≠ 0)]
  have hsub : S = 2 * K * r - A := by linarith only [he]
  rw [hsub] at hs2
  have hz : K * (K * r ^ 2 - A * r - d) = 0 := by nlinarith only [hs2]
  have hf : K * r ^ 2 - A * r - d = 0 := (mul_eq_zero.mp hz).resolve_left hK.ne'
  change 0 < r ∧ K * r ^ 2 = A * r + d
  exact ⟨hr, by linarith only [hf]⟩

/-- If `K > 0`, `d ≥ 0`, `K * r ^ 2 = A * r + d`, and `A + d ≤ K`,
then `r ≤ 1`. A hypothetical `r > 1` makes the difference between the quadratic
at `r` and at one positive, contradicting the equation. This supplies the profile's
upper-cutoff condition. -/
theorem triangular_root_le_one {K A d r : ℝ} (hK : 0 < K) (hd : 0 ≤ d) (heq : K * r ^ 2 = A * r + d)
    (hbudget : A + d ≤ K) : r ≤ 1 := by
  by_contra hh
  have hr1 : 1 < r := lt_of_not_ge hh
  have hgap : 0 < K * (r + 1) - A := by
    have hh' := mul_pos hK (show 0 < r - 1 by linarith only [hr1])
    nlinarith only [hh', hbudget, hd, hK]
  have hp := mul_pos (show 0 < r - 1 by linarith only [hr1]) hgap
  nlinarith only [hp, heq, hbudget]

/-- If `r > 0` solves `K * r ^ 2 = A * r + d` with `K > 0` and `d ≥ 0),
then every positive `a ≥ r` satisfies `A + d / a ≤ K * a`. Factor the difference
of the two quadratic values and divide by `a`. This is the profile's main margin
inequality. -/
theorem triangular_root_budget {K A d r a : ℝ} (hK : 0 < K) (hd : 0 ≤ d) (hr : 0 < r)
    (heq : K * r ^ 2 = A * r + d) (ha : r ≤ a) (ha0 : 0 < a) : A + d / a ≤ K * a := by
  have hmul : 0 ≤ (K * r - A) * r := by nlinarith only [heq, hd]
  have hkr : A ≤ K * r := by
    have h := nonneg_of_mul_nonneg_left hmul hr
    linarith only [h]
  have hKa := mul_nonneg hK.le (show 0 ≤ a by linarith only [ha0])
  have hprod : 0 ≤ (a - r) * (K * (a + r) - A) :=
    mul_nonneg (by linarith only [ha]) (by nlinarith only [hkr, hKa])
  have hpoly : A * a + d ≤ K * a ^ 2 := by nlinarith only [hprod, heq]
  have hdiv : d / a ≤ K * a - A := (div_le_iff₀ ha0).mpr (by nlinarith only [hpoly])
  linarith only [hdiv]

/-- Let `K > 0`, `d ≥ 0`, and `r > 0` solve `K * r ^ 2 = A * r + d`.
If `c > 0` satisfies `A * c + d ≤ K * c ^ 2`, then `r ≤ c). Factor the difference
of the quadratic values and use positivity of the second factor. This compares the
adaptive radius with explicit rational coefficients. -/
theorem triangular_root_le_of_budget {K A d r c : ℝ} (hK : 0 < K) (hd : 0 ≤ d) (hr : 0 < r)
    (hc : 0 < c) (heq : K * r ^ 2 = A * r + d) (hbound : A * c + d ≤ K * c ^ 2) : r ≤ c := by
  have hm : 0 ≤ (K * r - A) * r := by nlinarith only [heq, hd]
  have hkr : A ≤ K * r := by
    have hh := nonneg_of_mul_nonneg_left hm hr
    linarith only [hh]
  by_contra h
  have hrc : c < r := lt_of_not_ge h
  have hKc := mul_pos hK hc
  have hfactor : 0 < K * (r + c) - A := by nlinarith only [hkr, hKc]
  have hp := mul_pos (show 0 < r - c by linarith only [hrc]) hfactor
  nlinarith only [hp, heq, hbound]

end PseudoPrime.PrimeTestBounds.MillerRabin
