/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPhaseTaylor
public import PseudoPrime.Analysis.Phase64MomentInterpolation

/-! # Executable rational Gamma phase endpoint bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a rational component pair. Output: its totalized complex inverse in rational form.
Role: compute the corrected Gamma multiplier without transcendental operations. -/
def rationalComplexInv (z : ℚ × ℚ) : ℚ × ℚ :=
  (z.1 / (z.1 ^ 2 + z.2 ^ 2), -z.2 / (z.1 ^ 2 + z.2 ^ 2))

/-- Input: a rational pair. Claim: the rational inverse casts to the complex inverse.
Proof: compare components using the complex norm square formula.
Role: validate executable rational division, including zero. -/
theorem rationalComplexCast_inv (z : ℚ × ℚ) :
    rationalComplexCast (rationalComplexInv z) = (rationalComplexCast z)⁻¹ := by
  apply Complex.ext
  · simp only [rationalComplexInv, rationalComplexCast, Complex.inv_re, Complex.normSq_apply,
      Rat.cast_div, Rat.cast_add, pow_two, Rat.cast_mul]
  · simp only [rationalComplexInv, rationalComplexCast, Complex.inv_im, Complex.normSq_apply,
      Rat.cast_div, Rat.cast_neg, Rat.cast_add, pow_two, Rat.cast_mul]

/-- Input: grid denominator G and rational ordinate t.
Output: the rational pair representing the corrected order-256 rounded Gamma coefficient.
Definition: combine 16/s, the rational correction and the rounded Euler product.
Role: compute the analytic coefficient used in endpoint certification. -/
def rationalGamma256Coefficient (G : ℕ) (t : ℚ) : ℚ × ℚ :=
  let s : ℚ × ℚ := (1 / 2, t)
  rationalComplexMul
    (rationalComplexMul (rationalComplexScale 16 (rationalComplexInv s))
      (rationalComplexAdd (1, 0)
        (rationalComplexScale 128
          (rationalComplexMul (rationalComplexMul s (rationalComplexAdd s (1, 0)))
            (rationalComplexInv
              (rationalComplexMul (rationalComplexAdd (257, 0) s)
                (rationalComplexAdd (258, 0) s)))))))
    (roundedEulerUnitProduct G t 256)

/-- Input: grid denominator and rational ordinate.
Claim: the executable coefficient casts to roundedGamma256Coefficient.
Proof: commute component operations with casting and normalize the rational multiplier.
Role: transfer finite rational computations to the established Gamma approximation. -/
theorem rationalGamma256Coefficient_cast (G : ℕ) (t : ℚ) :
    rationalComplexCast (rationalGamma256Coefficient G t) = roundedGamma256Coefficient G t := by
  have hs : rationalComplexCast (1 / 2, t) = (1 / 2 : ℂ) + Complex.I * (t : ℂ) := by
    apply Complex.ext
    · norm_num only [rationalComplexCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
        Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ratCast_re, Complex.ratCast_im, zero_mul, mul_zero, sub_zero,
        add_zero]
    · norm_num only [rationalComplexCast, Complex.add_im, Complex.div_ofNat_im, Complex.one_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ratCast_re, Complex.ratCast_im,
        zero_mul, one_mul, zero_add, zero_div]
  have hc (n : ℚ) : rationalComplexCast (n, 0) = (n : ℂ) := by
    apply Complex.ext
    · rfl
    · exact Rat.cast_zero
  dsimp only [rationalGamma256Coefficient]
  simp only [rationalComplexCast_mul, rationalComplexCast_scale, rationalComplexCast_add,
    rationalComplexCast_inv, hs, hc]
  dsimp only [roundedGamma256Coefficient]
  norm_num only [Rat.cast_ofNat]
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num only
  ring

/-- Input: rational node-coefficient list and ordinate. Output: sum of c*a/(a^2+t^2).
Role: compute signed resolvent values in exact rational arithmetic. -/
def rationalSignedResolvent (l : List (ℚ × ℚ)) (t : ℚ) : ℚ :=
  (l.map (fun ab ↦ ab.2 * (ab.1 / (ab.1 ^ 2 + t ^ 2)))).sum

/-- Input: rational nodes and ordinate. Claim: casting gives the analytic signed resolvent.
Proof: induct over the list and commute rational arithmetic with casts.
Role: include the comparison function in exact endpoint checks. -/
theorem rationalSignedResolvent_cast (l : List (ℚ × ℚ)) (t : ℚ) :
    (rationalSignedResolvent l t : ℝ) = finiteSignedResolvent l (t : ℝ) := by
  induction l with
  | nil =>
    simp only [rationalSignedResolvent, finiteSignedResolvent, List.map_nil, List.sum_nil,
      Rat.cast_zero]
  | cons ab l
    ih =>
    simp only [rationalSignedResolvent, finiteSignedResolvent, List.map_cons, List.sum_cons,
      Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow] at ih ⊢
    rw [ih]

/-- Input: a rational pair. Claim: its complex norm is at most the sum of component magnitudes.
Proof: use the complex component bound. Role: supply a rational multiplier error budget. -/
theorem norm_rationalComplexCast_le (z : ℚ × ℚ) :
    ‖rationalComplexCast z‖ ≤ (|z.1| + |z.2| : ℚ) := by
  simpa only [rationalComplexCast, Rat.cast_add, Rat.cast_abs] using
    (Complex.norm_le_abs_re_add_abs_im (rationalComplexCast z))

/-- Input: a grid, Taylor length, ordinate, phase center and phase uncertainty.
Output: a rational lower bound candidate for the rounded resolvent-Gamma gap.
Definition: subtract the coefficient norm cap times the complete Taylor and phase errors.
Role: make spectral endpoint inequalities executable. -/
def rationalPhase64NodeLower (G n : ℕ) (t v ε : ℚ) : ℚ :=
  let C := rationalGamma256Coefficient G t
  rationalSignedResolvent phaseResolvent64Coefficients t +
      (rationalComplexMul C (rationalPhaseTaylor v n)).1 -
    (|C.1| + |C.2|) * (ε + |v| ^ n / (n.factorial : ℚ) * 2)

/-- Input: a valid Taylor length and a certified enclosure of the actual phase.
Claim: the rational endpoint candidate is below the actual rounded phase gap.
Proof: identify rational coefficients and use the weighted Taylor error theorem.
Role: remove analytic Gamma and exponential evaluation from finite node checks. -/
theorem rationalPhase64NodeLower_le {x : ℝ} (G n : ℕ) (t v ε : ℚ)
    (hv : |(v : ℝ)| / (n + 1 : ℕ) ≤ 1 / 2)
    (hphase : |(t : ℝ) * Real.log (256 * x) - (v : ℝ)| ≤ (ε : ℝ)) :
    (rationalPhase64NodeLower G n t v ε : ℝ) ≤ roundedPhase64Gap G x t := by
  have h :=
    phase_product_re_lower_of_taylor v n
      (norm_rationalComplexCast_le (rationalGamma256Coefficient G t)) hv hphase
  have hp :=
    congrArg Complex.re
      (rationalComplexCast_mul (rationalGamma256Coefficient G t) (rationalPhaseTaylor v n))
  change
    ((rationalComplexMul (rationalGamma256Coefficient G t) (rationalPhaseTaylor v n)).1 : ℝ) =
      (rationalComplexCast (rationalGamma256Coefficient G t) *
          rationalComplexCast (rationalPhaseTaylor v n)).re at hp
  simp only [Rat.cast_add, Rat.cast_abs] at h
  rw [rationalGamma256Coefficient_cast] at h hp
  dsimp only [rationalPhase64NodeLower]
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_abs, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat]
  rw [rationalSignedResolvent_cast]
  dsimp only [roundedPhase64Gap]
  rw [hp]
  linarith only [h]

/-- Input: a positive scale and grid, a node in [-5,5], a phase enclosure,
and a rational lower bound containing the Gamma approximation allowance.
Claim: the actual resolvent-Gamma gap exceeds the specified margin.
Proof: compose the rational phase bound with the existing Gamma error theorem.
Role: connect a finite arithmetic certificate to actual Gamma endpoints. -/
theorem phase64_actual_gap_ge_of_rational_node {x : ℝ} (hx : 0 < x) {G : ℕ} (hG : 0 < G) (n : ℕ)
    (t v ε : ℚ) (ht : |(t : ℝ)| ≤ 5) (hv : |(v : ℝ)| / (n + 1 : ℕ) ≤ 1 / 2)
    (hphase : |(t : ℝ) * Real.log (256 * x) - (v : ℝ)| ≤ (ε : ℝ)) {c : ℝ}
    (hc : c + ((1 / 25000 : ℝ) + 32768 / (G : ℝ)) ≤ (rationalPhase64NodeLower G n t v ε : ℝ)) :
    c ≤
      finiteSignedResolvent phaseResolvent64Coefficients (t : ℝ) +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) *
            (x : ℂ) ^ (Complex.I * (t : ℂ))).re := by
  exact
    phase64_actual_gap_ge_of_rounded_node hx hG t ht
      (hc.trans (rationalPhase64NodeLower_le G n t v ε hv hphase))

/-- Input: a real y between l and u and any signed ordinate t.
Claim: the midpoint phase error is at most |t|*(u-l)/2.
Proof: factor t and bound the midpoint distance using both endpoints.
Role: reuse a single logarithmic interval at every spectral node. -/
theorem phase_center_error_of_log_enclosure {y l u : ℝ} (hl : l ≤ y) (hu : y ≤ u) (t : ℝ) :
    |t * y - t * ((l + u) / 2)| ≤ |t| * ((u - l) / 2) := by
  have he : t * y - t * ((l + u) / 2) = t * (y - (l + u) / 2) := by ring
  have ha : |y - (l + u) / 2| ≤ (u - l) / 2 :=
    abs_le.mpr ⟨by linarith only [hl, hu], by linarith only [hl, hu]⟩
  rw [he, abs_mul]
  exact mul_le_mul_of_nonneg_left ha (abs_nonneg t)

end PseudoPrime.Analysis
