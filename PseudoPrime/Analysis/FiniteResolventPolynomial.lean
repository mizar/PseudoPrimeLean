/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SignedResolventEulerBounds

/-! # Recursive polynomial certificates for signed finite resolvents -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a rational node-coefficient list and a real square variable z.
Output: the product of all node denominators a^2+z, with empty product one.
Role: clear finite resolvent denominators without expanding nested fractions. -/
noncomputable def finiteResolventDenominator : List (ℚ × ℚ) → ℝ → ℝ
  | [], _ => 1
  | ab :: l, z => ((ab.1 : ℝ) ^ 2 + z) * finiteResolventDenominator l z

/-- Input: a rational node-coefficient list and a real square variable z.
Output: the numerator obtained recursively by adjoining c*a times the remaining denominator.
Role: reduce signed rational comparisons to polynomial identities. -/
noncomputable def finiteResolventNumerator : List (ℚ × ℚ) → ℝ → ℝ
  | [], _ => 0
  | ab :: l, z =>
    (ab.2 : ℝ) * (ab.1 : ℝ) * finiteResolventDenominator l z +
      ((ab.1 : ℝ) ^ 2 + z) * finiteResolventNumerator l z

/-- Input: real scalars and a nonzero denominator.
Claim: clearing one additional resolvent denominator preserves the numerator recursion.
Proof: use division cancellation and a ring identity.
Role: keep the finite-list proof independent of a global fraction-normalization tactic. -/
theorem resolvent_denominator_step (a c d s r : ℝ) (hd : d ≠ 0) :
    (d * s) * (c * (a / d) + r) = c * a * s + d * (s * r) := by
  have hc := div_mul_cancel₀ a hd
  calc
    _ = c * s * ((a / d) * d) + d * (s * r) := by ring
    _ = _ := by
      rw [hc]; ring

/-- Input: a rational node list and a real ordinate whose node denominators are nonzero.
Claim: denominator times the signed resolvent equals its recursive numerator.
Proof: induct on the list and clear one denominator at each step.
Role: verify polynomial certificates using ordinary ring arithmetic. -/
theorem finiteResolvent_denominator_mul_eq (l : List (ℚ × ℚ)) (t : ℝ)
    (hn : ∀ ab ∈ l, (ab.1 : ℝ) ^ 2 + t ^ 2 ≠ 0) :
    finiteResolventDenominator l (t ^ 2) * finiteSignedResolvent l t =
      finiteResolventNumerator l (t ^ 2) := by
  induction l with
  | nil =>
    simp only [finiteResolventDenominator, finiteSignedResolvent, finiteResolventNumerator,
      List.map_nil, List.sum_nil, mul_zero]
  | cons ab l ih =>
    have hd := hn ab List.mem_cons_self
    have hi := ih (fun cd hcd ↦ hn cd (List.mem_cons_of_mem ab hcd))
    change
      (((ab.1 : ℝ) ^ 2 + t ^ 2) * finiteResolventDenominator l (t ^ 2)) *
          ((ab.2 : ℝ) * ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + t ^ 2)) + finiteSignedResolvent l t) =
        (ab.2 : ℝ) * (ab.1 : ℝ) * finiteResolventDenominator l (t ^ 2) +
          ((ab.1 : ℝ) ^ 2 + t ^ 2) * finiteResolventNumerator l (t ^ 2)
    rw [resolvent_denominator_step _ _ _ _ _ hd, hi]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: a rational node list and a strictly positive square variable.
Claim: its denominator product is positive. Proof: every square plus the variable is positive.
Role: preserve inequalities when clearing the rational tail. -/
theorem finiteResolvent_denominator_pos (l : List (ℚ × ℚ)) {z : ℝ} (hz : 0 < z) :
    0 < finiteResolventDenominator l z := by
  induction l with
  | nil => norm_num only [finiteResolventDenominator]
  | cons ab l ih => exact mul_pos (add_pos_of_nonneg_of_pos (sq_nonneg (ab.1 : ℝ)) hz) ih

/-- Input: nonzero ordinate and a positive cleared polynomial difference.
Claim: the scaled signed resolvent exceeds the proposed constant.
Proof: combine the exact numerator identity with denominator positivity.
Role: transfer shifted polynomial certificates to entire unbounded frequency tails. -/
theorem finiteResolvent_scaled_gt (l : List (ℚ × ℚ)) {t c : ℝ} (ht : 0 < t ^ 2)
    (hpoly :
      0 <
        (1 + t ^ 2) * finiteResolventNumerator l (t ^ 2) -
          c * finiteResolventDenominator l (t ^ 2)) :
    c < (1 + t ^ 2) * finiteSignedResolvent l t := by
  have hd := finiteResolvent_denominator_pos l ht
  have he :=
    finiteResolvent_denominator_mul_eq l t
      (fun ab _ ↦ ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg (ab.1 : ℝ)) ht))
  have hid :
    finiteResolventDenominator l (t ^ 2) * ((1 + t ^ 2) * finiteSignedResolvent l t - c) =
      (1 + t ^ 2) * finiteResolventNumerator l (t ^ 2) -
        c * finiteResolventDenominator l (t ^ 2) := by
    calc
      _ =
          (1 + t ^ 2) * (finiteResolventDenominator l (t ^ 2) * finiteSignedResolvent l t) -
            c * finiteResolventDenominator l (t ^ 2) :=
        by ring
      _ = _ := by rw [he]
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hd).mp (hid.symm ▸ hpoly))

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: a nonzero ordinate and a positive cleared weighted resolvent difference.
Claim: the weighted resolvent exceeds the proposed scalar bound.
Proof: use denominator positivity and the recursive numerator identity.
Role: support arbitrary polynomial or exponential weights in rational certificates. -/
theorem finiteResolvent_weighted_gt (l : List (ℚ × ℚ)) {t a c : ℝ} (ht : 0 < t ^ 2)
    (hp : 0 < a * finiteResolventNumerator l (t ^ 2) - c * finiteResolventDenominator l (t ^ 2)) :
    c < a * finiteSignedResolvent l t := by
  have hd := finiteResolvent_denominator_pos l ht
  have he :=
    finiteResolvent_denominator_mul_eq l t
      (fun ab _ ↦ ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg (ab.1 : ℝ)) ht))
  have hid :
    finiteResolventDenominator l (t ^ 2) * (a * finiteSignedResolvent l t - c) =
      a * finiteResolventNumerator l (t ^ 2) - c * finiteResolventDenominator l (t ^ 2) := by
    calc
      _ =
          a * (finiteResolventDenominator l (t ^ 2) * finiteSignedResolvent l t) -
            c * finiteResolventDenominator l (t ^ 2) :=
        by ring
      _ = _ := by rw [he]
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hd).mp (hid.symm ▸ hp))

end PseudoPrime.Analysis
