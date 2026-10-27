/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RealLog
public import PseudoPrime.LLS.OddEndpointTwoCostWitness
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Fixed-cost reciprocal cutoff monotonicity for endpoint comparisons -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For t>=8, the logarithmic term in the mass-cap derivative is positive.
The tangent at eight and the existing log-two upper bound suffice. This supplies
the sign independently of conductor and exclusion costs. -/
theorem endpointCutoff_log_gap_pos {t : ℝ} (ht : 8 ≤ t) : 0 < t - 1 - 2 * Real.log t := by
  have hp : 0 < t := by linarith only [ht]
  have hlog := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 8) hp
  have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  rw [he] at hlog
  linarith only [hlog, ht, Real.log_two_lt_d9]

/-- The reciprocal endpoint mass cap in the variable t=sqrt Y.
Here a is half the conductor logarithm minus log pi, and r is the constant
reciprocal loss including the exclusion cost. Used to compare arbitrary cutoffs. -/
noncomputable def endpointCutoffMass (a r t : ℝ) : ℝ :=
  (a * (t ^ 2 - 1) + r * t ^ 2 - 2 * t ^ 2 * Real.log t) / (t - 1) ^ 2

/-- For t>1, the mass-cap derivative has an explicit signed numerator.
Differentiate the quotient and clear nonzero factors. This identity supplies
both continuity and the derivative sign for cutoff monotonicity. -/
theorem hasDerivAt_endpointCutoffMass (a r t : ℝ) (ht : 1 < t) :
    HasDerivAt (endpointCutoffMass a r)
      (-2 * (a * (t - 1) + r * t + t * (t - 1 - 2 * Real.log t)) / (t - 1) ^ 3) t := by
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have ht1 : t - 1 ≠ 0 := (sub_pos.mpr ht).ne'
  have hi := hasDerivAt_id t
  have hn := (((hi.pow 2).sub_const 1).const_mul a).add ((hi.pow 2).const_mul r)
  have hl := ((hi.pow 2).const_mul 2).mul (Real.hasDerivAt_log ht0)
  have hd := (hn.sub hl).div ((hi.sub_const 1).pow 2) (pow_ne_zero 2 ht1)
  apply hd.congr_deriv
  dsimp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  norm_num only [Nat.cast_ofNat, pow_one, Nat.add_one_sub_one]
  field_simp (disch :=
    first
    | exact ht0
    | exact ht1
    | norm_num only)
  ring

/-- For nonnegative conductor and cost parameters, the mass cap decreases
on t>=8. Apply the mean value inequality to the explicit derivative. This rules
out an improvement from shortening the reciprocal cutoff while keeping costs fixed. -/
theorem endpointCutoffMass_antitone (a r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) :
    AntitoneOn (endpointCutoffMass a r) (Set.Ici 8) := by
  apply
    antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t ↦
      -2 * (a * (t - 1) + r * t + t * (t - 1 - 2 * Real.log t)) / (t - 1) ^ 3) (convex_Ici 8)
  · intro t ht
    have h8 : 8 ≤ t := ht
    exact
      (hasDerivAt_endpointCutoffMass a r t (by linarith only [h8])).continuousAt.continuousWithinAt
  · intro t ht
    have h8 : 8 ≤ t := interior_subset ht
    exact (hasDerivAt_endpointCutoffMass a r t (by linarith only [h8])).hasDerivWithinAt
  · intro t ht
    have h8 : 8 ≤ t := interior_subset ht
    have hp : 0 < t := by linarith only [h8]
    have h1 : 0 < t - 1 := by linarith only [h8]
    have hs :=
      add_nonneg (add_nonneg (mul_nonneg ha h1.le) (mul_nonneg hr hp.le))
        (mul_nonneg hp.le (endpointCutoff_log_gap_pos h8).le)
    exact
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num only) hs)
        (pow_nonneg h1.le 3)

/-- For t>1, the reciprocal cap including cost c equals the normalized mass.
Rewrite the square root and logarithm and clear nonzero denominators. This
connects the scalar monotonicity to the actual endpoint comparison. -/
theorem reciprocalMassCap_add_cost_eq_endpointCutoffMass (q : ℕ) {t : ℝ} (ht : 1 < t) (c : ℝ) :
    reciprocalGapReciprocalMassCap q (t ^ 2) (Real.log (t ^ 2) - 31551 / 20000) +
        c / (1 - 1 / Real.sqrt (t ^ 2)) ^ 2 =
      endpointCutoffMass ((Real.log q - Real.log Real.pi) / 2) (26551 / 20000 + c) t := by
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have ht1 : t - 1 ≠ 0 := (sub_pos.mpr ht).ne'
  dsimp only [reciprocalGapReciprocalMassCap, endpointCutoffMass]
  rw [Real.sqrt_sq (zero_lt_one.trans ht).le, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  field_simp (disch :=
    first
    | exact ht0
    | exact ht1
    | norm_num only)
  ring

/-- For t>1, the endpoint limit separates into a positive coefficient times
the cutoff mass and a term independent of t. Expand the existing definitions
and use the mass identity. This prepares comparison at two reciprocal cutoffs. -/
theorem oddEndpointTwoCostLimit_eq_cutoffMass (q : ℕ) (x c D : ℝ) {t : ℝ} (ht : 1 < t) :
    oddEndpointTwoCostLimit q x (t ^ 2) c D =
      (2 + (Real.log x + 2) / Real.sqrt x) *
              endpointCutoffMass ((Real.log q - Real.log Real.pi) / 2) (26551 / 20000 + c) t +
            Real.log x * Real.log q / (2 * Real.sqrt x) +
            (9 / 2 - 3 / 4 * Real.log x) / Real.sqrt x -
          (x - Real.sqrt x / 20 - 1839 / 1000 * Real.log x - 21 / 20) / Real.sqrt x +
        D / Real.sqrt x := by
  have he := reciprocalMassCap_add_cost_eq_endpointCutoffMass q ht c
  dsimp only [oddEndpointTwoCostLimit, oddEndpointCostLimit, reciprocalGapFullEndpointLimit]
  rw [Real.sqrt_inv]
  linear_combination (2 + (Real.log x + 2) / Real.sqrt x) * he

/-- For x>=1, conductor log at least log pi and nonnegative reciprocal cost,
the endpoint limit decreases as Y increases on Y>=64. Apply mass monotonicity
at square roots and retain the independent logarithmic cost D. This covers the
fixed-cost negative and non-one witness comparisons. -/
theorem oddEndpointTwoCostLimit_antitone_cutoff (q : ℕ) {x Y Z c D : ℝ}
    (hq : Real.log Real.pi ≤ Real.log q) (hx : 1 ≤ x) (hc : 0 ≤ c) (hY : 64 ≤ Y) (hYZ : Y ≤ Z) :
    oddEndpointTwoCostLimit q x Z c D ≤ oddEndpointTwoCostLimit q x Y c D := by
  have hY0 : 0 ≤ Y := by linarith only [hY]
  have hZ0 : 0 ≤ Z := le_trans hY0 hYZ
  have hsY : 8 ≤ Real.sqrt Y := (Real.le_sqrt (by norm_num only) hY0).mpr (by linarith only [hY])
  have hsZ : 8 ≤ Real.sqrt Z := hsY.trans (Real.sqrt_le_sqrt hYZ)
  have hm :=
    endpointCutoffMass_antitone ((Real.log q - Real.log Real.pi) / 2) (26551 / 20000 + c)
      (div_nonneg (sub_nonneg.mpr hq) (by norm_num only)) (by linarith only [hc]) hsY hsZ
      (Real.sqrt_le_sqrt hYZ)
  have heY :=
    oddEndpointTwoCostLimit_eq_cutoffMass q x c D (by linarith only [hsY] : 1 < Real.sqrt Y)
  have heZ :=
    oddEndpointTwoCostLimit_eq_cutoffMass q x c D (by linarith only [hsZ] : 1 < Real.sqrt Z)
  rw [Real.sq_sqrt hY0] at heY
  rw [Real.sq_sqrt hZ0] at heZ
  have hk : 0 ≤ 2 + (Real.log x + 2) / Real.sqrt x :=
    add_nonneg (by norm_num only)
      (div_nonneg (by linarith only [Real.log_nonneg hx]) (Real.sqrt_nonneg x))
  rw [heY, heZ]
  linarith only [mul_le_mul_of_nonneg_left hm hk]

/-- For fixed nonnegative cost at x>=64, success at some cutoff in [64,x]
is equivalent to success at x when the conductor log is at least log pi.
Monotonicity proves the forward implication; x supplies the reverse witness.
This removes a redundant scalar optimization variable. -/
theorem oddEndpointTwoCostLimit_exists_cutoff_iff (q : ℕ) {x c D : ℝ}
    (hq : Real.log Real.pi ≤ Real.log q) (hx : 64 ≤ x) (hc : 0 ≤ c) :
    (∃ Y : ℝ, 64 ≤ Y ∧ Y ≤ x ∧ oddEndpointTwoCostLimit q x Y c D < 0) ↔
      oddEndpointTwoCostLimit q x x c D < 0 := by
  constructor
  · rintro ⟨Y, hY, hYx, hneg⟩
    exact
      (oddEndpointTwoCostLimit_antitone_cutoff q hq (by linarith only [hx]) hc hY hYx).trans_lt hneg
  · intro hneg
    exact ⟨x, hx, le_rfl, hneg⟩

end PseudoPrime.LLS.PaperStatements
