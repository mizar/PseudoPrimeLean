/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEntrance

/-! # Monotonicity tools for the refined residual envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At positive `x`, differentiate a fifth power of an affine logarithm times a real power.
The product and chain rules give the displayed factorization, whose last factor controls
monotonicity of the logarithmic terms in the residual envelope. -/
theorem refined_log_fifth_deriv {b p x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ (b + 2 * Real.log t) ^ 5 * t ^ (-p))
      (x ^ (-p - 1) * (b + 2 * Real.log x) ^ 4 * (10 - p * (b + 2 * Real.log x))) x := by
  have hd :=
    (((Real.hasDerivAt_log hx.ne').const_mul 2).const_add b).pow 5 |>.mul
      (Real.hasDerivAt_rpow_const (Or.inl hx.ne') (p := -p))
  have he :
    5 * (b + 2 * Real.log x) ^ 4 * (2 * x⁻¹) * x ^ (-p) +
        (b + 2 * Real.log x) ^ 5 * (-p * x ^ (-p - 1)) =
      x ^ (-p - 1) * (b + 2 * Real.log x) ^ 4 * (10 - p * (b + 2 * Real.log x)) := by
    rw [Real.rpow_sub_one hx.ne' (-p)]
    ring
  exact he ▸ hd

/-- For `E ≥ 1` and `p ≥ 0`, the logarithmic fifth-power factor decreases on `[E, ∞)`
provided its derivative is nonpositive at `E`. Monotonicity of the logarithm preserves
that sign throughout the interval, allowing a residual term to be bounded at its entrance. -/
theorem refined_log_fifth_antitone {b p E : ℝ} (hE : 1 ≤ E) (hp : 0 ≤ p)
    (hbound : 10 ≤ p * (b + 2 * Real.log E)) :
    AntitoneOn (fun t : ℝ ↦ (b + 2 * Real.log t) ^ 5 * t ^ (-p)) (Set.Ici E) := by
  apply
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici E)
      (fun x hx ↦
        (refined_log_fifth_deriv (b := b) (p := p)
            (zero_lt_one.trans_le (hE.trans hx))).continuousAt.continuousWithinAt)
      (fun x hx ↦
        (refined_log_fifth_deriv (b := b) (p := p)
            (zero_lt_one.trans_le (hE.trans (interior_subset hx)))).hasDerivWithinAt)
  intro x hx
  have hxE : E ≤ x := interior_subset hx
  have hl := Real.log_le_log (zero_lt_one.trans_le hE) hxE
  have hm :=
    mul_le_mul_of_nonneg_left (show b + 2 * Real.log E ≤ b + 2 * Real.log x by linarith only [hl])
      hp
  have hs : 10 - p * (b + 2 * Real.log x) ≤ 0 := by linarith only [hbound, hm]
  exact
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hE.trans hxE)) _) (by positivity)) hs

/-- For nonnegative `a` and `b`, the quotient `(a log x + b) / x` decreases for
`x ≥ 522`. Combine the standard decrease of `log x / x` beyond `exp 1` with the
monotonicity of reciprocal, for use on the linear-logarithm residual terms. -/
theorem refined_log_linear_le {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 522 ≤ x) (hxy : x ≤ y) :
    (a * Real.log y + b) / y ≤ (a * Real.log x + b) / x := by
  have hx0 : 0 < x := by linarith only [hx]
  have he : Real.exp 1 ≤ x := Real.exp_one_lt_three.le.trans (by linarith only [hx])
  have hl := Real.log_div_self_antitoneOn he (he.trans hxy) hxy
  have hi := one_div_le_one_div_of_le hx0 hxy
  have h := add_le_add (mul_le_mul_of_nonneg_left hl ha) (mul_le_mul_of_nonneg_left hi hb)
  convert h using 1 <;> ring

/-- The entrance radius satisfies `log 522 ≥ 5`. Compare it with `2 ^ 9` and use
the certified lower bound for `log 2`; this supplies the derivative-sign threshold. -/
theorem refined_log_entrance : (5 : ℝ) ≤ Real.log 522 := by
  have h :=
    Real.log_le_log (show (0 : ℝ) < 2 ^ 9 by norm_num only)
      (show (2 : ℝ) ^ 9 ≤ 522 by norm_num only)
  rw [Real.log_pow] at h
  have h2 := Real.log_two_gt_d9
  norm_num only at h
  linarith only [h, h2]

/-- The conductor contribution decreases for radii at least `522`.
Rewrite its real power with exponent `-29/25` and use the logarithmic fifth-power
monotonicity criterion with the certified entrance logarithm. -/
theorem refined_conductor_antitone :
    AntitoneOn (fun R : ℝ ↦ R * (R ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5)
      (Set.Ici 522) := by
  have hb : (10 : ℝ) ≤ (29 / 25 : ℝ) * (21 / 8 + 2 * Real.log 522) := by
    linarith only [refined_log_entrance]
  have ha :=
    refined_log_fifth_antitone (b := (21 / 8 : ℝ)) (p := (29 / 25 : ℝ)) (E := 522)
      (by norm_num only) (by norm_num only) hb
  intro x hx y hy hxy
  have he {z : ℝ} (hz : 522 ≤ z) :
    z * (z ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (z ^ 2)) ^ 5 =
      ((21 / 8 : ℝ) + 2 * Real.log z) ^ 5 * z ^ (-(29 / 25 : ℝ)) := by
    have hz0 : 0 < z := by linarith only [hz]
    have hr : (z ^ 2) ^ (-(27 / 25 : ℝ)) = z ^ (-(54 / 25 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]
      norm_num only
    have hr' : z * z ^ (-(54 / 25 : ℝ)) = z ^ (-(29 / 25 : ℝ)) := by
      calc
        _ = z ^ (1 : ℝ) * z ^ (-(54 / 25 : ℝ)) := by rw [Real.rpow_one]
        _ = z ^ (1 + (-(54 / 25 : ℝ))) := (Real.rpow_add hz0 _ _).symm
        _ = _ := by norm_num only
    rw [hr, hr', Real.log_pow]
    norm_num only
    ring
  change
    y * (y ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (y ^ 2)) ^ 5 ≤
      x * (x ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (x ^ 2)) ^ 5
  rw [he hx, he hy]
  exact ha hx hy hxy

/-- The fifth-power part of the dual tail decreases for radii at least `522`.
Rewrite the squared-radius power with exponent `-54/25` and apply the general
logarithmic monotonicity criterion at the certified entrance. -/
theorem refined_dual_fifth_antitone :
    AntitoneOn (fun R : ℝ ↦ (R ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5)
      (Set.Ici 522) := by
  have hb : (10 : ℝ) ≤ (54 / 25 : ℝ) * (21 / 8 + 2 * Real.log 522) := by
    linarith only [refined_log_entrance]
  have ha :=
    refined_log_fifth_antitone (b := (21 / 8 : ℝ)) (p := (54 / 25 : ℝ)) (E := 522)
      (by norm_num only) (by norm_num only) hb
  intro x hx y hy hxy
  have he {z : ℝ} (hz : 522 ≤ z) :
    (z ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (z ^ 2)) ^ 5 =
      ((21 / 8 : ℝ) + 2 * Real.log z) ^ 5 * z ^ (-(54 / 25 : ℝ)) := by
    have hz0 : 0 < z := by linarith only [hz]
    have hr : (z ^ 2) ^ (-(27 / 25 : ℝ)) = z ^ (-(54 / 25 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]
      norm_num only
    rw [hr, Real.log_pow]
    norm_num only
    ring
  change
    (y ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (y ^ 2)) ^ 5 ≤
      (x ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (x ^ 2)) ^ 5
  rw [he hx, he hy]
  exact ha hx hy hxy

/-- The negative real power of the squared radius decreases for radii at least `522`.
The square is positive and increasing, and a nonpositive exponent reverses the
comparison. This bounds the constant part of the dual tail. -/
theorem refined_dual_power_antitone :
    AntitoneOn (fun R : ℝ ↦ (R ^ 2) ^ (-(27 / 25 : ℝ))) (Set.Ici 522) := by
  intro x hx y hy hxy
  have hx' : (522 : ℝ) ≤ x := hx
  have hx0 : 0 < x := by linarith only [hx']
  have hsq : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx0.le hxy 2
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hx0) hsq (by norm_num only)

/-- The full one-variable residual envelope decreases for all radii at least `522`.
The conductor and dual terms decrease by the preceding real-power estimates; the
remaining terms decrease by the logarithm-over-radius and reciprocal comparisons.
This reduces each half-line residual certificate to its numerical endpoint. -/
theorem refined_residual_antitone : AntitoneOn refinedResidualEnvelope (Set.Ici 522) := by
  intro x hx y hy hxy
  have hx' : (522 : ℝ) ≤ x := hx
  have hy' : (522 : ℝ) ≤ y := hy
  have hx0 : 0 < x := by linarith only [hx']
  have hy0 : 0 < y := hx0.trans_le hxy
  have hc := refined_conductor_antitone hx hy hxy
  have hd := refined_dual_fifth_antitone hx hy hxy
  have hp := refined_dual_power_antitone hx hy hxy
  have hl :=
    refined_log_linear_le (a := (3678 / 1000 : ℝ)) (b := ((1839 / 1000 : ℝ) * (21 / 8) + 2))
      (by norm_num only) (by norm_num only) hx' hxy
  have hld :=
    refined_log_linear_le (a := (3678 / 1000 : ℝ)) (b := 2) (by norm_num only) (by norm_num only)
      hx' hxy
  have hi := one_div_le_one_div_of_le hx0 hxy
  have hsqrt := Real.sqrt_le_sqrt hxy
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hs := one_div_le_one_div_of_le hsx hsqrt
  dsimp only [refinedResidualEnvelope, refinedPaperResidual]
  have hw := refined_unit_weight_nonneg
  have hc' :=
    mul_le_mul_of_nonneg_left hc
      (show
        (0 : ℝ) ≤ (1000 / 261) * ((27 / 25 : ℝ) ^ 5 / 120 * Real.exp (-((27 / 25 : ℝ) * (21 / 8))))
        by positivity)
  have hd' :=
    mul_le_mul_of_nonneg_left hd
      (show
        (0 : ℝ) ≤
          ((27 / 25 : ℝ) ^ 5 / 120 * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            ((50 / 29 : ℝ) ^ 2 + 50 / 79)
        by positivity)
  have hp' :=
    mul_le_mul_of_nonneg_left hp
      (show
        (0 : ℝ) ≤
          ((27 / 25 : ℝ) ^ 5 / 120 * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            ((25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59))
        by positivity)
  have hl' :=
    mul_le_mul_of_nonneg_left hl
      (show (0 : ℝ) ≤ 5 * ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) by positivity)
  have hld' :=
    mul_le_mul_of_nonneg_left hld (show (0 : ℝ) ≤ 4 * |refinedWeightDeriv 1| by positivity)
  have hi' :=
    mul_le_mul_of_nonneg_left hi
      (show (0 : ℝ) ≤ 4 * refinedWeight 1 * (1839 / 1000 : ℝ) by positivity)
  have hs' :=
    mul_le_mul_of_nonneg_left hs
      (show (0 : ℝ) ≤ 4 * refinedWeight 1 * ((231 / 2500 : ℝ) * (7 / 3)) by positivity)
  have he (z : ℝ) (hz : z ≠ 0) :
    4 * |refinedWeightDeriv 1| * ((231 / 5000 : ℝ) * z + (1839 / 1000 : ℝ) * (2 * Real.log z) + 2) /
        z =
      4 * |refinedWeightDeriv 1| *
        ((231 / 5000 : ℝ) + ((3678 / 1000 : ℝ) * Real.log z + 2) / z) := by
    rw [mul_div_assoc, add_div, add_div, mul_div_cancel_right₀ _ hz]
    ring
  rw [he y hy0.ne', he x hx0.ne']
  simp only [div_eq_mul_inv] at hc' hd' hp' hl' hld' hi' hs' ⊢
  nlinarith only [hc', hd', hp', hl', hld', hi', hs']

/-- Monotonicity of the residual envelope and its three endpoint bounds imply the
three half-line bounds used by the piecewise witness theorem. Apply antitonicity at
each entrance; the endpoint inequalities and monotonicity remain explicit hypotheses. -/
theorem refined_envelopes_of_endpoints (hanti : AntitoneOn refinedResidualEnvelope (Set.Ici 522))
    (h3 : refinedResidualEnvelope 522 ≤ (27 / 25 : ℝ) ^ 5 * 3)
    (h1 : refinedResidualEnvelope 1566 ≤ (27 / 25 : ℝ) ^ 5 * 1)
    (h0 : refinedResidualEnvelope 5220 ≤ (27 / 25 : ℝ) ^ 5 * 0) :
    (∀ R : ℝ, 522 ≤ R → refinedResidualEnvelope R ≤ (27 / 25 : ℝ) ^ 5 * 3) ∧
      (∀ R : ℝ, 1566 ≤ R → refinedResidualEnvelope R ≤ (27 / 25 : ℝ) ^ 5 * 1) ∧
      (∀ R : ℝ, 5220 ≤ R → refinedResidualEnvelope R ≤ (27 / 25 : ℝ) ^ 5 * 0) := by
  constructor
  · intro R hR
    exact (hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hR) hR).trans h3
  constructor
  · intro R hR
    exact
      (hanti (Set.mem_Ici.mpr (by norm_num only)) (Set.mem_Ici.mpr (by linarith only [hR]))
            hR).trans
        h1
  · intro R hR
    exact
      (hanti (Set.mem_Ici.mpr (by norm_num only)) (Set.mem_Ici.mpr (by linarith only [hR]))
            hR).trans
        h0

/-- For `L ≥ 1000`, monotonicity and the three endpoint estimates bound the
residual at the selected root. Transfer each endpoint estimate to its half-line
and apply the piecewise root certificate. -/
theorem refined_selected_residual_of_endpoints {L : ℝ} (hL : 1000 ≤ L)
    (hanti : AntitoneOn refinedResidualEnvelope (Set.Ici 522))
    (h3 : refinedResidualEnvelope 522 ≤ (27 / 25 : ℝ) ^ 5 * 3)
    (h1 : refinedResidualEnvelope 1566 ≤ (27 / 25 : ℝ) ^ 5 * 1)
    (h0 : refinedResidualEnvelope 5220 ≤ (27 / 25 : ℝ) ^ 5 * 0) :
    refinedPaperResidual L (refinedPaperRoot L (refinedPaperAllowance L) ^ 2) ≤
      (27 / 25 : ℝ) ^ 5 * refinedPaperAllowance L := by
  have h := refined_envelopes_of_endpoints hanti h3 h1 h0
  exact refined_selected_residual_of_envelopes hL h.1 h.2.1 h.2.2

/-- For `L ≥ 1000`, the three entrance estimates alone bound the residual at the
selected paper root. The envelope is decreasing on the full relevant half-line,
so the previously conditional monotonicity premise is discharged. -/
theorem refined_selected_residual_of_three {L : ℝ} (hL : 1000 ≤ L)
    (h3 : refinedResidualEnvelope 522 ≤ (27 / 25 : ℝ) ^ 5 * 3)
    (h1 : refinedResidualEnvelope 1566 ≤ (27 / 25 : ℝ) ^ 5 * 1)
    (h0 : refinedResidualEnvelope 5220 ≤ (27 / 25 : ℝ) ^ 5 * 0) :
    refinedPaperResidual L (refinedPaperRoot L (refinedPaperAllowance L) ^ 2) ≤
      (27 / 25 : ℝ) ^ 5 * refinedPaperAllowance L := by
  exact refined_selected_residual_of_endpoints hL refined_residual_antitone h3 h1 h0

end PseudoPrime.PrimeTestBounds.MillerRabin
