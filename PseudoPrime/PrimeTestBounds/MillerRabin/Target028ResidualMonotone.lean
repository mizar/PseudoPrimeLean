/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028HighScalar
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleMonotonicity

/-! # High-range 0.28 residual envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The paper residual with its logarithmic variable bounded by the selected
scale relation. It reduces the high-range certificate to one real variable. -/
noncomputable def target028ResidualEnvelope (R : ℝ) : ℝ :=
  target028PaperResidual ((1000 / 529 : ℝ) * R) R

/-- At positive high-range scales, the residual is bounded by its one-variable
envelope. Only the nonnegative conductor factor depends on the logarithm. -/
theorem target028_residual_le_envelope {L R : ℝ} (hR : (529 / 10 : ℝ) ≤ R)
    (hLR : (529 / 1000 : ℝ) * L ≤ R) :
    target028PaperResidual L R ≤ target028ResidualEnvelope R := by
  have hR1 : (1 : ℝ) ≤ R ^ 2 := by nlinarith only [hR]
  have hlog : 0 ≤ Real.log (R ^ 2) := Real.log_nonneg hR1
  have hc :
    0 ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
        (R ^ 2) ^ (-(27 / 25 : ℝ)) *
        ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5) := by
    positivity
  have hL : L ≤ (1000 / 529 : ℝ) * R := by linarith only [hLR]
  have hm :=
    mul_le_mul_of_nonneg_right (show 2 * L ≤ 2 * ((1000 / 529 : ℝ) * R) by linarith only [hL]) hc
  dsimp only [target028ResidualEnvelope, target028PaperResidual]
  linarith only [hm]

/-- For nonnegative `a` and `b`, the quotient `(a log x + b) / x` decreases for
`x ≥ (529 / 10 : ℝ)`. Combine the standard decrease of `log x / x` beyond `exp 1` with the
monotonicity of reciprocal, for use on the linear-logarithm residual terms. -/
theorem target028_log_linear_le {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : (529 / 10 : ℝ) ≤ x)
    (hxy : x ≤ y) : (a * Real.log y + b) / y ≤ (a * Real.log x + b) / x := by
  have hx0 : 0 < x := by linarith only [hx]
  have he : Real.exp 1 ≤ x := Real.exp_one_lt_three.le.trans (by linarith only [hx])
  have hl := Real.log_div_self_antitoneOn he (he.trans hxy) hxy
  have hi := one_div_le_one_div_of_le hx0 hxy
  have h := add_le_add (mul_le_mul_of_nonneg_left hl ha) (mul_le_mul_of_nonneg_left hi hb)
  convert h using 1 <;> ring

/-- The entrance radius satisfies `log (529/10) ≥ 3`. Compare it with `2 ^ 5` and use
the certified lower bound for `log 2`; this supplies the derivative-sign threshold. -/
theorem target028_log_entrance : (3 : ℝ) ≤ Real.log (529 / 10 : ℝ) := by
  have h :=
    Real.log_le_log (show (0 : ℝ) < 2 ^ 5 by norm_num only)
      (show (2 : ℝ) ^ 5 ≤ (529 / 10 : ℝ) by norm_num only)
  rw [Real.log_pow] at h
  have h2 := Real.log_two_gt_d9
  norm_num only at h
  linarith only [h, h2]

/-- The conductor contribution decreases for radii at least `(529 / 10 : ℝ)`.
Rewrite its real power with exponent `-29/25` and use the logarithmic fifth-power
monotonicity criterion with the certified entrance logarithm. -/
theorem target028_conductor_antitone :
    AntitoneOn (fun R : ℝ ↦ R * (R ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5)
      (Set.Ici (529 / 10 : ℝ)) := by
  have hb : (10 : ℝ) ≤ (29 / 25 : ℝ) * (21 / 8 + 2 * Real.log (529 / 10 : ℝ)) := by
    linarith only [target028_log_entrance]
  have ha :=
    refined_log_fifth_antitone (b := (21 / 8 : ℝ)) (p := (29 / 25 : ℝ)) (E := (529 / 10 : ℝ))
      (by norm_num only) (by norm_num only) hb
  intro x hx y hy hxy
  have he {z : ℝ} (hz : (529 / 10 : ℝ) ≤ z) :
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

/-- The fifth-power part of the dual tail decreases for radii at least `(529 / 10 : ℝ)`.
Rewrite the squared-radius power with exponent `-54/25` and apply the general
logarithmic monotonicity criterion at the certified entrance. -/
theorem target028_dual_fifth_antitone :
    AntitoneOn (fun R : ℝ ↦ (R ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5)
      (Set.Ici (529 / 10 : ℝ)) := by
  have hb : (10 : ℝ) ≤ (54 / 25 : ℝ) * (21 / 8 + 2 * Real.log (529 / 10 : ℝ)) := by
    linarith only [target028_log_entrance]
  have ha :=
    refined_log_fifth_antitone (b := (21 / 8 : ℝ)) (p := (54 / 25 : ℝ)) (E := (529 / 10 : ℝ))
      (by norm_num only) (by norm_num only) hb
  intro x hx y hy hxy
  have he {z : ℝ} (hz : (529 / 10 : ℝ) ≤ z) :
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

/-- The negative real power of the squared radius decreases for radii at least `(529 / 10 : ℝ)`.
The square is positive and increasing, and a nonpositive exponent reverses the
comparison. This bounds the constant part of the dual tail. -/
theorem target028_dual_power_antitone :
    AntitoneOn (fun R : ℝ ↦ (R ^ 2) ^ (-(27 / 25 : ℝ))) (Set.Ici (529 / 10 : ℝ)) := by
  intro x hx y hy hxy
  have hx' : ((529 / 10 : ℝ) : ℝ) ≤ x := hx
  have hx0 : 0 < x := by linarith only [hx']
  have hsq : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx0.le hxy 2
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hx0) hsq (by norm_num only)

/-- The full one-variable residual envelope decreases for all radii at least `(529 / 10 : ℝ)`.
The conductor and dual terms decrease by the preceding real-power estimates; the
remaining terms decrease by the logarithm-over-radius and reciprocal comparisons.
This reduces each half-line residual certificate to its numerical endpoint. -/
theorem target028_residual_antitone :
    AntitoneOn target028ResidualEnvelope (Set.Ici (529 / 10 : ℝ)) := by
  intro x hx y hy hxy
  have hx' : ((529 / 10 : ℝ) : ℝ) ≤ x := hx
  have hy' : ((529 / 10 : ℝ) : ℝ) ≤ y := hy
  have hx0 : 0 < x := by linarith only [hx']
  have hy0 : 0 < y := hx0.trans_le hxy
  have hc := target028_conductor_antitone hx hy hxy
  have hd := target028_dual_fifth_antitone hx hy hxy
  have hp := target028_dual_power_antitone hx hy hxy
  have hl :=
    target028_log_linear_le (a := (3678 / 1000 : ℝ)) (b := ((1839 / 1000 : ℝ) * (21 / 8) + 2))
      (by norm_num only) (by norm_num only) hx' hxy
  have hld :=
    target028_log_linear_le (a := (3678 / 1000 : ℝ)) (b := 2) (by norm_num only) (by norm_num only)
      hx' hxy
  have hi := one_div_le_one_div_of_le hx0 hxy
  have hsqrt := Real.sqrt_le_sqrt hxy
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hs := one_div_le_one_div_of_le hsx hsqrt
  dsimp only [target028ResidualEnvelope, target028PaperResidual]
  have hw := refined_unit_weight_nonneg
  have hc' :=
    mul_le_mul_of_nonneg_left hc
      (show
        (0 : ℝ) ≤ (2000 / 529) * ((27 / 25 : ℝ) ^ 5 / 120 * Real.exp (-((27 / 25 : ℝ) * (21 / 8))))
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
            ((100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27))
        by positivity)
  have hl' :=
    mul_le_mul_of_nonneg_left hl
      (show (0 : ℝ) ≤ 5 * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) by positivity)
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

end PseudoPrime.PrimeTestBounds.MillerRabin
