/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidpointBracketsRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhase
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevScale43

/-! # Relative smoothing scales for the signed low-zero phase -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For a positive base and relative width between zero and one half, each
smoothing midpoint has square root at most `√x * (1 + δ/4)`. The right
midpoint controls the left, and the square-root scale bound controls the right. -/
theorem midpoint_sqrt_scale {x δ : ℝ} (hx : 0 < x) (hd : 0 ≤ δ) (hd2 : δ ≤ 1 / 2) :
    Real.sqrt ((x - x * δ + x) / 2) ≤ Real.sqrt x * (1 + δ / 4) ∧
      Real.sqrt ((x + (x + x * δ)) / 2) ≤ Real.sqrt x * (1 + δ / 4) := by
  have hp :=
    (scale_power_bounds hx (show (0 : ℝ) ≤ δ / 2 by linarith only [hd])
        (show δ / 2 ≤ 1 / 2 by linarith only [hd2])).1
  have he : x + x * (δ / 2) = (x + (x + x * δ)) / 2 := by ring
  rw [he] at hp
  have hf : 1 + δ / 2 / 2 = 1 + δ / 4 := by ring
  rw [hf] at hp
  constructor
  · exact
      (Real.sqrt_le_sqrt
            (show (x - x * δ + x) / 2 ≤ (x + (x + x * δ)) / 2 by nlinarith only [hx, hd])).trans
        hp
  · exact hp

/-- A positive relative width at most one half bounds the smoothing tail
coefficient by `√x * (1 + δ) * (2/δ)`. This combines the three-halves
power bound with the algebraic width identity. -/
theorem tail_coefficient_scale {x δ : ℝ} (hx : 0 < x) (hd : 0 < δ) (hd2 : δ ≤ 1 / 2) :
    ((x + x * δ) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / (x * δ) ≤
      (Real.sqrt x * (1 + δ)) * (2 / δ) := by
  have hp := scale_power_bounds hx hd.le hd2
  have hpow : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    have hr := Real.rpow_add hx (1 : ℝ) (1 / 2 : ℝ)
    convert hr using 1
    · norm_num only
    · rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have ht := add_le_add hp.2 (le_refl (x ^ (3 / 2 : ℝ)))
  apply le_trans (div_le_div_of_nonneg_right ht (mul_nonneg hx.le hd.le))
  rw [hpow]
  have hxinv := mul_inv_cancel₀ hx.ne'
  simp only [div_eq_mul_inv, mul_inv_rev]
  have heq :
    (x * Real.sqrt x * (1 + 2 * δ) + x * Real.sqrt x) * (δ⁻¹ * x⁻¹) =
      Real.sqrt x * (1 + δ) * (2 * δ⁻¹) := by
    linear_combination (2 * Real.sqrt x * (1 + δ) * δ⁻¹) * hxinv
  exact le_of_eq heq

/-- Normalize an error estimate with an explicit midpoint and curvature
budget by `√x`, preserving the sharper midpoint coefficient. The proof uses
only the positive square root and the identity `(√x)^2 = x`. -/
theorem normalize_phase_budget {x δ K M B C : ℝ} (hx : 0 < x)
    (h :
      C ≤
        x * δ / 2 + Real.log (2 * Real.pi) +
          (Real.sqrt x * (1 + δ / 4) * K + M * (x * δ) ^ 2 / 24) +
          Real.sqrt x * (1 + δ) * B +
          1 / (x * δ)) :
    C / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        ((1 + δ / 4) * K + M * (x * δ) ^ 2 / (24 * Real.sqrt x)) +
        (1 + δ) * B +
        1 / (x * δ * Real.sqrt x) := by
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hi := mul_inv_cancel₀ hs0.ne'
  have hsx : x * (Real.sqrt x)⁻¹ = Real.sqrt x := by
    calc
      x * (Real.sqrt x)⁻¹ = Real.sqrt x ^ 2 * (Real.sqrt x)⁻¹ :=
        congrArg (fun z : ℝ ↦ z * (Real.sqrt x)⁻¹) (Real.sq_sqrt hx.le).symm
      _ = Real.sqrt x * (Real.sqrt x * (Real.sqrt x)⁻¹) := by ring
      _ = _ := by
        rw [hi]; ring
  have heq :
    (x * δ / 2 + Real.log (2 * Real.pi) + (Real.sqrt x * (1 + δ / 4) * K + M * (x * δ) ^ 2 / 24) +
          Real.sqrt x * (1 + δ) * B +
          1 / (x * δ)) /
        Real.sqrt x =
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        ((1 + δ / 4) * K + M * (x * δ) ^ 2 / (24 * Real.sqrt x)) +
        (1 + δ) * B +
        1 / (x * δ * Real.sqrt x) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    linear_combination (δ / 2) * hsx + ((1 + δ / 4) * K) * hi + ((1 + δ) * B) * hi
  have hdiv := div_le_div_of_nonneg_right h hs0.le
  rw [heq] at hdiv
  exact hdiv

/-- For positive x and relative width at most one, the normalized midpoint
curvature term depends only on the relative width. Factor the base and use
`x^(3/2) = x * √x` to cancel all powers of x. -/
theorem phase_curvature_scale {x δ : ℝ} (hx : 0 < x) (hd : δ ≤ 1) :
    3640 * (x - x * δ) ^ (-(3 / 2 : ℝ)) * (x * δ) ^ 2 / (24 * Real.sqrt x) =
      3640 * δ ^ 2 * (1 - δ) ^ (-(3 / 2 : ℝ)) / 24 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hp : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    have h := Real.rpow_add hx (1 : ℝ) (1 / 2 : ℝ)
    convert h using 1
    · norm_num only
    · rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have he : x - x * δ = x * (1 - δ) := by ring
  rw [he, Real.mul_rpow hx.le (sub_nonneg.mpr hd), Real.rpow_neg hx.le, hp]
  have hsq := Real.sq_sqrt hx.le
  field_simp
  rw [hsq]

/-- Under RH and the ordered low-zero bracket and count hypotheses, bound
the normalized ψ error using a relative smoothing width and phase bounds at
both midpoints. The factor `1 + δ/4` preserves the midpoint improvement. -/
theorem psi_error_phase_scale (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x δ K : ℝ} (hx : 0 < x) (hd : 0 < δ) (hd2 : δ ≤ 1 / 2) (hleft : 1 < x - x * δ)
    (hcut : 100 ≤ 2 / δ) (hlo : |zeroHeadPhase g (Real.log ((x - x * δ + x) / 2))| ≤ K)
    (hhi : |zeroHeadPhase g (Real.log ((x + (x + x * δ)) / 2))| ≤ K) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        ((1 + δ / 4) * K + 3640 * δ ^ 2 * (1 - δ) ^ (-(3 / 2 : ℝ)) / 24) +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / (2 / δ) +
            1 / (15 * (2 / δ) ^ 2)) +
        1 / (x * δ * Real.sqrt x) := by
  have hc : zeroCount 100 ≤ 2 * (29 : ℕ) := by
    norm_num only [Nat.cast_ofNat]
    exact hcount
  have hk : 0 ≤ K := (abs_nonneg _).trans hlo
  have htlo : 0 < (x - x * δ + x) / 2 := by linarith only [hleft, hx]
  have hthi : 0 < (x + (x + x * δ)) / 2 := by
    have hm := mul_nonneg hx.le hd.le
    linarith only [hx, hm]
  have hs : Real.sqrt (x + x * δ) ≤ Real.sqrt x * (1 + δ) := by
    have h := (scale_power_bounds hx hd.le hd2).1
    have hh := mul_nonneg (Real.sqrt_nonneg x) hd.le
    nlinarith only [h, hh]
  have hD : 0 ≤ Real.sqrt x * (1 + δ) := mul_nonneg (Real.sqrt_nonneg x) (by linarith only [hd])
  have hzlo :=
    zero_head_phase_of_count hRH (show (0 : ℝ) ≤ 100 by norm_num only) htlo g hmono.injective hpos
      hheight hzero hc
  have hzhi :=
    zero_head_phase_of_count hRH (show (0 : ℝ) ≤ 100 by norm_num only) hthi g hmono.injective hpos
      hheight hzero hc
  have hp :=
    psi_error_midpoint_brackets hRH g hmono hpos hheight hzero hcount hl hu hcut (mul_pos hx hd)
      hleft hD hs (tail_coefficient_scale hx hd hd2) (C := Real.sqrt x * (1 + δ / 4) * K)
      (by
        rw [hzlo, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact
          (mul_le_mul_of_nonneg_left hlo (Real.sqrt_nonneg _)).trans
            (mul_le_mul_of_nonneg_right (midpoint_sqrt_scale hx hd.le hd2).1 hk))
      (by
        rw [hzhi, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact
          (mul_le_mul_of_nonneg_left hhi (Real.sqrt_nonneg _)).trans
            (mul_le_mul_of_nonneg_right (midpoint_sqrt_scale hx hd.le hd2).2 hk))
  have h := normalize_phase_budget hx hp
  rw [phase_curvature_scale hx (by linarith only [hd2])] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
