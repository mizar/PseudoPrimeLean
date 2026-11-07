/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowArithmetic
public import PseudoPrime.Analysis.GammaExpRationalBounds

/-! # Certified finite exponential Mangoldt row bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked prime-power row contributes at least its rational Taylor lower
value at a positive rational scale. The rational radius bounds its square root
above, the logarithm lower endpoint is nonnegative, and the Taylor height is
within the certified geometric remainder range. Compare normalized
exponentials before multiplying logarithms. This supplies finite Gamma cells. -/
theorem gamma_main_row_lower (r : EulerCenterRow) (hc : eulerCenterRowCheck r = true) {x R : ℚ}
    (hx : 0 < x) (hR : 0 < R) (hRs : (x : ℝ) ≤ (R : ℝ) ^ 2) (hlo : (0 : ℚ) ≤ r.lo)
    (ht : (((r.p ^ (r.k + 1) : ℕ) : ℚ) / x) / 25 ≤ 1 / 2) :
    ((r.lo * Analysis.gammaExpTaylorLower (((r.p ^ (r.k + 1) : ℕ) : ℚ) / x) 24 / R : ℚ) : ℝ) ≤
      Real.exp (-((r.p ^ (r.k + 1) : ℕ) : ℝ) / (x : ℝ)) *
          ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)) /
        Real.sqrt (x : ℝ) := by
  have hxR := (Rat.cast_pos (K := ℝ)).mpr hx
  have hRR := (Rat.cast_pos (K := ℝ)).mpr hR
  have hs0 := Real.sqrt_pos.mpr hxR
  have hs := (Real.sqrt_le_iff).mpr ⟨hRR.le, hRs⟩
  have he := Analysis.gamma_exp_taylor_lower_valid (div_nonneg (Nat.cast_nonneg _) hx.le) ht
  norm_num only [Rat.cast_div, Rat.cast_natCast] at he
  rw [← neg_div] at he
  have hed :=
    (div_le_div_of_nonneg_right he hRR.le).trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le hs0 hs)
  have hl := (checked_row_log_bounds hc).1
  rw [← checked_row_mangoldt_eq_log hc] at hl
  have hm :=
    mul_le_mul hed hl ((Rat.cast_nonneg (K := ℝ)).mpr hlo) (div_nonneg (Real.exp_pos _).le hs0.le)
  simpa only [Rat.cast_div, Rat.cast_mul, div_mul_eq_mul_div, mul_div_assoc, mul_comm] using hm

/-- Sum rational Taylor lower values over checked rows at a positive scale.
The radius bounds the square root above and each row satisfies the logarithm
sign and Taylor remainder hypotheses. Cast the rational sum and apply the
pointwise inequality. This is the finite main-sum input for Gamma cells. -/
theorem gamma_main_rows_lower (rows : List EulerCenterRow)
    (hc : rows.all eulerCenterRowCheck = true) {x R : ℚ} (hx : 0 < x) (hR : 0 < R) (hRs : x ≤ R ^ 2)
    (hb : ∀ r ∈ rows, (0 : ℚ) ≤ r.lo ∧ (((r.p ^ (r.k + 1) : ℕ) : ℚ) / x) / 25 ≤ 1 / 2) :
    (((rows.map
              (fun r ↦
                r.lo * Analysis.gammaExpTaylorLower (((r.p ^ (r.k + 1) : ℕ) : ℚ) / x) 24 / R)).sum :
          ℚ) :
        ℝ) ≤
      (rows.map
          (fun r ↦
            Real.exp (-((r.p ^ (r.k + 1) : ℕ) : ℝ) / (x : ℝ)) *
                ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)) /
              Real.sqrt (x : ℝ))).sum := by
  have hsR := (Rat.cast_le (K := ℝ)).mpr hRs
  rw [Rat.cast_pow] at hsR
  have hs :=
    List.sum_le_sum
      (fun r hr ↦
        gamma_main_row_lower r (List.all_eq_true.mp hc r hr) hx hR hsR (hb r hr).1 (hb r hr).2)
  simpa only [Rat.cast_list_sum, List.map_map, Function.comp_def] using hs

end PseudoPrime.PrimeTestBounds.MillerRabin
