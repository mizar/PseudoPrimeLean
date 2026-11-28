/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadCert

/-! # Numerical bounds for the H26 endpoint term -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Both high-kernel endpoint contributions are bounded by the same rational cap. -/
private theorem high_head_endpoint_charge (K : HighGaussianKernel) :
    headExpUpper (K.pole * 5) 36 * |headEndpointFast K| ≤ 90202 / 1000000 := by
  cases K <;> decide +kernel

/-- The rational endpoint comparison bounds the middle-value term of H26. -/
public theorem high_principal_edge_cap (K : HighGaussianKernel) :
    |highPrincipalEdge K| ≤ 90202 / 1000000 := by
  have ha := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have hp : 0 ≤ K.pole * 5 := mul_nonneg (Rat.cast_pos.mp ha).le (by norm_num only)
  have he := head_exp_upper_sound hp 36
  have hf : ((headEndpointFast K : ℚ) : ℝ) = K.realProfile.eval 5 := by
    simpa only [head_endpoint_fast_eq, high_rat_profile_map, Rat.coe_castHom, Rat.cast_ofNat] using
      (Polynomial.eval_map_apply (p := highRatProfile K) (Rat.castHom ℝ) (5 : ℚ)).symm
  have hc :
    ((headExpUpper (K.pole * 5) 36 * |headEndpointFast K| : ℚ) : ℝ) ≤ ((90202 / 1000000 : ℚ) : ℝ) :=
    Rat.cast_le.mpr (high_head_endpoint_charge K)
  simp only [Rat.cast_mul, Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat, hf] at hc
  simp only [Rat.cast_mul, Rat.cast_ofNat] at he
  rw [highPrincipalEdge, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul, mul_comm (5 : ℝ)]
  exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans hc

/-- Combine independently checked cell bounds with the certified endpoint bound. -/
private theorem high_head_cap_of_cells (K : HighGaussianKernel) (caps : Fin 32 → ℚ)
    (h : ∀ i, (headIntegralTerms K 36)[i.val]?.getD 0 ≤ caps i) :
    highPrincipalHeadCap K ≤ ((90202 / 1000000 + ∑ i, caps i : ℚ) : ℝ) := by
  apply (head_cap_fast_sound K).trans
  apply Rat.cast_le.mpr
  exact add_le_add (high_head_endpoint_charge K) (Finset.sum_le_sum (fun i _ ↦ h i))

/-- Upper endpoints for the weighted cell charges, in millionths. -/
private def headCellCaps : HighGaussianKernel → Array ℕ
  | .k186 =>
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 11, 74, 99, 168, 491, 275, 1707, 4462, 7007, 8235, 7732,
      5653, 2298, 2105, 7153, 12578, 17936, 22846, 26926, 29777, 31042]
  | .k196 =>
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 11, 73, 104, 170, 507, 284, 1787, 4682, 7329, 8586, 8054,
      5883, 2368, 2232, 7495, 13149, 18744, 23865, 28107, 31067, 32381]

/-- Interpret the stored upper endpoint as a rational cell charge. -/
private def headCellCap (K : HighGaussianKernel) (j : Fin 32) : ℚ :=
  ((headCellCaps K)[j.val]?.getD 0 : ℚ) / 1000000

/-- The desired H26 head cap, in thousandths, depends on the high kernel. -/
@[expose]
public def highHeadCapTicks : HighGaussianKernel → ℕ
  | .k186 => 279
  | .k196 => 288

/-- The rounded cell caps fit the intended head bound after charging the endpoint. -/
private theorem head_cells_budget (K : HighGaussianKernel) :
    (90202 / 1000000 + ∑ j, headCellCap K j : ℚ) ≤ (highHeadCapTicks K : ℚ) / 1000 := by
  cases K <;> decide +kernel

/-- The first weighted cell of K186 fits its rounded upper endpoint. -/
private theorem k186_head_first_cell :
    (headIntegralTerms .k186 36)[0]?.getD 0 ≤ headCellCap .k186 0 := by
  simp only [headIntegralTerms, Array.getElem?_ofFn, Nat.zero_lt_succ, dite_true, Option.getD_some,
    head_coeff_cache_eq]
  decide +kernel

/-- The first weighted cell of K196 fits its rounded upper endpoint. -/
private theorem k196_head_first_cell :
    (headIntegralTerms .k196 36)[0]?.getD 0 ≤ headCellCap .k196 0 := by
  simp only [headIntegralTerms, Array.getElem?_ofFn, Nat.zero_lt_succ, dite_true, Option.getD_some,
    head_coeff_cache_eq]
  decide +kernel

/-- Complete the head cap from the cells beyond the certified first cell. -/
private theorem high_head_cap_of_checks (K : HighGaussianKernel)
    (h : ∀ i, i ≠ 0 → (headIntegralTerms K 36)[i.val]?.getD 0 ≤ headCellCap K i) :
    highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000 := by
  have hall (i : Fin 32) : (headIntegralTerms K 36)[i.val]?.getD 0 ≤ headCellCap K i := by
    by_cases hi : i = 0
    · subst i
      cases K
      · exact k186_head_first_cell
      · exact k196_head_first_cell
    · exact h i hi
  apply (high_head_cap_of_cells K (headCellCap K) hall).trans
  have hb :
    ((90202 / 1000000 + ∑ j, headCellCap K j : ℚ) : ℝ) ≤
      (((highHeadCapTicks K : ℚ) / 1000 : ℚ) : ℝ) :=
    Rat.cast_le.mpr (head_cells_budget K)
  exact hb.trans_eq (by rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat])

/-- Insert the certified endpoint constant and a scalar head bound into the
zero-bracket estimate. -/
public theorem high_principal_midpoint_caps (K : HighGaussianKernel) {l r t : ℝ} (hl : 0 < l)
    (ht : t ∈ Set.Icc l r) (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000) :
    let a := (K.pole : ℝ)
    let M₀ := highCompactMass K
    let M₁ := highCompactSlope K
    ‖highPrincipalMultiplier K t‖ ≤
      ‖highPrincipalMultiplier K ((l + r) / 2)‖ +
        (3 * (K.normalization : ℝ) *
              (5 * M₀ ^ 2 / l ^ 4 + 4 * M₀ ^ 2 / l ^ 5 + 4 * a * M₀ * M₁ / l ^ 6) +
            4 * ((highHeadCapTicks K : ℝ) / 1000) / l ^ 2 +
            4 * (90202 / 1000000) / (l ^ 2 + 1 / 4)) *
          ((r - l) / 2) := by
  intro a M₀ M₁
  refine
    (high_principal_multiplier_midpoint K hl ht).trans
      (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right ?_
          (div_nonneg (sub_nonneg.mpr (ht.1.trans ht.2)) (by norm_num only))))
  unfold highPrincipalDerivCap
  exact
    add_le_add
      (add_le_add le_rfl
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num only))
          (sq_nonneg _)))
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (high_principal_edge_cap K) (by norm_num only))
        (add_nonneg (sq_nonneg _) (by norm_num only)))

/-- The coefficient sums used in the rational derivative estimate. -/
private def highCompactRat (K : HighGaussianKernel) : ℚ × ℚ :=
  match K with
  | .k186 => (335554205356312 / 813989428426, 1729460019748684 / 813989428426)
  | .k196 => (892039868556197 / 970498903459, 5454878552018281 / 970498903459)

/-- Casting the rational coefficient sums gives the analytic masses. -/
private theorem high_compact_rat_eq (K : HighGaussianKernel) :
    ((highCompactRat K).1 : ℝ) = highCompactMass K ∧
      ((highCompactRat K).2 : ℝ) = highCompactSlope K := by
  cases K
  · simpa only [highCompactRat, Rat.cast_div, Rat.cast_ofNat] using
      And.intro k186_compact_sums.1.symm k186_compact_sums.2.symm
  · simpa only [highCompactRat, Rat.cast_div, Rat.cast_ofNat] using
      And.intro k196_compact_sums.1.symm k196_compact_sums.2.symm

/-- The rational error charge for a zero bracket with positive left endpoint. -/
public def highPrincipalBracketError (K : HighGaussianKernel) (l r : ℚ) : ℚ :=
  let (M₀, M₁) := highCompactRat K
  (3 * K.normalization * (5 * M₀ ^ 2 / l ^ 4 + 4 * M₀ ^ 2 / l ^ 5 + 4 * K.pole * M₀ * M₁ / l ^ 6) +
      4 * ((highHeadCapTicks K : ℚ) / 1000) / l ^ 2 +
      4 * (90202 / 1000000) / (l ^ 2 + 1 / 4)) *
    ((r - l) / 2)

/-- The midpoint error on a rational bracket uses the rational error charge. -/
public theorem high_principal_midpoint_bracket (K : HighGaussianKernel) {l r : ℚ} {t : ℝ}
    (hl : 0 < l) (ht : t ∈ Set.Icc (l : ℝ) (r : ℝ))
    (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000) :
    ‖highPrincipalMultiplier K t‖ ≤
      ‖highPrincipalMultiplier K ((l + r : ℚ) / 2 : ℚ)‖ +
        (highPrincipalBracketError K l r : ℝ) := by
  have h := high_principal_midpoint_caps K (Rat.cast_pos.mpr hl) ht hc
  simpa only [highPrincipalBracketError, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one, (high_compact_rat_eq K).1,
    (high_compact_rat_eq K).2] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
