/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainApproximations
public import PseudoPrime.LLS.PrincipalExponentialTailBounds

/-! # Upper endpoints for finite principal Gamma sums -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked prime-power row and a rational exponential upper endpoint
bound the actual normalized Mangoldt contribution above. The positive radius
bounds the square root below. This is the upper counterpart of the finite
main lower certificate, used before adjoining the geometric tail. -/
theorem gamma_main_row_approx_upper (r : EulerCenterRow) (hc : eulerCenterRowCheck r = true)
    {x R e : ℚ} (hx : 0 < x) (hR : 0 < R) (hRs : (R : ℝ) ^ 2 ≤ (x : ℝ))
    (he : Analysis.gammaExpTaylorUpper (((r.p ^ (r.k + 1) : ℕ) : ℚ) / x) ≤ e) :
    Real.exp (-((r.p ^ (r.k + 1) : ℕ) : ℝ) / (x : ℝ)) *
          ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)) /
        Real.sqrt (x : ℝ) ≤
      ((r.hi * e / R : ℚ) : ℝ) := by
  have hRR := (Rat.cast_pos (K := ℝ)).mpr hR
  have hs := Real.le_sqrt_of_sq_le hRs
  have ht : (0 : ℚ) ≤ (((r.p ^ (r.k + 1) : ℕ) : ℚ) / x) := div_nonneg (Nat.cast_nonneg _) hx.le
  have hb := (Analysis.gamma_exp_taylor_upper_valid ht).trans ((Rat.cast_le (K := ℝ)).mpr he)
  norm_num only [Rat.cast_div, Rat.cast_natCast] at hb
  rw [← neg_div] at hb
  have hl := (checked_row_log_bounds hc).2
  rw [← checked_row_mangoldt_eq_log hc] at hl
  have hm := mul_le_mul hb hl ArithmeticFunction.vonMangoldt_nonneg ((Real.exp_pos _).le.trans hb)
  have hd :=
    (div_le_div_of_nonneg_right hm (Real.sqrt_nonneg (x : ℝ))).trans
      (div_le_div_of_nonneg_left
        (mul_nonneg ((Real.exp_pos _).le.trans hb) (ArithmeticFunction.vonMangoldt_nonneg.trans hl))
        hRR hs)
  simpa only [Rat.cast_div, Rat.cast_mul, mul_comm] using hd

/-- Aligned rational exponential upper endpoints bound a sum over checked
prime-power rows. Both lists end together, so no contribution is omitted.
The result is the finite upper input for the principal Gamma series. -/
theorem gamma_main_rows_approx_upper {rows : List EulerCenterRow} {es : List ℚ}
    (hc : rows.all eulerCenterRowCheck = true) {x R : ℚ} (hx : 0 < x) (hR : 0 < R)
    (hRs : (R : ℝ) ^ 2 ≤ (x : ℝ))
    (ha :
      List.Forall₂ (fun r e ↦ Analysis.gammaExpTaylorUpper (((r.p ^ (r.k + 1) : ℕ) : ℚ) / x) ≤ e)
        rows es) :
    (rows.map
          (fun r ↦
            Real.exp (-((r.p ^ (r.k + 1) : ℕ) : ℝ) / (x : ℝ)) *
                ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)) /
              Real.sqrt (x : ℝ))).sum ≤
      (((List.zipWith (fun r e ↦ r.hi * e / R) rows es).sum : ℚ) : ℝ) := by
  induction ha with
  | nil => simp only [List.zipWith_nil_left, List.sum_nil, Rat.cast_zero, List.map_nil, le_refl]
  | @cons r e rows es hr ht ih =>
    have hc' := Bool.and_eq_true_iff.mp hc
    have hh := gamma_main_row_approx_upper r hc'.1 hx hR hRs hr
    simpa only [List.zipWith_cons_cons, List.sum_cons, Rat.cast_add, List.map_cons] using
      add_le_add hh (ih hc'.2)

/-- Exact support and a rational aggregation upper bound give an upper
bound on the actual finite principal Gamma sum at a cutoff through 50000.
The endpoint relation accounts for every prime power and inherits all row
checks from the center certificate. The infinite tail is handled separately. -/
theorem gamma_main_prefix_approx_upper {B : ℕ} (hB : B ≤ 50000) (es : List ℚ) {x R U : ℚ}
    (hx : 0 < x) (hR : 0 < R) (hRs : R ^ 2 ≤ x)
    (ha :
      List.Forall₂ (fun r e ↦ Analysis.gammaExpTaylorUpper (((r.p ^ (r.k + 1) : ℕ) : ℚ) / x) ≤ e)
        (centerRowsBelow B) es)
    (hU : (List.zipWith (fun r e ↦ r.hi * e / R) (centerRowsBelow B) es).sum ≤ U) :
    (∑ n ∈ Finset.Ioc 0 B,
        Real.exp (-(n : ℝ) / (x : ℝ)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (x : ℝ)) ≤
      (U : ℝ) := by
  have hz :
    ∀ n : ℕ,
      ¬IsPrimePow n →
        Real.exp (-(n : ℝ) / (x : ℝ)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (x : ℝ) =
          0 := by
    intro n hn
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, mul_zero, zero_div]
  rw [centerRowsBelow_sum _ hz hB]
  have hsR := (Rat.cast_le (K := ℝ)).mpr hRs
  rw [Rat.cast_pow] at hsR
  exact
    (gamma_main_rows_approx_upper (centerRowsBelow_check B) hx hR hsR ha).trans
      ((Rat.cast_le (K := ℝ)).mpr hU)

/-- Exposed structural checker for aligned upper exponential endpoints.
Every row is checked and unequal list lengths are rejected. Its soundness
theorem supplies the relation required by finite principal upper bounds. -/
def gammaUpperListCheck (x : ℚ) : List EulerCenterRow → List ℚ → Bool
  | [], [] => true
  | r :: rows, e :: es =>
    decide (Analysis.gammaExpTaylorUpper (((r.p ^ (r.k + 1) : ℕ) : ℚ) / x) ≤ e) &&
      gammaUpperListCheck x rows es
  | _, _ => false

/-- A successful structural upper-endpoint check supplies every rational
comparison with equal list lengths. Induction transfers the Boolean checks
to the two-list relation consumed by the finite principal upper theorem. -/
theorem gammaUpperListCheck_sound {x : ℚ} {rows : List EulerCenterRow} {es : List ℚ}
    (hc : gammaUpperListCheck x rows es = true) :
    List.Forall₂ (fun r e ↦ Analysis.gammaExpTaylorUpper (((r.p ^ (r.k + 1) : ℕ) : ℚ) / x) ≤ e) rows
      es := by
  induction rows generalizing es with
  | nil =>
    cases es with
    | nil => exact List.Forall₂.nil
    | cons e es => simp only [gammaUpperListCheck, Bool.false_eq_true] at hc
  | cons r rows ih =>
    cases es with
    | nil => simp only [gammaUpperListCheck, Bool.false_eq_true] at hc
    | cons e es =>
      have h := Bool.and_eq_true_iff.mp hc
      exact List.Forall₂.cons (of_decide_eq_true h.1) (ih h.2)

/-- A finite normalized principal upper bound and an explicit tail bound
control the actual infinite principal Gamma series at positive scale.
Separate the zero term, apply the existing exponential-tail theorem, and
divide by the positive square root. No RH assumption is needed here. -/
theorem gamma_principal_upper_of_prefix {x U T : ℝ} (hx : 0 < x) (B : ℕ)
    (hU :
      (∑ n ∈ Finset.Ioc 0 B,
          Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x) ≤
        U)
    (hT : LLS.principalExponentialTailBound x (B + 1) / Real.sqrt x ≤ T) :
    (∑' n : ℕ, Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x) ≤
      U + T := by
  have ht :=
    div_le_div_of_nonneg_right (LLS.principalExponentialMass_le_finite_add_tail hx (B + 1))
      (Real.sqrt_nonneg x)
  rw [add_div] at ht
  change
    LLS.principalExponentialMass x / Real.sqrt x ≤
      (∑ n ∈ Finset.range (B + 1), Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n) /
          Real.sqrt x +
        LLS.principalExponentialTailBound x (B + 1) / Real.sqrt x at ht
  rw [Finset.sum_div, Nat.range_succ_eq_Icc_zero, ←
    Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le B)] at ht
  simp only [Nat.cast_zero, neg_zero, zero_div, Real.exp_zero, ArithmeticFunction.map_zero,
    mul_zero, add_zero] at ht
  rw [tsum_div_const]
  exact ht.trans (add_le_add hU hT)

end PseudoPrime.PrimeTestBounds.MillerRabin
