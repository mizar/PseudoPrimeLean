/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainRows
public import Mathlib.Data.List.Forall2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerCutoffRows

/-! # Rounded exponential endpoints for finite Gamma main sums -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Boolean certificate for a rounded exponential lower endpoint at one row.
It checks the logarithm sign, comparison with the Taylor lower bound and
the Taylor remainder range. Rounded endpoints keep aggregate denominators
bounded independently of the number of prime powers. -/
def gammaMainApproxCheck (x : ℚ) (r : EulerCenterRow) (e : ℚ) : Bool :=
  decide ((0 : ℚ) ≤ r.lo) &&
    decide (e ≤ Analysis.gammaExpTaylorLower (((r.p ^ (r.k + 1) : ℕ) : ℚ) / x) 24) &&
    decide (((((r.p ^ (r.k + 1) : ℕ) : ℚ) / x) / 25) ≤ 1 / 2)

/-- A checked rounded exponential endpoint supplies a rational lower bound
for the actual normalized Mangoldt contribution. Compare it with the exact
Taylor expression and use the row soundness theorem for the finite cells. -/
theorem gamma_main_row_approx_lower (r : EulerCenterRow) (hc : eulerCenterRowCheck r = true)
    {x R e : ℚ} (hx : 0 < x) (hR : 0 < R) (hRs : (x : ℝ) ≤ (R : ℝ) ^ 2)
    (ha : gammaMainApproxCheck x r e = true) :
    ((r.lo * e / R : ℚ) : ℝ) ≤
      Real.exp (-((r.p ^ (r.k + 1) : ℕ) : ℝ) / (x : ℝ)) *
          ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)) /
        Real.sqrt (x : ℝ) := by
  simp only [gammaMainApproxCheck, Bool.and_eq_true_iff, decide_eq_true_eq] at ha
  have hq := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha.1.2 ha.1.1) hR.le
  exact ((Rat.cast_le (K := ℝ)).mpr hq).trans (gamma_main_row_lower r hc hx hR hRs ha.1.1 ha.2)

/-- Aligned checked exponential endpoints bound the actual finite row sum.
The two-list relation verifies every endpoint and prevents truncation from
unequal list lengths. Induction adds the certified row contributions. -/
theorem gamma_main_rows_approx_lower {rows : List EulerCenterRow} {es : List ℚ}
    (hc : rows.all eulerCenterRowCheck = true) {x R : ℚ} (hx : 0 < x) (hR : 0 < R)
    (hRs : (x : ℝ) ≤ (R : ℝ) ^ 2)
    (ha : List.Forall₂ (fun r e ↦ gammaMainApproxCheck x r e = true) rows es) :
    (((List.zipWith (fun r e ↦ r.lo * e / R) rows es).sum : ℚ) : ℝ) ≤
      (rows.map
          (fun r ↦
            Real.exp (-((r.p ^ (r.k + 1) : ℕ) : ℝ) / (x : ℝ)) *
                ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)) /
              Real.sqrt (x : ℝ))).sum := by
  induction ha with
  | nil => simp only [List.zipWith_nil_left, List.sum_nil, Rat.cast_zero, List.map_nil, le_refl]
  | @cons r e rows es hr ht ih =>
    have hc' := Bool.and_eq_true_iff.mp hc
    have hh := gamma_main_row_approx_lower r hc'.1 hx hR hRs hr
    simpa only [List.zipWith_cons_cons, List.sum_cons, Rat.cast_add, List.map_cons] using
      add_le_add hh (ih hc'.2)

/-- Rounded exponential endpoint certificates and a rational sum comparison
bound the actual finite main sum at any cutoff at most 50000. Exact support
and inherited arithmetic checks remove all finite-series interpretation
premises. This supplies the main lower input of each Gamma cell. -/
theorem gamma_main_prefix_approx_lower {B : ℕ} (hB : B ≤ 50000) (es : List ℚ) {x R L : ℚ}
    (hx : 0 < x) (hR : 0 < R) (hRs : x ≤ R ^ 2)
    (ha : List.Forall₂ (fun r e ↦ gammaMainApproxCheck x r e = true) (centerRowsBelow B) es)
    (hL : L ≤ (List.zipWith (fun r e ↦ r.lo * e / R) (centerRowsBelow B) es).sum) :
    (L : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 B,
        Real.exp (-(n : ℝ) / (x : ℝ)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (x : ℝ) := by
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
    ((Rat.cast_le (K := ℝ)).mpr hL).trans
      (gamma_main_rows_approx_lower (centerRowsBelow_check B) hx hR hsR ha)

/-- Structurally recursive Boolean checker for aligned rounded endpoints.
It checks every row and requires both lists to end together. Unlike the
general two-list decision procedure, its definition is exposed for kernel
evaluation from downstream module files. -/
def gammaMainListCheck (x : ℚ) : List EulerCenterRow → List ℚ → Bool
  | [], [] => true
  | r :: rows, e :: es => gammaMainApproxCheck x r e && gammaMainListCheck x rows es
  | _, _ => false

/-- A successful exposed Boolean check proves the aligned endpoint relation.
Induction checks both lengths and transfers each row's approximation check.
This connects kernel numerical certificates to the finite-sum soundness API. -/
theorem gammaMainListCheck_sound {x : ℚ} {rows : List EulerCenterRow} {es : List ℚ}
    (hc : gammaMainListCheck x rows es = true) :
    List.Forall₂ (fun r e ↦ gammaMainApproxCheck x r e = true) rows es := by
  induction rows generalizing es with
  | nil =>
    cases es with
    | nil => exact List.Forall₂.nil
    | cons e es => simp only [gammaMainListCheck, Bool.false_eq_true] at hc
  | cons r rows ih =>
    cases es with
    | nil => simp only [gammaMainListCheck, Bool.false_eq_true] at hc
    | cons e es =>
      have h := Bool.and_eq_true_iff.mp hc
      exact List.Forall₂.cons h.1 (ih h.2)

end PseudoPrime.PrimeTestBounds.MillerRabin
