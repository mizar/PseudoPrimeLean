/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCheck
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimePowerLogRows
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix

/-! # Reusing checked Euler rows as prime-power logarithm rows -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Project a checked Euler-center row to the prime-power logarithm data it contains.
The prime, exponent, binary scale, and logarithm endpoints are retained, and the
Euler row's fixed Taylor length is 32. Root and Gamma data are not included. -/
def eulerLogRow (r : EulerCenterRow) : AnalyticNumberTheory.Arithmetic.PrimePowerLogRow where
  p := r.p
  k := r.k
  j := r.j
  terms := 32
  lo := r.lo
  hi := r.hi

/-- A successful Euler-center row check implies that its projected logarithm row
passes the generic prime-power checker. The primality and log checks are reused. -/
theorem euler_log_row_check {r : EulerCenterRow} (h : eulerCenterRowCheck r = true) :
    AnalyticNumberTheory.Arithmetic.primePowerLogCheck (eulerLogRow r) = true := by
  obtain ⟨h, _⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, hlog⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hp, _⟩ := Bool.and_eq_true_iff.mp h
  exact Bool.and_eq_true_iff.mpr ⟨hp, hlog⟩

/-- A list of checked Euler-center rows projects to a list of checked generic
prime-power logarithm rows, without rechecking the numerical candidates. -/
theorem euler_log_rows_check (rows : List EulerCenterRow)
    (h : rows.all eulerCenterRowCheck = true) :
    (rows.map eulerLogRow).all AnalyticNumberTheory.Arithmetic.primePowerLogCheck = true := by
  apply List.all_eq_true.mpr
  intro q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  exact euler_log_row_check (List.all_eq_true.mp h r hr)

/-- The logarithm endpoints of checked Euler-center rows bound the corresponding
Mangoldt sum on both sides. This applies the generic row theorem to the projection;
it does not claim that the rows cover any particular integer interval. -/
theorem euler_log_rows_bounds (rows : List EulerCenterRow)
    (h : rows.all eulerCenterRowCheck = true) :
    (rows.map (fun r ↦ (r.lo : ℝ))).sum ≤
        (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum ∧
      (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum ≤
        (rows.map (fun r ↦ (r.hi : ℝ))).sum := by
  have h' :=
    AnalyticNumberTheory.Arithmetic.prime_power_log_rows_bounds (rows.map eulerLogRow)
      (euler_log_rows_check rows h)
  simpa only [List.map_map, Function.comp_def, eulerLogRow] using h'

/-- Checked Euler rows extend the psi prefix from `a` to `b` when their Mangoldt
weights equal the interval increment. The coverage equality is an explicit input,
separate from the row checks, and the previous prefix bounds are reused. -/
theorem psi_prefix_of_euler_rows {a b : ℕ} {L U : ℝ} (hab : a ≤ b) (hL : L ≤ Chebyshev.psi a)
    (hU : Chebyshev.psi a ≤ U) (rows : List EulerCenterRow)
    (hrows : rows.all eulerCenterRowCheck = true)
    (hcover :
      (∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n) =
        (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum) :
    L + (rows.map (fun r ↦ (r.lo : ℝ))).sum ≤ Chebyshev.psi b ∧
      Chebyshev.psi b ≤ U + (rows.map (fun r ↦ (r.hi : ℝ))).sum := by
  exact
    AnalyticNumberTheory.Arithmetic.psi_prefix_bounds_of_interval hab hL hU
      (hcover ▸ (euler_log_rows_bounds rows hrows).1)
      (hcover ▸ (euler_log_rows_bounds rows hrows).2)

end PseudoPrime.PrimeTestBounds.MillerRabin
