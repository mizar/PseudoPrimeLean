/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtChecker
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGeneral

/-! # Square-root psi cells with coefficient 81/100 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Check endpoint order, crossing inequalities and squared bounds for a candidate cell using
coefficient `81 / 100`. The endpoint psi inequalities are supplied separately. -/
def psi81CellCheck (r : PsiSqrtCell) : Bool :=
  decide
    (1 ≤ r.a ∧
      r.a < r.b ∧
      1000 * r.b ≤ r.lo + r.cb ∧
      r.hi ≤ 1000 * r.a + r.ca ∧ r.ca ^ 2 ≤ 656100 * r.a ∧ r.cb ^ 2 ≤ 656100 * r.b)

/-- A squared integer guard bounds a thousandths-scaled value by `81 / 100` times a square root. -/
theorem psi81_scaled_sqrt_lower {n q : ℕ} (hq : q ^ 2 ≤ 656100 * n) :
    (q : ℝ) / 1000 ≤ (81 / 100 : ℝ) * Real.sqrt n := by
  have h : (q : ℝ) ^ 2 ≤ 656100 * (n : ℝ) := by exact_mod_cast hq
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hn := Real.sqrt_nonneg (n : ℝ)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  nlinarith only [h, hs, hn, hq0]

/-- If the integer guard succeeds and the two psi endpoint bounds hold, the `81 / 100`
square-root error bound holds at every real point in the cell. The result contains no candidate
table and can be composed with other independently checked cells. -/
theorem psi81_cell_sound (r : PsiSqrtCell) (hcheck : psi81CellCheck r = true)
    (hl : (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a)
    (hu : Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000) {x : ℝ} (ha : (r.a : ℝ) ≤ x)
    (hb : x < r.b) : |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hc :
    1 ≤ r.a ∧
      r.a < r.b ∧
      1000 * r.b ≤ r.lo + r.cb ∧
      r.hi ≤ 1000 * r.a + r.ca ∧ r.ca ^ 2 ≤ 656100 * r.a ∧ r.cb ^ 2 ≤ 656100 * r.b :=
    of_decide_eq_true hcheck
  have ha1 : (1 : ℝ) ≤ r.a := by exact_mod_cast hc.1
  have hleft : (1000 : ℝ) * r.b ≤ (r.lo : ℝ) + r.cb := by exact_mod_cast hc.2.2.1
  have hright : (r.hi : ℝ) ≤ 1000 * r.a + r.ca := by exact_mod_cast hc.2.2.2.1
  apply
    psi_sqrt_cross_cell (c := (81 / 100 : ℝ)) (by norm_num only) (by norm_num only) ha1 ha hb hl hu
      (psi81_scaled_sqrt_lower hc.2.2.2.2.1) (psi81_scaled_sqrt_lower hc.2.2.2.2.2)
  · linarith only [hleft]
  · linarith only [hright]

/-- Check a chain of adjacent `81 / 100` cells by consuming it from left to right. -/
def psi81ChainCheck (start stop : ℕ) : List PsiSqrtCell → Bool
  | [] => decide (start = stop)
  | r :: rs => decide (start = r.a) && psi81CellCheck r && psi81ChainCheck r.b stop rs

/-- Each real point in the range of a checked chain lies in one of its cells. -/
theorem psi81_chain_covers {start stop : ℕ} {rows : List PsiSqrtCell}
    (hcheck : psi81ChainCheck start stop rows = true) {x : ℝ} (ha : (start : ℝ) ≤ x)
    (hb : x < stop) : ∃ r ∈ rows, (r.a : ℝ) ≤ x ∧ x < r.b := by
  induction rows generalizing start with
  | nil =>
    simp only [psi81ChainCheck, decide_eq_true_eq] at hcheck
    subst stop
    exact False.elim (by linarith only [ha, hb])
  | cons r rs
    ih =>
    simp only [psi81ChainCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    by_cases hxb : x < r.b
    · refine ⟨r, List.mem_cons_self, ?_, hxb⟩
      simpa only [hcheck.1.1] using ha
    · have hstart : (r.b : ℝ) ≤ x := le_of_not_gt hxb
      obtain ⟨q, hq, hqa, hqb⟩ := ih hcheck.2 hstart
      exact ⟨q, List.mem_cons_of_mem r hq, hqa, hqb⟩

/-- Every member of a checked `81 / 100` chain passes its own cell check. -/
theorem psi81_check_of_chain {start stop : ℕ} {rows : List PsiSqrtCell}
    (hcheck : psi81ChainCheck start stop rows = true) {r : PsiSqrtCell} (hr : r ∈ rows) :
    psi81CellCheck r = true := by
  induction rows generalizing start with
  | nil => exact False.elim (List.not_mem_nil hr)
  | cons q qs
    ih =>
    simp only [psi81ChainCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases List.mem_cons.mp hr with h | h
    · subst r
      exact hcheck.1.2
    · exact ih hcheck.2 h

/-- A checked `81 / 100` chain with certified psi endpoint bounds proves the error bound
throughout its half-open interval. The list is traversed without indexed access. -/
theorem psi81_chain_sound {start stop : ℕ} {rows : List PsiSqrtCell}
    (hcheck : psi81ChainCheck start stop rows = true)
    (hlo : ∀ r ∈ rows, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a)
    (hhi : ∀ r ∈ rows, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000) {x : ℝ}
    (ha : (start : ℝ) ≤ x) (hb : x < stop) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  obtain ⟨r, hr, hra, hrb⟩ := psi81_chain_covers hcheck ha hb
  exact psi81_cell_sound r (psi81_check_of_chain hcheck hr) (hlo r hr) (hhi r hr) hra hrb

end PseudoPrime.AnalyticNumberTheory.Arithmetic
