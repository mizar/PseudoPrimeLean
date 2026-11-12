/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtCrossCell

/-! # Sequential square-root error certificate cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A candidate half-open integer cell with thousandths-scaled lower and upper
psi bounds and lower bounds for the square-root envelope at both endpoints.
The checker verifies endpoint order and all rational crossing conditions. -/
structure PsiSqrtCell where
  a : ℕ
  b : ℕ
  lo : ℕ
  hi : ℕ
  ca : ℕ
  cb : ℕ
  deriving DecidableEq

/-- Check the endpoint order, crossing inequalities, and squared integer
certificates for both endpoint envelope bounds. This computation does not
assert the semantic psi bounds, which are supplied separately. -/
def psiSqrtCellCheck (r : PsiSqrtCell) : Bool :=
  decide
    (1 ≤ r.a ∧
      r.a < r.b ∧
      1000 * r.b ≤ r.lo + r.cb ∧
      r.hi ≤ 1000 * r.a + r.ca ∧ 25 * r.ca ^ 2 ≤ 16000000 * r.a ∧ 25 * r.cb ^ 2 ≤ 16000000 * r.b)

/-- A nonnegative integer whose square satisfies the displayed rational guard
provides a lower bound on four fifths of the square root. -/
theorem scaled_sqrt_lower {n c : ℕ} (hc : 25 * c ^ 2 ≤ 16000000 * n) :
    (c : ℝ) / 1000 ≤ (4 / 5 : ℝ) * Real.sqrt n := by
  have h : (25 : ℝ) * (c : ℝ) ^ 2 ≤ 16000000 * (n : ℝ) := by exact_mod_cast hc
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  nlinarith only [h, hs, hs0, hc0]

/-- A successful integer cell check and certified endpoint psi bounds imply
the square-root error bound throughout the half-open cell. The checker uses
only integer arithmetic; square-root soundness follows from squaring. -/
theorem psi_sqrt_cell_sound (r : PsiSqrtCell) (hcheck : psiSqrtCellCheck r = true)
    (hl : (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a)
    (hu : Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000) {x : ℝ} (ha : (r.a : ℝ) ≤ x)
    (hb : x < r.b) : |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  have hc :
    1 ≤ r.a ∧
      r.a < r.b ∧
      1000 * r.b ≤ r.lo + r.cb ∧
      r.hi ≤ 1000 * r.a + r.ca ∧ 25 * r.ca ^ 2 ≤ 16000000 * r.a ∧ 25 * r.cb ^ 2 ≤ 16000000 * r.b :=
    of_decide_eq_true hcheck
  have ha1 : (1 : ℝ) ≤ r.a := by exact_mod_cast hc.1
  have hleft : (1000 : ℝ) * r.b ≤ (r.lo : ℝ) + r.cb := by exact_mod_cast hc.2.2.1
  have hright : (r.hi : ℝ) ≤ 1000 * r.a + r.ca := by exact_mod_cast hc.2.2.2.1
  apply
    psi_four_fifths_cross_cell ha1 ha hb hl hu (scaled_sqrt_lower hc.2.2.2.2.1)
      (scaled_sqrt_lower hc.2.2.2.2.2)
  · linarith only [hleft]
  · linarith only [hright]

/-- Check adjacent half-open cells by consuming the list from left to right.
The empty suffix is accepted only when its start equals the final endpoint;
no list element is accessed by index. -/
def psiSqrtChainCheck (start stop : ℕ) : List PsiSqrtCell → Bool
  | [] => decide (start = stop)
  | r :: rs => decide (start = r.a) && psiSqrtCellCheck r && psiSqrtChainCheck r.b stop rs

/-- Every real point in a successfully checked half-open chain belongs to one
of its cells. The induction follows the list and the checked adjacency data. -/
theorem psi_sqrt_chain_covers {start stop : ℕ} {rows : List PsiSqrtCell}
    (hcheck : psiSqrtChainCheck start stop rows = true) {x : ℝ} (ha : (start : ℝ) ≤ x)
    (hb : x < stop) : ∃ r ∈ rows, (r.a : ℝ) ≤ x ∧ x < r.b := by
  induction rows generalizing start with
  | nil =>
    simp only [psiSqrtChainCheck, decide_eq_true_eq] at hcheck
    subst stop
    exact False.elim (by linarith only [ha, hb])
  | cons r rs
    ih =>
    simp only [psiSqrtChainCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    by_cases hxb : x < r.b
    · refine ⟨r, List.mem_cons_self, ?_, hxb⟩
      simpa only [hcheck.1.1] using ha
    · have hstart : (r.b : ℝ) ≤ x := le_of_not_gt hxb
      obtain ⟨q, hq, hqa, hqb⟩ := ih hcheck.2 hstart
      exact ⟨q, List.mem_cons_of_mem r hq, hqa, hqb⟩

/-- Each cell in a successfully checked chain passes its own arithmetic check.
The proof traverses the list and does not expose any specific certificate. -/
theorem psi_sqrt_check_of_chain {start stop : ℕ} {rows : List PsiSqrtCell}
    (hcheck : psiSqrtChainCheck start stop rows = true) {r : PsiSqrtCell} (hr : r ∈ rows) :
    psiSqrtCellCheck r = true := by
  induction rows generalizing start with
  | nil => exact False.elim (List.not_mem_nil hr)
  | cons q qs
    ih =>
    simp only [psiSqrtChainCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases List.mem_cons.mp hr with h | h
    · subst r
      exact hcheck.1.2
    · exact ih hcheck.2 h

/-- A checked chain and certified psi bounds for each of its cells establish
the square-root error bound on the entire half-open interval. The finite data
remain explicit inputs and may be consumed privately by a concrete certificate. -/
theorem psi_sqrt_chain_sound {start stop : ℕ} {rows : List PsiSqrtCell}
    (hcheck : psiSqrtChainCheck start stop rows = true)
    (hlo : ∀ r ∈ rows, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a)
    (hhi : ∀ r ∈ rows, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000) {x : ℝ}
    (ha : (start : ℝ) ≤ x) (hb : x < stop) : |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  obtain ⟨r, hr, hra, hrb⟩ := psi_sqrt_chain_covers hcheck ha hb
  exact psi_sqrt_cell_sound r (psi_sqrt_check_of_chain hcheck hr) (hlo r hr) (hhi r hr) hra hrb

end PseudoPrime.AnalyticNumberTheory.Arithmetic
