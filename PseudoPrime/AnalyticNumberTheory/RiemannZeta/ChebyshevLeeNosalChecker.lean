/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalCrossCell

/-! # Rational cell checks for Lee–Nosal error bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Rational data for one half-open Lee–Nosal interval. Fields `a` and `b` are
integer endpoints, while `lo`, `hi`, `ca`, and `cb` are nonnegative thousandths
for the lower value, upper value, and two envelope bounds. The checker and its
soundness theorem supply the required order and cross-inequality invariants. -/
structure LeeNosalCell where
  a : ℕ
  b : ℕ
  lo : ℕ
  hi : ℕ
  ca : ℕ
  cb : ℕ
  deriving DecidableEq

/-- Check the endpoint order and the two cross inequalities for a thousandths-scaled
cell. The check does not certify the psi, theta, or envelope bounds themselves;
those remain explicit inputs to the soundness theorem. -/
def leeNosalCellCheck (r : LeeNosalCell) : Bool :=
  decide (3 ≤ r.a ∧ r.a < r.b ∧ 1000 * r.b ≤ r.lo + r.cb ∧ r.hi ≤ 1000 * r.a + r.ca)

/-- If the arithmetic check succeeds and the four scaled numerical endpoint bounds
are valid for a monotone floor-invariant function, the Lee–Nosal inequality holds
throughout the cell. Logarithm and prefix certificates are supplied separately. -/
theorem lee_nosal_cell_check_sound (r : LeeNosalCell) {f : ℝ → ℝ} (hf : Monotone f)
    (hfloor : ∀ t : ℝ, f t = f ⌊t⌋₊) (hcheck : leeNosalCellCheck r = true)
    (hl : (r.lo : ℝ) / 1000 ≤ f r.a) (hu : f (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000)
    (hca :
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a * (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)))
    (hcb :
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b * (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)))
    {x : ℝ} (ha : (r.a : ℝ) ≤ x) (hb : x < r.b) :
    |f x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  have h : 3 ≤ r.a ∧ r.a < r.b ∧ 1000 * r.b ≤ r.lo + r.cb ∧ r.hi ≤ 1000 * r.a + r.ca :=
    of_decide_eq_true hcheck
  have ha0 : Real.exp 1 ≤ (r.a : ℝ) := by
    have h3 : (3 : ℝ) ≤ r.a := by exact_mod_cast h.1
    linarith only [Real.exp_one_lt_three, h3]
  have hc1 : (1000 : ℝ) * r.b ≤ (r.lo : ℝ) + r.cb := by exact_mod_cast h.2.2.1
  have hc2 : (r.hi : ℝ) ≤ 1000 * r.a + r.ca := by exact_mod_cast h.2.2.2
  apply lee_nosal_cross_cell hf hfloor ha0 ha hb hl hu hca hcb _ _
  · linarith only [hc1]
  · linarith only [hc2]

/-- Check a list of cells from `start` to `stop`. Adjacent endpoints must agree,
each cell must pass its arithmetic check, and the final endpoint must equal `stop`.
This checker does not contain or certify any particular numerical table. -/
def leeNosalChainCheck (start stop : ℕ) : List LeeNosalCell → Bool
  | [] => decide (start = stop)
  | r :: rs => decide (start = r.a) && leeNosalCellCheck r && leeNosalChainCheck r.b stop rs

/-- A successful chain check covers every real point of the half-open interval
`[start, stop)` by one of its cells. Endpoint adjacency and the final endpoint
are verified by the checker rather than assumed from a candidate list. -/
theorem lee_nosal_chain_covers {start stop : ℕ} {rows : List LeeNosalCell}
    (hcheck : leeNosalChainCheck start stop rows = true) {x : ℝ} (ha : (start : ℝ) ≤ x)
    (hb : x < stop) : ∃ r ∈ rows, (r.a : ℝ) ≤ x ∧ x < r.b := by
  induction rows generalizing start with
  | nil =>
    simp only [leeNosalChainCheck, decide_eq_true_eq] at hcheck
    subst stop
    exact False.elim (by linarith only [ha, hb])
  | cons r rs
    ih =>
    simp only [leeNosalChainCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    by_cases hxb : x < r.b
    · refine ⟨r, List.mem_cons_self, ?_, hxb⟩
      simpa only [hcheck.1.1] using ha
    · have hstart : (r.b : ℝ) ≤ x := le_of_not_gt hxb
      obtain ⟨q, hq, hqa, hqb⟩ := ih hcheck.2 hstart
      exact ⟨q, List.mem_cons_of_mem r hq, hqa, hqb⟩

/-- Every cell occurring in a successfully checked chain passes its individual
arithmetic check. This separates list coverage from numerical soundness. -/
theorem lee_nosal_check_of_chain {start stop : ℕ} {rows : List LeeNosalCell}
    (hcheck : leeNosalChainCheck start stop rows = true) {r : LeeNosalCell} (hr : r ∈ rows) :
    leeNosalCellCheck r = true := by
  induction rows generalizing start with
  | nil => exact False.elim (List.not_mem_nil hr)
  | cons q qs
    ih =>
    simp only [leeNosalChainCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases List.mem_cons.mp hr with h | h
    · subst r
      exact hcheck.1.2
    · exact ih hcheck.2 h

/-- A checked chain and independently verified endpoint bounds for every member
prove the Lee–Nosal error inequality on the entire half-open interval. The four
families of semantic bounds remain explicit, so numerical candidates alone do not
establish the result. -/
theorem lee_nosal_chain_sound {start stop : ℕ} {rows : List LeeNosalCell} {f : ℝ → ℝ}
    (hf : Monotone f) (hfloor : ∀ t : ℝ, f t = f ⌊t⌋₊)
    (hcheck : leeNosalChainCheck start stop rows = true)
    (hlo : ∀ r ∈ rows, (r.lo : ℝ) / 1000 ≤ f r.a)
    (hhi : ∀ r ∈ rows, f (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000)
    (hca :
      ∀ r ∈ rows,
        (r.ca : ℝ) / 1000 ≤
          Real.sqrt r.a * (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)))
    (hcb :
      ∀ r ∈ rows,
        (r.cb : ℝ) / 1000 ≤
          Real.sqrt r.b * (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)))
    {x : ℝ} (ha : (start : ℝ) ≤ x) (hb : x < stop) :
    |f x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  obtain ⟨r, hr, hax, hxb⟩ := lee_nosal_chain_covers hcheck ha hb
  exact
    lee_nosal_cell_check_sound r hf hfloor (lee_nosal_check_of_chain hcheck hr) (hlo r hr)
      (hhi r hr) (hca r hr) (hcb r hr) hax hxb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
