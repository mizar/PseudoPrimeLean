/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleCells

/-! # Finite cover of the K186 residual interval -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational endpoints, residual lower bounds, and upper curvature
bounds of the twenty finite K186 cells. -/
private def k186Cells : List GaussianResidualCell :=
  [⟨30, 271 / 8, 1300658689 / 200000000, 8475235193 / 1000000000, 1628336647 / 1000000000⟩,
    ⟨271 / 8, 573 / 16, 8475235193 / 1000000000, 8147793981 / 1000000000, 16557975141 / 1000000000⟩,
    ⟨573 / 16, 151 / 4, 8147793981 / 1000000000, 7822676527 / 1000000000, 100125413 / 10000000⟩,
    ⟨151 / 4, 1239 / 32, 7822676527 / 1000000000, 7457300537 / 1000000000, 282709021 / 125000000⟩,
    ⟨1239 / 32, 635 / 16, 7457300537 / 1000000000, 7290545341 / 1000000000,
      6025901189 / 1000000000⟩,
    ⟨635 / 16, 333 / 8, 7290545341 / 1000000000, 7983205669 / 1000000000, 2362679123 / 1000000000⟩,
    ⟨333 / 8, 1363 / 32, 7983205669 / 1000000000, 7582737401 / 1000000000, 6869715957 / 1000000000⟩,
    ⟨1363 / 32, 697 / 16, 7582737401 / 1000000000, 8057347463 / 1000000000,
      13544019257 / 500000000⟩,
    ⟨697 / 16, 1425 / 32, 8057347463 / 1000000000, 746451793 / 62500000, 24384585687 / 1000000000⟩,
    ⟨1425 / 32, 91 / 2, 746451793 / 62500000, 9377930133 / 500000000, 4702122591 / 1000000000⟩,
    ⟨91 / 2, 759 / 16, 9377930133 / 500000000, 26287913833 / 1000000000, 2382220037 / 250000000⟩,
    ⟨759 / 16, 1549 / 32, 26287913833 / 1000000000, 31140692547 / 1000000000,
      37933781607 / 500000000⟩,
    ⟨1549 / 32, 395 / 8, 31140692547 / 1000000000, 13516450501 / 250000000,
      36153811909 / 200000000⟩,
    ⟨395 / 8, 1611 / 32, 13516450501 / 250000000, 22427070563 / 200000000,
      199864072313 / 1000000000⟩,
    ⟨1611 / 32, 821 / 16, 22427070563 / 200000000, 43508906053 / 200000000, 2081560211 / 15625000⟩,
    ⟨821 / 16, 213 / 4, 43508906053 / 200000000, 612320798507 / 1000000000,
      146655101471 / 1000000000⟩,
    ⟨213 / 4, 883 / 16, 612320798507 / 1000000000, 1495212496081 / 1000000000,
      54137772713 / 125000000⟩,
    ⟨883 / 16, 457 / 8, 1495212496081 / 1000000000, 1899335159301 / 500000000,
      1694727035807 / 1000000000⟩,
    ⟨457 / 8, 945 / 16, 1899335159301 / 500000000, 1250632389111 / 125000000,
      3621261921333 / 1000000000⟩,
    ⟨945 / 16, 61, 1250632389111 / 125000000, 26475625976097 / 1000000000,
      7095934361887 / 1000000000⟩]

/-- Check that consecutive cells partition an interval and that their
rational reserves are positive. -/
private def k186ChainOK (a b : ℚ) : List GaussianResidualCell → Bool
  | [] => decide (a = b)
  | c :: cs =>
    decide (c.left = a) && decide (a ≤ c.right) && decide (0 ≤ c.upperCurvature) &&
      decide (0 < c.reserve) &&
      k186ChainOK c.right b cs

/-- A passing chain and an analytic proof for each row ensure positivity
throughout its half-open interval. -/
private theorem k186_chain_pos {f f' f'' : ℝ → ℝ} {a b : ℚ} (cs : List GaussianResidualCell)
    (h : k186ChainOK a b cs = true) (hb : ∀ c ∈ cs, c.AnalyticBounds f f' f'') {x : ℝ}
    (hx : x ∈ Set.Ico (a : ℝ) (b : ℝ)) : 0 < f x := by
  induction cs generalizing a with
  | nil =>
    have he : a = b := of_decide_eq_true h
    exact False.elim (not_lt_of_ge (he ▸ hx.1) hx.2)
  | cons c cs ih =>
    simp only [k186ChainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hl, _⟩, hm⟩, hp⟩, hc⟩ := h
    by_cases hx' : x ≤ (c.right : ℝ)
    · exact
        (Rat.cast_pos.mpr hp).trans_le
          (GaussianResidualCell.reserve_le (hb c (List.mem_cons_self ..)) hm ⟨hl.symm ▸ hx.1, hx'⟩)
    · exact ih hc (fun d hd ↦ hb d (List.mem_cons_of_mem c hd)) ⟨le_of_lt (lt_of_not_ge hx'), hx.2⟩

/-- Access one finite check without putting the coefficient or cell rows
in the interface of the final witness theorems. -/
def k186FiniteCell (i : Fin 20) : GaussianResidualCell :=
  k186Cells[i.val]'(by simpa only [k186Cells, List.length_cons, List.length_nil] using i.isLt)

/-- Verified cell bounds imply positivity throughout the complete finite
logarithm range, including the right endpoint. -/
theorem k186_finite_pos_of_cells {f f' f'' : ℝ → ℝ}
    (hb : ∀ i : Fin 20, (k186FiniteCell i).AnalyticBounds f f' f'') {x : ℝ}
    (hx : x ∈ Set.Icc (30 : ℝ) 61) : 0 < f x := by
  rcases lt_or_eq_of_le hx.2 with hlt | he
  · have hcell : ∀ c ∈ k186Cells, c.AnalyticBounds f f' f'' := by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
      exact hb ⟨i, by simpa only [k186Cells, List.length_cons, List.length_nil] using hi⟩
    apply k186_chain_pos (a := 30) (b := 61) k186Cells (by decide +kernel) hcell
    exact ⟨by simpa only [Rat.cast_ofNat] using hx.1, by simpa only [Rat.cast_ofNat] using hlt⟩
  · subst x
    have h := (hb 19).2.2.2.2.2
    exact
      (show (0 : ℝ) < ((k186FiniteCell 19).lowerRight : ℝ) from
            Rat.cast_pos.mpr (by decide +kernel)).trans_le
        h

end PseudoPrime.PrimeTestBounds.MillerRabin
