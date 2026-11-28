/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131TailBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131RoundedTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131RoundedTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131TailBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointTails
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Log

/-! # Logarithm and radius enclosures for the K131 tail partition -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The two log endpoints and the four scaled rational bounds for a cell. -/
private structure TailBox where
  left : ℕ
  right : ℕ
  logLower : ℕ
  logUpper : ℕ
  rootLower : ℕ
  logLogLower : ℕ

private def tailBoxes : List TailBox :=
  [⟨8000, 10000, 16661434192, 17108492345, 2833009678, 2839574968⟩,
    ⟨10000, 13000, 17108492344, 17633932347, 2913283429, 2869825020⟩,
    ⟨13000, 16000, 17633932346, 18049655619, 3010543934, 2893126605⟩,
    ⟨16000, 19000, 18049655618, 18393660237, 3089791077, 2912006052⟩,
    ⟨19000, 22000, 18393660236, 18687088322, 3156941770, 2927832821⟩,
    ⟨22000, 25000, 18687088321, 18942923113, 3215371876, 2941430411⟩,
    ⟨25000, 28000, 18942923112, 19169712512, 3267197861, 2953331560⟩,
    ⟨28000, 31000, 19169712511, 19373384368, 3313837992, 2963900184⟩,
    ⟨31000, 34000, 19373384367, 19558218683, 3356291093, 2973395591⟩,
    ⟨34000, 36500, 19558218682, 19700184206, 3395288270, 2980627986⟩,
    ⟨36500, 38500, 19700184205, 19806920005, 3425548184, 2986031371⟩,
    ⟨38500, 40000, 19806920004, 19883392431, 3448476365, 2989884832⟩,
    ⟨40000, 41000, 19883392430, 19932796437, 3464997901, 2992366437⟩,
    ⟨41000, 41500, 19932796436, 19957048209, 3475713484, 2993582374⟩,
    ⟨41500, 41900, 19957048208, 19976240093, 3480985742, 2994543571⟩,
    ⟨41900, 42100, 19976240092, 19985767413, 3485163664, 2995020390⟩,
    ⟨42100, 42250, 19985767412, 19992883236, 3487239549, 2995376372⟩,
    ⟨42250, 42325, 19992883235, 19996431677, 3488790805, 2995553841⟩,
    ⟨42325, 42370, 19996431676, 19998557723, 3489564627, 2995660157⟩,
    ⟨42370, 42400, 19998557722, 19999973832, 3490028343, 2995730965⟩,
    ⟨42400, 42410, 19999973831, 20000445646, 3490337248, 2995754555⟩]

private def tailBoxRadius (L : ℕ) : ℚ :=
  (519674 / 1000000 : ℚ) * L - 8

private def tailBoxGeometry (row : TailBox) : Prop :=
  let l := tailBoxRadius row.left
  let u := tailBoxRadius row.right
  let a := (row.logLower : ℚ) / 1000000000
  let b := (row.logUpper : ℚ) / 1000000000
  let r := (row.rootLower : ℚ) / 1000000000
  let c := (row.logLogLower : ℚ) / 1000000000
  0 < a ∧
    0 < r ∧
    r ^ 8 ≤ l ∧
    (a : ℝ) ≤ 2 * Real.log (l : ℝ) ∧
    2 * Real.log (u : ℝ) ≤ (b : ℝ) ∧ (c : ℝ) ≤ Real.log (2 * Real.log (u : ℝ))

private theorem tail_boxes_geometry (row : TailBox) (h : row ∈ tailBoxes) :
    tailBoxGeometry row := by
  simp only [tailBoxes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp only [tailBoxGeometry, tailBoxRadius]
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
    all_goals dyadic_interval [prec := 70]

private def tailBoxesJoin (a b : ℕ) : List TailBox → Bool
  | [] => a == b
  | row :: rows => (a == row.left) && tailBoxesJoin row.right b rows

private def tailBoxBudget (row : TailBox) : Prop :=
  let u := tailBoxRadius row.right
  let a := (row.logLower : ℚ) / 1000000000
  let b := (row.logUpper : ℚ) / 1000000000
  let r := (row.rootLower : ℚ) / 1000000000
  let c := (row.logLogLower : ℚ) / 1000000000
  27 / 10000 < k131TailBudget u b c (k131RoundedTailCap a b r)

private theorem tail_boxes_budget (row : TailBox) (h : row ∈ tailBoxes) : tailBoxBudget row := by
  simp only [tailBoxes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp only [tailBoxBudget, tailBoxRadius]
    decide +kernel

private theorem tail_cover {L : ℝ} {a b : ℕ} {rows : List TailBox}
    (hd : tailBoxesJoin a b rows = true) (ha : (a : ℝ) ≤ L) (hb : L ≤ (b : ℝ)) :
    a = b ∧ L = a ∨ ∃ row ∈ rows, L ∈ Set.Icc (row.left : ℝ) (row.right : ℝ) := by
  induction rows generalizing a with
  | nil =>
    have hab : a = b := beq_iff_eq.mp hd
    exact Or.inl ⟨hab, le_antisymm (hab ▸ hb) ha⟩
  | cons row rows
    ih =>
    have hd' : (a == row.left) = true ∧ tailBoxesJoin row.right b rows = true :=
      Bool.and_eq_true_iff.mp hd
    have hl : a = row.left := beq_iff_eq.mp hd'.1
    have hleft : (row.left : ℝ) ≤ L := hl ▸ ha
    by_cases hright : L ≤ (row.right : ℝ)
    · exact Or.inr ⟨row, List.mem_cons_self, hleft, hright⟩
    · rcases ih hd'.2 (le_of_not_ge hright) with he | ⟨r, hr, hL⟩
      · exact False.elim (hright he.2.le)
      · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, hL⟩

/-- Every logarithm in [8000, 42410] belongs to a partition cell with
certified radius and logarithm enclosures, and a strict rational budget. -/
public theorem k131_tail_partition_enclosure {L : ℝ} (hL : L ∈ Set.Icc (8000 : ℝ) 42410) :
    ∃ lo hi : ℕ,
      ∃ a b r c : ℚ,
        L ∈ Set.Icc (lo : ℝ) (hi : ℝ) ∧
          let l := (519674 / 1000000 : ℚ) * lo - 8
          let u := (519674 / 1000000 : ℚ) * hi - 8
          0 < a ∧
            0 < r ∧
            r ^ 8 ≤ l ∧
            (a : ℝ) ≤ 2 * Real.log (l : ℝ) ∧
            2 * Real.log (u : ℝ) ≤ (b : ℝ) ∧
            (c : ℝ) ≤ Real.log (2 * Real.log (u : ℝ)) ∧
            27 / 10000 < k131TailBudget u b c (k131RoundedTailCap a b r) := by
  rcases tail_cover (a := 8000) (b := 42410) (rows := tailBoxes) (by decide +kernel) hL.1 hL.2 with
    he | ⟨row, hr, hmem⟩
  · exact False.elim ((by decide : (8000 : ℕ) ≠ 42410) he.1)
  · obtain ⟨ha, hpos, hroot, hl, hu, hc⟩ := tail_boxes_geometry row hr
    exact
      ⟨row.left, row.right, _, _, _, _, hmem, ha, hpos, hroot, hl, hu, hc, tail_boxes_budget row hr⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
