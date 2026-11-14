/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
public import Mathlib.Data.Fin.VecNotation

/-! # Rational phase certificate at log height 13.814 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Lower enclosures for the five ordinate samples at log height 13.814. -/
def phase13814ValueLower : Fin 29 → ℚ :=
  ![(677 : ℚ) / 10000, (934 : ℚ) / 10000, (-47 : ℚ) / 10000, (-409 : ℚ) / 10000, (246 : ℚ) / 10000,
    (-449 : ℚ) / 10000, (-115 : ℚ) / 10000, (452 : ℚ) / 10000, (-168 : ℚ) / 10000,
    (114 : ℚ) / 10000, (44 : ℚ) / 10000, (207 : ℚ) / 10000, (-3 : ℚ) / 10000, (-330 : ℚ) / 10000,
    (252 : ℚ) / 10000, (-3 : ℚ) / 10000, (-167 : ℚ) / 10000, (58 : ℚ) / 10000, (59 : ℚ) / 10000,
    (-191 : ℚ) / 10000, (76 : ℚ) / 10000, (225 : ℚ) / 10000, (213 : ℚ) / 10000, (220 : ℚ) / 10000,
    (221 : ℚ) / 10000, (155 : ℚ) / 10000, (118 : ℚ) / 10000, (-207 : ℚ) / 10000, (187 : ℚ) / 10000]

/-- Upper enclosures for the five ordinate samples at log height 13.814. -/
def phase13814ValueUpper : Fin 29 → ℚ :=
  ![(844 : ℚ) / 10000, (951 : ℚ) / 10000, (66 : ℚ) / 10000, (-331 : ℚ) / 10000, (323 : ℚ) / 10000,
    (-403 : ℚ) / 10000, (-45 : ℚ) / 10000, (463 : ℚ) / 10000, (-111 : ℚ) / 10000, (168 : ℚ) / 10000,
    (98 : ℚ) / 10000, (247 : ℚ) / 10000, (46 : ℚ) / 10000, (-326 : ℚ) / 10000, (277 : ℚ) / 10000,
    (41 : ℚ) / 10000, (-130 : ℚ) / 10000, (97 : ℚ) / 10000, (96 : ℚ) / 10000, (-162 : ℚ) / 10000,
    (111 : ℚ) / 10000, (237 : ℚ) / 10000, (227 : ℚ) / 10000, (229 : ℚ) / 10000, (227 : ℚ) / 10000,
    (177 : ℚ) / 10000, (144 : ℚ) / 10000, (-197 : ℚ) / 10000, (198 : ℚ) / 10000]

/-- All 145 rounded rational sample checks succeed at log height 13.814. -/
private theorem phase13814_node_checks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rationalOrdinateNodeCheck (6907 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (phase13814ValueLower i) (phase13814ValueUpper i) (10 ^ 12) 16 12 =
          true := by
  intro i k hk
  fin_cases i <;> interval_cases k <;> decide +kernel

/-- The summed rational ordinate interpolation budget lies within 51/100. -/
private theorem phase13814_budget_check :
    rationalOrdinateBudgetCheck (51 / 100) 21 phase1381Lower phase1381Upper phase13814ValueLower
        phase13814ValueUpper =
      true := by
  decide +kernel

/-- Every ordinate tuple within the 29 brackets has signed zero head at
most 51/100 in absolute value at log height 13.814. The proof checks all
145 sample values and the ordinate interpolation budget. -/
private theorem phase13814_head_bound (g : Fin 29 → ℝ)
    (hg : ∀ i, g i ∈ Set.Icc (phase1381Lower i : ℝ) (phase1381Upper i : ℝ)) :
    |zeroHeadPhase g (6907 / 500)| ≤ (51 / 100 : ℝ) := by
  have hnodes :
    ∀ i (k : ℕ),
      k ≤ 4 →
        (phase13814ValueLower i : ℝ) ≤
            ordinateTerm (6907 / 500)
              ((phase1381Lower i : ℝ) +
                (k : ℝ) * ((phase1381Upper i : ℝ) - (phase1381Lower i : ℝ)) / 4) ∧
          ordinateTerm (6907 / 500)
              ((phase1381Lower i : ℝ) +
                (k : ℝ) * ((phase1381Upper i : ℝ) - (phase1381Lower i : ℝ)) / 4) ≤
            (phase13814ValueUpper i : ℝ) := by
    intro i k hk
    have hq := phase1381_samples_in_range i k hk
    have h :=
      rationalOrdinateNodeCheck_100 (6907 / 500)
        (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
        (phase13814ValueLower i) (phase13814ValueUpper i) hq.1 hq.2 (by norm_num only)
        (phase13814_node_checks i k hk)
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_natCast] at h
    exact h
  have h :=
    zeroHeadPhase_four_cells g (fun i ↦ (phase1381Lower i : ℝ)) (fun i ↦ (phase1381Upper i : ℝ))
      (fun i ↦ (phase13814ValueLower i : ℝ)) (fun i ↦ (phase13814ValueUpper i : ℝ)) (6907 / 500) 21
      phase1381_lower_pos phase1381_lower_lt_upper hg (by norm_num only) hnodes
  have hb :=
    rationalOrdinateBudgetCheck_sound (51 / 100) 21 phase1381Lower phase1381Upper
      phase13814ValueLower phase13814ValueUpper phase13814_budget_check
  norm_num only [Rat.cast_ofNat, Rat.cast_div, ordinateCellError] at hb
  apply abs_le.mpr
  constructor <;> linarith only [h.1, h.2, hb.1, hb.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
