/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRationalGridRH
import Mathlib.Data.Fin.VecNotation

/-! # Rational phase certificate at log height 13.81 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Rational lower endpoints of the 29 ordinate brackets. -/
def phase1381Lower : Fin 29 → ℚ :=
  ![(14473 : ℚ) / 1024, (21526 : ℚ) / 1024, (25611 : ℚ) / 1024, (31155 : ℚ) / 1024,
    (33725 : ℚ) / 1024, (38488 : ℚ) / 1024, (41900 : ℚ) / 1024, (44366 : ℚ) / 1024,
    (49157 : ℚ) / 1024, (50968 : ℚ) / 1024, (54241 : ℚ) / 1024, (57800 : ℚ) / 1024,
    (60771 : ℚ) / 1024, (62291 : ℚ) / 1024, (66675 : ℚ) / 1024, (68689 : ℚ) / 1024,
    (71215 : ℚ) / 1024, (73796 : ℚ) / 1024, (77521 : ℚ) / 1024, (78996 : ℚ) / 1024,
    (81241 : ℚ) / 1024, (84900 : ℚ) / 1024, (86769 : ℚ) / 1024, (89523 : ℚ) / 1024,
    (90940 : ℚ) / 1024, (94711 : ℚ) / 1024, (96922 : ℚ) / 1024, (98171 : ℚ) / 1024,
    (101203 : ℚ) / 1024]

/-- Rational upper endpoints of the 29 ordinate brackets. -/
def phase1381Upper (i : Fin 29) : ℚ :=
  phase1381Lower i + 1 / 100

/-- Lower enclosures for the five ordinate samples at log height 13.81. -/
def phase1381ValueLower : Fin 29 → ℚ :=
  ![(606 : ℚ) / 10000, (916 : ℚ) / 10000, (-126 : ℚ) / 10000, (-469 : ℚ) / 10000, (316 : ℚ) / 10000,
    (-401 : ℚ) / 10000, (-191 : ℚ) / 10000, (456 : ℚ) / 10000, (-92 : ℚ) / 10000, (187 : ℚ) / 10000,
    (121 : ℚ) / 10000, (138 : ℚ) / 10000, (76 : ℚ) / 10000, (-326 : ℚ) / 10000, (199 : ℚ) / 10000,
    (76 : ℚ) / 10000, (-225 : ℚ) / 10000, (132 : ℚ) / 10000, (132 : ℚ) / 10000, (-128 : ℚ) / 10000,
    (147 : ℚ) / 10000, (238 : ℚ) / 10000, (233 : ℚ) / 10000, (187 : ℚ) / 10000, (211 : ℚ) / 10000,
    (198 : ℚ) / 10000, (46 : ℚ) / 10000, (-210 : ℚ) / 10000, (198 : ℚ) / 10000]

/-- Upper enclosures for the five ordinate samples at log height 13.81. -/
def phase1381ValueUpper : Fin 29 → ℚ :=
  ![(779 : ℚ) / 10000, (944 : ℚ) / 10000, (-13 : ℚ) / 10000, (-397 : ℚ) / 10000, (388 : ℚ) / 10000,
    (-346 : ℚ) / 10000, (-124 : ℚ) / 10000, (463 : ℚ) / 10000, (-33 : ℚ) / 10000, (237 : ℚ) / 10000,
    (172 : ℚ) / 10000, (184 : ℚ) / 10000, (123 : ℚ) / 10000, (-313 : ℚ) / 10000, (232 : ℚ) / 10000,
    (118 : ℚ) / 10000, (-195 : ℚ) / 10000, (167 : ℚ) / 10000, (166 : ℚ) / 10000, (-93 : ℚ) / 10000,
    (176 : ℚ) / 10000, (243 : ℚ) / 10000, (238 : ℚ) / 10000, (206 : ℚ) / 10000, (222 : ℚ) / 10000,
    (211 : ℚ) / 10000, (76 : ℚ) / 10000, (-203 : ℚ) / 10000, (204 : ℚ) / 10000]

/-- All 145 rounded rational sample checks succeed at log height 13.81. -/
theorem phase1381_node_checks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rationalOrdinateNodeCheck (1381 / 100)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (phase1381ValueLower i) (phase1381ValueUpper i) (10 ^ 12) 16 12 =
          true := by
  intro i k hk
  fin_cases i <;> interval_cases k <;> decide +kernel

/-- The summed rational ordinate interpolation budget lies within 51/100. -/
theorem phase1381_budget_check :
    rationalOrdinateBudgetCheck (51 / 100) 21 phase1381Lower phase1381Upper phase1381ValueLower
        phase1381ValueUpper =
      true := by
  decide +kernel

/-- The rational ordinate brackets lie in the positive interval ending at 100. -/
theorem phase1381_brackets_rational :
    ∀ i : Fin 29, 0 < phase1381Lower i ∧ phase1381Upper i ≤ 100 := by decide +kernel

/-- Every lower ordinate endpoint is positive. -/
theorem phase1381_lower_pos : ∀ i, (0 : ℝ) < phase1381Lower i := by
  intro i
  have h := (Rat.cast_lt (K := ℝ)).mpr (phase1381_brackets_rational i).1
  simpa only [Rat.cast_zero] using h

/-- Every upper ordinate endpoint is at most 100. -/
theorem phase1381_upper_le : ∀ i, (phase1381Upper i : ℝ) ≤ 100 := by
  intro i
  have h := (Rat.cast_le (K := ℝ)).mpr (phase1381_brackets_rational i).2
  simpa only [Rat.cast_ofNat] using h

/-- Each ordinate bracket is nondegenerate. -/
theorem phase1381_lower_lt_upper : ∀ i, (phase1381Lower i : ℝ) < phase1381Upper i := by
  intro i
  simp only [phase1381Upper, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
  linarith only

/-- The five sample ordinates in each bracket lie in the interval (0,100]. -/
theorem phase1381_samples_in_range :
    ∀ i (k : ℕ),
      k ≤ 4 →
        let q := phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4
        (0 : ℝ) < q ∧ (q : ℝ) ≤ 100 := by
  intro i k hk
  have ha := phase1381_lower_pos i
  have hb := phase1381_upper_le i
  have hab := phase1381_lower_lt_upper i
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk4 : (k : ℝ) ≤ 4 := by exact (Nat.cast_le).2 hk
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_ofNat]
  have h1 := mul_nonneg hk0 (sub_nonneg.mpr hab.le)
  have h2 := mul_nonneg (sub_nonneg.mpr hk4) (sub_nonneg.mpr hab.le)
  constructor <;> nlinarith only [ha, hb, h1, h2]

/-- Every ordinate tuple within the 29 brackets has signed zero head at
most 51/100 in absolute value at log height 13.81. The proof checks all
145 sample values and the ordinate interpolation budget. -/
theorem phase1381_head_bound (g : Fin 29 → ℝ)
    (hg : ∀ i, g i ∈ Set.Icc (phase1381Lower i : ℝ) (phase1381Upper i : ℝ)) :
    |zeroHeadPhase g (1381 / 100)| ≤ (51 / 100 : ℝ) := by
  have hnodes :
    ∀ i (k : ℕ),
      k ≤ 4 →
        (phase1381ValueLower i : ℝ) ≤
            ordinateTerm (1381 / 100)
              ((phase1381Lower i : ℝ) +
                (k : ℝ) * ((phase1381Upper i : ℝ) - (phase1381Lower i : ℝ)) / 4) ∧
          ordinateTerm (1381 / 100)
              ((phase1381Lower i : ℝ) +
                (k : ℝ) * ((phase1381Upper i : ℝ) - (phase1381Lower i : ℝ)) / 4) ≤
            (phase1381ValueUpper i : ℝ) := by
    intro i k hk
    have hq := phase1381_samples_in_range i k hk
    have h :=
      rationalOrdinateNodeCheck_100 (1381 / 100)
        (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
        (phase1381ValueLower i) (phase1381ValueUpper i) hq.1 hq.2 (by norm_num only)
        (phase1381_node_checks i k hk)
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_natCast] at h
    exact h
  have h :=
    zeroHeadPhase_four_cells g (fun i ↦ (phase1381Lower i : ℝ)) (fun i ↦ (phase1381Upper i : ℝ))
      (fun i ↦ (phase1381ValueLower i : ℝ)) (fun i ↦ (phase1381ValueUpper i : ℝ)) (1381 / 100) 21
      phase1381_lower_pos phase1381_lower_lt_upper hg (by norm_num only) hnodes
  have hb :=
    rationalOrdinateBudgetCheck_sound (51 / 100) 21 phase1381Lower phase1381Upper
      phase1381ValueLower phase1381ValueUpper phase1381_budget_check
  norm_num only [Rat.cast_ofNat, Rat.cast_div, ordinateCellError] at hb
  apply abs_le.mpr
  constructor <;> linarith only [h.1, h.2, hb.1, hb.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
