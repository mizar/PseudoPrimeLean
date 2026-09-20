/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement
import PseudoPrime.AnalyticNumberTheory.Arithmetic.OddPrimeCutoff
import PseudoPrime.PseudoSquare.CharacterBound
import PseudoPrime.PseudoSquare.Computation.SmallN

/-!
# The Robin-free boxed bound, conditional on `Arithmetic.ElementaryOmegaStatement`

This file proves the envelope comparisons for the Robin-free bound.
The target estimate is:

```
Q_{≠1}(B) ≤ Q_{-1}(B) ≤ (log(4B) + (24/5) * loglog(4B) + 3)^2      (B ≥ 750)
```

conditional only on `PseudoPrime.LLS.llsTheorem11S1Character` and the elementary, fully
combinatorial/calculus
`PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement` from
`AnalyticNumberTheory/Arithmetic/ElementaryOmegaStatement.lean`.

The elementary input is `ω(4n) ≤ (7/5)·log(4n)/loglog(4n)` for odd `n ≥ 750`.
Together with the nonnegative LLS auxiliary term, it bounds the correction by
`(24/5)·loglog(4n) + 3`. The elementary statement is discharged
unconditionally in `ElementaryOmegaFiniteCertificates.lean`; this file intentionally keeps it as
an interface so the envelope proof remains independent of certificate generation.
-/

namespace PseudoPrime.PseudoSquare

/-- The elementary bound gives the simplified upper bound for the LLS correction term, with
coefficient `2 + 2·(7/5) = 24/5`, for odd `n ≥ 750`. -/
theorem llsCorrectionTerm_le_elementary
    (hElem : AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement) {n : ℕ} (hn : Odd n)
    (hn750 : 750 ≤ n) :
    LLS.llsCorrectionTerm (NumberTheory.characterModulus n) ≤
      (24 / 5 : ℝ) * Real.log (Real.log (NumberTheory.characterModulus n)) + 3 := by
  have hq : 3000 ≤ NumberTheory.characterModulus n := by
    unfold NumberTheory.characterModulus; omega
  have hy := (AnalyticNumberTheory.Arithmetic.log_log_pos_of_le hq).2
  have hcount := AnalyticNumberTheory.Arithmetic.elementary_prime_count_term_le hElem hn hn750
  have haux := LLS.llsAuxiliaryTerm_nonneg (NumberTheory.characterModulus n)
  have hCeq : (2 : ℝ) * AnalyticNumberTheory.Arithmetic.elementaryOmegaConstant = 14 / 5 := by
    unfold AnalyticNumberTheory.Arithmetic.elementaryOmegaConstant; norm_num only
  unfold LLS.llsCorrectionTerm
  apply max_le
  · nlinarith [hCeq, hy]
  · nlinarith [hCeq, hcount]

/-- The squared real cutoff `(log(4B) + (24/5)·loglog(4B) + 3)^2`. -/
noncomputable def elementaryRadius (B : ℕ) : ℝ :=
  (Real.log (4 * B) + (24 / 5 : ℝ) * Real.log (Real.log (4 * B)) + 3) ^ 2

/-- For `B ≥ 3`, `elementaryRadius B` already exceeds `31` on its own: `Real.log (4 * B) > 2`
(from `4 * B ≥ 12 > exp 2`) and `Real.log (Real.log (4 * B)) > Real.log 2 > 0.6` (applying `log`
monotonicity again), so the squared base already exceeds `7.88 ^ 2 > 31` with substantial room to
spare. This makes the `max 31 (...)` safety margin in `elementaryUpperBound` unnecessary for
`B ≥ 3`, as expressed by `elementaryUpperBound_eq_of_le`. -/
theorem thirtyOne_lt_elementaryRadius {B : ℕ} (hB : 3 ≤ B) : (31 : ℝ) < elementaryRadius B := by
  have h12B : (12 : ℝ) ≤ 4 * B := by
    have : (3 : ℝ) ≤ B := by exact_mod_cast hB
    linarith only [this]
  have hexp2 : Real.exp 2 < 12 := by
    have h1 := Real.exp_one_lt_d9
    have h1pos := Real.exp_pos 1
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num only
    rw [h2]
    nlinarith only [h1, h1pos, h2]
  have hlog12 : (2 : ℝ) < Real.log 12 := (Real.lt_log_iff_exp_lt (by norm_num only)).mpr hexp2
  have hlog4B : (2 : ℝ) < Real.log (4 * B) :=
    hlog12.trans_le (Real.log_le_log (by norm_num only) h12B)
  have hloglog4B : Real.log 2 < Real.log (Real.log (4 * B)) :=
    Real.log_lt_log (by norm_num only) hlog4B
  have hbase : (7.88 : ℝ) < Real.log (4 * B) + (24 / 5 : ℝ) * Real.log (Real.log (4 * B)) + 3 := by
    nlinarith only [Real.log_two_gt_d9, hlog4B, hloglog4B]
  unfold elementaryRadius
  nlinarith only [hbase]

/-- The natural-number envelope: the maximum of `31` and the greatest odd prime below the radius. -/
noncomputable def elementaryUpperBound (B : ℕ) : ℕ :=
  max 31 (AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE (elementaryRadius B))

/-- The exceptional finite-range bound `31` is always included in the elementary envelope. -/
theorem thirty_one_le_elementaryUpperBound (B : ℕ) : 31 ≤ elementaryUpperBound B := by
  unfold elementaryUpperBound
  exact le_max_left _ _

/-- For `B ≥ 3`, the `max 31 (...)` safety margin in `elementaryUpperBound` is never active:
`Arithmetic.greatestOddPrimeLE (elementaryRadius B)` already dominates `31` on its own, since `31`
is itself
an odd prime not exceeding `elementaryRadius B` (`thirtyOne_lt_elementaryRadius`). -/
theorem thirtyOne_le_greatestOddPrimeLE_elementaryRadius {B : ℕ} (hB : 3 ≤ B) :
    31 ≤ AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE (elementaryRadius B) :=
  AnalyticNumberTheory.Arithmetic.le_greatestOddPrimeLE (by decide) (by decide)
    (thirtyOne_lt_elementaryRadius hB).le

/-- For `B ≥ 3`, `elementaryUpperBound B` is exactly `Arithmetic.greatestOddPrimeLE
(elementaryRadius B)` —
the `max 31 (...)` wrapper is redundant, since `31 ≤ Arithmetic.greatestOddPrimeLE
(elementaryRadius B)`
already. -/
theorem elementaryUpperBound_eq_of_le {B : ℕ} (hB : 3 ≤ B) :
    elementaryUpperBound B =
      AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE (elementaryRadius B) := by
  unfold elementaryUpperBound
  exact max_eq_right (thirtyOne_le_greatestOddPrimeLE_elementaryRadius hB)

/-- Every odd prime below the elementary radius is bounded by the elementary envelope. -/
theorem odd_prime_le_elementaryUpperBound {B p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hpR : (p : ℝ) ≤ elementaryRadius B) : p ≤ elementaryUpperBound B :=
  (AnalyticNumberTheory.Arithmetic.le_greatestOddPrimeLE hp hpodd hpR).trans (le_max_right _ _)

/-- For odd `750 ≤ n ≤ B`, the elementary omega estimate bounds the LLS squared radius at `4n`
by `elementaryRadius B`. -/
theorem elementary_sq_le_radius (hElem : AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement)
    {B n : ℕ} (hn : Odd n) (hnB : n ≤ B) (hn750 : 750 ≤ n) :
    (Real.log (NumberTheory.characterModulus n : ℝ) +
          LLS.llsCorrectionTerm (NumberTheory.characterModulus n)) ^
        2 ≤
      elementaryRadius B := by
  have hq : 3000 ≤ NumberTheory.characterModulus n := by
    unfold NumberTheory.characterModulus; omega
  have hB750 : 750 ≤ B := hn750.trans hnB
  have hqpos : 0 < NumberTheory.characterModulus n := (by norm_num only : 0 < 3000).trans_le hq
  have hmod := NumberTheory.characterModulus_le hnB
  have hx := (AnalyticNumberTheory.Arithmetic.log_log_pos_of_le hq).1
  have hy := (AnalyticNumberTheory.Arithmetic.log_log_pos_of_le hq).2
  have hqposReal : (0 : ℝ) < NumberTheory.characterModulus n := by exact_mod_cast hqpos
  have hmodReal : (NumberTheory.characterModulus n : ℝ) ≤ NumberTheory.characterModulus B := by
    exact_mod_cast hmod
  have hlog := Real.log_le_log hqposReal hmodReal
  have hloglog := Real.log_le_log hx hlog
  have hcorr := llsCorrectionTerm_le_elementary hElem hn hn750
  have hcast : (NumberTheory.characterModulus n : ℝ) = 4 * n := by
    unfold NumberTheory.characterModulus; push_cast; ring
  have hcastB : (NumberTheory.characterModulus B : ℝ) = 4 * B := by
    unfold NumberTheory.characterModulus; push_cast; ring
  rw [hcastB] at hlog hloglog
  have hbase :
    Real.log (NumberTheory.characterModulus n : ℝ) +
        LLS.llsCorrectionTerm (NumberTheory.characterModulus n) ≤
      Real.log (4 * B : ℝ) + (24 / 5 : ℝ) * Real.log (Real.log (4 * B : ℝ)) + 3 := by
    linarith only [hlog, hloglog, hcorr]
  have hleft :
    0 ≤
      Real.log (NumberTheory.characterModulus n : ℝ) +
        LLS.llsCorrectionTerm (NumberTheory.characterModulus n) :=
    add_nonneg hx.le (LLS.llsCorrectionTerm_nonneg _)
  have hright : 0 ≤ Real.log (4 * B : ℝ) + (24 / 5 : ℝ) * Real.log (Real.log (4 * B : ℝ)) + 3 := by
    have hxB : 0 < Real.log (4 * B : ℝ) := by
      have h3000 : (3000 : ℕ) ≤ 4 * B := by omega
      have : (1 : ℝ) < 4 * B := by
        have : (3000 : ℝ) ≤ 4 * B := by exact_mod_cast h3000
        linarith only [this]
      exact Real.log_pos this
    have hyB : 0 < Real.log (Real.log (4 * B : ℝ)) := hy.trans_le hloglog
    positivity
  unfold elementaryRadius
  exact (sq_le_sq₀ hleft hright).mpr hbase

/-- LLS and the elementary bound together bound each large admissible least witness by the
endpoint radius. -/
theorem primeNegOneWitness_cast_le_elementaryRadius (hLLS : LLS.llsTheorem11S1Character)
    (hElem : AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement) {B n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hn750 : 750 ≤ n)
    (hw : (NumberTheory.PrimeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ elementaryRadius B := by
  have hq : 3000 ≤ NumberTheory.characterModulus n := by
    unfold NumberTheory.characterModulus; omega
  exact
    (primeNegOneWitness_le_of_LLS hLLS n hn hns hq hw).trans
      (elementary_sq_le_radius hElem hn hnB hn750)

end PseudoPrime.PseudoSquare
