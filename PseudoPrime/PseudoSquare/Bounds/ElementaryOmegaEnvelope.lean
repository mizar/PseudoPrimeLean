/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.OddPrimeCutoff
public import PseudoPrime.PseudoSquare.CharacterBound
public import PseudoPrime.PseudoSquare.Computation.SmallN

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

@[expose] public section

namespace PseudoPrime.PseudoSquare

/--
Assuming `ElementaryOmegaStatement`, odd `n ≥ 750` has LLS correction term at most
`(24/5) * loglog(4n) + 3`. The proof uses `4n ≥ 3000` to obtain positive logarithms,
bounds the prime-count contribution with the elementary omega estimate, and drops the
nonnegative auxiliary term. Both branches of the correction-term maximum are bounded.
This is the correction comparison used by the squared-radius theorem.
-/
theorem llsCorrectionTerm_le_elementary
    (hElem : AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement) {n : ℕ} (hn : Odd n)
    (hn750 : 750 ≤ n) :
    LLS.llsCorrectionTerm (NumberTheory.characterModulus n) ≤
      (24 / 5 : ℝ) * Real.log (Real.log (NumberTheory.characterModulus n)) + 3 := by
  have hq : 3000 ≤ NumberTheory.characterModulus n := by
    unfold NumberTheory.characterModulus
    calc
      3000 = 4 * 750 := by norm_num only
      _ ≤ 4 * n := Nat.mul_le_mul_left 4 hn750
  have hy := (AnalyticNumberTheory.Arithmetic.log_log_pos_of_le hq).2
  have hcount := AnalyticNumberTheory.Arithmetic.elementary_prime_count_term_le hElem hn hn750
  have haux := LLS.llsAuxiliaryTerm_nonneg (NumberTheory.characterModulus n)
  have hCeq : (2 : ℝ) * AnalyticNumberTheory.Arithmetic.elementaryOmegaConstant = 14 / 5 := by
    unfold AnalyticNumberTheory.Arithmetic.elementaryOmegaConstant
    norm_num only
  unfold LLS.llsCorrectionTerm
  apply max_le
  · nlinarith only [hy]
  · nlinarith only [hCeq, hcount, haux, hy]

/--
The real squared cutoff `(log(4B) + (24/5) * loglog(4B) + 3)^2` for a natural
endpoint `B`. It packages the simplified LLS radius after the elementary omega bound.
The square is nonnegative for every `B`; the envelope theorems use it to bound witnesses
and finite maxima, while the explicit public theorem unfolds this definition.
-/
noncomputable def elementaryRadius (B : ℕ) : ℝ :=
  (Real.log (4 * B) + (24 / 5 : ℝ) * Real.log (Real.log (4 * B)) + 3) ^ 2

/--
For `B ≥ 3`, `31 < elementaryRadius B`. Since `4B ≥ 12 > exp 2`, the proof obtains
`log(4B) > 2` and then `loglog(4B) > log 2`. The explicit logarithm constant makes
the positive base exceed `7.88`, whose square exceeds `31`. This shows that the
real radius includes the exceptional prime `31` and makes the maximum margin redundant.
-/
theorem thirtyOne_lt_elementaryRadius {B : ℕ} (hB : 3 ≤ B) : (31 : ℝ) < elementaryRadius B := by
  have h12B : (12 : ℝ) ≤ 4 * B := by
    have : (3 : ℝ) ≤ B := by exact_mod_cast hB
    linarith only [this]
  have hexp2 : Real.exp 2 < 12 := by
    have h1 := Real.exp_one_lt_d9
    have h1pos := Real.exp_pos 1
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num only
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

/--
The natural envelope `max 31 (greatestOddPrimeLE (elementaryRadius B))`.
The constant `31` covers the exceptional finite range, and the odd-prime cutoff rounds
the real radius for larger witnesses. It is defined for every natural `B`; for `B ≥ 3`
the cutoff already dominates `31`, so the maximum wrapper can be removed.
-/
noncomputable def elementaryUpperBound (B : ℕ) : ℕ :=
  max 31 (AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE (elementaryRadius B))

/--
For every natural `B`, `31 ≤ elementaryUpperBound B`. Unfolding the definition
reduces the claim to the left bound of a maximum. This absorbs the unconditional
small-range witness bound into the common elementary envelope.
-/
theorem thirty_one_le_elementaryUpperBound (B : ℕ) : 31 ≤ elementaryUpperBound B := by
  unfold elementaryUpperBound
  exact le_max_left _ _

/--
For `B ≥ 3`, the greatest odd prime at most `elementaryRadius B` is at least `31`.
The proof checks that `31` is an odd prime and applies the odd-prime cutoff interface
to `31 < elementaryRadius B`. This removes the exceptional safety margin from the
final bound on this domain.
-/
theorem thirtyOne_le_greatestOddPrimeLE_elementaryRadius {B : ℕ} (hB : 3 ≤ B) :
    31 ≤ AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE (elementaryRadius B) :=
  AnalyticNumberTheory.Arithmetic.le_greatestOddPrimeLE (by decide) (by decide)
    (thirtyOne_lt_elementaryRadius hB).le

/--
For `B ≥ 3`, `elementaryUpperBound B = greatestOddPrimeLE (elementaryRadius B)`.
The cutoff already dominates `31`, so `max_eq_right` removes the finite-range margin.
This identifies the common envelope with the bare odd-prime cutoff in the boxed theorem.
-/
theorem elementaryUpperBound_eq_of_le {B : ℕ} (hB : 3 ≤ B) :
    elementaryUpperBound B =
      AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE (elementaryRadius B) := by
  unfold elementaryUpperBound
  exact max_eq_right (thirtyOne_le_greatestOddPrimeLE_elementaryRadius hB)

/--
An odd prime `p` with `(p : ℝ) ≤ elementaryRadius B` satisfies
`p ≤ elementaryUpperBound B`. The proof rounds the real bound through
`le_greatestOddPrimeLE` and then includes that cutoff in the maximum envelope.
This converts the large-input real witness estimate to the natural finite-maximum bound.
-/
theorem odd_prime_le_elementaryUpperBound {B p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hpR : (p : ℝ) ≤ elementaryRadius B) : p ≤ elementaryUpperBound B :=
  (AnalyticNumberTheory.Arithmetic.le_greatestOddPrimeLE hp hpodd hpR).trans (le_max_right _ _)

/--
Assuming `ElementaryOmegaStatement` and odd `750 ≤ n ≤ B`, the squared corrected
LLS radius at `4n` is at most `elementaryRadius B`. The proof compares both logarithms
by monotonicity, substitutes the elementary correction bound, and checks nonnegativity
of both bases before squaring. This transports the pointwise LLS radius to the endpoint.
-/
theorem elementary_sq_le_radius (hElem : AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement)
    {B n : ℕ} (hn : Odd n) (hnB : n ≤ B) (hn750 : 750 ≤ n) :
    (Real.log (NumberTheory.characterModulus n : ℝ) +
          LLS.llsCorrectionTerm (NumberTheory.characterModulus n)) ^
        2 ≤
      elementaryRadius B := by
  have hq : 3000 ≤ NumberTheory.characterModulus n := by
    unfold NumberTheory.characterModulus
    calc
      3000 = 4 * 750 := by norm_num only
      _ ≤ 4 * n := Nat.mul_le_mul_left 4 hn750
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
    unfold NumberTheory.characterModulus
    push_cast
    ring
  have hcastB : (NumberTheory.characterModulus B : ℝ) = 4 * B := by
    unfold NumberTheory.characterModulus
    push_cast
    ring
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
      have h3000 : (3000 : ℕ) ≤ 4 * B := by
        calc
          3000 = 4 * 750 := by norm_num only
          _ ≤ 4 * B := Nat.mul_le_mul_left 4 hB750
      have : (1 : ℝ) < 4 * B := by
        have : (3000 : ℝ) ≤ 4 * B := by exact_mod_cast h3000
        linarith only [this]
      exact Real.log_pos this
    have hyB : 0 < Real.log (Real.log (4 * B : ℝ)) := hy.trans_le hloglog
    exact
      add_nonneg
        (add_nonneg (le_of_lt hxB) (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 24 / 5) hyB.le))
        (by norm_num only)
  unfold elementaryRadius
  exact (sq_le_sq₀ hleft hright).mpr hbase

/--
Assuming the LLS S1 bound and `ElementaryOmegaStatement`, an odd nonsquare
`750 ≤ n ≤ B` has least odd-prime Jacobi `-1` witness, with nonemptiness proof `hw`,
at most `elementaryRadius B` after real casting. The proof obtains `4n ≥ 3000`, applies
the LLS least-witness bound, and composes it with the squared-radius comparison.
This supplies the large-input branch of the final finite maximum theorem.
-/
theorem primeNegOneWitness_cast_le_elementaryRadius (hLLS : LLS.llsTheorem11S1Character)
    (hElem : AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement) {B n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hn750 : 750 ≤ n)
    (hw : (NumberTheory.PrimeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ elementaryRadius B := by
  have hq : 3000 ≤ NumberTheory.characterModulus n := by
    unfold NumberTheory.characterModulus
    calc
      3000 = 4 * 750 := by norm_num only
      _ ≤ 4 * n := Nat.mul_le_mul_left 4 hn750
  exact
    (primeNegOneWitness_le_of_LLS hLLS n hn hns hq hw).trans
      (elementary_sq_le_radius hElem hn hnB hn750)

end PseudoPrime.PseudoSquare
