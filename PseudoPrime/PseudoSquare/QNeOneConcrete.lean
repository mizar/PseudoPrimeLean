/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannWeightedBounds
public import PseudoPrime.LLS.Extensions.PaperProofs

/-!
# Concrete quadratic bridge applications

This module contains the application layer that instantiates the generic LLS analytic estimates
with the Jacobi character and witness set attached to a concrete odd nonsquare `n`.  Generic
analytic estimates remain in `LLS/Extensions`.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-!
The arithmetic bridge supplies the exact primitive-character hypotheses required by the
three analytic contradiction theorems. These wrappers keep the conductor equality and the
root cutoff at the bridge boundary, so the analytic theorems themselves remain generic.
-/

/--
For the arithmetic bridge of an odd nonsquare `n`, assume GRH, `y ≥ 12`,
`log conductor ≤ y + log 4`, both Riemann weighted lower bounds, and no odd-prime Jacobi `≠ 1`
witness up to `⌊y^2⌋₊`. If the primitive character takes value `0` at `2`, these
assumptions contradict the corresponding generic log-weighted estimate.
The proof transports conductor nonzeroness and derives the required odd-prime evaluations
from the no-witness assumption. This supplies the concrete 0 branch.
-/
theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_false_common_of_bridge {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log bridge.character.conductor ≤ y + Real.log 4)
    (hriemann : LLS.LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLS.LLSRiemannReciprocalLowerBound)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n)
    (h2 : bridge.character.primitiveCharacter 2 = 0) : False := by
  let _ : NeZero bridge.character.conductor :=
    ⟨by
      intro hc
      exact
        (inferInstance : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor).out
          ((DirichletCharacter.isPrimitive_def bridge.character).mp bridge.character_primitive ▸
            hc)⟩
  have hodd :
    ∀ {k p : ℕ},
      k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
        p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
        p.Prime → Odd p → bridge.character.primitiveCharacter p = 1 :=
    bridge.primitiveCharacter_eq_one_in_log_square_range (by linarith only [hy]) hno
  exact
    LLS.Extensions.primitiveLogWeightedBounds_of_qneOne_zero_branch_even_false_common
      bridge.character bridge.character_ne_one bridge.primitiveCharacter_even hGRH hy hlogD hriemann
      hriemannReciprocal hodd h2

/--
For the arithmetic bridge of an odd nonsquare `n`, assume GRH, `y ≥ 12`,
`log conductor ≤ y`, both Riemann weighted lower bounds, and no odd-prime Jacobi `≠ 1`
witness up to `⌊y^2⌋₊`. If the primitive character takes value `-1` at `2`, these
assumptions contradict the corresponding general-character log-weighted estimate.
The proof transports conductor nonzeroness and derives the required odd-prime evaluations
from the no-witness assumption. This supplies the concrete -1 branch.
-/
theorem primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_false_common_of_bridge {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log bridge.character.conductor ≤ y) (hriemann : LLS.LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLS.LLSRiemannReciprocalLowerBound)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n)
    (h2 : bridge.character.primitiveCharacter 2 = -1) : False := by
  let _ : NeZero bridge.character.conductor :=
    ⟨by
      intro hc
      exact
        (inferInstance : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor).out
          ((DirichletCharacter.isPrimitive_def bridge.character).mp bridge.character_primitive ▸
            hc)⟩
  have hodd :
    ∀ {k p : ℕ},
      k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
        p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
        p.Prime → Odd p → bridge.character.primitiveCharacter p = 1 :=
    bridge.primitiveCharacter_eq_one_in_log_square_range (by linarith only [hy]) hno
  exact
    LLS.Extensions.primitiveLogWeightedBounds_of_qneOne_neg_one_branch_false_common bridge.character
      bridge.character_ne_one bridge.primitiveCharacter_even hGRH hy hlogD hriemann
      hriemannReciprocal hodd h2

/--
For the arithmetic bridge of an odd nonsquare `n`, assume GRH, `y ≥ 12`,
`log conductor ≤ y`, both Riemann weighted lower bounds, and no odd-prime Jacobi `≠ 1`
witness up to `⌊y^2⌋₊`. If the primitive character takes value `1` at `2`, these
assumptions contradict the corresponding general-character log-weighted estimate.
The proof transports conductor nonzeroness and derives the required odd-prime evaluations
from the no-witness assumption. This supplies the concrete 1 branch.
-/
theorem primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_false_common_of_bridge {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log bridge.character.conductor ≤ y) (hriemann : LLS.LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLS.LLSRiemannReciprocalLowerBound)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n)
    (h2 : bridge.character.primitiveCharacter 2 = 1) : False := by
  let _ : NeZero bridge.character.conductor :=
    ⟨by
      intro hc
      exact
        (inferInstance : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor).out
          ((DirichletCharacter.isPrimitive_def bridge.character).mp bridge.character_primitive ▸
            hc)⟩
  have hodd :
    ∀ {k p : ℕ},
      k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
        p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
        p.Prime → Odd p → bridge.character.primitiveCharacter p = 1 :=
    bridge.primitiveCharacter_eq_one_in_log_square_range (by linarith only [hy]) hno
  exact
    LLS.Extensions.primitiveLogWeightedBounds_of_qneOne_one_branch_false_common bridge.character
      bridge.character_ne_one bridge.primitiveCharacter_even hGRH hy hlogD hriemann
      hriemannReciprocal hodd h2

/--
Under GRH, `y ≥ 12`, `log conductor ≤ y + log 4`, and absence of odd-prime Jacobi `≠ 1` witnesses
up to `⌊y^2⌋₊`, the arithmetic bridge cannot have primitive-character value `0` at `2`.
The proof derives both Riemann weighted lower bounds from the Riemann hypothesis component
of GRH and applies the concrete 0 branch. This removes the explicit Riemann inputs
from the cutoff application.
-/
theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_false_common_of_bridge_of_rh
    {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log bridge.character.conductor ≤ y + Real.log 4)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n)
    (h2 : bridge.character.primitiveCharacter 2 = 0) : False := by
  have hriemann := LLS.llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann
  have hriemannReciprocal := LLS.llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann
  exact
    primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_false_common_of_bridge bridge hGRH hy
      hlogD hriemann hriemannReciprocal hno h2

/--
Under GRH, `y ≥ 12`, `log conductor ≤ y`, and absence of odd-prime Jacobi `≠ 1` witnesses
up to `⌊y^2⌋₊`, the arithmetic bridge cannot have primitive-character value `-1` at `2`.
The proof derives both Riemann weighted lower bounds from the Riemann hypothesis component
of GRH and applies the concrete -1 branch. This removes the explicit Riemann inputs
from the cutoff application.
-/
theorem primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_false_common_of_bridge_of_rh
    {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log bridge.character.conductor ≤ y)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n)
    (h2 : bridge.character.primitiveCharacter 2 = -1) : False := by
  have hriemann := LLS.llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann
  have hriemannReciprocal := LLS.llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann
  exact
    primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_false_common_of_bridge bridge hGRH
      hy hlogD hriemann hriemannReciprocal hno h2

/--
Under GRH, `y ≥ 12`, `log conductor ≤ y`, and absence of odd-prime Jacobi `≠ 1` witnesses
up to `⌊y^2⌋₊`, the arithmetic bridge cannot have primitive-character value `1` at `2`.
The proof derives both Riemann weighted lower bounds from the Riemann hypothesis component
of GRH and applies the concrete 1 branch. This removes the explicit Riemann inputs
from the cutoff application.
-/
theorem primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_false_common_of_bridge_of_rh
    {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log bridge.character.conductor ≤ y)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n)
    (h2 : bridge.character.primitiveCharacter 2 = 1) : False := by
  have hriemann := LLS.llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann
  have hriemannReciprocal := LLS.llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann
  exact
    primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_false_common_of_bridge bridge hGRH hy
      hlogD hriemann hriemannReciprocal hno h2

/-! The c=±1 branches derive their sharp `log conductor ≤ y` premise from the bridge. -/

/--
For a positive cutoff `N` with `12 ≤ log N` and `N ≤ bridge.squarefreePart`, GRH and
absence of odd-prime Jacobi `≠ 1` witnesses up to `⌊bridge.y^2⌋₊` contradict primitive
character value `-1` at `2`. Nonvanishing at `2` yields coprimality; conductor-discriminant
comparison then identifies the discriminant with the squarefree part and supplies the sharp
`log conductor ≤ bridge.y` bound. This is the negative branch of the cutoff contradiction.
-/
theorem qNeOneNegCutoffFalse {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {N : ℕ} (hNpos : 0 < N)
    (hN : 12 ≤ Real.log (N : ℝ)) (hNd : N ≤ bridge.squarefreePart)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊bridge.y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n)
    (h2 : bridge.character.primitiveCharacter 2 = -1) : False := by
  have hy := bridge.y_ge_of_nat_cutoff_of_twelve hNpos hN hNd
  have hdvd : bridge.squarefreePart ∣ n := by
    exact
      ⟨bridge.squareFactor ^ 2, by
        simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  have hcond := NumberTheory.complexQuadraticCharacter_conductor_eq_discriminant bridge hdvd
  have hcop : IsCoprime (2 : ℤ) bridge.character.conductor := by
    by_contra hcop
    have hz :=
      (DirichletCharacter.apply_eq_zero_iff bridge.character.primitiveCharacter (2 : ℤ)).mpr hcop
    have h2' : bridge.character.primitiveCharacter (2 : ℤ) = -1 := by
      simpa only [Int.cast_ofNat] using h2
    rw [h2'] at hz
    norm_num only at hz
  have hlevel :
    bridge.character.conductor = (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (DirichletCharacter.isPrimitive_def bridge.character).mp bridge.character_primitive
  have hcopLevel : IsCoprime (2 : ℤ) (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    hlevel ▸ hcop
  have hprimitive :=
    DirichletCharacter.primitiveCharacter_apply_of_isCoprime (χ := bridge.character) hcopLevel
  have hc :
    NumberTheory.primitiveQuadraticCharacter n hn
        (2 : ZMod (NumberTheory.complexQuadraticCharacter n hn).conductor) =
      -1 := by
    have hprimitive' :
      bridge.character.primitiveCharacter (2 : ℤ) =
        NumberTheory.primitiveQuadraticCharacter n hn (2 : ℤ) := by
      simpa only [Int.cast_ofNat, bridge.character_eq] using hprimitive
    have h2' : bridge.character.primitiveCharacter (2 : ℤ) = -1 := by
      simpa only [Int.cast_ofNat] using h2
    simpa only [Int.cast_ofNat] using hprimitive'.symm.trans h2'
  have hD := bridge.discriminant_eq_squarefreePart_of_two_eq_neg_one hcond hc
  have hlogD := bridge.log_character_conductor_le_of_discriminant_le hD.le
  exact
    primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_false_common_of_bridge_of_rh bridge
      hGRH hy hlogD hno h2

/--
For positive `N` with `12 ≤ log N` and `N ≤ bridge.squarefreePart`, assume GRH and no
odd-prime Jacobi `≠ 1` witnesses up to `⌊bridge.y^2⌋₊`. Primitive-character value `1` at `2`
is impossible: nonvanishing yields coprimality, the discriminant equals the squarefree part,
and the resulting sharp conductor bound feeds the value-one contradiction.
This supplies the positive branch without a separate conductor estimate.
-/
theorem primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_false_common_of_bridge_of_cutoff
    {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {N : ℕ} (hNpos : 0 < N)
    (hN : 12 ≤ Real.log (N : ℝ)) (hNd : N ≤ bridge.squarefreePart)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊bridge.y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n)
    (h2 : bridge.character.primitiveCharacter 2 = 1) : False := by
  have hy := bridge.y_ge_of_nat_cutoff_of_twelve hNpos hN hNd
  have hdvd : bridge.squarefreePart ∣ n := by
    exact
      ⟨bridge.squareFactor ^ 2, by
        simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  have hcond := NumberTheory.complexQuadraticCharacter_conductor_eq_discriminant bridge hdvd
  have hcop : IsCoprime (2 : ℤ) bridge.character.conductor := by
    by_contra hcop
    have hz :=
      (DirichletCharacter.apply_eq_zero_iff bridge.character.primitiveCharacter (2 : ℤ)).mpr hcop
    have h2' : bridge.character.primitiveCharacter (2 : ℤ) = 1 := by
      simpa only [Int.cast_ofNat] using h2
    rw [h2'] at hz
    norm_num only at hz
  have hlevel :
    bridge.character.conductor = (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (DirichletCharacter.isPrimitive_def bridge.character).mp bridge.character_primitive
  have hcopLevel : IsCoprime (2 : ℤ) (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    hlevel ▸ hcop
  have hprimitive :=
    DirichletCharacter.primitiveCharacter_apply_of_isCoprime (χ := bridge.character) hcopLevel
  have hc :
    NumberTheory.primitiveQuadraticCharacter n hn
        (2 : ZMod (NumberTheory.complexQuadraticCharacter n hn).conductor) =
      1 := by
    have hprimitive' :
      bridge.character.primitiveCharacter (2 : ℤ) =
        NumberTheory.primitiveQuadraticCharacter n hn (2 : ℤ) := by
      simpa only [Int.cast_ofNat, bridge.character_eq] using hprimitive
    have h2' : bridge.character.primitiveCharacter (2 : ℤ) = 1 := by
      simpa only [Int.cast_ofNat] using h2
    simpa only [Int.cast_ofNat] using hprimitive'.symm.trans h2'
  have hD := bridge.discriminant_eq_squarefreePart_of_two_eq_one hcond hc
  have hlogD := bridge.log_character_conductor_le_of_discriminant_le hD.le
  exact
    primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_false_common_of_bridge_of_rh bridge
      hGRH hy hlogD hno h2

/--
For positive `N` with `12 ≤ log N` and `N ≤ bridge.squarefreePart`, GRH and no odd-prime
Jacobi `≠ 1` witnesses up to `⌊bridge.y^2⌋₊` contradict primitive-character value `0` at `2`.
The proof derives `bridge.y ≥ 12` from the cutoff and uses the bridge estimate
`log conductor ≤ bridge.y + log 4` in the zero-branch theorem. This covers the ramified branch.
-/
theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_false_common_of_bridge_of_cutoff
    {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {N : ℕ} (hNpos : 0 < N)
    (hN : 12 ≤ Real.log (N : ℝ)) (hNd : N ≤ bridge.squarefreePart)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊bridge.y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n)
    (h2 : bridge.character.primitiveCharacter 2 = 0) : False := by
  have hy := bridge.y_ge_of_nat_cutoff_of_twelve hNpos hN hNd
  have hlogD := bridge.log_character_conductor_le_y_add_log_four
  exact
    primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_false_common_of_bridge_of_rh bridge
      hGRH hy hlogD hno h2

/-! The cutoff contradiction dispatches the three possible primitive-character values at `2`. -/

/--
Given the arithmetic bridge, GRH, a positive `N` with `12 ≤ log N` below its squarefree
part, and no odd-prime Jacobi `≠ 1` witness up to `⌊bridge.y^2⌋₊`, derive `False`.
Quadraticity restricts the primitive character at `2` to `0`, `1`, or `-1`; the proof
dispatches the three cutoff contradictions. This is the analytic no-witness elimination
used with the explicit million cutoff.
-/
theorem qNeOneAnalyticFalse_of_bridge_of_cutoff {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {N : ℕ} (hNpos : 0 < N)
    (hN : 12 ≤ Real.log (N : ℝ)) (hNd : N ≤ bridge.squarefreePart)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊bridge.y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n) :
    False := by
  rcases
    NumberTheory.isQuadratic_primitiveCharacter bridge.character bridge.character_quadratic
      (2 : ZMod bridge.character.conductor) with
    h2 | h2 | h2
  · exact
      primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_false_common_of_bridge_of_cutoff
        bridge hGRH hNpos hN hNd hno h2
  · exact
      primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_false_common_of_bridge_of_cutoff
        bridge hGRH hNpos hN hNd hno h2
  · exact qNeOneNegCutoffFalse bridge hGRH hNpos hN hNd hno h2

/--
For the arithmetic bridge of an odd nonsquare `n`, assume GRH, squarefree part
`d ≥ 10^6`, and no odd-prime Jacobi `≠ 1` witnesses up to `⌊(log d)^2⌋₊`.
These assumptions imply `False`. The proof rewrites `log(10^6) = 6 log 10` and uses
the explicit lower bounds for `log 2` and `log 5` to obtain `12 ≤ log(10^6)`, then
applies the three-branch cutoff contradiction. This supplies the analytic branch of
the integrated logarithmic-square witness theorem.
-/
theorem qNeOneAnalyticFalse_of_bridge_of_explicit_cutoff {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hNd : 10 ^ 6 ≤ bridge.squarefreePart)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊bridge.y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n) :
    False := by
  have hNpos : 0 < (10 ^ 6 : ℕ) := by norm_num only
  have hN : (12 : ℝ) ≤ Real.log ((10 ^ 6 : ℕ) : ℝ) := by
    have h8 : Real.log (8 : ℝ) ≤ Real.log 10 := by
      exact
        Real.strictMonoOn_log.monotoneOn (by norm_num only [Set.mem_Ioi])
          (by norm_num only [Set.mem_Ioi]) (by norm_num only)
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
      norm_num only
    have h2 := Real.log_two_gt_d9
    norm_num only at h2
    have hlog10 : (207 / 100 : ℝ) < Real.log 10 := by
      rw [Real.log_ten_eq]
      linarith only [Real.log_two_gt_d9, Real.log_five_gt_d9]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only
    nlinarith only [hlog10]
  exact qNeOneAnalyticFalse_of_bridge_of_cutoff bridge hGRH hNpos hN hNd hno

end PseudoPrime.PseudoSquare
