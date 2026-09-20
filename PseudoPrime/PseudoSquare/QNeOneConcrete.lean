/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: Mizar
-/
import PseudoPrime.LLS.Extensions.RiemannBounds
import PseudoPrime.LLS.Extensions.QNeOneLogWeightedBounds

/-!
# Concrete quadratic bridge applications

This module contains the application layer that instantiates the generic LLS analytic estimates
with the Jacobi character and witness set attached to a concrete odd nonsquare `n`.  Generic
analytic estimates remain in `LLS/Extensions`.
-/

namespace PseudoPrime.PseudoSquare

/-!
The arithmetic bridge now supplies the exact primitive-character hypotheses required by the
three analytic contradiction theorems. These wrappers keep the conductor equality and the
root cutoff at the bridge boundary, so the analytic theorems themselves remain generic.
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
    bridge.primitiveCharacter_eq_one_in_log_square_range (by linarith) hno
  exact
    LLS.Extensions.primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_even_false_common
      bridge.character bridge.character_ne_one bridge.primitiveCharacter_isQuadratic
      bridge.primitiveCharacter_even hGRH hy hlogD hriemann hriemannReciprocal hodd h2

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
    bridge.primitiveCharacter_eq_one_in_log_square_range (by linarith) hno
  exact
    LLS.Extensions.primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_false_common
      bridge.character bridge.character_ne_one bridge.primitiveCharacter_isQuadratic
      bridge.primitiveCharacter_even hGRH hy hlogD hriemann hriemannReciprocal hodd h2

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
    bridge.primitiveCharacter_eq_one_in_log_square_range (by linarith) hno
  exact
    LLS.Extensions.primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_false_common
      bridge.character bridge.character_ne_one bridge.primitiveCharacter_isQuadratic
      bridge.primitiveCharacter_even hGRH hy hlogD hriemann hriemannReciprocal hodd h2

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_false_common_of_bridge_of_rh
    {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log bridge.character.conductor ≤ y + Real.log 4)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n)
    (h2 : bridge.character.primitiveCharacter 2 = 0) : False := by
  obtain ⟨hriemann, hriemannReciprocal⟩ :=
    LLS.Extensions.riemannBounds_of_riemannHypothesis hGRH.riemann
  exact
    primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_false_common_of_bridge bridge hGRH hy
      hlogD hriemann hriemannReciprocal hno h2

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_false_common_of_bridge_of_rh
    {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log bridge.character.conductor ≤ y)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n)
    (h2 : bridge.character.primitiveCharacter 2 = -1) : False := by
  obtain ⟨hriemann, hriemannReciprocal⟩ :=
    LLS.Extensions.riemannBounds_of_riemannHypothesis hGRH.riemann
  exact
    primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_false_common_of_bridge bridge hGRH
      hy hlogD hriemann hriemannReciprocal hno h2

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_false_common_of_bridge_of_rh
    {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log bridge.character.conductor ≤ y)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n)
    (h2 : bridge.character.primitiveCharacter 2 = 1) : False := by
  obtain ⟨hriemann, hriemannReciprocal⟩ :=
    LLS.Extensions.riemannBounds_of_riemannHypothesis hGRH.riemann
  exact
    primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_false_common_of_bridge bridge hGRH hy
      hlogD hriemann hriemannReciprocal hno h2

/-! The c=±1 wrappers now manufacture their sharp `log conductor ≤ y` premise from the bridge. -/

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

theorem qNeOneAnalyticFalse_of_bridge_of_cutoff {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {N : ℕ} (hNpos : 0 < N)
    (hN : 12 ≤ Real.log (N : ℝ)) (hNd : N ≤ bridge.squarefreePart)
    (hno : ∀ q, q.Prime → Odd q → q ≤ ⌊bridge.y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n) :
    False := by
  rcases bridge.primitiveCharacter_isQuadratic (2 : ZMod bridge.character.conductor) with h2 | h2 |
    h2
  · exact
      primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_false_common_of_bridge_of_cutoff
        bridge hGRH hNpos hN hNd hno h2
  · exact
      primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_false_common_of_bridge_of_cutoff
        bridge hGRH hNpos hN hNd hno h2
  · exact qNeOneNegCutoffFalse bridge hGRH hNpos hN hNd hno h2

/-!
Input/assumptions: the arithmetic bridge, GRH, squarefree part `d ≥ 10^6`, and absence of
odd-prime Jacobi `≠ 1` witnesses up to `⌊(log d)^2⌋₊`.
Conclusion: the three-way analytic contradiction applies once the squarefree part dominates
this concrete integer.
Content: `log (10^6) = 6 log 10`, and `8 < 10` together with the checked lower bound
for `log 2` gives `12 ≤ log (10^6)`.
Role: supplies the analytic branch of `exists_primeNeOneWitness_cast_le_log_sq_of_odd_nonsquare`.
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
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) (by norm_num) (by norm_num)
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
      norm_num only
    have h2 := Real.log_two_gt_d9
    norm_num only at h2
    have hlog10 : (207 / 100 : ℝ) < Real.log 10 := by linarith
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only
    nlinarith
  exact qNeOneAnalyticFalse_of_bridge_of_cutoff bridge hGRH hNpos (by linarith) hNd hno

end PseudoPrime.PseudoSquare
