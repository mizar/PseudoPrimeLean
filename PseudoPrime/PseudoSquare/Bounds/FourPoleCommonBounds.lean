/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleCommonScale
public import PseudoPrime.PseudoSquare.Bounds.LogScaleBounds
public import PseudoPrime.PseudoSquare.Bounds.FourPoleFiniteBounds

/-! # Fourth-pole witness maxima at a common logarithmic scale

The actual-prime comparison is valid at every common scale above the finite entrance.
Using that scale directly covers earlier inputs and removes the former, larger history
constant. The selected numerical coefficient belongs to this application; the lifting
interface remains independent in `LogScaleBounds`.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The fourth-pole candidate at the larger entrance or endpoint logarithm.
Input: any natural endpoint, including an empty admissible range.
Definition: coefficient 777/1000 times the squared common scale.
Role: replace the former low-input history constant without extrapolating a pointwise theorem. -/
noncomputable def fourPoleScaleBound (B : ℕ) : ℝ :=
  logScaleBound (777 / 1000) ((10 : ℝ) ^ 18) B

/-- GRH bounds the negative-witness maximum by the common-scale fourth-pole candidate.
Input: any natural endpoint and GRH. Claim: every smaller admissible input is covered.
Proof: apply the closed least-witness theorem at one common upper scale.
Role: expose the full-domain candidate with no arithmetic or scalar-gap hypothesis. -/
theorem QNegOne_le_fourPole_scale (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ fourPoleScaleBound B :=
  QNegOne_le_logScaleBound (by norm_num only : (0 : ℝ) ≤ 777 / 1000)
    (fun {_n} hn hns {_L} hL hlog hw ↦
      LLS.PaperStatements.fourPole_common_scale_least hn hns hGRH hL hlog hw)
    B

/-- Both witness maxima obey the common-scale fourth-pole candidate under GRH.
Input: any natural endpoint and GRH. Claim: the negative and non-one maxima are bounded.
Proof: non-one witnesses are no larger than negative witnesses.
Role: supply cumulative Jacobi and Selfridge consumers at all endpoints. -/
theorem witnessMaxima_le_fourPole_scale (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ fourPoleScaleBound B ∧ (QNeOne B : ℝ) ≤ fourPoleScaleBound B :=
  ⟨QNegOne_le_fourPole_scale B hGRH,
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans (QNegOne_le_fourPole_scale B hGRH)⟩

/-- The common-scale candidate always includes its coefficient times the entrance squared.
Input: any endpoint. Claim: the fixed entrance is a lower bound for the candidate.
Proof: square the nonnegative maximum comparison.
Role: absorb the exceptional small Selfridge stopping values. -/
theorem fourPole_scale_lower (B : ℕ) :
    (777 / 1000 : ℝ) * ((10 : ℝ) ^ 18) ^ 2 ≤ fourPoleScaleBound B := by
  have hE : (0 : ℝ) ≤ (10 : ℝ) ^ 18 := by norm_num only
  exact
    mul_le_mul_of_nonneg_left ((sq_le_sq₀ hE (hE.trans (le_max_left _ _))).mpr (le_max_left _ _))
      (by norm_num only : (0 : ℝ) ≤ 777 / 1000)

/-- The common-scale candidate is no larger than the former cumulative history bound.
Input: any natural endpoint. Claim: the old public fourth-pole value is preserved or improved.
Proof: split according to which common-scale maximum is selected.
Role: certify non-worsening without changing the witness contract. -/
theorem fourPole_scale_le_legacy (B : ℕ) : fourPoleScaleBound B ≤ fourPoleCumulativeBound B := by
  change
    (777 / 1000 : ℝ) * max ((10 : ℝ) ^ 18) (Real.log B) ^ 2 ≤
      max ((9999 / 10000 : ℝ) * ((10 : ℝ) ^ 18) ^ 2) ((777 / 1000 : ℝ) * Real.log B ^ 2)
  by_cases h : Real.log B ≤ (10 : ℝ) ^ 18
  · rw [max_eq_left h]
    exact
      (mul_le_mul_of_nonneg_right (by norm_num only : (777 / 1000 : ℝ) ≤ 9999 / 10000)
            (sq_nonneg _)).trans
        (le_max_left _ _)
  · rw [max_eq_right (le_of_not_ge h)]
    exact le_max_right _ _

/-- The new candidate strictly improves the former history near the finite entrance.
Input: an endpoint logarithm between the entrance and eleven tenths of it.
Claim: the common-scale value is strictly smaller than the former cumulative value.
Proof: bound the squared logarithm by its rational upper endpoint.
Role: exhibit a certified winning interval, independent of decimal approximations. -/
theorem fourPole_scale_lt_legacy {B : ℕ} (hL : (10 : ℝ) ^ 18 ≤ Real.log B)
    (hU : Real.log B ≤ (11 / 10 : ℝ) * (10 : ℝ) ^ 18) :
    fourPoleScaleBound B < fourPoleCumulativeBound B := by
  change
    (777 / 1000 : ℝ) * max ((10 : ℝ) ^ 18) (Real.log B) ^ 2 <
      max ((9999 / 10000 : ℝ) * ((10 : ℝ) ^ 18) ^ 2) ((777 / 1000 : ℝ) * Real.log B ^ 2)
  rw [max_eq_right hL]
  have hs :=
    (sq_le_sq₀ (Real.log_natCast_nonneg B)
          (by norm_num only : (0 : ℝ) ≤ (11 / 10 : ℝ) * (10 : ℝ) ^ 18)).mpr
      hU
  exact
    (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 777 / 1000)).trans_lt
      ((by norm_num only :
            (777 / 1000 : ℝ) * ((11 / 10 : ℝ) * (10 : ℝ) ^ 18) ^ 2 <
              (9999 / 10000 : ℝ) * ((10 : ℝ) ^ 18) ^ 2).trans_le
        (le_max_left _ _))

end PseudoPrime.PseudoSquare
