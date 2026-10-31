/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleFiniteEntrance
public import PseudoPrime.LLS.PaperStatements.RationalPoleSharpEntrance
public import PseudoPrime.PseudoSquare.Bounds.CommonEndpointBounds

/-! # Full-domain cumulative fourth-pole witness bounds -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- A cumulative fourth-pole candidate. The old common endpoint bounds every input
below the finite entrance; the new coefficient controls every later input through `B`.
The maximum retains the low-input cap instead of extrapolating a pointwise entrance. -/
noncomputable def fourPoleCumulativeBound (B : ℕ) : ℝ :=
  max ((9999 / 10000 : ℝ) * ((10 : ℝ) ^ 18) ^ 2) ((777 / 1000 : ℝ) * (Real.log B) ^ 2)

/-- Under GRH, the fourth-pole cumulative candidate bounds the negative witness
maximum at every natural endpoint, including an empty admissible domain. -/
theorem QNegOne_le_fourPole_cumulative (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ fourPoleCumulativeBound B := by
  apply
    QNegOne_cast_le_of_forall
      ((by norm_num only : (0 : ℝ) ≤ (9999 / 10000) * ((10 : ℝ) ^ 18) ^ 2).trans (le_max_left _ _))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare
  by_cases hL : (10 : ℝ) ^ 18 ≤ Real.log n
  · have hb :=
      LLS.PaperStatements.fourPole_sharp_jacobi_finite_least ha.odd ha.not_isSquare hGRH hL hw
    have hlog := Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le)
    have hs := mul_self_le_mul_self (Real.log_natCast_nonneg n) hlog
    have he : (777 / 1000 : ℝ) * (Real.log n) ^ 2 ≤ (777 / 1000 : ℝ) * (Real.log B) ^ 2 := by
      nlinarith only [hs]
    exact (hb.trans he).trans (le_max_right _ _)
  · have hb :=
      primeNegOneWitness_cast_le_joint_entrance_endpoint ha.odd ha.not_isSquare hGRH
        (by norm_num only : (255 : ℝ) ≤ (10 : ℝ) ^ 18) (le_of_not_ge hL) hw
    exact hb.trans (le_max_left _ _)

/-- Under GRH, both witness maxima obey the new full-domain cumulative candidate.
The non-one maximum is no larger than the negative maximum. -/
theorem witnessMaxima_le_fourPole (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ fourPoleCumulativeBound B ∧ (QNeOne B : ℝ) ≤ fourPoleCumulativeBound B := by
  have h := QNegOne_le_fourPole_cumulative B hGRH
  exact ⟨h, (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans h⟩

/-- At every natural endpoint, the coefficient-777 cumulative candidate is no larger
than the previous coefficient-39/50 candidate with the same low-input cap.
Compare the nonnegative quadratic terms and retain the maximum. -/
theorem fourPole_cumulative_le_previous (B : ℕ) :
    fourPoleCumulativeBound B ≤
      max ((9999 / 10000 : ℝ) * ((10 : ℝ) ^ 18) ^ 2) ((39 / 50 : ℝ) * Real.log B ^ 2) := by
  exact
    max_le_max le_rfl
      (mul_le_mul_of_nonneg_right (by norm_num only : (777 / 1000 : ℝ) ≤ 39 / 50) (sq_nonneg _))

/-- Once log B is at least twice the entrance logarithm, the new cumulative candidate
is strictly smaller than the previous candidate. The quadratic term dominates the
retained low-input cap and the coefficient comparison is strict. -/
theorem fourPole_cumulative_lt_previous {B : ℕ} (hL : 2 * (10 : ℝ) ^ 18 ≤ Real.log B) :
    fourPoleCumulativeBound B <
      max ((9999 / 10000 : ℝ) * ((10 : ℝ) ^ 18) ^ 2) ((39 / 50 : ℝ) * Real.log B ^ 2) := by
  have hpos : 0 < Real.log B := by
    norm_num only at hL; linarith only [hL]
  have hcap : (9999 / 10000 : ℝ) * ((10 : ℝ) ^ 18) ^ 2 ≤ (777 / 1000 : ℝ) * Real.log B ^ 2 := by
    norm_num only at hL ⊢
    nlinarith only [hL, sq_nonneg (Real.log B - 2 * (10 : ℝ) ^ 18)]
  rw [fourPoleCumulativeBound, max_eq_right hcap]
  exact
    (mul_lt_mul_of_pos_right (by norm_num only : (777 / 1000 : ℝ) < 39 / 50)
          (sq_pos_of_pos hpos)).trans_le
      (le_max_right _ _)

end PseudoPrime.PseudoSquare
