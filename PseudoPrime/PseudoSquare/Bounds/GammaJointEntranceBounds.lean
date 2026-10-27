/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaJointEntranceBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaJointCommonBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaTransportedEntranceBounds

/-! # Negative and non-one odd-prime witnesses from logarithmic endpoint 255 -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH, L>=255 and log n<=L for odd nonsquare n, the least negative
odd-prime witness is at most (9999/10000)L^2. Below 260 use the transported
joint margin; above 260 apply the existing half-line theorem. -/
theorem primeNegOneWitness_cast_le_joint_entrance_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 255 ≤ L)
    (hlog : Real.log n ≤ L) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * L ^ 2 := by
  by_cases h260 : 260 ≤ L
  · exact
      primeNegOneWitness_cast_le_base_ratio_endpoint hn hns hGRH (by linarith only [h260]) hlog hw
  · have hU := le_of_lt (lt_of_not_ge h260)
    obtain ⟨hlo, hhi, hx, hb, hlow, hupp⟩ := LLS.gamma_joint_entrance_profile_inputs hL hU
    have hs := LLS.gamma_joint_entrance_separation hGRH.riemann hL hU
    have h :=
      primeNegOneWitness_cast_le_of_joint_factor_free_separation hn hns hGRH (by linarith only [hL])
        hlog hx (by norm_num only : (1 : ℝ) ≤ 50000) hb hs.le hw
    nlinarith only [h]

/-- For odd nonsquare n with log n>=255 under GRH, an odd negative Jacobi prime
exists through (9999/10000)(log n)^2. Extract the least witness from the
common-endpoint bound. This proves the improved entrance for all larger inputs. -/
theorem exists_prime_neg_one_witness_le_joint_entrance_log_255 {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 255 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n p = -1 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hm := NumberTheory.primeNegOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNegOneWitness n hw, hm.1, hm.2.1,
      primeNegOneWitness_cast_le_joint_entrance_endpoint hn hns hGRH hL (le_refl _) hw, hm.2.2⟩

/-- Under the same input and GRH hypotheses, an odd non-one Jacobi prime obeys
the log-255 bound. Its constructed value is minus one, so zero is not needed. -/
theorem exists_prime_ne_one_witness_le_joint_entrance_log_255 {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 255 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_neg_one_witness_le_joint_entrance_log_255 hn hns hGRH hL
  refine ⟨p, hp, ho, hb, ?_⟩
  rw [hv]
  norm_num only

/-- For odd nonsquare n and log n>=255 under GRH, the least non-one odd-prime
witness is at most (9999/10000)(log n)^2 and strictly below (log n)^2.
Use leastness and positivity of the squared logarithm. -/
theorem primeNeOneWitness_bound_joint_entrance_log_255 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 255 ≤ Real.log n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
      (NumberTheory.primeNeOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_ne_one_witness_le_joint_entrance_log_255 hn hns hGRH hL
  have h := (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb
  have hs := sq_pos_of_pos (show 0 < Real.log n by linarith only [hL])
  exact ⟨h, by nlinarith only [h, hs]⟩

/-- Under GRH and log B>=255, QNegOne(B) obeys the coefficient-9999/10000
bound and is strictly below (log B)^2. The common-endpoint theorem includes
every smaller odd nonsquare input; no finite input certificate is used. -/
theorem QNegOne_bound_joint_entrance_log_255 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 255 ≤ Real.log B) :
    (QNegOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 ∧
      (QNegOne B : ℝ) < (Real.log B) ^ 2 := by
  have h : (QNegOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 := by
    apply
      QNegOne_cast_le_of_forall
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 9999 / 10000) (sq_nonneg _))
    intro n hn
    have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
    exact
      primeNegOneWitness_cast_le_joint_entrance_endpoint ha.odd ha.not_isSquare hGRH hL
        (Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le))
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)
  have hs := sq_pos_of_pos (show 0 < Real.log B by linarith only [hL])
  exact ⟨h, by nlinarith only [h, hs]⟩

/-- Under GRH and log B>=255, QNeOne(B) satisfies the same strict square-log
bound. Transfer the negative maximum theorem through QNeOne<=QNegOne. -/
theorem QNeOne_bound_joint_entrance_log_255 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 255 ≤ Real.log B) :
    (QNeOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 ∧ (QNeOne B : ℝ) < (Real.log B) ^ 2 := by
  have h := QNegOne_bound_joint_entrance_log_255 hGRH hL
  have hc : (QNeOne B : ℝ) ≤ QNegOne B := Nat.cast_le.mpr (QNeOne_le_QNegOne B)
  exact ⟨hc.trans h.1, hc.trans_lt h.2⟩

end PseudoPrime.PseudoSquare
