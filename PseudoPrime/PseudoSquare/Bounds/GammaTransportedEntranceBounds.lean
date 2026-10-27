/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaTransportedEntranceBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaSignedPrincipalEntranceBounds

/-! # Quadratic witnesses from log 519/2 by transporting existing rows -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: an odd nonsquare n, GRH, L>=2591/10 and log(n)<=L. Claim: the
least negative odd-prime witness is at most (9999/10000)L^2. Below 260 apply
the transported separation, then use the established bound above 260.
Role: include every smaller input in the finite-maximum bound. -/
theorem primeNegOneWitness_cast_le_base_ratio_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 2591 / 10 ≤ L)
    (hlog : Real.log n ≤ L) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * L ^ 2 := by
  by_cases h260 : 260 ≤ L
  · exact primeNegOneWitness_cast_le_signedPrincipal_log_260_endpoint hn hns hGRH h260 hlog hw
  · obtain ⟨hlo, hhi, hx, hb⟩ :=
      LLS.gamma_transported_profile_inputs hL (le_of_lt (lt_of_not_ge h260))
    have hs := LLS.gamma_transported_separation hGRH.riemann hL (le_of_lt (lt_of_not_ge h260))
    have h :=
      primeNegOneWitness_cast_le_of_retained_common_factor_free_separation hn hns hGRH
        (by linarith only [hL]) hlog hx (by norm_num only : (1 : ℝ) ≤ 50000) hb hs.le hw
    nlinarith only [h]

/-- Input: the former log-519/2 endpoint assumptions. Claim: the same bound
holds. Apply the stronger base-sensitive entrance theorem.
Role: preserve the existing public interface. -/
theorem primeNegOneWitness_cast_le_transported_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 519 / 2 ≤ L)
    (hlog : Real.log n ≤ L) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * L ^ 2 := by
  exact primeNegOneWitness_cast_le_base_ratio_endpoint hn hns hGRH (by linarith only [hL]) hlog hw

/-- Input: GRH and the displayed odd-nonsquare or common-endpoint hypotheses
from logarithmic level 519/2. Claim: the coefficient-9999/10000 witness or
maximum bound holds. Apply the transported common-endpoint theorem and the
existing minimization/maximum interfaces. Role: expose the improved half-line. -/
theorem exists_prime_neg_one_witness_le_transported_log_519_div_two {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 519 / 2 ≤ Real.log n) :
    ∃ q : ℕ,
      q.Prime ∧ Odd q ∧ (q : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n q = -1 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hm := NumberTheory.primeNegOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNegOneWitness n hw, hm.1, hm.2.1,
      primeNegOneWitness_cast_le_transported_endpoint hn hns hGRH hL (le_refl _) hw, hm.2.2⟩

/-- Input: GRH and the displayed odd-nonsquare or common-endpoint hypotheses
from logarithmic level 519/2. Claim: the coefficient-9999/10000 witness or
maximum bound holds. Apply the transported common-endpoint theorem and the
existing minimization/maximum interfaces. Role: expose the improved half-line. -/
theorem primeNegOneWitness_bound_transported_log_519_div_two {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 519 / 2 ≤ Real.log n) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
      (NumberTheory.primeNegOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  have h := primeNegOneWitness_cast_le_transported_endpoint hn hns hGRH hL (le_refl _) hw
  exact ⟨h, by nlinarith only [h, sq_pos_of_pos (show 0 < Real.log n by linarith only [hL])]⟩

/-- Input: GRH and the displayed odd-nonsquare or common-endpoint hypotheses
from logarithmic level 519/2. Claim: the coefficient-9999/10000 witness or
maximum bound holds. Apply the transported common-endpoint theorem and the
existing minimization/maximum interfaces. Role: expose the improved half-line. -/
theorem primeNeOneWitness_bound_transported_log_519_div_two {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 519 / 2 ≤ Real.log n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
      (NumberTheory.primeNeOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨q, hq, ho, hbound, hv⟩ :=
    exists_prime_neg_one_witness_le_transported_log_519_div_two hn hns hGRH hL
  have hne : jacobiSym n q ≠ 1 := by
    rw [hv]; norm_num only
  have h := (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hq, ho, hne⟩)).trans hbound
  exact ⟨h, by nlinarith only [h, sq_pos_of_pos (show 0 < Real.log n by linarith only [hL])]⟩

/-- Input: GRH and the displayed odd-nonsquare or common-endpoint hypotheses
from logarithmic level 519/2. Claim: the coefficient-9999/10000 witness or
maximum bound holds. Apply the transported common-endpoint theorem and the
existing minimization/maximum interfaces. Role: expose the improved half-line. -/
theorem QNegOne_bound_transported_log_519_div_two {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 519 / 2 ≤ Real.log B) :
    (QNegOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 ∧
      (QNegOne B : ℝ) < (Real.log B) ^ 2 := by
  have hle : (QNegOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 := by
    apply
      QNegOne_cast_le_of_forall
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 9999 / 10000) (sq_nonneg _))
    intro n hn
    have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
    exact
      primeNegOneWitness_cast_le_transported_endpoint ha.odd ha.not_isSquare hGRH hL
        (Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le))
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)
  exact ⟨hle, by nlinarith only [hle, sq_pos_of_pos (show 0 < Real.log B by linarith only [hL])]⟩

/-- Input: GRH and the displayed odd-nonsquare or common-endpoint hypotheses
from logarithmic level 519/2. Claim: the coefficient-9999/10000 witness or
maximum bound holds. Apply the transported common-endpoint theorem and the
existing minimization/maximum interfaces. Role: expose the improved half-line. -/
theorem QNeOne_bound_transported_log_519_div_two {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 519 / 2 ≤ Real.log B) :
    (QNeOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 ∧ (QNeOne B : ℝ) < (Real.log B) ^ 2 := by
  have hn := QNegOne_bound_transported_log_519_div_two hGRH hL
  have hc : (QNeOne B : ℝ) ≤ QNegOne B := Nat.cast_le.mpr (QNeOne_le_QNegOne B)
  exact ⟨hc.trans hn.1, hc.trans_lt hn.2⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Input: GRH and the displayed odd-nonsquare or common-endpoint hypotheses
from logarithmic level 2591/10. Claim: the coefficient-9999/10000 witness or
maximum bound holds. Apply the transported common-endpoint theorem and the
existing minimization/maximum interfaces. Role: expose the improved half-line. -/
theorem exists_prime_neg_one_witness_le_base_ratio_log_2591_div_ten {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 2591 / 10 ≤ Real.log n) :
    ∃ q : ℕ,
      q.Prime ∧ Odd q ∧ (q : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n q = -1 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hm := NumberTheory.primeNegOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNegOneWitness n hw, hm.1, hm.2.1,
      primeNegOneWitness_cast_le_base_ratio_endpoint hn hns hGRH hL (le_refl _) hw, hm.2.2⟩

/-- Input: GRH and the displayed odd-nonsquare or common-endpoint hypotheses
from logarithmic level 2591/10. Claim: the coefficient-9999/10000 witness or
maximum bound holds. Apply the transported common-endpoint theorem and the
existing minimization/maximum interfaces. Role: expose the improved half-line. -/
theorem primeNegOneWitness_bound_base_ratio_log_2591_div_ten {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 2591 / 10 ≤ Real.log n) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
      (NumberTheory.primeNegOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  have h := primeNegOneWitness_cast_le_base_ratio_endpoint hn hns hGRH hL (le_refl _) hw
  exact ⟨h, by nlinarith only [h, sq_pos_of_pos (show 0 < Real.log n by linarith only [hL])]⟩

/-- Input: GRH and the displayed odd-nonsquare or common-endpoint hypotheses
from logarithmic level 2591/10. Claim: the coefficient-9999/10000 witness or
maximum bound holds. Apply the transported common-endpoint theorem and the
existing minimization/maximum interfaces. Role: expose the improved half-line. -/
theorem primeNeOneWitness_bound_base_ratio_log_2591_div_ten {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 2591 / 10 ≤ Real.log n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
      (NumberTheory.primeNeOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨q, hq, ho, hbound, hv⟩ :=
    exists_prime_neg_one_witness_le_base_ratio_log_2591_div_ten hn hns hGRH hL
  have hne : jacobiSym n q ≠ 1 := by
    rw [hv]; norm_num only
  have h := (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hq, ho, hne⟩)).trans hbound
  exact ⟨h, by nlinarith only [h, sq_pos_of_pos (show 0 < Real.log n by linarith only [hL])]⟩

/-- Input: GRH and the displayed odd-nonsquare or common-endpoint hypotheses
from logarithmic level 2591/10. Claim: the coefficient-9999/10000 witness or
maximum bound holds. Apply the transported common-endpoint theorem and the
existing minimization/maximum interfaces. Role: expose the improved half-line. -/
theorem QNegOne_bound_base_ratio_log_2591_div_ten {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 2591 / 10 ≤ Real.log B) :
    (QNegOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 ∧
      (QNegOne B : ℝ) < (Real.log B) ^ 2 := by
  have hle : (QNegOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 := by
    apply
      QNegOne_cast_le_of_forall
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 9999 / 10000) (sq_nonneg _))
    intro n hn
    have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
    exact
      primeNegOneWitness_cast_le_base_ratio_endpoint ha.odd ha.not_isSquare hGRH hL
        (Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le))
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)
  exact ⟨hle, by nlinarith only [hle, sq_pos_of_pos (show 0 < Real.log B by linarith only [hL])]⟩

/-- Input: GRH and the displayed odd-nonsquare or common-endpoint hypotheses
from logarithmic level 2591/10. Claim: the coefficient-9999/10000 witness or
maximum bound holds. Apply the transported common-endpoint theorem and the
existing minimization/maximum interfaces. Role: expose the improved half-line. -/
theorem QNeOne_bound_base_ratio_log_2591_div_ten {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 2591 / 10 ≤ Real.log B) :
    (QNeOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 ∧ (QNeOne B : ℝ) < (Real.log B) ^ 2 := by
  have hn := QNegOne_bound_base_ratio_log_2591_div_ten hGRH hL
  have hc : (QNeOne B : ℝ) ≤ QNegOne B := Nat.cast_le.mpr (QNeOne_le_QNegOne B)
  exact ⟨hc.trans hn.1, hc.trans_lt hn.2⟩

end PseudoPrime.PseudoSquare
