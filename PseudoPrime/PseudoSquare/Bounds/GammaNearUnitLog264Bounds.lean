/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaLog264Bounds
public import PseudoPrime.PseudoSquare.Bounds.GammaNearUnitLog265Bounds

/-! # Quadratic prime-witness bounds on the full logarithmic half-line starting at 264 -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: L>=264. Claim: the quadratic scale and prefix satisfy the general witness criterion.
Proof: compare squares and normalize the exact profile endpoint. Role: half-line admissibility. -/
theorem gamma_near_unit_profile_inputs_of_log_ge_264 {L : ℝ} (hlo : 264 ≤ L) :
    4096 ≤ (101 / 250 : ℝ) * L ^ 2 ∧
      1 ≤ (9999 / 10000 : ℝ) * L ^ 2 ∧
      (9999 / 10000 : ℝ) * L ^ 2 ≤ (99 / 40 : ℝ) * ((101 / 250 : ℝ) * L ^ 2) := by
  have hsq := mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ L + 264 by linarith only [hlo])
  refine ⟨by nlinarith only [hsq], by nlinarith only [hsq], ?_⟩
  exact le_of_eq (by ring)

/-- Input: GRH, odd nonsquare n, L>=264, log n<=L and a nonempty least-witness set.
Claim: the least negative odd-prime witness is at most (9999/10000)L^2.
Proof: use the asymmetric-prefix bridge through 265 and the established half-line beyond it.
Role: lower the common-endpoint entrance without enumerating inputs. -/
theorem primeNegOneWitness_cast_le_nearUnit_log_264_endpoint {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : 264 ≤ L) (hlog : Real.log n ≤ L) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * L ^ 2 := by
  by_cases h265 : 265 ≤ L
  · exact primeNegOneWitness_cast_le_nearUnit_log_265_endpoint hn hns hGRH h265 hlog hw
  · obtain ⟨hx, hb, hbx⟩ := gamma_near_unit_profile_inputs_of_log_ge_264 hL
    have hs := LLS.gamma_log264_separation_264_265 hGRH.riemann hL (lt_of_not_ge h265).le
    have h :=
      primeNegOneWitness_cast_le_of_factor_free_separation hn hns hGRH (by linarith only [hL]) hlog
        hx hb hbx hs hw
    nlinarith only [h]

/-- Input: GRH, odd nonsquare n and log n>=264.
Claim: an odd-prime negative Jacobi witness exists through (9999/10000)(log n)^2.
Proof: combine least-witness membership with the common-endpoint bound.
Role: expose the actual prime witness under the improved half-line entrance. -/
theorem exists_prime_neg_one_witness_le_nearUnit_log_264 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 264 ≤ Real.log n) :
    ∃ q : ℕ,
      q.Prime ∧ Odd q ∧ (q : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n q = -1 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hm := NumberTheory.primeNegOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNegOneWitness n hw, hm.1, hm.2.1,
      primeNegOneWitness_cast_le_nearUnit_log_264_endpoint hn hns hGRH hL (le_refl _) hw, hm.2.2⟩

/-- Input: GRH, odd nonsquare n with log n>=264 and a nonempty least-negative set.
Claim: the least odd-prime negative witness obeys <=(9999/10000)(log n)^2<(log n)^2.
Proof: specialize the common endpoint to log n. Role: public least-negative half-line bound. -/
theorem primeNegOneWitness_bound_nearUnit_log_264 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 264 ≤ Real.log n)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
      (NumberTheory.primeNegOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  have h := primeNegOneWitness_cast_le_nearUnit_log_264_endpoint hn hns hGRH hL (le_refl _) hw
  exact ⟨h, by nlinarith only [h, sq_pos_of_pos (show 0 < Real.log n by linarith only [hL])]⟩

/-- Input: GRH, odd nonsquare n with log n>=264 and a nonempty least-non-one set.
Claim: the least odd-prime non-one witness has both stated square-log bounds.
Proof: use a negative witness as a non-one witness. Role: cover both quadratic witness kinds. -/
theorem primeNeOneWitness_bound_nearUnit_log_264 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 264 ≤ Real.log n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
      (NumberTheory.primeNeOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨q, hq, ho, hbound, hv⟩ := exists_prime_neg_one_witness_le_nearUnit_log_264 hn hns hGRH hL
  have hne : jacobiSym n q ≠ 1 := by
    rw [hv]; norm_num only
  have h := (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hq, ho, hne⟩)).trans hbound
  exact ⟨h, by nlinarith only [h, sq_pos_of_pos (show 0 < Real.log n by linarith only [hL])]⟩

/-- Input: GRH and log B>=264. Claim: the full negative-witness maximum is bounded by
(9999/10000)(log B)^2 and strictly by (log B)^2. Proof: bound every admissible input at
the common endpoint log B. Role: include smaller inputs in the half-line maximum bound. -/
theorem QNegOne_bound_nearUnit_log_264 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 264 ≤ Real.log B) :
    (QNegOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 ∧
      (QNegOne B : ℝ) < (Real.log B) ^ 2 := by
  have hle : (QNegOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 := by
    apply
      QNegOne_cast_le_of_forall
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 9999 / 10000) (sq_nonneg _))
    intro n hn
    have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
    exact
      primeNegOneWitness_cast_le_nearUnit_log_264_endpoint ha.odd ha.not_isSquare hGRH hL
        (Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le))
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)
  exact ⟨hle, by nlinarith only [hle, sq_pos_of_pos (show 0 < Real.log B by linarith only [hL])]⟩

/-- Input: GRH and log B>=264. Claim: the full non-one-witness maximum has both bounds.
Proof: compare it with the negative-witness maximum. Role: expose the second quadratic maximum. -/
theorem QNeOne_bound_nearUnit_log_264 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 264 ≤ Real.log B) :
    (QNeOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 ∧ (QNeOne B : ℝ) < (Real.log B) ^ 2 := by
  have hn := QNegOne_bound_nearUnit_log_264 hGRH hL
  have hc : (QNeOne B : ℝ) ≤ QNegOne B := Nat.cast_le.mpr (QNeOne_le_QNegOne B)
  exact ⟨hc.trans hn.1, hc.trans_lt hn.2⟩

end PseudoPrime.PseudoSquare
