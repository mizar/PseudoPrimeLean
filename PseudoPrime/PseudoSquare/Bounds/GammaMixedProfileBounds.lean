/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaMixedProfileSeparation
public import PseudoPrime.PseudoSquare.Bounds.GammaFactorFreeBounds

/-! # Quadratic prime witnesses on the certified logarithmic cell [300,310] -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: 300<=L<=310. Claim: the quadratic scale and prefix meet the general witness criterion.
Proof: square comparisons and exact endpoint identity. Role: reuse scalar-cell admissibility. -/
theorem gamma_mixed_profile_inputs_300_310 {L : ℝ} (hlo : 300 ≤ L) (hhi : L ≤ 310) :
    4096 ≤ (2 / 5 : ℝ) * L ^ 2 ∧
      1 ≤ (99 / 100 : ℝ) * L ^ 2 ∧
      (99 / 100 : ℝ) * L ^ 2 ≤ (99 / 40 : ℝ) * ((2 / 5 : ℝ) * L ^ 2) := by
  have hx := (LLS.gamma_mixed_profile_geometry_300_310 hlo hhi).1
  have hsq := mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ L + 300 by linarith only [hlo])
  refine ⟨by linarith only [hx], by nlinarith only [hsq], ?_⟩
  exact le_of_eq (by ring)

/-- Input: GRH, odd nonsquare n, log n<=L and 300<=L<=310.
Claim: an odd-prime negative Jacobi witness exists through (99/100)L^2.
Proof: apply the fully certified factor-free separation.
Role: turn the mixed arithmetic certificate into an actual prime witness. -/
theorem exists_prime_neg_one_witness_mixed_300_310 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hlo : 300 ≤ L)
    (hhi : L ≤ 310) (hlog : Real.log n ≤ L) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ (q : ℝ) ≤ (99 / 100 : ℝ) * L ^ 2 ∧ jacobiSym n q = -1 := by
  obtain ⟨hx, hb, hbx⟩ := gamma_mixed_profile_inputs_300_310 hlo hhi
  have hs := LLS.gamma_factor_free_separation_300_310 hGRH.riemann hlo hhi
  obtain ⟨q, hq, ho, hbound, hv⟩ :=
    exists_prime_neg_one_witness_of_factor_free_separation hn hns hGRH (by linarith only [hlo]) hlog
      hx hb hbx hs
  exact ⟨q, hq, ho, by nlinarith only [hbound], hv⟩

/-- Input: GRH, odd nonsquare n with 300<=log n<=310, and the least-witness set's nonemptiness.
Claim: the least odd-prime negative witness is <=(99/100)(log n)^2 and <(log n)^2.
Proof: minimize the certified prime witness. Role: expose the improved analytic cell publicly. -/
theorem primeNegOneWitness_bound_mixed_300_310 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : 300 ≤ Real.log n)
    (hhi : Real.log n ≤ 310) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
      (NumberTheory.primeNegOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨q, hq, ho, hbound, hv⟩ :=
    exists_prime_neg_one_witness_mixed_300_310 hn hns hGRH hlo hhi (le_refl _)
  have h := (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hq, ho, hv⟩)).trans hbound
  exact ⟨h, by nlinarith only [h, sq_pos_of_pos (show 0 < Real.log n by linarith only [hlo])]⟩

/-- Input: the same GRH and input cell, with the non-one witness set nonempty.
Claim: the least odd-prime non-one witness has both stated square-log bounds.
Proof: use the negative witness as a non-one witness. Role: cover both quadratic witness kinds. -/
theorem primeNeOneWitness_bound_mixed_300_310 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : 300 ≤ Real.log n)
    (hhi : Real.log n ≤ 310) (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
      (NumberTheory.primeNeOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨q, hq, ho, hbound, hv⟩ :=
    exists_prime_neg_one_witness_mixed_300_310 hn hns hGRH hlo hhi (le_refl _)
  have hne : jacobiSym n q ≠ 1 := by
    rw [hv]; norm_num only
  have h := (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hq, ho, hne⟩)).trans hbound
  exact ⟨h, by nlinarith only [h, sq_pos_of_pos (show 0 < Real.log n by linarith only [hlo])]⟩

/-- Input: GRH and an integer endpoint B with 300<=log B<=310.
Claim: the full negative-witness maximum through B has both square-log endpoint bounds.
Proof: use the common scalar separation for every admissible n<=B.
Role: include smaller inputs without an input enumeration certificate. -/
theorem QNegOne_bound_mixed_300_310 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : 300 ≤ Real.log B)
    (hhi : Real.log B ≤ 310) :
    (QNegOne B : ℝ) ≤ (99 / 100 : ℝ) * (Real.log B) ^ 2 ∧ (QNegOne B : ℝ) < (Real.log B) ^ 2 := by
  obtain ⟨hx, hb, hbx⟩ := gamma_mixed_profile_inputs_300_310 hlo hhi
  have hs := LLS.gamma_factor_free_separation_300_310 hGRH.riemann hlo hhi
  have h := QNegOne_le_of_factor_free_separation hGRH (by linarith only [hlo]) hx hb hbx hs
  have hle : (QNegOne B : ℝ) ≤ (99 / 100 : ℝ) * (Real.log B) ^ 2 := by nlinarith only [h]
  exact ⟨hle, by nlinarith only [hle, sq_pos_of_pos (show 0 < Real.log B by linarith only [hlo])]⟩

/-- Input: GRH and 300<=log B<=310. Claim: the full non-one maximum through B has
both square-log endpoint bounds. Proof: compare the two finite maxima.
Role: expose the complete non-one endpoint bound on the certified cell. -/
theorem QNeOne_bound_mixed_300_310 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : 300 ≤ Real.log B)
    (hhi : Real.log B ≤ 310) :
    (QNeOne B : ℝ) ≤ (99 / 100 : ℝ) * (Real.log B) ^ 2 ∧ (QNeOne B : ℝ) < (Real.log B) ^ 2 := by
  have hn := QNegOne_bound_mixed_300_310 hGRH hlo hhi
  have hc : (QNeOne B : ℝ) ≤ QNegOne B := Nat.cast_le.mpr (QNeOne_le_QNegOne B)
  exact ⟨hc.trans hn.1, hc.trans_lt hn.2⟩

end PseudoPrime.PseudoSquare
