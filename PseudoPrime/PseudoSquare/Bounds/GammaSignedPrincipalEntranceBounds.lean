/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSignedPrincipalEntranceCertificates
public import PseudoPrime.PseudoSquare.Bounds.GammaNearUnitLog264Bounds
public import PseudoPrime.PseudoSquare.Bounds.GammaSignedVariationBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaFactorFreeBounds

/-! # Quadratic witness bounds on the half-line starting at log 260 -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH and the displayed scale, prefix and signed-principal margin
conditions, the stated pointwise witness or common-endpoint maximum bound follows.
Use the character-free comparison and minimize or maximize as indicated.
Role: expose the improved principal estimate independently of a logarithmic profile. -/
theorem exists_prime_neg_one_witness_of_signed_principal_factor_free_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaSignedPrincipalFactorFreeSeparation L b x) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  let Q := max 20000 (4 * n)
  have hQ : 20000 ≤ Q := le_max_left _ _
  have hnQ : 4 * n ≤ Q := le_max_right _ _
  have hlogQ := LLS.gamma_log_pole_level_le_of_common_endpoint hn hL hlog
  have hs :=
    LLS.gamma_signed_principal_separation_le_joint_add_small_scale (Q := Q) (b := b) hn hns hlog hx
      hlogQ
  have hg :
    0 ≤
      LLS.gammaJointPrefixSeparationWithPrincipalCap Q (NumberTheory.complexQuadraticCharacter n hn)
        b x (-3 / 2) (LLS.gammaSignedVariationPrincipalCap x) := by
    linarith only [hs, hgap]
  exact
    exists_prime_neg_one_witness_of_signed_principal_separation hn hns hQ hnQ hGRH
      (by linarith only [hx]) hb hbx hg

/-- Under GRH and the displayed scale, prefix and signed-principal margin
conditions, the stated pointwise witness or common-endpoint maximum bound follows.
Use the character-free comparison and minimize or maximize as indicated.
Role: expose the improved principal estimate independently of a logarithmic profile. -/
theorem primeNegOneWitness_cast_le_of_signed_principal_factor_free_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaSignedPrincipalFactorFreeSeparation L b x)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_signed_principal_factor_free_separation hn hns hGRH hL hlog hx
      hb hbx hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpb

/-- Under GRH and the displayed scale, prefix and signed-principal margin
conditions, the stated pointwise witness or common-endpoint maximum bound follows.
Use the character-free comparison and minimize or maximize as indicated.
Role: expose the improved principal estimate independently of a logarithmic profile. -/
theorem exists_prime_ne_one_witness_of_signed_principal_factor_free_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaSignedPrincipalFactorFreeSeparation L b x) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_signed_principal_factor_free_separation hn hns hGRH hL hlog hx
      hb hbx hgap
  refine ⟨p, hp, ho, hpb, ?_⟩
  rw [hv]
  norm_num only

/-- Under GRH and the displayed scale, prefix and signed-principal margin
conditions, the stated pointwise witness or common-endpoint maximum bound follows.
Use the character-free comparison and minimize or maximize as indicated.
Role: expose the improved principal estimate independently of a logarithmic profile. -/
theorem QNegOne_le_of_signed_principal_factor_free_separation {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x : ℝ} (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaSignedPrincipalFactorFreeSeparation (Real.log B) b x) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply
    QNegOne_cast_le_of_forall
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (by linarith only [hx]))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_of_signed_principal_factor_free_separation ha.odd ha.not_isSquare
      hGRH hB (Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le)) hx hb hbx hgap
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- Under GRH and the displayed scale, prefix and signed-principal margin
conditions, the stated pointwise witness or common-endpoint maximum bound follows.
Use the character-free comparison and minimize or maximize as indicated.
Role: expose the improved principal estimate independently of a logarithmic profile. -/
theorem QNeOne_le_of_signed_principal_factor_free_separation {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x : ℝ} (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaSignedPrincipalFactorFreeSeparation (Real.log B) b x) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  exact
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans
      (QNegOne_le_of_signed_principal_factor_free_separation hGRH hB hx hb hbx hgap)

/-- Input: L >= 260. Claim: the prescribed scale and prefix are admissible.
Compare squares and normalize the exact ramp endpoint. Role: supply geometry
for the common-endpoint half-line theorem without finite input enumeration. -/
theorem gamma_near_unit_profile_inputs_of_log_ge_260 {L : ℝ} (hlo : 260 ≤ L) :
    4096 ≤ (101 / 250 : ℝ) * L ^ 2 ∧
      1 ≤ (9999 / 10000 : ℝ) * L ^ 2 ∧
      (9999 / 10000 : ℝ) * L ^ 2 ≤ (99 / 40 : ℝ) * ((101 / 250 : ℝ) * L ^ 2) := by
  have hsq := mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ L + 260 by linarith only [hlo])
  refine ⟨by nlinarith only [hsq], by nlinarith only [hsq], ?_⟩
  exact le_of_eq (by ring)

/-- Under GRH and the displayed odd-nonsquare or maximum-endpoint hypotheses,
the stated coefficient-9999/10000 bound holds from logarithmic level 260.
Use the three new analytic cells below 264 and the established half-line above it.
Role: export the improved entrance to pointwise, least or finite-maximum witnesses. -/
theorem primeNegOneWitness_cast_le_signedPrincipal_log_260_endpoint {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : 260 ≤ L) (hlog : Real.log n ≤ L) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * L ^ 2 := by
  by_cases h264 : 264 ≤ L
  · exact primeNegOneWitness_cast_le_nearUnit_log_264_endpoint hn hns hGRH h264 hlog hw
  · obtain ⟨hx, hb, hbx⟩ := gamma_near_unit_profile_inputs_of_log_ge_260 hL
    have hs := LLS.gamma_signed_principal_separation_260_264 hGRH.riemann hL (lt_of_not_ge h264).le
    have h :=
      primeNegOneWitness_cast_le_of_signed_principal_factor_free_separation hn hns hGRH
        (by linarith only [hL]) hlog hx hb hbx hs hw
    nlinarith only [h]

/-- Under GRH and the displayed odd-nonsquare or maximum-endpoint hypotheses,
the stated coefficient-9999/10000 bound holds from logarithmic level 260.
Use the three new analytic cells below 264 and the established half-line above it.
Role: export the improved entrance to pointwise, least or finite-maximum witnesses. -/
theorem exists_prime_neg_one_witness_le_signedPrincipal_log_260 {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 260 ≤ Real.log n) :
    ∃ q : ℕ,
      q.Prime ∧ Odd q ∧ (q : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n q = -1 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hm := NumberTheory.primeNegOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNegOneWitness n hw, hm.1, hm.2.1,
      primeNegOneWitness_cast_le_signedPrincipal_log_260_endpoint hn hns hGRH hL (le_refl _) hw,
      hm.2.2⟩

/-- Under GRH and the displayed odd-nonsquare or maximum-endpoint hypotheses,
the stated coefficient-9999/10000 bound holds from logarithmic level 260.
Use the three new analytic cells below 264 and the established half-line above it.
Role: export the improved entrance to pointwise, least or finite-maximum witnesses. -/
theorem primeNegOneWitness_bound_signedPrincipal_log_260 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 260 ≤ Real.log n)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
      (NumberTheory.primeNegOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  have h :=
    primeNegOneWitness_cast_le_signedPrincipal_log_260_endpoint hn hns hGRH hL (le_refl _) hw
  exact ⟨h, by nlinarith only [h, sq_pos_of_pos (show 0 < Real.log n by linarith only [hL])]⟩

/-- Under GRH and the displayed odd-nonsquare or maximum-endpoint hypotheses,
the stated coefficient-9999/10000 bound holds from logarithmic level 260.
Use the three new analytic cells below 264 and the established half-line above it.
Role: export the improved entrance to pointwise, least or finite-maximum witnesses. -/
theorem primeNeOneWitness_bound_signedPrincipal_log_260 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 260 ≤ Real.log n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
      (NumberTheory.primeNeOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨q, hq, ho, hbound, hv⟩ :=
    exists_prime_neg_one_witness_le_signedPrincipal_log_260 hn hns hGRH hL
  have hne : jacobiSym n q ≠ 1 := by
    rw [hv]; norm_num only
  have h := (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hq, ho, hne⟩)).trans hbound
  exact ⟨h, by nlinarith only [h, sq_pos_of_pos (show 0 < Real.log n by linarith only [hL])]⟩

/-- Under GRH and the displayed odd-nonsquare or maximum-endpoint hypotheses,
the stated coefficient-9999/10000 bound holds from logarithmic level 260.
Use the three new analytic cells below 264 and the established half-line above it.
Role: export the improved entrance to pointwise, least or finite-maximum witnesses. -/
theorem QNegOne_bound_signedPrincipal_log_260 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 260 ≤ Real.log B) :
    (QNegOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 ∧
      (QNegOne B : ℝ) < (Real.log B) ^ 2 := by
  have hle : (QNegOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 := by
    apply
      QNegOne_cast_le_of_forall
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 9999 / 10000) (sq_nonneg _))
    intro n hn
    have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
    exact
      primeNegOneWitness_cast_le_signedPrincipal_log_260_endpoint ha.odd ha.not_isSquare hGRH hL
        (Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le))
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)
  exact ⟨hle, by nlinarith only [hle, sq_pos_of_pos (show 0 < Real.log B by linarith only [hL])]⟩

/-- Under GRH and the displayed odd-nonsquare or maximum-endpoint hypotheses,
the stated coefficient-9999/10000 bound holds from logarithmic level 260.
Use the three new analytic cells below 264 and the established half-line above it.
Role: export the improved entrance to pointwise, least or finite-maximum witnesses. -/
theorem QNeOne_bound_signedPrincipal_log_260 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 260 ≤ Real.log B) :
    (QNeOne B : ℝ) ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 ∧ (QNeOne B : ℝ) < (Real.log B) ^ 2 := by
  have hn := QNegOne_bound_signedPrincipal_log_260 hGRH hL
  have hc : (QNeOne B : ℝ) ≤ QNegOne B := Nat.cast_le.mpr (QNeOne_le_QNegOne B)
  exact ⟨hc.trans hn.1, hc.trans_lt hn.2⟩

end PseudoPrime.PseudoSquare
