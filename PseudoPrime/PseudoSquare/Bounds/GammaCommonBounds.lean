/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.LogScaleBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaMixedLog290Bounds
public import PseudoPrime.PseudoSquare.Bounds.GammaPrincipalEulerNonOneBounds
public import PseudoPrime.LLS.GammaQuadraticUniformBounds

/-! # Gamma witness maxima at common logarithmic scales

These candidates reuse already certified real-scale witness estimates. Their selected
coefficients and entrances stay with the quadratic-witness consumers. A non-one estimate
is kept separate from a negative estimate and is never transferred in the opposite direction.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The mixed negative-witness candidate with a common scale of at least 290.
Input: any natural endpoint. Output: 99/100 times the squared larger logarithmic scale.
Role: cover earlier inputs without restricting the candidate to an endpoint guard. -/
noncomputable def mixedScaleBound (B : ℕ) : ℝ :=
  logScaleBound (99 / 100) 290 B

/-- The principal-even non-one candidate with a common scale of at least 22221.
Input: any natural endpoint. Output: four fifths times the squared larger scale.
Role: retain the dedicated factor-detecting branch rather than use a negative-only estimate. -/
noncomputable def neOneScaleBound (B : ℕ) : ℝ :=
  logScaleBound (4 / 5) 22221 B

/-- Under GRH every negative witness maximum obeys the common 290-scale estimate.
Input: any natural endpoint and GRH. Claim: the complete maximum is bounded.
Proof: lift the existing mixed common-endpoint least-witness theorem.
Role: remove the unnecessary pointwise entrance from cumulative candidate selection. -/
theorem QNegOne_le_mixed_scale (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ mixedScaleBound B :=
  QNegOne_le_logScaleBound (by norm_num only : (0 : ℝ) ≤ 99 / 100)
    (fun {_n} hn hns {_L} hL hlog hw ↦
      negOneWitness_cast_le_mixed_log_290_endpoint hn hns hGRH hL hlog hw)
    B

/-- Under GRH every non-one witness maximum obeys the common principal-even estimate.
Input: any natural endpoint and GRH. Claim: the complete non-one maximum is bounded.
Proof: lift the existing least-witness theorem at a common real endpoint.
Role: supply a candidate valid below its pointwise entrance without conflating witness kinds. -/
theorem QNeOne_le_principal_scale (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ neOneScaleBound B :=
  QNeOne_le_logScaleBound (by norm_num only : (0 : ℝ) ≤ 4 / 5)
    (fun {_n} hn hns {_L} hL hlog hw ↦
      neOneWitness_le_gammaPrincipalEven_GRH hGRH hn hns hL hlog hw)
    B

/-- Below level twenty thousand, the elementary radius is at most ninety squared.
Input: a positive natural input below that original-level cutoff.
Claim: the existing elementary expression fits a small fixed scalar allowance.
Proof: compare the level with two to the fifteenth and bound both logarithms.
Role: cover small levels in a free common-scale Gamma witness theorem. -/
private theorem gamma_small_radius_bound {n : ℕ} (hn : 0 < n) (hq : 4 * n < 20000) :
    elementaryRadius n ≤ (90 : ℝ) ^ 2 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlevel : 0 < 4 * (n : ℝ) := mul_pos (by norm_num only) hnR
  have hfour : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num only, Real.log_pow]
    norm_num only
    linarith only [Real.log_two_gt_d9]
  have hlo : 1 ≤ Real.log (4 * (n : ℝ)) :=
    hfour.trans
      (Real.log_le_log (by norm_num only : (0 : ℝ) < 4)
        ((le_of_eq (mul_one (4 : ℝ)).symm).trans
          (mul_le_mul_of_nonneg_left (Nat.one_le_cast.mpr hn) (by norm_num only : (0 : ℝ) ≤ 4))))
  have hhi : Real.log (4 * (n : ℝ)) ≤ 15 := by
    have hqR : 4 * (n : ℝ) ≤ (2 : ℝ) ^ 15 := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        (Nat.cast_le (α := ℝ)).mpr (hq.le.trans (by norm_num only : 20000 ≤ (2 : ℕ) ^ 15))
    have h := Real.log_le_log hlevel hqR
    rw [Real.log_pow] at h
    norm_num only at h
    linarith only [h, Real.log_two_lt_d9]
  have hll := Real.log_le_self (zero_le_one.trans hlo)
  have hll0 := Real.log_nonneg hlo
  have hroot0 :
    0 ≤ Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3 := by
    linarith only [hlo, hll0]
  have hroot :
    Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3 ≤ 90 := by
    linarith only [hhi, hll]
  exact (sq_le_sq₀ hroot0 (by norm_num only : (0 : ℝ) ≤ 90)).mpr hroot

/-- The existing smoothed comparison gives an actual witness at a free common scale.
Input: GRH, an odd nonsquare input at large level, and a scale of at least 46000
covering its logarithm. Claim: an actual negative witness is below four fifths of its square.
Proof: apply the existing uniform no-witness contradiction at the common scale.
Role: expose the real-scale quantification already used inside cumulative Gamma bounds. -/
private theorem gamma_common_scale_large {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hq : 20000 ≤ 4 * n) {L : ℝ} (hL : 46000 ≤ L) (hlog : Real.log n ≤ L)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hlogq : Real.log (4 * n : ℕ) ≤ L + 2 :=
    (le_of_eq (LLS.log_original_quadratic_level hn.pos)).trans (add_le_add hlog LLS.log_four_le_two)
  by_contra hnone
  apply
    LLS.gamma_ramp_prime_trivial_false_uniform hn (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns) hq hL hlogq hGRH
  intro p hp hd hb
  by_contra hv
  have hm := NumberTheory.negOneWitness_mem_of_quadratic_ne_one n hn hp hd hv
  have hcut : (99 / 40 : ℝ) * ((32 / 99 : ℝ) * L ^ 2) = (4 / 5 : ℝ) * L ^ 2 := by ring
  rw [hcut] at hb
  exact hnone ⟨p, hm, hb⟩

/-- A common logarithmic scale of at least 46000 bounds every least negative witness.
Input: an odd nonsquare input, GRH, a valid common scale and witness-set nonemptiness.
Claim: the least witness fits four fifths of the squared scale.
Proof: use uniform smoothed comparison at large levels and the elementary bound below them.
Role: supply a closed full-domain cumulative Gamma candidate without a separate history cap. -/
theorem negOneWitness_le_common_46000 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 46000 ≤ L)
    (hlog : Real.log n ≤ L) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 := by
  by_cases hq : 20000 ≤ 4 * n
  · obtain ⟨p, hp, hb⟩ := gamma_common_scale_large hn hns hq hL hlog hGRH
    exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw hp)).trans hb
  · obtain ⟨p, hp, ho, hb, hj⟩ := exists_prime_neg_one_witness_of_grh hGRH hn.pos hn hns
    have hsmall := gamma_small_radius_bound hn.pos (lt_of_not_ge hq)
    have hLs :=
      (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 46000)
            ((by norm_num only : (0 : ℝ) ≤ 46000).trans hL)).mpr
        hL
    have hbudget : (90 : ℝ) ^ 2 ≤ (4 / 5 : ℝ) * L ^ 2 := by nlinarith only [hLs]
    exact
      (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans
        (hb.trans (hsmall.trans hbudget))

/-- The smoothed negative-witness candidate with common scale at least 46000.
Input: any natural endpoint. Output: four fifths times the squared larger scale.
Role: retain the negative-witness semantics, independently of the earlier non-one entrance. -/
noncomputable def negativeScaleBound (B : ℕ) : ℝ :=
  logScaleBound (4 / 5) 46000 B

/-- Under GRH every negative witness maximum obeys the common smoothed Gamma estimate.
Input: any natural endpoint and GRH. Claim: all admissible inputs below it are bounded.
Proof: lift the common real-scale least-witness theorem to the finite maximum.
Role: remove the unnecessary natural-endpoint threshold from this cumulative candidate. -/
theorem QNegOne_le_smoothed_scale (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ negativeScaleBound B :=
  QNegOne_le_logScaleBound (by norm_num only : (0 : ℝ) ≤ 4 / 5)
    (fun {_n} hn hns {_L} hL hlog hw ↦ negOneWitness_le_common_46000 hn hns hGRH hL hlog hw) B

/-- The free 290-scale candidate beats the former 255-endpoint scalar near 290.
Input: an endpoint logarithm between 289 and 290. Claim: the new scalar is strictly smaller.
Proof: exact rational square comparisons. Role: identify a winning candidate interval. -/
theorem mixed_scale_lt_joint {B : ℕ} (hL : 289 ≤ Real.log B) (hU : Real.log B ≤ 290) :
    mixedScaleBound B < (9999 / 10000 : ℝ) * max 255 (Real.log B) ^ 2 := by
  change (99 / 100 : ℝ) * max 290 (Real.log B) ^ 2 < (9999 / 10000 : ℝ) * max 255 (Real.log B) ^ 2
  rw [max_eq_left hU, max_eq_right (show 255 ≤ Real.log B by linarith only [hL])]
  have hs := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 289) (Real.log_natCast_nonneg B)).mpr hL
  nlinarith only [hs]

/-- The non-one common-scale candidate beats the shifted-log scalar before its entrance.
Input: an endpoint logarithm between 21000 and 22221. Claim: a strict scalar improvement.
Proof: compare squares at the lower logarithmic endpoint.
Role: certify the benefit of common-scale lifting while retaining non-one semantics. -/
theorem neOne_scale_lt_shifted {B : ℕ} (hL : 21000 ≤ Real.log B) (hU : Real.log B ≤ 22221) :
    neOneScaleBound B < (Real.log B - 1 / 2) ^ 2 := by
  change (4 / 5 : ℝ) * max 22221 (Real.log B) ^ 2 < (Real.log B - 1 / 2) ^ 2
  rw [max_eq_left hU]
  have hz : 0 ≤ Real.log B - 1 / 2 := by linarith only [hL]
  have hs :=
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ (21000 : ℝ) - 1 / 2) hz).mpr
      (sub_le_sub_right hL (1 / 2))
  nlinarith only [hs]

/-- The free negative 46000-scale candidate beats the mixed scalar before its entrance.
Input: an endpoint logarithm between 44000 and 46000. Claim: a strict scalar improvement.
Proof: exact lower and upper square comparisons.
Role: record a negative-witness winning interval independently of the non-one candidate. -/
theorem negative_scale_lt_mixed {B : ℕ} (hL : 44000 ≤ Real.log B) (hU : Real.log B ≤ 46000) :
    negativeScaleBound B < mixedScaleBound B := by
  change (4 / 5 : ℝ) * max 46000 (Real.log B) ^ 2 < (99 / 100 : ℝ) * max 290 (Real.log B) ^ 2
  rw [max_eq_left hU, max_eq_right (show 290 ≤ Real.log B by linarith only [hL])]
  have hs := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 44000) (Real.log_natCast_nonneg B)).mpr hL
  nlinarith only [hs]

end PseudoPrime.PseudoSquare
