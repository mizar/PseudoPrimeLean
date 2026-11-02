/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.PreciseSavingJacobiBounds
public import PseudoPrime.LLS.PreciseSavingScaleBounds

/-! # Precise-saving quadratic witness radii and cumulative maxima

The factor-independent radii evaluate the selected LLS majorants at the original level
four times the input. The existing bound thirty-one covers every smaller odd nonsquare;
no new input enumeration is used. Monotonicity is proved for these two majorants, rather
than assumed for the factor-aware precise-saving cutoff. Empty witness domains retain
maximum zero. Trial-count empty-domain conventions are handled separately by Selfridge.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The elementary precise-saving radius at a natural endpoint.
Input: any endpoint. Output: the square of the original-level root with additive 1.4062.
Role: a factor-independent pointwise and cumulative negative-witness candidate. -/
noncomputable def preciseElementaryRadius (B : ℕ) : ℝ :=
  LLS.preciseElementaryRoot (4 * B) ^ 2

/-- The radius retaining the selected cutoff-thirty-one saving at a natural endpoint.
Input: any endpoint. Output: the square of the certified original-level root.
Role: a cumulative candidate that requires no factorization of the endpoint or earlier inputs. -/
noncomputable def prime31SavingRadius (B : ℕ) : ℝ :=
  LLS.prime31SavingRoot (4 * B) ^ 2

/-- Odd nonsquares have input at least three.
Input: oddness and nonsquareness. Claim: the first admissible natural input is three.
Proof: exclude the zero coefficient in the odd representation.
Role: supply the domain of the two monotone majorants. -/
private theorem precise_input_three_le {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n) : 3 ≤ n := by
  have hn1 : n ≠ 1 := fun he ↦ hns (he.symm ▸ (show IsSquare (1 : ℕ) from ⟨1, rfl⟩))
  obtain ⟨k, hk⟩ := hn
  have hk0 : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro he
    apply hn1
    rw [hk, he]
    norm_num only
  rw [hk]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hk0)) 1

/-- The improved elementary root differs from the former root by the selected constant change.
Input: any natural input. Claim: the original-level root decreases by 0.5938.
Proof: normalize the natural cast and rational constants.
Role: reuse the existing lower bound and monotonicity without changing its API. -/
private theorem precise_root_eq_refined_sub (n : ℕ) :
    LLS.preciseElementaryRoot (4 * n) = refinedElementaryRoot n - 2969 / 5000 := by
  dsimp only [LLS.preciseElementaryRoot, refinedElementaryRoot]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- The original quadratic level has logarithm greater than one from input three onward.
Input: an input at least three. Claim: its logarithm is in the positive double-log domain.
Proof: compare with level four and use the certified logarithm of two.
Role: positivity and monotonicity of the cutoff-thirty-one majorant. -/
private theorem precise_level_log_gt_one {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log (4 * n : ℕ) := by
  have hq : 4 ≤ 4 * n := Nat.mul_le_mul_left 4 ((by norm_num only : (1 : ℕ) ≤ 3).trans hn)
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 4) (Nat.cast_le.mpr hq)
  have h4 : (1 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num only, Real.log_pow]
    norm_num only
    linarith only [Real.log_two_gt_d9]
  exact h4.trans_le hl

/-- The improved elementary root uniformly exceeds 6.2862.
Input: an input at least three. Claim: the selected positive root floor.
Proof: subtract the rational change from the existing root lower bound.
Role: absorb the completed small-input witness cap thirty-one. -/
private theorem precise_elementary_root_lower {n : ℕ} (hn : 3 ≤ n) :
    (31431 / 5000 : ℝ) < LLS.preciseElementaryRoot (4 * n) := by
  have hr := refinedElementaryRoot_gt hn
  have he := precise_root_eq_refined_sub n
  linarith only [hr, he]

/-- The retained-saving root uniformly exceeds nine.
Input: an input at least three. Claim: the positive original-level root floor.
Proof: its logarithmic terms are positive and its constant exceeds nine.
Role: absorb the completed small-input witness cap without a new certificate. -/
private theorem precise_prime31_root_lower {n : ℕ} (hn : 3 ≤ n) :
    (9 : ℝ) < LLS.prime31SavingRoot (4 * n) := by
  have hl := precise_level_log_gt_one hn
  have hz := Real.log_pos hl
  dsimp only [LLS.prime31SavingRoot]
  linarith only [hl, hz]

/-- The elementary precise-saving radius exceeds the existing finite witness cap.
Input: an endpoint at least three. Claim: the radius is strictly above thirty-one.
Proof: square the positive uniform root floor. Role: close all inputs below 750. -/
theorem preciseRadius_gt_thirty_one {B : ℕ} (hB : 3 ≤ B) :
    (31 : ℝ) < preciseElementaryRadius B := by
  have hr := precise_elementary_root_lower hB
  have hs :=
    (sq_lt_sq₀ (by norm_num only : (0 : ℝ) ≤ 31431 / 5000)
          ((by norm_num only : (0 : ℝ) ≤ 31431 / 5000).trans hr.le)).mpr
      hr
  exact (by norm_num only : (31 : ℝ) ≤ (31431 / 5000 : ℝ) ^ 2).trans_lt hs

/-- The cutoff-thirty-one radius exceeds eighty-one on the nonempty input range.
Input: an endpoint at least three. Claim: the radius exceeds nine squared.
Proof: square the root floor. Role: small witnesses and Selfridge exceptional stops. -/
theorem prime31Radius_gt_eighty_one {B : ℕ} (hB : 3 ≤ B) : (81 : ℝ) < prime31SavingRadius B := by
  have hr := precise_prime31_root_lower hB
  have hs :=
    (sq_lt_sq₀ (by norm_num only : (0 : ℝ) ≤ 9) ((by norm_num only : (0 : ℝ) ≤ 9).trans hr.le)).mpr
      hr
  norm_num only at hs
  exact hs

/-- The improved elementary radius is nondecreasing from input three onward.
Input: ordered endpoints with the smaller at least three. Claim: the squared roots are ordered.
Proof: reuse the former root monotonicity and the unchanged rational shift.
Role: transport pointwise precise-saving witnesses to a common cumulative endpoint. -/
theorem preciseElementaryRadius_mono {n B : ℕ} (hn : 3 ≤ n) (hnB : n ≤ B) :
    preciseElementaryRadius n ≤ preciseElementaryRadius B := by
  have h0 := (by norm_num only : (0 : ℝ) ≤ 31431 / 5000).trans (precise_elementary_root_lower hn).le
  have h0B :=
    (by norm_num only : (0 : ℝ) ≤ 31431 / 5000).trans
      (precise_elementary_root_lower (hn.trans hnB)).le
  have hr : LLS.preciseElementaryRoot (4 * n) ≤ LLS.preciseElementaryRoot (4 * B) := by
    rw [precise_root_eq_refined_sub, precise_root_eq_refined_sub]
    exact sub_le_sub_right (refinedElementaryRoot_mono hn hnB) _
  exact (sq_le_sq₀ h0 h0B).mpr hr

/-- The cutoff-thirty-one radius is nondecreasing from input three onward.
Input: ordered endpoints with the smaller at least three. Claim: the squared majorants are ordered.
Proof: apply logarithmic monotonicity twice and square the positive roots.
Role: cumulative lifting independently of the factor-aware cutoff's behavior. -/
theorem prime31SavingRadius_mono {n B : ℕ} (hn : 3 ≤ n) (hnB : n ≤ B) :
    prime31SavingRadius n ≤ prime31SavingRadius B := by
  have hn0 : (0 : ℝ) < (4 * n : ℕ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (by norm_num only) ((by norm_num only : (0 : ℕ) < 3).trans_le hn))
  have hl := Real.log_le_log hn0 (Nat.cast_le.mpr (Nat.mul_le_mul_left 4 hnB))
  have hll := Real.log_le_log (zero_lt_one.trans (precise_level_log_gt_one hn)) hl
  have hr : LLS.prime31SavingRoot (4 * n) ≤ LLS.prime31SavingRoot (4 * B) := by
    dsimp only [LLS.prime31SavingRoot]
    linarith only [hl, hll]
  exact
    (sq_le_sq₀ ((by norm_num only : (0 : ℝ) ≤ 9).trans (precise_prime31_root_lower hn).le)
          ((by norm_num only : (0 : ℝ) ≤ 9).trans
            (precise_prime31_root_lower (hn.trans hnB)).le)).mpr
      hr

/-- For large inputs, one least witness satisfies both factor-independent majorants.
Input: an odd nonsquare at least 750, GRH and witness nonemptiness.
Claim: its least negative witness is bounded by both selected radii.
Proof: combine the factor-aware theorem with both certified root comparisons.
Role: the shared large-input branch of the full pointwise witness interface. -/
private theorem leastWitness_le_preciseRadii_large {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hn750 : 750 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ preciseElementaryRadius n ∧
      (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ prime31SavingRadius n := by
  have hb := leastWitness_le_preciseSaving hn hns hn750 hGRH hw
  have ha := LLS.preciseSavingRoot_le_elementary hn hn750
  have hc := LLS.preciseSavingRoot_le_prime31 hn hn750
  have hq : 3000 ≤ 4 * n := Nat.mul_le_mul_left 4 hn750
  have hcorr : 0 ≤ LLS.preciseSavingCorrectionTerm (4 * n) := le_max_left _ _
  have h0 : 0 ≤ LLS.preciseSavingRadiusRoot (4 * n) := by
    change 0 ≤ Real.log (4 * n : ℕ) + LLS.preciseSavingCorrectionTerm (4 * n)
    exact
      add_nonneg ((by norm_num only : (0 : ℝ) ≤ 8).trans (Analysis.eight_lt_log_level hq).le) hcorr
  exact
    ⟨hb.trans ((sq_le_sq₀ h0 (h0.trans ha)).mpr ha), hb.trans ((sq_le_sq₀ h0 (h0.trans hc)).mpr hc)⟩

/-- Every odd nonsquare's least negative witness satisfies both precise-saving radii under GRH.
Input: an odd nonsquare, GRH and witness nonemptiness. Claim: both pointwise bounds hold.
Proof: use the actual-prime majorants above 750 and the completed thirty-one cap below it.
Role: close the full input domain without a congruence or squarefree restriction. -/
theorem leastWitness_le_preciseRadii {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ preciseElementaryRadius n ∧
      (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ prime31SavingRadius n := by
  by_cases hn750 : 750 ≤ n
  · exact leastWitness_le_preciseRadii_large hn hns hn750 hGRH hw
  · have hn3 := precise_input_three_le hn hns
    have hs : (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ 31 :=
      Nat.cast_le.mpr (smallNegOneWitnessBound n hn hns (Nat.lt_of_not_ge hn750))
    exact
      ⟨hs.trans (preciseRadius_gt_thirty_one hn3).le,
        hs.trans ((by norm_num only : (31 : ℝ) ≤ 81).trans (prime31Radius_gt_eighty_one hn3).le)⟩

/-- An actual negative Jacobi witness lies below the smaller precise-saving radius under GRH.
Input: an odd nonsquare and GRH. Claim: an odd-prime witness meets both majorants.
Proof: choose the common least witness.
Role: actual-prime counterpart of the cumulative candidate. -/
theorem existsWitness_le_preciseRadii {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p ∈ NumberTheory.primeNegOneWitnessSet n ∧
        (p : ℝ) ≤ min (preciseElementaryRadius n) (prime31SavingRadius n) :=
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  let hb := leastWitness_le_preciseRadii hn hns hGRH hw
  ⟨NumberTheory.primeNegOneWitness n hw, NumberTheory.primeNegOneWitness_mem n hw, le_min hb.1 hb.2⟩

/-- Both radii bound the negative cumulative maximum at every natural endpoint.
Input: any endpoint and GRH. Claim: every earlier admissible input fits both majorants.
Proof: pointwise least bounds and monotonicity through the finite supremum.
Role: full-domain cumulative candidates, with empty domains covered by nonnegative squares. -/
theorem QNegOne_le_preciseRadii (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ preciseElementaryRadius B ∧ (QNegOne B : ℝ) ≤ prime31SavingRadius B := by
  constructor
  · apply QNegOne_cast_le_of_forall (sq_nonneg _)
    intro n hn
    have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
    exact
      (leastWitness_le_preciseRadii ha.odd ha.not_isSquare hGRH _).1.trans
        (preciseElementaryRadius_mono (precise_input_three_le ha.odd ha.not_isSquare) ha.le)
  · apply QNegOne_cast_le_of_forall (sq_nonneg _)
    intro n hn
    have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
    exact
      (leastWitness_le_preciseRadii ha.odd ha.not_isSquare hGRH _).2.trans
        (prime31SavingRadius_mono (precise_input_three_le ha.odd ha.not_isSquare) ha.le)

/-- Both Jacobi witness maxima obey the smaller precise-saving radius under GRH.
Input: any natural endpoint and GRH. Claim: negative and non-one maxima satisfy the bound.
Proof: combine the two negative estimates and use witness inclusion.
Role: a valid transfer only; dedicated non-one candidates remain separate and stronger. -/
theorem witnessMaxima_le_preciseRadii (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ min (preciseElementaryRadius B) (prime31SavingRadius B) ∧
      (QNeOne B : ℝ) ≤ min (preciseElementaryRadius B) (prime31SavingRadius B) :=
  let hb := QNegOne_le_preciseRadii B hGRH
  let hm := le_min hb.1 hb.2
  ⟨hm, (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans hm⟩

/-- Natural endpoints below three retain zero for both empty Jacobi maxima.
Input: an endpoint below three. Claim: neither finite domain contains an admissible input.
Proof: an odd nonsquare would have to be at least three.
Role: make the empty-domain boundary explicit before transferring to totalized trial counts. -/
theorem witnessMaxima_eq_zero_of_small {B : ℕ} (hB : B < 3) : QNegOne B = 0 ∧ QNeOne B = 0 := by
  have hz : (QNegOne B : ℝ) ≤ 0 := by
    apply QNegOne_cast_le_of_forall (by norm_num only : (0 : ℝ) ≤ 0)
    intro n hn
    have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
    exact
      False.elim
        ((Nat.not_le_of_lt hB) ((precise_input_three_le ha.odd ha.not_isSquare).trans ha.le))
  have he : QNegOne B = 0 :=
    Nat.eq_zero_of_le_zero ((Nat.cast_le (α := ℝ)).mp (by simpa only [Nat.cast_zero] using hz))
  exact ⟨he, Nat.eq_zero_of_le_zero ((QNeOne_le_QNegOne B).trans_eq he)⟩

end PseudoPrime.PseudoSquare
