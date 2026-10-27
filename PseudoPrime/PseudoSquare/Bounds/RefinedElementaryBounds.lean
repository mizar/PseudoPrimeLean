/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RefinedTheorem11S1
public import PseudoPrime.PseudoSquare.Bounds.ElementaryOmegaFinal

/-! # The refined elementary envelope for least quadratic witnesses -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The refined root log(4n)+(24/5)log(log(4n))+2.
The elementary prime-factor bound controls the refined LLS correction by its final two terms.
Its square is the uniform real radius for least quadratic witnesses. -/
noncomputable def refinedElementaryRoot (n : ℕ) : ℝ :=
  Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 2

/-- The square of the refined elementary root, defined for every natural input.
For inputs at least three it absorbs the finite witness bound 31 and the large-input LLS bound.
It is used for pointwise witnesses and their finite maxima. -/
noncomputable def refinedElementaryRadius (n : ℕ) : ℝ :=
  (refinedElementaryRoot n) ^ 2

/-- For n≥3 the refined elementary root exceeds 172/25.
Lower bounds for log(12) and log(2) give a uniform positive root.
Its square exceeds 31, so existing small-input witnesses fit the refined envelope. -/
theorem refinedElementaryRoot_gt {n : ℕ} (hn : 3 ≤ n) :
    (172 / 25 : ℝ) < refinedElementaryRoot n := by
  have h12 : (12 : ℝ) ≤ 4 * n := by
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [hnR]
  have hlog12 : (2 : ℝ) < Real.log 12 := by
    rw [show (12 : ℝ) = 2 ^ (2 : ℕ) * 3 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    norm_num only [Nat.cast_ofNat] at ⊢
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hl : (2 : ℝ) < Real.log (4 * (n : ℝ)) :=
    hlog12.trans_le (Real.log_le_log (by norm_num only) h12)
  have hll := Real.log_lt_log (by norm_num only : (0 : ℝ) < 2) hl
  unfold refinedElementaryRoot
  linarith only [hl, hll, Real.log_two_gt_d9]

/-- For 3≤n≤B the refined elementary root is nondecreasing.
Apply logarithmic monotonicity twice on positive arguments and add the terms.
This transfers pointwise bounds to the common endpoint of a finite maximum. -/
theorem refinedElementaryRoot_mono {n B : ℕ} (hn : 3 ≤ n) (hnB : n ≤ B) :
    refinedElementaryRoot n ≤ refinedElementaryRoot B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 3) hn)
  have hmul : (4 * (n : ℝ)) ≤ 4 * B :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnB) (by norm_num only)
  have hl := Real.log_le_log (mul_pos (by norm_num only) hn0) hmul
  have hnR : (3 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hln : 0 < Real.log (4 * (n : ℝ)) := Real.log_pos (by nlinarith only [hnR])
  have hll := Real.log_le_log hln hl
  unfold refinedElementaryRoot
  linarith only [hl, hll]

/-- For odd n≥750, the refined LLS correction at level 4n is at most
(24/5)log(log(4n))+2. Use the unconditional elementary prime-factor estimate
and nonnegativity of the refined reciprocal saving. This is the large-input radius comparison. -/
theorem refinedCorrectionTerm_le_elementary {n : ℕ} (hn : Odd n) (hn750 : 750 ≤ n) :
    LLS.refinedCorrectionTerm (NumberTheory.characterModulus n) ≤
      (24 / 5 : ℝ) * Real.log (Real.log (NumberTheory.characterModulus n)) + 2 := by
  have hq : 3000 ≤ NumberTheory.characterModulus n := by
    unfold NumberTheory.characterModulus
    exact Nat.mul_le_mul_left 4 hn750
  have hy := (AnalyticNumberTheory.Arithmetic.log_log_pos_of_le hq).2
  have hc :=
    AnalyticNumberTheory.Arithmetic.elementary_prime_count_term_le
      AnalyticNumberTheory.Arithmetic.elementaryOmegaStatement hn hn750
  have ha : 0 ≤ LLS.refinedAuxiliaryTerm (NumberTheory.characterModulus n) := le_max_left _ _
  norm_num only [AnalyticNumberTheory.Arithmetic.elementaryOmegaConstant] at hc
  unfold LLS.refinedCorrectionTerm
  apply max_le
  · linarith only [hy]
  · linarith only [hc, ha]

/-- Under GRH, an odd nonsquare n≥750 has its least odd-prime negative Jacobi
witness within the refined elementary radius. Apply the refined LLS character theorem at 4n,
convert the character value to a negative Jacobi witness, and bound the correction.
This supplies the large-input branch without dropping the modulus or odd-prime conditions. -/
theorem primeNegOneWitness_le_refinedElementaryRadius_of_large {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hn750 : 750 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ refinedElementaryRadius n := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  have hq : 3000 ≤ 4 * n := Nat.mul_le_mul_left 4 hn750
  obtain ⟨p, hp, hd, hv, hb⟩ :=
    LLS.exists_prime_character_ne_one_le_refinedRadius (NumberTheory.complexQuadraticCharacter n hn)
      hq (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns) hGRH
  have hm := NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd hv
  have hleast : (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ p :=
    Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw hm)
  have hc := refinedCorrectionTerm_le_elementary hn hn750
  simp only [NumberTheory.characterModulus, Nat.cast_mul, Nat.cast_ofNat] at hc
  have hbase : LLS.refinedRadiusRoot (4 * n) ≤ refinedElementaryRoot n := by
    unfold LLS.refinedRadiusRoot refinedElementaryRoot
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hc]
  have hnonneg : 0 ≤ LLS.refinedRadiusRoot (4 * n) :=
    (Analysis.eight_lt_log_level hq).le.trans (le_add_of_nonneg_right (le_max_left _ _)) |>.trans'
      (by norm_num only)
  have hright : 0 ≤ refinedElementaryRoot n :=
    (by norm_num only : (0 : ℝ) ≤ 172 / 25).trans
      (refinedElementaryRoot_gt ((by norm_num only : 3 ≤ 750).trans hn750)).le
  exact hleast.trans (hb.trans ((sq_le_sq₀ hnonneg hright).mpr hbase))

/-- Under GRH, every odd nonsquare n≥3 has its least negative Jacobi witness
within the refined elementary radius. Inputs below 750 reuse the existing bound 31;
larger inputs use the refined LLS theorem. This is the full pointwise input to the maximum. -/
theorem primeNegOneWitness_le_refinedElementaryRadius {n : ℕ} (hn3 : 3 ≤ n) (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ refinedElementaryRadius n := by
  by_cases hn750 : 750 ≤ n
  · exact primeNegOneWitness_le_refinedElementaryRadius_of_large hn hns hn750 hGRH hw
  · have hs : (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ 31 :=
      Nat.cast_le.mpr (smallNegOneWitnessBound n hn hns (Nat.lt_of_not_ge hn750))
    have hb := refinedElementaryRoot_gt hn3
    have hr : (31 : ℝ) ≤ refinedElementaryRadius n := by
      unfold refinedElementaryRadius
      nlinarith only [hb]
    exact hs.trans hr

/-- Under GRH and B≥3, QNeOne(B)≤QNegOne(B), and QNegOne(B) is within the
refined elementary radius. Bound each admissible input, use root monotonicity,
and lift the pointwise real estimates through the finite supremum.
This proves the global quadratic envelope with additive constant two. -/
theorem refined_elementary_formula_real {B : ℕ} (hB : 3 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    QNeOne B ≤ QNegOne B ∧ (QNegOne B : ℝ) ≤ refinedElementaryRadius B := by
  refine ⟨QNeOne_le_QNegOne B, QNegOne_cast_le_of_forall (sq_nonneg _) ?_⟩
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hn1 : n ≠ 1 := by
    intro he
    exact ha.not_isSquare (he.symm ▸ (show IsSquare (1 : ℕ) from ⟨1, rfl⟩))
  have hn3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := ha.odd
    have hk0 : 0 < k := by
      by_contra hh
      have hz := Nat.eq_zero_of_not_pos hh
      apply hn1
      rw [hk, hz]
      norm_num only
    rw [hk]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hk0)) 1
  have hb :=
    primeNegOneWitness_le_refinedElementaryRadius hn3 ha.odd ha.not_isSquare hGRH
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)
  have hr := refinedElementaryRoot_mono hn3 ha.le
  have h0 : 0 ≤ refinedElementaryRoot n :=
    (by norm_num only : (0 : ℝ) ≤ 172 / 25).trans (refinedElementaryRoot_gt hn3).le
  have hB0 : 0 ≤ refinedElementaryRoot B :=
    (by norm_num only : (0 : ℝ) ≤ 172 / 25).trans (refinedElementaryRoot_gt hB).le
  exact hb.trans ((sq_le_sq₀ h0 hB0).mpr hr)

/-- Under GRH and B≥3, the maximum least negative Jacobi witness is at most
(log(4B)+(24/5)log(log(4B))+2)², and it bounds the non-one witness maximum.
Unfold the refined radius in the real maximum theorem. This is the explicit public envelope. -/
theorem refined_elementary_formula_explicit {B : ℕ} (hB : 3 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    QNeOne B ≤ QNegOne B ∧
      (QNegOne B : ℝ) ≤
        (Real.log (4 * (B : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (B : ℝ))) + 2) ^ 2 := by
  exact refined_elementary_formula_real hB hGRH

/-- Under GRH, every odd nonsquare n≥3 has an odd prime with Jacobi value −1
at most (log(4n)+(24/5)log(log(4n))+2)².
Take the least negative witness and use the full pointwise refined envelope.
This is the explicit prime-existence form of the improved global quadratic bound. -/
theorem exists_prime_neg_one_witness_le_refined_elementary
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn3 : 3 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤
          (Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 2) ^ 2 ∧
        jacobiSym n p = -1 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hb := primeNegOneWitness_le_refinedElementaryRadius hn3 hn hns hGRH hw
  have hm := NumberTheory.primeNegOneWitness_mem n hw
  exact ⟨NumberTheory.primeNegOneWitness n hw, hm.1, hm.2.1, hb, hm.2.2⟩

end PseudoPrime.PseudoSquare
