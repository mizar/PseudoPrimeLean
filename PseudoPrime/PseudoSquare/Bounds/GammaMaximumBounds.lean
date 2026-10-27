/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.GammaWitnessBounds
public import PseudoPrime.PseudoSquare.Bounds.RefinedElementaryBounds
public import PseudoPrime.LLS.GammaQuadraticUniformBounds

/-! # Derived finite maxima for the smoothed Gamma witness bound

The endpoint-scale comparison and a small-input prefix cover all admissible inputs.
The coefficient and decimal starting value agree with the primary pointwise bound.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Every odd nonsquare natural input is at least three.
Writing it as 2k+1, the nonsquare condition excludes k=0. -/
private theorem three_le_of_odd_nonsquare {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n) : 3 ≤ n := by
  obtain ⟨k, rfl⟩ := hn
  have hk : 0 < k :=
    Nat.pos_of_ne_zero
      (fun he ↦
        hns
          (by
            rw [he]; exact ⟨1, rfl⟩))
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hk)) 1

/-- For 3≤n≤5000, the refined elementary root is at most seventy.
Bound log(4n) by log(46000)<11 and loglog(4n) by log(4n).
This covers every input below the ambient range of the smoothed formula. -/
private theorem small_gamma_root_le_seventy {n : ℕ} (hn3 : 3 ≤ n) (hn : n ≤ 5000) :
    refinedElementaryRoot n ≤ 70 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num only) hn3)
  have hq0 : 0 < 4 * (n : ℝ) := mul_pos (by norm_num only) hn0
  have hq : 4 * (n : ℝ) ≤ 46000 := by
    have hnR : (n : ℝ) ≤ 5000 := by exact_mod_cast hn
    linarith only [hnR]
  have hlog := (Real.log_le_log hq0 hq).trans Analysis.log_46000_lt_eleven.le
  have hlog0 : 0 ≤ Real.log (4 * (n : ℝ)) :=
    Real.log_nonneg
      (by
        have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
        linarith only [hnR])
  have hloglog := Real.log_le_self hlog0
  dsimp only [refinedElementaryRoot]
  nlinarith only [hlog, hloglog]

/-- For odd nonsquare n≤B with 4n≥20000 and log(B)≥46000, there is a negative
odd-prime witness at most (4/5)log(B)² under GRH.
Apply the uniform no-witness comparison at the endpoint scale, preserving level 4n.
This supplies the large-input portion of the derived finite maximum. -/
private theorem exists_primeNegOneWitness_le_gamma_endpoint {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hq : 20000 ≤ 4 * n) (hL : 46000 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log B) ^ 2 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  let x := (32 / 99 : ℝ) * (Real.log B) ^ 2
  have hcut : (99 / 40 : ℝ) * x = (4 / 5 : ℝ) * (Real.log B) ^ 2 := by
    dsimp only [x]
    ring
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Odd.pos hn)) (Nat.cast_le.mpr hnB)
  have hlogq : Real.log (4 * n : ℕ) ≤ Real.log B + 2 := by
    rw [LLS.log_original_quadratic_level (Odd.pos hn)]
    linarith only [hmono, LLS.log_four_le_two]
  by_contra hnone
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ 4 * n →
        (p : ℝ) ≤ (99 / 40 : ℝ) * x → NumberTheory.complexQuadraticCharacter n hn p = 1 := by
    intro p hp hd hb
    by_contra hv
    have hm := NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd hv
    rw [hcut] at hb
    exact hnone ⟨p, hm, hb⟩
  exact
    LLS.gamma_ramp_prime_trivial_false_uniform hn (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns) hq hL hlogq hGRH hsmall

/-- Under GRH, every odd nonsquare n≤B has least negative witness at most
(4/5)log(B)² when log(B)≥46000. Use the endpoint-scale comparison at large level
and the refined elementary root bound for the remaining small inputs. -/
private theorem least_gamma_le_endpoint_smoothed {n B : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hnB : n ≤ B) (hL : 46000 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (4 / 5 : ℝ) * (Real.log B) ^ 2 := by
  by_cases hq : 20000 ≤ 4 * n
  · obtain ⟨p, hp, hb⟩ := exists_primeNegOneWitness_le_gamma_endpoint hn hns hnB hq hL hGRH
    exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw hp)).trans hb
  · have hn3 := three_le_of_odd_nonsquare hn hns
    have hnsmall : n ≤ 5000 := by linarith only [lt_of_not_ge hq]
    have hroot := small_gamma_root_le_seventy hn3 hnsmall
    have hroot0 : 0 ≤ refinedElementaryRoot n := by linarith only [refinedElementaryRoot_gt hn3]
    have hradius : refinedElementaryRadius n ≤ (70 : ℝ) ^ 2 :=
      (sq_le_sq₀ hroot0 (by norm_num only)).mpr hroot
    have hB0 : 0 ≤ Real.log B := by linarith only [hL]
    have hBsq := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 46000) hB0).mpr hL
    have hbudget : (70 : ℝ) ^ 2 ≤ (4 / 5 : ℝ) * (Real.log B) ^ 2 := by nlinarith only [hBsq]
    exact
      (primeNegOneWitness_le_refinedElementaryRadius hn3 hn hns hGRH hw).trans
        (hradius.trans hbudget)

/-- Under GRH and B≥10^20000, both finite witness maxima have the same
(4/5)log(B)² envelope as the primary pointwise Gamma theorem.
Cover all admissible inputs using the uniform endpoint comparison and the small-input prefix,
then lift through the finite supremum. No additional starting value is required. -/
theorem gamma_formula_explicit {B : ℕ} (hB : 10 ^ 20000 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    QNeOne B ≤ QNegOne B ∧ (QNegOne B : ℝ) ≤ (4 / 5 : ℝ) * (Real.log B) ^ 2 := by
  refine
    ⟨QNeOne_le_QNegOne B,
      QNegOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4 / 5) (sq_nonneg _)) ?_⟩
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    least_gamma_le_endpoint_smoothed ha.odd ha.not_isSquare ha.le
      (Analysis.log_nat_gt_46000_of_decimal hB).le hGRH
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- Under GRH for B≥10^19978, both finite witness maxima share the
coefficient (4/5)log(B)² of the refined pointwise theorem. Use the same log
threshold 46000 in the endpoint comparison and include every smaller admissible
input through the proved small-input prefix. No finite-maximum threshold is added. -/
theorem gamma_formula_explicit_19978 {B : ℕ} (hB : 10 ^ 19978 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    QNeOne B ≤ QNegOne B ∧ (QNegOne B : ℝ) ≤ (4 / 5 : ℝ) * (Real.log B) ^ 2 := by
  refine
    ⟨QNeOne_le_QNegOne B,
      QNegOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4 / 5) (sq_nonneg _)) ?_⟩
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    least_gamma_le_endpoint_smoothed ha.odd ha.not_isSquare ha.le
      (Analysis.log_nat_gt_46000_of_decimal_19978 hB).le hGRH
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

end PseudoPrime.PseudoSquare
