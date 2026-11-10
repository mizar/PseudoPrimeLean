/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInteriorReduced
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCommonLow

/-! # Interior witness at common scale 68 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At common scale 68, the explicit interior lower bound exceeds the
principal and conductor cost. Certified exponential, square-root and
logarithm estimates prove the strict scalar gap. -/
theorem quarter_interior_gap68 :
    (32 - Real.log ((34 : ℝ) ^ 2)) * 68 + (137 / 330 : ℝ) * (34 + (34 : ℝ)⁻¹) +
        (4 / 15 : ℝ) * (Real.sqrt 34 + (Real.sqrt 34)⁻¹) +
        15 / 11 <
      (100 - 4 * Real.log ((34 : ℝ) ^ 2)) * 34 -
        (19 / 30 : ℝ) * (156 - 6 * Real.log ((34 : ℝ) ^ 2)) * Real.sqrt 34 -
        ((98717 / 12000 : ℝ) * (48 - Real.log ((34 : ℝ) ^ 2) - Real.log 16) - 59 / 5) := by
  have he : (34 : ℝ) ≤ Real.exp (3527 / 1000 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3527 / 1000) 20
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
      Nat.cast_one, pow_zero, pow_succ] at h
    linarith only [h]
  have hlog : Real.log 34 ≤ (3527 / 1000 : ℝ) := (Real.log_le_iff_le_exp (by norm_num only)).2 he
  have hs : Real.sqrt 34 ≤ (5831 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hslo : (58 / 10 : ℝ) ≤ Real.sqrt 34 :=
    (Real.le_sqrt (by norm_num only) (by norm_num only)).2 (by norm_num only)
  have hinv : (Real.sqrt 34)⁻¹ ≤ (5 / 29 : ℝ) := by
    have h :=
      (inv_le_inv₀ (Real.sqrt_pos.2 (by norm_num only : (0 : ℝ) < 34))
            (by norm_num only : (0 : ℝ) < 58 / 10)).2
        hslo
    norm_num only [show (58 / 10 : ℝ)⁻¹ = 5 / 29 by norm_num only] at h
    exact h
  have hlog16 : (277 / 100 : ℝ) ≤ Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hprod :=
    mul_nonneg (show 0 ≤ 5831 / 1000 - Real.sqrt 34 by linarith only [hs])
      (show 0 ≤ (156 : ℝ) - 12 * Real.log 34 by linarith only [hlog])
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hlog, hs, hslo, hinv, hlog16, hprod]

/-- Under GRH, an odd input whose logarithm is at most 68 and whose Fermat
index is at least 33000 has a rejecting prime at most 34 squared. The
interior no-witness inequality contradicts the certified endpoint gap. -/
theorem quarter_interior_witness68 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hscale : Real.log n ≤ 68)
    (hindex : 33000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 34 ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have hlog : Real.log ((34 : ℝ) ^ 2) ≤ 16 := by
    have hm :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 34) (by norm_num only : (34 : ℝ) ≤ 2 ^ (6 : ℕ))
    rw [Real.log_pow] at hm ⊢
    norm_num only [Nat.cast_ofNat] at hm ⊢
    linarith only [hm, Real.log_two_lt_d9]
  by_contra hnone
  have h :=
    quarter_interior_reduced hn ho (r := 34) (T := 68) (by norm_num only) hlog (by norm_num only)
      hscale hindex hGRH hnone
  exact (not_lt_of_ge h) quarter_interior_gap68

/-- Under GRH, a nonuniform odd composite whose logarithm is at most 68 has
a rejecting prime at most one quarter of 68 squared. Split the Fermat index
at 33000 and use the small-index and interior endpoint witnesses. -/
theorem quarter_nonuniform_scale68 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hu : ¬UniformKorseltTriple n) (hscale : Real.log n ≤ 68)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * 68 ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 33000
  · exact
      quarter_common_index_le hn ho hc (PrimeTest.fermatSubgroup n) le_rfl hi hu hGRH
        (by norm_num only) hscale
  · obtain ⟨p, hp, hb, hf⟩ :=
      quarter_interior_witness68 hn ho hscale (Nat.le_of_lt (Nat.lt_of_not_ge hi)) hGRH
    refine ⟨p, hp, ?_, hf⟩
    norm_num only at hb ⊢
    exact hb

end PseudoPrime.PrimeTestBounds.MillerRabin
