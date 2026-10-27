/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeightRatioLayers

/-! # Exact exchange of reciprocal-height weights -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For a finite family with positive natural heights, exchange the reciprocal
height weights with the scale index. Count the integers d≤H/height and
reverse the finite sums. This retains all multiplicities without layer rounding. -/
theorem reciprocal_height_sum_eq_sum_restricted_card {ι : Type*} (S : Finset ι) (h : ι → ℕ) (H : ℕ)
    (hh : ∀ q ∈ S, 0 < h q) :
    (∑ q ∈ S, H / h q) = ∑ d ∈ Finset.Icc 1 H, (S.filter (fun q ↦ h q ≤ H / d)).card := by
  classical
  have hcount (k : ℕ) (hk : 0 < k) : H / k = ∑ d ∈ Finset.Icc 1 H, if k ≤ H / d then 1 else 0 := by
    have hf : (Finset.Icc 1 H).filter (fun d ↦ k ≤ H / d) = Finset.Icc 1 (H / k) := by
      ext d
      rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hd, hdH⟩, hkd⟩
        exact
          ⟨hd,
            (Nat.le_div_iff_mul_le hk).mpr
              (by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hkd)⟩
      · rintro ⟨hd, hdk⟩
        exact
          ⟨⟨hd, hdk.trans (Nat.div_le_self H k)⟩,
            (Nat.le_div_iff_mul_le hd).mpr
              (by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk).mp hdk)⟩
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hf, Nat.card_Icc, Nat.add_sub_cancel,
      Nat.cast_id]
  calc
    _ = ∑ q ∈ S, ∑ d ∈ Finset.Icc 1 H, if h q ≤ H / d then 1 else 0 :=
      Finset.sum_congr rfl (fun q hq ↦ hcount (h q) (hh q hq))
    _ = ∑ d ∈ Finset.Icc 1 H, ∑ q ∈ S, if h q ≤ H / d then 1 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]

/-- The weighted sum over actual positive Heilbronn ratios equals the sum of
the canonical-height restricted counts at floor(H/d). No primality-size
restriction is needed for this finite identity. It is the count-transfer input. -/
theorem positiveRatioSet_height_weight_sum_eq {p H : ℕ} [Fact p.Prime] :
    (∑ q ∈ positiveRatioSet p H, H / rationalPairHeight q) =
      ∑ d ∈ Finset.Icc 1 H, (heightRestrictedRatioSet p H (H / d)).card := by
  apply reciprocal_height_sum_eq_sum_restricted_card
  intro q hq
  exact (Rat.den_pos q).trans_le (le_max_right _ _)

/-- For odd p and H<p, the full signed congruence count is at most four times
the sum of restricted ratio counts at floor(H/d). Combine signed multiplicities
with the exact finite exchange; no analytic ratio bound is assumed here. -/
theorem boundedCongruenceCount_le_sum_restricted_card {p H : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hHp : H < p) :
    boundedCongruenceCount p H ≤
      4 * ∑ d ∈ Finset.Icc 1 H, (heightRestrictedRatioSet p H (H / d)).card := by
  rw [← positiveRatioSet_height_weight_sum_eq]
  exact boundedCongruenceCount_le_four_height_sum hodd hHp

/-- A common height-linear ratio bound at all T≤H yields the full congruence
bound with only the harmonic loss 1+log H. For odd p and H<p, apply the exact
scale exchange and the existing divisor-sum inequality. The ratio premise is
kept explicit for subsequent uniform eight-degree estimates. -/
theorem boundedCongruenceCount_le_of_uniform_height_ratios {p H : ℕ} [Fact p.Prime] {C beta : ℝ}
    (hodd : Odd p) (hHp : H < p) (hC : 0 ≤ C)
    (hR : ∀ T : ℕ, T ≤ H → ((heightRestrictedRatioSet p H T).card : ℝ) ≤ C * T * (p : ℝ) ^ beta) :
    (boundedCongruenceCount p H : ℝ) ≤ 4 * C * H * (1 + Real.log H) * (p : ℝ) ^ beta := by
  have hcount := Nat.cast_le (α := ℝ).mpr (boundedCongruenceCount_le_sum_restricted_card hodd hHp)
  have hcount' :
    (boundedCongruenceCount p H : ℝ) ≤
      4 * ∑ d ∈ Finset.Icc 1 H, ((heightRestrictedRatioSet p H (H / d)).card : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using hcount
  have hsum := Finset.sum_le_sum (s := Finset.Icc 1 H) (fun d _ ↦ hR (H / d) (Nat.div_le_self H d))
  have hsum' :
    (∑ d ∈ Finset.Icc 1 H, ((heightRestrictedRatioSet p H (H / d)).card : ℝ)) ≤
      C * (p : ℝ) ^ beta * ∑ d ∈ Finset.Icc 1 H, ((H / d : ℕ) : ℝ) := by
    simpa only [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hsum
  have hlog :=
    mul_le_mul_of_nonneg_left (sum_nat_div_le_log H)
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg p) beta))
  rw [Nat.cast_sum] at hlog
  calc
    _ ≤ 4 * (C * (p : ℝ) ^ beta * ∑ d ∈ Finset.Icc 1 H, ((H / d : ℕ) : ℝ)) :=
      hcount'.trans (mul_le_mul_of_nonneg_left hsum' (by norm_num only))
    _ ≤ 4 * (C * (p : ℝ) ^ beta * ((H : ℝ) * (1 + Real.log H))) :=
      mul_le_mul_of_nonneg_left hlog (by norm_num only)
    _ = _ := by ring

end PseudoPrime.NumberTheory.Heilbronn
