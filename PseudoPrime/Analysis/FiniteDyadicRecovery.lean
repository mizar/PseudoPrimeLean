/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteQuadraticHeightWeights

/-! # Finite dyadic recovery from half-scale difference bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A finite sequence in a seminormed additive commutative group has total
displacement at most `2B` when its successive differences are bounded by
`B / 2^k` with `B ≥ 0`. Telescope the finite differences and sum the geometric
majorant. This is the norm estimate for recovering an unsplit smoothed sum. -/
theorem norm_dyadic_telescope_le_two {E : Type*} [SeminormedAddCommGroup E] (a : ℕ → E) {B : ℝ}
    (hB : 0 ≤ B) (K : ℕ) (hstep : ∀ k < K, ‖a k - a (k + 1)‖ ≤ B * (1 / 2 : ℝ) ^ k) :
    ‖a 0 - a K‖ ≤ 2 * B := by
  have hg : HasSum (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) 2 := by
    convert
      hasSum_geometric_of_lt_one (by norm_num only : (0 : ℝ) ≤ 1 / 2)
        (by norm_num only : (1 / 2 : ℝ) < 1) using
      1
    norm_num only
  have hs : ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k ≤ 2 :=
    (hg.summable.sum_le_tsum (Finset.range K) (fun k _ ↦ pow_nonneg (by norm_num only) k)).trans_eq
      hg.tsum_eq
  rw [← Finset.sum_range_sub' a K]
  calc
    _ ≤ ∑ k ∈ Finset.range K, ‖a k - a (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range K, B * (1 / 2 : ℝ) ^ k :=
      Finset.sum_le_sum (fun k hk ↦ hstep k (Finset.mem_range.mp hk))
    _ = B * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
    _ ≤ B * 2 := mul_le_mul_of_nonneg_left hs hB
    _ = _ := by ring

/-- For `x ≥ L > 0`, one dyadic rescaling of `x` lies in `[L,2L)`.
Choose the binary logarithm of the floor of `x/L` and use its adjacent power
bounds. This fixes a finite stopping scale without an infinite telescope. -/
theorem exists_dyadic_scale_between {x L : ℝ} (hL : 0 < L) (hxL : L ≤ x) :
    ∃ K : ℕ, L ≤ x / (2 : ℝ) ^ K ∧ x / (2 : ℝ) ^ K < 2 * L := by
  have hr : 1 ≤ x / L := (le_div_iff₀ hL).mpr (by simpa only [one_mul] using hxL)
  let n := ⌊x / L⌋₊
  let K := Nat.log 2 n
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.floor_pos.mpr hr)
  have hlo := Nat.pow_log_le_self 2 hn
  have hlo' : (2 : ℝ) ^ K ≤ x / L := by
    have hc : (2 : ℝ) ^ K ≤ (n : ℝ) := by exact_mod_cast hlo
    exact hc.trans (Nat.floor_le (zero_le_one.trans hr))
  have hhi := Nat.lt_pow_succ_log_self (by norm_num only : 1 < 2) n
  have hh : x / L < (2 : ℝ) ^ (K + 1) := by
    have hf := Nat.lt_floor_add_one (x / L)
    have hn' : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (K + 1) := by exact_mod_cast hhi
    exact lt_of_lt_of_le hf hn'
  have hp : 0 < (2 : ℝ) ^ K := pow_pos (by norm_num only) _
  refine ⟨K, ?_, ?_⟩
  · apply (le_div_iff₀ hp).mpr
    have h := (le_div_iff₀ hL).mp hlo'
    nlinarith only [h]
  · apply (div_lt_iff₀ hp).mpr
    have h := (div_lt_iff₀ hL).mp hh
    rw [pow_succ] at h
    nlinarith only [h]

/-- For a function into a seminormed additive commutative group, a half-scale
error at most `εt` above `L > 0` and a local bound `M` on `[L,2L)` imply
`‖f x‖ ≤ 2εx + M` for every `x ≥ L`. Stop at a dyadic scale in the local
interval and sum the finite half-scale errors. This retains a concrete small-scale
remainder for uniform arithmetic estimates. -/
theorem norm_le_two_half_scale_error_add_local_bound {E : Type*} [SeminormedAddCommGroup E]
    (f : ℝ → E) {ε L M x : ℝ} (hε : 0 ≤ ε) (hL : 0 < L) (hx : L ≤ x)
    (hlocal : ∀ t : ℝ, L ≤ t → t < 2 * L → ‖f t‖ ≤ M)
    (hhalf : ∀ t : ℝ, L ≤ t → ‖f t - f (t / 2)‖ ≤ ε * t) : ‖f x‖ ≤ 2 * ε * x + M := by
  obtain ⟨K, hKlo, hKhi⟩ := exists_dyadic_scale_between hL hx
  have hxpos : 0 < x := hL.trans_le hx
  have hstep (k : ℕ) (hk : k < K) :
    ‖f (x / (2 : ℝ) ^ k) - f (x / (2 : ℝ) ^ (k + 1))‖ ≤ (ε * x) * (1 / 2 : ℝ) ^ k := by
    have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num only) hk.le
    have hscale : L ≤ x / (2 : ℝ) ^ k :=
      hKlo.trans (div_le_div_of_nonneg_left hxpos.le (pow_pos (by norm_num only) _) hpow)
    have h := hhalf (x / (2 : ℝ) ^ k) hscale
    rw [pow_succ, div_mul_eq_div_div]
    convert h using 1
    rw [one_div_pow]
    ring
  have ht :=
    norm_dyadic_telescope_le_two (fun k ↦ f (x / (2 : ℝ) ^ k)) (mul_nonneg hε hxpos.le) K hstep
  simp only [pow_zero, div_one] at ht
  have hb := hlocal (x / (2 : ℝ) ^ K) hKlo hKhi
  have hn := norm_add_le (f x - f (x / (2 : ℝ) ^ K)) (f (x / (2 : ℝ) ^ K))
  rw [sub_add_cancel] at hn
  nlinarith only [ht, hb, hn]

/-- For a finite family of functions, an aggregate half-scale error `εt` and
individual local bounds `M i` imply a full aggregate bound `2εx + Σ M i`.
Apply finite dyadic recovery to the sum of norms and use the reverse triangle
inequality for each increment. The main error retains the family-wide budget;
the number of indices only affects the explicit local remainder. -/
theorem sum_norm_le_two_half_scale_error_add_local_bound {ι E : Type*} [SeminormedAddCommGroup E]
    (S : Finset ι) (f : ι → ℝ → E) (M : ι → ℝ) {ε L x : ℝ} (hε : 0 ≤ ε) (hL : 0 < L) (hx : L ≤ x)
    (hlocal : ∀ t : ℝ, L ≤ t → t < 2 * L → ∀ i ∈ S, ‖f i t‖ ≤ M i)
    (hhalf : ∀ t : ℝ, L ≤ t → ∑ i ∈ S, ‖f i t - f i (t / 2)‖ ≤ ε * t) :
    ∑ i ∈ S, ‖f i x‖ ≤ 2 * ε * x + ∑ i ∈ S, M i := by
  let g := fun t ↦ ∑ i ∈ S, ‖f i t‖
  have hnorm (t : ℝ) : ‖g t‖ = g t :=
    Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ ↦ norm_nonneg (f i t)))
  have hsmall (t : ℝ) (htlo : L ≤ t) (hthi : t < 2 * L) : ‖g t‖ ≤ ∑ i ∈ S, M i := by
    rw [hnorm]
    exact Finset.sum_le_sum (hlocal t htlo hthi)
  have hstep (t : ℝ) (ht : L ≤ t) : ‖g t - g (t / 2)‖ ≤ ε * t := by
    have hbound : ‖g t - g (t / 2)‖ ≤ ∑ i ∈ S, ‖f i t - f i (t / 2)‖ := by
      change ‖(∑ i ∈ S, ‖f i t‖) - ∑ i ∈ S, ‖f i (t / 2)‖‖ ≤ _
      rw [← Finset.sum_sub_distrib]
      exact
        (norm_sum_le _ _).trans
          (Finset.sum_le_sum
            (fun i _ ↦ by
              simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (f i t) (f i (t / 2))))
    exact hbound.trans (hhalf t ht)
  have hb := norm_le_two_half_scale_error_add_local_bound g hε hL hx hsmall hstep
  rwa [hnorm] at hb

end PseudoPrime.Analysis
