/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.SmoothPrimeProductCount
public import PseudoPrime.Analysis.HeilbronnSmoothLogarithmicBudget

/-! # A quantitative smooth-number supply at the Heilbronn cutoff -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Eventually, uniformly for all cutoffs p^28<=k^15<=32768p^28, the
floor(log(p)^(15/8))+1-smooth integers up to k satisfy 256k<=p times their count.
Use squarefree products, Chebyshev prime supply and the rational margins
b=1873/1000, c=199/200 and beta=217/250; no analytic hypothesis is assumed. -/
theorem eventually_smooth_count_at_cutoff :
    Filter.Eventually
      (fun p : ℕ ↦
        ∀ k : ℕ,
          0 < k →
            p ^ 28 ≤ k ^ 15 →
            k ^ 15 ≤ 32768 * p ^ 28 →
            256 * k ≤
              p * (Nat.smoothNumbersUpTo k (Nat.floor ((Real.log p) ^ (15 / 8 : ℝ)) + 1)).card)
      Filter.atTop := by
  let A : ℝ := 15 / 8
  let b : ℝ := 1873 / 1000
  let c : ℝ := 199 / 200
  let beta : ℝ := 217 / 250
  have hAp : 0 < A := by norm_num only [A]
  have hb : 1 < b := by norm_num only [b]
  have hbA : b < A := by norm_num only [b, A]
  have hc : 0 < c := by norm_num only [c]
  have hcA : c * A < (28 / 15 : ℝ) := by norm_num only [c, A]
  have hcb : beta < c * (b - 1) := by norm_num only [beta, c, b]
  have hL : Filter.Tendsto (fun p : ℕ ↦ Real.log p) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hgap := hratio.eventually_lt_const (div_pos (sub_pos.mpr hcA) hAp)
  have hM :=
    hL.eventually
      (NumberTheory.eventually_const_mul_rpow_le_primeCounting_floor_rpow (C := 2)
        (zero_lt_one.trans hb) hbA)
  have hBfloor :=
    hL.eventually (NumberTheory.eventually_rpow_le_nat_floor_rpow (b := 0) (by norm_num only) hAp)
  have hCfloor :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (NumberTheory.eventually_rpow_le_nat_floor_rpow (b := 0) (A := beta) (by norm_num only)
        (by norm_num only [beta]))
  have hlogc := hL.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (2 * c))
  filter_upwards [hM, hBfloor, hCfloor, hlogc, hL.eventually hgap, hL.eventually_ge_atTop 2,
    Filter.eventually_gt_atTop (0 : ℕ), Analysis.eventually_cutoff_le_prime_mul_floor_power] with p
    hMp hBf hCf hcL hg hLp hp henv
  intro k hk hlo hhi
  let L := Real.log (p : ℝ)
  let B := Nat.floor (L ^ A)
  let C := Nat.floor ((p : ℝ) ^ beta)
  let s := Nat.ceil (c * L / Real.log L)
  have hL2 : 2 ≤ L := hLp
  have hL1 : 1 < L := lt_of_lt_of_le (by norm_num only) hL2
  have hLpos : 0 < L := zero_lt_one.trans hL1
  have hBpos : 0 < B := by
    apply (Nat.cast_pos (α := ℝ)).mp
    have hf : (1 : ℝ) ≤ B := by simpa only [Real.rpow_zero] using hBf
    exact zero_lt_one.trans_le hf
  have hCpos : 0 < C := by
    apply (Nat.cast_pos (α := ℝ)).mp
    have hf : (1 : ℝ) ≤ C := by simpa only [Real.rpow_zero] using hCf
    exact zero_lt_one.trans_le hf
  obtain ⟨hs, hsL, hslo, hshi⟩ := Analysis.ceil_log_scale_bounds hc hL2 hcL
  have hgapL : c * A * L + A * Real.log L < (28 / 15 : ℝ) * L := by
    have hm := (div_lt_div_iff₀ hLpos hAp).mp hg
    nlinarith only [hm]
  have hsize : B ^ s < k :=
    Analysis.product_lt_cutoff_of_log_scale hp hBpos hk hL1 hAp
      (Nat.floor_le (Real.rpow_nonneg hLpos.le A)) hshi hgapL hlo
  have hlogC : Real.log C ≤ beta * L := by
    have hf := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) beta)
    have hh := Real.log_le_log (Nat.cast_pos.mpr hCpos) hf
    rw [Real.log_rpow (Nat.cast_pos.mpr hp) beta] at hh
    exact hh
  have hbudget : C * s ^ s < (B.primeCounting + 1 - s) ^ s :=
    Analysis.subgroup_power_budget_of_log_scale hCpos hL1 hb hcb hs hsL hslo hMp hlogC
  have hchoose := NumberTheory.card_lt_choose_of_power_budget hbudget
  have hsmooth :=
    choose_le_smoothNumbersUpTo_card (S := B.primesLE) (fun q hq ↦ (Nat.mem_primesLE.mp hq).2)
      (fun q hq ↦ (Nat.mem_primesLE.mp hq).1) hsize.le
  rw [Nat.primesLE_card_eq_primeCounting] at hsmooth
  exact (henv k hhi).trans (Nat.mul_le_mul_left p (hchoose.le.trans hsmooth))

end PseudoPrime.NumberTheory.Heilbronn
