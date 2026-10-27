/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.SmoothPrimeProductCount
public import PseudoPrime.Analysis.RationalHeilbronnSmoothBudget
public import PseudoPrime.NumberTheory.Heilbronn.RationalEnergyScales

/-! # Smooth supply and Fermat witnesses for rational Heilbronn scales -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For 1<t/a<A, eventually smooth products with prime factors up to log(p)^A
outnumber the subgroup interval bound at every cutoff p^t<=k^a<=2^a*p^t.
Combine strict logarithmic margins with Chebyshev supply and binomial growth.
The threshold depends only on a,t,A, and no finite certificate is needed. -/
theorem eventually_smooth_count_at_rational_cutoff {a t : ℕ} {A : ℝ} (ha : 0 < a)
    (hκ : 1 < (t : ℝ) / a) (hA : (t : ℝ) / a < A) :
    Filter.Eventually
      (fun p : ℕ ↦
        ∀ k : ℕ,
          0 < k →
            p ^ t ≤ k ^ a →
            k ^ a ≤ 2 ^ a * p ^ t →
            256 * k ≤ p * (Nat.smoothNumbersUpTo k (Nat.floor ((Real.log p) ^ A) + 1)).card)
      Filter.atTop := by
  obtain ⟨b, c, beta, hb, hbA, hc, hcA, hbeta, hcb⟩ :=
    Analysis.choose_smooth_parameters_of_cutoff hκ hA
  have hAp : 0 < A := (zero_lt_one.trans hb).trans hbA
  have hbetap : 0 < beta := (lt_trans (sub_pos.mpr hκ) hbeta)
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
        hbetap)
  have hlogc := hL.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (2 * c))
  filter_upwards [hM, hBfloor, hCfloor, hlogc, hL.eventually hgap, hL.eventually_ge_atTop 2,
    Filter.eventually_gt_atTop (0 : ℕ),
    Analysis.eventually_rational_cutoff_le_prime_mul_floor_power ha hκ hbeta] with p hMp hBf hCf hcL
    hg hLp hp henv
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
  have hgapL : c * A * L + A * Real.log L < ((t : ℝ) / a) * L := by
    have hm := (div_lt_div_iff₀ hLpos hAp).mp hg
    nlinarith only [hm]
  have hsize : B ^ s < k :=
    Analysis.product_lt_rational_cutoff_of_log_scale ha hp hBpos hk hL1 hAp
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

/-- Every A>13/7 admits a rational scale t/a strictly between 13/7 and min(A,2).
Choose a positive rational between these real endpoints and expose its natural
numerator and positive denominator. This fixes all auxiliary scales before p varies. -/
theorem exists_rational_scale_above_thirteen_sevenths {A : ℝ} (hA : (13 / 7 : ℝ) < A) :
    ∃ a t : ℕ, 0 < a ∧ 13 * a < 7 * t ∧ t < 2 * a ∧ (t : ℝ) / a < A := by
  have hint : (13 / 7 : ℝ) < min A 2 := lt_min hA (by norm_num only)
  obtain ⟨q, hlo, hhi⟩ := exists_rat_btwn hint
  have hq0 : (0 : ℝ) ≤ q := (lt_trans (by norm_num only : (0 : ℝ) < 13 / 7) hlo).le
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr (Rat.cast_nonneg.mp hq0)
  have he : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) ((Int.natCast_natAbs q.num).trans (abs_of_nonneg hn))
  rw [Rat.cast_def, ← he] at hlo hhi
  have haR : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hgapR : (13 : ℝ) * q.den < 7 * q.num.natAbs := by
    have h := (lt_div_iff₀ haR).mp hlo
    nlinarith only [h]
  have hsmallR : (q.num.natAbs : ℝ) < 2 * q.den :=
    (div_lt_iff₀ haR).mp (hhi.trans_le (min_le_right A 2))
  refine ⟨q.den, q.num.natAbs, q.pos, ?_, ?_, hhi.trans_le (min_le_left A 2)⟩
  · exact_mod_cast hgapR
  · exact_mod_cast hsmallR

/-- For every fixed A>13/7, sufficiently large odd primes p have a prime
q<=log(p)^A with q^(p-1) nontrivial modulo p². Fix a rational scale below A,
combine its proved interval and smooth-count bounds, and extract a prime factor.
The threshold depends only on A; GRH and external Fermat estimates are absent. -/
theorem eventually_exists_prime_nontrivial_power_of_thirteen_sevenths {A : ℝ}
    (hA : (13 / 7 : ℝ) < A) :
    Filter.Eventually
      (fun p : ℕ ↦
        p.Prime →
          p ≠ 2 → ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ (Real.log p) ^ A ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1)
      Filter.atTop := by
  obtain ⟨a, t, ha, hgap, hsmall, hscale⟩ := exists_rational_scale_above_thirteen_sevenths hA
  have hat : a < t := by nlinarith only [hgap, ha]
  have hκ : 1 < (t : ℝ) / a := (one_lt_div (Nat.cast_pos.mpr ha)).mpr (Nat.cast_lt.mpr hat)
  obtain ⟨P, hP⟩ := exists_uniform_rational_heilbronn_interval_bound ha hgap hsmall
  filter_upwards [eventually_smooth_count_at_rational_cutoff ha hκ hscale,
    Filter.eventually_ge_atTop P] with p hsm hlarge hp hp2
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk, hkp, hlo, hhi, hcount⟩ := hP p (hp.odd_of_ne_two hp2) hlarge
  obtain ⟨q, hq, hqB, hpow⟩ :=
    exists_prime_nontrivial_power_of_interval_and_smooth hcount (hsm k hk hlo hhi)
  have hB := Nat.lt_add_one_iff.mp hqB
  have hle : (q : ℝ) ≤ (Real.log p) ^ A :=
    (Nat.cast_le.mpr hB).trans
      (Nat.floor_le (Real.rpow_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hp.one_lt.le)) _))
  exact ⟨q, hq, hle, hpow⟩

end PseudoPrime.NumberTheory.Heilbronn
