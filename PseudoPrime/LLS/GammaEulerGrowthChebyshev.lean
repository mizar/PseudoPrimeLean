/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannWeightedErrorBounds
public import PseudoPrime.LLS.RiemannOneSidedCheckpoint
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.Analysis.GammaEulerPositiveLowerBound
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences

/-! # Analytic Chebyshev blocks and growing positive Euler prefixes -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: RH and x>=50000. Claim: the logarithmically weighted Mangoldt
error is at most (3/20)sqrt(x). Retain the refined square-root and logarithm
terms and use the logarithm tangent at 256. Role: quantify large-scale psi bounds. -/
theorem logWeightedMangoldtSum_error_le_three_twentieths_sqrt (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 50000 ≤ x) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x| ≤
      (3 / 20 : ℝ) * Real.sqrt x := by
  have hx1 : 1 < x := by linarith only [hx]
  have hx0 := zero_lt_one.trans hx1
  have hs : (220 : ℝ) ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by norm_num only) hx0.le).mpr
    linarith only [hx]
  have he := Real.log_pow (2 : ℝ) 8
  norm_num only [Nat.cast_ofNat] at he
  have ht :=
    Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 256) (Real.sqrt_pos.mpr hx0)
  rw [Real.log_sqrt hx0.le] at ht
  have hl : Real.log x ≤ Real.sqrt x / 20 := by linarith only [ht, he, hs, Real.log_two_lt_d9]
  have h := logWeightedMangoldtSum_error_le_refined hRH hx1
  linarith only [h, hl, hs]

/-- Input: RH and t>=100000. Claim: (93/100)t<=psi(t)<=(27/25)t.
Compare smoothed sums at 19t/20,t,21t/20 and use the sharp half-line error.
Role: supply analytic interval mass without prime-power enumeration. -/
theorem psi_bounds_of_hundred_thousand_le (hRH : RiemannHypothesis) {t : ℝ} (ht : 100000 ≤ t) :
    (93 / 100 : ℝ) * t ≤ Chebyshev.psi t ∧ Chebyshev.psi t ≤ (27 / 25 : ℝ) * t := by
  have ht0 : 0 < t := by linarith only [ht]
  have hs := Real.sqrt_nonneg t
  have hsq := Real.sq_sqrt ht0.le
  have hs300 : (300 : ℝ) ≤ Real.sqrt t :=
    (Real.le_sqrt (by norm_num only) ht0.le).mpr (by linarith only [ht])
  have hg : 300 * Real.sqrt t ≤ t := by
    nlinarith only [hsq, mul_nonneg (by linarith only [hs300] : 0 ≤ Real.sqrt t - 300) hs]
  have hsmall : Real.sqrt ((19 / 20 : ℝ) * t) ≤ Real.sqrt t :=
    Real.sqrt_le_sqrt (by linarith only [ht0])
  have hbig : Real.sqrt ((21 / 20 : ℝ) * t) ≤ (11 / 10 : ℝ) * Real.sqrt t := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨mul_nonneg (by norm_num only) hs, by nlinarith only [hsq]⟩
  have hl :=
    (AnalyticNumberTheory.Arithmetic.psi_bounds_of_logWeighted_error_without_log
        (by linarith only [ht0] : 0 < (19 / 20 : ℝ) * t)
        (by linarith only [ht0] : (19 / 20 : ℝ) * t < t)
        (logWeightedMangoldtSum_error_le_three_twentieths_sqrt hRH (by linarith only [ht]))
        (logWeightedMangoldtSum_error_le_three_twentieths_sqrt hRH (by linarith only [ht]))).2
  have hu :=
    (AnalyticNumberTheory.Arithmetic.psi_bounds_of_logWeighted_error_without_log ht0
        (by linarith only [ht0] : t < (21 / 20 : ℝ) * t)
        (logWeightedMangoldtSum_error_le_three_twentieths_sqrt hRH (by linarith only [ht]))
        (logWeightedMangoldtSum_error_le_three_twentieths_sqrt hRH (by linarith only [ht]))).1
  have hlr : ((19 / 20 : ℝ) * t) / (t - (19 / 20) * t) = 19 := by
    apply (div_eq_iff (by linarith only [ht0] : t - (19 / 20 : ℝ) * t ≠ 0)).mpr
    ring
  have hur : ((21 / 20 : ℝ) * t) / ((21 / 20) * t - t) = 21 := by
    apply (div_eq_iff (by linarith only [ht0] : (21 / 20 : ℝ) * t - t ≠ 0)).mpr
    ring
  rw [mul_div_assoc, hlr] at hl
  rw [mul_div_assoc, hur] at hu
  constructor <;> linarith only [hl, hu, hsmall, hbig, hg]

/-- Input: 0<t<=(5/2)^20. Claim: t^(-1/20)>=2/5. Apply antitonicity
and combine real powers. Role: bound the endpoint weight of every doubling block. -/
theorem rpow_neg_twentieth_ge_two_fifths {t : ℝ} (ht0 : 0 < t) (ht : t ≤ (5 / 2 : ℝ) ^ (20 : ℕ)) :
    (2 / 5 : ℝ) ≤ t ^ (-1 / 20 : ℝ) := by
  have h := Real.rpow_le_rpow_of_nonpos ht0 ht (by norm_num only : (-1 / 20 : ℝ) ≤ 0)
  rw [← Real.rpow_natCast (5 / 2 : ℝ) 20, ← Real.rpow_mul (by norm_num only : (0 : ℝ) ≤ 5 / 2)] at h
  norm_num only [show (20 : ℝ) * (-1 / 20) = -1 by norm_num only, Real.rpow_neg_one] at h
  simpa only [neg_div] using h

/-- Input: RH, a>=100000, 2a<=90000000 and a prefix credit at a.
Claim: the prefix through 2a gains at least 39/500. Keep the positive Euler
lower bound and the analytic psi increment. Role: replace finite block certificates. -/
theorem gamma_euler_prefix_doubling_gain (hRH : RiemannHypothesis) {a : ℕ} (ha : 100000 ≤ a)
    (hb : 2 * a ≤ 90000000) {C : ℝ}
    (hC : C ≤ ∑ k ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight k) :
    C + 39 / 500 ≤ ∑ k ∈ Finset.Ioc 0 (2 * a), Analysis.gammaResolventMangoldtWeight k := by
  have haR : (100000 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (2 : ℝ) * a ≤ 90000000 := by exact_mod_cast hb
  have hap := psi_bounds_of_hundred_thousand_le hRH haR
  have hbp :=
    psi_bounds_of_hundred_thousand_le hRH (show (100000 : ℝ) ≤ (2 : ℝ) * a by linarith only [haR])
  have hd : (39 / 100 : ℝ) * ((2 : ℝ) * a) ≤ Chebyshev.psi ((2 : ℝ) * a) - Chebyshev.psi a := by
    linarith only [hap.2, hbp.1]
  have hp :=
    rpow_neg_twentieth_ge_two_fifths (show (0 : ℝ) < (2 : ℝ) * a by linarith only [haR])
      (show (2 : ℝ) * a ≤ (5 / 2 : ℝ) ^ (20 : ℕ) by
        norm_num only at hbR ⊢; linarith only [hbR])
  have he : (((2 : ℝ) * a) ^ (-21 / 20 : ℝ)) * ((2 : ℝ) * a) = ((2 : ℝ) * a) ^ (-1 / 20 : ℝ) := by
    calc
      _ = ((2 : ℝ) * a) ^ (-21 / 20 : ℝ) * ((2 : ℝ) * a) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ((2 : ℝ) * a) ^ ((-21 / 20 : ℝ) + 1) := (Real.rpow_add (by linarith only [haR]) _ _).symm
      _ = _ := by norm_num only
  have hg :=
    Analysis.gamma_euler_prefix_lower_growth (show a ≤ 2 * a by nlinarith only [Nat.zero_le a]) hC
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, neg_div] at hg
  have hm :=
    mul_le_mul_of_nonneg_left hd
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)
        (Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) * a by linarith only [haR]) (-21 / 20 : ℝ)))
  have hex :
    (1 / 2 : ℝ) * ((2 : ℝ) * a) ^ (-21 / 20 : ℝ) * ((39 / 100 : ℝ) * ((2 : ℝ) * a)) =
      (39 / 200 : ℝ) * ((2 : ℝ) * a) ^ (-1 / 20 : ℝ) := by
    rw [← he]
    ring
  rw [hex] at hm
  norm_num only at hg hm hp
  linarith only [hg, hm, hp]

/-- Input: RH, an initial prefix credit at a>=100000 and an admissible final
cutoff a*2^k<=90000000. Claim: the credit grows by (39/500)k. Induct on k
using the uniform doubling lemma. Role: avoid enumerating prime powers or blocks. -/
theorem gamma_euler_prefix_lower_doublings (hRH : RiemannHypothesis) {a : ℕ} (ha : 100000 ≤ a)
    {C : ℝ} (hC : C ≤ ∑ n ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight n) (k : ℕ) :
    a * 2 ^ k ≤ 90000000 →
      C + (39 / 500 : ℝ) * k ≤
        ∑ n ∈ Finset.Ioc 0 (a * 2 ^ k), Analysis.gammaResolventMangoldtWeight n := by
  induction k with
  | zero =>
    intro _
    simpa only [pow_zero, mul_one, Nat.cast_zero, mul_zero, add_zero] using hC
  | succ k ih =>
    intro htop
    have heq : a * 2 ^ (k + 1) = 2 * (a * 2 ^ k) := by
      rw [pow_succ]; ring
    have hsmall : a * 2 ^ k ≤ a * 2 ^ (k + 1) := by
      rw [heq]
      nlinarith only [Nat.zero_le (a * 2 ^ k)]
    have hpow : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num only : 0 < (2 : ℕ)) _
    have hlow : a ≤ a * 2 ^ k := by nlinarith only [hpow, Nat.zero_le a]
    have hg :=
      gamma_euler_prefix_doubling_gain hRH (ha.trans hlow)
        (show 2 * (a * 2 ^ k) ≤ 90000000 by
          rw [← heq]; exact htop)
        (ih (hsmall.trans htop))
    rw [heq]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith only [hg]

/-- Input: RH and a cutoff b>=51200000. Claim: its Euler prefix is at least
32003/5000. Apply nine symbolic doublings to the existing analytic seed and
use prefix monotonicity. Role: provide a stronger actual credit for witness bounds. -/
theorem gamma_prefix51200000_lower_halfline (hRH : RiemannHypothesis) {b : ℝ} (hb : 51200000 ≤ b) :
    (32003 / 5000 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight n := by
  have hs := gamma_prefix50000_lower_asymmetric hRH (by norm_num only : (50000 : ℝ) ≤ 100000)
  have hsN :
    (28493 / 5000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 (100000 : ℕ), Analysis.gammaResolventMangoldtWeight n := by
    simpa only [Nat.floor_ofNat] using hs
  have hg :=
    gamma_euler_prefix_lower_doublings hRH (by norm_num only : (100000 : ℕ) ≤ 100000) hsN 9
      (by norm_num only : (100000 : ℕ) * 2 ^ 9 ≤ 90000000)
  change
    (28493 / 5000 : ℝ) + (39 / 500 : ℝ) * 9 ≤
      ∑ n ∈ Finset.Ioc 0 (51200000 : ℕ), Analysis.gammaResolventMangoldtWeight n at hg
  have hc :
    ((32003 / 5000 : ℚ) : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 (51200000 : ℕ), Analysis.gammaResolventMangoldtWeight n := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    linarith only [hg]
  have hf := Nat.floor_mono hb
  norm_num only [Nat.floor_ofNat] at hf
  have h := Analysis.gamma_euler_prefix_lower_mono hf hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: a>=900. Claim: the asymmetric mass budget for [a,2a],
with probes 7a/4 and 5a/4, is at least a/4. Keep separate root/log errors
and use a logarithmic tangent at 1024. Role: quantify positive doubling
blocks at scales below the fixed short-block checkpoints. -/
theorem psi_asymmetric_doubling_block_lower {a : ℝ} (ha : 900 ≤ a) :
    a / 4 ≤ psiAsymmetricBlockLower a (2 * a) ((7 / 4 : ℝ) * a) ((5 / 4 : ℝ) * a) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hs := Real.sqrt_nonneg a
  have hsq := Real.sq_sqrt ha0.le
  have hs30 : (30 : ℝ) ≤ Real.sqrt a :=
    (Real.le_sqrt (by norm_num only) ha0.le).mpr (by linarith only [ha])
  have hroot : Real.sqrt a ≤ a / 30 := by
    nlinarith only [hsq, mul_nonneg (by linarith only [hs30] : 0 ≤ Real.sqrt a - 30) hs]
  have h1 : Real.sqrt ((7 / 4 : ℝ) * a) ≤ (4 / 3 : ℝ) * Real.sqrt a := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨mul_nonneg (by norm_num only) hs, by nlinarith only [hsq, ha0]⟩
  have h2 : Real.sqrt (2 * a) ≤ (3 / 2 : ℝ) * Real.sqrt a := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨mul_nonneg (by norm_num only) hs, by nlinarith only [hsq, ha0]⟩
  have h3 : Real.sqrt ((5 / 4 : ℝ) * a) ≤ (6 / 5 : ℝ) * Real.sqrt a := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨mul_nonneg (by norm_num only) hs, by nlinarith only [hsq, ha0]⟩
  have he := Real.log_pow (2 : ℝ) 10
  norm_num only [Nat.cast_ofNat] at he
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 1024) ha0
  have hlog : Real.log a ≤ a / 130 := by linarith only [he, ht, Real.log_two_lt_d9, ha]
  have hlogb : Real.log (2 * a) ≤ a / 130 + 7 / 10 := by
    rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) ha0.ne']
    linarith only [hlog, Real.log_two_lt_d9]
  have hlo : ((7 / 4 : ℝ) * a) / (2 * a - (7 / 4) * a) = 7 := by
    apply (div_eq_iff (by linarith only [ha0] : 2 * a - (7 / 4 : ℝ) * a ≠ 0)).mpr
    ring
  have hhi : ((5 / 4 : ℝ) * a) / ((5 / 4 : ℝ) * a - a) = 5 := by
    apply (div_eq_iff (by linarith only [ha0] : (5 / 4 : ℝ) * a - a ≠ 0)).mpr
    ring
  dsimp only [psiAsymmetricBlockLower]
  rw [mul_div_assoc, hlo, mul_div_assoc, hhi]
  linarith only [h1, h2, h3, hroot, hlog, hlogb, ha]

/-- Input: RH and a>=900. Claim: psi(2a)-psi(a)>=a/4. Combine the
continuous asymmetric comparison and the uniform doubling budget.
Role: provide analytic mass without a finite prime-power table. -/
theorem psi_doubling_block_lower (hRH : RiemannHypothesis) {a : ℝ} (ha : 900 ≤ a) :
    a / 4 ≤ Chebyshev.psi (2 * a) - Chebyshev.psi a := by
  have hd :=
    psi_sub_psi_ge_asymmetric_rh_bound hRH (show (1 : ℝ) < (7 / 4 : ℝ) * a by linarith only [ha])
      (show (7 / 4 : ℝ) * a < 2 * a by linarith only [ha]) (show (1 : ℝ) < a by linarith only [ha])
      (show a < (5 / 4 : ℝ) * a by linarith only [ha])
  exact (psi_asymmetric_doubling_block_lower ha).trans hd

/-- Input: RH, a>=900, b>=2a and an Euler prefix credit at a.
Claim: the prefix through b gains at least (a/200)b^(-21/20). Use
monotonicity of psi, the uniform short block and the positive Euler weight.
Role: supply reusable growth below the large-scale doubling entrance. -/
theorem gamma_euler_prefix_lower_growth_of_doubling_block (hRH : RiemannHypothesis) {a b : ℕ}
    {C : ℝ} (ha : 900 ≤ a) (hratio : (2 : ℝ) * a ≤ b)
    (hC : C ≤ ∑ j ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight j) :
    C + ((a : ℝ) / 8) * (b : ℝ) ^ (-21 / 20 : ℝ) ≤
      ∑ j ∈ Finset.Ioc 0 b, Analysis.gammaResolventMangoldtWeight j := by
  have haR : (900 : ℝ) ≤ a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by linarith only [haR, hratio]
  have hab : a ≤ b := by exact_mod_cast habR
  have hl := psi_doubling_block_lower hRH haR
  have hm := Chebyshev.psi_mono hratio
  have hd : (a : ℝ) / 4 ≤ Chebyshev.psi b - Chebyshev.psi a := by linarith only [hl, hm]
  have hp :=
    mul_le_mul_of_nonneg_left hd
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)
        (Real.rpow_nonneg (Nat.cast_nonneg b) (-21 / 20 : ℝ)))
  have hg := Analysis.gamma_euler_prefix_lower_growth hab hC
  nlinarith only [hp, hg]

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: a>=10000. Claim: the asymmetric psi budget for [a,5a/4],
with probes 6a/5 and 21a/20, is at least a/100. Keep the root/log errors
and bound them uniformly by a tangent inequality.
Role: remove the large-scale entrance from analytic positive block mass. -/
theorem psi_asymmetric_five_fourths_block_lower {a : ℝ} (ha : 10000 ≤ a) :
    a / 100 ≤
      psiAsymmetricBlockLower a ((5 / 4 : ℝ) * a) ((6 / 5 : ℝ) * a) ((21 / 20 : ℝ) * a) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hs := Real.sqrt_nonneg a
  have hsq := Real.sq_sqrt ha0.le
  have hs100 : (100 : ℝ) ≤ Real.sqrt a :=
    (Real.le_sqrt (by norm_num only) ha0.le).mpr (by linarith only [ha])
  have hroot : Real.sqrt a ≤ a / 100 := by
    nlinarith only [hsq, mul_nonneg (by linarith only [hs100] : 0 ≤ Real.sqrt a - 100) hs]
  have h1 : Real.sqrt ((6 / 5 : ℝ) * a) ≤ (11 / 10 : ℝ) * Real.sqrt a := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨mul_nonneg (by norm_num only) hs, by nlinarith only [hsq, ha0]⟩
  have h2 : Real.sqrt ((5 / 4 : ℝ) * a) ≤ (6 / 5 : ℝ) * Real.sqrt a := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨mul_nonneg (by norm_num only) hs, by nlinarith only [hsq, ha0]⟩
  have h3 : Real.sqrt ((21 / 20 : ℝ) * a) ≤ (11 / 10 : ℝ) * Real.sqrt a := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨mul_nonneg (by norm_num only) hs, by nlinarith only [hsq, ha0]⟩
  have he := Real.log_pow (2 : ℝ) 14
  norm_num only [Nat.cast_ofNat] at he
  have hm :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 10000) (by norm_num only : (10000 : ℝ) ≤ 16384)
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 10000) ha0
  have hlog : Real.log a ≤ a / 1000 := by linarith only [he, hm, ht, Real.log_two_lt_d9, ha]
  have hlog5 := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 5 / 4)
  have hlogb : Real.log ((5 / 4 : ℝ) * a) ≤ a / 1000 + 1 / 4 := by
    rw [Real.log_mul (by norm_num only : (5 / 4 : ℝ) ≠ 0) ha0.ne']
    linarith only [hlog, hlog5]
  have hlo : ((6 / 5 : ℝ) * a) / ((5 / 4 : ℝ) * a - (6 / 5) * a) = 24 := by
    apply (div_eq_iff (by linarith only [ha0] : (5 / 4 : ℝ) * a - (6 / 5) * a ≠ 0)).mpr
    ring
  have hhi : ((21 / 20 : ℝ) * a) / ((21 / 20 : ℝ) * a - a) = 21 := by
    apply (div_eq_iff (by linarith only [ha0] : (21 / 20 : ℝ) * a - a ≠ 0)).mpr
    ring
  dsimp only [psiAsymmetricBlockLower]
  rw [mul_div_assoc, hlo, mul_div_assoc, hhi]
  linarith only [h1, h2, h3, hroot, hlog, hlogb, ha]

/-- Input: RH and a>=10000. Claim: psi(5a/4)-psi(a)>=a/100.
Combine the continuous asymmetric mass comparison with the uniform budget.
Role: supply positive blocks at scales below the former doubling entrance. -/
theorem psi_five_fourths_block_lower (hRH : RiemannHypothesis) {a : ℝ} (ha : 10000 ≤ a) :
    a / 100 ≤ Chebyshev.psi ((5 / 4 : ℝ) * a) - Chebyshev.psi a := by
  have hd :=
    psi_sub_psi_ge_asymmetric_rh_bound hRH (show (1 : ℝ) < (6 / 5 : ℝ) * a by linarith only [ha])
      (show (6 / 5 : ℝ) * a < (5 / 4 : ℝ) * a by linarith only [ha])
      (show (1 : ℝ) < a by linarith only [ha]) (show a < (21 / 20 : ℝ) * a by linarith only [ha])
  exact (psi_asymmetric_five_fourths_block_lower ha).trans hd

/-- Input: RH, a>=10000, b>=5a/4 and an Euler prefix credit at a.
Claim: the prefix through b gains at least (a/200)b^(-21/20). Use
monotonicity of psi, the uniform short block and the positive Euler weight.
Role: supply reusable growth below the large-scale doubling entrance. -/
theorem gamma_euler_prefix_lower_growth_of_five_fourths_block (hRH : RiemannHypothesis) {a b : ℕ}
    {C : ℝ} (ha : 10000 ≤ a) (hratio : (5 / 4 : ℝ) * a ≤ b)
    (hC : C ≤ ∑ j ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight j) :
    C + ((a : ℝ) / 200) * (b : ℝ) ^ (-21 / 20 : ℝ) ≤
      ∑ j ∈ Finset.Ioc 0 b, Analysis.gammaResolventMangoldtWeight j := by
  have haR : (10000 : ℝ) ≤ a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by linarith only [haR, hratio]
  have hab : a ≤ b := by exact_mod_cast habR
  have hl := psi_five_fourths_block_lower hRH haR
  have hm := Chebyshev.psi_mono hratio
  have hd : (a : ℝ) / 100 ≤ Chebyshev.psi b - Chebyshev.psi a := by linarith only [hl, hm]
  have hp :=
    mul_le_mul_of_nonneg_left hd
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)
        (Real.rpow_nonneg (Nat.cast_nonneg b) (-21 / 20 : ℝ)))
  have hg := Analysis.gamma_euler_prefix_lower_growth hab hC
  nlinarith only [hp, hg]

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: RH, ordered natural endpoints, an initial prefix credit and
1<s<b, 1<a<t. Claim: the explicit asymmetric psi block adds the displayed
Euler credit. Retain the endpoint weight in the actual prefix growth theorem.
Role: handle short blocks below the fixed large-scale doubling entrance. -/
theorem gamma_euler_prefix_lower_growth_of_asymmetric_rh_errors (hRH : RiemannHypothesis) {a b : ℕ}
    {s t C : ℝ} (hab : a ≤ b) (hs : 1 < s) (hsb : s < b) (ha : (1 : ℝ) < a) (hat : (a : ℝ) < t)
    (hC : C ≤ ∑ j ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight j) :
    C + (1 / 2 : ℝ) * (b : ℝ) ^ (-21 / 20 : ℝ) * psiAsymmetricBlockLower a b s t ≤
      ∑ j ∈ Finset.Ioc 0 b, Analysis.gammaResolventMangoldtWeight j := by
  have hd := psi_sub_psi_ge_asymmetric_rh_bound hRH hs hsb ha hat
  have hm :=
    mul_le_mul_of_nonneg_left hd
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)
        (Real.rpow_nonneg (Nat.cast_nonneg b) (-21 / 20 : ℝ)))
  have hg := Analysis.gamma_euler_prefix_lower_growth hab hC
  linarith only [hm, hg]

/-- Claim: the asymmetric block with endpoints 50000 and 62500 and
difference probes 60000 and 52500 has mass bound at least 5454. Bound four
square roots and both logarithms analytically. Role: certify a short block
without calculating a prime sum. -/
theorem psi_asymmetric_block_50000_62500_lower :
    (5454 : ℝ) ≤ psiAsymmetricBlockLower 50000 62500 60000 52500 := by
  have h1 : Real.sqrt (60000 : ℝ) ≤ 245 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  have h2 : Real.sqrt (62500 : ℝ) ≤ 250 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  have h3 : Real.sqrt (52500 : ℝ) ≤ 230 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  have h4 : Real.sqrt (50000 : ℝ) ≤ 224 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  have he := Real.log_pow (2 : ℝ) 16
  norm_num only [Nat.cast_ofNat] at he
  have h5 :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 62500) (by norm_num only : (62500 : ℝ) ≤ 65536)
  have h6 :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 50000) (by norm_num only : (50000 : ℝ) ≤ 65536)
  have hl1 : Real.log (62500 : ℝ) ≤ 56 / 5 := by linarith only [h5, he, Real.log_two_lt_d9]
  have hl2 : Real.log (50000 : ℝ) ≤ 56 / 5 := by linarith only [h6, he, Real.log_two_lt_d9]
  norm_num only [psiAsymmetricBlockLower]
  linarith only [h1, h2, h3, h4, hl1, hl2]

/-- Input: RH and a prefix credit at 50000. Claim: the prefix through
62500 gains at least 1/40. Use the certified asymmetric mass and a rational
lower bound on the endpoint power. Role: improve usable small-cutoff credits. -/
theorem gamma_euler_prefix_50000_62500_gain (hRH : RiemannHypothesis) {C : ℝ}
    (hC : C ≤ ∑ j ∈ Finset.Ioc 0 (50000 : ℕ), Analysis.gammaResolventMangoldtWeight j) :
    C + 1 / 40 ≤ ∑ j ∈ Finset.Ioc 0 (62500 : ℕ), Analysis.gammaResolventMangoldtWeight j := by
  have hd :=
    psi_sub_psi_ge_asymmetric_rh_bound hRH (by norm_num only : (1 : ℝ) < 60000)
      (by norm_num only : (60000 : ℝ) < 62500) (by norm_num only : (1 : ℝ) < 50000)
      (by norm_num only : (50000 : ℝ) < 52500)
  have hp := psi_asymmetric_block_50000_62500_lower.trans hd
  have hr :=
    Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 62500)
      (by norm_num only : (62500 : ℝ) ≤ (40 / 23 : ℝ) ^ (20 : ℕ))
      (by norm_num only : (-1 / 20 : ℝ) ≤ 0)
  rw [← Real.rpow_natCast (40 / 23 : ℝ) 20, ←
    Real.rpow_mul (by norm_num only : (0 : ℝ) ≤ 40 / 23)] at hr
  norm_num only [show (20 : ℝ) * (-1 / 20) = -1 by norm_num only, Real.rpow_neg_one] at hr
  have he : (62500 : ℝ) ^ (-21 / 20 : ℝ) * 62500 = (62500 : ℝ) ^ (-1 / 20 : ℝ) := by
    calc
      _ = (62500 : ℝ) ^ (-21 / 20 : ℝ) * (62500 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (62500 : ℝ) ^ ((-21 / 20 : ℝ) + 1) := (Real.rpow_add (by norm_num only) _ _).symm
      _ = _ := by norm_num only
  norm_num only [neg_div] at hr he
  rw [← he] at hr
  have hm :=
    mul_le_mul_of_nonneg_left hp
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)
        (Real.rpow_nonneg (by norm_num only : (0 : ℝ) ≤ 62500) (-21 / 20 : ℝ)))
  have hg := Analysis.gamma_euler_prefix_lower_growth (by norm_num only : (50000 : ℕ) ≤ 62500) hC
  norm_num only [Nat.cast_ofNat, neg_div] at hg hm hr
  nlinarith only [hg, hm, hr]

/-- Input: RH and b>=62500. Claim: its Euler prefix is at least 14309/2500.
Add the analytic short-block gain to the existing initial bound and use
positive-prefix monotonicity. Role: strengthen credits at admissible small cutoffs. -/
theorem gamma_prefix62500_lower_asymmetric (hRH : RiemannHypothesis) {b : ℝ} (hb : 62500 ≤ b) :
    (14309 / 2500 : ℝ) ≤ ∑ j ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight j := by
  have hs := gamma_prefix50000_lower_asymmetric hRH (le_refl (50000 : ℝ))
  have hsN :
    (28493 / 5000 : ℝ) ≤
      ∑ j ∈ Finset.Ioc 0 (50000 : ℕ), Analysis.gammaResolventMangoldtWeight j := by
    simpa only [Nat.floor_ofNat] using hs
  have hg := gamma_euler_prefix_50000_62500_gain hRH hsN
  have hc :
    ((14309 / 2500 : ℚ) : ℝ) ≤
      ∑ j ∈ Finset.Ioc 0 (62500 : ℕ), Analysis.gammaResolventMangoldtWeight j := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    linarith only [hg]
  have hf := Nat.floor_mono hb
  norm_num only [Nat.floor_ofNat] at hf
  have h := Analysis.gamma_euler_prefix_lower_mono hf hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: RH, a>=100000, an initial Euler credit C and r<=(2a)^(-1/20).
Claim: doubling adds at least (39/200)r to the credit. Retain the positive
Euler endpoint weight and the psi block mass. Role: remove a fixed upper
cutoff from analytic prefix growth. -/
theorem gamma_euler_prefix_doubling_gain_of_power_lower (hRH : RiemannHypothesis) {a : ℕ}
    (ha : 100000 ≤ a) {r C : ℝ} (hr : r ≤ ((2 : ℝ) * a) ^ (-1 / 20 : ℝ))
    (hC : C ≤ ∑ k ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight k) :
    C + (39 / 200 : ℝ) * r ≤
      ∑ k ∈ Finset.Ioc 0 (2 * a), Analysis.gammaResolventMangoldtWeight k := by
  have haR : (100000 : ℝ) ≤ a := by exact_mod_cast ha
  have hap := psi_bounds_of_hundred_thousand_le hRH haR
  have hbp :=
    psi_bounds_of_hundred_thousand_le hRH (show (100000 : ℝ) ≤ (2 : ℝ) * a by linarith only [haR])
  have hd : (39 / 100 : ℝ) * ((2 : ℝ) * a) ≤ Chebyshev.psi ((2 : ℝ) * a) - Chebyshev.psi a := by
    linarith only [hap.2, hbp.1]
  have he : (((2 : ℝ) * a) ^ (-21 / 20 : ℝ)) * ((2 : ℝ) * a) = ((2 : ℝ) * a) ^ (-1 / 20 : ℝ) := by
    calc
      _ = ((2 : ℝ) * a) ^ (-21 / 20 : ℝ) * ((2 : ℝ) * a) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ((2 : ℝ) * a) ^ ((-21 / 20 : ℝ) + 1) := (Real.rpow_add (by linarith only [haR]) _ _).symm
      _ = _ := by norm_num only
  have hg :=
    Analysis.gamma_euler_prefix_lower_growth (show a ≤ 2 * a by nlinarith only [Nat.zero_le a]) hC
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, neg_div] at hg
  have hm :=
    mul_le_mul_of_nonneg_left hd
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)
        (Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) * a by linarith only [haR]) (-21 / 20 : ℝ)))
  have hex :
    (1 / 2 : ℝ) * ((2 : ℝ) * a) ^ (-21 / 20 : ℝ) * ((39 / 100 : ℝ) * ((2 : ℝ) * a)) =
      (39 / 200 : ℝ) * ((2 : ℝ) * a) ^ (-1 / 20 : ℝ) := by
    rw [← he]
    ring
  rw [hex] at hm
  norm_num only at hg hm
  linarith only [hg, hm, hr]

/-- Input: RH, a>=100000, an initial Euler credit C, and r<=B^(-1/20).
Claim: k doubling blocks ending at most at B add (39/200)rk to the credit.
Induct over blocks and use antitonicity of the endpoint power. Role: keep
the final scale dependence instead of rounding it at a fixed cutoff. -/
theorem gamma_euler_prefix_lower_doublings_of_power_lower (hRH : RiemannHypothesis) {a B : ℕ}
    (ha : 100000 ≤ a) {r C : ℝ} (hr : r ≤ (B : ℝ) ^ (-1 / 20 : ℝ))
    (hC : C ≤ ∑ n ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight n) (k : ℕ) :
    a * 2 ^ k ≤ B →
      C + (39 / 200 : ℝ) * r * k ≤
        ∑ n ∈ Finset.Ioc 0 (a * 2 ^ k), Analysis.gammaResolventMangoldtWeight n := by
  induction k with
  | zero =>
    intro _
    simpa only [pow_zero, mul_one, Nat.cast_zero, mul_zero, add_zero] using hC
  | succ k ih =>
    intro htop
    have heq : a * 2 ^ (k + 1) = 2 * (a * 2 ^ k) := by
      rw [pow_succ]; ring
    have hsmall : a * 2 ^ k ≤ a * 2 ^ (k + 1) := by
      rw [heq]
      nlinarith only [Nat.zero_le (a * 2 ^ k)]
    have hpow : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num only : 0 < (2 : ℕ)) _
    have hlow : a ≤ a * 2 ^ k := by nlinarith only [hpow, Nat.zero_le a]
    have htopR : (2 : ℝ) * (a * 2 ^ k : ℕ) ≤ B := by
      exact_mod_cast
        (show 2 * (a * 2 ^ k) ≤ B by
          rw [← heq]; exact htop)
    have hnode : (0 : ℝ) < (2 : ℝ) * (a * 2 ^ k : ℕ) := by
      have hlowR : (100000 : ℝ) ≤ (a * 2 ^ k : ℕ) := by exact_mod_cast ha.trans hlow
      linarith only [hlowR]
    have hp := Real.rpow_le_rpow_of_nonpos hnode htopR (by norm_num only : (-1 / 20 : ℝ) ≤ 0)
    have hg :=
      gamma_euler_prefix_doubling_gain_of_power_lower hRH (ha.trans hlow) (hr.trans hp)
        (ih (hsmall.trans htop))
    rw [heq]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith only [hg]

/-- Input: RH and b>=102400000. Claim: its Euler prefix is at least
64591/10000. Apply ten symbolic doubling blocks with endpoint power at least
39/100, then use prefix monotonicity. Role: a stronger analytic witness credit. -/
theorem gamma_prefix102400000_lower_halfline (hRH : RiemannHypothesis) {b : ℝ}
    (hb : 102400000 ≤ b) :
    (64591 / 10000 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight n := by
  have hp :=
    Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 102400000)
      (by norm_num only : (102400000 : ℝ) ≤ (100 / 39 : ℝ) ^ (20 : ℕ))
      (by norm_num only : (-1 / 20 : ℝ) ≤ 0)
  rw [← Real.rpow_natCast (100 / 39 : ℝ) 20, ←
    Real.rpow_mul (by norm_num only : (0 : ℝ) ≤ 100 / 39)] at hp
  norm_num only [show (20 : ℝ) * (-1 / 20) = -1 by norm_num only, Real.rpow_neg_one] at hp
  have hs := gamma_prefix50000_lower_asymmetric hRH (by norm_num only : (50000 : ℝ) ≤ 100000)
  have hsN :
    (28493 / 5000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 (100000 : ℕ), Analysis.gammaResolventMangoldtWeight n := by
    simpa only [Nat.floor_ofNat] using hs
  have hg :=
    gamma_euler_prefix_lower_doublings_of_power_lower hRH (by norm_num only : (100000 : ℕ) ≤ 100000)
      (show (39 / 100 : ℝ) ≤ (102400000 : ℝ) ^ (-1 / 20 : ℝ) by simpa only [neg_div] using hp) hsN
      10 (by norm_num only : (100000 : ℕ) * 2 ^ 10 ≤ 102400000)
  change
    (28493 / 5000 : ℝ) + (39 / 200 : ℝ) * (39 / 100) * 10 ≤
      ∑ n ∈ Finset.Ioc 0 (102400000 : ℕ), Analysis.gammaResolventMangoldtWeight n at hg
  have hc :
    ((64591 / 10000 : ℚ) : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 (102400000 : ℕ), Analysis.gammaResolventMangoldtWeight n := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    linarith only [hg]
  have hf := Nat.floor_mono hb
  norm_num only [Nat.floor_ofNat] at hf
  have h := Analysis.gamma_euler_prefix_lower_mono hf hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

end PseudoPrime.LLS
