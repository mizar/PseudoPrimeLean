/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiberEnergyThreshold
public import PseudoPrime.NumberTheory.Heilbronn.ThirteenthEnergyBridge
public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiberPowerCount
public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiberCoefficientBudget
public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiberLogThreshold
public import PseudoPrime.NumberTheory.Heilbronn.FreeFiberBandParameters
public import PseudoPrime.NumberTheory.Heilbronn.PointwiseRationalSmoothSupply
public import PseudoPrime.NumberTheory.Heilbronn.FiniteFiberRationalScales
public import PseudoPrime.Analysis.ExplicitSmoothLogBudgets
public import PseudoPrime.Analysis.ThirteenthCountingBudget

/-! # Explicit finite-fiber interval count at rational scale 125/68 -/

public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The binary power 2^k lies below P(u) whenever k<u. Compare exponents
using u<2^u while the threshold parameter is still symbolic. This avoids
evaluating a closed double-exponential threshold during specialization. -/
theorem two_pow_lt_explicit_finite_fiber_threshold {k u : ℕ} (h : k < u) :
    2 ^ k < explicitFiniteFiberPrimeThreshold u := by
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (h.trans (Nat.lt_two_pow_self (n := u)))

/-- If 6a<u, the rational cutoff coefficient 32^a 2^a lies below P(u).
Collect its binary powers before specializing a,u. This discharges the
extra Fourier-height condition for the fixed scale a=68,u=1388714689827. -/
theorem cutoff_coefficient_lt_explicit_finite_fiber_threshold {a u : ℕ} (h : 6 * a < u) :
    32 ^ a * 2 ^ a < explicitFiniteFiberPrimeThreshold u := by
  have he : (32 : ℕ) ^ a * 2 ^ a = 2 ^ (6 * a) := by
    rw [show (32 : ℕ) = 2 ^ 5 by decide, ← pow_mul, ← pow_add]
    congr 1
    ring
  exact he.trans_lt (two_pow_lt_explicit_finite_fiber_threshold h)

/-- For a base p>1 and d<a, an integer height with H^a≤p^d is below p.
Compare natural powers under the contrary assumption. Keeping the exponents
generic avoids unfolding large fixed powers in cutoff specialization. -/
theorem height_lt_base_of_power_bound {p H a d : ℕ} (hp : 1 < p) (hd : d < a)
    (hheight : H ^ a ≤ p ^ d) : H < p := by
  by_contra hn
  have hh := (Nat.pow_le_pow_left (Nat.le_of_not_gt hn) a).trans hheight
  exact (not_le_of_gt (Nat.pow_lt_pow_right hp hd)) hh

/-- At the prescribed threshold, the log-square energy estimate supplies the
explicit finite-fiber budget. The coefficient uses exponent 1 and the
logarithmic factor uses exponent 2, leaving the strict margin 3. -/
theorem fixed_log_square_finite_fiber_energy_budget {p H k : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold (1388714689827) ≤ p) (hHp : H < p)
    (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (hcut : p ^ 125 ≤ k ^ 68)
    (hheight : H ^ 68 ≤ p ^ (2 * 68 - 125)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hA : (2 ^ 176 : ℕ) ^ 68 ≤ 2 ^ (176 * 68) := le_of_eq (pow_mul 2 176 68).symm
  have hcoeffNat :
    (2 ^ 176 : ℕ) ^ 68 * finiteFiberCountCoefficient 136 68 ^ (13 * 68) <
      explicitFiniteFiberPrimeThreshold (1388714689827) :=
    mul_power_lt_explicit_finite_fiber_threshold (B := 1388714676973 + 1) (k := 176 * 68)
      finiteFiberCountCoefficient_136_68_lt_double_exp.le hA (by norm_num only)
  have hPgt := one_lt_explicit_finite_fiber_threshold (1388714689827)
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (hPgt.le.trans hlarge)
  have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hPcast : (explicitFiniteFiberPrimeThreshold (1388714689827) : ℝ) ≤ p := by
    exact_mod_cast hlarge
  have hcoeffCast :
    (2 ^ 176 : ℝ) ^ 68 * (finiteFiberCountCoefficient 136 68 : ℝ) ^ (13 * 68) <
      (explicitFiniteFiberPrimeThreshold (1388714689827) : ℝ) := by
    exact_mod_cast hcoeffNat
  have hcoeff :
    (2 ^ 176 : ℝ) ^ 68 * (finiteFiberCountCoefficient 136 68 : ℝ) ^ (13 * 68) < (p : ℝ) := by
    exact hcoeffCast.trans_le hPcast
  have hz := three_hundred_eighty_seven_billion_le_double_log_of_explicit_fiber_threshold hlarge
  have hLp := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hzsmall : 20000000000 ≤ Real.log (Real.log p) := le_trans (by norm_num only) hz
  obtain ⟨hL, _⟩ :=
    Analysis.fixed_smooth_log_size_bounds hLp
      (le_trans (by norm_num only : (2000000000 : ℝ) ≤ 20000000000) hzsmall)
  have hlogLower : (10 : ℝ) ^ 12 ≤ Real.log p := by
    exact (by norm_num only : (10 : ℝ) ^ 12 ≤ 10 ^ 20).trans hL
  have hfactor : 1 + Real.log p ≤ (p : ℝ) ^ (1 / 2000 : ℝ) := by
    have hsmall := Analysis.thirty_two_mul_le_exp_div_two_thousand hlogLower
    have hone : 1 + Real.log p ≤ 32 * Real.log p := by nlinarith only [hlogLower]
    rw [Real.rpow_def_of_pos hpPos]
    calc
      1 + Real.log p ≤ 32 * Real.log p := hone
      _ ≤ Real.exp (Real.log p / 2000) := hsmall
      _ = Real.exp (Real.log p * (1 / 2000 : ℝ)) := by
        congr 1; ring
  have hlogPow : (1 + Real.log p) ^ (2 * 68) ≤ (p : ℝ) ^ 2 := by
    have hraised := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log p) hfactor (2 * 68)
    have hconvert : ((p : ℝ) ^ (1 / 2000 : ℝ)) ^ (2 * 68) = (p : ℝ) ^ (17 / 250 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      congr 1
      norm_num only
    have hexp : (17 / 250 : ℝ) ≤ 2 := by norm_num only
    have hpower : Real.rpow (p : ℝ) (17 / 250 : ℝ) ≤ Real.rpow (p : ℝ) (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpR hexp
    exact hraised.trans_eq hconvert |>.trans (hpower.trans_eq (Real.rpow_natCast (p : ℝ) 2))
  have hmargin :
    (2 ^ 176 : ℝ) ^ 68 * (finiteFiberCountCoefficient 136 68 : ℝ) ^ (13 * 68) *
        (1 + Real.log p) ^ (2 * 68) <
      (p : ℝ) ^ 3 := by
    calc
      _ ≤
          ((2 ^ 176 : ℝ) ^ 68 * (finiteFiberCountCoefficient 136 68 : ℝ) ^ (13 * 68)) *
            (p : ℝ) ^ 2 :=
        by gcongr
      _ < (p : ℝ) * (p : ℝ) ^ 2 := mul_lt_mul_of_pos_right hcoeff (by positivity)
      _ = (p : ℝ) ^ 3 := by
        calc
          _ = (p : ℝ) ^ 1 * (p : ℝ) ^ 2 := by rw [pow_one]
          _ = _ := by rw [← pow_add]
  have henergy :=
    thirteenth_energy_power_lt_of_log_square_slack hodd 68 (finiteFiberCountCoefficient 136 68) 3
      hmargin
  have hcount :=
    boundedCongruenceCount_power_le_explicit_finite_fiber_of_exponent_bound (a := 68) (c := 136)
      (g := 2) (by decide) (by decide) (by norm_num only) (by norm_num only) p H hodd hHp htop
  have hslack : 71 * 68 + 13 * 2 < 39 * 125 := by decide
  exact
    Analysis.thirteenth_counting_budget_of_energy_exponent_le (Fact.out : p.Prime).pos (by decide)
      (by decide) hslack hcut hheight hcount henergy (by decide)

/-- Inputs: a prime `p`, a height `H`, independent positive exponents `a` and
`h`, count precision `c`, cutoff exponent `b`, and integer count and energy
bounds. The count estimate loses `1/h`, while the finite-fiber energy uses
the separate power `a`. Claim: these data imply
`p * heilbronnEnergy p * boundedCongruenceCount p H < k^2` whenever the
available slack `39b-(71a+13g)` covers the logarithmic energy remainder.
Proof: apply the separated count-power estimate, then the thirteenth-energy
budget. Role: connects independent count and energy exponents to the cutoff
inequality. -/
theorem separate_count_finite_fiber_energy_budget {p H k a h c b g r : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hHp : H < p) (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (ha : 0 < a) (hh : 0 < h)
    (hc : 0 < c) (hprec : 1 / (c : ℝ) ≤ (1 / (h : ℝ)) / 2)
    (hratio : 1 / 84 + 1 / (h : ℝ) ≤ (g : ℝ) / a) (hb : b ≤ 2 * a)
    (hslack : 71 * a + 13 * g < 39 * b) (hcut : p ^ b ≤ k ^ a) (hheight : H ^ a ≤ p ^ (2 * a - b))
    (henergy :
      (2 ^ 176 : ℝ) ^ a * (freeFiniteFiberCountCoefficient c h : ℝ) ^ (13 * a) *
          (1 + Real.log p) ^ (2 * a) <
        (p : ℝ) ^ r)
    (hr : r ≤ 39 * b - (71 * a + 13 * g)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hcount :=
    boundedCongruenceCount_power_le_explicit_free_finite_fiber ha hh hc hprec hratio p H hodd hHp
      htop
  have hbudget :=
    thirteenth_energy_power_lt_of_log_square_slack hodd a (freeFiniteFiberCountCoefficient c h) r
      henergy
  exact
    Analysis.thirteenth_counting_budget_of_energy_exponent_le (Fact.out : p.Prime).pos ha hb hslack
      hcut hheight hcount hbudget hr

/-- Under the same independent count and energy exponents, a squared
coefficient bound and a matching squared logarithmic bound suffice when the
integer slack is only one. The two factors are each bounded by `p` after
squaring, so their product fits the strict unit budget. Role: exposes the
small-slack route for new rational finite-fiber scales. -/
theorem separate_count_finite_fiber_energy_budget_square {p H k a h c b g : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hHp : H < p) (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (ha : 0 < a) (hh : 0 < h)
    (hc : 0 < c) (hprec : 1 / (c : ℝ) ≤ (1 / (h : ℝ)) / 2)
    (hratio : 1 / 84 + 1 / (h : ℝ) ≤ (g : ℝ) / a) (hb : b ≤ 2 * a)
    (hslack : 71 * a + 13 * g < 39 * b) (hcut : p ^ b ≤ k ^ a) (hheight : H ^ a ≤ p ^ (2 * a - b))
    (hcoeff : (((2 ^ 176 : ℝ) ^ a) * (freeFiniteFiberCountCoefficient c h : ℝ) ^ (13 * a)) ^ 2 < p)
    (hlog : (1 + Real.log p) ^ (4 * a) ≤ p) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hcount :=
    boundedCongruenceCount_power_le_explicit_free_finite_fiber ha hh hc hprec hratio p H hodd hHp
      htop
  have hbudget :=
    thirteenth_energy_power_lt_of_square_slack hodd a (freeFiniteFiberCountCoefficient c h) hcoeff
      hlog
  have hr : 1 ≤ 39 * b - (71 * a + 13 * g) := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hslack)
  exact
    Analysis.thirteenth_counting_budget_of_energy_exponent_le (Fact.out : p.Prime).pos ha hb hslack
      hcut hheight hcount hbudget hr

/-- Every odd prime p≥P(1388714689827) has a cutoff at scale 125/68 satisfying
the strict Heilbronn energy budget. Use the log-square energy estimate and
absorb its logarithmic factor before applying the explicit finite-fiber count.
The starting threshold is the prescribed expression, not an existential value. -/
theorem exists_fixed_finite_fiber_rational_energy_cutoff {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold (1388714689827) ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 125 ≤ k ^ 68 ∧
        k ^ 68 ≤ 2 ^ 68 * p ^ 125 ∧
        p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ 125 < (p ^ 2) ^ 68 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 (by decide)
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 125) hp0) (by decide : 0 < 68) with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget (d := 2) (a := 68) (b := 125) hp0 (by decide) hlo
    have hheightExplicit : (p ^ 2 / k) ^ 68 ≤ p ^ 11 := by
      have hheight' := hheight
      rw [show (2 * 68 - 125 : ℕ) = 11 by decide] at hheight'
      exact hheight'
    have hHp := height_lt_base_of_power_bound hp1 (by decide : 11 < 68) hheightExplicit
    have htop :=
      height_le_real_power_of_power (a := 68) (d := 11) (by decide) hp1.le
        (by norm_num only : (11 : ℝ) / 68 ≤ 5 / 28) hheightExplicit
    exact fixed_log_square_finite_fiber_energy_budget hodd hlarge hHp htop hlo hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Every odd prime p≥P(1388714689827) has a cutoff p^125≤k^68≤2^68 p^125
with p J_p(k)<256k. Pass to the smaller Fourier height using count
monotonicity and discharge 32k<p² from the fixed threshold. This is the
explicit interval input to the remaining smooth-number extraction. -/
theorem exists_fixed_finite_fiber_interval_bound {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold (1388714689827) ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k < p ^ 2 ∧
        p ^ 125 ≤ k ^ 68 ∧ k ^ 68 ≤ 2 ^ 68 * p ^ 125 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ := exists_fixed_finite_fiber_rational_energy_cutoff hodd hlarge
  have hc : (32 : ℕ) ^ 68 * 2 ^ 68 < p :=
    (cutoff_coefficient_lt_explicit_finite_fiber_threshold (a := 68) (u := 1388714689827)
          (by norm_num only)).trans_le
      hlarge
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt (by decide : 0 < 68)
      (by decide : 125 < 2 * 68) hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

/-- At the separate scale 74/40, the logarithmic-square energy estimate
supplies the explicit finite-fiber budget above P(283000007562). The
coefficient and logarithmic factor leave energy exponent three. -/
theorem fixed_log_square_finite_fiber_energy_budget_40_74 {p H k : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 283000007562 ≤ p) (hHp : H < p)
    (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (hcut : p ^ 74 ≤ k ^ 40)
    (hheight : H ^ 40 ≤ p ^ (2 * 40 - 74)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hA : (2 ^ 176 : ℕ) ^ 40 ≤ 2 ^ (176 * 40) := le_of_eq (pow_mul 2 176 40).symm
  have hcoeffNat :
    (2 ^ 176 : ℕ) ^ 40 * finiteFiberCountCoefficient 80 40 ^ (13 * 40) <
      explicitFiniteFiberPrimeThreshold 283000007562 :=
    mul_power_lt_explicit_finite_fiber_threshold (B := 283000000000 + 1) (k := 176 * 40)
      finiteFiberCountCoefficient_80_40_lt_double_exp.le hA (by norm_num only)
  have hPgt := one_lt_explicit_finite_fiber_threshold 283000007562
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (hPgt.le.trans hlarge)
  have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hPcast : (explicitFiniteFiberPrimeThreshold 283000007562 : ℝ) ≤ p := by exact_mod_cast hlarge
  have hcoeffCast :
    (2 ^ 176 : ℝ) ^ 40 * (finiteFiberCountCoefficient 80 40 : ℝ) ^ (13 * 40) <
      (explicitFiniteFiberPrimeThreshold 283000007562 : ℝ) := by
    exact_mod_cast hcoeffNat
  have hcoeff :
    (2 ^ 176 : ℝ) ^ 40 * (finiteFiberCountCoefficient 80 40 : ℝ) ^ (13 * 40) < (p : ℝ) :=
    hcoeffCast.trans_le hPcast
  have hz := one_hundred_billion_le_double_log_of_explicit_fiber_threshold hlarge
  have hLp := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hzsmall : 20000000000 ≤ Real.log (Real.log p) := le_trans (by norm_num only) hz
  obtain ⟨hL, _⟩ :=
    Analysis.fixed_smooth_log_size_bounds hLp
      (le_trans (by norm_num only : (2000000000 : ℝ) ≤ 20000000000) hzsmall)
  have hlogLower : (10 : ℝ) ^ 12 ≤ Real.log p := by
    exact (by norm_num only : (10 : ℝ) ^ 12 ≤ 10 ^ 20).trans hL
  have hfactor : 1 + Real.log p ≤ (p : ℝ) ^ (1 / 2000 : ℝ) := by
    have hsmall := Analysis.thirty_two_mul_le_exp_div_two_thousand hlogLower
    have hone : 1 + Real.log p ≤ 32 * Real.log p := by nlinarith only [hlogLower]
    rw [Real.rpow_def_of_pos hpPos]
    calc
      1 + Real.log p ≤ 32 * Real.log p := hone
      _ ≤ Real.exp (Real.log p / 2000) := hsmall
      _ = Real.exp (Real.log p * (1 / 2000 : ℝ)) := by
        congr 1; ring
  have hlogPow : (1 + Real.log p) ^ (2 * 40) ≤ (p : ℝ) ^ 2 := by
    have hraised := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log p) hfactor (2 * 40)
    have hconvert : ((p : ℝ) ^ (1 / 2000 : ℝ)) ^ (2 * 40) = (p : ℝ) ^ (1 / 25 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      congr 1
      norm_num only
    have hexp : (1 / 25 : ℝ) ≤ 2 := by norm_num only
    have hpower : Real.rpow (p : ℝ) (1 / 25 : ℝ) ≤ Real.rpow (p : ℝ) (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpR hexp
    exact hraised.trans_eq hconvert |>.trans (hpower.trans_eq (Real.rpow_natCast (p : ℝ) 2))
  have hmargin :
    (2 ^ 176 : ℝ) ^ 40 * (finiteFiberCountCoefficient 80 40 : ℝ) ^ (13 * 40) *
        (1 + Real.log p) ^ (2 * 40) <
      (p : ℝ) ^ 3 := by
    calc
      _ ≤
          ((2 ^ 176 : ℝ) ^ 40 * (finiteFiberCountCoefficient 80 40 : ℝ) ^ (13 * 40)) *
            (p : ℝ) ^ 2 :=
        by gcongr
      _ < (p : ℝ) * (p : ℝ) ^ 2 := mul_lt_mul_of_pos_right hcoeff (by positivity)
      _ = (p : ℝ) ^ 3 := by
        calc
          _ = (p : ℝ) ^ 1 * (p : ℝ) ^ 2 := by rw [pow_one]
          _ = _ := by rw [← pow_add]
  have henergy :=
    thirteenth_energy_power_lt_of_log_square_slack hodd 40 (finiteFiberCountCoefficient 80 40) 3
      hmargin
  have hcount :=
    boundedCongruenceCount_power_le_explicit_finite_fiber_of_exponent_bound (a := 40) (c := 80)
      (g := 2) (by decide) (by decide) (by norm_num only) (by norm_num only) p H hodd hHp htop
  have hslack : 71 * 40 + 13 * 2 < 39 * 74 := by decide
  exact
    Analysis.thirteenth_counting_budget_of_energy_exponent_le (Fact.out : p.Prime).pos (by decide)
      (by decide) hslack hcut hheight hcount henergy (by decide)

/-- At the separate scale 70/38, the logarithmic-square energy estimate
supplies the explicit finite-fiber budget above P(242591045876). The
coefficient and logarithmic factor leave energy exponent three. -/
theorem fixed_log_square_finite_fiber_energy_budget_38_70 {p H k : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 242591045876 ≤ p) (hHp : H < p)
    (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (hcut : p ^ 70 ≤ k ^ 38)
    (hheight : H ^ 38 ≤ p ^ (2 * 38 - 70)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hA : (2 ^ 176 : ℕ) ^ 38 ≤ 2 ^ (176 * 38) := le_of_eq (pow_mul 2 176 38).symm
  have hcoeffNat :
    (2 ^ 176 : ℕ) ^ 38 * finiteFiberCountCoefficient 76 38 ^ (13 * 38) <
      explicitFiniteFiberPrimeThreshold 242591045876 :=
    mul_power_lt_explicit_finite_fiber_threshold (B := 242591038692 + 1) (k := 176 * 38)
      finiteFiberCountCoefficient_76_38_lt_double_exp.le hA (by norm_num only)
  have hPgt := one_lt_explicit_finite_fiber_threshold 242591045876
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (hPgt.le.trans hlarge)
  have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hPcast : (explicitFiniteFiberPrimeThreshold 242591045876 : ℝ) ≤ p := by exact_mod_cast hlarge
  have hcoeffCast :
    (2 ^ 176 : ℝ) ^ 38 * (finiteFiberCountCoefficient 76 38 : ℝ) ^ (13 * 38) <
      (explicitFiniteFiberPrimeThreshold 242591045876 : ℝ) := by
    exact_mod_cast hcoeffNat
  have hcoeff :
    (2 ^ 176 : ℝ) ^ 38 * (finiteFiberCountCoefficient 76 38 : ℝ) ^ (13 * 38) < (p : ℝ) :=
    hcoeffCast.trans_le hPcast
  have hz := one_hundred_billion_le_double_log_of_explicit_fiber_threshold_38_70 hlarge
  have hLp := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hzsmall : 20000000000 ≤ Real.log (Real.log p) := le_trans (by norm_num only) hz
  obtain ⟨hL, _⟩ :=
    Analysis.fixed_smooth_log_size_bounds hLp
      (le_trans (by norm_num only : (2000000000 : ℝ) ≤ 20000000000) hzsmall)
  have hlogLower : (10 : ℝ) ^ 12 ≤ Real.log p := by
    exact (by norm_num only : (10 : ℝ) ^ 12 ≤ 10 ^ 20).trans hL
  have hfactor : 1 + Real.log p ≤ (p : ℝ) ^ (1 / 2000 : ℝ) := by
    have hsmall := Analysis.thirty_two_mul_le_exp_div_two_thousand hlogLower
    have hone : 1 + Real.log p ≤ 32 * Real.log p := by nlinarith only [hlogLower]
    rw [Real.rpow_def_of_pos hpPos]
    calc
      1 + Real.log p ≤ 32 * Real.log p := hone
      _ ≤ Real.exp (Real.log p / 2000) := hsmall
      _ = Real.exp (Real.log p * (1 / 2000 : ℝ)) := by
        congr 1; ring
  have hlogPow : (1 + Real.log p) ^ (2 * 38) ≤ (p : ℝ) ^ 2 := by
    have hraised := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log p) hfactor (2 * 38)
    have hconvert : ((p : ℝ) ^ (1 / 2000 : ℝ)) ^ (2 * 38) = (p : ℝ) ^ (19 / 500 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      congr 1
      norm_num only
    have hexp : (19 / 500 : ℝ) ≤ 2 := by norm_num only
    have hpower : Real.rpow (p : ℝ) (19 / 500 : ℝ) ≤ Real.rpow (p : ℝ) (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpR hexp
    exact hraised.trans_eq hconvert |>.trans (hpower.trans_eq (Real.rpow_natCast (p : ℝ) 2))
  have hmargin :
    (2 ^ 176 : ℝ) ^ 38 * (finiteFiberCountCoefficient 76 38 : ℝ) ^ (13 * 38) *
        (1 + Real.log p) ^ (2 * 38) <
      (p : ℝ) ^ 3 := by
    calc
      _ ≤
          ((2 ^ 176 : ℝ) ^ 38 * (finiteFiberCountCoefficient 76 38 : ℝ) ^ (13 * 38)) *
            (p : ℝ) ^ 2 :=
        by gcongr
      _ < (p : ℝ) * (p : ℝ) ^ 2 := mul_lt_mul_of_pos_right hcoeff (by positivity)
      _ = (p : ℝ) ^ 3 := by
        calc
          _ = (p : ℝ) ^ 1 * (p : ℝ) ^ 2 := by rw [pow_one]
          _ = _ := by rw [← pow_add]
  have henergy :=
    thirteenth_energy_power_lt_of_log_square_slack hodd 38 (finiteFiberCountCoefficient 76 38) 3
      hmargin
  have hcount :=
    boundedCongruenceCount_power_le_explicit_finite_fiber_of_exponent_bound (a := 38) (c := 76)
      (g := 2) (by decide) (by decide) (by norm_num only) (by norm_num only) p H hodd hHp htop
  have hslack : 71 * 38 + 13 * 2 < 39 * 70 := by decide
  exact
    Analysis.thirteenth_counting_budget_of_energy_exponent_le (Fact.out : p.Prime).pos (by decide)
      (by decide) hslack hcut hheight hcount henergy (by decide)

/-- Every odd prime p≥P(283000007562) has a 74/40 cutoff satisfying the
strict Heilbronn energy budget. Obtain its height and real-power bounds from
the rational cutoff inequalities. -/
theorem exists_fixed_finite_fiber_rational_energy_cutoff_40_74 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 283000007562 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 74 ≤ k ^ 40 ∧
        k ^ 40 ≤ 2 ^ 40 * p ^ 74 ∧
        p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ 74 < (p ^ 2) ^ 40 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 (by decide)
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 74) hp0) (by decide : 0 < 40) with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget (d := 2) (a := 40) (b := 74) hp0 (by decide) hlo
    have hheightExplicit : (p ^ 2 / k) ^ 40 ≤ p ^ 6 := by
      have hheight' := hheight
      rw [show (2 * 40 - 74 : ℕ) = 6 by decide] at hheight'
      exact hheight'
    have hHp := height_lt_base_of_power_bound hp1 (by decide : 6 < 40) hheightExplicit
    have htop :=
      height_le_real_power_of_power (a := 40) (d := 6) (by decide) hp1.le
        (by norm_num only : (6 : ℝ) / 40 ≤ 5 / 28) hheightExplicit
    exact fixed_log_square_finite_fiber_energy_budget_40_74 hodd hlarge hHp htop hlo hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Every odd prime p≥P(283000007562) has a cutoff p^74≤k^40≤2^40 p^74
with p J_p(k)<256k. Transfer the energy bound to the shorter Fourier height
by monotonicity of the finite-fiber count. -/
theorem exists_fixed_finite_fiber_interval_bound_40_74 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 283000007562 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k < p ^ 2 ∧
        p ^ 74 ≤ k ^ 40 ∧ k ^ 40 ≤ 2 ^ 40 * p ^ 74 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ :=
    exists_fixed_finite_fiber_rational_energy_cutoff_40_74 hodd hlarge
  have hc : (32 : ℕ) ^ 40 * 2 ^ 40 < p :=
    (cutoff_coefficient_lt_explicit_finite_fiber_threshold (a := 40) (u := 283000007562)
          (by norm_num only)).trans_le
      hlarge
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt (by decide : 0 < 40)
      (by decide : 74 < 2 * 40) hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

/-- Every odd prime p≥P(242591045876) has a 70/38 cutoff satisfying the
strict Heilbronn energy budget. Obtain its height and real-power bounds from
the rational cutoff inequalities. -/
theorem exists_fixed_finite_fiber_rational_energy_cutoff_38_70 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 242591045876 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 70 ≤ k ^ 38 ∧
        k ^ 38 ≤ 2 ^ 38 * p ^ 70 ∧
        p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ 70 < (p ^ 2) ^ 38 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 (by decide)
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 70) hp0) (by decide : 0 < 38) with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget (d := 2) (a := 38) (b := 70) hp0 (by decide) hlo
    have hheightExplicit : (p ^ 2 / k) ^ 38 ≤ p ^ 6 := by
      have hheight' := hheight
      rw [show (2 * 38 - 70 : ℕ) = 6 by decide] at hheight'
      exact hheight'
    have hHp := height_lt_base_of_power_bound hp1 (by decide : 6 < 38) hheightExplicit
    have htop :=
      height_le_real_power_of_power (a := 38) (d := 6) (by decide) hp1.le
        (by norm_num only : (6 : ℝ) / 38 ≤ 5 / 28) hheightExplicit
    exact fixed_log_square_finite_fiber_energy_budget_38_70 hodd hlarge hHp htop hlo hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Every odd prime p≥P(242591045876) has a cutoff p^70≤k^38≤2^38 p^70
with p J_p(k)<256k. Transfer the energy bound to the shorter Fourier height
by monotonicity of the finite-fiber count. -/
theorem exists_fixed_finite_fiber_interval_bound_38_70 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 242591045876 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k < p ^ 2 ∧
        p ^ 70 ≤ k ^ 38 ∧ k ^ 38 ≤ 2 ^ 38 * p ^ 70 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ :=
    exists_fixed_finite_fiber_rational_energy_cutoff_38_70 hodd hlarge
  have hc : (32 : ℕ) ^ 38 * 2 ^ 38 < p :=
    (cutoff_coefficient_lt_explicit_finite_fiber_threshold (a := 38) (u := 242591045876)
          (by norm_num only)).trans_le
      hlarge
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt (by decide : 0 < 38)
      (by decide : 70 < 2 * 38) hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

/-- At scale 59/32, the logarithmic-square energy estimate gives the
finite-fiber budget above P(145000006050). The coefficient and log factor
leave energy exponent three. -/
theorem fixed_log_square_finite_fiber_energy_budget_32_59 {p H k : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 145000006050 ≤ p) (hHp : H < p)
    (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (hcut : p ^ 59 ≤ k ^ 32)
    (hheight : H ^ 32 ≤ p ^ (2 * 32 - 59)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hA : (2 ^ 176 : ℕ) ^ 32 ≤ 2 ^ (176 * 32) := le_of_eq (pow_mul 2 176 32).symm
  have hcoeffNat :
    (2 ^ 176 : ℕ) ^ 32 * finiteFiberCountCoefficient 64 32 ^ (13 * 32) <
      explicitFiniteFiberPrimeThreshold 145000006050 :=
    mul_power_lt_explicit_finite_fiber_threshold (B := 145000000000 + 1) (k := 176 * 32)
      finiteFiberCountCoefficient_64_32_lt_double_exp.le hA (by norm_num only)
  have hPgt := one_lt_explicit_finite_fiber_threshold 145000006050
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (hPgt.le.trans hlarge)
  have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hPcast : (explicitFiniteFiberPrimeThreshold 145000006050 : ℝ) ≤ p := by exact_mod_cast hlarge
  have hcoeffCast :
    (2 ^ 176 : ℝ) ^ 32 * (finiteFiberCountCoefficient 64 32 : ℝ) ^ (13 * 32) <
      (explicitFiniteFiberPrimeThreshold 145000006050 : ℝ) := by
    exact_mod_cast hcoeffNat
  have hcoeff :
    (2 ^ 176 : ℝ) ^ 32 * (finiteFiberCountCoefficient 64 32 : ℝ) ^ (13 * 32) < (p : ℝ) :=
    hcoeffCast.trans_le hPcast
  have hz := twenty_billion_le_double_log_of_explicit_fiber_threshold_32_59 hlarge
  have hLp := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hzsmall : 20000000000 ≤ Real.log (Real.log p) := le_trans (by norm_num only) hz
  obtain ⟨hL, _⟩ :=
    Analysis.fixed_smooth_log_size_bounds hLp
      (le_trans (by norm_num only : (2000000000 : ℝ) ≤ 20000000000) hzsmall)
  have hlogLower : (10 : ℝ) ^ 12 ≤ Real.log p :=
    (by norm_num only : (10 : ℝ) ^ 12 ≤ 10 ^ 20).trans hL
  have hfactor : 1 + Real.log p ≤ (p : ℝ) ^ (1 / 2000 : ℝ) := by
    have hsmall := Analysis.thirty_two_mul_le_exp_div_two_thousand hlogLower
    have hone : 1 + Real.log p ≤ 32 * Real.log p := by nlinarith only [hlogLower]
    rw [Real.rpow_def_of_pos hpPos]
    calc
      1 + Real.log p ≤ 32 * Real.log p := hone
      _ ≤ Real.exp (Real.log p / 2000) := hsmall
      _ = Real.exp (Real.log p * (1 / 2000 : ℝ)) := by
        congr 1; ring
  have hlogPow : (1 + Real.log p) ^ (2 * 32) ≤ (p : ℝ) ^ 2 := by
    have hraised := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log p) hfactor (2 * 32)
    have hconvert : ((p : ℝ) ^ (1 / 2000 : ℝ)) ^ (2 * 32) = (p : ℝ) ^ (4 / 125 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      congr 1
      norm_num only
    have hexp : (4 / 125 : ℝ) ≤ 2 := by norm_num only
    have hpower : Real.rpow (p : ℝ) (4 / 125 : ℝ) ≤ Real.rpow (p : ℝ) (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpR hexp
    exact hraised.trans_eq hconvert |>.trans (hpower.trans_eq (Real.rpow_natCast (p : ℝ) 2))
  have hmargin :
    (2 ^ 176 : ℝ) ^ 32 * (finiteFiberCountCoefficient 64 32 : ℝ) ^ (13 * 32) *
        (1 + Real.log p) ^ (2 * 32) <
      (p : ℝ) ^ 3 := by
    calc
      _ ≤
          ((2 ^ 176 : ℝ) ^ 32 * (finiteFiberCountCoefficient 64 32 : ℝ) ^ (13 * 32)) *
            (p : ℝ) ^ 2 :=
        by gcongr
      _ < (p : ℝ) * (p : ℝ) ^ 2 := mul_lt_mul_of_pos_right hcoeff (by positivity)
      _ = (p : ℝ) ^ 3 := by
        calc
          _ = (p : ℝ) ^ 1 * (p : ℝ) ^ 2 := by rw [pow_one]
          _ = _ := by rw [← pow_add]
  have henergy :=
    thirteenth_energy_power_lt_of_log_square_slack hodd 32 (finiteFiberCountCoefficient 64 32) 3
      hmargin
  have hcount :=
    boundedCongruenceCount_power_le_explicit_finite_fiber_of_exponent_bound (a := 32) (c := 64)
      (g := 2) (by decide) (by decide) (by norm_num only) (by norm_num only) p H hodd hHp htop
  have hslack : 71 * 32 + 13 * 2 < 39 * 59 := by decide
  exact
    Analysis.thirteenth_counting_budget_of_energy_exponent_le (Fact.out : p.Prime).pos (by decide)
      (by decide) hslack hcut hheight hcount henergy (by decide)

/-- Every odd prime p≥P(145000006050) has a 59/32 cutoff satisfying the
strict finite-fiber energy budget. -/
theorem exists_fixed_finite_fiber_rational_energy_cutoff_32_59 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 145000006050 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 59 ≤ k ^ 32 ∧
        k ^ 32 ≤ 2 ^ 32 * p ^ 59 ∧
        p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ 59 < (p ^ 2) ^ 32 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 (by decide)
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 59) hp0) (by decide : 0 < 32) with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget (d := 2) (a := 32) (b := 59) hp0 (by decide) hlo
    have hheightExplicit : (p ^ 2 / k) ^ 32 ≤ p ^ 5 := by
      have hheight' := hheight
      rw [show (2 * 32 - 59 : ℕ) = 5 by decide] at hheight'
      exact hheight'
    have hHp := height_lt_base_of_power_bound hp1 (by decide : 5 < 32) hheightExplicit
    have htop :=
      height_le_real_power_of_power (a := 32) (d := 5) (by decide) hp1.le
        (by norm_num only : (5 : ℝ) / 32 ≤ 5 / 28) hheightExplicit
    exact fixed_log_square_finite_fiber_energy_budget_32_59 hodd hlarge hHp htop hlo hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Every odd prime p≥P(145000006050) has a 59/32 cutoff with
p J_p(k)<256k. Transfer the energy estimate by monotonicity. -/
theorem exists_fixed_finite_fiber_interval_bound_32_59 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 145000006050 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k < p ^ 2 ∧
        p ^ 59 ≤ k ^ 32 ∧ k ^ 32 ≤ 2 ^ 32 * p ^ 59 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ :=
    exists_fixed_finite_fiber_rational_energy_cutoff_32_59 hodd hlarge
  have hc : (32 : ℕ) ^ 32 * 2 ^ 32 < p :=
    (cutoff_coefficient_lt_explicit_finite_fiber_threshold (a := 32) (u := 145000006050)
          (by norm_num only)).trans_le
      hlarge
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt (by decide : 0 < 32)
      (by decide : 59 < 2 * 32) hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

/-- At scale 19/10, the logarithmic-square energy estimate gives the
finite-fiber budget above P(4449271510), with energy exponent three. -/
theorem fixed_log_square_finite_fiber_energy_budget_10_19 {p H k u : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hu : 76598623 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p)
    (hHp : H < p) (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (hcut : p ^ 19 ≤ k ^ 10)
    (hheight : H ^ 10 ≤ p ^ (2 * 10 - 19)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hA : (2 ^ 176 : ℕ) ^ 10 ≤ 2 ^ (176 * 10) := le_of_eq (pow_mul 2 176 10).symm
  have hcoeffNat :
    (2 ^ 176 : ℕ) ^ 10 * finiteFiberCountCoefficient 20 10 ^ (13 * 10) <
      explicitFiniteFiberPrimeThreshold u :=
    mul_power_lt_explicit_finite_fiber_threshold (B := 76596731 + 1) (k := 176 * 10)
      finiteFiberCountCoefficient_20_10_lt_double_exp.le hA
      (Nat.lt_of_lt_of_le (by norm_num only : 76598622 < 76598623) hu)
  have hPgt := one_lt_explicit_finite_fiber_threshold u
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (hPgt.le.trans hlarge)
  have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hPcast : (explicitFiniteFiberPrimeThreshold u : ℝ) ≤ p := by exact_mod_cast hlarge
  have hcoeffCast :
    (2 ^ 176 : ℝ) ^ 10 * (finiteFiberCountCoefficient 20 10 : ℝ) ^ (13 * 10) <
      (explicitFiniteFiberPrimeThreshold u : ℝ) := by
    exact_mod_cast hcoeffNat
  have hcoeff :
    (2 ^ 176 : ℝ) ^ 10 * (finiteFiberCountCoefficient 20 10 : ℝ) ^ (13 * 10) < (p : ℝ) :=
    hcoeffCast.trans_le hPcast
  have hLp := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := fifty_three_million_le_double_log_of_explicit_fiber_threshold hu hlarge
  have hlogLower : (10 : ℝ) ^ 12 ≤ Real.log p :=
    Analysis.twelve_pow_le_of_double_log_ge_fifty_three_million hLp hz
  have hfactor : 1 + Real.log p ≤ (p : ℝ) ^ (1 / 2000 : ℝ) := by
    have hsmall := Analysis.thirty_two_mul_le_exp_div_two_thousand hlogLower
    have hone : 1 + Real.log p ≤ 32 * Real.log p := by nlinarith only [hlogLower]
    rw [Real.rpow_def_of_pos hpPos]
    calc
      1 + Real.log p ≤ 32 * Real.log p := hone
      _ ≤ Real.exp (Real.log p / 2000) := hsmall
      _ = Real.exp (Real.log p * (1 / 2000 : ℝ)) := by
        congr 1; ring
  have hlogPow : (1 + Real.log p) ^ (2 * 10) ≤ (p : ℝ) ^ 2 := by
    have hraised := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log p) hfactor (2 * 10)
    have hconvert : ((p : ℝ) ^ (1 / 2000 : ℝ)) ^ (2 * 10) = (p : ℝ) ^ (1 / 100 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      congr 1
      norm_num only
    have hexp : (1 / 100 : ℝ) ≤ 2 := by norm_num only
    have hpower : Real.rpow (p : ℝ) (1 / 100 : ℝ) ≤ Real.rpow (p : ℝ) (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpR hexp
    exact hraised.trans_eq hconvert |>.trans (hpower.trans_eq (Real.rpow_natCast (p : ℝ) 2))
  have hmargin :
    (2 ^ 176 : ℝ) ^ 10 * (finiteFiberCountCoefficient 20 10 : ℝ) ^ (13 * 10) *
        (1 + Real.log p) ^ (2 * 10) <
      (p : ℝ) ^ 3 := by
    calc
      _ ≤
          ((2 ^ 176 : ℝ) ^ 10 * (finiteFiberCountCoefficient 20 10 : ℝ) ^ (13 * 10)) *
            (p : ℝ) ^ 2 :=
        by gcongr
      _ < (p : ℝ) * (p : ℝ) ^ 2 := mul_lt_mul_of_pos_right hcoeff (by positivity)
      _ = (p : ℝ) ^ 3 := by
        calc
          _ = (p : ℝ) ^ 1 * (p : ℝ) ^ 2 := by rw [pow_one]
          _ = _ := by rw [← pow_add]
  have henergy :=
    thirteenth_energy_power_lt_of_log_square_slack hodd 10 (finiteFiberCountCoefficient 20 10) 3
      hmargin
  have hcount :=
    boundedCongruenceCount_power_le_explicit_finite_fiber_of_exponent_bound (a := 10) (c := 20)
      (g := 2) (by decide) (by decide) (by norm_num only) (by norm_num only) p H hodd hHp htop
  have hslack : 71 * 10 + 13 * 2 < 39 * 19 := by decide
  exact
    Analysis.thirteenth_counting_budget_of_energy_exponent_le (Fact.out : p.Prime).pos (by decide)
      (by decide) hslack hcut hheight hcount henergy (by decide)

/-- At scale 19/10, the free precision-20 count and logarithmic-square energy
estimate fit the explicit prime threshold `P(21518759)`. -/
theorem fixed_log_square_finite_fiber_energy_budget_10_19_free {p H k : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 21518759 ≤ p) (hHp : H < p)
    (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (hcut : p ^ 19 ≤ k ^ 10)
    (hheight : H ^ 10 ≤ p ^ (2 * 10 - 19)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hcoeffNat := free_finite_fiber_energy_coefficient_lt_prime_threshold_20
  have hPgt := one_lt_explicit_finite_fiber_threshold 21518759
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (hPgt.le.trans hlarge)
  have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hPcast : (explicitFiniteFiberPrimeThreshold 21518759 : ℝ) ≤ p := by exact_mod_cast hlarge
  have hcoeffCast :
    (2 ^ 176 : ℝ) ^ 10 * (freeFiniteFiberCountCoefficient 20 10 : ℝ) ^ (13 * 10) <
      (explicitFiniteFiberPrimeThreshold 21518759 : ℝ) := by
    exact_mod_cast hcoeffNat
  have hcoeff :
    (2 ^ 176 : ℝ) ^ 10 * (freeFiniteFiberCountCoefficient 20 10 : ℝ) ^ (13 * 10) < (p : ℝ) :=
    hcoeffCast.trans_le hPcast
  have hLp := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz :=
    fourteen_million_nine_hundred_thousand_le_double_log_of_explicit_fiber_threshold
      (by norm_num only : 21518759 ≤ 21518759) hlarge
  have hlogLower : (10 : ℝ) ^ 12 ≤ Real.log p :=
    Analysis.twelve_pow_le_of_double_log_ge_fourteen_nine_million hLp hz
  have hfactor : 1 + Real.log p ≤ (p : ℝ) ^ (1 / 2000 : ℝ) := by
    have hsmall := Analysis.thirty_two_mul_le_exp_div_two_thousand hlogLower
    have hone : 1 + Real.log p ≤ 32 * Real.log p := by nlinarith only [hlogLower]
    rw [Real.rpow_def_of_pos hpPos]
    calc
      1 + Real.log p ≤ 32 * Real.log p := hone
      _ ≤ Real.exp (Real.log p / 2000) := hsmall
      _ = Real.exp (Real.log p * (1 / 2000 : ℝ)) := by
        congr 1; ring
  have hlogPow : (1 + Real.log p) ^ (2 * 10) ≤ (p : ℝ) ^ 2 := by
    have hraised := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log p) hfactor (2 * 10)
    have hconvert : ((p : ℝ) ^ (1 / 2000 : ℝ)) ^ (2 * 10) = (p : ℝ) ^ (1 / 100 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      congr 1
      norm_num only
    have hexp : (1 / 100 : ℝ) ≤ 2 := by norm_num only
    have hpower : Real.rpow (p : ℝ) (1 / 100 : ℝ) ≤ Real.rpow (p : ℝ) 2 :=
      Real.rpow_le_rpow_of_exponent_le hpR hexp
    exact hraised.trans_eq hconvert |>.trans (hpower.trans_eq (Real.rpow_natCast (p : ℝ) 2))
  have hmargin :
    (2 ^ 176 : ℝ) ^ 10 * (freeFiniteFiberCountCoefficient 20 10 : ℝ) ^ (13 * 10) *
        (1 + Real.log p) ^ (2 * 10) <
      (p : ℝ) ^ 3 := by
    calc
      _ ≤
          ((2 ^ 176 : ℝ) ^ 10 * (freeFiniteFiberCountCoefficient 20 10 : ℝ) ^ (13 * 10)) *
            (p : ℝ) ^ 2 :=
        by gcongr
      _ < (p : ℝ) * (p : ℝ) ^ 2 := mul_lt_mul_of_pos_right hcoeff (by positivity)
      _ = (p : ℝ) ^ 3 := by
        calc
          _ = (p : ℝ) ^ 1 * (p : ℝ) ^ 2 := by rw [pow_one]
          _ = _ := by rw [← pow_add]
  have henergy :=
    thirteenth_energy_power_lt_of_log_square_slack hodd 10 (freeFiniteFiberCountCoefficient 20 10) 3
      hmargin
  have hcount :=
    boundedCongruenceCount_power_le_explicit_free_finite_fiber (a := 10) (h := 10) (c := 20) (g :=
      2) (by decide) (by decide) (by decide)
      (by norm_num only : (1 / (20 : ℝ)) ≤ (1 / (10 : ℝ)) / 2)
      (by norm_num only : 1 / 84 + 1 / 10 ≤ (2 : ℝ) / 10) p H hodd hHp htop
  have hslack : 71 * 10 + 13 * 2 < 39 * 19 := by norm_num only
  exact
    Analysis.thirteenth_counting_budget_of_energy_exponent_le (Fact.out : p.Prime).pos (by decide)
      (by decide) hslack hcut hheight hcount henergy (by norm_num only)

/-- If the inner threshold index increases by at least one, squaring its
double-exponential threshold stays below the threshold at the larger index. -/
theorem explicit_finite_fiber_threshold_square_le {u v : ℕ} (huv : u + 1 ≤ v) :
    explicitFiniteFiberPrimeThreshold u ^ 2 ≤ explicitFiniteFiberPrimeThreshold v := by
  rw [explicitFiniteFiberPrimeThreshold, explicitFiniteFiberPrimeThreshold, ← Nat.pow_mul]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  calc
    2 ^ u * 2 = 2 ^ (u + 1) := by rw [pow_succ]
    _ ≤ 2 ^ v := Nat.pow_le_pow_right (by decide : 0 < 2) huv

/-- At scale 30/16, the free precision-18 count with loss 9 and logarithmic-
square energy estimate fit the explicit prime threshold `P(21518759)`. -/
theorem fixed_log_square_finite_fiber_energy_budget_30_16_free {p H k : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 21518759 ≤ p) (hHp : H < p)
    (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (hcut : p ^ 30 ≤ k ^ 16)
    (hheight : H ^ 16 ≤ p ^ (2 * 16 - 30)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hcountCoeff :=
    freeFiniteFiberCountCoefficient_18_9_lt_double_exp (by norm_num only : 17428673 ≤ 17428673)
  have hcoeffNat :=
    free_finite_fiber_energy_coefficient_lt_prime_threshold (a := 16) (B := 17428673) (u :=
      21518759) (c := 18) (h := 9) hcountCoeff (by norm_num only)
  have hPgt := one_lt_explicit_finite_fiber_threshold 21518759
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (hPgt.le.trans hlarge)
  have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hPcast : (explicitFiniteFiberPrimeThreshold 21518759 : ℝ) ≤ p := by exact_mod_cast hlarge
  have hcoeffCast :
    (2 ^ 176 : ℝ) ^ 16 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 16) <
      (explicitFiniteFiberPrimeThreshold 21518759 : ℝ) := by
    exact_mod_cast hcoeffNat
  have hcoeff :
    (2 ^ 176 : ℝ) ^ 16 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 16) < (p : ℝ) :=
    hcoeffCast.trans_le hPcast
  have hLp := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz :=
    fourteen_million_nine_hundred_thousand_le_double_log_of_explicit_fiber_threshold
      (by norm_num only : 21518759 ≤ 21518759) hlarge
  have hlogLower : (10 : ℝ) ^ 12 ≤ Real.log p :=
    Analysis.twelve_pow_le_of_double_log_ge_fourteen_nine_million hLp hz
  have hfactor : 1 + Real.log p ≤ (p : ℝ) ^ (1 / 2000 : ℝ) := by
    have hsmall := Analysis.thirty_two_mul_le_exp_div_two_thousand hlogLower
    have hone : 1 + Real.log p ≤ 32 * Real.log p := by nlinarith only [hlogLower]
    rw [Real.rpow_def_of_pos hpPos]
    calc
      1 + Real.log p ≤ 32 * Real.log p := hone
      _ ≤ Real.exp (Real.log p / 2000) := hsmall
      _ = Real.exp (Real.log p * (1 / 2000 : ℝ)) := by
        congr 1; ring
  have hbaseNonneg : 0 ≤ 1 + Real.log p := by linarith only [hlogLower]
  have hlogPow : (1 + Real.log p) ^ (2 * 16) ≤ (p : ℝ) := by
    have hraised := pow_le_pow_left₀ hbaseNonneg hfactor (2 * 16)
    have hconvert : ((p : ℝ) ^ (1 / 2000 : ℝ)) ^ (2 * 16) = (p : ℝ) ^ (2 / 125 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      congr 1
      norm_num only
    have hexp : (2 / 125 : ℝ) ≤ 1 := by norm_num only
    have hpower : Real.rpow (p : ℝ) (2 / 125 : ℝ) ≤ Real.rpow (p : ℝ) 1 :=
      Real.rpow_le_rpow_of_exponent_le hpR hexp
    exact hraised.trans_eq hconvert |>.trans (hpower.trans_eq (Real.rpow_one (p : ℝ)))
  have hcoefNonneg :
    0 ≤ (2 ^ 176 : ℝ) ^ 16 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 16) :=
    mul_nonneg (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 176) 16)
      (pow_nonneg (Nat.cast_nonneg (freeFiniteFiberCountCoefficient 18 9)) (13 * 16))
  have hmargin :
    (2 ^ 176 : ℝ) ^ 16 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 16) *
        (1 + Real.log p) ^ (2 * 16) <
      (p : ℝ) ^ 2 := by
    calc
      _ ≤ ((2 ^ 176 : ℝ) ^ 16 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 16)) * p :=
        mul_le_mul_of_nonneg_left hlogPow hcoefNonneg
      _ < p * p := mul_lt_mul_of_pos_right hcoeff hpPos
      _ = p ^ 2 := by rw [pow_two]
  have henergy :=
    thirteenth_energy_power_lt_of_log_square_slack hodd 16 (freeFiniteFiberCountCoefficient 18 9) 2
      hmargin
  have hcount :=
    boundedCongruenceCount_power_le_explicit_free_finite_fiber (a := 16) (h := 9) (c := 18) (g := 2)
      (by decide) (by decide) (by decide) (by norm_num only : (1 / (18 : ℝ)) ≤ (1 / (9 : ℝ)) / 2)
      (by norm_num only : 1 / 84 + 1 / 9 ≤ (2 : ℝ) / 16) p H hodd hHp htop
  have hslack : 71 * 16 + 13 * 2 < 39 * 30 := by norm_num only
  exact
    Analysis.thirteenth_counting_budget_of_energy_exponent_le (Fact.out : p.Prime).pos (by decide)
      (by decide) hslack hcut hheight hcount henergy (by norm_num only)

/-- At scale 28/15, the free precision-18 count with loss 9 and logarithmic-
square energy estimate fit the explicit prime threshold `P(u)` for every
`u≥17431511`. The
available integer slack is one, so the coefficient and logarithmic factors
are each absorbed by one prime factor. -/
theorem fixed_log_square_finite_fiber_energy_budget_28_15_free {p H k u : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hu : 17431511 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p)
    (hHp : H < p) (htop : (H : ℝ) ≤ (p : ℝ) ^ (2 / 15 : ℝ)) (hcut : p ^ 28 ≤ k ^ 15)
    (hheight : H ^ 15 ≤ p ^ (2 * 15 - 28)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hcountCoeff :=
    freeFiniteFiberCountCoefficient_18_9_lt_double_exp (by norm_num only : 17428673 ≤ 17428673)
  have hcoeffNat :=
    free_finite_fiber_energy_coefficient_lt_prime_threshold (a := 15) (B := 17428673) (u :=
      17431510) (c := 18) (h := 9) hcountCoeff (by norm_num only)
  have hPgt := one_lt_explicit_finite_fiber_threshold u
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (hPgt.le.trans hlarge)
  have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have huThreshold : 17431510 + 1 ≤ u := Nat.le_trans (by norm_num only) hu
  have hthresholdSq := explicit_finite_fiber_threshold_square_le huThreshold
  have hcoeffCastSmall :
    (2 ^ 176 : ℝ) ^ 15 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 15) <
      (explicitFiniteFiberPrimeThreshold 17431510 : ℝ) := by
    exact_mod_cast hcoeffNat
  have hcoeffBaseNonneg :
    0 ≤ (2 ^ 176 : ℝ) ^ 15 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 15) :=
    mul_nonneg (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 176) 15)
      (pow_nonneg (Nat.cast_nonneg (freeFiniteFiberCountCoefficient 18 9)) (13 * 15))
  have hcoeffSmallSq :
    ((2 ^ 176 : ℝ) ^ 15 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 15)) ^ 2 <
      (explicitFiniteFiberPrimeThreshold 17431510 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hcoeffCastSmall hcoeffBaseNonneg (by norm_num only : (2 : ℕ) ≠ 0)
  have hcoeffSquare :
    ((2 ^ 176 : ℝ) ^ 15 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 15)) ^ 2 <
      (p : ℝ) := by
    calc
      _ < (explicitFiniteFiberPrimeThreshold 17431510 : ℝ) ^ 2 := hcoeffSmallSq
      _ ≤ (explicitFiniteFiberPrimeThreshold u : ℝ) := by exact_mod_cast hthresholdSq
      _ ≤ p := by exact_mod_cast hlarge
  have hLp := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz :=
    twelve_million_eighty_two_thousand_six_hundred_one_le_double_log_of_explicit_fiber_threshold hu
      hlarge
  have hlogLower : (10 : ℝ) ^ 12 ≤ Real.log p :=
    Analysis.twelve_pow_le_of_double_log_ge_twelve_million_eighty_two_thousand_six_hundred_one hLp
      hz
  have hfactor : 1 + Real.log p ≤ (p : ℝ) ^ (1 / 2000 : ℝ) := by
    have hsmall := Analysis.thirty_two_mul_le_exp_div_two_thousand hlogLower
    have hone : 1 + Real.log p ≤ 32 * Real.log p := by nlinarith only [hlogLower]
    rw [Real.rpow_def_of_pos hpPos]
    calc
      1 + Real.log p ≤ 32 * Real.log p := hone
      _ ≤ Real.exp (Real.log p / 2000) := hsmall
      _ = Real.exp (Real.log p * (1 / 2000 : ℝ)) := by
        congr 1; ring
  have hbaseNonneg : 0 ≤ 1 + Real.log p := by linarith only [hlogLower]
  have hlogPow : (1 + Real.log p) ^ 60 ≤ (p : ℝ) := by
    have hraised := pow_le_pow_left₀ hbaseNonneg hfactor 60
    have hconvert : ((p : ℝ) ^ (1 / 2000 : ℝ)) ^ 60 = (p : ℝ) ^ (3 / 100 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      congr 1
      norm_num only
    have hexp : (3 / 100 : ℝ) ≤ 1 := by norm_num only
    have hpower : Real.rpow (p : ℝ) (3 / 100 : ℝ) ≤ Real.rpow (p : ℝ) 1 :=
      Real.rpow_le_rpow_of_exponent_le hpR hexp
    exact hraised.trans_eq hconvert |>.trans (hpower.trans_eq (Real.rpow_one (p : ℝ)))
  let logCost : ℝ := (1 + Real.log p) ^ 30
  have hlogCostSq : logCost ^ 2 ≤ (p : ℝ) := by
    have hlogPow' := hlogPow
    rw [show 60 = 30 * 2 by norm_num only, pow_mul] at hlogPow'
    simpa only [logCost] using hlogPow'
  have hlogCostNonneg : 0 ≤ logCost := by
    dsimp only [logCost]
    exact pow_nonneg hbaseNonneg 30
  have hcoeffNonneg := hcoeffBaseNonneg
  have hmargin :
    (2 ^ 176 : ℝ) ^ 15 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 15) * logCost < p := by
    by_cases hzero : logCost = 0
    · rw [hzero]
      simp only [mul_zero]
      exact hpPos
    · have hlogCostPos : 0 < logCost ^ 2 :=
        pow_pos (lt_of_le_of_ne hlogCostNonneg (Ne.symm hzero)) 2
      have hprodSq :
        (((2 ^ 176 : ℝ) ^ 15 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 15)) * logCost) ^
            2 <
          (p : ℝ) ^ 2 := by
        calc
          _ =
              ((2 ^ 176 : ℝ) ^ 15 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 15)) ^ 2 *
                logCost ^ 2 :=
            by ring
          _ < (p : ℝ) * logCost ^ 2 := mul_lt_mul_of_pos_right hcoeffSquare hlogCostPos
          _ ≤ p * p := mul_le_mul_of_nonneg_left hlogCostSq (Nat.cast_nonneg p)
          _ = (p : ℝ) ^ 2 := by rw [pow_two]
      nlinarith only [hcoeffNonneg, hlogCostNonneg, hpPos, hprodSq]
  have hmargin' :
    (2 ^ 176 : ℝ) ^ 15 * (freeFiniteFiberCountCoefficient 18 9 : ℝ) ^ (13 * 15) *
        (1 + Real.log p) ^ (2 * 15) <
      (p : ℝ) ^ 1 := by
    simpa only [logCost, show 2 * 15 = 30 by norm_num only, pow_one] using hmargin
  have henergy :=
    thirteenth_energy_power_lt_of_log_square_slack hodd 15 (freeFiniteFiberCountCoefficient 18 9) 1
      hmargin'
  have htop' : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) := by
    exact
      htop.trans (Real.rpow_le_rpow_of_exponent_le hpR (by norm_num only : (2 / 15 : ℝ) ≤ 5 / 28))
  have hcount :=
    boundedCongruenceCount_power_le_explicit_free_finite_fiber (a := 15) (h := 9) (c := 18) (g := 2)
      (by decide) (by decide) (by decide) (by norm_num only : (1 / (18 : ℝ)) ≤ (1 / (9 : ℝ)) / 2)
      (by norm_num only : 1 / 84 + 1 / 9 ≤ (2 : ℝ) / 15) p H hodd hHp htop'
  have hslack : 71 * 15 + 13 * 2 < 39 * 28 := by norm_num only
  exact
    Analysis.thirteenth_counting_budget_of_energy_exponent_le (Fact.out : p.Prime).pos (by decide)
      (by decide) hslack hcut hheight hcount henergy (by norm_num only)

/-- Every odd prime above `P(21518759)` has a 30/16 cutoff satisfying the
free finite-fiber energy budget. -/
theorem exists_fixed_finite_fiber_rational_energy_cutoff_30_16_free {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 21518759 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 30 ≤ k ^ 16 ∧
        k ^ 16 ≤ 2 ^ 16 * p ^ 30 ∧
        p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ 30 < (p ^ 2) ^ 16 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 (by norm_num only)
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 30) hp0) (by decide : 0 < 16) with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget (d := 2) (a := 16) (b := 30) hp0 (by decide) hlo
    have hheightExplicit : (p ^ 2 / k) ^ 16 ≤ p ^ 2 := by
      have hheight' := hheight
      rw [show (2 * 16 - 30 : ℕ) = 2 by norm_num only] at hheight'
      exact hheight'
    have hHp := height_lt_base_of_power_bound hp1 (by norm_num only : 2 < 16) hheightExplicit
    have htop :=
      height_le_real_power_of_power (a := 16) (d := 2) (rho := (5 / 28 : ℝ)) (by norm_num only)
        hp1.le (by norm_num only : (2 : ℕ) / 16 ≤ (5 : ℝ) / 28) hheightExplicit
    exact fixed_log_square_finite_fiber_energy_budget_30_16_free hodd hlarge hHp htop hlo hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Inputs: an odd prime above `P(21518759)`.
Claim: a 30/16 cutoff has initial-count cost less than `256 * k`.
Content: Convert the energy bound for the finite-fiber count into the
initial-count interval used by smooth-number extraction. Proof: Bound the
cutoff height by `p^2` and apply monotonicity of the congruence count.
Role: Supplies the interval estimate for the 30/16 prime-extraction theorem. -/
theorem exists_fixed_finite_fiber_interval_bound_30_16_free {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 21518759 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k < p ^ 2 ∧
        p ^ 30 ≤ k ^ 16 ∧ k ^ 16 ≤ 2 ^ 16 * p ^ 30 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ :=
    exists_fixed_finite_fiber_rational_energy_cutoff_30_16_free hodd hlarge
  have hc : (32 : ℕ) ^ 16 * 2 ^ 16 < p :=
    (cutoff_coefficient_lt_explicit_finite_fiber_threshold (a := 16) (u := 21518759)
          (by norm_num only)).trans_le
      hlarge
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt (by decide : 0 < 16)
      (by decide : 30 < 2 * 16) hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

/-- Every odd prime above `P(u)` with `u≥17431511` has a 28/15 cutoff
satisfying the free finite-fiber energy budget. -/
theorem exists_fixed_finite_fiber_rational_energy_cutoff_28_15_free {p u : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hu : 17431511 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 28 ≤ k ^ 15 ∧
        k ^ 15 ≤ 2 ^ 15 * p ^ 28 ∧
        p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ 28 < (p ^ 2) ^ 15 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 (by norm_num only)
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 28) hp0) (by decide : 0 < 15) with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget (d := 2) (a := 15) (b := 28) hp0 (by decide) hlo
    have hheightExplicit : (p ^ 2 / k) ^ 15 ≤ p ^ 2 := by
      have hheight' := hheight
      rw [show (2 * 15 - 28 : ℕ) = 2 by norm_num only] at hheight'
      exact hheight'
    have hHp := height_lt_base_of_power_bound hp1 (by norm_num only : 2 < 15) hheightExplicit
    have htop :=
      height_le_real_power_of_power (a := 15) (d := 2) (rho := (2 / 15 : ℝ)) (by norm_num only)
        hp1.le (by norm_num only : (2 : ℕ) / 15 ≤ (2 : ℝ) / 15) hheightExplicit
    exact fixed_log_square_finite_fiber_energy_budget_28_15_free hodd hu hlarge hHp htop hlo hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Inputs: an odd prime above `P(21518759)`.
Claim: a 28/15 cutoff has initial-count cost less than `256 * k`.
Content: Transfer the finite-fiber energy bound to the initial-count interval
used by smooth-number extraction. -/
theorem exists_fixed_finite_fiber_interval_bound_28_15_free {p : ℕ} [Fact p.Prime] {u : ℕ}
    (hodd : Odd p) (hu : 17431511 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k < p ^ 2 ∧
        p ^ 28 ≤ k ^ 15 ∧ k ^ 15 ≤ 2 ^ 15 * p ^ 28 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ :=
    exists_fixed_finite_fiber_rational_energy_cutoff_28_15_free hodd hu hlarge
  have hc : (32 : ℕ) ^ 15 * 2 ^ 15 < p :=
    (cutoff_coefficient_lt_explicit_finite_fiber_threshold (a := 15) (u := u)
          (Nat.lt_of_lt_of_le (by norm_num only) hu)).trans_le
      hlarge
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt (by decide : 0 < 15)
      (by decide : 28 < 2 * 15) hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

/-- At scale 150/82, the free precision-162 count and the logarithmic-square
energy estimate fit the explicit prime threshold `P(1411732827)`. -/
theorem fixed_log_square_finite_fiber_energy_budget_150_82_free {p H k : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 1411732827 ≤ p) (hHp : H < p)
    (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (hcut : p ^ 150 ≤ k ^ 82)
    (hheight : H ^ 82 ≤ p ^ (2 * 82 - 150)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hcoeffNat := free_finite_fiber_energy_coefficient_lt_prime_threshold_162
  have hPgt := one_lt_explicit_finite_fiber_threshold 1411732827
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (hPgt.le.trans hlarge)
  have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hPcast : (explicitFiniteFiberPrimeThreshold 1411732827 : ℝ) ≤ p := by exact_mod_cast hlarge
  have hcoeffCast :
    (2 ^ 176 : ℝ) ^ 82 * (freeFiniteFiberCountCoefficient 162 81 : ℝ) ^ (13 * 82) <
      (explicitFiniteFiberPrimeThreshold 1411732827 : ℝ) := by
    exact_mod_cast hcoeffNat
  have hcoeff :
    (2 ^ 176 : ℝ) ^ 82 * (freeFiniteFiberCountCoefficient 162 81 : ℝ) ^ (13 * 82) < (p : ℝ) :=
    hcoeffCast.trans_le hPcast
  have hLp := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz :=
    fifty_three_million_le_double_log_of_explicit_fiber_threshold
      (by norm_num only : 76598623 ≤ 1411732827) hlarge
  have hlogLower : (10 : ℝ) ^ 12 ≤ Real.log p :=
    Analysis.twelve_pow_le_of_double_log_ge_fifty_three_million hLp hz
  have hfactor : 1 + Real.log p ≤ (p : ℝ) ^ (1 / 2000 : ℝ) := by
    have hsmall := Analysis.thirty_two_mul_le_exp_div_two_thousand hlogLower
    have hone : 1 + Real.log p ≤ 32 * Real.log p := by nlinarith only [hlogLower]
    rw [Real.rpow_def_of_pos hpPos]
    calc
      1 + Real.log p ≤ 32 * Real.log p := hone
      _ ≤ Real.exp (Real.log p / 2000) := hsmall
      _ = Real.exp (Real.log p * (1 / 2000 : ℝ)) := by
        congr 1; ring
  have hlogPow : (1 + Real.log p) ^ (2 * 82) ≤ (p : ℝ) := by
    have hraised := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log p) hfactor (2 * 82)
    have hconvert : ((p : ℝ) ^ (1 / 2000 : ℝ)) ^ (2 * 82) = (p : ℝ) ^ (41 / 500 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      congr 1
      norm_num only
    have hexp : (41 / 500 : ℝ) ≤ 1 := by norm_num only
    have hpower : Real.rpow (p : ℝ) (41 / 500 : ℝ) ≤ Real.rpow (p : ℝ) 1 :=
      Real.rpow_le_rpow_of_exponent_le hpR hexp
    exact hraised.trans_eq hconvert |>.trans (hpower.trans_eq (Real.rpow_one (p : ℝ)))
  have hmargin :
    (2 ^ 176 : ℝ) ^ 82 * (freeFiniteFiberCountCoefficient 162 81 : ℝ) ^ (13 * 82) *
        (1 + Real.log p) ^ (2 * 82) <
      (p : ℝ) ^ 2 := by
    calc
      _ ≤ ((2 ^ 176 : ℝ) ^ 82 * (freeFiniteFiberCountCoefficient 162 81 : ℝ) ^ (13 * 82)) * p :=
        mul_le_mul_of_nonneg_left hlogPow (by positivity)
      _ < p * p := mul_lt_mul_of_pos_right hcoeff (by positivity)
      _ = p ^ 2 := by rw [pow_two]
  have henergy :=
    thirteenth_energy_power_lt_of_log_square_slack hodd 82 (freeFiniteFiberCountCoefficient 162 81)
      2 hmargin
  have hcount :=
    boundedCongruenceCount_power_le_explicit_free_finite_fiber (a := 82) (h := 81) (c := 162) (g :=
      2) (by decide) (by decide) (by decide)
      (by norm_num only : (1 / (162 : ℝ)) ≤ (1 / (81 : ℝ)) / 2)
      (by norm_num only : 1 / 84 + 1 / 81 ≤ (2 : ℝ) / 82) p H hodd hHp htop
  have hslack : 71 * 82 + 13 * 2 < 39 * 150 := by norm_num only
  exact
    Analysis.thirteenth_counting_budget_of_energy_exponent_le (Fact.out : p.Prime).pos (by decide)
      (by decide) hslack hcut hheight hcount henergy (by norm_num only)

/-- At scale 75/41, use the precision-162 count coefficient with loss 1/81
and consume the single available integer slack. The squared coefficient
threshold is inherited from the 150/82 estimate, while the fourth-power
logarithmic bound is the same as its exponent-164 absorption. -/
theorem fixed_log_square_finite_fiber_energy_budget_75_41_free {p H k : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 1411732827 ≤ p) (hHp : H < p)
    (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (hcut : p ^ 75 ≤ k ^ 41)
    (hheight : H ^ 41 ≤ p ^ (2 * 41 - 75)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hcoeffNat := free_finite_fiber_energy_coefficient_lt_prime_threshold_162
  have hPgt := one_lt_explicit_finite_fiber_threshold 1411732827
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (hPgt.le.trans hlarge)
  have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hcoeffCast :
    (2 ^ 176 : ℝ) ^ 82 * (freeFiniteFiberCountCoefficient 162 81 : ℝ) ^ (13 * 82) <
      (explicitFiniteFiberPrimeThreshold 1411732827 : ℝ) := by
    exact_mod_cast hcoeffNat
  let x : ℝ := (2 ^ 176 : ℝ) ^ 41
  let y : ℝ := (freeFiniteFiberCountCoefficient 162 81 : ℝ) ^ (13 * 41)
  have hx : x ^ 2 = (2 ^ 176 : ℝ) ^ 82 := by
    dsimp only [x]
    rw [← pow_mul]
  have hy : y ^ 2 = (freeFiniteFiberCountCoefficient 162 81 : ℝ) ^ (13 * 82) := by
    dsimp only [y]
    rw [← pow_mul]
  have hcoeff : (x * y) ^ 2 < p := by
    calc
      (x * y) ^ 2 = x ^ 2 * y ^ 2 := by rw [mul_pow]
      _ = (2 ^ 176 : ℝ) ^ 82 * (freeFiniteFiberCountCoefficient 162 81 : ℝ) ^ (13 * 82) := by
        rw [hx, hy]
      _ < explicitFiniteFiberPrimeThreshold 1411732827 := by exact_mod_cast hcoeffNat
      _ ≤ p := by exact_mod_cast hlarge
  have hLp := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz :=
    fifty_three_million_le_double_log_of_explicit_fiber_threshold
      (by norm_num only : 76598623 ≤ 1411732827) hlarge
  have hlogLower : (10 : ℝ) ^ 12 ≤ Real.log p :=
    Analysis.twelve_pow_le_of_double_log_ge_fifty_three_million hLp hz
  have hfactor : 1 + Real.log p ≤ (p : ℝ) ^ (1 / 2000 : ℝ) := by
    have hsmall := Analysis.thirty_two_mul_le_exp_div_two_thousand hlogLower
    have hone : 1 + Real.log p ≤ 32 * Real.log p := by nlinarith only [hlogLower]
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)]
    calc
      1 + Real.log p ≤ 32 * Real.log p := hone
      _ ≤ Real.exp (Real.log p / 2000) := hsmall
      _ = Real.exp (Real.log p * (1 / 2000 : ℝ)) := by
        congr 1; ring
  have hlog : (1 + Real.log p) ^ (4 * 41) ≤ (p : ℝ) := by
    have hraised := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log p) hfactor (4 * 41)
    have hconvert : ((p : ℝ) ^ (1 / 2000 : ℝ)) ^ (4 * 41) = (p : ℝ) ^ (41 / 500 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      congr 1
      norm_num only
    have hexp : (41 / 500 : ℝ) ≤ 1 := by norm_num only
    have hpower : Real.rpow (p : ℝ) (41 / 500 : ℝ) ≤ Real.rpow (p : ℝ) 1 :=
      Real.rpow_le_rpow_of_exponent_le hpR hexp
    exact hraised.trans_eq hconvert |>.trans (hpower.trans_eq (Real.rpow_one (p : ℝ)))
  have hratio : 1 / 84 + 1 / 81 ≤ (1 : ℝ) / 41 := by norm_num only
  exact
    separate_count_finite_fiber_energy_budget_square (a := 41) (h := 81) (c := 162) (b := 75) (g :=
      1) hodd hHp htop (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only : 1 / (162 : ℝ) ≤ (1 / (81 : ℝ)) / 2)
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using hratio) (by norm_num only)
      (by norm_num only) hcut hheight hcoeff hlog

/-- At scale 2048/1120, precision 164 and independent loss 82 give a
square-slack energy bound below `P(1,447,213,072)`. -/
theorem fixed_log_square_finite_fiber_energy_budget_2048_1120_free {p H k : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 1447213072 ≤ p) (hHp : H < p)
    (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (hcut : p ^ 2048 ≤ k ^ 1120)
    (hheight : H ^ 1120 ≤ p ^ (2 * 1120 - 2048)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hcoeffNat := free_finite_fiber_energy_coefficient_lt_prime_threshold_164_82_2240
  have hPgt := one_lt_explicit_finite_fiber_threshold 1447213072
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (hPgt.le.trans hlarge)
  have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  let x : ℝ := (2 ^ 176 : ℝ) ^ 1120
  let y : ℝ := (freeFiniteFiberCountCoefficient 164 82 : ℝ) ^ (13 * 1120)
  have hx : x ^ 2 = (2 ^ 176 : ℝ) ^ 2240 := by
    dsimp only [x]
    rw [← pow_mul]
  have hy : y ^ 2 = (freeFiniteFiberCountCoefficient 164 82 : ℝ) ^ (13 * 2240) := by
    dsimp only [y]
    rw [← pow_mul]
  have hcoeff : (x * y) ^ 2 < p := by
    calc
      (x * y) ^ 2 = x ^ 2 * y ^ 2 := by rw [mul_pow]
      _ = (2 ^ 176 : ℝ) ^ 2240 * (freeFiniteFiberCountCoefficient 164 82 : ℝ) ^ (13 * 2240) := by
        rw [hx, hy]
      _ < explicitFiniteFiberPrimeThreshold 1447213072 := by exact_mod_cast hcoeffNat
      _ ≤ p := by exact_mod_cast hlarge
  have hz :=
    fifty_three_million_le_double_log_of_explicit_fiber_threshold
      (by norm_num only : 76598623 ≤ 1447213072) hlarge
  have hlogLower :=
    Analysis.twelve_pow_le_of_double_log_ge_fifty_three_million
      (Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)) hz
  have hlogLowerFive : (2000000000 : ℝ) ≤ Real.log p :=
    (by norm_num only : (2000000000 : ℝ) ≤ 10 ^ 12).trans hlogLower
  have hfactor : 1 + Real.log p ≤ (p : ℝ) ^ (1 / 5000 : ℝ) := by
    have hsmall := Analysis.thirty_two_mul_le_exp_div_five_thousand hlogLowerFive
    have hone : 1 + Real.log p ≤ 32 * Real.log p := by nlinarith only [hlogLower]
    rw [Real.rpow_def_of_pos hpPos]
    calc
      1 + Real.log p ≤ 32 * Real.log p := hone
      _ ≤ Real.exp (Real.log p / 5000) := hsmall
      _ = Real.exp (Real.log p * (1 / 5000 : ℝ)) := by
        congr 1; ring
  have hlog : (1 + Real.log p) ^ (4 * 1120) ≤ p := by
    have hraised := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log p) hfactor (4 * 1120)
    have hconvert : ((p : ℝ) ^ (1 / 5000 : ℝ)) ^ (4 * 1120) = (p : ℝ) ^ (112 / 125 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      congr 1
      norm_num only
    have hexp : (112 / 125 : ℝ) ≤ 1 := by norm_num only
    have hpower : Real.rpow p (112 / 125 : ℝ) ≤ Real.rpow p 1 :=
      Real.rpow_le_rpow_of_exponent_le hpR hexp
    exact hraised.trans_eq hconvert |>.trans (hpower.trans_eq (Real.rpow_one p))
  have hratio : 1 / 84 + 1 / (82 : ℝ) ≤ (27 : ℝ) / 1120 := by norm_num only
  have hslack : 71 * 1120 + 13 * 27 < 39 * 2048 := by norm_num only
  exact
    separate_count_finite_fiber_energy_budget_square (a := 1120) (h := 82) (c := 164) (b := 2048)
      (g := 27) hodd hHp htop (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only : 1 / (164 : ℝ) ≤ (1 / (82 : ℝ)) / 2) hratio (by norm_num only) hslack hcut
      hheight hcoeff hlog

set_option exponentiation.threshold 4096 in
/-- Every odd prime above `P(1,447,213,072)` has a 2048/1120 cutoff
satisfying the free finite-fiber energy budget. -/
theorem exists_fixed_finite_fiber_rational_energy_cutoff_2048_1120_free {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 1447213072 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 2048 ≤ k ^ 1120 ∧
        k ^ 1120 ≤ 2 ^ 1120 * p ^ 2048 ∧
        p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ 2048 < (p ^ 2) ^ 1120 := by
    calc
      p ^ 2048 < p ^ (2 * 1120) := Nat.pow_lt_pow_right hp1 (by norm_num only : 2048 < 2 * 1120)
      _ = (p ^ 2) ^ 1120 := Nat.pow_mul p 2 1120
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 2048) hp0)
      (by norm_num only : 0 < 1120) with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget (d := 2) (a := 1120) (b := 2048) hp0 (by norm_num only) hlo
    have hheightExplicit : (p ^ 2 / k) ^ 1120 ≤ p ^ 192 := by
      have hheight' := hheight
      rw [show (2 * 1120 - 2048 : ℕ) = 192 by norm_num only] at hheight'
      exact hheight'
    have hHp := height_lt_base_of_power_bound hp1 (by norm_num only : 192 < 1120) hheightExplicit
    have htop :=
      height_le_real_power_of_power (a := 1120) (d := 192) (by norm_num only) hp1.le
        (by norm_num only : (192 : ℕ) / 1120 ≤ (5 : ℝ) / 28) hheightExplicit
    exact
      fixed_log_square_finite_fiber_energy_budget_2048_1120_free hodd hlarge hHp htop hlo hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Transfer the free 2048/1120 energy cutoff to the initial-count interval
bound needed for prime extraction. -/
theorem exists_fixed_finite_fiber_interval_bound_2048_1120_free {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 1447213072 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k < p ^ 2 ∧
        p ^ 2048 ≤ k ^ 1120 ∧
        k ^ 1120 ≤ 2 ^ 1120 * p ^ 2048 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ :=
    exists_fixed_finite_fiber_rational_energy_cutoff_2048_1120_free hodd hlarge
  have hc : (32 : ℕ) ^ 1120 * 2 ^ 1120 < p :=
    (cutoff_coefficient_lt_explicit_finite_fiber_threshold (a := 1120) (u := 1447213072)
          (by norm_num only)).trans_le
      hlarge
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt
      (by norm_num only : 0 < 1120) (by norm_num only : 2048 < 2 * 1120) hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

/-- At scale 192/105, use precision 280 and loss 140. The count coefficient
fits the explicit prime threshold `P(4,217,312,731)`. Seven units of integer
slack let the energy estimate use the ordinary, unsquared budget. -/
theorem fixed_log_square_finite_fiber_energy_budget_192_105_free {p H k : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 4217312731 ≤ p) (hHp : H < p)
    (htop : (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ)) (hcut : p ^ 192 ≤ k ^ 105)
    (hheight : H ^ 105 ≤ p ^ (2 * 105 - 192)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hcoeffNat := free_finite_fiber_energy_coefficient_lt_prime_threshold_280_140_105
  have hPgt := one_lt_explicit_finite_fiber_threshold 4217312731
  have hpR : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (hPgt.le.trans hlarge)
  have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hPcast : (explicitFiniteFiberPrimeThreshold 4217312731 : ℝ) ≤ p := by exact_mod_cast hlarge
  have hcoeffCast :
    (2 ^ 176 : ℝ) ^ 105 * (freeFiniteFiberCountCoefficient 280 140 : ℝ) ^ (13 * 105) <
      (explicitFiniteFiberPrimeThreshold 4217312731 : ℝ) := by
    exact_mod_cast hcoeffNat
  have hcoeff := hcoeffCast.trans_le hPcast
  have hz :=
    fifty_three_million_le_double_log_of_explicit_fiber_threshold
      (by norm_num only : 76598623 ≤ 4217312731) hlarge
  have hlogLower : (10 : ℝ) ^ 12 ≤ Real.log p :=
    Analysis.twelve_pow_le_of_double_log_ge_fifty_three_million
      (Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)) hz
  have hlogLowerFive : 2000000000 ≤ Real.log p :=
    (by norm_num only : (2000000000 : ℝ) ≤ 10 ^ 12).trans hlogLower
  have hfactor : 1 + Real.log p ≤ (p : ℝ) ^ (1 / 5000 : ℝ) := by
    have hsmall := Analysis.thirty_two_mul_le_exp_div_five_thousand hlogLowerFive
    have hone : 1 + Real.log p ≤ 32 * Real.log p := by nlinarith only [hlogLower]
    rw [Real.rpow_def_of_pos hpPos]
    calc
      1 + Real.log p ≤ 32 * Real.log p := hone
      _ ≤ Real.exp (Real.log p / 5000) := hsmall
      _ = Real.exp (Real.log p * (1 / 5000 : ℝ)) := by
        congr 1; ring
  have hlog : (1 + Real.log p) ^ (2 * 105) ≤ p := by
    have hraised := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log p) hfactor (2 * 105)
    have hconvert : ((p : ℝ) ^ (1 / 5000 : ℝ)) ^ (2 * 105) = (p : ℝ) ^ (21 / 500 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      congr 1
      norm_num only
    have hexp : (21 / 500 : ℝ) ≤ 1 := by norm_num only
    have hpower : Real.rpow p (21 / 500 : ℝ) ≤ Real.rpow p 1 :=
      Real.rpow_le_rpow_of_exponent_le hpR hexp
    exact hraised.trans_eq hconvert |>.trans (hpower.trans_eq (Real.rpow_one p))
  have henergy :
    (2 ^ 176 : ℝ) ^ 105 * (freeFiniteFiberCountCoefficient 280 140 : ℝ) ^ (13 * 105) *
        (1 + Real.log p) ^ (2 * 105) <
      (p : ℝ) ^ 2 := by
    calc
      _ ≤ ((2 ^ 176 : ℝ) ^ 105 * (freeFiniteFiberCountCoefficient 280 140 : ℝ) ^ (13 * 105)) * p :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ < p * p := mul_lt_mul_of_pos_right hcoeff hpPos
      _ = p ^ 2 := by rw [pow_two]
  exact
    separate_count_finite_fiber_energy_budget (a := 105) (h := 140) (c := 280) (b := 192) (g := 2)
      (r := 2) hodd hHp htop (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) hcut hheight
      henergy (by norm_num only)

/-- Every odd prime above `P(4,217,312,731)` has a cutoff at scale 192/105
satisfying the finite-fiber energy budget. Convert the floor-power bound into
a height bound with exponent 18, then apply the explicit energy theorem. -/
theorem exists_fixed_finite_fiber_rational_energy_cutoff_192_105_free {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 4217312731 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 192 ≤ k ^ 105 ∧
        k ^ 105 ≤ 2 ^ 105 * p ^ 192 ∧
        p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ 192 < (p ^ 2) ^ 105 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 (by norm_num only : 192 < 2 * 105)
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 192) hp0)
      (by norm_num only : 0 < 105) with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget (d := 2) (a := 105) (b := 192) hp0 (by norm_num only) hlo
    have hheightExplicit : (p ^ 2 / k) ^ 105 ≤ p ^ 18 := by
      have hheight' := hheight
      rw [show 2 * 105 - 192 = 18 by norm_num only] at hheight'
      exact hheight'
    have hHp := height_lt_base_of_power_bound hp1 (by norm_num only : 18 < 105) hheightExplicit
    have htop :=
      height_le_real_power_of_power (a := 105) (d := 18) (by norm_num only) hp1.le
        (by norm_num only : (18 : ℝ) / 105 ≤ 5 / 28) hheightExplicit
    exact fixed_log_square_finite_fiber_energy_budget_192_105_free hodd hlarge hHp htop hlo hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Every odd prime above `P(4,217,312,731)` has a 192/105 cutoff that also
satisfies the initial-count bound for prime extraction. Transfer the energy
inequality to the smaller Fourier height using count monotonicity. -/
theorem exists_fixed_finite_fiber_interval_bound_192_105_free {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 4217312731 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k < p ^ 2 ∧
        p ^ 192 ≤ k ^ 105 ∧
        k ^ 105 ≤ 2 ^ 105 * p ^ 192 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ :=
    exists_fixed_finite_fiber_rational_energy_cutoff_192_105_free hodd hlarge
  have hc : (32 : ℕ) ^ 105 * 2 ^ 105 < p :=
    (cutoff_coefficient_lt_explicit_finite_fiber_threshold (a := 105) (u := 4217312731)
          (by norm_num only)).trans_le
      hlarge
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt
      (by norm_num only : 0 < 105) (by norm_num only : 192 < 2 * 105) hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

/-- Every odd prime above `P(1411732827)` has a 75/41 cutoff satisfying the
free finite-fiber energy budget. Convert the floor power bound into a height
bound with exponent seven, then apply the one-unit-slack energy theorem. -/
theorem exists_fixed_finite_fiber_rational_energy_cutoff_75_41_free {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 1411732827 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 75 ≤ k ^ 41 ∧
        k ^ 41 ≤ 2 ^ 41 * p ^ 75 ∧
        p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ 75 < (p ^ 2) ^ 41 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 (by norm_num only : 75 < 82)
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 75) hp0)
      (by norm_num only : 0 < 41) with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget (d := 2) (a := 41) (b := 75) hp0 (by norm_num only) hlo
    have hheightExplicit : (p ^ 2 / k) ^ 41 ≤ p ^ 7 := by
      have hheight' := hheight
      rw [show 2 * 41 - 75 = 7 by norm_num only] at hheight'
      exact hheight'
    have hHp := height_lt_base_of_power_bound hp1 (by norm_num only : 7 < 41) hheightExplicit
    have htop :=
      height_le_real_power_of_power (a := 41) (d := 7) (rho := (5 / 28 : ℝ)) (by norm_num only)
        hp1.le (by norm_num only : (7 : ℕ) / 41 ≤ (5 : ℝ) / 28) hheightExplicit
    exact fixed_log_square_finite_fiber_energy_budget_75_41_free hodd hlarge hHp htop hlo hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Every odd prime above `P(1411732827)` has a 75/41 cutoff that also
satisfies the initial-count bound needed for prime extraction. Transfer the
energy inequality to the smaller Fourier height using count monotonicity. -/
theorem exists_fixed_finite_fiber_interval_bound_75_41_free {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 1411732827 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k < p ^ 2 ∧
        p ^ 75 ≤ k ^ 41 ∧ k ^ 41 ≤ 2 ^ 41 * p ^ 75 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ :=
    exists_fixed_finite_fiber_rational_energy_cutoff_75_41_free hodd hlarge
  have hc : (32 : ℕ) ^ 41 * 2 ^ 41 < p :=
    (cutoff_coefficient_lt_explicit_finite_fiber_threshold (a := 41) (u := 1411732827)
          (by norm_num only)).trans_le
      hlarge
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt (by norm_num only : 0 < 41)
      (by norm_num only : 75 < 2 * 41) hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

/-- Every odd prime above `P(1411732827)` has a 150/82 cutoff satisfying the
free finite-fiber energy budget. -/
theorem exists_fixed_finite_fiber_rational_energy_cutoff_150_82_free {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 1411732827 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 150 ≤ k ^ 82 ∧
        k ^ 82 ≤ 2 ^ 82 * p ^ 150 ∧
        p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ 150 < (p ^ 2) ^ 82 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 (by norm_num only)
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 150) hp0) (by decide : 0 < 82) with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget (d := 2) (a := 82) (b := 150) hp0 (by decide) hlo
    have hheightExplicit : (p ^ 2 / k) ^ 82 ≤ p ^ 14 := by
      have hheight' := hheight
      rw [show (2 * 82 - 150 : ℕ) = 14 by norm_num only] at hheight'
      exact hheight'
    have hHp := height_lt_base_of_power_bound hp1 (by norm_num only : 14 < 82) hheightExplicit
    have htop :=
      height_le_real_power_of_power (a := 82) (d := 14) (rho := (5 / 28 : ℝ)) (by norm_num only)
        hp1.le (by norm_num only : (14 : ℕ) / 82 ≤ (5 : ℝ) / 28) hheightExplicit
    exact fixed_log_square_finite_fiber_energy_budget_150_82_free hodd hlarge hHp htop hlo hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Transfer the free 150/82 energy cutoff to the initial-count interval
bound needed for prime extraction. -/
theorem exists_fixed_finite_fiber_interval_bound_150_82_free {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 1411732827 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k < p ^ 2 ∧
        p ^ 150 ≤ k ^ 82 ∧ k ^ 82 ≤ 2 ^ 82 * p ^ 150 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ :=
    exists_fixed_finite_fiber_rational_energy_cutoff_150_82_free hodd hlarge
  have hc : (32 : ℕ) ^ 82 * 2 ^ 82 < p :=
    (cutoff_coefficient_lt_explicit_finite_fiber_threshold (a := 82) (u := 1411732827)
          (by norm_num only)).trans_le
      hlarge
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt (by norm_num only : 0 < 82)
      (by norm_num only : 150 < 2 * 82) hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

/-- Prime supply and the free finite-fiber interval bound produce a prime
with nontrivial Fermat quotient modulo the square of every large odd prime. -/
theorem exists_prime_nontrivial_power_of_free_finite_fiber_interval_150_82 {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 1411732827 ≤ p)
    {A alpha gamma c beta : ℝ} (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ A))
    (hC : 0 < Nat.floor ((p : ℝ) ^ gamma)) (hcL : 2 * c ≤ Real.log (Real.log p))
    (hMp : 2 * (Real.log p) ^ alpha ≤ ((Nat.floor ((Real.log p) ^ A)).primeCounting : ℝ))
    (hgap : c * A * Real.log p + A * Real.log (Real.log p) < (150 / 82 : ℝ) * Real.log p)
    (hlogC : Real.log (Nat.floor ((p : ℝ) ^ gamma)) ≤ beta * Real.log p)
    (henv : ∀ k : ℕ, k ^ 82 ≤ 2 ^ 82 * p ^ 150 → 256 * k ≤ p * Nat.floor ((p : ℝ) ^ gamma))
    (hA : 0 < A) (halpha : 1 < alpha) (hc : 0 < c) (hcb : beta < c * (alpha - 1)) :
    ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ (Real.log p) ^ A ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ :=
    exists_fixed_finite_fiber_interval_bound_150_82_free hodd hlarge
  have hsmooth :=
    smooth_count_at_rational_cutoff_of_log_bounds (a := 82) (t := 150) (A := A) (b := alpha)
      (by decide) (Fact.out : p.Prime).pos hB hC hk hL hA halpha hc hcb hcL hMp
      (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) A)) hgap hlogC (henv k hhi) hlo
  obtain ⟨q, hq, hqB, hpow⟩ := exists_prime_nontrivial_power_of_interval_and_smooth hcount hsmooth
  exact
    ⟨q, hq,
      (Nat.cast_le.mpr (Nat.lt_add_one_iff.mp hqB)).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) A)),
      hpow⟩

/-- Inputs: interval, prime-count, floor, and smooth-scale bounds for an odd
prime above `P(21518759)`.
Claim: A prime `q ≤ (log p)^A` has nontrivial `(p - 1)`-st power modulo `p^2`.
Content: Connect the 30/16 initial-count interval to the prime witness.
Proof: Apply the rational-cutoff smooth-count bound, then extract a prime.
Role: Converts the finite-fiber interval estimate into a Fermat-quotient
prime witness for the later Miller–Rabin reduction. -/
theorem exists_prime_nontrivial_power_of_free_finite_fiber_interval_30_16 {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 21518759 ≤ p)
    {A alpha gamma c beta : ℝ} (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ A))
    (hC : 0 < Nat.floor ((p : ℝ) ^ gamma)) (hcL : 2 * c ≤ Real.log (Real.log p))
    (hMp : 2 * (Real.log p) ^ alpha ≤ ((Nat.floor ((Real.log p) ^ A)).primeCounting : ℝ))
    (hgap : c * A * Real.log p + A * Real.log (Real.log p) < (30 / 16 : ℝ) * Real.log p)
    (hlogC : Real.log (Nat.floor ((p : ℝ) ^ gamma)) ≤ beta * Real.log p)
    (henv : ∀ k : ℕ, k ^ 16 ≤ 2 ^ 16 * p ^ 30 → 256 * k ≤ p * Nat.floor ((p : ℝ) ^ gamma))
    (hA : 0 < A) (halpha : 1 < alpha) (hc : 0 < c) (hcb : beta < c * (alpha - 1)) :
    ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ (Real.log p) ^ A ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ :=
    exists_fixed_finite_fiber_interval_bound_30_16_free hodd hlarge
  have hsmooth :=
    smooth_count_at_rational_cutoff_of_log_bounds (a := 16) (t := 30) (A := A) (b := alpha)
      (by decide) (Fact.out : p.Prime).pos hB hC hk hL hA halpha hc hcb hcL hMp
      (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) A)) hgap hlogC (henv k hhi) hlo
  obtain ⟨q, hq, hqB, hpow⟩ := exists_prime_nontrivial_power_of_interval_and_smooth hcount hsmooth
  exact
    ⟨q, hq,
      (Nat.cast_le.mpr (Nat.lt_add_one_iff.mp hqB)).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) A)),
      hpow⟩

/-- Inputs: prime supply, floor, and smooth-scale bounds above
`P(21518759)`. Claim: a prime `q ≤ (log p)^A` has nontrivial
`(p - 1)`-st power modulo `p^2` at the 28/15 cutoff. -/
theorem exists_prime_nontrivial_power_of_free_finite_fiber_interval_28_15 {p u : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hu : 17431511 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p)
    {A alpha gamma c beta : ℝ} (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ A))
    (hC : 0 < Nat.floor ((p : ℝ) ^ gamma)) (hcL : 2 * c ≤ Real.log (Real.log p))
    (hMp : 2 * (Real.log p) ^ alpha ≤ ((Nat.floor ((Real.log p) ^ A)).primeCounting : ℝ))
    (hgap : c * A * Real.log p + A * Real.log (Real.log p) < (28 / 15 : ℝ) * Real.log p)
    (hlogC : Real.log (Nat.floor ((p : ℝ) ^ gamma)) ≤ beta * Real.log p)
    (henv : ∀ k : ℕ, k ^ 15 ≤ 2 ^ 15 * p ^ 28 → 256 * k ≤ p * Nat.floor ((p : ℝ) ^ gamma))
    (hA : 0 < A) (halpha : 1 < alpha) (hc : 0 < c) (hcb : beta < c * (alpha - 1)) :
    ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ (Real.log p) ^ A ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ :=
    exists_fixed_finite_fiber_interval_bound_28_15_free hodd hu hlarge
  have hsmooth :=
    smooth_count_at_rational_cutoff_of_log_bounds (a := 15) (t := 28) (A := A) (b := alpha)
      (by decide) (Fact.out : p.Prime).pos hB hC hk hL hA halpha hc hcb hcL hMp
      (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) A)) hgap hlogC (henv k hhi) hlo
  obtain ⟨q, hq, hqB, hpow⟩ := exists_prime_nontrivial_power_of_interval_and_smooth hcount hsmooth
  exact
    ⟨q, hq,
      (Nat.cast_le.mpr (Nat.lt_add_one_iff.mp hqB)).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) A)),
      hpow⟩

/-- Every odd prime p≥P(4449271510) has a 19/10 cutoff satisfying the
strict finite-fiber energy budget. -/
theorem exists_fixed_finite_fiber_rational_energy_cutoff_10_19 {p u : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hu : 76598623 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 19 ≤ k ^ 10 ∧
        k ^ 10 ≤ 2 ^ 10 * p ^ 19 ∧
        p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ 19 < (p ^ 2) ^ 10 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 (by decide)
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 19) hp0) (by decide : 0 < 10) with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget (d := 2) (a := 10) (b := 19) hp0 (by decide) hlo
    have hheightExplicit : (p ^ 2 / k) ^ 10 ≤ p ^ 1 := by
      have hheight' := hheight
      rw [show (2 * 10 - 19 : ℕ) = 1 by decide] at hheight'
      exact hheight'
    have hHp := height_lt_base_of_power_bound hp1 (by decide : 1 < 10) hheightExplicit
    have htop :=
      height_le_real_power_of_power (a := 10) (d := 1) (rho := (5 / 28 : ℝ)) (by decide) hp1.le
        (by norm_num only : ((1 : ℕ) : ℝ) / (10 : ℕ) ≤ (5 : ℝ) / 28) hheightExplicit
    exact fixed_log_square_finite_fiber_energy_budget_10_19 hodd hu hlarge hHp htop hlo hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Every odd prime p≥P(4449271510) has a 19/10 cutoff with
p J_p(k)<256k. Transfer the energy estimate by monotonicity. -/
theorem exists_fixed_finite_fiber_interval_bound_10_19 {p : ℕ} [Fact p.Prime] {u : ℕ} (hodd : Odd p)
    (hu : 76598623 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k < p ^ 2 ∧
        p ^ 19 ≤ k ^ 10 ∧ k ^ 10 ≤ 2 ^ 10 * p ^ 19 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ :=
    exists_fixed_finite_fiber_rational_energy_cutoff_10_19 hodd hu hlarge
  have hc : (32 : ℕ) ^ 10 * 2 ^ 10 < p :=
    (cutoff_coefficient_lt_explicit_finite_fiber_threshold (a := 10) (u := u)
          (Nat.lt_of_lt_of_le (by norm_num only : 60 < 76598623) hu)).trans_le
      hlarge
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt (by decide : 0 < 10)
      (by decide : 19 < 2 * 10) hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

/-- Every odd prime above `P(21518759)` has a 19/10 cutoff satisfying the
free finite-fiber energy budget. -/
theorem exists_fixed_finite_fiber_rational_energy_cutoff_10_19_free {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 21518759 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 19 ≤ k ^ 10 ∧
        k ^ 10 ≤ 2 ^ 10 * p ^ 19 ∧
        p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ 19 < (p ^ 2) ^ 10 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 (by decide)
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 19) hp0) (by decide : 0 < 10) with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget (d := 2) (a := 10) (b := 19) hp0 (by decide) hlo
    have hheightExplicit : (p ^ 2 / k) ^ 10 ≤ p ^ 1 := by
      have hheight' := hheight
      rw [show (2 * 10 - 19 : ℕ) = 1 by norm_num only] at hheight'
      exact hheight'
    have hHp := height_lt_base_of_power_bound hp1 (by norm_num only : 1 < 10) hheightExplicit
    have htop :=
      height_le_real_power_of_power (a := 10) (d := 1) (rho := (5 / 28 : ℝ)) (by decide) hp1.le
        (by norm_num only : (1 : ℕ) / 10 ≤ (5 : ℝ) / 28) hheightExplicit
    exact fixed_log_square_finite_fiber_energy_budget_10_19_free hodd hlarge hHp htop hlo hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Transfer the free 19/10 energy cutoff to the initial-count interval bound
needed for prime extraction. -/
theorem exists_fixed_finite_fiber_interval_bound_10_19_free {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 21518759 ≤ p) :
    ∃ k : ℕ,
      0 < k ∧
        k < p ^ 2 ∧
        p ^ 19 ≤ k ^ 10 ∧ k ^ 10 ≤ 2 ^ 10 * p ^ 19 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ :=
    exists_fixed_finite_fiber_rational_energy_cutoff_10_19_free hodd hlarge
  have hc : (32 : ℕ) ^ 10 * 2 ^ 10 < p :=
    (cutoff_coefficient_lt_explicit_finite_fiber_threshold (a := 10) (u := 21518759)
          (by norm_num only)).trans_le
      hlarge
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt (by decide : 0 < 10)
      (by decide : 19 < 2 * 10) hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

/-- Prime supply and the free 19/10 finite-fiber interval bound produce a
prime with nontrivial Fermat quotient modulo the square of every large odd prime. -/
theorem exists_prime_nontrivial_power_of_free_finite_fiber_interval_10_19 {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 21518759 ≤ p)
    {A alpha gamma c beta : ℝ} (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ A))
    (hC : 0 < Nat.floor ((p : ℝ) ^ gamma)) (hcL : 2 * c ≤ Real.log (Real.log p))
    (hMp : 2 * (Real.log p) ^ alpha ≤ ((Nat.floor ((Real.log p) ^ A)).primeCounting : ℝ))
    (hgap : c * A * Real.log p + A * Real.log (Real.log p) < (19 / 10 : ℝ) * Real.log p)
    (hlogC : Real.log (Nat.floor ((p : ℝ) ^ gamma)) ≤ beta * Real.log p)
    (henv : ∀ k : ℕ, k ^ 10 ≤ 2 ^ 10 * p ^ 19 → 256 * k ≤ p * Nat.floor ((p : ℝ) ^ gamma))
    (hA : 0 < A) (halpha : 1 < alpha) (hc : 0 < c) (hcb : beta < c * (alpha - 1)) :
    ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ (Real.log p) ^ A ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ :=
    exists_fixed_finite_fiber_interval_bound_10_19_free hodd hlarge
  have hsmooth :=
    smooth_count_at_rational_cutoff_of_log_bounds (a := 10) (t := 19) (A := A) (b := alpha)
      (by decide) (Fact.out : p.Prime).pos hB hC hk hL hA halpha hc hcb hcL hMp
      (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) A)) hgap hlogC (henv k hhi) hlo
  obtain ⟨q, hq, hqB, hpow⟩ := exists_prime_nontrivial_power_of_interval_and_smooth hcount hsmooth
  exact
    ⟨q, hq,
      (Nat.cast_le.mpr (Nat.lt_add_one_iff.mp hqB)).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) A)),
      hpow⟩

end PseudoPrime.NumberTheory.Heilbronn
