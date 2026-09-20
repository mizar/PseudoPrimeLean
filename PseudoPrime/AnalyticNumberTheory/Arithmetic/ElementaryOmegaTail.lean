/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterModulus

/-!
# The `ElementaryOmegaStatement` tail (`m := ω(n) ≥ 163`)

This file proves the inequality in `ElementaryOmegaStatement`
for every odd `n` whose number of distinct prime factors `m := n.primeFactors.card` is at least
`163`, using a one-variable calculus
argument bounding the target ratio via `PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryF`,
a function of the *real* variable `t`
(reindexing `m`) that turns out to be monotone decreasing for `t ≥ 11`, plus a single numeric
evaluation `PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryF 163 ≤ 7/5`
bounding the whole tail.

The remaining case `1 ≤ m < 163`, for odd `n ≥ 750`, uses finite checks at primorial anchors
(the crude `2^m·m!` bound used here is not tight enough there); it is isolated as
`ElementaryOmegaFiniteStatement` and proved in `ElementaryOmegaFiniteCertificates`.

## Outline

For `n` odd with `m := n.primeFactors.card`, `n ≥ 2^m · m!` by
`pow_mul_factorial_le_of_card_primeFactors`. Write
`a(t) := log(2t) - 1`, `u(t) := t · a(t)`.  Stirling's inequality turns the primorial bound into
`log n ≥ u(m)`, hence `log(4n) ≥ u(m)` too.  Since `z ↦ log z / z` is antitone for `z ≥ e`
(mathlib's `Real.log_div_self_antitoneOn`), `loglog(4n)/log(4n) ≤ log(u(m))/u(m)`, so

```
  ω(4n) · loglog(4n)/log(4n)
≤ (m+1) · log(u(m))/u(m)
= PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryF m
```

where `PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryF(t) := (1 + 1/t) · (log(u(t))/a(t))`.
A derivative computation shows `h(t) := log(u(t))/a(t)` satisfies
`h'(t) = log(2/a(t)) / (t · a(t)²)`, which is `≤ 0` once `a(t) ≥ 2`
(i.e. `t ≥ e³/2`, in particular `t ≥ 11`); combined with `(1 + 1/t)` also being
antitone and both factors nonnegative there,
`PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryF` is antitone on `[11, ∞)`.
So for `m ≥ 163`,
`PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryF m`
` ≤ PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryF 163 ≤ 7/5`
(the one numeric certificate needed), giving the target.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- `a(t) := log(2t) - 1`. -/
noncomputable def elementaryA (t : ℝ) : ℝ :=
  Real.log (2 * t) - 1

/-- `u(t) := t · a(t)`, the crude Stirling-based lower bound on `log` of an odd number with `t`
distinct prime factors. -/
noncomputable def elementaryU (t : ℝ) : ℝ :=
  t * elementaryA t

/-- `h(t) := log(u(t)) / a(t)`. -/
noncomputable def elementaryH (t : ℝ) : ℝ :=
  Real.log (elementaryU t) / elementaryA t

/-- `F(t) := (1 + 1/t) · h(t)`, the target ratio bound as a function of the real reindexing of
`m := ω(n) = ω(4n) - 1` for odd `n`. -/
noncomputable def elementaryF (t : ℝ) : ℝ :=
  (1 + 1 / t) * elementaryH t

theorem hasDerivAt_elementaryA {t : ℝ} (ht : 0 < t) : HasDerivAt elementaryA (1 / t) t := by
  have hlin : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul 2
  have hne : (2 * t : ℝ) ≠ 0 := by positivity
  have hlog := hlin.log hne
  have hsub : HasDerivAt (fun s : ℝ => Real.log (2 * s) - 1) (2 / (2 * t)) t := hlog.sub_const 1
  have heq : (2 : ℝ) / (2 * t) = 1 / t := by field_simp
  rwa [heq] at hsub

theorem hasDerivAt_elementaryU {t : ℝ} (ht : 0 < t) :
    HasDerivAt elementaryU (elementaryA t + 1) t := by
  have hid : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
  have ha := hasDerivAt_elementaryA ht
  have hmul := hid.mul ha
  have heq : 1 * elementaryA t + t * (1 / t) = elementaryA t + 1 := by field_simp
  rwa [heq] at hmul

/-- `a(t) ≥ 2` for `t ≥ 11`, using `e³ < 22 ≤ 2t`. -/
theorem elementaryA_ge_two {t : ℝ} (ht : 11 ≤ t) : (2 : ℝ) ≤ elementaryA t := by
  have ht0 : (0 : ℝ) < t := by linarith only [ht]
  unfold elementaryA
  have h22 : (22 : ℝ) ≤ 2 * t := by linarith only [ht]
  have he3 : Real.exp 3 < 22 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num only, Real.exp_add, Real.exp_add]
    rw [h3]
    have hep : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    nlinarith only [h1, hep]
  have hlog22 : (3 : ℝ) < Real.log 22 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num only : (0 : ℝ) < 22)]
    exact he3
  have := Real.log_le_log (by norm_num only : (0 : ℝ) < 22) h22
  have hlog3 : (3 : ℝ) < Real.log (2 * t) := hlog22.trans_le this
  exact (show (2 : ℝ) < Real.log (2 * t) - 1 by linarith only [hlog3]).le

theorem elementaryA_pos {t : ℝ} (ht : 11 ≤ t) : (0 : ℝ) < elementaryA t := by
  linarith only [elementaryA_ge_two ht]

/-- `h'(t) = log(2/a(t)) / (t·a(t)²) ≤ 0` for `t ≥ 11`. -/
theorem hasDerivAt_elementaryH {t : ℝ} (ht : 11 ≤ t) : ∃ d, HasDerivAt elementaryH d t ∧ d ≤ 0 := by
  have ht0 : (0 : ℝ) < t := by linarith only [ht]
  have ha := hasDerivAt_elementaryA ht0
  have hu := hasDerivAt_elementaryU ht0
  have hapos := elementaryA_pos ht
  have huval : elementaryU t = t * elementaryA t := rfl
  have hupos : (0 : ℝ) < elementaryU t := by
    rw [huval]; positivity
  have hlogu := hu.log hupos.ne'
  have hdiv := hlogu.div ha hapos.ne'
  refine ⟨_, hdiv, ?_⟩
  set L : ℝ := Real.log (elementaryU t) with hLdef
  have hLeq : L = Real.log t + Real.log (elementaryA t) := by
    rw [hLdef, huval, Real.log_mul ht0.ne' hapos.ne']
  have haeq : elementaryA t + 1 = Real.log 2 + Real.log t := by
    unfold elementaryA
    rw [Real.log_mul (by norm_num only) ht0.ne']
    ring
  have hnum_eq :
    ((elementaryA t + 1) / elementaryU t * elementaryA t - L * (1 / t)) / elementaryA t ^ 2 =
      Real.log (2 / elementaryA t) / (t * elementaryA t ^ 2) := by
    rw [huval, hLeq, haeq, Real.log_div (by norm_num only) hapos.ne']
    field_simp
    ring
  rw [hnum_eq]
  have hloghalf : Real.log (2 / elementaryA t) ≤ 0 := by
    rw [Real.log_nonpos_iff (by positivity), div_le_one hapos]
    exact elementaryA_ge_two ht
  have hden : (0 : ℝ) ≤ t * elementaryA t ^ 2 := by positivity
  exact div_nonpos_iff.mpr (Or.inr ⟨hloghalf, hden⟩)

theorem elementaryH_antitoneOn : AntitoneOn elementaryH (Set.Ici (11 : ℝ)) := by
  have hD : Convex ℝ (Set.Ici (11 : ℝ)) := convex_Ici _
  have hcont : ContinuousOn elementaryH (Set.Ici (11 : ℝ)) := fun t ht =>
    (hasDerivAt_elementaryH (Set.mem_Ici.mp ht)).choose_spec.1.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ elementaryH (interior (Set.Ici (11 : ℝ))) := by
    rw [interior_Ici]
    intro t ht
    exact
      (hasDerivAt_elementaryH
            (le_of_lt (Set.mem_Ioi.mp ht))).choose_spec.1.differentiableAt |>.differentiableWithinAt
  apply antitoneOn_of_deriv_nonpos hD hcont hdiff
  intro t ht
  rw [interior_Ici, Set.mem_Ioi] at ht
  obtain ⟨d, hd, hd_nonpos⟩ := hasDerivAt_elementaryH ht.le
  rwa [hd.deriv]

theorem elementaryU_ge {t : ℝ} (ht : 11 ≤ t) : (22 : ℝ) ≤ elementaryU t := by
  unfold elementaryU
  have ha2 := elementaryA_ge_two ht
  nlinarith only [mul_le_mul ht ha2 (by norm_num only : (0 : ℝ) ≤ 2)
      (by linarith only [ht] : (0 : ℝ) ≤ t)]

theorem elementaryH_nonneg {t : ℝ} (ht : 11 ≤ t) : 0 ≤ elementaryH t := by
  unfold elementaryH
  apply div_nonneg
  · exact Real.log_nonneg (by linarith only [elementaryU_ge ht])
  · linarith only [elementaryA_pos ht]

/-- `F` is antitone on `[11, ∞)`: a product of the two antitone nonnegative factors
`1 + 1/t` and `h(t)`. -/
theorem elementaryF_antitoneOn : AntitoneOn elementaryF (Set.Ici (11 : ℝ)) := by
  intro t1 h1 t2 h2 h12
  unfold elementaryF
  rw [Set.mem_Ici] at h1 h2
  have hh1 : elementaryH t2 ≤ elementaryH t1 := elementaryH_antitoneOn h1 h2 h12
  have hh2nn : 0 ≤ elementaryH t2 := elementaryH_nonneg h2
  have hc1 : (1 + 1 / t2 : ℝ) ≤ 1 + 1 / t1 := by
    have : (1 : ℝ) / t2 ≤ 1 / t1 := one_div_le_one_div_of_le (by linarith only [h1]) h12
    linarith only [this]
  have hc1pos : (0 : ℝ) ≤ 1 + 1 / t1 := by positivity
  calc
    (1 + 1 / t2) * elementaryH t2 ≤ (1 + 1 / t1) * elementaryH t2 :=
      mul_le_mul_of_nonneg_right hc1 hh2nn
    _ ≤ (1 + 1 / t1) * elementaryH t1 := mul_le_mul_of_nonneg_left hh1 hc1pos

-- The single numeric certificate closing the tail: `F(163) ≤ 7/5`.
set_option exponentiation.threshold 2000 in
theorem elementaryF_163_le : elementaryF 163 ≤ (7 / 5 : ℝ) := by
  have hx1 : |(1 - (326 : ℝ) / 2 ^ 9)| < 1 := by norm_num only [abs_of_nonneg]
  obtain ⟨hlo1, hhi1⟩ := Analysis.log_bounds_of_taylor (N := 326) (by norm_num only) 9 30 rfl hx1
  have hlog326_lo : (5786897379 / 1000000000 : ℝ) ≤ Real.log 326 := by
    nlinarith only [hlo1, Real.log_two_gt_d9]
  have hlog326_hi : Real.log 326 ≤ (723362173 / 125000000 : ℝ) := by
    nlinarith only [hhi1, Real.log_two_lt_d9]
  have hA163eq : elementaryA 163 = Real.log 326 - 1 := by
    unfold elementaryA; norm_num only
  have hA_lo : (4786897379 / 1000000000 : ℝ) ≤ elementaryA 163 := by
    rw [hA163eq]; linarith only [hlog326_lo]
  have hA_hi : elementaryA 163 ≤ (598362173 / 125000000 : ℝ) := by
    rw [hA163eq]; linarith only [hlog326_hi]
  have hA_pos : (0 : ℝ) < elementaryA 163 := by linarith only [hA_lo]
  have hU163eq : elementaryU 163 = 163 * elementaryA 163 := rfl
  have hU_hi : elementaryU 163 ≤ (780264273592 / 1000000000 : ℝ) := by
    rw [hU163eq]; nlinarith only [hA_hi]
  have hU_pos : (0 : ℝ) < elementaryU 163 := by
    rw [hU163eq]; nlinarith only [hA_lo]
  have hx2 : |(1 - (780264273592 / 1000000000 : ℝ) / 2 ^ 10)| < 1 := by norm_num only
  obtain ⟨_, hhi2⟩ :=
    Analysis.log_bounds_of_taylor_real (N := (780264273592 / 1000000000 : ℝ)) (by norm_num only) 10
      30 rfl hx2
  have hlogU_hi : Real.log (elementaryU 163) ≤ (6659632677 / 1000000000 : ℝ) := by
    have hmono := Real.log_le_log hU_pos hU_hi
    norm_num only [Finset.sum_range_succ] at hhi2
    nlinarith only [hhi2, Real.log_two_lt_d9, hmono]
  have hHeq : elementaryH 163 = Real.log (elementaryU 163) / elementaryA 163 := rfl
  have hgoal_eq : elementaryF 163 = (164 / 163 * Real.log (elementaryU 163)) / elementaryA 163 := by
    unfold elementaryF; rw [hHeq]; ring
  rw [hgoal_eq, div_le_iff₀ hA_pos]
  nlinarith only [hlogU_hi, hA_lo]

/-- Stirling's inequality (log form) gives `log(m!) ≥ m·log m - m` for `m ≥ 1`, dropping the
nonnegative tail `(log m + log(2π))/2` (nonnegative since `2πm ≥ 1`). -/
theorem log_factorial_ge {m : ℕ} (hm1 : 1 ≤ m) :
    (m : ℝ) * Real.log m - m ≤ Real.log (Nat.factorial m) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hstirling := Stirling.le_log_factorial_stirling (n := m) (by omega)
  have htail : (0 : ℝ) ≤ Real.log m / 2 + Real.log (2 * Real.pi) / 2 := by
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hpi3 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    have h2 : (1 : ℝ) ≤ 2 * Real.pi * m := by
      nlinarith only [mul_le_mul hpi3 hm1' (by norm_num only : (0 : ℝ) ≤ 1)
          (by linarith : (0 : ℝ) ≤ Real.pi)]
    have h3 : (0 : ℝ) ≤ Real.log (2 * Real.pi * m) := Real.log_nonneg h2
    have h4 : Real.log (2 * Real.pi * m) = Real.log (2 * Real.pi) + Real.log m := by
      rw [Real.log_mul (by positivity) hmpos.ne']
    linarith only [h3, h4]
  linarith only [hstirling, htail]

/-- `log n ≥ u(m)` for any natural `n ≥ 2^m·m!` (`m ≥ 1`),
combining `log(2^m·m!) = m·log2 + log(m!)`
with `PseudoPrime.AnalyticNumberTheory.Arithmetic.log_factorial_ge`. -/
theorem log_ge_elementaryU_of_pow_mul_factorial_le {n m : ℕ} (hm1 : 1 ≤ m)
    (hn : 2 ^ m * Nat.factorial m ≤ n) : elementaryU (m : ℝ) ≤ Real.log n := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < 2 ^ m * Nat.factorial m := by positivity
    exact_mod_cast this.trans_le hn
  have hstep1 : Real.log (2 ^ m * Nat.factorial m : ℝ) ≤ Real.log n := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hn
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hsplit :
    Real.log ((2 : ℝ) ^ m * Nat.factorial m) =
      (m : ℝ) * Real.log 2 + Real.log (Nat.factorial m) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hfact := log_factorial_ge hm1
  have hUeq : elementaryU (m : ℝ) = (m : ℝ) * (Real.log 2 + Real.log m - 1) := by
    unfold elementaryU elementaryA
    rw [Real.log_mul (by norm_num only) hmpos.ne']
  rw [hUeq]
  nlinarith only [hstep1, hsplit, hfact]

theorem distinctPrimeFactorCount_eq_primeFactors_card (n : ℕ) :
    distinctPrimeFactorCount n = n.primeFactors.card := by
  rw [distinctPrimeFactorCount, ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    Nat.toFinset_factors]

/--
**The `PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement` tail**:
unconditional for every odd `n` with `m := n.primeFactors.card ≥ 163`.
-/
theorem elementaryOmegaStatement_tail {n : ℕ} (hn : Odd n) (hm163 : 163 ≤ n.primeFactors.card) :
    ((NumberTheory.characterModulus n).primeFactors.card : ℝ) ≤
      elementaryOmegaConstant * Real.log (NumberTheory.characterModulus n) /
        Real.log (Real.log (NumberTheory.characterModulus n)) := by
  set m : ℕ := n.primeFactors.card with hm_def
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact absurd (h0 ▸ hn) (by decide)
    · exact h0
  have hm1 : 1 ≤ m := by omega
  have hnpowfact : 2 ^ m * Nat.factorial m ≤ n := pow_mul_factorial_le_of_card_primeFactors hn
  have hlogn_ge : elementaryU (m : ℝ) ≤ Real.log n :=
    log_ge_elementaryU_of_pow_mul_factorial_le hm1 hnpowfact
  have hcastq : (NumberTheory.characterModulus n : ℝ) = 4 * n := by
    unfold NumberTheory.characterModulus; push_cast; ring
  have hqpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hlogq_ge : elementaryU (m : ℝ) ≤ Real.log (NumberTheory.characterModulus n) := by
    rw [hcastq]
    have hsplit4 : Real.log ((4 : ℝ) * n) = Real.log 4 + Real.log n :=
      Real.log_mul (by norm_num only) hqpos.ne'
    rw [hsplit4]
    linarith only [hlogn_ge, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num only)]
  have hm163R : (163 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm163
  have hm11R : (11 : ℝ) ≤ (m : ℝ) := by linarith only [hm163R]
  have hU_ge_e : Real.exp 1 ≤ elementaryU (m : ℝ) := by
    have h22 := elementaryU_ge (t := (m : ℝ)) hm11R
    have hexp1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith only [h22, hexp1]
  have hsub :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.mpr hU_ge_e)
      (Set.mem_Ici.mpr (hU_ge_e.trans hlogq_ge)) hlogq_ge
  have hFmono : elementaryF (m : ℝ) ≤ elementaryF 163 :=
    elementaryF_antitoneOn (Set.mem_Ici.mpr (by norm_num only : (11 : ℝ) ≤ 163))
      (Set.mem_Ici.mpr hm11R) hm163R
  have hF163 := elementaryF_163_le
  have hFeq :
    elementaryF (m : ℝ) =
      ((m : ℝ) + 1) * (Real.log (elementaryU (m : ℝ)) / elementaryU (m : ℝ)) := by
    have hApos := elementaryA_pos hm11R
    have hUeq2 : elementaryU (m : ℝ) = (m : ℝ) * elementaryA (m : ℝ) := rfl
    unfold elementaryF elementaryH
    rw [hUeq2]
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith only [hm11R]
    field_simp
  have hlogq_pos : (0 : ℝ) < Real.log (NumberTheory.characterModulus n) := by
    linarith only [hU_ge_e, hlogq_ge, Real.exp_pos 1]
  have hloglogq_ge1 : (1 : ℝ) ≤ Real.log (Real.log (NumberTheory.characterModulus n)) := by
    have hge : Real.exp 1 ≤ Real.log (NumberTheory.characterModulus n) := hU_ge_e.trans hlogq_ge
    have hh := Real.log_le_log (Real.exp_pos 1) hge
    rwa [Real.log_exp] at hh
  have hloglogq_pos : (0 : ℝ) < Real.log (Real.log (NumberTheory.characterModulus n)) := by linarith
  have hmR_nonneg : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have hstep1 :
    ((m : ℝ) + 1) *
        (Real.log (Real.log (NumberTheory.characterModulus n)) /
          Real.log (NumberTheory.characterModulus n)) ≤
      ((m : ℝ) + 1) * (Real.log (elementaryU (m : ℝ)) / elementaryU (m : ℝ)) :=
    mul_le_mul_of_nonneg_left hsub hmR_nonneg
  rw [← hFeq] at hstep1
  have hchain :
    ((m : ℝ) + 1) *
        (Real.log (Real.log (NumberTheory.characterModulus n)) /
          Real.log (NumberTheory.characterModulus n)) ≤
      (7 / 5 : ℝ) := by
    linarith only [hstep1, hFmono, hF163]
  have homega_eq : (NumberTheory.characterModulus n).primeFactors.card = m + 1 := by
    have h1 := distinctPrimeFactorCount_characterModulus hn
    rwa [distinctPrimeFactorCount_eq_primeFactors_card,
      distinctPrimeFactorCount_eq_primeFactors_card, ← hm_def] at h1
  rw [homega_eq]
  unfold elementaryOmegaConstant
  push_cast
  rw [le_div_iff₀ hloglogq_pos]
  have hchain2 :
    ((m : ℝ) + 1) * Real.log (Real.log (NumberTheory.characterModulus n)) ≤
      (7 / 5 : ℝ) * Real.log (NumberTheory.characterModulus n) := by
    have hmul := mul_le_mul_of_nonneg_right hchain hlogq_pos.le
    have heq :
      ((m : ℝ) + 1) *
          (Real.log (Real.log (NumberTheory.characterModulus n)) /
            Real.log (NumberTheory.characterModulus n)) *
          Real.log (NumberTheory.characterModulus n) =
        ((m : ℝ) + 1) * Real.log (Real.log (NumberTheory.characterModulus n)) := by
      field_simp
    rwa [heq] at hmul
  linarith only [hchain2]

/-- The finite part of the factor-count bound: odd `n ≥ 750` with `ω(n) < 163` satisfies
`ω(4n) ≤ (7/5) * log(4n) / loglog(4n)`. These hypotheses imply `1 ≤ ω(n)`.
`elementaryOmegaFiniteStatement_of_certificates` reduces it to primorial-anchor certificates,
which are supplied in `ElementaryOmegaFiniteCertificates`. -/
def ElementaryOmegaFiniteStatement : Prop :=
  ∀ n : ℕ,
    Odd n →
      750 ≤ n →
      n.primeFactors.card < 163 →
      ((NumberTheory.characterModulus n).primeFactors.card : ℝ) ≤
        elementaryOmegaConstant * Real.log (NumberTheory.characterModulus n) /
          Real.log (Real.log (NumberTheory.characterModulus n))

/-- `PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement`
reduces to the finite case: the tail (`m ≥ 163`) is now
unconditional. -/
theorem elementaryOmegaStatement_of_finite (hfin : ElementaryOmegaFiniteStatement) :
    ElementaryOmegaStatement := by
  intro n hn hn750
  by_cases hm : 163 ≤ n.primeFactors.card
  · exact elementaryOmegaStatement_tail hn hm
  · exact hfin n hn hn750 (by omega)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
