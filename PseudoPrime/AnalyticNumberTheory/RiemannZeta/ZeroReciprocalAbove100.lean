/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountAbelBudget
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCriticalEnumeration
import PseudoPrime.Analysis.LogLinearIntegral
import PseudoPrime.Analysis.LogBudgetIntegral
import PseudoPrime.Analysis.RationalReciprocalSum
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocal100Numerics

/-! # Reciprocal zero sum above height 100 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and a certified total zero count of 58 at height 100, the
reciprocal sum above 100 is bounded by the endpoint and integral terms from
the RH zero-count budget. The negative lower endpoint is retained for the
explicit middle-range estimate. -/
theorem reciprocal_above_100_le_of_count (hRH : RiemannHypothesis) (h100 : zeroCount 100 = 58)
    {T : ℝ} (hT : 100 ≤ T) :
    zeroReciprocalSum T - zeroReciprocalSum 100 ≤
      ((1 / Real.pi) * T * (Real.log T - Real.log (2 * Real.pi) - 1) + 7 / 4) / T - 58 / 100 +
        (∫ t in (100 : ℝ)..T,
          ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4) / t ^ 2) +
        ((3 / 4 : ℝ) * Real.log T + 16 / 5 + (2 / 5 : ℝ) / T) / T +
        (∫ t in (100 : ℝ)..T, ((3 / 4 : ℝ) * Real.log t + 16 / 5 + (2 / 5 : ℝ) / t) / t ^ 2) := by
  have hbase : 2 * Real.pi * Real.exp 1 ≤ (100 : ℝ) := by
    have hp :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hp]
  have hM :
    ContinuousOn (fun t : ℝ ↦ (1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)
      (Set.Icc 100 T) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith only [ht.1]
    exact
      (((continuousAt_const.mul continuousAt_id).mul
              (((Real.continuousAt_log ht0).sub continuousAt_const).sub continuousAt_const)).add
          continuousAt_const).continuousWithinAt
  have hE :
    ContinuousOn (fun t : ℝ ↦ (3 / 4 : ℝ) * Real.log t + 16 / 5 + (2 / 5 : ℝ) / t)
      (Set.Icc 100 T) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith only [ht.1]
    exact
      (((continuousAt_const.mul (Real.continuousAt_log ht0)).add continuousAt_const).add
          (continuousAt_const.div continuousAt_id ht0)).continuousWithinAt
  have hQ :
    ∀ t ∈ Set.Icc (100 : ℝ) T,
      |zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)| ≤
        (3 / 4 : ℝ) * Real.log t + 16 / 5 + (2 / 5 : ℝ) / t := by
    intro t ht
    have h := zero_count_budget_of_RH hRH (hbase.trans ht.1)
    convert h using 1
    ring
  have h := reciprocal_interval_le_of_error (by norm_num only : (1 : ℝ) < 100) hT hM hE hQ
  rw [h100] at h
  exact h

/-- Under RH and the height-100 zero count, evaluate the logarithmic main
term and error integrals in the reciprocal-sum bound. The explicit negative
endpoint term remains available for the middle-range scalar estimate. -/
theorem reciprocal_above_100_explicit (hRH : RiemannHypothesis) (h100 : zeroCount 100 = 58) {T : ℝ}
    (hT : 100 ≤ T) :
    zeroReciprocalSum T - zeroReciprocalSum 100 ≤
      (1 / Real.pi) / 2 *
                  ((Real.log T - Real.log (2 * Real.pi)) ^ 2 -
                    (Real.log 100 - Real.log (2 * Real.pi)) ^ 2) +
                (1 / Real.pi) * (Real.log 100 - Real.log (2 * Real.pi) - 1) +
                (7 / 4 : ℝ) / 100 -
              58 / 100 +
            ((3 / 4 : ℝ) * (Real.log 100 + 1) + 16 / 5) / 100 +
            (2 / 5 : ℝ) / (2 * 100 ^ 2) -
          (3 / 4 : ℝ) / T +
        (2 / 5 : ℝ) / (2 * T ^ 2) := by
  have hm :=
    Analysis.log_linear_div_sq_boundary (a := 100) (b := T) (k := 1 / Real.pi) (c :=
      Real.log (2 * Real.pi)) (d := 7 / 4) (by norm_num only) hT
  have he :=
    Analysis.log_budget_div_sq_boundary (a := 100) (b := T) (α := 3 / 4) (β := 16 / 5) (γ := 2 / 5)
      (by norm_num only) hT
  have h := reciprocal_above_100_le_of_count hRH h100 hT
  linarith only [h, hm, he]

/-- Under RH and a certified zero count of 58 at height 100, the reciprocal
zero sum above that height has the logarithmic upper bound with the negative
`-143/125` entrance correction. The explicit upper-endpoint correction is
nonpositive for `T ≥ 100`. -/
theorem reciprocal_above_100_of_count (hRH : RiemannHypothesis) (h100 : zeroCount 100 = 58) {T : ℝ}
    (hT : 100 ≤ T) :
    zeroReciprocalSum T - zeroReciprocalSum 100 ≤
      (Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) - 143 / 125 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num only) Real.pi_pos)
  have ht1 : (1 / 5 : ℝ) / T ≤ 3 / 4 := by
    apply (div_le_iff₀ hT0).2
    linarith only [hT]
  have ht2 := div_le_div_of_nonneg_right ht1 hT0.le
  have ht : -(3 / 4 : ℝ) / T + (2 / 5 : ℝ) / (2 * T ^ 2) ≤ 0 := by
    have he : (1 / 5 : ℝ) / T / T = (2 / 5 : ℝ) / (2 * T ^ 2) := by ring
    rw [he] at ht2
    have hsub := sub_nonpos.mpr ht2
    convert hsub using 1
    ring
  have h := reciprocal_above_100_explicit hRH h100 hT
  have hK := reciprocal_100_entrance_le
  rw [Real.log_div hT0.ne' hp]
  norm_num only at h hK ht ⊢
  simp only [div_eq_mul_inv, mul_inv_rev] at h hK ht ⊢
  nlinarith only [h, hK, ht]

/-- Under RH, a height-100 zero count of 58 and a reciprocal head bound of
`237/200` imply the full reciprocal zero-sum bound with correction `41/1000`.
This combines the head estimate with the certified negative entrance term. -/
theorem reciprocal_sum_of_head100 (hRH : RiemannHypothesis) (h100 : zeroCount 100 = 58)
    (hhead : zeroReciprocalSum 100 ≤ 237 / 200) {T : ℝ} (hT : 100 ≤ T) :
    zeroReciprocalSum T ≤ (Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 41 / 1000 := by
  have h := reciprocal_above_100_of_count hRH h100 hT
  linarith only [h, hhead]

/-- Under RH, a complete paired head of 29 ordinates and a certified sum of
positive rational lower brackets imply the full reciprocal-sum estimate.
The bracket function is a parameter, so this interface does not expose a
particular numerical table. -/
theorem reciprocal_sum_of_brackets100 (hRH : RiemannHypothesis) (h100 : zeroCount 100 = 58)
    (a : Fin 29 → ℚ) (g : Fin 29 → ℝ) (ha : ∀ i, 0 < a i) (hg : ∀ i, (a i : ℝ) ≤ g i)
    (heq : zeroReciprocalSum 100 = ∑ i, (2 : ℝ) / g i) (hc : (∑ i, (2 : ℚ) / a i) < 237 / 200)
    {T : ℝ} (hT : 100 ≤ T) :
    zeroReciprocalSum T ≤ (Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 41 / 1000 := by
  have hh : zeroReciprocalSum 100 ≤ 237 / 200 := by
    rw [heq]
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Analysis.reciprocal_sum_lt_of_lower a g ha hg hc).le
  exact reciprocal_sum_of_head100 hRH h100 hh hT

/-- Under RH, an injective complete enumeration of the 29 positive-height
zeros through 100, together with multiplicity-one and rational lower-bracket
certificates, gives the reciprocal zero-sum bound above 100. The zero count
and head-sum identities are derived from the same enumeration. -/
theorem reciprocal_sum_of_enumeration100 (hRH : RiemannHypothesis) (z : Fin 29 → ℂ) (g : Fin 29 → ℝ)
    (a : Fin 29 → ℚ) (hinj : Function.Injective z)
    (hledger : (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) = Finset.univ.image z)
    (hm : ∀ i, riemannZetaZeroMultiplicity (z i) = 1) (him : ∀ i, (z i).im = g i)
    (ha : ∀ i, 0 < a i) (hg : ∀ i, (a i : ℝ) ≤ g i) (hc : (∑ i, (2 : ℚ) / a i) < 237 / 200) {T : ℝ}
    (hT : 100 ≤ T) :
    zeroReciprocalSum T ≤ (Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 41 / 1000 := by
  have h100 : zeroCount 100 = 58 := by
    have h :=
      zeroCount_of_simple_enumeration hRH (by norm_num only : (0 : ℝ) ≤ 100) z hinj hledger hm
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have heq :=
    zeroReciprocal_of_simple_enumeration hRH (by norm_num only : (0 : ℝ) ≤ 100) z g hinj hledger hm
      him
  exact reciprocal_sum_of_brackets100 hRH h100 a g ha hg heq hc hT

/-- Under RH, an ordered complete enumeration of the 29 simple positive
critical-line zeros through 100 and certified positive rational lower bounds
imply the reciprocal zero-sum estimate. This form matches the mathematical
contents of a zero certificate without exposing its numerical table. -/
theorem reciprocal_sum_of_ordinates100 (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (a : Fin 29 → ℚ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hsimple : ∀ i, analyticOrderAt riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 1)
    (hcomplete :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          0 < ρ.im → ρ.im ≤ 100 → ∃ i, ρ = ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I)
    (ha : ∀ i, 0 < a i) (hg : ∀ i, (a i : ℝ) ≤ g i) (hc : (∑ i, (2 : ℚ) / a i) < 237 / 200) {T : ℝ}
    (hT : 100 ≤ T) :
    zeroReciprocalSum T ≤ (Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 41 / 1000 := by
  let z : Fin 29 → ℂ := fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I
  have hinj : Function.Injective z := critical_points_injective g hmono.injective
  have hledger :=
    positive_ledger_of_ordinates (by norm_num only : (0 : ℝ) ≤ 100) g hpos hheight hzero hcomplete
  have hm : ∀ i, riemannZetaZeroMultiplicity (z i) = 1 := fun i ↦
    zeroMultiplicity_eq_one (hsimple i)
  have him : ∀ i, (z i).im = g i := by
    intro i
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  exact reciprocal_sum_of_enumeration100 hRH z g a hinj hledger hm him ha hg hc hT

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
