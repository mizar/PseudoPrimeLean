/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapLogarithmicLower
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Secant lower bounds for the variable-gap principal kernel -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive h,T and 0<=t<=T, the exponential gap is bounded below by its
secant on [0,T]. Apply convexity of exp at the endpoints and normalize positive factors.
This keeps the exact endpoint coefficient instead of the tangent-denominator relaxation. -/
theorem exp_gap_ge_secant {h T t : ℝ} (hh : 0 < h) (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) :
    ((1 - Real.exp (-h * T)) / (h * T)) * t ≤ (1 - Real.exp (-h * t)) / h := by
  have ha : 0 ≤ 1 - t / T := sub_nonneg.mpr ((div_le_one hT).mpr htT)
  have hb : 0 ≤ t / T := div_nonneg ht hT.le
  have hs : 1 - t / T + t / T = 1 := by ring
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-h * T)) ha hb hs
  have he : (1 - t / T) * 0 + (t / T) * (-h * T) = -h * t := by
    field_simp (disch := exact hT.ne')
    ring
  simp only [smul_eq_mul] at hc
  rw [he, Real.exp_zero, mul_one] at hc
  apply (le_div_iff₀ hh).mpr
  have hn : ((1 - Real.exp (-h * T)) / (h * T)) * t * h = (t / T) * (1 - Real.exp (-h * T)) := by
    field_simp (disch :=
      first
      | exact hT.ne'
      | exact hh.ne')
  rw [hn]
  nlinarith only [hc]

/-- The exact endpoint coefficient (1-x^(-h))/(h log x). Inputs are totalized.
For h>0 and x>1 it transfers a logarithmic Mangoldt lower bound to the gap kernel.
It is independent of the modulus and the selected arithmetic support. -/
noncomputable def reciprocalGapLogSecant (h x : ℝ) : ℝ :=
  (1 - x ^ (-h)) / (h * Real.log x)

/-- For h>0 and x>1, the secant coefficient is nonnegative. Use x^(-h)<=1.
This permits multiplying analytic principal lower bounds by the coefficient. -/
theorem reciprocalGapLogSecant_nonneg {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    0 ≤ reciprocalGapLogSecant h x := by
  have hp : x ^ (-h) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (neg_nonpos.mpr hh.le)
  exact div_nonneg (sub_nonneg.mpr hp) (mul_nonneg hh.le (Real.log_pos hx).le)

/-- For h>0 and x>1, the secant coefficient strictly exceeds 1/(1+h log x).
Use the strict exponential tangent at h log x. This proves uniform improvement
of the old coefficient without restricting the gap parameter. -/
theorem reciprocalGapLogSecant_gt_fraction {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    1 / (1 + h * Real.log x) < reciprocalGapLogSecant h x := by
  have hv : 0 < h * Real.log x := mul_pos hh (Real.log_pos hx)
  have hd : 0 < 1 + h * Real.log x := by linarith only [hv]
  have he := mul_lt_mul_of_pos_right (Real.add_one_lt_exp hv.ne') (Real.exp_pos (-(h * Real.log x)))
  have heq : Real.exp (h * Real.log x) * Real.exp (-(h * Real.log x)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [heq] at he
  have hc : h * Real.log x < (1 - Real.exp (-(h * Real.log x))) * (1 + h * Real.log x) := by
    nlinarith only [he]
  have hfrac := (div_lt_iff₀ hd).mpr hc
  dsimp only [reciprocalGapLogSecant]
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
  have hn : Real.log x * -h = -(h * Real.log x) := by ring
  rw [hn]
  apply (lt_div_iff₀ hv).mpr
  have hf :
    (1 / (1 + h * Real.log x)) * (h * Real.log x) = (h * Real.log x) / (1 + h * Real.log x) := by
    ring
  rw [hf]
  exact hfrac

/-- For h>0, x>1 and 1<=n<=x, the secant coefficient times log(x/n)
bounds the principal gap factor below. Apply the exponential secant on [0,log x].
This is the scalar input for arbitrary selected Mangoldt supports. -/
theorem reciprocal_gap_ge_log_secant {h x : ℝ} (hh : 0 < h) (hx : 1 < x) {n : ℕ} (hn : 1 ≤ n)
    (hnx : (n : ℝ) ≤ x) :
    reciprocalGapLogSecant h x * Real.log (x / n) ≤ (1 - ((n : ℝ) / x) ^ h) / h := by
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hx0 : 0 < x := zero_lt_one.trans hx
  have ht : 0 ≤ Real.log (x / n) := Real.log_nonneg ((one_le_div hn0).mpr hnx)
  have htL : Real.log (x / n) ≤ Real.log x := by
    rw [Real.log_div hx0.ne' hn0.ne']
    linarith only [Real.log_nonneg hn1]
  have he : Real.exp (-h * Real.log (x / n)) = ((n : ℝ) / x) ^ h := by
    rw [Real.rpow_def_of_pos (div_pos hn0 hx0), Real.log_div hx0.ne' hn0.ne',
      Real.log_div hn0.ne' hx0.ne']
    congr 1
    ring
  have heL : Real.exp (-h * Real.log x) = x ^ (-h) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have hg := exp_gap_ge_secant hh (Real.log_pos hx) ht htL
  rw [he, heL] at hg
  exact hg

/-- Under the positive-gap and positive-index conditions, the normalized logarithmic
Mangoldt term multiplied by the secant coefficient is at most the gap weight.
Multiply the scalar secant by nonnegative Lambda(n)/sqrt x. This supplies finite sums. -/
theorem logTerm_secant_le_gapWeight {h x : ℝ} (hh : 0 < h) (hx : 1 < x) {n : ℕ} (hn : 1 ≤ n)
    (hnx : (n : ℝ) ≤ x) :
    reciprocalGapLogSecant h x * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n /
        Real.sqrt x ≤
      reciprocalGapPrincipalWeight h x n := by
  have hl :=
    mul_le_mul_of_nonneg_left (reciprocal_gap_ge_log_secant hh hx hn hnx)
      (div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (Real.sqrt_nonneg x))
  dsimp only [AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm, reciprocalGapPrincipalWeight]
  convert hl using 1
  ring

/-- For h>0,x>1 and a selected positive support through x, the secant-scaled
logarithmic sum bounds the selected gap sum below. Sum the termwise comparison.
The support may impose arbitrary prime exclusions independently of the gap. -/
theorem logSum_secant_le_gapSum {h x : ℝ} (hh : 0 < h) (hx : 1 < x) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) :
    reciprocalGapLogSecant h x *
          (∑ n ∈ B, AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) /
        Real.sqrt x ≤
      ∑ n ∈ B, reciprocalGapPrincipalWeight h x n := by
  rw [Finset.mul_sum, Finset.sum_div]
  exact
    Finset.sum_le_sum
      (fun n hn ↦
        logTerm_secant_le_gapWeight hh hx (Finset.mem_Ioc.mp (hB hn)).1
          ((Nat.cast_le.mpr (Finset.mem_Ioc.mp (hB hn)).2).trans
            (Nat.floor_le (zero_lt_one.trans hx).le)))

/-- For positive h,M and x>1, the new secant lower expression strictly exceeds
the old denominator lower expression. Multiply the strict coefficient comparison by
M/sqrt x. This identifies when an analytic numerator gives a strict gain. -/
theorem reciprocalGapSecant_lower_gt_fraction {h x M : ℝ} (hh : 0 < h) (hx : 1 < x) (hM : 0 < M) :
    M / (Real.sqrt x * (1 + h * Real.log x)) < reciprocalGapLogSecant h x * M / Real.sqrt x := by
  have hc := mul_lt_mul_of_pos_right (reciprocalGapLogSecant_gt_fraction hh hx) hM
  have hd := div_lt_div_of_pos_right hc (Real.sqrt_pos.mpr (zero_lt_one.trans hx))
  have he :
    (1 / (1 + h * Real.log x) * M) / Real.sqrt x = M / (Real.sqrt x * (1 + h * Real.log x)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at hd
  exact hd

/-- Under RH, q dividing N, h>0,x>1 and triviality at N-coprime small primes,
the character gap sum has the displayed secant-scaled analytic lower bound.
Keep both the common-factor logarithmic loss and the additional nonunit weight exact.
This is the improved principal input for negative unit-prime extraction. -/
theorem reciprocalGapCharacterSum_re_ge_secant_analytic {q N : ℕ} (hqN : q ∣ N)
    (χ : DirichletCharacter ℂ q) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) (hRH : RiemannHypothesis)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1) :
    reciprocalGapLogSecant h x *
            (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20 -
              AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x N) /
          Real.sqrt x -
        PseudoPrime.LLS.PaperStatements.reciprocalGapAdditionalNonunitWeight h q N x ≤
      (PseudoPrime.LLS.PaperStatements.reciprocalGapCharacterSum h χ x).re := by
  let B := (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ Nat.Coprime n N)
  have hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊ := fun n hn ↦ (Finset.mem_filter.mp hn).1
  have hcop : ∀ n ∈ B, Nat.Coprime n N := fun n hn ↦ (Finset.mem_filter.mp hn).2
  have hg := logSum_secant_le_gapSum hh hx B hB
  have ha :=
    PseudoPrime.LLS.PaperStatements.selected_reciprocalGap_sum_sub_loss_le_character hqN hh.le
      (zero_lt_one.trans hx) χ ht B hB hcop
  have hs :
    (∑ n ∈ B, AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) =
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x -
        AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x N := by
    have he :=
      Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc 0 ⌊x⌋₊) (f :=
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x) (p := fun n ↦ Nat.Coprime n N)
    unfold AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum
      AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum
    exact (eq_sub_iff_add_eq).mpr he
  rw [hs] at hg
  have hr :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (sub_le_sub_right (PseudoPrime.LLS.logWeightedMangoldtSum_ge_rational_refined hRH hx)
          (AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x N))
        (reciprocalGapLogSecant_nonneg hh hx))
      (Real.sqrt_nonneg x)
  linarith only [hr, hg, ha]

/-- Under RH, h>0 and x>1, the principal gap sum exceeds the secant-scaled
rational logarithmic Mangoldt lower profile. Sum over the full support and use the
proved RH lower bound. This is the exclusion-free input for MR witnesses. -/
theorem reciprocalGap_principal_ge_secant_analytic {h x : ℝ} (hh : 0 < h) (hx : 1 < x)
    (hRH : RiemannHypothesis) :
    reciprocalGapLogSecant h x * (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) /
        Real.sqrt x ≤
      (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re := by
  have hs := logSum_secant_le_gapSum hh hx (Finset.Ioc 0 ⌊x⌋₊) (fun _ hn ↦ hn)
  change
    reciprocalGapLogSecant h x * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x /
        Real.sqrt x ≤
      _ at hs
  rw [← reciprocalGap_principal_re_eq_sum] at hs
  have hr :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (logWeightedMangoldtSum_ge_rational_refined hRH hx)
        (reciprocalGapLogSecant_nonneg hh hx))
      (Real.sqrt_nonneg x)
  exact hr.trans hs

end PseudoPrime.LLS.PaperStatements
