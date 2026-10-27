/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapAmbientArithmetic
public import PseudoPrime.LLS.RiemannWeightedErrorBounds

/-! # Logarithmic main-term lower bounds uniform over positive gaps -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For h>0 and t>=0, the normalized exponential gap is at least t/(1+h*t).
Multiply exp(h*t)>=1+h*t by exp(-h*t) and divide positive denominators.
This lower comparison remains useful as h approaches zero. -/
theorem exp_gap_ge_log_fraction {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) :
    t / (1 + h * t) ≤ (1 - Real.exp (-h * t)) / h := by
  have hd : 0 < 1 + h * t := by nlinarith only [hh, ht]
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (h * t)) (Real.exp_pos (-h * t)).le
  have hx : Real.exp (h * t) * Real.exp (-h * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hx] at he
  have hc : h * t ≤ (1 - Real.exp (-h * t)) * (1 + h * t) := by nlinarith only [he]
  have hq := (div_le_iff₀ hd).mpr hc
  calc
    t / (1 + h * t) = (h * t / (1 + h * t)) / h := by field_simp [hh.ne']
    _ ≤ (1 - Real.exp (-h * t)) / h := div_le_div_of_nonneg_right hq hh.le

/-- For h>0, x>=1 and 1<=n<=x, the gap weight is at least
log(x/n)/(1+h*log x). Apply the exponential gap comparison and log n>=0.
This supplies one common denominator for all principal summands. -/
theorem reciprocal_gap_ge_log_fraction {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x) {n : ℕ} (hn : 1 ≤ n)
    (hnx : (n : ℝ) ≤ x) :
    Real.log (x / n) / (1 + h * Real.log x) ≤ (1 - ((n : ℝ) / x) ^ h) / h := by
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ht : 0 ≤ Real.log (x / n) := Real.log_nonneg ((one_le_div hn0).mpr hnx)
  have htL : Real.log (x / n) ≤ Real.log x := by
    rw [Real.log_div hx0.ne' hn0.ne']
    linarith only [Real.log_nonneg hn1]
  have hd : 0 < 1 + h * Real.log (x / n) := by nlinarith only [hh, ht]
  have hdL : 1 + h * Real.log (x / n) ≤ 1 + h * Real.log x :=
    add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left htL hh.le)
  have hl := div_le_div_of_nonneg_left ht hd hdL
  have he : Real.exp (-h * Real.log (x / n)) = ((n : ℝ) / x) ^ h := by
    rw [Real.rpow_def_of_pos (div_pos hn0 hx0), Real.log_div hx0.ne' hn0.ne',
      Real.log_div hn0.ne' hx0.ne']
    congr 1
    ring
  have hg := exp_gap_ge_log_fraction hh ht
  rw [he] at hg
  exact hl.trans hg

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- Under the same positive-gap and index conditions, the logarithmic Mangoldt
term divided by sqrt(x)*(1+h*log x) is at most the gap principal term.
Multiply the scalar comparison by nonnegative Lambda(n)/sqrt(x).
This transfers existing logarithmic main-term lower bounds to the gap kernel. -/
theorem logTerm_div_le_gapWeight {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x) {n : ℕ} (hn : 1 ≤ n)
    (hnx : (n : ℝ) ≤ x) :
    logWeightedMangoldtTerm x n / (Real.sqrt x * (1 + h * Real.log x)) ≤
      PseudoPrime.LLS.PaperStatements.reciprocalGapPrincipalWeight h x n := by
  have hl :=
    mul_le_mul_of_nonneg_left (reciprocal_gap_ge_log_fraction hh hx hn hnx)
      (div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (Real.sqrt_nonneg x))
  unfold logWeightedMangoldtTerm PseudoPrime.LLS.PaperStatements.reciprocalGapPrincipalWeight
  convert hl using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- For positive gap, x>=1 and any selected support in the positive floor interval,
the selected logarithmic sum with the common denominator bounds the gap sum below.
Sum the termwise comparison. The support can enforce arbitrary prime exclusions. -/
theorem logSum_div_le_gapSum {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) :
    (∑ n ∈ B, logWeightedMangoldtTerm x n) / (Real.sqrt x * (1 + h * Real.log x)) ≤
      ∑ n ∈ B, PseudoPrime.LLS.PaperStatements.reciprocalGapPrincipalWeight h x n := by
  rw [Finset.sum_div]
  exact
    Finset.sum_le_sum
      (fun n hn ↦
        logTerm_div_le_gapWeight hh hx (Finset.mem_Ioc.mp (hB hn)).1
          ((Nat.cast_le.mpr (Finset.mem_Ioc.mp (hB hn)).2).trans
            (Nat.floor_le (zero_le_one.trans hx))))

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- Under RH, q dividing N, h>0,x>1 and character triviality at N-coprime primes
through x, the real gap sum has the displayed analytic lower bound. Apply the
logarithmic comparison on the full N-coprime support and the existing RH main term.
Keep both the common-factor logarithmic loss and additional gap nonunit loss exact.
No enumerated principal support or per-modulus certificate is required. -/
theorem reciprocalGapCharacterSum_re_ge_logarithmic_analytic {q N : ℕ} (hqN : q ∣ N)
    (χ : DirichletCharacter ℂ q) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) (hRH : RiemannHypothesis)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1) :
    (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20 -
            commonFactorLogWeightedSum x N) /
          (Real.sqrt x * (1 + h * Real.log x)) -
        PseudoPrime.LLS.PaperStatements.reciprocalGapAdditionalNonunitWeight h q N x ≤
      (PseudoPrime.LLS.PaperStatements.reciprocalGapCharacterSum h χ x).re := by
  let B := (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ Nat.Coprime n N)
  have hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊ := fun n hn ↦ (Finset.mem_filter.mp hn).1
  have hcop : ∀ n ∈ B, Nat.Coprime n N := fun n hn ↦ (Finset.mem_filter.mp hn).2
  have hg := logSum_div_le_gapSum hh hx.le B hB
  have ha :=
    PseudoPrime.LLS.PaperStatements.selected_reciprocalGap_sum_sub_loss_le_character hqN hh.le
      (zero_lt_one.trans hx) χ ht B hB hcop
  have hs :
    (∑ n ∈ B, logWeightedMangoldtTerm x n) =
      logWeightedMangoldtSum x - commonFactorLogWeightedSum x N := by
    have he :=
      Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc 0 ⌊x⌋₊) (f := logWeightedMangoldtTerm x)
        (p := fun n ↦ Nat.Coprime n N)
    unfold logWeightedMangoldtSum commonFactorLogWeightedSum
    exact (eq_sub_iff_add_eq).mpr he
  rw [hs] at hg
  have hd : 0 ≤ Real.sqrt x * (1 + h * Real.log x) :=
    mul_nonneg (Real.sqrt_nonneg x) (by nlinarith only [hh, Real.log_pos hx])
  have hr :=
    div_le_div_of_nonneg_right
      (sub_le_sub_right (PseudoPrime.LLS.logWeightedMangoldtSum_ge_rational_refined hRH hx)
        (commonFactorLogWeightedSum x N))
      hd
  linarith only [hr, hg, ha]

end PseudoPrime.LLS.PaperStatements
