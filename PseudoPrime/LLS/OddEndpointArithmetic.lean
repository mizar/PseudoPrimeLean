/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterOddTriviality
public import PseudoPrime.LLS.ReciprocalGapEndpointLimit

/-! # Odd-prime endpoint arithmetic with losses only at powers of two -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- Under triviality at odd primes through Y>0, the reciprocal character sum is
at least the unsigned sum minus twice the common-factor reciprocal sum at two.
Apply the generic odd-prime weighted inequality to nonnegative reciprocal factors.
No conductor/exclusion divisibility or support certificate is assumed. -/
theorem reciprocalSum_re_ge_of_odd_prime_trivial {q : ℕ} (χ : DirichletCharacter ℂ q) {Y : ℝ}
    (hY : 0 < Y) (ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ Y → χ p = 1) :
    reciprocalWeightedMangoldtSum Y - 2 * commonFactorReciprocalWeightedSum Y 2 ≤
      (characterReciprocalWeightedSum Y χ).re := by
  have hs :=
    weighted_sum_re_ge_of_odd_prime_trivial χ ht (Finset.Ioc 0 ⌊Y⌋₊)
      (fun n hn ↦ (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hY.le))
      (reciprocalMangoldtFactor Y)
      (fun n hn ↦
        reciprocalMangoldtFactor_nonneg hY n
          ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hY.le)))
  simp only [mul_assoc, mangoldt_mul_reciprocalMangoldtFactor] at hs
  unfold characterReciprocalWeightedSum characterReciprocalWeightedTerm
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have he :
    (∑ n ∈ Finset.Ioc 0 ⌊Y⌋₊, reciprocalWeightedMangoldtTerm Y n * (χ n).re) =
      ∑ n ∈ Finset.Ioc 0 ⌊Y⌋₊, (χ n).re * reciprocalWeightedMangoldtTerm Y n := by
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he]
  exact hs

open AnalyticNumberTheory.Arithmetic in
/-- For positive gap, positive x and positive natural n, the gap principal term
is at most the logarithmic term divided by sqrt(x). Use exp(t)>=1+t and multiply
by nonnegative Lambda(n)/sqrt(x). This upper bounds the excluded even-index loss. -/
theorem reciprocalGapPrincipalWeight_le_log_term {h x : ℝ} (hh : 0 < h) (hx : 0 < x) {n : ℕ}
    (hn : 0 < n) :
    reciprocalGapPrincipalWeight h x n ≤ logWeightedMangoldtTerm x n / Real.sqrt x := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he := Real.add_one_le_exp (Real.log ((n : ℝ) / x) * h)
  rw [← Real.rpow_def_of_pos (div_pos hn0 hx)] at he
  have hd : (1 - ((n : ℝ) / x) ^ h) / h ≤ Real.log (x / n) := by
    apply (div_le_iff₀ hh).mpr
    rw [Real.log_div hn0.ne' hx.ne'] at he
    rw [Real.log_div hx.ne' hn0.ne']
    nlinarith only [he]
  have hm :=
    mul_le_mul_of_nonneg_left hd
      (div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (Real.sqrt_nonneg x))
  unfold reciprocalGapPrincipalWeight logWeightedMangoldtTerm
  convert hm using 1
  simp only [div_eq_mul_inv]
  ring

open AnalyticNumberTheory.Arithmetic in
/-- Under RH, h>0,x>1 and odd-prime triviality through x, the gap character sum
has the displayed analytic lower bound with only twice the two-part logarithmic
loss. Apply the generic odd-prime inequality, the principal analytic lower bound,
and the termwise upper bound on the even part. No modulus prime-factor loss remains. -/
theorem reciprocalGapSum_re_ge_of_odd_prime_trivial {q : ℕ} (χ : DirichletCharacter ℂ q) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hRH : RiemannHypothesis)
    (ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ x → χ p = 1) :
    (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) /
          (Real.sqrt x * (1 + h * Real.log x)) -
        2 * commonFactorLogWeightedSum x 2 / Real.sqrt x ≤
      (reciprocalGapCharacterSum h χ x).re := by
  have hs :=
    weighted_sum_re_ge_of_odd_prime_trivial χ ht (Finset.Ioc 0 ⌊x⌋₊)
      (fun n hn ↦
        (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le (zero_lt_one.trans hx).le))
      (reciprocalGapPrincipalFactor h x)
      (fun n hn ↦
        reciprocalGapPrincipalFactor_nonneg hh.le (zero_lt_one.trans hx) n
          ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans
            (Nat.floor_le (zero_lt_one.trans hx).le)))
  simp only [mul_assoc, mangoldt_mul_reciprocalGapPrincipalFactor] at hs
  rw [← reciprocalGapCharacterSum_re_eq_weighted] at hs
  have he :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬Nat.Coprime n 2),
        reciprocalGapPrincipalWeight h x n) ≤
      commonFactorLogWeightedSum x 2 / Real.sqrt x := by
    unfold commonFactorLogWeightedSum
    rw [Finset.sum_div]
    exact
      Finset.sum_le_sum
        (fun n hn ↦
          reciprocalGapPrincipalWeight_le_log_term hh (zero_lt_one.trans hx)
            (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1)
  have hl := logSum_div_le_gapSum hh hx.le (Finset.Ioc 0 ⌊x⌋₊) (fun _ hn ↦ hn)
  change logWeightedMangoldtSum x / (Real.sqrt x * (1 + h * Real.log x)) ≤ _ at hl
  have hd : 0 ≤ Real.sqrt x * (1 + h * Real.log x) :=
    mul_nonneg (Real.sqrt_nonneg x) (by nlinarith only [hh, Real.log_pos hx])
  have hr :=
    div_le_div_of_nonneg_right (PseudoPrime.LLS.logWeightedMangoldtSum_ge_rational_refined hRH hx)
      hd
  simp only [mul_div_assoc]
  linarith only [hs, he, hl, hr]

end PseudoPrime.LLS.PaperStatements
