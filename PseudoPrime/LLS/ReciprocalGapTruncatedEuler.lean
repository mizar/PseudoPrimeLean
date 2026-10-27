/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapTwoShiftBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedMangoldtBounds

/-! # Explicit truncated Euler caps in the two-shift prime-witness criterion -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The full two-shift separation budget with three independent finite Euler cutoffs.
It combines the zero-prefix comparison, retained-prefix pole budget, signed left budget
and signed Gamma term, using the explicit truncated Euler ratio at every required exponent.
Inputs are totalized; the witness theorem imposes positive gaps, admissible c and cutoffs>=3.
This removes external infinite-series cap premises from the analytic witness interface. -/
noncomputable def reciprocalGapTruncatedSeparation (h r c : ℝ) (q : ℕ) (x : ℝ) (B₀ B₁ : Finset ℕ)
    (N₀ N₁ N₂ : ℕ) : ℝ :=
  (1 / c) *
      (Real.log q / 2 + reciprocalGapOddGammaUpper (1 / 2 + c) +
          AnalyticNumberTheory.Arithmetic.truncatedEulerUpper (c - 1 / 2) N₀ -
        2 * ∑ n ∈ B₀, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) +
    (reciprocalGapPrefixPoleBudget h r q x
        (AnalyticNumberTheory.Arithmetic.truncatedEulerUpper r N₁)
        (reciprocalGapOddGammaUpper (1 + r)) B₁ +
      reciprocalGapRealAxisBudget h q x (AnalyticNumberTheory.Arithmetic.truncatedEulerUpper h N₂)
        (reciprocalGapEvenGammaLower (1 + h)) +
      reciprocalGapSignedGammaBudget h x)

open AnalyticNumberTheory.DirichletLFunction in
/-- For any character, positive horizontal gap and cutoff at least three, the ordinary
logarithmic derivative on Re(s)=1+r has norm at most the explicit truncated Euler ratio.
Dominate the twisted Mangoldt series uniformly in height, then apply the finite-prefix cap.
No GRH, primitivity or character nontriviality is required. -/
theorem norm_logDeriv_vertical_le_truncatedEuler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 3 ≤ N) (t : ℝ) :
    ‖logDeriv χ.LFunction (((1 + r : ℝ) : ℂ) + t * Complex.I)‖ ≤
      AnalyticNumberTheory.Arithmetic.truncatedEulerUpper r N := by
  have hn :=
    norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ
      (show 1 < 1 + r by linarith only [hr]) t
  simp only [neg_div, norm_neg] at hn
  exact hn.trans (AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_truncatedEuler hr hN)

/-- For primitive nonprincipal GRH data at level at least two, positive h,r, admissible c,
x>=1 and two finite supports below x, three arbitrary cutoffs>=3 give an explicit
finite-prefix separation condition implying a non-one prime witness below x.
Supply all three Euler caps from the proved truncated ratio and apply the two-shift
criterion. Numerical certification of a particular parameter range remains a separate step. -/
theorem exists_prime_not_one_of_reciprocalGap_truncated_separation {h r c : ℝ} (hh : 0 < h)
    (hr : 0 < r) {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ}
    (hx : 1 ≤ x) (B₀ B₁ : Finset ℕ) (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x)
    (N₀ N₁ N₂ : ℕ) (hN₀ : 3 ≤ N₀) (hN₁ : 3 ≤ N₁) (hN₂ : 3 ≤ N₂)
    (hgap :
      reciprocalGapTruncatedSeparation h r c q x B₀ B₁ N₀ N₁ N₂ <
        (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  have h0 := AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_truncatedEuler (sub_pos.mpr hc) hN₀
  have he : (1 : ℝ) + (c - 1 / 2) = 1 / 2 + c := by ring
  rw [he] at h0
  exact
    exists_prime_not_one_of_reciprocalGap_two_shift_prefix hh hr hq hGRH hp hne hinv hc hbound hx B₀
      B₁ hB₀ hB₁ (AnalyticNumberTheory.Arithmetic.truncatedEulerUpper (c - 1 / 2) N₀)
      (AnalyticNumberTheory.Arithmetic.truncatedEulerUpper r N₁)
      (AnalyticNumberTheory.Arithmetic.truncatedEulerUpper h N₂) h0
      (AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_truncatedEuler hr hN₁)
      (AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_truncatedEuler hh hN₂) hgap

end PseudoPrime.LLS.PaperStatements
