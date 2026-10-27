/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterFullTriviality
public import PseudoPrime.LLS.ReciprocalGapEndpointAnalyticWitness
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants

/-! # Full-prime endpoint separation with no arithmetic exclusion losses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- At nonnegative Y, triviality at every prime through Y identifies the real
reciprocal character sum with the unsigned sum. Apply the generic weighted
Mangoldt identity to reciprocal factors. This supplies a loss-free mass input. -/
theorem reciprocalSum_re_eq_of_full_prime_trivial {q : ℕ} (χ : DirichletCharacter ℂ q) {Y : ℝ}
    (hY : 0 ≤ Y) (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y → χ p = 1) :
    (characterReciprocalWeightedSum Y χ).re = reciprocalWeightedMangoldtSum Y := by
  have hs :=
    AnalyticNumberTheory.Arithmetic.weighted_sum_re_eq_of_full_prime_trivial χ ht
      (Finset.Ioc 0 ⌊Y⌋₊)
      (fun n hn ↦ (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hY))
      (reciprocalMangoldtFactor Y)
  simp only [mul_assoc, mangoldt_mul_reciprocalMangoldtFactor] at hs
  unfold characterReciprocalWeightedSum characterReciprocalWeightedTerm
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  calc
    _ = ∑ n ∈ Finset.Ioc 0 ⌊Y⌋₊, (χ n).re * reciprocalWeightedMangoldtTerm Y n := by
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = reciprocalWeightedMangoldtSum Y := hs

/-- For nonnegative x and arbitrary gap h, triviality at all primes through x
identifies the real gap sum with its principal counterpart. Apply the generic
weighted Mangoldt identity to gap factors. No exclusions or coprimality losses occur. -/
theorem reciprocalGapSum_re_eq_of_full_prime_trivial {q : ℕ} (χ : DirichletCharacter ℂ q) {h x : ℝ}
    (hx : 0 ≤ x) (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1) :
    (reciprocalGapCharacterSum h χ x).re =
      (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re := by
  rw [reciprocalGapCharacterSum_re_eq_weighted, reciprocalGap_principal_re_eq_sum]
  have hs :=
    AnalyticNumberTheory.Arithmetic.weighted_sum_re_eq_of_full_prime_trivial χ ht
      (Finset.Ioc 0 ⌊x⌋₊)
      (fun n hn ↦ (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx))
      (reciprocalGapPrincipalFactor h x)
  simpa only [mul_assoc, mangoldt_mul_reciprocalGapPrincipalFactor] using hs

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Scalar endpoint upper minus analytic principal lower with reciprocal loss
31551/20000 and no excluded primes. Inputs h,q,x,Y are totalized; strict negativity
is used with h>0 and 64<=Y<=x. No finite supports, character sums or factorizations
enter this criterion, so it can be studied as an explicit real inequality. -/
noncomputable def reciprocalGapFullEndpointSeparation (h : ℝ) (q : ℕ) (x Y : ℝ) : ℝ :=
  let M := reciprocalGapReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ))
  2 * M + reciprocalGapEndpointMassBudget h q x M + reciprocalGapSignedGammaBudget h x -
    (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) /
      (Real.sqrt x * (1 + h * Real.log x))

open AnalyticNumberTheory.RiemannZeta in
/-- For primitive nonprincipal GRH data at q>=2, h>0 and 64<=Y<=x, strict full
endpoint separation produces a prime at most x with character value different
from one. Under nonexistence both weighted sums become unsigned, so the existing
RH bounds give the contradiction. A prime dividing the level is an allowed witness.
This removes the ambient exclusion costs in MR-type applications. -/
theorem exists_prime_not_one_of_reciprocalGap_full_endpoint {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y : ℝ} (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hgap : reciprocalGapFullEndpointSeparation h q x Y < 0) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1 := by
    intro p hp hpx
    by_contra hv
    exact hn ⟨p, hp, hpx, hv⟩
  have hy2 : (2 : ℝ) ≤ Y := by linarith only [hY]
  have he :=
    reciprocalSum_re_eq_of_full_prime_trivial χ (by linarith only [hy2] : 0 ≤ Y)
      (fun p hp hpy ↦ ht p hp (hpy.trans hYx))
  have hR := reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000 hGRH.riemann hy2
  rw [← he] at hR
  have hm := reciprocalGap_mass_le_reciprocal_cap hq hGRH hp hne hinv hY hR
  have hU := reciprocalGapCharacterSum_re_le_endpoint_mass hh hq hGRH hp hne hinv hx.le hm
  have hL := logSum_div_le_gapSum hh hx.le (Finset.Ioc 0 ⌊x⌋₊) (fun _ hn ↦ hn)
  change
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x /
        (Real.sqrt x * (1 + h * Real.log x)) ≤
      _ at hL
  rw [← reciprocalGap_principal_re_eq_sum, ←
    reciprocalGapSum_re_eq_of_full_prime_trivial χ (zero_lt_one.trans hx).le ht] at hL
  have hd : 0 ≤ Real.sqrt x * (1 + h * Real.log x) :=
    mul_nonneg (Real.sqrt_nonneg x) (by nlinarith only [hh, Real.log_pos hx])
  have hl :=
    div_le_div_of_nonneg_right
      (PseudoPrime.LLS.logWeightedMangoldtSum_ge_rational_refined hGRH.riemann hx) hd
  dsimp only [reciprocalGapFullEndpointSeparation] at hgap
  linarith only [hU, hL, hl, hgap]

end PseudoPrime.LLS.PaperStatements
