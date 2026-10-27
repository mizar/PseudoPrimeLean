/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaSignedEulerIdentity
public import Mathlib.NumberTheory.EulerProduct.Basic

/-! # Nonnegative paired Euler sums on the real axis

Keep the principal and character logarithmic derivatives together before estimating.
The arithmetic identity is the method used in Section 2 of the October 1, 2026
preprint `Uniform exclusion of Landau-Siegel zeros`; no zero-exclusion result is assumed.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The paired real-axis term Λ(m)(1+Re χ(m))/m^σ.
For σ>1 these terms converge absolutely, and norm-bounded character values
make every term nonnegative. Their sum retains both logarithmic derivatives. -/
noncomputable def realPairedEulerTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (σ : ℝ) (m : ℕ) : ℝ :=
  (1 + (χ m).re) * ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ σ

/-- For σ>1, the paired Euler terms are summable. Combine the absolutely
convergent untwisted and twisted Mangoldt series without estimating them separately. -/
theorem summable_realPairedEulerTerm {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (realPairedEulerTerm χ σ) := by
  have hs := (Arithmetic.summable_vonMangoldt_div_rpow hσ).add (summable_real_twistedMangoldt χ hσ)
  exact
    hs.congr
      (fun m ↦ by
        dsimp only [realPairedEulerTerm]; ring)

/-- Every paired term is nonnegative, at any real exponent. The real part
of a character value is at least minus one, while Mangoldt and real powers
are nonnegative. This allows retaining only a selected prime-power subseries. -/
theorem realPairedEulerTerm_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (σ : ℝ) (m : ℕ) :
    0 ≤ realPairedEulerTerm χ σ m := by
  have hχ := (abs_le.mp ((Complex.abs_re_le_norm (χ m)).trans (χ.norm_le_one m))).1
  exact
    div_nonneg (mul_nonneg (by linarith only [hχ]) ArithmeticFunction.vonMangoldt_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg m) σ)

/-- At σ>1, minus the real logarithmic derivatives of the level-one
principal function and χ equal the single paired Euler sum. The principal
function is the Riemann zeta function. Absolute convergence permits summing
the two real identities before any estimate; no primitivity or RH is required. -/
theorem neg_real_logDeriv_pair_eq_euler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) :
    -(logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
        (logDeriv χ.LFunction (σ : ℂ)).re =
      ∑' m : ℕ, realPairedEulerTerm χ σ m := by
  rw [re_logDeriv_eq_signed_Mangoldt_tsum _ hσ, re_logDeriv_eq_signed_Mangoldt_tsum χ hσ]
  simp only [MulChar.one_apply (isUnit_of_subsingleton (_ : ZMod 1)), Complex.one_re, one_mul,
    neg_neg, sub_neg_eq_add]
  rw [← (Arithmetic.summable_vonMangoldt_div_rpow hσ).tsum_add (summable_real_twistedMangoldt χ hσ)]
  exact
    tsum_congr
      (fun m ↦ by
        dsimp only [realPairedEulerTerm]; ring)

/-- At σ>1 the paired real logarithmic derivative is nonnegative.
Use the exact Euler identity and its nonnegative terms. The paired form is
retained rather than replaced by separate absolute-value estimates. -/
theorem neg_real_logDeriv_pair_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) :
    0 ≤
      -(logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
        (logDeriv χ.LFunction (σ : ℂ)).re := by
  rw [neg_real_logDeriv_pair_eq_euler χ hσ]
  exact tsum_nonneg (realPairedEulerTerm_nonneg χ σ)

/-- At σ>1 the paired Euler sum is exactly the double prime-power sum
with coefficient log(p)(1+Re(χ(p)^(k+1))). Mangoldt vanishes outside prime
powers, and absolute convergence justifies the unique prime-power reindexing. -/
theorem realPairedEuler_tsum_eq_prime_powers {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) :
    (∑' m : ℕ, realPairedEulerTerm χ σ m) =
      ∑' p : Nat.Primes,
        ∑' k : ℕ,
          (1 + ((χ (p : ℕ)) ^ (k + 1)).re) * Real.log (p : ℕ) / ((p : ℝ) ^ (k + 1)) ^ σ := by
  have hf : Function.support (realPairedEulerTerm χ σ) ⊆ {m | IsPrimePow m} := by
    intro m hm
    by_contra hnp
    exact
      hm
        (by
          simp only [realPairedEulerTerm, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp,
            mul_zero, zero_div])
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers (summable_realPairedEulerTerm χ hσ) hf]
  apply tsum_congr
  intro p
  apply tsum_congr
  intro k
  simp only [realPairedEulerTerm, Nat.cast_pow, map_pow,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
    ArithmeticFunction.vonMangoldt_apply_prime p.property]

/-- Any selected finite paired Euler sum is at most the real-axis paired
logarithmic derivative at σ>1. Positivity allows discarding the complementary
prime powers without an absolute-value loss. -/
theorem realPairedEuler_prefix_le_logDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) (B : Finset ℕ) :
    (∑ m ∈ B, realPairedEulerTerm χ σ m) ≤
      -(logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
        (logDeriv χ.LFunction (σ : ℂ)).re := by
  rw [neg_real_logDeriv_pair_eq_euler χ hσ]
  exact
    (summable_realPairedEulerTerm χ hσ).sum_le_tsum B (fun m _ ↦ realPairedEulerTerm_nonneg χ σ m)

/-- At σ>1 the exact zeta-plus-character logarithmic derivative is the
nonnegative paired prime-power series. Identify the level-one L-function
with zeta and use the absolutely convergent prime-power reindexing. -/
theorem neg_real_zeta_logDeriv_pair_eq_prime_powers {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) :
    -(logDeriv riemannZeta (σ : ℂ)).re - (logDeriv χ.LFunction (σ : ℂ)).re =
      ∑' p : Nat.Primes,
        ∑' k : ℕ,
          (1 + ((χ (p : ℕ)) ^ (k + 1)).re) * Real.log (p : ℕ) / ((p : ℝ) ^ (k + 1)) ^ σ := by
  rw [← DirichletCharacter.LFunction_modOne_eq (χ := (1 : DirichletCharacter ℂ 1)),
    neg_real_logDeriv_pair_eq_euler χ hσ, realPairedEuler_tsum_eq_prime_powers χ hσ]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
