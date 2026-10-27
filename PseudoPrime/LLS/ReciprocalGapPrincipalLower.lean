/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapRationalGamma

/-! # Selected finite lower bounds for the reciprocal-gap principal sum -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The real principal summand Lambda(n)/sqrt(x)*(1-(n/x)^h)/h.
Inputs h,x,n are totalized; nonnegativity requires h>=0,x>0,n<=x.
This exposes the arithmetic side for selected finite lower certificates. -/
noncomputable def reciprocalGapPrincipalWeight (h x : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n / Real.sqrt x) * ((1 - ((n : ℝ) / x) ^ h) / h)

/-- For arbitrary real h,x, the level-one principal character sum is the real
sum of the principal weights. The level-one character is identically one.
This removes complex arithmetic from lower-bound certificates. -/
theorem reciprocalGap_principal_re_eq_sum (h x : ℝ) :
    (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, reciprocalGapPrincipalWeight h x n := by
  have hone (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton ((n : ℕ) : ZMod 1))
  simp only [reciprocalGapCharacterSum, reciprocalGapPrincipalWeight, hone, mul_one,
    ← Complex.ofReal_mul, Complex.re_sum, Complex.ofReal_re]

/-- For h>=0,x>0 and natural n<=x, the principal weight is nonnegative.
Use the power bound on [0,1] and nonnegativity of the Mangoldt function.
This permits discarding unselected terms when bounding the principal sum below. -/
theorem reciprocalGapPrincipalWeight_nonneg {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) (n : ℕ)
    (hn : (n : ℝ) ≤ x) : 0 ≤ reciprocalGapPrincipalWeight h x n := by
  have hp := Real.rpow_le_one (div_nonneg (Nat.cast_nonneg n) hx.le) ((div_le_one hx).mpr hn) hh
  exact
    mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg x))
      (div_nonneg (sub_nonneg.mpr hp) hh)

/-- For h>=0,x>0, the weights on any selected subset of positive integers below x
sum to at most the principal character sum. Bound the omitted weights by zero.
The support may be chosen independently of both comparison prefixes. -/
theorem sum_reciprocalGapPrincipalWeight_le {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) :
    (∑ n ∈ B, reciprocalGapPrincipalWeight h x n) ≤
      (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re := by
  rw [reciprocalGap_principal_re_eq_sum]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hB
      (fun n hn _ ↦
        reciprocalGapPrincipalWeight_nonneg hh hx n
          ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx.le)))

/-- For h,x>0 and a selected support below x, Mangoldt lower endpoints and power
upper endpoints at most one give a lower bound for the principal sum.
Compare products termwise and discard unselected nonnegative weights.
Lower endpoints may be negative; only the upper power endpoints need be at most one. -/
theorem sum_lower_le_reciprocalGap_principal {h x : ℝ} (hh : 0 < h) (hx : 0 < x) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ B, u n ≤ 1) :
    (∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) ≤
      (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re := by
  have hp :
    (∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) ≤
      ∑ n ∈ B, reciprocalGapPrincipalWeight h x n := by
    refine Finset.sum_le_sum (fun n hn ↦ ?_)
    exact
      mul_le_mul (div_le_div_of_nonneg_right (hlo n hn) (Real.sqrt_nonneg x))
        (div_le_div_of_nonneg_right (sub_le_sub_left (hu n hn) 1) hh.le)
        (div_nonneg (sub_nonneg.mpr (hu1 n hn)) hh.le)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg x))
  exact hp.trans (sum_reciprocalGapPrincipalWeight_le hh.le hx B hB)

/-- For primitive nonprincipal GRH data at q>=2,x>=1 and supports below x, separation
against any certified selected lower sum gives a non-one prime witness below x.
Compose the principal lower certificate with the rational-Gamma witness criterion.
Euler and Gamma special values and the full principal sum are absent from the premises. -/
theorem exists_prime_not_one_of_reciprocalGap_principal_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (B₀ B₁ B : Finset ℕ)
    (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊)
    (lo u : ℕ → ℝ) (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n)
    (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u n) (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapRationalGammaSeparation q x B₀ B₁ <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / (7 / 10 : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  apply
    exists_prime_not_one_of_reciprocalGap_rationalGamma_separation hq hGRH hp hne hinv hx B₀ B₁ hB₀
      hB₁
  exact
    hgap.trans_le
      (sum_lower_le_reciprocalGap_principal (by norm_num only : (0 : ℝ) < 7 / 10)
        (zero_lt_one.trans_le hx) B hB lo u hlo hu hu1)

end PseudoPrime.LLS.PaperStatements
