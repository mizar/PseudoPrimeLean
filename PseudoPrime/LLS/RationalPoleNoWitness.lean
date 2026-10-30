/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalPoleLocalCosts
public import PseudoPrime.LLS.RationalPoleExplicitFormula

/-! # Finite no-witness comparison for the fourth-pole kernel -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The real quadratic-character summand equals the character real value times the
actual nonnegative principal Mangoldt weight. -/
theorem fourPole_quadratic_summand_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic)
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ((MellinKernel.summand rationalPoleFourKernel) χ x n).re =
      (χ n).re * (ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) := by
  by_cases hn : n = 0
  · subst n
    simp only [MellinKernel.summand, ite_true, Complex.zero_re, ArithmeticFunction.map_zero,
      zero_mul, mul_zero]
  · have he :
      (MellinKernel.summand rationalPoleFourKernel) χ x n =
        χ n * (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ 1) x n := by
      simp only [MellinKernel.summand, ite_eq_right hn,
        MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one]
      ring
    have him : (χ n).im = 0 := by
      rcases hq n with h | h | h
      · rw [h, Complex.zero_im]
      · rw [h, Complex.one_im]
      · rw [h, Complex.neg_im, Complex.one_im, neg_zero]
    rw [he, Complex.mul_re, him, zero_mul, sub_zero, fourPole_principal_summand_eq hx hn]

/-- If all eligible primes through the cutoff have value one, every eligible prime
power through the cutoff also has value one, by multiplicativity. -/
theorem fourPole_unit_prime_power_one {q a n : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hsmall : ∀ p : ℕ, p.Prime → Nat.Coprime p a → (p : ℝ) ≤ x → χ p = 1) (hpow : IsPrimePow n)
    (hcop : Nat.Coprime n a) (hcut : (n : ℝ) ≤ x) : χ n = 1 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
  have hc := (Nat.coprime_pow_left_iff hk _ _).mp hcop
  have hle : (p : ℝ) ≤ (p ^ k : ℕ) := Nat.cast_le.mpr (Nat.le_self_pow hk.ne' p)
  have hv := hsmall p hp hc (hle.trans hcut)
  simp only [Nat.cast_pow, map_pow, hv, one_pow]

/-- Under prime triviality through the cutoff, twice the truncated principal term is
bounded by the principal and character terms plus the exact nonunit local correction. -/
theorem fourPole_no_witness_term_le {q a : ℕ} (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic)
    {x : ℝ} (hx : 0 < x) (hsmall : ∀ p : ℕ, p.Prime → Nat.Coprime p a → (p : ℝ) ≤ x → χ p = 1)
    (n : ℕ) :
    (if n ∈ Finset.Ioc 0 ⌊x⌋₊ then 2 * (ArithmeticFunction.vonMangoldt n * fourScaledWeight x n)
      else 0) ≤
      ArithmeticFunction.vonMangoldt n * fourScaledWeight x n +
        ((MellinKernel.summand rationalPoleFourKernel) χ x n).re +
        (if n ∈ Finset.Ioc 0 ⌊x⌋₊ then if Nat.Coprime n a then 0 else fourPoleLocalTerm χ x n
        else 0) := by
  rw [fourPole_quadratic_summand_eq χ hq hx n]
  by_cases hcut : n ∈ Finset.Ioc 0 ⌊x⌋₊
  · rw [ite_eq_left hcut, ite_eq_left hcut]
    by_cases hc : Nat.Coprime n a
    · rw [ite_eq_left hc]
      by_cases hp : IsPrimePow n
      · have hnR : (n : ℝ) ≤ x :=
          (Nat.cast_le.mpr (Finset.mem_Ioc.mp hcut).2).trans (Nat.floor_le hx.le)
        rw [fourPole_unit_prime_power_one χ hsmall hp hc hnR, Complex.one_re, one_mul, add_zero]
        ring_nf
        exact le_rfl
      · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp]
        simp only [zero_mul, mul_zero, add_zero, le_refl]
    · rw [ite_eq_right hc]
      dsimp only [fourPoleLocalTerm]
      nlinarith only
  · rw [ite_eq_right hcut, ite_eq_right hcut, add_zero]
    have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * fourScaledWeight x n := by
      by_cases hn : n = 0
      · subst n
        rw [ArithmeticFunction.map_zero, zero_mul]
      · rw [← fourPole_principal_summand_eq hx hn]
        exact MellinKernel.principal_summand_re_nonneg rationalPoleFourKernel hx n
    rcases hq n with h | h | h
    · rw [h, Complex.zero_re, zero_mul, add_zero]
      exact hw
    · rw [h, Complex.one_re, one_mul]
      linarith only [hw]
    · rw [h, Complex.neg_re, Complex.one_re, neg_one_mul, add_neg_cancel]

/-- The full quadratic-character series is exactly its finite sum through the upper
support endpoint; the actual weight vanishes beyond that endpoint. -/
theorem fourPole_quadratic_sum_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) χ x n).re =
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (28 / 25 : ℝ) * x⌋₊,
        ((MellinKernel.summand rationalPoleFourKernel) χ x n).re := by
  have hs := MellinKernel.summable_summand rationalPoleFourKernel χ hx
  change Complex.reCLM (∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) χ x n) = _
  rw [Complex.reCLM.map_tsum hs]
  apply tsum_eq_sum
  intro n hn
  change ((MellinKernel.summand rationalPoleFourKernel) χ x n).re = 0
  by_cases hn0 : n = 0
  · subst n
    simp only [MellinKernel.summand, ite_true, Complex.zero_re]
  · have hlt : ⌊Real.exp (28 / 25 : ℝ) * x⌋₊ < n := by
      by_contra h
      exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, le_of_not_gt h⟩)
    have hnr : Real.exp (28 / 25 : ℝ) * x < (n : ℝ) := Nat.lt_of_floor_lt hlt
    rw [fourPole_quadratic_summand_eq χ hq hx n]
    dsimp only [fourScaledWeight]
    rw [fourPoleKernelWeight_zero_of_lt ((lt_div_iff₀ hx).mpr hnr), zero_div, mul_zero, mul_zero]

/-- Prime triviality on eligible primes through the cutoff forces the principal
cutoff gap below the full character series plus the exact ambient local cost.
Sum the pointwise comparison over the finite support. -/
theorem fourPole_no_witness_comparison {q a : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) {x : ℝ} (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → Nat.Coprime p a → (p : ℝ) ≤ x → χ p = 1) :
    2 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
        (∑' n : ℕ,
            (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ 1) x n).re ≤
      (∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) χ x n).re +
        fourPoleLocalCost χ a x := by
  let F := Finset.Ioc 0 ⌊Real.exp (28 / 25 : ℝ) * x⌋₊
  let S := Finset.Ioc 0 ⌊x⌋₊
  have hsub : S ⊆ F :=
    Finset.Ioc_subset_Ioc le_rfl
      (Nat.floor_mono
        (le_mul_of_one_le_left hx.le
          (Real.one_le_exp_iff.mpr (by norm_num only : (0 : ℝ) ≤ 28 / 25))))
  have h := Finset.sum_le_sum (s := F) (fun n _ ↦ fourPole_no_witness_term_le χ hq hx hsmall n)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hsub, ← Finset.mul_sum] at h
  have he :
    (∑ n ∈ F, if n ∈ S then if Nat.Coprime n a then 0 else fourPoleLocalTerm χ x n else 0) =
      fourPoleLocalCost χ a x := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    rw [fourPoleLocalCost, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hc : Nat.Coprime n a
    · rw [ite_eq_left hc, ite_eq_right (not_not_intro hc)]
    · rw [ite_eq_right hc, ite_eq_left hc]
  change
    (2 * ∑ n ∈ S, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) ≤
      (∑ n ∈ F, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) +
        (∑ n ∈ F, ((MellinKernel.summand rationalPoleFourKernel) χ x n).re) +
        (∑ n ∈ F, if n ∈ S then if Nat.Coprime n a then 0 else fourPoleLocalTerm χ x n else 0) at h
  rw [he, ← fourPole_principal_sum_finite hx, ← fourPole_quadratic_sum_finite χ hq hx] at h
  linarith only [h]

/-- Under GRH and primitive nonprincipal quadratic data, a strict explicit gap between
the principal main term and all Euler, contour, arithmetic and local errors produces
an eligible prime with non-one character value through the cutoff. -/
theorem fourPole_exists_prime_of_gap {q a : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hq : 2 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (A B : Finset ℕ)
    (hgap :
      rationalPoleFourEulerBudget χ A B + 3 + (24 * Real.log q + 793) * x ^ (-3 / 4 : ℝ) +
          (65 * x ^ (1 / 4 : ℝ) + 120 / Real.sqrt x) +
          fourPoleLocalCost χ a x <
        Real.sqrt x *
          (2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
            (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4))) :
    ∃ p : ℕ, p.Prime ∧ Nat.Coprime p a ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  by_contra hno
  have hsmall : ∀ p : ℕ, p.Prime → Nat.Coprime p a → (p : ℝ) ≤ x → χ p = 1 := by
    intro p hpp hpc hpx
    by_contra hpne
    exact hno ⟨p, hpp, hpc, hpx, hpne⟩
  have hc :=
    fourPole_no_witness_comparison χ hquad ((by norm_num only : (0 : ℝ) < 2).trans_le hx) hsmall
  have hP := fourPole_principal_gap_lower hGRH.riemann hx
  have hC :=
    rationalPole_four_smoothed_le hq hGRH hp hne hinv ((by norm_num only : (1 : ℝ) ≤ 2).trans hx) A
      B
  have hr := le_abs_self (∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) χ x n).re
  linarith only [hc, hP, hC, hr, hgap]

end PseudoPrime.LLS.PaperStatements
