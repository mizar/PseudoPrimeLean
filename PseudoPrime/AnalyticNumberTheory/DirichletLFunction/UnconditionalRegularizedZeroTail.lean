/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalGenusTail
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogZeroTail

/-! # Uniform high-zero tails for the regularized logarithmic formula -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character with nonprincipal inverse, modulus
at least two, scale at least two, and any real height cutoff, the regularized
norm tail is at most the original norm tail plus `log 2` times its genus tail.
Use absolute summability, the pointwise triangle inequality, and the exact
definition of regularization. This separates the two quantitative tail inputs. -/
theorem tsum_norm_regularizedLogHalfZeroTerm_tail_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 2 ≤ x) (R : ℝ) :
    (∑' ρ : ℂ, if R ≤ |ρ.im| then ‖regularizedLogHalfZeroTerm χ x ρ‖ else 0) ≤
      (∑' ρ : ℂ, if R ≤ |ρ.im| then ‖completedLogHalfZeroTerm χ x ρ‖ else 0) +
        Real.log 2 *
          ∑' ρ : ℂ,
            if R ≤ |ρ.im| then
              ‖(MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
                  (1 / ((2 : ℂ) - ρ) + 1 / ρ)‖
            else 0 := by
  have hreg := (summable_regularizedLogHalfZeroTerm_unconditionally hq hp hne hinv hx).norm
  have hold := (summable_completedLogHalfZeroTerm_unconditionally hq hp hne hinv hx).norm
  have hgen :=
    (summable_completed_genus_terms_right hq hp hne hinv (s := 2)
        (by norm_num only [Complex.re_ofNat])).norm
  have hr := hreg.indicator {ρ : ℂ | R ≤ |ρ.im|}
  have ho := hold.indicator {ρ : ℂ | R ≤ |ρ.im|}
  have hg := hgen.indicator {ρ : ℂ | R ≤ |ρ.im|}
  change Summable (fun ρ : ℂ ↦ if R ≤ |ρ.im| then ‖regularizedLogHalfZeroTerm χ x ρ‖ else 0) at hr
  change Summable (fun ρ : ℂ ↦ if R ≤ |ρ.im| then ‖completedLogHalfZeroTerm χ x ρ‖ else 0) at ho
  change
    Summable
      (fun ρ : ℂ ↦
        if R ≤ |ρ.im| then
          ‖(MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
              (1 / ((2 : ℂ) - ρ) + 1 / ρ)‖
        else 0) at hg
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have hpoint (ρ : ℂ) :
    (if R ≤ |ρ.im| then ‖regularizedLogHalfZeroTerm χ x ρ‖ else 0) ≤
      (if R ≤ |ρ.im| then ‖completedLogHalfZeroTerm χ x ρ‖ else 0) +
        Real.log 2 *
          (if R ≤ |ρ.im| then
            ‖(MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
                (1 / ((2 : ℂ) - ρ) + 1 / ρ)‖
          else 0) := by
    by_cases hh : R ≤ |ρ.im|
    · rw [ite_eq_left hh, ite_eq_left hh, ite_eq_left hh]
      have hb :=
        norm_sub_le (completedLogHalfZeroTerm χ x ρ)
          ((Real.log 2 : ℂ) *
            ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
              (1 / ((2 : ℂ) - ρ) + 1 / ρ)))
      simpa only [regularizedLogHalfZeroTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hlog] using hb
    · rw [ite_eq_right hh, ite_eq_right hh, ite_eq_right hh, mul_zero, add_zero]
  have hb := hr.tsum_le_tsum hpoint (ho.add (hg.mul_left (Real.log 2)))
  rw [ho.tsum_add (hg.mul_left (Real.log 2)), tsum_mul_left] at hb
  exact hb

/-- There is a positive absolute local-count constant giving the displayed
regularized high-zero tail bound for all primitive nonprincipal characters with
nonprincipal inverse, moduli at least two, scales at least two, and integer
cutoffs at least two. Combine the original inverse-height tail with the uniform
genus correction of size `O(log q)`. No zero gap, RH, or unproved counting input
is assumed; both ordinate signs and actual multiplicities are retained. -/
theorem exists_tsum_norm_regularizedLogHalfZeroTerm_tail_bound_unconditionally :
    ∃ K : ℝ,
      0 < K ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (x : ℝ),
                  2 ≤ x →
                    ∀ (H : ℕ),
                      2 ≤ H →
                        (∑' ρ : ℂ,
                            if (H + 1 : ℕ) ≤ |ρ.im| then ‖regularizedLogHalfZeroTerm χ x ρ‖
                            else 0) ≤
                          24 * x * K * Real.log q / ((H - 1 : ℕ) : ℝ) +
                            192 * x * K * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) +
                            Real.log 2 *
                              (32 *
                                (12 +
                                  LogFreeDensity.completedGenusMassShiftConstant *
                                    (Real.log 4 + 1) +
                                  Real.log q +
                                  LogFreeDensity.completedGenusMassCenterConstant *
                                    (Real.log 4 + 1))) := by
  obtain ⟨K, hK, htail⟩ := exists_tsum_norm_completedLogHalfZeroTerm_tail_bound_unconditionally
  refine ⟨K, hK, ?_⟩
  intro q inst hq χ hp hne hinv x hx H hH
  have hc := tsum_norm_regularizedLogHalfZeroTerm_tail_le hq hp hne hinv hx (H + 1 : ℕ)
  have hg :=
    tsum_norm_completed_genus_tail_le_uniform_bound hq hp hne hinv (R := (H + 1 : ℕ))
      (by
        have hhr : (2 : ℝ) ≤ H := by exact_mod_cast hH
        norm_num only [Nat.cast_add, Nat.cast_one]
        linarith only [hhr])
  exact
    hc.trans
      (add_le_add (htail q hq χ hp hne hinv x hx H hH)
        (mul_le_mul_of_nonneg_left hg (Real.log_nonneg (by norm_num only))))

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
