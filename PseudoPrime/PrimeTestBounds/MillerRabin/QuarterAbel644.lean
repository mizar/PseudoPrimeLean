/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbel570
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Exact principal sums for the section 122 kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On any positive subinterval of the support, the principal sum has an exact
Abel formula with both endpoint atoms and the psi-weighted derivative integral. -/
theorem quarter_principal_abel_644 {X a b : ℝ} (hX : 0 < X) (ha : 0 < a) (hab : a ≤ b)
    (hb : Real.log (b / X) ≤ 2687 / 1000) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) X n).re) =
      quarterWeight644 X b * Chebyshev.psi b - quarterWeight644 X a * Chebyshev.psi a -
        ∫ t in a..b, deriv (quarterWeight644 X) t * Chebyshev.psi t := by
  have hc {t : ℝ} (ht : 0 < t) : ContDiffAt ℝ 1 (quarterWeight644 X) t := by
    have hs : ContDiffAt ℝ 1 Real.sqrt t := Real.contDiffAt_sqrt ht.ne'
    unfold quarterWeight644
    dsimp only
    fun_prop (disch := positivity)
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := hc (ha.trans_le ht.1)
  have hder : ContinuousOn (deriv (quarterWeight644 X)) (Set.Icc a b) := by
    have hu : ContDiffOn ℝ 1 (quarterWeight644 X) (Set.Ioi 0) := fun t ht ↦ (hc ht).contDiffWithinAt
    exact
      (hu.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono (fun t ht ↦ ha.trans_le ht.1)
  have hh :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt (by decide)) hder.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at hh
  simp only [← Chebyshev.psi_eq_sum_Icc] at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  have hnb := (Nat.le_floor_iff (ha.le.trans hab)).mp (Finset.mem_Ioc.mp hn).2
  exact
    quarter_summand_644 hX hn0
      ((Real.log_le_log (div_pos (Nat.cast_pos.mpr hn0) hX)
            (div_le_div_of_nonneg_right hnb hX.le)).trans
        hb)

/-- Terms beyond X exp(2687/1000) vanish, so the full real principal series is a finite sum. -/
theorem quarter_principal_finite_644 {X : ℝ} (hX : 0 < X) :
    (∑' n : ℕ, (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) X n).re) =
      ∑ n ∈ Finset.Ioc 0 ⌊X * Real.exp (2687 / 1000)⌋₊,
        (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) X n).re := by
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re]
  have hcut : ⌊X * Real.exp (2687 / 1000)⌋₊ < n := by
    by_contra h
    exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, le_of_not_gt h⟩)
  have hi : Real.exp (2687 / 1000) < (n : ℝ) / X :=
    (lt_div_iff₀ hX).mpr ((mul_comm _ X).trans_lt (Nat.lt_of_floor_lt hcut))
  have hp := (Real.exp_pos _).trans hi
  have hlog := Real.log_lt_log (Real.exp_pos _) hi
  rw [Real.log_exp] at hlog
  rw [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn0, quarterKernel644,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ hp, Analysis.rationalPoleProfile,
    ite_eq_right (fun h ↦ (not_lt_of_ge h.2) (by linarith only [hlog]))]
  simp only [Complex.ofReal_zero, mul_zero, Complex.zero_re]

end PseudoPrime.PrimeTestBounds.MillerRabin
