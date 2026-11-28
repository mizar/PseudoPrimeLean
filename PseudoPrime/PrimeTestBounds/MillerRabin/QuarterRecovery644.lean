/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterConductor644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriple644

/-! # Radius monotonicity of the additional reflected recovery in section 122 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The radius-dependent factor of one reflected prime-power contribution.
The shift includes the logarithm of the prime power through the parameter v. -/
noncomputable def quarterRecoveryFactor (v r : ℝ) : ℝ :=
  r ^ (-(107 / 50) : ℝ) * (v + 2 * Real.log r) ^ 5

private theorem recovery_factor_deriv (v : ℝ) {r : ℝ} (hr : 0 < r) :
    let z := v + 2 * Real.log r
    HasDerivAt (quarterRecoveryFactor v) (r ^ (-(107 / 50) : ℝ) * z ^ 4 * (10 - (107 / 50) * z) / r)
      r := by
  intro z
  have h :=
    (Real.hasDerivAt_rpow_const (p := -(107 / 50 : ℝ)) (Or.inl hr.ne')).mul
      ((((Real.hasDerivAt_log hr.ne').const_mul 2).const_add v).pow 5)
  apply h.congr_deriv
  rw [Real.rpow_sub_one hr.ne']
  dsimp only [z, Pi.pow_apply]
  field_simp [hr.ne']
  ring

private theorem recovery_log_lower {r : ℝ} (hr : 316 ≤ r) : 4 ≤ Real.log r := by
  have hp : 0 < r := by linarith only [hr]
  have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
  apply (Real.le_log_iff_exp_le hp).mpr
  rw [show (4 : ℝ) = (4 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
  linarith only [he, hr]

/-- At radius at least 316, a nonnegative shift makes the reflected factor
decrease: the negative power dominates the logarithmic fifth power. -/
theorem quarter_recovery_factor_antitone {v : ℝ} (hv : 0 ≤ v) :
    AntitoneOn (quarterRecoveryFactor v) (Set.Icc 316 322) := by
  have hd (r : ℝ) (hr : r ∈ Set.Icc 316 322) :=
    recovery_factor_deriv v (show 0 < r by linarith only [hr.1])
  apply
    antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun r hr ↦ (hd r hr).continuousAt.continuousWithinAt)
      (fun r hr ↦ (hd r (interior_subset hr)).differentiableAt.differentiableWithinAt)
  intro r hr
  have hi : r ∈ Set.Icc (316 : ℝ) 322 := interior_subset hr
  have hl := recovery_log_lower hi.1
  have hp : 0 ≤ r := by linarith only [hi.1]
  rw [(hd r hi).deriv]
  exact
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (Real.rpow_nonneg hp _) (pow_nonneg (by linarith only [hv, hl]) 4))
        (by linarith only [hv, hl]))
      hp

/-- The additional section 122 reflected recovery uses the fixed Mangoldt
sum on (2701,99000]. Its terms include the radius factor and Mellin constant. -/
noncomputable def quarterRecovery644 (r : ℝ) : ℝ :=
  (4 * (107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120) *
    ∑ m ∈ Finset.Ioc 2701 99000,
      (ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(157 / 100) : ℝ)) *
        quarterRecoveryFactor (2687 / 1000 + Real.log m) r

/-- The reflected recovery on the entire section 122 radius interval is at
least its value at 322. Nonnegative Mangoldt weights preserve each termwise
comparison, so the same endpoint certificate will serve all four rows. -/
theorem quarter_recovery_at_322 {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    quarterRecovery644 322 ≤ quarterRecovery644 r := by
  unfold quarterRecovery644
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro m hm
  have hm1 : (1 : ℝ) ≤ m := by
    exact_mod_cast (show 1 ≤ m from (by decide : 1 ≤ 2701).trans (Finset.mem_Ioc.mp hm).1.le)
  have hv : 0 ≤ (2687 / 1000 : ℝ) + Real.log m := by linarith only [Real.log_nonneg hm1]
  exact
    mul_le_mul_of_nonneg_left
      (quarter_recovery_factor_antitone hv hr (Set.right_mem_Icc.mpr (by norm_num only)) hr.2)
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _))

/-- On the reflected tail above 2701, the trace bound pays at most one
copy of each nonnegative weight. On (2701,99000] the trace is three, so
four copies are recovered. The result retains the radius-322 recovery. -/
theorem quarter_reflected_recovery_644 {r : ℝ} (hr : r ∈ Set.Icc 316 322) {N : ℕ} (hN : 99000 ≤ N)
    (τ : ℕ → ℝ) (ht : ∀ m, -1 ≤ τ m)
    (hpass : ∀ m ∈ Finset.Ioc 2701 99000, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3) :
    let C := (107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120
    let W := fun m : ℕ ↦
      (ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(157 / 100) : ℝ)) *
        quarterRecoveryFactor (2687 / 1000 + Real.log m) r
    C * (∑ m ∈ Finset.Ioc 2701 N, -τ m * W m) ≤
      C * (∑ m ∈ Finset.Ioc 2701 N, W m) - quarterRecovery644 322 := by
  intro C W
  have hW {m : ℕ} (hm : m ∈ Finset.Ioc 99000 N) : 0 ≤ W m := by
    have hm1 : (1 : ℝ) ≤ m := by
      exact_mod_cast (show 1 ≤ m from (by decide : 1 ≤ 99000).trans (Finset.mem_Ioc.mp hm).1.le)
    have hlog := Real.log_nonneg hm1
    have hl := recovery_log_lower hr.1
    have hp : 0 ≤ r := by linarith only [hr.1]
    exact
      mul_nonneg
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _))
        (mul_nonneg (Real.rpow_nonneg hp _) (pow_nonneg (by linarith only [hlog, hl]) 5))
  have hlo :
    (∑ m ∈ Finset.Ioc 2701 99000, -τ m * W m) = (-3 : ℝ) * ∑ m ∈ Finset.Ioc 2701 99000, W m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hΛ : ArithmeticFunction.vonMangoldt m = 0
    · simp only [W, hΛ, zero_mul, mul_zero]
    · rw [hpass m hm hΛ]
  have hhi : (∑ m ∈ Finset.Ioc 99000 N, -τ m * W m) ≤ ∑ m ∈ Finset.Ioc 99000 N, W m :=
    Finset.sum_le_sum
      (fun m hm ↦ by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (neg_le.mpr (ht m)) (hW hm))
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have h := quarter_recovery_at_322 hr
  have hEq : quarterRecovery644 r = 4 * C * (∑ m ∈ Finset.Ioc 2701 99000, W m) := by
    unfold quarterRecovery644
    dsimp only [C, W]
    ring
  rw [hEq] at h
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (by decide : 2701 ≤ 99000) hN,
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl),
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl), hlo]
  nlinarith only [h, mul_le_mul_of_nonneg_left hhi hC]

/-- The prime-passing hypothesis at the square cutoff forces trace
three on the Mangoldt support of the recovered interval for all four rows. -/
theorem quarter_recovery_trace_644 {p q s : ℕ} {r : ℝ} (hr : r ∈ Set.Icc 316 322)
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) {m : ℕ} (hm : m ∈ Finset.Ioc 2701 99000)
    (hΛ : ArithmeticFunction.vonMangoldt m ≠ 0) : (a m).re + (b m).re + (c m).re = 3 := by
  have hR : (99000 : ℝ) ≤ r ^ 2 := by nlinarith only [hr.1, sq_nonneg (r - 316)]
  have hmR : (m : ℝ) ≤ r ^ 2 := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hm).2).trans hR
  have h (d : ℕ) (χ : DirichletCharacter ℂ d) (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → χ l = 1) :
    χ m = 1 :=
    AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
      (fun l hl hlX _ ↦ hχ l hl hlX) hmR (Nat.coprime_one_right m) hΛ
  rw [h p a hA, h q b hB, h s c hC, Complex.one_re]
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
