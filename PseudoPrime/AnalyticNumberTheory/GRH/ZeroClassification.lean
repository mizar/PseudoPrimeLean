/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.GRH.TrivialZeroExistence
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation

/-! # Unconditional classification of primitive nonprincipal Dirichlet
L-function zeros outside the closed critical strip -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.GRH

/-- A primitive nonprincipal character zero at nonpositive real part forces
its gamma factor to vanish. Otherwise it is a completed zero, contradicting
reflection and right-half-plane nonvanishing. No GRH assumption is used. -/
theorem gammaFactor_eq_zero_of_LFunction_zero_re_nonpos {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive) (hne : χ ≠ 1) {s : ℂ} (hz : χ.LFunction s = 0)
    (hs : s.re ≤ 0) : χ.gammaFactor s = 0 := by
  by_contra hΓ
  have he :=
    DirichletLFunction.dirichletLFunction_eq_completed_div_gammaFactor χ s
      (Or.inr (DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one hne))
  have hc : χ.completedLFunction s = 0 := (div_eq_zero_iff.mp (he.symm.trans hz)).resolve_right hΓ
  exact
    (not_lt_of_ge hs) (DirichletLFunction.completedLFunction_zero_re_pos hp (inv_ne_one.mpr hne) hc)

/-- Every gamma-forced point of a nonprincipal character lies in its prescribed
integer-valued trivial-zero set, embedded into the complex numbers. Split
parity and use the exact zeros of GammaR; no primitivity is required. -/
theorem mem_trivialZeros_of_gammaFactor_eq_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hne : χ ≠ 1) {s : ℂ} (hΓ : χ.gammaFactor s = 0) :
    s ∈ (Int.cast : ℤ → ℂ) '' dirichletTrivialZeros χ := by
  have hN := DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one hne
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hΓ
    obtain ⟨n, rfl⟩ := hΓ
    refine ⟨-2 * (n : ℤ), ?_, ?_⟩
    · simp only [dirichletTrivialZeros, ite_eq_right hN, ite_eq_right he.not_odd]
      exact ⟨n, rfl⟩
    · simp only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, neg_mul]
  · rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hΓ
    obtain ⟨n, hn⟩ := hΓ
    refine ⟨-2 * (n : ℤ) - 1, ?_, ?_⟩
    · simp only [dirichletTrivialZeros, ite_eq_right hN, ite_eq_left ho]
      exact ⟨n, rfl⟩
    · simp only [Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast,
        Int.cast_one, neg_mul]
      exact (eq_sub_of_add_eq hn).symm

/-- A primitive nonprincipal L-function zero outside 0<=Re(s)<=1 is a
prescribed trivial zero. The right half-plane is zero-free and the left
half-plane forces a gamma zero. This unconditional theorem complements GRH. -/
theorem mem_trivialZeros_of_LFunction_zero_outside_strip {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive) (hne : χ ≠ 1) {s : ℂ} (hz : χ.LFunction s = 0)
    (hout : ¬(0 ≤ s.re ∧ s.re ≤ 1)) : s ∈ (Int.cast : ℤ → ℂ) '' dirichletTrivialZeros χ := by
  have hr : s.re < 1 :=
    lt_of_not_ge fun h ↦ DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) h hz
  have hl : s.re < 0 := lt_of_not_ge fun h ↦ hout ⟨h, hr.le⟩
  exact
    mem_trivialZeros_of_gammaFactor_eq_zero χ hne
      (gammaFactor_eq_zero_of_LFunction_zero_re_nonpos χ hp hne hz hl.le)

end PseudoPrime.AnalyticNumberTheory.GRH
