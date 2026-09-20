/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.GRH.TrivialZeros
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Generalized Riemann hypothesis for Dirichlet L-functions

GRH includes all primitive complex Dirichlet characters, including the character of modulus one.
Its modulus-one specialization is equivalent to RH; the open-strip API serves the existing bounds.

This predicate is the general GRH interface used by the analytic-number-theory modules below.
-/

namespace PseudoPrime.AnalyticNumberTheory.GRH

/-- Input: a character. Assertion: every zero outside the cast of its integer-valued trivial-zero
set lies on the critical line. This per-character predicate is specialized at modulus one to
recover RH. -/
def DirichletRiemannHypothesis {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ,
    χ.LFunction s = 0 → s ∉ (Int.cast : ℤ → ℂ) '' dirichletTrivialZeros χ → s.re = (1 : ℝ) / 2

/--
The generalized Riemann hypothesis for all primitive Dirichlet characters.

Input: a positive modulus and primitive character. Assertion: all nontrivial zeros lie on the
critical line. Includes modulus one, so it supplies both the zeta and character estimates.
-/
@[wikidata Q685140]
def GeneralizedRiemannHypothesis : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → DirichletRiemannHypothesis χ

/-- Modulus-one Dirichlet RH is exactly RH. The proof identifies its L-function with zeta;
the excluded pole value is nonzero in mathlib. Used to extract RH from GRH. -/
theorem dirichletRiemannHypothesis_one_iff :
    DirichletRiemannHypothesis (1 : DirichletCharacter ℂ 1) ↔ RiemannHypothesis := by
  have htriv (s : ℂ) :
    s ∉ (Int.cast : ℤ → ℂ) '' ({z : ℤ | ∃ n : ℕ, z = -2 * ((n : ℤ) + 1)} : Set ℤ) ↔
      ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    constructor
    · intro hs h
      rcases h with ⟨n, hn⟩
      apply hs
      refine ⟨-2 * ((n : ℤ) + 1), ⟨n, rfl⟩, ?_⟩
      calc
        ((-2 * ((n : ℤ) + 1) : ℤ) : ℂ) = -2 * ((n : ℂ) + 1) := by
          norm_num only [Int.cast_neg, Int.cast_mul, Int.cast_add, Int.cast_natCast]
        _ = s := hn.symm
    · intro hs h
      rcases h with ⟨z, ⟨n, hn⟩, hz⟩
      apply hs
      refine ⟨n, ?_⟩
      calc
        s = (z : ℂ) := hz.symm
        _ = ((-2 * ((n : ℤ) + 1) : ℤ) : ℂ) := by rw [← hn]
        _ = -2 * ((n : ℂ) + 1) := by
          norm_num only [Int.cast_neg, Int.cast_mul, Int.cast_add, Int.cast_natCast]
  simp only [DirichletRiemannHypothesis, DirichletCharacter.LFunction_modOne_eq,
    dirichletTrivialZeros, RiemannHypothesis, ite_eq_left]
  simp only [htriv]
  constructor
  · intro h s hs ht _; exact h s hs ht
  · intro h s hs ht; exact h s hs ht (fun he => riemannZeta_one_ne_zero (he ▸ hs))

/-- GRH implies RH by applying the modulus-one equivalence to the primitive trivial character.
Supplies the RH input of existing zeta estimates without an independent assumption. -/
theorem GeneralizedRiemannHypothesis.riemann (h : GeneralizedRiemannHypothesis) :
    RiemannHypothesis := by
  have hDirichlet : DirichletRiemannHypothesis 1 :=
    h 1 1 DirichletCharacter.isPrimitive_one_level_one
  exact dirichletRiemannHypothesis_one_iff.mp hDirichlet

/-- Trivial zeros have nonpositive real part, hence cannot lie in the open critical strip.
Input: positive real part. Output: exclusion from the prescribed set, for the strip adapter. -/
theorem not_mem_dirichletTrivialZeros_of_re_pos {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) : s ∉ (Int.cast : ℤ → ℂ) '' dirichletTrivialZeros χ := by
  classical
  unfold dirichletTrivialZeros
  split_ifs <;> rintro ⟨z, ⟨n, rfl⟩, rfl⟩ <;>
    norm_num only [Int.cast_neg, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast,
      Complex.mul_re, Complex.neg_re, Complex.re_ofNat, Complex.add_re, Complex.natCast_re,
      Complex.one_re, Complex.sub_re, Complex.neg_im, Complex.intCast_re, Complex.im_ofNat,
      Complex.natCast_im] at hs <;>
    nlinarith only [hs, Nat.cast_nonneg (α := ℝ) n]

/--
Input: GRH, a primitive character, and a zero with positive real part.
Output: real part one half.
Proof: positive real part excludes every trivial zero. Preserves the analytic consumers' API. -/
theorem GeneralizedRiemannHypothesis.zero_re_eq_half (h : GeneralizedRiemannHypothesis) (q : ℕ)
    [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (s : ℂ) (hz : χ.LFunction s = 0)
    (hpos : 0 < s.re) : s.re = (1 : ℝ) / 2 := by
  exact h q χ hp s hz (not_mem_dirichletTrivialZeros_of_re_pos χ hpos)

end PseudoPrime.AnalyticNumberTheory.GRH
