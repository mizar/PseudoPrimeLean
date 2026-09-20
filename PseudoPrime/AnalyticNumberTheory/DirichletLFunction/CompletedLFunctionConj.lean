/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Conjugation symmetry of the completed Dirichlet `L`-function

The conjugation identity underlying
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.primitiveBRe_inv_eq` is
`conj (completedLFunction χ s) = completedLFunction χ⁻¹ (conj s)`, with the
corresponding value and derivative consequences at `s = 0`.

The key structural fact is that `DirichletCharacter.completedLFunction` reduces to a **finite**
sum (`ZMod.completedLFunction`) of `completedHurwitzZetaEven`/`Odd` terms, each built (via
`hurwitzEvenFEPair`/`hurwitzOddFEPair`) from a `WeakFEPair` whose defining kernel `f`, `g`, and
constants `f₀`, `g₀`, `ε`, `k` are all real (cast into `ℂ`). For real-valued `f`,
conjugating the Mellin-transform integrand
`(t:ℂ)^(s-1) • f t` replaces `s` by `conj s`; the integrand need not itself be real.
Conjugation commutes with the integral
(`Complex.conj_cpow` for the real-positive base `t`, plus `integral_conj`). This propagates through
the finite-sum structure without ever needing analytic continuation or an identity theorem.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: a function `f : ℝ → ℂ` that is real-valued (`conj (f t) = f t` for every `t`),
and a point `s : ℂ`.
Conclusion: `conj (mellin f s) = mellin f (conj s)`.
Content: `mellin f s = ∫ t in Ioi 0, (t:ℂ)^(s-1) • f t`; conjugating the integral (`integral_conj`)
and, termwise, the real-positive-base power (`Complex.conj_cpow`, since `(t:ℂ).arg = 0 ≠ π` for
`t > 0`) and the real value `f t` (hypothesis) recovers the same integral at `conj s`.
Role: the elementary real-integrand conjugation fact underlying every other lemma in this file.
-/
theorem mellin_conj {f : ℝ → ℂ} (hfreal : ∀ t, (starRingEnd ℂ) (f t) = f t) (s : ℂ) :
    (starRingEnd ℂ) (mellin f s) = mellin f (starRingEnd ℂ s) := by
  rw [mellin, mellin, ← integral_conj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [smul_eq_mul, map_mul, hfreal]
  have hxarg : ((t : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact Real.pi_pos.ne'.symm
  have hxconj : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  have hcp := Complex.conj_cpow (t : ℂ) (s - 1) hxarg
  rw [hxconj] at hcp
  rw [hcp, Complex.conj_conj]
  congr 1
  simp only [map_sub, map_one]

/--
Input/assumptions: a `WeakFEPair ℂ` whose kernel `f` and constants `f₀`, `g₀`, `ε` are all real
(fixed by conjugation).
Conclusion: `conj (P.f_modif x) = P.f_modif x` for every `x : ℝ`.
Content: `f_modif` is built from `f`, `f₀`, `g₀`, `ε` and real powers of `x` by a three-way case
split on `x` versus `1` (the `Ioi 1`/`Ioo 0 1` indicator regions of its definition); each branch
is real-valued given the hypotheses.
Role: feeds `PseudoPrime.AnalyticNumberTheory.DirichletLFunction.mellin_conj`
to conjugate `Λ₀ := mellin f_modif`.
-/
theorem WeakFEPair.f_modif_conj (P : WeakFEPair ℂ) (hf : ∀ x, (starRingEnd ℂ) (P.f x) = P.f x)
    (hf0 : (starRingEnd ℂ) P.f₀ = P.f₀) (hg0 : (starRingEnd ℂ) P.g₀ = P.g₀)
    (hε : (starRingEnd ℂ) P.ε = P.ε) (x : ℝ) : (starRingEnd ℂ) (P.f_modif x) = P.f_modif x := by
  classical
  unfold WeakFEPair.f_modif
  simp only [Pi.add_apply]
  rcases lt_trichotomy x 1 with hx1 | hx1 | hx1
  · have hnotIoi : x ∉ Set.Ioi (1 : ℝ) := by
      simp only [Set.mem_Ioi, not_lt.mpr hx1.le, not_false_eq_true]
    by_cases hx0 : 0 < x
    · have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
      rw [Set.indicator_of_notMem hnotIoi, Set.indicator_of_mem hx01]
      simp only [zero_add, map_sub, smul_eq_mul, map_mul, hε, hg0, hf]
      congr 2
      rw [Complex.conj_ofReal]
    · have hnotIoo : x ∉ Set.Ioo (0 : ℝ) 1 := by
        simp only [Set.mem_Ioo, hx0, false_and, not_false_eq_true]
      rw [Set.indicator_of_notMem hnotIoi, Set.indicator_of_notMem hnotIoo]
      simp only [add_zero, map_zero]
  · subst hx1
    have hnotIoi : (1 : ℝ) ∉ Set.Ioi (1 : ℝ) := by
      simp only [Set.mem_Ioi, lt_self_iff_false, not_false_eq_true]
    have hnotIoo : (1 : ℝ) ∉ Set.Ioo (0 : ℝ) 1 := by
      simp only [Set.mem_Ioo, zero_lt_one, lt_self_iff_false, and_false, not_false_eq_true]
    rw [Set.indicator_of_notMem hnotIoi, Set.indicator_of_notMem hnotIoo]
    simp only [add_zero, map_zero]
  · have hmemIoi : x ∈ Set.Ioi (1 : ℝ) := hx1
    have hnotIoo : x ∉ Set.Ioo (0 : ℝ) 1 := fun h => absurd h.2 (not_lt.mpr hx1.le)
    rw [Set.indicator_of_mem hmemIoi, Set.indicator_of_notMem hnotIoo]
    simp only [add_zero, map_sub, hf, hf0]

/--
Input/assumptions: as `PseudoPrime.AnalyticNumberTheory.DirichletLFunction.WeakFEPair.f_modif_conj`.
Conclusion: `conj (P.Λ₀ s) = P.Λ₀ (conj s)`.
Content: `Λ₀ := mellin P.f_modif`;
apply `PseudoPrime.AnalyticNumberTheory.DirichletLFunction.mellin_conj` with
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.WeakFEPair.f_modif_conj`.
-/
theorem WeakFEPair.Λ₀_conj (P : WeakFEPair ℂ) (hf : ∀ x, (starRingEnd ℂ) (P.f x) = P.f x)
    (hf0 : (starRingEnd ℂ) P.f₀ = P.f₀) (hg0 : (starRingEnd ℂ) P.g₀ = P.g₀)
    (hε : (starRingEnd ℂ) P.ε = P.ε) (s : ℂ) :
    (starRingEnd ℂ) (P.Λ₀ s) = P.Λ₀ (starRingEnd ℂ s) := by
  unfold WeakFEPair.Λ₀
  exact mellin_conj (WeakFEPair.f_modif_conj P hf hf0 hg0 hε) s

/--
Input/assumptions: as `WeakFEPair.Λ₀_conj`, plus `P.k : ℝ` fixed by conjugation (automatic, since
`k : ℝ` cast into `ℂ`).
Conclusion: `conj (P.Λ s) = P.Λ (conj s)`.
Content: `Λ s := Λ₀ s - (1/s) • f₀ - (ε/(k-s)) • g₀`; conjugate termwise using `Λ₀_conj` and the
reality hypotheses on `f₀`, `g₀`, `ε`, `k`.
Role: the meromorphic-continuation-level conjugation identity, specialized below to the even/odd
Hurwitz zeta completions.
-/
theorem WeakFEPair.Λ_conj (P : WeakFEPair ℂ) (hf : ∀ x, (starRingEnd ℂ) (P.f x) = P.f x)
    (hf0 : (starRingEnd ℂ) P.f₀ = P.f₀) (hg0 : (starRingEnd ℂ) P.g₀ = P.g₀)
    (hε : (starRingEnd ℂ) P.ε = P.ε) (hk : (starRingEnd ℂ) (P.k : ℂ) = (P.k : ℂ)) (s : ℂ) :
    (starRingEnd ℂ) (P.Λ s) = P.Λ (starRingEnd ℂ s) := by
  unfold WeakFEPair.Λ
  rw [map_sub, map_sub, WeakFEPair.Λ₀_conj P hf hf0 hg0 hε, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, map_mul, map_mul, map_div₀, map_div₀, map_one, hf0, hε, hg0, map_sub, hk]

/--
Input/assumptions: a `UnitAddCircle` point `a` and `s : ℂ`.
Conclusion: `conj (completedHurwitzZetaEven a s) = completedHurwitzZetaEven a (conj s)`.
Content: `hurwitzEvenFEPair a` has real `f := ofReal ∘ evenKernel a`, `g := ofReal ∘ cosKernel a`,
`f₀ := if a = 0 then 1 else 0`, `g₀ := 1`, `ε := 1`, `k := 1/2`; `WeakFEPair.Λ_conj` applies at
`s / 2`.
Role: the even-parity half of the completed-`L` conjugation symmetry.
-/
theorem HurwitzZeta.completedHurwitzZetaEven_conj (a : UnitAddCircle) (s : ℂ) :
    (starRingEnd ℂ) (HurwitzZeta.completedHurwitzZetaEven a s) =
      HurwitzZeta.completedHurwitzZetaEven a (starRingEnd ℂ s) := by
  unfold HurwitzZeta.completedHurwitzZetaEven
  have hf :
    ∀ x,
      (starRingEnd ℂ) ((HurwitzZeta.hurwitzEvenFEPair a).f x) =
        (HurwitzZeta.hurwitzEvenFEPair a).f x := by
    intro x
    unfold HurwitzZeta.hurwitzEvenFEPair
    simp only [Function.comp_apply, Complex.conj_ofReal]
  have hf0 :
    (starRingEnd ℂ) (HurwitzZeta.hurwitzEvenFEPair a).f₀ =
      (HurwitzZeta.hurwitzEvenFEPair a).f₀ := by
    unfold HurwitzZeta.hurwitzEvenFEPair
    split
    · simp only [map_one]
    · simp only [map_zero]
  have hg0 :
    (starRingEnd ℂ) (HurwitzZeta.hurwitzEvenFEPair a).g₀ =
      (HurwitzZeta.hurwitzEvenFEPair a).g₀ := by
    unfold HurwitzZeta.hurwitzEvenFEPair
    simp only [map_one]
  have hε :
    (starRingEnd ℂ) (HurwitzZeta.hurwitzEvenFEPair a).ε = (HurwitzZeta.hurwitzEvenFEPair a).ε := by
    unfold HurwitzZeta.hurwitzEvenFEPair
    simp only [map_one]
  have hk :
    (starRingEnd ℂ) ((HurwitzZeta.hurwitzEvenFEPair a).k : ℂ) =
      ((HurwitzZeta.hurwitzEvenFEPair a).k : ℂ) := by
    unfold HurwitzZeta.hurwitzEvenFEPair
    rw [Complex.conj_ofReal]
  have hΛ := WeakFEPair.Λ_conj (HurwitzZeta.hurwitzEvenFEPair a) hf hf0 hg0 hε hk (s / 2)
  simp only [map_div₀, map_ofNat, hΛ]

/--
Input/assumptions: a `UnitAddCircle` point `a` and `s : ℂ`.
Conclusion: `conj (completedHurwitzZetaOdd a s) = completedHurwitzZetaOdd a (conj s)`.
Content: identical strategy to `completedHurwitzZetaEven_conj`, using `hurwitzOddFEPair a`
(`k := 3/2`, `f₀ = g₀ = 0`) and `WeakFEPair.Λ_conj` at `(s + 1) / 2`.
Role: the odd-parity half of the completed-`L` conjugation symmetry.
-/
theorem HurwitzZeta.completedHurwitzZetaOdd_conj (a : UnitAddCircle) (s : ℂ) :
    (starRingEnd ℂ) (HurwitzZeta.completedHurwitzZetaOdd a s) =
      HurwitzZeta.completedHurwitzZetaOdd a (starRingEnd ℂ s) := by
  unfold HurwitzZeta.completedHurwitzZetaOdd
  have hf :
    ∀ x,
      (starRingEnd ℂ) ((HurwitzZeta.hurwitzOddFEPair a).f x) =
        (HurwitzZeta.hurwitzOddFEPair a).f x := by
    intro x
    unfold HurwitzZeta.hurwitzOddFEPair
    simp only [Function.comp_apply, Complex.conj_ofReal]
  have hf0 :
    (starRingEnd ℂ) (HurwitzZeta.hurwitzOddFEPair a).f₀ = (HurwitzZeta.hurwitzOddFEPair a).f₀ := by
    unfold HurwitzZeta.hurwitzOddFEPair
    simp only [map_zero]
  have hg0 :
    (starRingEnd ℂ) (HurwitzZeta.hurwitzOddFEPair a).g₀ = (HurwitzZeta.hurwitzOddFEPair a).g₀ := by
    unfold HurwitzZeta.hurwitzOddFEPair
    simp only [map_zero]
  have hε :
    (starRingEnd ℂ) (HurwitzZeta.hurwitzOddFEPair a).ε = (HurwitzZeta.hurwitzOddFEPair a).ε := by
    unfold HurwitzZeta.hurwitzOddFEPair
    simp only [map_one]
  have hk :
    (starRingEnd ℂ) ((HurwitzZeta.hurwitzOddFEPair a).k : ℂ) =
      ((HurwitzZeta.hurwitzOddFEPair a).k : ℂ) := by
    unfold HurwitzZeta.hurwitzOddFEPair
    rw [Complex.conj_ofReal]
  have hΛ := WeakFEPair.Λ_conj (HurwitzZeta.hurwitzOddFEPair a) hf hf0 hg0 hε hk ((s + 1) / 2)
  have hsplit : (starRingEnd ℂ) ((s + 1) / 2) = ((starRingEnd ℂ) s + 1) / 2 := by
    rw [map_div₀, map_add, map_one, map_ofNat]
  rw [hsplit] at hΛ
  simp only [map_div₀, map_ofNat, hΛ]

/-- `conj (N^s) = N^(conj s)` for a natural-number base cast into `ℂ`, via `Complex.conj_cpow`
(the base's argument is `0 ≠ π`). -/
theorem Complex.conj_cpow_natCast (N : ℕ) (s : ℂ) :
    (starRingEnd ℂ) ((N : ℂ) ^ s) = (N : ℂ) ^ (starRingEnd ℂ) s := by
  have hxarg : ((N : ℂ)).arg ≠ Real.pi := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · simp only [h0, Nat.cast_zero, Complex.arg_zero, ne_eq]
      exact Real.pi_pos.ne'.symm
    · rw [show ((N : ℂ)) = ((N : ℝ) : ℂ) from by
          push_cast; ring,
        Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg N)]
      exact Real.pi_pos.ne'.symm
  have hNconj : (starRingEnd ℂ) (N : ℂ) = (N : ℂ) := by
    rw [show ((N : ℂ)) = ((N : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.conj_ofReal]
  have hcp := Complex.conj_cpow ((N : ℂ)) s hxarg
  rw [hNconj] at hcp
  rw [hcp, Complex.conj_conj]

/--
Input/assumptions: a positive level `N`, a function `Φ : ZMod N → ℂ`, and `s : ℂ`.
Conclusion: `conj (ZMod.completedLFunction Φ s) = ZMod.completedLFunction (conj ∘ Φ) (conj s)`.
Content: `ZMod.completedLFunction Φ s := N^{-s} · Σ_j Φ(j) · completedHurwitzZetaEven(toAddCircle j,
s) + N^{-s} · Σ_j Φ(j) · completedHurwitzZetaOdd(toAddCircle j, s)` (a **finite** sum over
`j : ZMod N`); conjugate `N^{-s}` via `conj_cpow_natCast` and each summand via
`completedHurwitzZetaEven_conj`/`completedHurwitzZetaOdd_conj`.
Role: lifts the even/odd conjugation symmetry to the level of `ZMod.completedLFunction`, the
building block `DirichletCharacter.completedLFunction` is literally defined to equal.
-/
theorem ZMod.completedLFunction_conj {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (s : ℂ) :
    (starRingEnd ℂ) (ZMod.completedLFunction Φ s) =
      ZMod.completedLFunction (fun j => (starRingEnd ℂ) (Φ j)) (starRingEnd ℂ s) := by
  unfold ZMod.completedLFunction
  rw [map_add, map_mul, map_mul, Complex.conj_cpow_natCast N (-s), map_neg]
  congr 2
  · rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, HurwitzZeta.completedHurwitzZetaEven_conj]
  · rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, HurwitzZeta.completedHurwitzZetaOdd_conj]

/--
Input/assumptions: a positive level `N`, a complex Dirichlet character `χ` of level `N`, and
`s : ℂ`.
Conclusion: `conj (completedLFunction χ s) = completedLFunction χ⁻¹ (conj s)`.
Content: `DirichletCharacter.completedLFunction χ s := ZMod.completedLFunction (⇑χ) s`;
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZMod.completedLFunction_conj`
reduces the claim to `(fun j => conj (χ j)) = ⇑χ⁻¹`, which is
`MulChar.star_apply'` (the conjugation step) pointwise.
Role: supplies the value symmetry used by `primitiveBRe_inv_eq` in `PrimitiveFunctionalEquation`.
-/
theorem DirichletCharacter.completedLFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) :
    (starRingEnd ℂ) (DirichletCharacter.completedLFunction χ s) =
      DirichletCharacter.completedLFunction χ⁻¹ (starRingEnd ℂ s) := by
  rw [DirichletCharacter.completedLFunction, ZMod.completedLFunction_conj,
    DirichletCharacter.completedLFunction]
  congr 1
  funext j
  have := MulChar.star_apply' χ j
  simp only [RCLike.star_def] at this
  exact this

/--
Input/assumptions: a positive level `N`, a complex Dirichlet character `χ` of level `N` with
`χ ≠ 1`.
Conclusion: `conj (deriv (completedLFunction χ) 0) = deriv (completedLFunction χ⁻¹) 0`.
Content: differentiate
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.DirichletCharacter.completedLFunction_conj`
at `s := 0` via
`HasDerivAt.conj_conj` (`HasDerivAt f f' x → HasDerivAt (conj ∘ f ∘ conj) (conj f') (conj x)`):
since `conj ∘ F(χ) ∘ conj = F(χ⁻¹)` (pointwise, from the value identity) and `conj 0 = 0`, the
resulting `HasDerivAt F(χ⁻¹) (conj (deriv F(χ) 0)) 0` must agree with `F(χ⁻¹)`'s own derivative at
`0` by uniqueness.
Role: supplies derivative conjugation at zero for the completed logarithmic derivative.
-/
theorem DirichletCharacter.deriv_completedLFunction_zero_conj {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) :
    (starRingEnd ℂ) (deriv (DirichletCharacter.completedLFunction χ) 0) =
      deriv (DirichletCharacter.completedLFunction χ⁻¹) 0 := by
  have hinvne : χ⁻¹ ≠ 1 := fun h => hne (by rw [← inv_inv χ, h, inv_one])
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hdiffinv := DirichletCharacter.differentiable_completedLFunction hinvne
  have hd0 :
    HasDerivAt (DirichletCharacter.completedLFunction χ)
      (deriv (DirichletCharacter.completedLFunction χ) 0) 0 :=
    (hdiff 0).hasDerivAt
  have hcc := hd0.conj_conj
  have heqfun :
    (starRingEnd ℂ) ∘ (DirichletCharacter.completedLFunction χ) ∘ (starRingEnd ℂ) =
      DirichletCharacter.completedLFunction χ⁻¹ := by
    funext z
    simp only [Function.comp_apply]
    rw [DirichletCharacter.completedLFunction_conj, Complex.conj_conj]
  rw [heqfun, map_zero] at hcc
  exact ((hdiffinv 0).hasDerivAt.unique hcc).symm

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
