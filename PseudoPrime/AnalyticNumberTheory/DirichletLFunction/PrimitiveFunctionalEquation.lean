/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardLimit
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveCharacterInv
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedLFunctionConj
import PseudoPrime.AnalyticNumberTheory.RiemannXi.HadamardLimit

/-!
# Functional equations and zero-mass estimates for primitive characters

The pair `(χ,χ⁻¹)` gives reflection of completed zeros and a logarithmic-derivative
functional equation. Under GRH, the zeros lie on the critical line and their mass equals
`|primitiveBRe χ|`. Conjugation identifies the constants for inverse characters.
The resulting estimates control weighted zero sums, the derivative at zero, and truncated
genus sums. No quadratic-character assumption or LLS numerical inequality is used.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: a positive level `N` and a complex Dirichlet character `χ` of level `N`.
Conclusion: `χ⁻¹.gammaFactor = χ.gammaFactor` (as functions of `s`).
Content: `gammaFactor` depends on `χ` only through its parity (`Even.gammaFactor_def`:
`s.Gammaℝ`; `Odd.gammaFactor_def`: `(s+1).Gammaℝ`, both independent of `χ`, `N` otherwise);
`DirichletLFunction.DirichletCharacter.even_inv_iff`/`odd_inv_iff` (the conjugation step-derived)
transport `χ`'s parity to `χ⁻¹`.
Role: the conjugation identity, needed to relate `L = completedL / gammaFactor` for `χ` and `χ⁻¹`
with the *same*
archimedean factor.
-/
theorem DirichletCharacter.gammaFactor_inv_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) : χ⁻¹.gammaFactor s = χ.gammaFactor s := by
  rcases χ.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def,
      (DirichletCharacter.even_inv_iff.mpr
          heven).gammaFactor_def]
  · rw [hodd.gammaFactor_def,
      (DirichletCharacter.odd_inv_iff.mpr
          hodd).gammaFactor_def]

/--
Input/assumptions: GRH, a primitive nontrivial complex Dirichlet character with `χ⁻¹ ≠ 1`, and a
completed-`L` zero.
Conclusion: that zero has real part `1 / 2`.
Content: the counterpart of `completedLFunction_zero_re_eq_half_of_grh_quadratic`
that drops the quadratic hypothesis: instead of collapsing `χ⁻¹` back to `χ` via self-duality, the
reflected zero of `χ⁻¹` is ruled out directly by applying GRH-driven nonvanishing to `χ⁻¹` itself
(using `hinv` in place of `hquad.inv`).
Role: supplies critical-line classification to zero-mass and summability estimates.
-/
theorem completedLFunction_zero_re_eq_half_of_grh {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {ρ : ℂ}
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0) : ρ.re = (1 : ℝ) / 2 := by
  have hstep1 :
    ∀ (ψ : DirichletCharacter ℂ N),
      ψ ≠ 1 → ∀ s : ℂ, DirichletCharacter.completedLFunction ψ s = 0 → 1 ≤ s.re → False := by
    intro ψ hψne s hs0 hs1
    have hsne0 : s ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hs1
      linarith
    have heq :=
      dirichletLFunction_eq_completed_div_gammaFactor
        ψ s (Or.inl hsne0)
    rw [hs0, zero_div] at heq
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψne) hs1 heq
  have hlt1 : ρ.re < 1 := by
    by_contra h
    push Not at h
    exact hstep1 χ hne ρ hzero h
  have hgt0 : 0 < ρ.re := by
    by_contra h
    push Not at h
    set s := 1 - ρ with hs_def
    have hs_eq : (1 : ℂ) - s = ρ := by
      rw [hs_def]
      ring
    have hcompleted_one_sub : DirichletCharacter.completedLFunction χ (1 - s) = 0 := by
      rw [hs_eq]
      exact hzero
    have hzero_s : DirichletCharacter.completedLFunction χ⁻¹ s = 0 :=
      dirichletCompletedLFunction_inv_zero_of_one_sub_zero
        hprimitive s hcompleted_one_sub
    have hsre : 1 ≤ s.re := by
      have hsre_eq : s.re = 1 - ρ.re := by
        rw [hs_def]
        simp only [Complex.sub_re, Complex.one_re]
      rw [hsre_eq]
      linarith
    exact hstep1 χ⁻¹ hinv s hzero_s hsre
  have hρne0 : ρ ≠ 0 := by
    intro h
    rw [h] at hgt0
    simp only [Complex.zero_re, lt_self_iff_false] at hgt0
  have hL0 : DirichletCharacter.LFunction χ ρ = 0 := by
    have heq :=
      dirichletLFunction_eq_completed_div_gammaFactor
        χ ρ (Or.inl hρne0)
    rw [hzero, zero_div] at heq
    exact heq
  exact hGRH.zero_re_eq_half N χ hprimitive ρ hL0 hgt0

/--
Input/assumptions: a nontrivial complex Dirichlet character and a point with nonzero divisor
multiplicity (for the global `Set.univ` divisor).
Conclusion: the completed `L`-function vanishes there.
Content: contrapositive of
`DirichletLFunction.meromorphicOrderAt_dirichletCompletedLFunction_eq_zero_of_ne_zero`
(a nonzero value forces order, hence divisor, zero).
-/
theorem dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {ρ : ℂ}
    (hρ : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ ≠ 0) :
    DirichletCharacter.completedLFunction χ ρ = 0 := by
  by_contra hρne
  apply hρ
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ =>
    hdiff.analyticAt z
  rw [MeromorphicOn.divisor_apply hanalytic.meromorphicOn (Set.mem_univ ρ),
    meromorphicOrderAt_dirichletCompletedLFunction_eq_zero_of_ne_zero
      hne hρne]
  rfl

/--
Input/assumptions: a point on the critical line `Re ρ = 1 / 2`.
Conclusion: the genus-one term's real part collapses to twice the real part of `1 / ρ`.
Content: on the critical line `1 - ρ = conj ρ`, so `1 / (1 - ρ) = conj (1 / ρ)` has the same real
part as `1 / ρ`.
-/
theorem genusOneTerm_re_eq_of_re_eq_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    (1 / (1 - ρ) + 1 / ρ).re = 2 * (1 / ρ).re := by
  have hconj : (1 : ℂ) - ρ = starRingEnd ℂ ρ := by
    have h1 : (1 - ρ).re = (starRingEnd ℂ ρ).re := by
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith [hρ]
    have h2 : (1 - ρ).im = (starRingEnd ℂ ρ).im := by
      simp only [Complex.sub_im, Complex.one_im, zero_sub, Complex.conj_im]
    exact Complex.ext h1 h2
  simp only [hconj, one_div, ← map_inv₀ (starRingEnd ℂ) ρ, Complex.add_re, Complex.conj_re]
  ring

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive nontrivial complex Dirichlet character with
`χ⁻¹ ≠ 1`.
Conclusion: half the real part of the global Hadamard genus-one `tsum` equals the classical
zero-mass sum `Σ' ρ, m_ρ Re(1 / ρ)`.
Content: identical to `dirichletCompletedLFunctionQuadraticZeroMass_eq_tsum_re_inv` but with the
zero classification supplied by the `hquad`-free
`DirichletLFunction.completedLFunction_zero_re_eq_half_of_grh`
(applying GRH to `χ⁻¹` in place of self-duality).
Role: relates the genus sum to the real zero mass used in zero-contribution bounds.
-/
theorem dirichletCompletedLFunctionZeroMass_eq_tsum_re_inv {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (1 / 2 : ℝ) *
        (∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (1 / (1 - ρ) + 1 / ρ)).re =
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re := by
  have hsummable :=
    summable_completedLFunctionGenusOneTerm_one
      hN2 hprimitive hne hinv
  have hpt :
    ∀ ρ : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
            (1 / (1 - ρ) + 1 / ρ)).re =
        2 *
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re) := by
    intro ρ
    set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
    by_cases hD0 : D = 0
    · simp only [hD0, Int.cast_zero, one_div, zero_mul, Complex.zero_re, Complex.inv_re, mul_zero]
    · have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
        dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
          hne hD0
      have hre_half : ρ.re = (1 : ℝ) / 2 :=
        completedLFunction_zero_re_eq_half_of_grh
          hGRH hprimitive hne hinv hzero
      have hterm :=
        genusOneTerm_re_eq_of_re_eq_half
          hre_half
      have hcast : ((D : ℤ) : ℂ) = (((D : ℤ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, Complex.re_ofReal_mul, hterm]
      ring
  rw [Complex.re_tsum hsummable, tsum_congr hpt, tsum_mul_left]
  ring

/--
Input/assumptions: a primitive complex Dirichlet character with `χ ≠ 1` and `χ⁻¹ ≠ 1`, and a point
`s : ℂ`.
Conclusion: the completed-`L` divisor of `χ⁻¹` at `s` equals the completed-`L` divisor of `χ` at
the reflected point `1 - s`.
Content: from `F(χ)(1-z) = c(z) * F(χ⁻¹)(z)` with `c(z) := N^(z-1/2) * rootNumber χ` everywhere
nonzero and entire (so `analyticOrderAt c z = 0` for every `z`), `analyticOrderAt_mul` gives
`analyticOrderAt (fun z => F(χ)(1-z)) s = analyticOrderAt (F(χ⁻¹)) s`. Separately,
`analyticOrderAt_comp_of_deriv_ne_zero` applied to `g z := 1 - z` (`deriv g s = -1 ≠ 0`) gives
`analyticOrderAt (F(χ) ∘ g) s = analyticOrderAt (F(χ)) (1 - s)`. Chaining the two and converting
`analyticOrderAt` to `MeromorphicOn.divisor` via `MeromorphicOn.AnalyticOnNhd.divisor_apply` (both
`F(χ)` and `F(χ⁻¹)` being entire) gives the claim.
Role: the key reflection identity for the generic application route `Z_χ = Z_{χ⁻¹}` zero-mass
symmetry, needed
to eventually pair `DirichletLFunction.primitiveBRe χ` with `DirichletLFunction.primitiveBRe χ⁻¹`
without a quadratic hypothesis.
-/
theorem completedLFunction_divisor_inv_apply_eq_reflect {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (s : ℂ) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ⁻¹) Set.univ s =
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ (1 - s) := by
  have hdiffχ := DirichletCharacter.differentiable_completedLFunction hne
  have hdiffχinv := DirichletCharacter.differentiable_completedLFunction hinv
  have hAnχ : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ =>
    hdiffχ.analyticAt z
  have hAnχinv : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ⁻¹) Set.univ := fun z _ =>
    hdiffχinv.analyticAt z
  have hrootne : DirichletCharacter.rootNumber χ ≠ 0 :=
    dirichletCharacter_rootNumber_ne_zero_of_isPrimitive
      hprimitive
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  set c : ℂ → ℂ := fun z => (N : ℂ) ^ (z - 1 / 2) * DirichletCharacter.rootNumber χ with hc_def
  have hcdiff : Differentiable ℂ c :=
    ((differentiable_id.sub_const (1 / 2 : ℂ)).const_cpow (Or.inl hNne)).mul_const _
  have hcanalytic : ∀ z, AnalyticAt ℂ c z := fun z => hcdiff.analyticAt z
  have hcne : ∀ z, c z ≠ 0 := fun z =>
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hNne)) hrootne
  have hfeq :
    ∀ z,
      DirichletCharacter.completedLFunction χ (1 - z) =
        c z * DirichletCharacter.completedLFunction χ⁻¹ z :=
    dirichletCompletedLFunction_one_sub_of_isPrimitive
      hprimitive
  have horder_c : ∀ z, analyticOrderAt c z = 0 := fun z =>
    (hcanalytic z).analyticOrderAt_eq_zero.mpr (hcne z)
  have hg : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) - z) s := analyticAt_const.sub analyticAt_id
  have hgderiv : deriv (fun z : ℂ => (1 : ℂ) - z) s ≠ 0 := by
    have : deriv (fun z : ℂ => (1 : ℂ) - z) s = -1 := by simp only [deriv_const_sub_id']
    rw [this]
    norm_num only
  have hLHS :
    analyticOrderAt (fun z => DirichletCharacter.completedLFunction χ (1 - z)) s =
      analyticOrderAt (DirichletCharacter.completedLFunction χ) (1 - s) :=
    analyticOrderAt_comp_of_deriv_ne_zero (f := DirichletCharacter.completedLFunction χ) hg hgderiv
  have hRHS :
    analyticOrderAt (fun z => DirichletCharacter.completedLFunction χ (1 - z)) s =
      analyticOrderAt (DirichletCharacter.completedLFunction χ⁻¹) s := by
    have heq2 :
      (fun z => DirichletCharacter.completedLFunction χ (1 - z)) =
        c * DirichletCharacter.completedLFunction χ⁻¹ :=
      funext hfeq
    rw [heq2, analyticOrderAt_mul (hcanalytic s) (hAnχinv s (Set.mem_univ s)), horder_c, zero_add]
  have horderEq :
    analyticOrderAt (DirichletCharacter.completedLFunction χ⁻¹) s =
      analyticOrderAt (DirichletCharacter.completedLFunction χ) (1 - s) := by
    rw [← hRHS, hLHS]
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAnχinv (Set.mem_univ s),
    MeromorphicOn.AnalyticOnNhd.divisor_apply hAnχ (Set.mem_univ (1 - s)), horderEq]

/--
Input/assumptions: GRH, a primitive complex Dirichlet character with `χ ≠ 1` and `χ⁻¹ ≠ 1`.
Conclusion: the real zero mass of `χ⁻¹` equals the real zero mass of `χ`:
`Σ' ρ, m_ρ(χ⁻¹) Re(1/ρ) = Σ' ρ, m_ρ(χ) Re(1/ρ)`.
Content: termwise, `DirichletLFunction.completedLFunction_divisor_inv_apply_eq_reflect` rewrites
the `χ⁻¹`-divisor at
`ρ` as the `χ`-divisor at `1 - ρ`; where that divisor is nonzero, `1 - ρ` is a zero of `F(χ)`, so
GRH (`DirichletLFunction.completedLFunction_zero_re_eq_half_of_grh`) forces `Re ρ = 1 / 2`, whence
`1 - ρ = conj ρ`
and `Re(1/ρ) = Re(1/(1-ρ))`. The resulting sum `Σ' ρ, m_ρ(χ)(1-ρ) Re(1/(1-ρ))` is exactly the
`χ`-zero-mass reindexed along the involutive equivalence `Equiv.subLeft 1 : ρ ↦ 1 - ρ`
(`Equiv.tsum_eq`), which collapses back to the unreindexed `χ`-zero-mass.
Role: supplies the zero-mass reflection symmetry for the inverse-character pair.
-/
theorem dirichletCompletedLFunctionZeroMass_inv_eq_of_grh {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ⁻¹) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re) =
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re := by
  have hpt :
    ∀ ρ : ℂ,
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ⁻¹) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re =
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ (1 - ρ) : ℤ) :
            ℝ) *
          (1 / (1 - ρ)).re := by
    intro ρ
    rw [completedLFunction_divisor_inv_apply_eq_reflect
        hprimitive hne hinv ρ]
    set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ (1 - ρ) with
      hD_def
    by_cases hD0 : D = 0
    · simp only [hD0, Int.cast_zero, one_div, Complex.inv_re, zero_mul, Complex.sub_re,
        Complex.one_re]
    · have hzero : DirichletCharacter.completedLFunction χ (1 - ρ) = 0 :=
        dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
          hne hD0
      have hre_half : (1 - ρ).re = (1 : ℝ) / 2 :=
        completedLFunction_zero_re_eq_half_of_grh
          hGRH hprimitive hne hinv hzero
      have hρre : ρ.re = 1 / 2 := by
        simp only [Complex.sub_re, Complex.one_re] at hre_half
        linarith
      have hg :=
        genusOneTerm_re_eq_of_re_eq_half hρre
      have hsplit : (1 / (1 - ρ) + 1 / ρ).re = (1 / (1 - ρ)).re + (1 / ρ).re := Complex.add_re _ _
      have hswap : (1 / (1 - ρ)).re = (1 / ρ).re := by linarith [hg, hsplit]
      rw [hswap]
  rw [tsum_congr hpt]
  exact
    Equiv.tsum_eq (Equiv.subLeft (1 : ℂ))
      (fun t =>
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ t : ℤ) : ℝ) *
          (1 / t).re)

/--
Input/assumptions: a positive natural number.
Conclusion: the log-derivative of `z ↦ (N : ℂ) ^ (z - 1 / 2)` is the constant `Complex.log N`.
Content: `HasDerivAt.const_cpow` gives the derivative `N ^ (s - 1/2) * log N`; dividing by the
(nonzero) function value cancels the `cpow` factor.
-/
theorem logDeriv_level_cpow_sub_half (N : ℕ) (hN : N ≠ 0) (s : ℂ) :
    logDeriv (fun z : ℂ => (N : ℂ) ^ (z - 1 / 2)) s = Complex.log N := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hf : HasDerivAt (fun z : ℂ => z - 1 / 2) 1 s := by
    simpa only [one_div, hasDerivAt_sub_const_iff, id_eq] using
      (hasDerivAt_id s).sub_const (1 / 2 : ℂ)
  have hderiv := hf.const_cpow (c := (N : ℂ)) (Or.inl hNne)
  have hne : (N : ℂ) ^ (s - 1 / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hNne)
  rw [logDeriv_apply, hderiv.deriv, mul_one, mul_div_cancel_left₀ _ hne]

/--
Input/assumptions: a primitive nontrivial complex Dirichlet character (no self-duality assumed),
and a point `s` where the completed `L`-function of `χ⁻¹` doesn't vanish.
Conclusion: the pair-system functional equation's log-derivative at the reflection pair
`(s, 1 - s)`, taken across the character and its inverse:
`-logDeriv F(χ) (1 - s) = Complex.log N + logDeriv F(χ⁻¹) s`.
Content: differentiate `F(χ) (1 - z) = N ^ (z - 1/2) * rootNumber χ * F(χ⁻¹) z` in `z` at `s`,
using the chain rule on the left and `logDeriv_mul`/`logDeriv_mul_const`/
`DirichletLFunction.logDeriv_level_cpow_sub_half` on the right (`logDeriv_mul` needs `F(χ⁻¹) s ≠
0`, the only place
nonvanishing enters). This is the general counterpart of
`completedLFunction_logDeriv_functionalEquation_isQuadratic_at`: for a self-dual `χ` (`χ⁻¹ = χ`)
it specializes to that single-function statement.
Role: `completedLFunction_logDeriv_functionalEquation_isQuadratic_at` is now a corollary of this
pair-system version, substituting `hquad.inv : χ⁻¹ = χ`.
-/
theorem completedLFunction_logDeriv_functionalEquation_at {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {s : ℂ}
    (hFs : DirichletCharacter.completedLFunction χ⁻¹ s ≠ 0) :
    -logDeriv (DirichletCharacter.completedLFunction χ) (1 - s) =
      Complex.log N + logDeriv (DirichletCharacter.completedLFunction χ⁻¹) s := by
  have hinvne : χ⁻¹ ≠ 1 := fun h => hne (by rw [← inv_inv χ, h, inv_one])
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hdiffinv := DirichletCharacter.differentiable_completedLFunction hinvne
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hrootne : DirichletCharacter.rootNumber χ ≠ 0 :=
    dirichletCharacter_rootNumber_ne_zero_of_isPrimitive hprimitive
  have hfeq : ∀ z : ℂ, DirichletCharacter.completedLFunction χ (1 - z) =
      (N : ℂ) ^ (z - 1 / 2) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ z :=
    dirichletCompletedLFunction_one_sub_of_isPrimitive hprimitive
  have hLHS : logDeriv (fun z : ℂ => DirichletCharacter.completedLFunction χ (1 - z)) s =
      -logDeriv (DirichletCharacter.completedLFunction χ) (1 - s) := by
    have hg : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
      simpa only [id_eq] using (hasDerivAt_id s).const_sub (1 : ℂ)
    have hcomp := logDeriv_comp (f := DirichletCharacter.completedLFunction χ)
      (g := fun z : ℂ => 1 - z) (x := s) hdiff.differentiableAt hg.differentiableAt
    have hcompEq : (DirichletCharacter.completedLFunction χ ∘ fun z : ℂ => 1 - z) =
        (fun z : ℂ => DirichletCharacter.completedLFunction χ (1 - z)) := rfl
    rw [hcompEq, hg.deriv] at hcomp
    simpa only [mul_neg, mul_one] using hcomp
  have hRHS : logDeriv (fun z : ℂ => (N : ℂ) ^ (z - 1 / 2) * DirichletCharacter.rootNumber χ *
      DirichletCharacter.completedLFunction χ⁻¹ z) s =
      Complex.log N + logDeriv (DirichletCharacter.completedLFunction χ⁻¹) s := by
    have hfacthd : HasDerivAt (fun z : ℂ => z - 1 / 2) 1 s := by
      simpa only [one_div, hasDerivAt_sub_const_iff, id_eq] using
        (hasDerivAt_id s).sub_const (1 / 2 : ℂ)
    have hfactd : DifferentiableAt ℂ (fun z : ℂ => (N : ℂ) ^ (z - 1 / 2)) s :=
      (hfacthd.const_cpow (c := (N : ℂ)) (Or.inl hNne)).differentiableAt
    have hfactne : (N : ℂ) ^ (s - 1 / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hNne)
    have hgroupne : (N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ ≠ 0 :=
      mul_ne_zero hfactne hrootne
    have hgroupd : DifferentiableAt ℂ
        (fun z : ℂ => (N : ℂ) ^ (z - 1 / 2) * DirichletCharacter.rootNumber χ) s :=
      hfactd.mul_const _
    rw [show (fun z : ℂ => (N : ℂ) ^ (z - 1 / 2) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ z) =
        (fun z : ℂ => (N : ℂ) ^ (z - 1 / 2) * DirichletCharacter.rootNumber χ) *
          (fun z : ℂ => DirichletCharacter.completedLFunction χ⁻¹ z) from by
            funext z
            simp only [Pi.mul_apply]
            ,
      logDeriv_mul s hgroupne hFs hgroupd (hdiffinv.differentiableAt),
      logDeriv_mul_const s (DirichletCharacter.rootNumber χ) hrootne,
      logDeriv_level_cpow_sub_half N (NeZero.ne N) s]
  have hcombine : logDeriv (fun z : ℂ => DirichletCharacter.completedLFunction χ (1 - z)) s =
      logDeriv (fun z : ℂ => (N : ℂ) ^ (z - 1 / 2) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ z) s := by
    congr 1
    funext z
    exact hfeq z
  rw [← hLHS, hcombine, hRHS]

/--
Definition: `Re(logDeriv (completedLFunction χ) 0) + (1/2) log χ.conductor`.
Input: any complex Dirichlet character of nonzero level.
For a primitive character the conductor is the level `N`; multiplying mathlib's
completed function `F(s)` by `N^(s/2)` adds `(1/2) log N` to its logarithmic derivative.
Role: records the real Hadamard constant in that conductor-scaled normalization.
-/
noncomputable def primitiveBRe {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℝ :=
  (logDeriv (DirichletCharacter.completedLFunction χ) 0).re + (1 / 2) * Real.log χ.conductor

/--
Input/assumptions: a primitive complex Dirichlet character with `χ ≠ 1` and `χ⁻¹ ≠ 1`.
Conclusion: the pair-system functional equation's log-derivative specialized to `s = 0`:
`-logDeriv F(χ) 1 = Complex.log N + logDeriv F(χ⁻¹) 0`.
Content: `DirichletLFunction.completedLFunction_logDeriv_functionalEquation_at` at `s := 0`, using
`DirichletLFunction.DirichletCharacter.isPrimitive_inv` and
`DirichletLFunction.dirichletCompletedLFunction_zero_ne_zero_of_primitive`
for the nonvanishing hypothesis on `F(χ⁻¹)`, and `sub_zero` to simplify `1 - 0` to `1`.
Role: the `hquad`-free counterpart of `completedLFunction_logDeriv_functionalEquation_isQuadratic`,
feeding the paired `DirichletLFunction.primitiveBRe` conclusion below.
-/
theorem completedLFunction_logDeriv_functionalEquation_at_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    -logDeriv (DirichletCharacter.completedLFunction χ) 1 =
      Complex.log N + logDeriv (DirichletCharacter.completedLFunction χ⁻¹) 0 := by
  have hprimitiveinv : χ⁻¹.IsPrimitive :=
    DirichletCharacter.isPrimitive_inv
      hprimitive
  have hF0ne : DirichletCharacter.completedLFunction χ⁻¹ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive
      hprimitiveinv hinv
  have h :=
    completedLFunction_logDeriv_functionalEquation_at
      hprimitive hne (s := 0) hF0ne
  simpa only [sub_zero] using h

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: `DirichletLFunction.primitiveBRe χ + DirichletLFunction.primitiveBRe χ⁻¹ = -2 Z_χ`,
where `Z_χ` is the real zero mass
`Σ' ρ, m_ρ(χ) Re(1/ρ)` of `χ` itself.
Content: take real parts of the centered identity for `χ`
(`DirichletLFunction.completedLFunction_centeredLogDeriv_one_eq_tsum`, `L₁(χ) - L₀(χ) = 2 Z_χ` via
`DirichletLFunction.dirichletCompletedLFunctionZeroMass_eq_tsum_re_inv`) and of the pair-system
functional-equation log-derivative at `s = 0`
(`DirichletLFunction.completedLFunction_logDeriv_functionalEquation_at_zero`, `-L₁(χ) = log N +
L₀(χ⁻¹)`), then
`linarith` to eliminate `L₁(χ)` and isolate `L₀(χ⁻¹) + log N` in terms of `L₀(χ)` and `Z_χ`. Adding
`DirichletLFunction.primitiveBRe χ = L₀(χ) + (1/2) log N` and `DirichletLFunction.primitiveBRe χ⁻¹
= L₀(χ⁻¹) + (1/2) log N` (both via
`DirichletLFunction.DirichletCharacter.isPrimitive_inv` identifying `χ⁻¹.conductor = N`) collapses
the two
`(1/2) log N` and `log N` terms and cancels `L₀(χ)`, leaving `-2 Z_χ`.
Role: supplies the pair-sum identity; `primitiveBRe_inv_eq` reduces it to a single-character
identity.
-/
theorem primitiveBRe_add_inv_eq_neg_two_mul_zeroMass_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    primitiveBRe χ +
        primitiveBRe χ⁻¹ =
      -(2 *
          ∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
              (1 / ρ).re) := by
  have hprimitiveinv : χ⁻¹.IsPrimitive :=
    DirichletCharacter.isPrimitive_inv
      hprimitive
  have hH9g :=
    completedLFunction_centeredLogDeriv_one_eq_tsum
      hN2 hprimitive hne hinv
  have hH6 :=
    dirichletCompletedLFunctionZeroMass_eq_tsum_re_inv
      hN2 hGRH hprimitive hne hinv
  have hG5 :=
    completedLFunction_logDeriv_functionalEquation_at_zero
      hprimitive hne hinv
  have hlogNre : (Complex.log (N : ℂ)).re = Real.log N := by
    rw [show ((N : ℂ)) = ((N : ℝ) : ℂ) from by
        push_cast; ring]
    exact Complex.log_ofReal_re _
  have hre9g :
    (logDeriv (DirichletCharacter.completedLFunction χ) 1).re -
        (logDeriv (DirichletCharacter.completedLFunction χ) 0).re =
      (∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
            (1 / (1 - ρ) + 1 / ρ)).re := by
    have := congrArg Complex.re hH9g
    simpa only [one_div, Complex.sub_re] using this
  have hre5 :
    -(logDeriv (DirichletCharacter.completedLFunction χ) 1).re =
      Real.log N + (logDeriv (DirichletCharacter.completedLFunction χ⁻¹) 0).re := by
    have := congrArg Complex.re hG5
    simpa only [Complex.neg_re, Complex.add_re, hlogNre] using this
  rw [primitiveBRe,
    primitiveBRe,
    (hprimitive : χ.conductor = N), (hprimitiveinv : χ⁻¹.conductor = N)]
  linarith [hre9g, hre5, hH6]

/--
Input/assumptions: GRH and a primitive nontrivial complex Dirichlet character with `χ⁻¹ ≠ 1`
(no self-duality assumed).
Conclusion: the real zero mass `Z_χ = Σ' ρ, m_ρ Re(1/ρ)` is nonnegative.
Content: identical to `primitiveZeroMass_nonneg_of_grh_quadratic` but with the zero classification
supplied by the `hquad`-free `DirichletLFunction.completedLFunction_zero_re_eq_half_of_grh`.
Role: supplies the sign needed to convert the Hadamard constant to an absolute value.
-/
theorem primitiveZeroMass_nonneg_of_grh {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    0 ≤
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ =>
    hdiff.analyticAt z
  apply tsum_nonneg
  intro ρ
  set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
  by_cases hD0 : D = 0
  · simp only [hD0, Int.cast_zero, one_div, Complex.inv_re, zero_mul, Std.le_refl]
  · have hDnonneg : (0 : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic ρ
    have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
        hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_grh
        hGRH hprimitive hne hinv hzero
    have hinv_re_pos : 0 ≤ (1 / ρ).re := by
      rw [one_div, Complex.inv_re, hre_half]
      exact div_nonneg (by norm_num only) (Complex.normSq_nonneg ρ)
    exact mul_nonneg hDnonneg hinv_re_pos

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: `Z_χ = |DirichletLFunction.primitiveBRe χ + DirichletLFunction.primitiveBRe χ⁻¹| / 2`,
where `Z_χ` is the real zero mass
`Σ' ρ, m_ρ(χ) Re(1/ρ)` of `χ` itself.
Content: `DirichletLFunction.primitiveBRe_add_inv_eq_neg_two_mul_zeroMass_of_grh` gives
`DirichletLFunction.primitiveBRe χ +
DirichletLFunction.primitiveBRe χ⁻¹ = -(2 Z_χ)`; taking absolute values and using
`DirichletLFunction.primitiveZeroMass_nonneg_of_grh`
(`Z_χ ≥ 0`) collapses `|-(2 Z_χ)|` to `2 Z_χ`, then dividing by `2` gives the claim.
Role: expresses the real zero mass using the inverse-character pair of Hadamard constants.
-/
theorem zeroMass_eq_abs_primitiveBRe_add_inv_div_two_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re) =
      |primitiveBRe χ +
            primitiveBRe χ⁻¹| /
        2 := by
  have hsum :=
    primitiveBRe_add_inv_eq_neg_two_mul_zeroMass_of_grh
      hN2 hGRH hprimitive hne hinv
  have hZnonneg :=
    primitiveZeroMass_nonneg_of_grh hGRH
      hprimitive hne hinv
  rw [hsum, abs_neg,
    abs_of_nonneg
      (by linarith :
        (0 : ℝ) ≤
          2 *
            ∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) *
                (1 / ρ).re)]
  ring

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive nontrivial complex Dirichlet character with
`χ⁻¹ ≠ 1` (no self-duality assumed).
Conclusion: the inverse-square zero mass `Σ' ρ, m_ρ / |ρ|²` converges.
Content: identical to `summable_divisor_div_normSq_of_grh_quadratic` but with the zero
classification supplied by the `hquad`-free
`DirichletLFunction.completedLFunction_zero_re_eq_half_of_grh`.
Role: justifies the norm-sum estimates for weighted completed zeros.
-/
theorem summable_divisor_div_normSq_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Summable
      (fun ρ : ℂ =>
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ) := by
  have hsummable :=
    summable_completedLFunctionGenusOneTerm_one
      hN2 hprimitive hne hinv
  have hsummableRe := Complex.reCLM.summable hsummable
  apply hsummableRe.congr
  intro ρ
  set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
  by_cases hD0 : D = 0
  · simp only [hD0, Int.cast_zero, one_div, zero_mul, Complex.reCLM_apply, Complex.zero_re,
      zero_div]
  · have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
        hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_grh
        hGRH hprimitive hne hinv hzero
    have hterm :=
      genusOneTerm_re_eq_of_re_eq_half hre_half
    have hInvRe : (1 / ρ).re = (1 : ℝ) / 2 / Complex.normSq ρ := by
      rw [one_div, Complex.inv_re, hre_half]
    have hcast : ((D : ℤ) : ℂ) = (((D : ℤ) : ℝ) : ℂ) := by
      push_cast
      ring
    change Complex.reCLM (((D : ℤ) : ℂ) * (1 / (1 - ρ) + 1 / ρ)) = ((D : ℤ) : ℝ) / Complex.normSq ρ
    rw [Complex.reCLM_apply, hcast, Complex.re_ofReal_mul, hterm, hInvRe]
    ring

/--
Input/assumptions: GRH, a primitive nontrivial complex Dirichlet character with `χ⁻¹ ≠ 1`
(no self-duality assumed), a positive real `x`, and any `ρ : ℂ`.
Conclusion: `‖D_ρ x^{ρ-1}/(ρ(ρ-1))‖ = (D_ρ/normSq ρ)/√x`.
Content: identical to `norm_completedReciprocalZeroTerm_eq` but with the zero classification
supplied by the `hquad`-free `DirichletLFunction.completedLFunction_zero_re_eq_half_of_grh`.
Role: provides the pointwise reciprocal zero-term identity for finite and infinite sums.
-/
theorem norm_completedReciprocalZeroTerm_eq_of_grh {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
            (x : ℂ) ^ (ρ - 1) /
          (ρ * (ρ - 1))‖ =
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ) /
        Real.sqrt x := by
  set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
  by_cases hD0 : D = 0
  · simp only [hD0, Int.cast_zero, zero_mul, zero_div, norm_zero]
  · have hDnonneg : (0 : ℝ) ≤ (D : ℝ) := by
      have hdiff := DirichletCharacter.differentiable_completedLFunction hne
      have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
        fun z _ => hdiff.analyticAt z
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic ρ
    have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
        hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_grh
        hGRH hprimitive hne hinv hzero
    have hconj : (1 : ℂ) - ρ = starRingEnd ℂ ρ := by
      have h1 : (1 - ρ).re = (starRingEnd ℂ ρ).re := by
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith [hre_half]
      have h2 : (1 - ρ).im = (starRingEnd ℂ ρ).im := by
        simp only [Complex.sub_im, Complex.one_im, zero_sub, Complex.conj_im]
      exact Complex.ext h1 h2
    have hprod : ρ * (ρ - 1) = -(Complex.normSq ρ : ℂ) := by
      have : ρ - 1 = -starRingEnd ℂ ρ := by
        rw [← hconj]
        ring
      rw [this, mul_neg, Complex.mul_conj]
    have hnormprod : ‖ρ * (ρ - 1)‖ = Complex.normSq ρ := by
      rw [hprod, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg ρ)]
    have hnormpow : ‖(x : ℂ) ^ (ρ - 1)‖ = 1 / Real.sqrt x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re, hre_half,
        show (1 : ℝ) / 2 - 1 = -(1 / 2 : ℝ) from by ring, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow,
        one_div]
    rw [norm_div, norm_mul, Complex.norm_intCast, abs_of_nonneg hDnonneg, hnormpow, hnormprod]
    ring

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: the inverse-square zero mass `Σ' ρ, m_ρ / |ρ|²` equals `2 * Z_χ`, where `Z_χ` is the
real zero mass `Σ' ρ, m_ρ Re(1/ρ)` of `χ` itself.
Content: identical rescaling to `tsum_divisor_inv_normSq_eq_two_mul_abs_BRe` (`Re(1/ρ) = 1/(2
normSq ρ)` on the critical line, via
`DirichletLFunction.completedLFunction_zero_re_eq_half_of_grh`), but stated
directly in terms of `Z_χ` rather than routing through `|DirichletLFunction.primitiveBRe χ|` —
avoiding the
single-character `DirichletLFunction.primitiveBRe` obstacle entirely.
Role: feeds reciprocal and logarithmic zero-contribution bounds.
-/
theorem tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh {N : ℕ} [NeZero N] (_hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ =
      2 *
        ∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro ρ
  set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
  by_cases hD0 : D = 0
  · simp only [hD0, Int.cast_zero, zero_div, one_div, Complex.inv_re, zero_mul, mul_zero]
  · have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
        hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_grh
        hGRH hprimitive hne hinv hzero
    have hInvRe : (1 / ρ).re = (1 : ℝ) / 2 / Complex.normSq ρ := by
      rw [one_div, Complex.inv_re, hre_half]
    rw [hInvRe]
    ring

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis), and a positive real `x`.
Conclusion: the reciprocal zero-sum contribution `Σ' ρ, m_ρ x^{ρ-1} / (ρ(ρ-1))` has norm at most
`2 * Z_χ / √x`.
Content: identical to `norm_tsum_reciprocalZeroContribution_le` but built on the `hquad`-free
`DirichletLFunction.norm_completedReciprocalZeroTerm_eq_of_grh`,
`DirichletLFunction.summable_divisor_div_normSq_of_grh`, and
`DirichletLFunction.tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh` instead.
Role: bounds the reciprocal zero sum for a general primitive character.
-/
theorem norm_tsum_reciprocalZeroContribution_le_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ (ρ - 1) /
            (ρ * (ρ - 1))‖ ≤
      2 *
          (∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
              (1 / ρ).re) /
        Real.sqrt x := by
  have hsummableInv :=
    summable_divisor_div_normSq_of_grh hN2 hGRH
      hprimitive hne hinv
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hpt :=
    norm_completedReciprocalZeroTerm_eq_of_grh
      hGRH hprimitive hne hinv hx
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · exact (hsummableInv.div_const (Real.sqrt x)).congr (fun ρ => (hpt ρ).symm)
  · calc
      ∑' ρ : ℂ,
            ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                    ℂ) *
                  (x : ℂ) ^ (ρ - 1) /
                (ρ * (ρ - 1))‖ =
          ∑' ρ : ℂ,
            (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) /
                Complex.normSq ρ) /
              Real.sqrt x :=
        tsum_congr hpt
      _ =
          (∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) /
                Complex.normSq ρ) /
            Real.sqrt x :=
        tsum_div_const
      _ =
          2 *
              (∑' ρ : ℂ,
                ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                    ℝ) *
                  (1 / ρ).re) /
            Real.sqrt x :=
        by
        rw [tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh
            hN2 hGRH hprimitive hne hinv]

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis), and a positive real `x`.
Conclusion: the logarithmic zero-sum contribution `Σ' ρ, m_ρ x^ρ / ρ²` has norm at most
`2 * √x * Z_χ`.
Content: identical to `norm_tsum_logZeroContribution_le` but built on the `hquad`-free
`DirichletLFunction.summable_divisor_div_normSq_of_grh` and
`DirichletLFunction.tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh`
instead, with the pointwise norm identity re-derived via
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunction_zero_re_eq_half_of_grh`.
Role: bounds the logarithmic zero sum for a general primitive character.
-/
theorem norm_tsum_logZeroContribution_le_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2‖ ≤
      2 * Real.sqrt x *
        (∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re) := by
  have hsummableInv :=
    summable_divisor_div_normSq_of_grh hN2 hGRH
      hprimitive hne hinv
  have hpt :
    ∀ ρ : ℂ,
      ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2‖ =
        Real.sqrt x *
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
            Complex.normSq ρ) := by
    intro ρ
    set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
    by_cases hD0 : D = 0
    · simp only [hD0, Int.cast_zero, zero_mul, zero_div, norm_zero, mul_zero]
    · have hDnonneg : (0 : ℝ) ≤ (D : ℝ) := by
        have hdiff := DirichletCharacter.differentiable_completedLFunction hne
        have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
          fun z _ => hdiff.analyticAt z
        exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic ρ
      have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
        dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
          hne hD0
      have hre_half : ρ.re = (1 : ℝ) / 2 :=
        completedLFunction_zero_re_eq_half_of_grh
          hGRH hprimitive hne hinv hzero
      have hnormsq : ‖ρ ^ 2‖ = Complex.normSq ρ := by rw [norm_pow, ← Complex.normSq_eq_norm_sq]
      have hnormpow : ‖(x : ℂ) ^ ρ‖ = Real.sqrt x := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre_half, ← Real.sqrt_eq_rpow]
      rw [norm_div, norm_mul, Complex.norm_intCast, abs_of_nonneg hDnonneg, hnormpow, hnormsq]
      ring
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · exact (hsummableInv.mul_left (Real.sqrt x)).congr (fun ρ => (hpt ρ).symm)
  · calc
      ∑' ρ : ℂ,
            ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                    ℂ) *
                  (x : ℂ) ^ ρ /
                ρ ^ 2‖ =
          ∑' ρ : ℂ,
            Real.sqrt x *
              (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) /
                Complex.normSq ρ) :=
        tsum_congr hpt
      _ =
          Real.sqrt x *
            ∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) /
                Complex.normSq ρ :=
        tsum_mul_left
      _ =
          2 * Real.sqrt x *
            (∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) *
                (1 / ρ).re) :=
        by
        rw [tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh
            hN2 hGRH hprimitive hne hinv]
        ring

/--
Input/assumptions: GRH, a primitive complex Dirichlet character with `χ ≠ 1` and `χ⁻¹ ≠ 1` (no
quadratic hypothesis), `2 ≤ N`, and `R > 0`.
Conclusion: `DirichletLFunction.completedLFunctionTruncatedGenusSum χ R` has a derivative `D` at
`0` with
`‖D‖ ≤ 2 Z_χ`, where `Z_χ` is the real zero mass `Σ' ρ, m_ρ(χ) Re(1/ρ)` of `χ` itself.
Content: identical to `exists_hasDerivAt_completedLFunctionTruncatedGenusSum_zero_norm_le` but
built on the `hquad`-free `DirichletLFunction.summable_divisor_div_normSq_of_grh` and
`DirichletLFunction.tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh` instead, with `Z_χ` as the
witness. The
derivative computation itself (termwise `HasDerivAt` on the finite genus-sum support) is
`hquad`-independent and reused verbatim; only the final norm bound's zero-mass identity changes.
Role: the generic application route, the `hquad`-free Hadamard-derivative bound feeding the
log-residue `s = 0`
evaluation.
-/
theorem exists_hasDerivAt_completedLFunctionTruncatedGenusSum_zero_norm_le_of_grh {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hN2 : 2 ≤ N) {R : ℝ}
    (_hR : 0 < R) :
    ∃ D : ℂ,
      HasDerivAt
          (completedLFunctionTruncatedGenusSum χ
            R)
          D 0 ∧
        ‖D‖ ≤
          2 *
            ∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) *
                (1 / ρ).re := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalyticClosed :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  set Dv :=
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) with
    hDv_def
  have hfin : (Function.support Dv).Finite :=
    hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have h0ne : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive
      hprimitive hne
  have hkey : ∀ u ∈ hfin.toFinset, u ∈ Metric.ball (0 : ℂ) R ∧ u ≠ 0 := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    exact
      ⟨Dv.supportWithinDomain hu,
        ne_of_mem_divisorBallSupport_of_completedLFunction_ne_zero
          hne hu h0ne⟩
  have hsub :
    ∀ s : ℂ,
      Function.support (fun ρ : ℂ => ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)) ⊆ hfin.toFinset := by
    intro s u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu0
    apply hu
    rw [hDu0]
    simp only [Int.cast_zero, one_div, zero_mul]
  have heq :
    completedLFunctionTruncatedGenusSum χ R =
      fun s : ℂ => ∑ ρ ∈ hfin.toFinset, ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
    funext s
    rw [completedLFunctionTruncatedGenusSum,
      finsum_eq_sum_of_support_subset _ (hsub s)]
  set D : ℂ := ∑ ρ ∈ hfin.toFinset, ((Dv ρ : ℤ) : ℂ) * (-(1 / ρ ^ 2)) with hD_def
  refine ⟨D, ?_, ?_⟩
  · rw [heq]
    apply HasDerivAt.fun_sum
    intro ρ hρ
    obtain ⟨_, hρne0⟩ := hkey ρ hρ
    have hne' : (0 : ℂ) - ρ ≠ 0 := by
      rw [zero_sub, neg_ne_zero]
      exact hρne0
    have hc : HasDerivAt (fun s : ℂ => s - ρ) 1 0 := (hasDerivAt_id (0 : ℂ)).sub_const ρ
    have hinvderiv := hc.inv hne'
    have hval : -(1 : ℂ) / ((0 : ℂ) - ρ) ^ 2 = -(1 / ρ ^ 2) := by
      rw [zero_sub, neg_sq]
      ring
    rw [hval] at hinvderiv
    have h2 : HasDerivAt (fun s : ℂ => (1 : ℂ) / (s - ρ)) (-(1 / ρ ^ 2)) 0 := by
      have heq2 : (fun s : ℂ => (1 : ℂ) / (s - ρ)) = (fun s : ℂ => s - ρ)⁻¹ := by
        funext s
        rw [Pi.inv_apply, one_div]
      rw [heq2]
      exact hinvderiv
    have h3 : HasDerivAt (fun _ : ℂ => (1 : ℂ) / ρ) 0 0 := hasDerivAt_const 0 (1 / ρ)
    have h4 : HasDerivAt (fun s : ℂ => (1 : ℂ) / (s - ρ) + 1 / ρ) (-(1 / ρ ^ 2)) 0 := by
      have hadd := h2.add h3
      have hfun :
        (fun s : ℂ => (1 : ℂ) / (s - ρ)) + (fun _ : ℂ => (1 : ℂ) / ρ) = fun s : ℂ =>
          (1 : ℂ) / (s - ρ) + 1 / ρ := by
        funext s
        rfl
      rw [hfun, add_zero] at hadd
      exact hadd
    exact h4.const_mul ((Dv ρ : ℤ) : ℂ)
  · have hsummable :=
      summable_divisor_div_normSq_of_grh hN2
        hGRH hprimitive hne hinv
    have htsum :=
      tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh
        hN2 hGRH hprimitive hne hinv
    have hterm :
      ∀ ρ ∈ hfin.toFinset,
        ‖((Dv ρ : ℤ) : ℂ) * (-(1 / ρ ^ 2))‖ =
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
            Complex.normSq ρ := by
      intro ρ hρ
      obtain ⟨hρball, _⟩ := hkey ρ hρ
      have hDeq :
        Dv ρ = MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ := by
        rw [hDv_def,
          divisor_ball_eq_if_univ hne,
          ite_eq_left (by rwa [Metric.mem_ball, dist_zero_right] at hρball)]
      have hanalyticUniv : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
        fun z _ => hdiff.analyticAt z
      have hDnonneg :
        (0 : ℝ) ≤
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
            ℝ) := by
        exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticUniv ρ
      have hnormsq : ‖ρ ^ 2‖ = Complex.normSq ρ := by rw [norm_pow, ← Complex.normSq_eq_norm_sq]
      rw [norm_mul, Complex.norm_intCast, hDeq, abs_of_nonneg hDnonneg, norm_neg, norm_div,
        norm_one, hnormsq, mul_one_div]
    calc
      ‖D‖ ≤ ∑ ρ ∈ hfin.toFinset, ‖((Dv ρ : ℤ) : ℂ) * (-(1 / ρ ^ 2))‖ := by
        rw [hD_def]
        exact norm_sum_le _ _
      _ =
          ∑ ρ ∈ hfin.toFinset,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ :=
        Finset.sum_congr rfl hterm
      _ ≤
          ∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ :=
        by
        have hanalyticUniv : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
          fun z _ => hdiff.analyticAt z
        have hallNonneg :
          ∀ ρ : ℂ,
            (0 : ℝ) ≤
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) /
                Complex.normSq ρ := by
          intro ρ
          have :
            (0 : ℝ) ≤
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                ℝ) := by
            exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticUniv ρ
          exact div_nonneg this (Complex.normSq_nonneg ρ)
        exact hsummable.sum_le_tsum hfin.toFinset (fun ρ _ => hallNonneg ρ)
      _ =
          2 *
            ∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) *
                (1 / ρ).re :=
        htsum

/-- The finite-radius `R` slope error, factored so the finite-radius estimate's bound reads
`‖Q_R(s)‖ ≤ DirichletLFunction.completedLFunctionH9eSlopeError χ R * ‖s‖`. -/
noncomputable def completedLFunctionH9eSlopeError {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (R : ℝ) : ℝ :=
  192 *
        ((4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
            Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
          1) /
      R ^ 2 +
    2 / R ^ 2 *
      (Real.log
          (max 1
              (completedLFunctionBallBound N
                (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2)

/-- `DirichletLFunction.completedLFunctionH9eSlopeError χ R → 0` as `R → ∞`: the sum of the main
term's error
(`DirichletLFunction.tendsto_const_mul_add_mul_log_add_const_div_sq_atTop`) and the second term's
error
(`DirichletLFunction.tendsto_h9dError_atTop`, whose `2 * 1 / R ^ 2` coefficient is `2 / R ^ 2` up
to `mul_one`). -/
theorem tendsto_completedLFunctionH9eSlopeError_atTop {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Filter.Tendsto
      (completedLFunctionH9eSlopeError χ)
      Filter.atTop (nhds 0) := by
  have h1 :=
    tendsto_const_mul_add_mul_log_add_const_div_sq_atTop
      192 (4 * (N : ℝ) + 3) (-Real.log ‖DirichletCharacter.completedLFunction χ 0‖ + 1)
  have h2 :=
    tendsto_h9dError_atTop hN2 hprimitive hne
      hinv
  simp only [mul_one] at h2
  have hsum := h1.add h2
  simp only [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards with R
  unfold completedLFunctionH9eSlopeError
  ring

/--
Input/assumptions: `1 < N`, primitive nontrivial `χ`, `hinv`, `R ≥ 1`, `R` zero-free
sphere, and the truncated genus sum's derivative bundle at `0`.
Conclusion: `‖deriv (logDeriv F) 0 - D‖ ≤ DirichletLFunction.completedLFunctionH9eSlopeError χ R`.
Content: `Q_R(s) := (logDeriv F(s) - logDeriv F(0)) -
DirichletLFunction.completedLFunctionTruncatedGenusSum χ R s`
has `Q_R(0) = 0` and, eventually near `0`, satisfies the slope bound; `HasDerivAt.tendsto_slope`
plus `RiemannXi.norm_deriv_le_of_eventually_norm_le_mul_norm` extracts the derivative-norm bound.
Role: a differentiated error bound, isolating `(logDeriv F)'(0)` up to the truncated genus sum's
own (already-bounded) derivative.
-/
theorem norm_deriv_logDeriv_completedLFunction_zero_sub_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hN1 : 1 < N) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {R : ℝ} (hR : 1 ≤ R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) {D : ℂ}
    (hD :
      HasDerivAt
        (completedLFunctionTruncatedGenusSum χ
          R)
        D 0) :
    ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0 - D‖ ≤
      completedLFunctionH9eSlopeError χ R := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have h0ne : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive
      hprimitive hne
  set F := DirichletCharacter.completedLFunction χ
  have hLogHasDeriv : HasDerivAt (logDeriv F) (deriv (logDeriv F) 0) 0 :=
    (differentiableAt_logDeriv_completedLFunction_zero
        hprimitive hne).hasDerivAt
  have hQ :
    HasDerivAt
      (fun s : ℂ =>
        (logDeriv F s - logDeriv F 0) -
          completedLFunctionTruncatedGenusSum χ
            R s)
      (deriv (logDeriv F) 0 - D) 0 :=
    (hLogHasDeriv.sub_const _).sub hD
  have hQ0 :
    (logDeriv F 0 - logDeriv F 0) -
        completedLFunctionTruncatedGenusSum χ R
          0 =
      0 := by
    rw [sub_self,
      completedLFunctionTruncatedGenusSum_zero,
      zero_sub, neg_zero]
  have hRpos : (0 : ℝ) < R := by linarith
  have hev : ∀ᶠ s : ℂ in nhds (0 : ℂ), ‖s‖ ≤ R / 2 ∧ F s ≠ 0 := by
    have h1 : ∀ᶠ s : ℂ in nhds (0 : ℂ), ‖s‖ ≤ R / 2 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < R / 2 by linarith)] with s hs
      rw [Metric.mem_ball, dist_zero_right] at hs
      exact hs.le
    have h2 : ∀ᶠ s : ℂ in nhds (0 : ℂ), F s ≠ 0 :=
      (hdiff.continuous.continuousAt).eventually_ne h0ne
    filter_upwards [h1, h2] with s hs1 hs2 using ⟨hs1, hs2⟩
  have hbound :
    ∀ᶠ s : ℂ in nhdsWithin 0 ({0}ᶜ : Set ℂ),
      ‖(logDeriv F s - logDeriv F 0) -
            completedLFunctionTruncatedGenusSum
              χ R s‖ ≤
        completedLFunctionH9eSlopeError χ R *
          ‖s‖ := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with s hs
    have h9e :=
      norm_centeredLogDeriv_sub_truncatedGenus_le
        hN1 hprimitive hne hinv hR hzf hs.1 hs.2
    have hfactor :
      192 * ‖s‖ * ((4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) - Real.log ‖F 0‖ + 1) / R ^ 2 +
          2 * ‖s‖ / R ^ 2 *
            (Real.log
                (max 1
                    (completedLFunctionBallBound
                      N (2 * R)) /
                  ‖F 0‖) /
              Real.log 2) =
        completedLFunctionH9eSlopeError χ R *
          ‖s‖ := by
      unfold completedLFunctionH9eSlopeError
      ring
    rwa [hfactor] at h9e
  exact
    RiemannXi.norm_deriv_le_of_eventually_norm_le_mul_norm hQ hQ0
      hbound

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis), `R ≥ 1`, and `R` a zero-free sphere radius.
Conclusion: `‖deriv (logDeriv F) 0‖ ≤ DirichletLFunction.completedLFunctionH9eSlopeError χ R + 2
Z_χ`, where `Z_χ` is
the real zero mass `Σ' ρ, m_ρ(χ) Re(1/ρ)` of `χ` itself.
Content: identical to `norm_deriv_logDeriv_completedLFunction_zero_le` but built on the
`hquad`-free
`DirichletLFunction.exists_hasDerivAt_completedLFunctionTruncatedGenusSum_zero_norm_le_of_grh`
instead,
with `Z_χ` as the witness. `DirichletLFunction.norm_deriv_logDeriv_completedLFunction_zero_sub_le`
(the finite-radius estimate slope
bound feeding the triangle inequality) is already `hquad`-free and reused verbatim.
Role: the generic application route, a fixed-`R` bound, ready for `R → ∞` along a good-radius
sequence.
-/
theorem norm_deriv_logDeriv_completedLFunction_zero_le_of_grh {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hN2 : 2 ≤ N) {R : ℝ} (hR : 1 ≤ R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) :
    ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖ ≤
      completedLFunctionH9eSlopeError χ R +
        2 *
          ∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
              (1 / ρ).re := by
  have hN1 : 1 < N := by omega
  obtain ⟨D, hD, hDnorm⟩ :=
    exists_hasDerivAt_completedLFunctionTruncatedGenusSum_zero_norm_le_of_grh
      hGRH hprimitive hne hinv hN2 (show (0 : ℝ) < R by linarith)
  have hsub :=
    norm_deriv_logDeriv_completedLFunction_zero_sub_le
      hN1 hprimitive hne hinv hR hzf hD
  calc
    ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖ ≤
        ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0 - D‖ + ‖D‖ :=
      by
      have := norm_add_le (deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0 - D) D
      simpa only [ge_iff_le, sub_add_cancel] using this
    _ ≤
        completedLFunctionH9eSlopeError χ R +
          2 *
            ∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) *
                (1 / ρ).re :=
      add_le_add hsub hDnorm

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: `‖deriv (logDeriv F) 0‖ ≤ 2 Z_χ`.
Content: identical to `norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_abs_BRe` but built
on `DirichletLFunction.norm_deriv_logDeriv_completedLFunction_zero_le_of_grh` instead, transferring
through `R → ∞`
along `DirichletLFunction.completedLFunctionGoodRadius` exactly as the quadratic version does.
Role: the generic application route, a Hadamard-side derivative-norm bound at the origin, without
ever exposing
the global identity `(logDeriv F)'(0) = -Σ_ρ m_ρ/ρ²` — only the triangle-inequality bound
survives to the public API.
-/
theorem norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_zeroMass_of_grh {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hN2 : 2 ≤ N) :
    ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖ ≤
      2 *
        ∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re := by
  have htendError :=
    tendsto_completedLFunctionH9eSlopeError_atTop
      hN2 hprimitive hne hinv
  have htendComp :=
    htendError.comp
      (tendsto_completedLFunctionGoodRadius_atTop
        hne)
  have htendSum :
    Filter.Tendsto
      (fun n : ℕ =>
        completedLFunctionH9eSlopeError χ
            (completedLFunctionGoodRadius hne
              n) +
          2 *
            ∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) *
                (1 / ρ).re)
      Filter.atTop
      (nhds
        (0 +
          2 *
            ∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) *
                (1 / ρ).re)) :=
    htendComp.add tendsto_const_nhds
  simp only [zero_add] at htendSum
  have hev :
    ∀ᶠ n : ℕ in Filter.atTop,
      ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖ ≤
        completedLFunctionH9eSlopeError χ
            (completedLFunctionGoodRadius hne
              n) +
          2 *
            ∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) *
                (1 / ρ).re := by
    filter_upwards with n
    have hRgt :=
      completedLFunctionGoodRadius_gt hne n
    have hR1 :
      (1 : ℝ) ≤
        completedLFunctionGoodRadius hne n := by
      have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact
      norm_deriv_logDeriv_completedLFunction_zero_le_of_grh
        hGRH hprimitive hne hinv hN2 hR1
        (completedLFunctionGoodRadius_zeroFree
          hne n)
  exact ge_of_tendsto htendSum hev

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial mod `N`, GRH, `χ⁻¹ ≠ 1` (no quadratic
hypothesis).
Conclusion: `-Re(deriv(logDeriv F) 0) ≤ 2 Z_χ`.
Content: identical to `neg_re_deriv_logDeriv_completedLFunction_zero_le` but built on
`DirichletLFunction.norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_zeroMass_of_grh` instead.
Role: the generic application route, a real-part corollary of the derivative-norm bound at the
origin.
-/
theorem neg_re_deriv_logDeriv_completedLFunction_zero_le_of_grh {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hN2 : 2 ≤ N) :
    -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re ≤
      2 *
        ∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re := by
  have hnormBound :=
    norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_zeroMass_of_grh
      hGRH hprimitive hne hinv hN2
  have hre := Complex.re_le_norm (-deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0)
  rw [Complex.neg_re, norm_neg] at hre
  linarith [hre, hnormBound]

/--
Input/assumptions: a primitive complex Dirichlet character.
Conclusion: `(logDeriv (completedLFunction χ) 0).re = DirichletLFunction.primitiveBRe χ - (1/2) log
N`.
Content: pure rearrangement of `DirichletLFunction.primitiveBRe`'s definition
(`DirichletLFunction.primitiveBRe χ = Re(logDeriv F 0) +
(1/2) log conductor`) using `χ.conductor = N` (primitivity). No GRH or quadratic hypothesis is
needed — this is definitionally true for any primitive character.
Role: gives the endpoint real part directly in terms of `primitiveBRe χ`;
the sign is identified below using
`primitiveBRe_inv_eq` and the GRH zero-mass identity.
-/
theorem completedLFunction_logDeriv_zero_re_eq_primitiveBRe_sub_half_log {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) :
    (logDeriv (DirichletCharacter.completedLFunction χ) 0).re =
      primitiveBRe χ -
        (1 / 2) * Real.log N := by
  rw [primitiveBRe,
    (hprimitive : χ.conductor = N)]
  ring

/--
Input/assumptions: a primitive complex Dirichlet character with `χ ≠ 1` and `χ⁻¹ ≠ 1`.
Conclusion: `(logDeriv (completedLFunction χ) 1).re = -DirichletLFunction.primitiveBRe χ⁻¹ - (1/2)
log N`.
Content: the pair-system functional equation at `s = 0`
(`DirichletLFunction.completedLFunction_logDeriv_functionalEquation_at_zero`, `-logDeriv F(χ) 1 =
log N +
logDeriv F(χ⁻¹) 0`); taking `.re` and substituting
`DirichletLFunction.completedLFunction_logDeriv_zero_re_eq_primitiveBRe_sub_half_log` for `χ⁻¹`
(via `DirichletLFunction.DirichletCharacter.isPrimitive_inv`) gives the claim by `linarith`. No GRH
or quadratic
hypothesis is needed.
Role: the `hquad`-free analogue of `completedLFunction_logDeriv_one_re_eq_abs_BRe_sub_half_log`,
expressed via `DirichletLFunction.primitiveBRe χ⁻¹` (the `χ⁻¹`-side term does not collapse to
`DirichletLFunction.primitiveBRe χ` without
either `DirichletLFunction.primitiveBRe_inv_eq` or the `Z_χ`-witness route).
-/
theorem completedLFunction_logDeriv_one_re_eq_neg_primitiveBRe_inv_sub_half_log {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (logDeriv (DirichletCharacter.completedLFunction χ) 1).re =
      -primitiveBRe χ⁻¹ -
        (1 / 2) * Real.log N := by
  have hprimitiveinv : χ⁻¹.IsPrimitive :=
    DirichletCharacter.isPrimitive_inv
      hprimitive
  have hFE :=
    completedLFunction_logDeriv_functionalEquation_at_zero
      hprimitive hne hinv
  have hlogNre : (Complex.log (N : ℂ)).re = Real.log N := by
    rw [show ((N : ℕ) : ℂ) = ((N : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.log_ofReal_re]
  have hFEre :
    -(logDeriv (DirichletCharacter.completedLFunction χ) 1).re =
      Real.log N + (logDeriv (DirichletCharacter.completedLFunction χ⁻¹) 0).re := by
    have := congrArg Complex.re hFE
    simpa only [Complex.neg_re, Complex.add_re, hlogNre] using this
  have hzero :=
    completedLFunction_logDeriv_zero_re_eq_primitiveBRe_sub_half_log
      hprimitiveinv
  linarith [hFEre, hzero]

/--
Input/assumptions: a complex Dirichlet character with `χ ≠ 1` (no primitivity, GRH, or quadratic
hypothesis).
Conclusion: `DirichletLFunction.primitiveBRe χ⁻¹ = DirichletLFunction.primitiveBRe χ`.
Content: **the conjugation identity, complete**. From
`DirichletLFunction.DirichletCharacter.completedLFunction_conj` at `s = 0` (`conj (F(χ) 0) = F(χ⁻¹)
0`) and
`DirichletLFunction.DirichletCharacter.deriv_completedLFunction_zero_conj` (`conj (deriv F(χ) 0) =
deriv F(χ⁻¹) 0`),
`logDeriv F(χ⁻¹) 0 = deriv F(χ⁻¹) 0 / F(χ⁻¹) 0 = conj (deriv F(χ) 0) / conj (F(χ) 0) =
conj (logDeriv F(χ) 0)`, so `Re (logDeriv F(χ⁻¹) 0) = Re (logDeriv F(χ) 0)`
(`Complex.conj_re`). Combined with `DirichletLFunction.DirichletCharacter.conductor_inv_eq`
(`χ⁻¹.conductor =
χ.conductor`), `DirichletLFunction.primitiveBRe`'s definition gives the claim.
Role: reduces the pair-sum zero-mass identity to the single-character constant used by the residue
estimates.
-/
theorem primitiveBRe_inv_eq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) :
    primitiveBRe χ⁻¹ =
      primitiveBRe χ := by
  have hFconj0 :=
    DirichletCharacter.completedLFunction_conj χ
      0
  simp only [map_zero] at hFconj0
  have hderivconj :=
    DirichletCharacter.deriv_completedLFunction_zero_conj
      hne
  rw [primitiveBRe,
    primitiveBRe,
    DirichletCharacter.conductor_inv_eq]
  congr 1
  rw [logDeriv_apply, logDeriv_apply, ← hFconj0, ← hderivconj, ← map_div₀, Complex.conj_re]

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: `DirichletLFunction.primitiveBRe χ = -Z_χ`, where `Z_χ` is the real zero mass `Σ' ρ,
m_ρ(χ) Re(1/ρ)`.
Content: `DirichletLFunction.primitiveBRe_add_inv_eq_neg_two_mul_zeroMass_of_grh` gives
`DirichletLFunction.primitiveBRe χ +
DirichletLFunction.primitiveBRe χ⁻¹ = -2 Z_χ`; substituting
`DirichletLFunction.primitiveBRe_inv_eq` (`DirichletLFunction.primitiveBRe χ⁻¹ =
DirichletLFunction.primitiveBRe χ`) collapses this to `2 · DirichletLFunction.primitiveBRe χ = -2
Z_χ`.
Role: the complete `hquad`-free analogue of `primitiveBRe_eq_neg_zeroMass_isQuadratic`.
-/
theorem primitiveBRe_eq_neg_zeroMass_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    primitiveBRe χ =
      -(∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re) := by
  have hpair :=
    primitiveBRe_add_inv_eq_neg_two_mul_zeroMass_of_grh
      hN2 hGRH hprimitive hne hinv
  rw [primitiveBRe_inv_eq hne] at hpair
  linarith [hpair]

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: `|PseudoPrime.AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| = Z_χ`.
Content: combines `DirichletLFunction.primitiveBRe_eq_neg_zeroMass_of_grh` with the sign
information from
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.primitiveZeroMass_nonneg_of_grh`.
Role: the complete `hquad`-free analogue of `abs_primitiveBRe_eq_zeroMass_isQuadratic`; from here,
`Z_χ`-witness zero-sum and derivative bounds can be rewritten in terms of
`|DirichletLFunction.primitiveBRe χ|`, matching the
existing quadratic route's shared witness with no redesign of downstream consumers.
-/
theorem abs_primitiveBRe_eq_zeroMass_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    |primitiveBRe χ| =
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re := by
  rw [primitiveBRe_eq_neg_zeroMass_of_grh hN2
      hGRH hprimitive hne hinv,
    abs_neg,
    abs_of_nonneg
      (primitiveZeroMass_nonneg_of_grh hGRH
        hprimitive hne hinv)]

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: `Σ' ρ, m_ρ(χ)/normSq ρ = 2 |DirichletLFunction.primitiveBRe χ|`.
Content: `DirichletLFunction.tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh` rewritten via
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass_of_grh` from the `Z_χ` witness to the
`|DirichletLFunction.primitiveBRe χ|` witness,
matching the quadratic route's `tsum_divisor_inv_normSq_eq_two_mul_abs_BRe` verbatim.
Role: the generic application route (Cauchy–Schwarz truncated-genus-sum bound), the shared-witness
zero-mass
identity feeding `DirichletLFunction.norm_completedLFunctionTruncatedGenusSum_le_of_grh`.
-/
theorem tsum_divisor_inv_normSq_eq_two_mul_abs_BRe_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ =
      2 * |primitiveBRe χ| := by
  rw [abs_primitiveBRe_eq_zeroMass_of_grh hN2
      hGRH hprimitive hne hinv]
  exact
    tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh
      hN2 hGRH hprimitive hne hinv

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis), and a positive real `x`.
Conclusion: the reciprocal zero-sum contribution has norm at most `2 *
|DirichletLFunction.primitiveBRe χ| / √x`.
Content: `DirichletLFunction.norm_tsum_reciprocalZeroContribution_le_of_grh` rewritten via
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass_of_grh` from the `Z_χ` witness to the
`|DirichletLFunction.primitiveBRe χ|` witness,
matching the quadratic route's `norm_tsum_reciprocalZeroContribution_le` verbatim.
Role: supplies the reciprocal zero-sum bound in terms of the shared Hadamard constant.
-/
theorem norm_tsum_reciprocalZeroContribution_le_abs_BRe_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ (ρ - 1) /
            (ρ * (ρ - 1))‖ ≤
      2 * |primitiveBRe χ| / Real.sqrt x := by
  rw [abs_primitiveBRe_eq_zeroMass_of_grh hN2
      hGRH hprimitive hne hinv]
  exact
    norm_tsum_reciprocalZeroContribution_le_of_grh
      hN2 hGRH hprimitive hne hinv hx

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis), and a positive real `x`.
Conclusion: the logarithmic zero-sum contribution has norm at most `2 * √x *
|DirichletLFunction.primitiveBRe χ|`.
Content: `DirichletLFunction.norm_tsum_logZeroContribution_le_of_grh` rewritten via
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass_of_grh` from the `Z_χ` witness to the
`|DirichletLFunction.primitiveBRe χ|` witness,
matching the quadratic route's `norm_tsum_logZeroContribution_le` verbatim.
Role: supplies the logarithmic zero-sum bound in terms of the shared Hadamard constant.
-/
theorem norm_tsum_logZeroContribution_le_abs_BRe_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2‖ ≤
      2 * Real.sqrt x * |primitiveBRe χ| := by
  rw [abs_primitiveBRe_eq_zeroMass_of_grh hN2
      hGRH hprimitive hne hinv]
  exact
    norm_tsum_logZeroContribution_le_of_grh hN2
      hGRH hprimitive hne hinv hx

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial mod `N`, GRH, `χ⁻¹ ≠ 1` (no quadratic
hypothesis).
Conclusion: `‖deriv (logDeriv (completedLFunction χ)) 0‖ ≤ 2 |DirichletLFunction.primitiveBRe χ|`.
Content:
`DirichletLFunction.norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_zeroMass_of_grh`
rewritten via
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass_of_grh` from the `Z_χ` witness to the
`|DirichletLFunction.primitiveBRe χ|` witness,
matching the quadratic route's `norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_abs_BRe`.
Role: supplies the Hadamard-derivative bound used at the logarithmic Mellin pole.
-/
theorem norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_abs_BRe_of_grh {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hN2 : 2 ≤ N) :
    ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖ ≤
      2 * |primitiveBRe χ| := by
  rw [abs_primitiveBRe_eq_zeroMass_of_grh hN2
      hGRH hprimitive hne hinv]
  exact
    norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_zeroMass_of_grh
      hGRH hprimitive hne hinv hN2

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial mod `N`, GRH, `χ⁻¹ ≠ 1` (no quadratic
hypothesis).
Conclusion: `-Re(deriv(logDeriv F) 0) ≤ 2 |DirichletLFunction.primitiveBRe χ|`.
Content: `DirichletLFunction.neg_re_deriv_logDeriv_completedLFunction_zero_le_of_grh` rewritten via
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass_of_grh` from the `Z_χ` witness to the
`|DirichletLFunction.primitiveBRe χ|` witness.
Role: supplies its real-part derivative bound for logarithmic residue estimates.
-/
theorem neg_re_deriv_logDeriv_completedLFunction_zero_le_abs_BRe_of_grh {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hN2 : 2 ≤ N) :
    -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re ≤
      2 * |primitiveBRe χ| := by
  rw [abs_primitiveBRe_eq_zeroMass_of_grh hN2
      hGRH hprimitive hne hinv]
  exact
    neg_re_deriv_logDeriv_completedLFunction_zero_le_of_grh
      hGRH hprimitive hne hinv hN2

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: `(logDeriv (completedLFunction χ) 0).re = -|DirichletLFunction.primitiveBRe χ| - (1/2)
log N`.
Content: substitute `DirichletLFunction.primitiveBRe_eq_neg_zeroMass_of_grh` and
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass_of_grh`
into `DirichletLFunction.completedLFunction_logDeriv_zero_re_eq_primitiveBRe_sub_half_log`, exactly
mirroring the
quadratic proof of `completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log`.
Role: supplies the shared-constant endpoint closed form at `s = 0` under GRH.
-/
theorem completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (logDeriv (DirichletCharacter.completedLFunction χ) 0).re =
      -|primitiveBRe χ| -
        (1 / 2) * Real.log N := by
  have hB :=
    primitiveBRe_eq_neg_zeroMass_of_grh hN2 hGRH
      hprimitive hne hinv
  have habs :=
    abs_primitiveBRe_eq_zeroMass_of_grh hN2 hGRH
      hprimitive hne hinv
  have hBneg :
    primitiveBRe χ =
      -|primitiveBRe χ| := by
    rw [habs, hB]
  have hBRe :=
    completedLFunction_logDeriv_zero_re_eq_primitiveBRe_sub_half_log
      hprimitive
  rw [hBneg] at hBRe
  linarith [hBRe]

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: `(logDeriv (completedLFunction χ) 1).re = |DirichletLFunction.primitiveBRe χ| - (1/2)
log N`.
Content: rewrite
`DirichletLFunction.completedLFunction_logDeriv_one_re_eq_neg_primitiveBRe_inv_sub_half_log`'s
`DirichletLFunction.primitiveBRe χ⁻¹` term via `DirichletLFunction.primitiveBRe_inv_eq` to
`DirichletLFunction.primitiveBRe χ`, then apply
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass_of_grh`/
`DirichletLFunction.primitiveBRe_eq_neg_zeroMass_of_grh`
to identify the sign,
exactly mirroring `completedLFunction_logDeriv_one_re_eq_abs_BRe_sub_half_log`.
Role: supplies the shared-constant endpoint identity at one, without an inverse-character term.
-/
theorem completedLFunction_logDeriv_one_re_eq_abs_BRe_sub_half_log_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (logDeriv (DirichletCharacter.completedLFunction χ) 1).re =
      |primitiveBRe χ| -
        (1 / 2) * Real.log N := by
  have hone :=
    completedLFunction_logDeriv_one_re_eq_neg_primitiveBRe_inv_sub_half_log
      hprimitive hne hinv
  rw [primitiveBRe_inv_eq hne] at hone
  have hB :=
    primitiveBRe_eq_neg_zeroMass_of_grh hN2 hGRH
      hprimitive hne hinv
  have habs :=
    abs_primitiveBRe_eq_zeroMass_of_grh hN2 hGRH
      hprimitive hne hinv
  have hBneg :
    primitiveBRe χ =
      -|primitiveBRe χ| := by
    rw [habs, hB]
  rw [hBneg] at hone
  linarith [hone]

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive nontrivial complex Dirichlet character with
`χ⁻¹ ≠ 1` (no quadratic hypothesis), `0 < R`, a point `s` where `completedLFunction χ` does not
vanish, and a positive margin `δ` such that every zero of `completedLFunction χ` inside
`ball 0 R` stays at distance `≥ δ` from `s`.
Conclusion: `‖DirichletLFunction.completedLFunctionTruncatedGenusSum χ R s‖ ≤ ‖s‖ ·
√(2|DirichletLFunction.primitiveBRe χ|) · √(log(max 1 (completedLFunctionBallBound N
(2R))/‖F(0)‖)/log 2) / δ`.
Content: identical to `norm_completedLFunctionTruncatedGenusSum_le` but built on the `hquad`-free
`DirichletLFunction.summable_divisor_div_normSq_of_grh` and
`DirichletLFunction.tsum_divisor_inv_normSq_eq_two_mul_abs_BRe_of_grh`
instead of their quadratic counterparts; the weighted Cauchy–Schwarz argument itself
(`Finset.sum_mul_sq_le_sq_mul_sq` on `1/|ρ|`, `1/|s-ρ|`) and the good-height margin bound
(`DirichletLFunction.finsum_divisor_ball_completedLFunction_le`,
`DirichletLFunction.finsum_divisor_completedLFunction_le`) never
mentioned `χ.IsQuadratic` and are reused verbatim.
Role: supplies the genus-sum term in the horizontal logarithmic-derivative estimate.
-/
theorem norm_completedLFunctionTruncatedGenusSum_le_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ} (hR : 0 < R) {s : ℂ}
    (hsne : DirichletCharacter.completedLFunction χ s ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ‖ρ‖ < R → δ ≤ ‖s - ρ‖) :
    ‖completedLFunctionTruncatedGenusSum χ R
          s‖ ≤
      ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
          Real.sqrt
            (Real.log
                (max 1
                    (completedLFunctionBallBound
                      N (2 * R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) /
        δ := by
  have hN1 : 1 < N := by omega
  set Dv :=
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) with
    hDv_def
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hAnClosed :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  have hAnBall :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) := fun z _ =>
    hdiff.analyticAt z
  have hAnU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ =>
    hdiff.analyticAt z
  have h0ne : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive
      hprimitive hne
  have hfin : (Function.support Dv).Finite := hAnClosed.meromorphicOn.divisor_ball_support_finite
  set S := hfin.toFinset with hS_def
  have hDv_nonneg : ∀ ρ, (0 : ℤ) ≤ Dv ρ := fun ρ =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnBall ρ
  have hρ_ball : ∀ ρ, Dv ρ ≠ 0 → ρ ∈ Metric.ball (0 : ℂ) R := by
    intro ρ hne'
    by_contra hnot
    exact hne' (Dv.apply_eq_zero_of_notMem hnot)
  have hDv_zero :
    ∀ ρ, ρ ∈ Metric.ball (0 : ℂ) R → Dv ρ ≠ 0 → DirichletCharacter.completedLFunction χ ρ = 0 := by
    intro ρ hρmem hDvne
    by_contra hFne
    apply hDvne
    have hordzero : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ = 0 :=
      (hAnBall ρ hρmem).analyticOrderAt_eq_zero.mpr hFne
    rw [hDv_def, MeromorphicOn.AnalyticOnNhd.divisor_apply hAnBall hρmem, hordzero]
    simp only [ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero, WithTop.untop₀_zero]
  -- Step 1: rewrite the genus sum as a Finset sum over S
  have heqsum :
    completedLFunctionTruncatedGenusSum χ R s =
      ∑ ρ ∈ S, ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
    unfold completedLFunctionTruncatedGenusSum
    apply finsum_eq_finsetSum_of_support_subset
    intro ρ hρ
    rw [hS_def, Set.Finite.coe_toFinset]
    rw [Function.mem_support] at hρ ⊢
    intro hDv0
    apply hρ
    rw [hDv0]
    simp only [Int.cast_zero, one_div, zero_mul]
  -- Step 2: termwise norm computation
  have hterm_eq :
    ∀ ρ ∈ S, ‖((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ = (Dv ρ : ℝ) * ‖s‖ / (‖ρ‖ * ‖s - ρ‖) := by
    intro ρ hρS
    rw [hS_def, Set.Finite.mem_toFinset, Function.mem_support] at hρS
    have hρmem := hρ_ball ρ hρS
    have hFzero := hDv_zero ρ hρmem hρS
    have hρ0 : ρ ≠ 0 := fun h0 => h0ne (h0 ▸ hFzero)
    have hsρ : s ≠ ρ := fun heq => hsne (heq ▸ hFzero)
    have hid : (1 : ℂ) / (s - ρ) + 1 / ρ = s / (ρ * (s - ρ)) := by
      field_simp
      ring
    rw [hid, norm_mul, norm_div, norm_mul, Complex.norm_intCast,
      abs_of_nonneg (show (0 : ℝ) ≤ (Dv ρ : ℝ) by exact_mod_cast hDv_nonneg ρ)]
    ring
  -- Step 3: triangle inequality
  have hnorm_le :
    ‖completedLFunctionTruncatedGenusSum χ R
          s‖ ≤
      ‖s‖ * ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) := by
    rw [heqsum]
    calc
      ‖∑ ρ ∈ S, ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ ≤
          ∑ ρ ∈ S, ‖((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ :=
        norm_sum_le S _
      _ = ∑ ρ ∈ S, (Dv ρ : ℝ) * ‖s‖ / (‖ρ‖ * ‖s - ρ‖) := Finset.sum_congr rfl hterm_eq
      _ = ‖s‖ * ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ρ _ => by ring)
  -- Step 4: weighted Cauchy–Schwarz
  have hCS :
    (∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖)) ^ 2 ≤
      (∑ ρ ∈ S, (Dv ρ : ℝ) / ‖ρ‖ ^ 2) * (∑ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2) := by
    have hkey :=
      Finset.sum_mul_sq_le_sq_mul_sq S (fun ρ => Real.sqrt (Dv ρ) / ‖ρ‖)
        (fun ρ => Real.sqrt (Dv ρ) / ‖s - ρ‖)
    have heq1 :
      ∀ ρ ∈ S,
        (Real.sqrt (Dv ρ) / ‖ρ‖) * (Real.sqrt (Dv ρ) / ‖s - ρ‖) = (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) :=
      fun ρ _ => by rw [div_mul_div_comm, Real.mul_self_sqrt (by exact_mod_cast hDv_nonneg ρ)]
    have heq2 : ∀ ρ ∈ S, (Real.sqrt (Dv ρ) / ‖ρ‖) ^ 2 = (Dv ρ : ℝ) / ‖ρ‖ ^ 2 := fun ρ _ => by
      rw [div_pow, Real.sq_sqrt (by exact_mod_cast hDv_nonneg ρ)]
    have heq3 : ∀ ρ ∈ S, (Real.sqrt (Dv ρ) / ‖s - ρ‖) ^ 2 = (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 := fun ρ _ =>
      by rw [div_pow, Real.sq_sqrt (by exact_mod_cast hDv_nonneg ρ)]
    rwa [Finset.sum_congr rfl heq1, Finset.sum_congr rfl heq2, Finset.sum_congr rfl heq3] at hkey
  -- Step 5a: bound the first Cauchy–Schwarz factor via the zero mass
  have hfactorA :
    ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖ρ‖ ^ 2 ≤
      2 * |primitiveBRe χ| := by
    have hterm_eq2 :
      ∀ ρ ∈ S,
        (Dv ρ : ℝ) / ‖ρ‖ ^ 2 =
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
            Complex.normSq ρ := by
      intro ρ hρS
      rw [hS_def, Set.Finite.mem_toFinset, Function.mem_support] at hρS
      have hρmem := hρ_ball ρ hρS
      rw [← Complex.normSq_eq_norm_sq, hDv_def,
        divisor_completedLFunction_domain_eq hne
          hρmem]
    calc
      ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖ρ‖ ^ 2 =
          ∑ ρ ∈ S,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ :=
        Finset.sum_congr rfl hterm_eq2
      _ ≤
          ∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ :=
        (summable_divisor_div_normSq_of_grh hN2
              hGRH hprimitive hne hinv).sum_le_tsum
          S
          (fun i _ =>
            div_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnU i)
              (Complex.normSq_nonneg i))
      _ = 2 * |primitiveBRe χ| :=
        tsum_divisor_inv_normSq_eq_two_mul_abs_BRe_of_grh
          hN2 hGRH hprimitive hne hinv
  -- Step 5b: bound the second Cauchy–Schwarz factor via the good-height margin
  have hfactorB :
    ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 ≤
      (Real.log
            (max 1
                (completedLFunctionBallBound N
                  (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2) /
        δ ^ 2 := by
    have hterm_le : ∀ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 ≤ (Dv ρ : ℝ) / δ ^ 2 := by
      intro ρ hρS
      rw [hS_def, Set.Finite.mem_toFinset, Function.mem_support] at hρS
      have hρmem := hρ_ball ρ hρS
      have hFzero := hDv_zero ρ hρmem hρS
      have hρnorm : ‖ρ‖ < R := by
        rw [Metric.mem_ball, dist_zero_right] at hρmem
        exact hρmem
      have hsep' : δ ≤ ‖s - ρ‖ := hsep ρ hFzero hρnorm
      have hδsq : δ ^ 2 ≤ ‖s - ρ‖ ^ 2 := pow_le_pow_left₀ hδ.le hsep' 2
      have hDvρnonneg : (0 : ℝ) ≤ (Dv ρ : ℝ) := by exact_mod_cast hDv_nonneg ρ
      gcongr
    have hSsum :
      (∑ ρ ∈ S, (Dv ρ : ℝ)) ≤
        Real.log
            (max 1
                (completedLFunctionBallBound N
                  (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 := by
      have hSsumZ : (∑ ρ ∈ S, Dv ρ : ℤ) = ∑ᶠ ρ, Dv ρ := by
        symm
        apply finsum_eq_finsetSum_of_support_subset
        rw [hS_def, Set.Finite.coe_toFinset]
      have : ((∑ ρ ∈ S, Dv ρ : ℤ) : ℝ) = ∑ ρ ∈ S, (Dv ρ : ℝ) := by
        push_cast
        ring
      rw [← this, hSsumZ]
      exact
        finsum_divisor_ball_completedLFunction_le
          hN1 hprimitive hne hinv hR
    calc
      ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 ≤ ∑ ρ ∈ S, (Dv ρ : ℝ) / δ ^ 2 := Finset.sum_le_sum hterm_le
      _ = (∑ ρ ∈ S, (Dv ρ : ℝ)) / δ ^ 2 := by rw [Finset.sum_div]
      _ ≤ _ := by gcongr
  -- Step 6: combine
  have hH2nonneg :
    (0 : ℝ) ≤
      Real.log
          (max 1
              (completedLFunctionBallBound N
                (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 := by
    have hfinsum_nonneg :
      (0 : ℤ) ≤
        ∑ᶠ u,
          MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R) u := by
      apply finsum_nonneg
      intro u
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnClosed u
    exact
      le_trans (by exact_mod_cast hfinsum_nonneg)
        (finsum_divisor_completedLFunction_le
          hN1 hprimitive hne hinv hR)
  have hCSfull :
    (∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖)) ^ 2 ≤
      2 * |primitiveBRe χ| *
        (Real.log
            (max 1
                (completedLFunctionBallBound N
                  (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 /
          δ ^ 2) :=
    hCS.trans
      (mul_le_mul hfactorA hfactorB
        (Finset.sum_nonneg (fun ρ _ => div_nonneg (by exact_mod_cast hDv_nonneg ρ) (sq_nonneg _)))
        (by positivity))
  have hsum_nonneg : 0 ≤ ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) :=
    Finset.sum_nonneg
      (fun ρ _ =>
        div_nonneg (by exact_mod_cast hDv_nonneg ρ) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hrw :
    2 * |primitiveBRe χ| *
        (Real.log
            (max 1
                (completedLFunctionBallBound N
                  (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 /
          δ ^ 2) =
      (Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1
                      (completedLFunctionBallBound
                        N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ) ^
        2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hH2nonneg]
    ring
  rw [hrw] at hCSfull
  have hsum_le :
    ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) ≤
      Real.sqrt (2 * |primitiveBRe χ|) *
          Real.sqrt
            (Real.log
                (max 1
                    (completedLFunctionBallBound
                      N (2 * R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) /
        δ := by
    have hrhs_nonneg :
      (0 : ℝ) ≤
        Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1
                      (completedLFunctionBallBound
                        N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ := by
      positivity
    nlinarith [hCSfull, hsum_nonneg, hrhs_nonneg]
  calc
    ‖completedLFunctionTruncatedGenusSum χ R
            s‖ ≤
        ‖s‖ * ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) :=
      hnorm_le
    _ ≤
        ‖s‖ *
          (Real.sqrt (2 * |primitiveBRe χ|) *
              Real.sqrt
                (Real.log
                    (max 1
                        (completedLFunctionBallBound
                          N (2 * R)) /
                      ‖DirichletCharacter.completedLFunction χ 0‖) /
                  Real.log 2) /
            δ) :=
      mul_le_mul_of_nonneg_left hsum_le (norm_nonneg s)
    _ =
        ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1
                      (completedLFunctionBallBound
                        N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ :=
      by ring

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive nontrivial complex Dirichlet character with
`χ⁻¹ ≠ 1` (no quadratic hypothesis), `R ≥ 1` with no zero of `completedLFunction χ` exactly on
`‖ρ‖ = R`, a point `s` with `‖s‖ ≤ R/2` where `completedLFunction χ` doesn't vanish, and a margin
`δ > 0` separating `s` from every zero inside `ball 0 R`.
Conclusion: `‖logDeriv F(s) - logDeriv F(0)‖` is bounded by the finite-radius error term plus the
Cauchy–Schwarz genus-sum bound.
Content: identical to `norm_centeredLogDeriv_le_of_separation` but built on the `hquad`-free
`DirichletLFunction.norm_completedLFunctionTruncatedGenusSum_le_of_grh` instead; the
triangle-inequality combination
with `DirichletLFunction.norm_centeredLogDeriv_sub_truncatedGenus_le` (from `HadamardLimit`, with
no quadratic hypothesis) is
reused verbatim.
Role: combines the finite-radius error with the genus-sum estimate before choosing a good height.
-/
theorem norm_centeredLogDeriv_le_of_separation_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ} (hR : 1 ≤ R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) {s : ℂ}
    (hs : ‖s‖ ≤ R / 2) (hsne : DirichletCharacter.completedLFunction χ s ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ‖ρ‖ < R → δ ≤ ‖s - ρ‖) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
          logDeriv (DirichletCharacter.completedLFunction χ) 0‖ ≤
      192 * ‖s‖ *
            ((4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
                Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
              1) /
          R ^ 2 +
        2 * ‖s‖ / R ^ 2 *
          (Real.log
              (max 1
                  (completedLFunctionBallBound N
                    (2 * R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) +
        ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1
                      (completedLFunctionBallBound
                        N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ := by
  have hN1 : 1 < N := by omega
  have hH9e :=
    norm_centeredLogDeriv_sub_truncatedGenus_le
      hN1 hprimitive hne hinv hR hzf hs hsne
  have hGenus :=
    norm_completedLFunctionTruncatedGenusSum_le_of_grh
      hN2 hGRH hprimitive hne hinv (show (0 : ℝ) < R by linarith) hsne hδ hsep
  calc
    ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
            logDeriv (DirichletCharacter.completedLFunction χ) 0‖ =
        ‖((logDeriv (DirichletCharacter.completedLFunction χ) s -
                logDeriv (DirichletCharacter.completedLFunction χ) 0) -
              completedLFunctionTruncatedGenusSum
                χ R s) +
            completedLFunctionTruncatedGenusSum
              χ R s‖ :=
      by ring_nf
    _ ≤
        ‖(logDeriv (DirichletCharacter.completedLFunction χ) s -
                logDeriv (DirichletCharacter.completedLFunction χ) 0) -
              completedLFunctionTruncatedGenusSum
                χ R s‖ +
          ‖completedLFunctionTruncatedGenusSum χ
              R s‖ :=
      norm_add_le _ _
    _ ≤ _ := add_le_add hH9e hGenus

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
