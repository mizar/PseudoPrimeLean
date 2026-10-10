/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardLimit
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveCharacterInv
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedLFunctionConj
public import PseudoPrime.AnalyticNumberTheory.General.DerivativeNorm

/-!
# Functional equations and zero-mass estimates for primitive characters

The pair `(χ,χ⁻¹)` gives reflection of completed zeros and a logarithmic-derivative
functional equation. Under GRH, the zeros lie on the critical line and their mass equals
`|primitiveBRe χ|`. Conjugation identifies the constants for inverse characters.
The resulting estimates control weighted zero sums, the derivative at zero, and truncated
genus sums. No quadratic-character assumption or LLS numerical inequality is used.
-/

@[expose] public section

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
  · rw [heven.gammaFactor_def, (DirichletCharacter.even_inv_iff.mpr heven).gammaFactor_def]
  · rw [hodd.gammaFactor_def, (DirichletCharacter.odd_inv_iff.mpr hodd).gammaFactor_def]

/--
Input/assumptions: a nontrivial complex Dirichlet character, and `w : ℂ` with `1 ≤ w.re`.
Conclusion: `completedLFunction χ w ≠ 0`.
Content: `L = F / gammaFactor` (unconditionally, since `0 / x = 0`) turns `F w = 0` into
`L w = 0`, contradicting mathlib's `LFunction_ne_zero_of_one_le_re`.
-/
theorem completedLFunction_ne_zero_of_one_le_re {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {w : ℂ} (hw : 1 ≤ w.re) : DirichletCharacter.completedLFunction χ w ≠ 0 := by
  intro h
  have hLeq :=
    dirichletLFunction_eq_completed_div_gammaFactor χ w
      (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne))
  rw [h, zero_div] at hLeq
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) hw hLeq

/-- A completed zero of a nontrivial character has real part less than one.
Apply unconditional right-half-plane nonvanishing; no RH assumption is needed.
The inequality also classifies zeros reflected by the functional equation. -/
theorem completedLFunction_zero_re_lt_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {s : ℂ} (hz : χ.completedLFunction s = 0) : s.re < 1 := by
  exact lt_of_not_ge (fun hs ↦ completedLFunction_ne_zero_of_one_le_re hne hs hz)

/-- A primitive character with nontrivial inverse has no completed zero in `Re s ≤ 0`.
Reflect the zero to the inverse character and apply its right-half-plane nonvanishing.
The positive real part excludes trivial zeros when using individual Dirichlet RH. -/
theorem completedLFunction_zero_re_pos {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {s : ℂ} (hz : χ.completedLFunction s = 0) : 0 < s.re := by
  have he : (1 : ℂ) - (1 - s) = s := by ring
  have hi := dirichletCompletedLFunction_inv_zero_of_one_sub_zero hp (1 - s) (he.symm ▸ hz)
  have hb := completedLFunction_zero_re_lt_one hinv hi
  simp only [Complex.sub_re, Complex.one_re] at hb
  linarith only [hb]

/-- Individual Dirichlet RH puts every completed zero of a primitive character on the line.
The inverse is nontrivial. Unconditional reflection first gives positive real part,
so the ordinary zero is outside the trivial-zero set. This transfers the hypothesis
of Lemma 2.5 to the general completed-function RH predicate without assuming global GRH. -/
theorem completedLFunction_zero_re_eq_half_of_dirichletRH {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) {s : ℂ} (hz : χ.completedLFunction s = 0) : s.re = 1 / 2 := by
  have hs := completedLFunction_zero_re_pos hp hinv hz
  have hs0 : s ≠ 0 := fun he ↦ (ne_of_gt hs) (congrArg Complex.re he)
  have hL := dirichletLFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  rw [hz, zero_div] at hL
  exact hRH s hL (GRH.not_mem_dirichletTrivialZeros_of_re_pos χ hs)

/--
Input/assumptions: GRH, primitive nontrivial `χ`, `χ⁻¹ ≠ 1`, and a completed-function zero.
Conclusion: the zero has real part `1 / 2`.
Proof: unconditional nonvanishing on `Re s ≥ 1` excludes the right half-plane; the functional
equation reflects a zero with `Re s ≤ 0` to a forbidden zero of the inverse character.
The zero therefore has positive real part and is an ordinary `L`-function zero, to which GRH
applies.
Role: supplies critical-line classification for zero-mass and summability estimates.
-/
theorem completedLFunction_zero_re_eq_half {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (_hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {ρ : ℂ} (hzero : DirichletCharacter.completedLFunction χ ρ = 0) :
    ρ.re = (1 : ℝ) / 2 := by
  exact
    completedLFunction_zero_re_eq_half_of_dirichletRH (hGRH N χ hprimitive) hprimitive hinv hzero

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
    meromorphicOrderAt_dirichletCompletedLFunction_eq_zero_of_ne_zero hne hρne]
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
      linarith only [hρ]
    have h2 : (1 - ρ).im = (starRingEnd ℂ ρ).im := by
      simp only [Complex.sub_im, Complex.one_im, zero_sub, Complex.conj_im]
    exact Complex.ext h1 h2
  simp only [hconj, one_div, ← map_inv₀ (starRingEnd ℂ) ρ, Complex.add_re, Complex.conj_re]
  ring

/-- Half the real genus-one sum at one equals the inverse-zero mass under individual RH.
Use critical-line reflection and real-part summability to extract the factor two.
The character is primitive and nontrivial, with nontrivial inverse.
This supplies the local-RH mass input to Lemma 2.5. -/
theorem dirichletCompletedLFunctionZeroMass_eq_tsum_re_inv_of_dirichletRH {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (1 / 2 : ℝ) *
        (∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (1 / (1 - ρ) + 1 / ρ)).re =
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re := by
  have hsummable := summable_completedLFunctionGenusOneTerm_one hN2 hprimitive hne hinv
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
        dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD0
      have hre_half : ρ.re = (1 : ℝ) / 2 :=
        completedLFunction_zero_re_eq_half_of_dirichletRH hRH hprimitive hinv hzero
      have hterm := genusOneTerm_re_eq_of_re_eq_half hre_half
      have hcast : ((D : ℤ) : ℂ) = (((D : ℤ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, Complex.re_ofReal_mul, hterm]
      ring
  rw [Complex.re_tsum hsummable, tsum_congr hpt, tsum_mul_left]
  ring

/--
For GRH, `2 ≤ N`, primitive nontrivial `χ`, and `χ⁻¹ ≠ 1`, half the real part of the global
genus-one sum at one equals `Z_χ = Σ' ρ, m_ρ Re(1/ρ)`.
Proof: at every zero, critical-line reflection makes the genus term's real part twice
`Re(1/ρ)`; terms with zero multiplicity vanish. Summability permits taking the real part
inside the sum, and constant multiplication extracts the factor two.
Role: converts the centered Hadamard identity into the real zero mass.
-/
theorem dirichletCompletedLFunctionZeroMass_eq_tsum_re_inv {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (1 / 2 : ℝ) *
        (∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (1 / (1 - ρ) + 1 / ρ)).re =
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re := by
  exact
    dirichletCompletedLFunctionZeroMass_eq_tsum_re_inv_of_dirichletRH hN2 (hGRH N χ hprimitive)
      hprimitive hne hinv

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
For primitive nontrivial `χ` and a point `s` where `F(χ⁻¹)(s) ≠ 0`,
`-logDeriv F(χ)(1-s) = Complex.log N + logDeriv F(χ⁻¹)(s)`.
Proof: apply the chain rule to the reflected completed function and the product rule to
`N^(z-1/2) * rootNumber χ * F(χ⁻¹)(z)`. The root number and conductor power are nonzero;
the former is constant and the latter contributes `Complex.log N`.
Role: gives the inverse-character functional equation used at zero and in endpoint estimates.
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
Role: supplies the endpoint functional equation used in the paired Hadamard-constant identity.
-/
theorem completedLFunction_logDeriv_functionalEquation_at_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    -logDeriv (DirichletCharacter.completedLFunction χ) 1 =
      Complex.log N + logDeriv (DirichletCharacter.completedLFunction χ⁻¹) 0 := by
  have hprimitiveinv : χ⁻¹.IsPrimitive := DirichletCharacter.isPrimitive_inv hprimitive
  have hF0ne : DirichletCharacter.completedLFunction χ⁻¹ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitiveinv hinv
  have h := completedLFunction_logDeriv_functionalEquation_at hprimitive hne (s := 0) hF0ne
  simpa only [sub_zero] using h

/-- The two inverse-character Hadamard constants sum to minus twice the real zero mass.
Under individual RH, combine the centered Hadamard identity with the functional equation.
The character is primitive and nontrivial, with nontrivial inverse.
This supplies the local-RH mass input to Lemma 2.5. -/
theorem primitiveBRe_add_inv_eq_neg_two_mul_zeroMass_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    primitiveBRe χ + primitiveBRe χ⁻¹ =
      -(2 *
          ∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
              (1 / ρ).re) := by
  have hprimitiveinv : χ⁻¹.IsPrimitive := DirichletCharacter.isPrimitive_inv hprimitive
  have hH9g := completedLFunction_centeredLogDeriv_one_eq_tsum hN2 hprimitive hne hinv
  have hH6 :=
    dirichletCompletedLFunctionZeroMass_eq_tsum_re_inv_of_dirichletRH hN2 hRH hprimitive hne hinv
  have hG5 := completedLFunction_logDeriv_functionalEquation_at_zero hprimitive hne hinv
  have hlogNre : (Complex.log (N : ℂ)).re = Real.log N := by
    rw [show ((N : ℂ)) = ((N : ℝ) : ℂ) from by
        push_cast
        ring]
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
  rw [primitiveBRe, primitiveBRe, (hprimitive : χ.conductor = N),
    (hprimitiveinv : χ⁻¹.conductor = N)]
  linarith only [hre9g, hre5, hH6]

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
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    primitiveBRe χ + primitiveBRe χ⁻¹ =
      -(2 *
          ∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
              (1 / ρ).re) := by
  exact
    primitiveBRe_add_inv_eq_neg_two_mul_zeroMass_of_dirichletRH hN2 (hGRH N χ hprimitive) hprimitive
      hne hinv

/-- The real inverse-zero mass is nonnegative under individual RH.
Entire-function divisor multiplicities and critical-line inverse real parts are nonnegative.
The character is primitive and nontrivial, with nontrivial inverse.
This supplies the local-RH mass input to Lemma 2.5. -/
theorem primitiveZeroMass_nonneg_of_dirichletRH {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
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
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_dirichletRH hRH hprimitive hinv hzero
    have hinv_re_pos : 0 ≤ (1 / ρ).re := by
      rw [one_div, Complex.inv_re, hre_half]
      exact div_nonneg (by norm_num only) (Complex.normSq_nonneg ρ)
    exact mul_nonneg hDnonneg hinv_re_pos

/--
Under GRH, primitive nontrivial `χ` with `χ⁻¹ ≠ 1` has nonnegative real zero mass
`Z_χ = Σ' ρ, m_ρ Re(1/ρ)`.
Proof: the entire completed function has nonnegative divisor multiplicities. At every zero,
GRH gives `Re(1/ρ) = (1/2)/normSq ρ ≥ 0`; all other summands vanish.
Apply `tsum_nonneg`. Role: identifies the sign needed for absolute-value Hadamard bounds.
-/
theorem primitiveZeroMass_nonneg {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
    0 ≤
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re := by
  exact primitiveZeroMass_nonneg_of_dirichletRH (hGRH N χ hprimitive) hprimitive hne hinv

/-- Under individual RH, a primitive nonprincipal character of modulus at least two has
summable completed-zero inverse-square divisor mass. Take real parts of the convergent
genus-one series at one and identify critical-line terms. Only this character's RH is needed
for shifted logarithmic zero bounds. -/
theorem summable_divisor_div_normSq_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Summable
      (fun ρ : ℂ ↦
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ) := by
  have hsummable := summable_completedLFunctionGenusOneTerm_one hN2 hprimitive hne hinv
  have hsummableRe := Complex.reCLM.summable hsummable
  apply hsummableRe.congr
  intro ρ
  set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
  by_cases hD0 : D = 0
  · simp only [hD0, Int.cast_zero, one_div, zero_mul, Complex.reCLM_apply, Complex.zero_re,
      zero_div]
  · have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_dirichletRH hRH hprimitive hinv hzero
    have hterm := genusOneTerm_re_eq_of_re_eq_half hre_half
    have hInvRe : (1 / ρ).re = (1 : ℝ) / 2 / Complex.normSq ρ := by
      rw [one_div, Complex.inv_re, hre_half]
    have hcast : ((D : ℤ) : ℂ) = (((D : ℤ) : ℝ) : ℂ) := (Complex.ofReal_intCast D).symm
    change Complex.reCLM (((D : ℤ) : ℂ) * (1 / (1 - ρ) + 1 / ρ)) = ((D : ℤ) : ℝ) / Complex.normSq ρ
    rw [Complex.reCLM_apply, hcast, Complex.re_ofReal_mul, hterm, hInvRe]
    ring

/--
Under GRH, `2 ≤ N`, primitive nontrivial `χ`, and `χ⁻¹ ≠ 1`, the family
`ρ ↦ m_ρ / normSq ρ` is summable.
Proof: take real parts of the summable genus-one family at one. On the critical line each
real part is exactly `m_ρ / normSq ρ`, and zero-multiplicity terms vanish.
Role: justifies estimates by sums of norms for weighted completed zeros.
-/
theorem summable_divisor_div_normSq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
    Summable
      (fun ρ : ℂ =>
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ) := by
  exact summable_divisor_div_normSq_of_dirichletRH hN2 (hGRH N χ hprimitive) hprimitive hne hinv

/--
Under GRH, primitive nontrivial `χ`, `χ⁻¹ ≠ 1`, and `x > 0`, every `ρ` satisfies
`‖m_ρ x^(ρ-1)/(ρ(ρ-1))‖ = (m_ρ/normSq ρ)/√x`.
Proof: the identity is immediate for zero multiplicity. Otherwise GRH gives critical-line
reflection, `ρ(ρ-1) = -normSq ρ`, and `‖x^(ρ-1)‖ = 1/√x`; multiplicity is nonnegative.
Role: provides the pointwise norm identity for reciprocal zero sums.
-/
theorem norm_completedReciprocalZeroTerm_eq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
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
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half hGRH hprimitive hne hinv hzero
    have hconj : (1 : ℂ) - ρ = starRingEnd ℂ ρ := by
      have h1 : (1 - ρ).re = (starRingEnd ℂ ρ).re := by
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith only [hre_half]
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

/-- The inverse-square divisor mass equals twice the inverse-zero mass under individual RH.
Use Re(1/ρ) = (1/2)/normSq ρ termwise, including zero-multiplicity points.
The character is primitive and nontrivial, with nontrivial inverse.
This supplies the local-RH mass input to Lemma 2.5. -/
theorem tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_dirichletRH {N : ℕ} [NeZero N] (_hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ)
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
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_dirichletRH hRH hprimitive hinv hzero
    have hInvRe : (1 / ρ).re = (1 : ℝ) / 2 / Complex.normSq ρ := by
      rw [one_div, Complex.inv_re, hre_half]
    rw [hInvRe]
    ring

/--
Under GRH, primitive nontrivial `χ`, and `χ⁻¹ ≠ 1`, the inverse-square zero sum equals `2 Z_χ`,
where `Z_χ = Σ' ρ, m_ρ Re(1/ρ)`. The retained level assumption is unused in this proof.
Proof: termwise, GRH gives `Re(1/ρ) = (1/2)/normSq ρ` at every zero; zero-multiplicity
terms vanish. Move the constant two through the total sum.
Role: feeds reciprocal, logarithmic, and derivative zero-contribution bounds.
-/
theorem tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh {N : ℕ} [NeZero N] (_hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ =
      2 *
        ∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re := by
  exact
    tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_dirichletRH _hN2 (hGRH N χ hprimitive) hprimitive
      hne hinv

/--
Under GRH, `2 ≤ N`, primitive nontrivial `χ`, `χ⁻¹ ≠ 1`, and the retained assumption `R > 0`,
the truncated genus sum has a derivative `D` at zero with `‖D‖ ≤ 2 Z_χ`.
Proof: its divisor has finite support and does not contain zero. Differentiate each term to
obtain `D = Σ m_ρ (-1/ρ²)` on that support; the sum of its norms is bounded by the global
nonnegative inverse-square mass `2 Z_χ`. Positivity of `R` is not needed by this argument.
Role: supplies the finite-genus derivative estimate for the logarithmic residue at zero.
-/
theorem exists_hasDerivAt_completedLFunctionTruncatedGenusSum_zero_norm_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hN2 : 2 ≤ N) {R : ℝ}
    (_hR : 0 < R) :
    ∃ D : ℂ,
      HasDerivAt (completedLFunctionTruncatedGenusSum χ R) D 0 ∧
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
    dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  have hkey : ∀ u ∈ hfin.toFinset, u ∈ Metric.ball (0 : ℂ) R ∧ u ≠ 0 := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    exact
      ⟨Dv.supportWithinDomain hu,
        ne_of_mem_divisorBallSupport_of_completedLFunction_ne_zero hne hu h0ne⟩
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
    completedLFunctionTruncatedGenusSum χ R = fun s : ℂ =>
      ∑ ρ ∈ hfin.toFinset, ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
    funext s
    rw [completedLFunctionTruncatedGenusSum, finsum_eq_sum_of_support_subset _ (hsub s)]
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
  · have hsummable := summable_divisor_div_normSq hN2 hGRH hprimitive hne hinv
    have htsum := tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh hN2 hGRH hprimitive hne hinv
    have hterm :
      ∀ ρ ∈ hfin.toFinset,
        ‖((Dv ρ : ℤ) : ℂ) * (-(1 / ρ ^ 2))‖ =
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
            Complex.normSq ρ := by
      intro ρ hρ
      obtain ⟨hρball, _⟩ := hkey ρ hρ
      have hDeq :
        Dv ρ = MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ := by
        rw [hDv_def, divisor_ball_eq_if_univ hne,
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
          (max 1 (completedLFunctionBallBound N (2 * R)) /
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
    Filter.Tendsto (completedLFunctionH9eSlopeError χ) Filter.atTop (nhds 0) := by
  have h1 :=
    tendsto_const_mul_add_mul_log_add_const_div_sq_atTop 192 (4 * (N : ℝ) + 3)
      (-Real.log ‖DirichletCharacter.completedLFunction χ 0‖ + 1)
  have h2 := tendsto_h9dError_atTop hN2 hprimitive hne hinv
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
    (hD : HasDerivAt (completedLFunctionTruncatedGenusSum χ R) D 0) :
    ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0 - D‖ ≤
      completedLFunctionH9eSlopeError χ R := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have h0ne : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  set F := DirichletCharacter.completedLFunction χ
  have hLogHasDeriv : HasDerivAt (logDeriv F) (deriv (logDeriv F) 0) 0 :=
    (differentiableAt_logDeriv_completedLFunction_zero hprimitive hne).hasDerivAt
  have hQ :
    HasDerivAt
      (fun s : ℂ => (logDeriv F s - logDeriv F 0) - completedLFunctionTruncatedGenusSum χ R s)
      (deriv (logDeriv F) 0 - D) 0 :=
    (hLogHasDeriv.sub_const _).sub hD
  have hQ0 : (logDeriv F 0 - logDeriv F 0) - completedLFunctionTruncatedGenusSum χ R 0 = 0 := by
    rw [sub_self, completedLFunctionTruncatedGenusSum_zero, zero_sub, neg_zero]
  have hRpos : (0 : ℝ) < R := by exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hR
  have hev : ∀ᶠ s : ℂ in nhds (0 : ℂ), ‖s‖ ≤ R / 2 ∧ F s ≠ 0 := by
    have h1 : ∀ᶠ s : ℂ in nhds (0 : ℂ), ‖s‖ ≤ R / 2 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
          (show (0 : ℝ) < R / 2 by exact div_pos hRpos (by norm_num only : (0 : ℝ) < 2))] with
        s hs
      rw [Metric.mem_ball, dist_zero_right] at hs
      exact hs.le
    have h2 : ∀ᶠ s : ℂ in nhds (0 : ℂ), F s ≠ 0 :=
      (hdiff.continuous.continuousAt).eventually_ne h0ne
    filter_upwards [h1, h2] with s hs1 hs2 using ⟨hs1, hs2⟩
  have hbound :
    ∀ᶠ s : ℂ in nhdsWithin 0 ({0}ᶜ : Set ℂ),
      ‖(logDeriv F s - logDeriv F 0) - completedLFunctionTruncatedGenusSum χ R s‖ ≤
        completedLFunctionH9eSlopeError χ R * ‖s‖ := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with s hs
    have h9e := norm_centeredLogDeriv_sub_truncatedGenus_le hN1 hprimitive hne hinv hR hzf hs.1 hs.2
    have hfactor :
      192 * ‖s‖ * ((4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) - Real.log ‖F 0‖ + 1) / R ^ 2 +
          2 * ‖s‖ / R ^ 2 *
            (Real.log (max 1 (completedLFunctionBallBound N (2 * R)) / ‖F 0‖) / Real.log 2) =
        completedLFunctionH9eSlopeError χ R * ‖s‖ := by
      unfold completedLFunctionH9eSlopeError
      ring
    rwa [hfactor] at h9e
  exact RiemannXi.norm_deriv_le_of_eventually_norm_le_mul_norm hQ hQ0 hbound

/--
For GRH, `2 ≤ N`, primitive nontrivial `χ`, `χ⁻¹ ≠ 1`, and a zero-free sphere radius `R ≥ 1`,
`‖(logDeriv F)'(0)‖ ≤ completedLFunctionH9eSlopeError χ R + 2 Z_χ`.
Proof: choose the truncated genus derivative bounded by `2 Z_χ`, bound its difference from
`(logDeriv F)'(0)` by the finite-radius slope error, and use the triangle inequality.
Role: gives the fixed-radius estimate before taking the good-radius limit.
-/
theorem norm_deriv_logDeriv_completedLFunction_zero_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hN2 : 2 ≤ N) {R : ℝ} (hR : 1 ≤ R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) :
    ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖ ≤
      completedLFunctionH9eSlopeError χ R +
        2 *
          ∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
              (1 / ρ).re := by
  have hN1 : 1 < N := by exact Nat.lt_of_succ_le hN2
  obtain ⟨D, hD, hDnorm⟩ :=
    exists_hasDerivAt_completedLFunctionTruncatedGenusSum_zero_norm_le hGRH hprimitive hne hinv hN2
      (show (0 : ℝ) < R by exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hR)
  have hsub := norm_deriv_logDeriv_completedLFunction_zero_sub_le hN1 hprimitive hne hinv hR hzf hD
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
Under GRH, `2 ≤ N`, primitive nontrivial `χ`, and `χ⁻¹ ≠ 1`,
`‖(logDeriv F)'(0)‖ ≤ 2 Z_χ`.
Proof: apply the finite-radius derivative estimate along `completedLFunctionGoodRadius`.
These radii are zero-free, are at least one, and tend to infinity; the slope error tends to zero.
Pass the inequalities to the limit using `ge_of_tendsto`.
Role: gives the origin derivative bound needed for the logarithmic Mellin residue.
-/
theorem norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_zeroMass {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hN2 : 2 ≤ N) :
    ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖ ≤
      2 *
        ∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re := by
  have htendError := tendsto_completedLFunctionH9eSlopeError_atTop hN2 hprimitive hne hinv
  have htendComp := htendError.comp (tendsto_completedLFunctionGoodRadius_atTop hne)
  have htendSum :
    Filter.Tendsto
      (fun n : ℕ =>
        completedLFunctionH9eSlopeError χ (completedLFunctionGoodRadius hne n) +
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
        completedLFunctionH9eSlopeError χ (completedLFunctionGoodRadius hne n) +
          2 *
            ∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) *
                (1 / ρ).re := by
    filter_upwards with n
    have hRgt := completedLFunctionGoodRadius_gt hne n
    have hR1 : (1 : ℝ) ≤ completedLFunctionGoodRadius hne n := by
      have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith only [hRgt, hnnn]
    exact
      norm_deriv_logDeriv_completedLFunction_zero_le hGRH hprimitive hne hinv hN2 hR1
        (completedLFunctionGoodRadius_zeroFree hne n)
  exact ge_of_tendsto htendSum hev

/--
Under GRH, `2 ≤ N`, primitive nontrivial `χ`, and `χ⁻¹ ≠ 1`,
`-Re((logDeriv F)'(0)) ≤ 2 Z_χ`.
Proof: the real part of the negative derivative is at most its norm, which equals the norm
of the derivative and is bounded by the origin derivative theorem.
Role: supplies the real-part inequality for logarithmic residue estimates.
-/
theorem neg_re_deriv_logDeriv_completedLFunction_zero_le_of_grh {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hN2 : 2 ≤ N) :
    -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re ≤
      2 *
        ∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re := by
  have hnormBound :=
    norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_zeroMass hGRH hprimitive hne hinv hN2
  have hre := Complex.re_le_norm (-deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0)
  rw [Complex.neg_re, norm_neg] at hre
  exact le_trans hre hnormBound

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
      primitiveBRe χ - (1 / 2) * Real.log N := by
  rw [primitiveBRe, (hprimitive : χ.conductor = N)]
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
Role: gives the endpoint real part at one; conjugation identifies the inverse constant below.
-/
theorem completedLFunction_logDeriv_one_re_eq_neg_primitiveBRe_inv_sub_half_log {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (logDeriv (DirichletCharacter.completedLFunction χ) 1).re =
      -primitiveBRe χ⁻¹ - (1 / 2) * Real.log N := by
  have hprimitiveinv : χ⁻¹.IsPrimitive := DirichletCharacter.isPrimitive_inv hprimitive
  have hFE := completedLFunction_logDeriv_functionalEquation_at_zero hprimitive hne hinv
  have hlogNre : (Complex.log (N : ℂ)).re = Real.log N := by
    rw [show ((N : ℕ) : ℂ) = ((N : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.log_ofReal_re]
  have hFEre :
    -(logDeriv (DirichletCharacter.completedLFunction χ) 1).re =
      Real.log N + (logDeriv (DirichletCharacter.completedLFunction χ⁻¹) 0).re := by
    have := congrArg Complex.re hFE
    simpa only [Complex.neg_re, Complex.add_re, hlogNre] using this
  have hzero := completedLFunction_logDeriv_zero_re_eq_primitiveBRe_sub_half_log hprimitiveinv
  linarith only [hFEre, hzero]

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
    primitiveBRe χ⁻¹ = primitiveBRe χ := by
  have hFconj0 := DirichletCharacter.completedLFunction_conj χ 0
  simp only [map_zero] at hFconj0
  have hderivconj := DirichletCharacter.deriv_completedLFunction_zero_conj hne
  rw [primitiveBRe, primitiveBRe, DirichletCharacter.conductor_inv_eq]
  congr 1
  rw [logDeriv_apply, logDeriv_apply, ← hFconj0, ← hderivconj, ← map_div₀, Complex.conj_re]

/-- The Hadamard constant equals minus the real inverse-zero mass under individual RH.
Use the pair identity and conjugation invariance of the real Hadamard constant.
The character is primitive and nontrivial, with nontrivial inverse.
This supplies the local-RH mass input to Lemma 2.5. -/
theorem primitiveBRe_eq_neg_zeroMass_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    primitiveBRe χ =
      -(∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re) := by
  have hpair :=
    primitiveBRe_add_inv_eq_neg_two_mul_zeroMass_of_dirichletRH hN2 hRH hprimitive hne hinv
  rw [primitiveBRe_inv_eq hne] at hpair
  linarith only [hpair]

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
Role: identifies the sign and value of the single-character Hadamard constant.
-/
theorem primitiveBRe_eq_neg_zeroMass {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
    primitiveBRe χ =
      -(∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re) := by
  exact primitiveBRe_eq_neg_zeroMass_of_dirichletRH hN2 (hGRH N χ hprimitive) hprimitive hne hinv

/-- The absolute real Hadamard constant equals the real inverse-zero mass under individual RH.
Combine the signed mass identity with nonnegativity of the mass.
The character is primitive and nontrivial, with nontrivial inverse.
This supplies the local-RH mass input to Lemma 2.5. -/
theorem abs_primitiveBRe_eq_zeroMass_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    |primitiveBRe χ| =
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re := by
  rw [primitiveBRe_eq_neg_zeroMass_of_dirichletRH hN2 hRH hprimitive hne hinv, abs_neg,
    abs_of_nonneg (primitiveZeroMass_nonneg_of_dirichletRH hRH hprimitive hne hinv)]

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: `|PseudoPrime.AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| = Z_χ`.
Content: combines `DirichletLFunction.primitiveBRe_eq_neg_zeroMass` with the sign
information from
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.primitiveZeroMass_nonneg`.
Role: rewrites zero-sum and derivative bounds using the shared constant `|primitiveBRe χ|`.
-/
theorem abs_primitiveBRe_eq_zeroMass {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
    |primitiveBRe χ| =
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re := by
  exact abs_primitiveBRe_eq_zeroMass_of_dirichletRH hN2 (hGRH N χ hprimitive) hprimitive hne hinv

/-- The inverse-square divisor mass equals twice the absolute Hadamard constant under individual RH.
Combine the inverse-square mass identity with the absolute Hadamard-constant identity.
The character is primitive and nontrivial, with nontrivial inverse.
This supplies the local-RH mass input to Lemma 2.5. -/
theorem tsum_divisor_inv_normSq_eq_two_mul_abs_BRe_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ =
      2 * |primitiveBRe χ| := by
  rw [abs_primitiveBRe_eq_zeroMass_of_dirichletRH hN2 hRH hprimitive hne hinv]
  exact tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_dirichletRH hN2 hRH hprimitive hne hinv

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: `Σ' ρ, m_ρ(χ)/normSq ρ = 2 |DirichletLFunction.primitiveBRe χ|`.
Content: `DirichletLFunction.tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh` rewritten via
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass` from the `Z_χ` witness to the
`|DirichletLFunction.primitiveBRe χ|` witness.
Role: the generic application route (Cauchy–Schwarz truncated-genus-sum bound), the shared-witness
zero-mass
identity feeding `DirichletLFunction.norm_completedLFunctionTruncatedGenusSum_le`.
-/
theorem tsum_divisor_inv_normSq_eq_two_mul_abs_BRe {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ =
      2 * |primitiveBRe χ| := by
  exact
    tsum_divisor_inv_normSq_eq_two_mul_abs_BRe_of_dirichletRH hN2 (hGRH N χ hprimitive) hprimitive
      hne hinv

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial mod `N`, GRH, `χ⁻¹ ≠ 1` (no quadratic
hypothesis).
Conclusion: `-Re(deriv(logDeriv F) 0) ≤ 2 |DirichletLFunction.primitiveBRe χ|`.
Content: `DirichletLFunction.neg_re_deriv_logDeriv_completedLFunction_zero_le_of_grh` rewritten via
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass` from the `Z_χ` witness to the
`|DirichletLFunction.primitiveBRe χ|` witness.
Role: supplies its real-part derivative bound for logarithmic residue estimates.
-/
theorem neg_re_deriv_logDeriv_completedLFunction_zero_le_abs_BRe {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hN2 : 2 ≤ N) :
    -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re ≤ 2 * |primitiveBRe χ| := by
  rw [abs_primitiveBRe_eq_zeroMass hN2 hGRH hprimitive hne hinv]
  exact neg_re_deriv_logDeriv_completedLFunction_zero_le_of_grh hGRH hprimitive hne hinv hN2

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: `(logDeriv (completedLFunction χ) 0).re = -|DirichletLFunction.primitiveBRe χ| - (1/2)
log N`.
Content: substitute `DirichletLFunction.primitiveBRe_eq_neg_zeroMass` and
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass`
into `DirichletLFunction.completedLFunction_logDeriv_zero_re_eq_primitiveBRe_sub_half_log`.
Role: supplies the shared-constant endpoint closed form at `s = 0` under GRH.
-/
theorem completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (logDeriv (DirichletCharacter.completedLFunction χ) 0).re =
      -|primitiveBRe χ| - (1 / 2) * Real.log N := by
  have hB := primitiveBRe_eq_neg_zeroMass hN2 hGRH hprimitive hne hinv
  have habs := abs_primitiveBRe_eq_zeroMass hN2 hGRH hprimitive hne hinv
  have hBneg : primitiveBRe χ = -|primitiveBRe χ| := by rw [habs, hB]
  have hBRe := completedLFunction_logDeriv_zero_re_eq_primitiveBRe_sub_half_log hprimitive
  rw [hBneg] at hBRe
  exact hBRe

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis).
Conclusion: `(logDeriv (completedLFunction χ) 1).re = |DirichletLFunction.primitiveBRe χ| - (1/2)
log N`.
Content: rewrite
`DirichletLFunction.completedLFunction_logDeriv_one_re_eq_neg_primitiveBRe_inv_sub_half_log`'s
`DirichletLFunction.primitiveBRe χ⁻¹` term via `DirichletLFunction.primitiveBRe_inv_eq` to
`DirichletLFunction.primitiveBRe χ`, then apply
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass`/
`DirichletLFunction.primitiveBRe_eq_neg_zeroMass`
to identify the sign.
Role: supplies the shared-constant endpoint identity at one, without an inverse-character term.
-/
theorem completedLFunction_logDeriv_one_re_eq_abs_BRe_sub_half_log {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (logDeriv (DirichletCharacter.completedLFunction χ) 1).re =
      |primitiveBRe χ| - (1 / 2) * Real.log N := by
  have hone :=
    completedLFunction_logDeriv_one_re_eq_neg_primitiveBRe_inv_sub_half_log hprimitive hne hinv
  rw [primitiveBRe_inv_eq hne] at hone
  have hB := primitiveBRe_eq_neg_zeroMass hN2 hGRH hprimitive hne hinv
  have habs := abs_primitiveBRe_eq_zeroMass hN2 hGRH hprimitive hne hinv
  have hBneg : primitiveBRe χ = -|primitiveBRe χ| := by rw [habs, hB]
  rw [hBneg] at hone
  linarith only [hone]

/-- For a primitive nonprincipal character with nonprincipal inverse under its own RH,
a positive radius and separation margin give the displayed truncated genus-sum bound.
Weighted Cauchy-Schwarz uses the individually proved inverse-square zero mass and Jensen's
zero-count estimate. This removes full GRH from the horizontal logarithmic-derivative input. -/
theorem norm_completedLFunctionTruncatedGenusSum_le_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ} (hR : 0 < R) {s : ℂ}
    (hsne : DirichletCharacter.completedLFunction χ s ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ‖ρ‖ < R → δ ≤ ‖s - ρ‖) :
    ‖completedLFunctionTruncatedGenusSum χ R s‖ ≤
      ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
          Real.sqrt
            (Real.log
                (max 1 (completedLFunctionBallBound N (2 * R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) /
        δ := by
  have hN1 : 1 < N := by exact Nat.lt_of_succ_le hN2
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
    dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
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
      field_simp [hρ0, hsρ]
      ring
    rw [hid, norm_mul, norm_div, norm_mul, Complex.norm_intCast,
      abs_of_nonneg (show (0 : ℝ) ≤ (Dv ρ : ℝ) by exact_mod_cast hDv_nonneg ρ)]
    ring
  -- Step 3: triangle inequality
  have hnorm_le :
    ‖completedLFunctionTruncatedGenusSum χ R s‖ ≤ ‖s‖ * ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) := by
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
  have hfactorA : ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖ρ‖ ^ 2 ≤ 2 * |primitiveBRe χ| := by
    have hterm_eq2 :
      ∀ ρ ∈ S,
        (Dv ρ : ℝ) / ‖ρ‖ ^ 2 =
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
            Complex.normSq ρ := by
      intro ρ hρS
      rw [hS_def, Set.Finite.mem_toFinset, Function.mem_support] at hρS
      have hρmem := hρ_ball ρ hρS
      rw [← Complex.normSq_eq_norm_sq, hDv_def, divisor_completedLFunction_domain_eq hne hρmem]
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
        (summable_divisor_div_normSq_of_dirichletRH hN2 hRH hprimitive hne hinv).sum_le_tsum S
          (fun i _ =>
            div_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnU i)
              (Complex.normSq_nonneg i))
      _ = 2 * |primitiveBRe χ| :=
        tsum_divisor_inv_normSq_eq_two_mul_abs_BRe_of_dirichletRH hN2 hRH hprimitive hne hinv
  -- Step 5b: bound the second Cauchy–Schwarz factor via the good-height margin
  have hfactorB :
    ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 ≤
      (Real.log
            (max 1 (completedLFunctionBallBound N (2 * R)) /
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
            (max 1 (completedLFunctionBallBound N (2 * R)) /
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
      exact finsum_divisor_ball_completedLFunction_le hN1 hprimitive hne hinv hR
    calc
      ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 ≤ ∑ ρ ∈ S, (Dv ρ : ℝ) / δ ^ 2 := Finset.sum_le_sum hterm_le
      _ = (∑ ρ ∈ S, (Dv ρ : ℝ)) / δ ^ 2 := by rw [Finset.sum_div]
      _ ≤ _ := by gcongr
  -- Step 6: combine
  have hH2nonneg :
    (0 : ℝ) ≤
      Real.log
          (max 1 (completedLFunctionBallBound N (2 * R)) /
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
        (finsum_divisor_completedLFunction_le hN1 hprimitive hne hinv hR)
  have hCSfull :
    (∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖)) ^ 2 ≤
      2 * |primitiveBRe χ| *
        (Real.log
            (max 1 (completedLFunctionBallBound N (2 * R)) /
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
            (max 1 (completedLFunctionBallBound N (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 /
          δ ^ 2) =
      (Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * R)) /
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
                (max 1 (completedLFunctionBallBound N (2 * R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) /
        δ := by
    have hrhs_nonneg :
      (0 : ℝ) ≤
        Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ := by
      positivity
    nlinarith only [hCSfull, hsum_nonneg, hrhs_nonneg]
  calc
    ‖completedLFunctionTruncatedGenusSum χ R s‖ ≤ ‖s‖ * ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) :=
      hnorm_le
    _ ≤
        ‖s‖ *
          (Real.sqrt (2 * |primitiveBRe χ|) *
              Real.sqrt
                (Real.log
                    (max 1 (completedLFunctionBallBound N (2 * R)) /
                      ‖DirichletCharacter.completedLFunction χ 0‖) /
                  Real.log 2) /
            δ) :=
      mul_le_mul_of_nonneg_left hsum_le (norm_nonneg s)
    _ =
        ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ :=
      by ring

/--
For GRH, `2 ≤ N`, primitive nontrivial `χ`, `χ⁻¹ ≠ 1`, and `R > 0`, assume `F(s) ≠ 0`
and a margin `δ > 0` separating `s` from every completed zero in `ball 0 R`.
The truncated genus sum is bounded by
`‖s‖ √(2|primitiveBRe χ|) √(log(max 1 (completedLFunctionBallBound N (2R))/‖F(0)‖)/log 2) / δ`.
Proof: rewrite over the finite divisor support and use the term norm
`m_ρ ‖s‖/(‖ρ‖ ‖s-ρ‖)`. Weighted Cauchy–Schwarz bounds the inverse-square factor by
`2|primitiveBRe χ|`; separation and the Jensen zero-count bound control the other factor.
Role: supplies the genus term in the horizontal logarithmic-derivative estimate.
-/
theorem norm_completedLFunctionTruncatedGenusSum_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ} (hR : 0 < R) {s : ℂ}
    (hsne : DirichletCharacter.completedLFunction χ s ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ‖ρ‖ < R → δ ≤ ‖s - ρ‖) :
    ‖completedLFunctionTruncatedGenusSum χ R s‖ ≤
      ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
          Real.sqrt
            (Real.log
                (max 1 (completedLFunctionBallBound N (2 * R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) /
        δ := by
  exact
    norm_completedLFunctionTruncatedGenusSum_le_of_dirichletRH hN2 (hGRH N χ hprimitive) hprimitive
      hne hinv hR hsne hδ hsep

/-- For N >= 2 and a primitive nonprincipal character with nonprincipal inverse under
its individual RH, assume a zero-free sphere of radius R >= 1, norm s <= R/2,
F(s) != 0 and a positive distance margin from every completed zero in the ball.
Bound the centered logarithmic derivative by the finite-radius remainder plus the
weighted Cauchy-Schwarz genus estimate. This supplies the signed horizontal bounds. -/
theorem norm_centeredLogDeriv_le_of_separation_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ)
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
              (max 1 (completedLFunctionBallBound N (2 * R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) +
        ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ := by
  have hN1 : 1 < N := by exact Nat.lt_of_succ_le hN2
  have hH9e := norm_centeredLogDeriv_sub_truncatedGenus_le hN1 hprimitive hne hinv hR hzf hs hsne
  have hGenus :=
    norm_completedLFunctionTruncatedGenusSum_le_of_dirichletRH hN2 hRH hprimitive hne hinv
      (show (0 : ℝ) < R by exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hR) hsne hδ hsep
  calc
    ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
            logDeriv (DirichletCharacter.completedLFunction χ) 0‖ =
        ‖((logDeriv (DirichletCharacter.completedLFunction χ) s -
                logDeriv (DirichletCharacter.completedLFunction χ) 0) -
              completedLFunctionTruncatedGenusSum χ R s) +
            completedLFunctionTruncatedGenusSum χ R s‖ :=
      by ring_nf
    _ ≤
        ‖(logDeriv (DirichletCharacter.completedLFunction χ) s -
                logDeriv (DirichletCharacter.completedLFunction χ) 0) -
              completedLFunctionTruncatedGenusSum χ R s‖ +
          ‖completedLFunctionTruncatedGenusSum χ R s‖ :=
      norm_add_le _ _
    _ ≤ _ := add_le_add hH9e hGenus

/--
For GRH, `2 ≤ N`, primitive nontrivial `χ`, and `χ⁻¹ ≠ 1`, assume a zero-free sphere
radius `R ≥ 1`, `‖s‖ ≤ R/2`, `F(s) ≠ 0`, and a positive distance margin from zeros in `ball 0 R`.
The centered logarithmic derivative is bounded by the two finite-radius error terms plus
the Cauchy–Schwarz genus estimate displayed below.
Proof: write it as the truncated genus sum plus its remainder, apply the triangle inequality,
and combine the finite-radius remainder and separated genus-sum bounds.
Role: prepares the quantitative horizontal bound for a chosen good height.
-/
theorem norm_centeredLogDeriv_le_of_separation {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
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
              (max 1 (completedLFunctionBallBound N (2 * R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) +
        ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ := by
  exact
    norm_centeredLogDeriv_le_of_separation_of_dirichletRH hN2 (hGRH N χ hprimitive) hprimitive hne
      hinv hR hzf hs hsne hδ hsep

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
