/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroCounting
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardMultiplicityFactorization
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorMultiplicityBridge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.QuadraticFunctionalConsequences

/-!
# Ordinary zero contributions and completed-zero bounds

The two contribution functions use `dirichletLFunctionZeroMultiplicity` for the
ordinary, uncompleted `LFunction`: `-mρ*x^(ρ-1)/(ρ*(ρ-1))` and `-mρ*x^ρ/ρ²`.
At points where the gamma factor is nonzero, the multiplicity bridge identifies this
with the completed-function divisor. At the remaining nonzero points, trivial-zero
sign estimates suffice. GRH completed-zero mass bounds then control arbitrary finite
subsets, in both quadratic and general primitive-character forms.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
The reciprocal contribution `-mρ*x^(ρ-1)/(ρ*(ρ-1))`, where `mρ` is the ordinary
`LFunction` analytic multiplicity. Defined for every real `x`, character, and complex
point; the residue interpretation away from the Mellin points is proved separately.
-/
noncomputable def dirichletLFunctionReciprocalZeroContribution {N : ℕ} [NeZero N] (x : ℝ)
    (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℂ :=
  -(dirichletLFunctionZeroMultiplicity χ ρ : ℂ) * (x : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))

/--
The logarithmic contribution `-mρ*x^ρ/ρ²`, where `mρ` is the ordinary
`LFunction` analytic multiplicity. Defined for every real `x`, character, and complex
point; the residue interpretation away from zero is proved separately.
-/
noncomputable def dirichletLFunctionLogZeroContribution {N : ℕ} [NeZero N] (x : ℝ)
    (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℂ :=
  -(dirichletLFunctionZeroMultiplicity χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ ^ 2

/--
Input/assumptions: `N ≥ 1`, `χ`, `x > 0`, `ρ ≠ 0` with `gammaFactor χ ρ = 0`.
Conclusion: `(dirichletLFunctionLogZeroContribution x χ ρ).re ≤ 0`.
Content: parity dispatch on `Complex.Gammaℝ_eq_zero_iff` shows `ρ` is a genuine negative real
number; on such `ρ`, `x^ρ` is a positive real (`Complex.ofReal_cpow`) and `ρ²` a positive real, so
`-mult · x^ρ/ρ²` is a real number `≤ 0`.
Role: the log-kernel trivial-zero sign bound.
-/
theorem dirichletLFunctionLogZeroContribution_re_nonpos_of_gammaFactor_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hΓ : DirichletCharacter.gammaFactor χ ρ = 0) :
    (dirichletLFunctionLogZeroContribution x χ ρ).re ≤ 0 := by
  have hreim : ρ.im = 0 ∧ ρ.re < 0 := by
    rcases χ.even_or_odd with heven | hodd
    · rw [heven.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hΓ
      obtain ⟨m, hm⟩ := hΓ
      have hm0 : m ≠ 0 := by
        rintro rfl
        apply hρ0
        rw [hm]
        simp only [CharP.cast_eq_zero, mul_zero, neg_zero]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
      have hρre : ρ = ((-(2 * (m : ℝ)) : ℝ) : ℂ) := by
        rw [hm]; push_cast; ring
      rw [hρre, Complex.ofReal_im, Complex.ofReal_re]
      exact ⟨rfl, by linarith⟩
    · rw [hodd.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hΓ
      obtain ⟨m, hm⟩ := hΓ
      have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hρre : ρ = ((-(2 * (m : ℝ)) - 1 : ℝ) : ℂ) := by
        have : ρ = -(2 * (m : ℂ)) - 1 := by linear_combination hm
        rw [this]; push_cast; ring
      rw [hρre, Complex.ofReal_im, Complex.ofReal_re]
      exact ⟨rfl, by linarith⟩
  obtain ⟨him, hre⟩ := hreim
  have hρeq_real : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [him, Complex.ofReal_im]
  set σ : ℝ := ρ.re with hσ_def
  have hxpow : (x : ℂ) ^ ρ = ((x ^ σ : ℝ) : ℂ) := by
    conv_lhs => rw [hρeq_real]
    rw [Complex.ofReal_cpow hx.le]
  have hxpow_pos : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx _
  have hdenom : ρ ^ 2 = ((σ ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [hρeq_real]
    push_cast; ring
  have hdenom_pos : (0 : ℝ) < σ ^ 2 := by nlinarith [hre]
  set m : ℕ := dirichletLFunctionZeroMultiplicity χ ρ with hm_def
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  unfold dirichletLFunctionLogZeroContribution
  rw [← hm_def, hxpow, hdenom,
    show -(m : ℂ) * ((x ^ σ : ℝ) : ℂ) / ((σ ^ 2 : ℝ) : ℂ) = ((-(m : ℝ) * x ^ σ / σ ^ 2 : ℝ) : ℂ)
      from by
      push_cast; ring,
    Complex.ofReal_re]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [mul_nonneg hmnn hxpow_pos.le]
  · exact hdenom_pos.le

/--
Input/assumptions: GRH, a nonzero level, a primitive nontrivial quadratic complex Dirichlet
character, and
a positive real `x`.
Conclusion: `‖D_ρ x^ρ/ρ²‖ = (D_ρ/normSq ρ) · √x`, where `D_ρ` is the completed-`L` divisor at `ρ`.
Content: extracted from `norm_tsum_logZeroContribution_le`'s pointwise identity, so both a
whole-line `tsum` bound and a finite `Finset` bound below reuse the same computation.
Role: a log-kernel analogue of `DirichletLFunction.norm_completedReciprocalZeroTerm_eq`.
-/
theorem norm_completedLogZeroTerm_eq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
            (x : ℂ) ^ ρ /
          ρ ^ 2‖ =
      Real.sqrt x *
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ) := by
  set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
  by_cases hD0 : D = 0
  · simp only [hD0, Int.cast_zero, zero_mul, zero_div, norm_zero, mul_zero]
  · have hDnonneg : (0 : ℝ) ≤ (D : ℝ) := by
      have hdiff := DirichletCharacter.differentiable_completedLFunction hne
      have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
        fun z _ => hdiff.analyticAt z
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic ρ
    have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_grh_quadratic hGRH hprimitive hne hquad hzero
    have hnormsq : ‖ρ ^ 2‖ = Complex.normSq ρ := by rw [norm_pow, ← Complex.normSq_eq_norm_sq]
    have hnormpow : ‖(x : ℂ) ^ ρ‖ = Real.sqrt x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre_half, ← Real.sqrt_eq_rpow]
    rw [norm_div, norm_mul, Complex.norm_intCast, abs_of_nonneg hDnonneg, hnormpow, hnormsq]
    ring

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive nontrivial quadratic complex Dirichlet character,
`x > 0`, and an arbitrary `Finset ℂ`.
Conclusion: `∑ ρ ∈ S, ‖D_ρ x^ρ/ρ²‖ ≤ 2√x |Re B(χ)|`.
Content: `Summable.sum_le_tsum` (the term is pointwise nonnegative) plus the same calc chain as
`norm_tsum_logZeroContribution_le` (`norm_completedLogZeroTerm_eq`, `tsum_mul_left`,
`DirichletLFunction.tsum_divisor_inv_normSq_eq_two_mul_abs_BRe`) — the finite-sum bound follows the
whole-line `tsum`
bound without needing the norm-of-tsum triangle inequality.
Role: a log-kernel analogue of `sum_norm_completedReciprocalZeroTerm_le`, uniform in `S`.
-/
theorem sum_norm_completedLogZeroTerm_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) (S : Finset ℂ) :
    ∑ ρ ∈ S,
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2‖ ≤
      2 * Real.sqrt x * |primitiveBRe χ| := by
  have hsummableInv :=
    summable_divisor_div_normSq_of_grh_quadratic hN2 hGRH hprimitive hne hinv hquad
  have hpt := norm_completedLogZeroTerm_eq hGRH hprimitive hne hquad hx
  have hsummableTerm :
    Summable
      (fun ρ : ℂ =>
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2‖) :=
    (hsummableInv.mul_left (Real.sqrt x)).congr (fun ρ => (hpt ρ).symm)
  calc
    ∑ ρ ∈ S,
          ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
                (x : ℂ) ^ ρ /
              ρ ^ 2‖ ≤
        ∑' ρ : ℂ,
          ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
                (x : ℂ) ^ ρ /
              ρ ^ 2‖ :=
      hsummableTerm.sum_le_tsum S (fun _ _ => norm_nonneg _)
    _ =
        ∑' ρ : ℂ,
          Real.sqrt x *
            (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                ℝ) /
              Complex.normSq ρ) :=
      tsum_congr hpt
    _ =
        Real.sqrt x *
          ∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ :=
      tsum_mul_left
    _ = 2 * Real.sqrt x * |primitiveBRe χ| := by
      rw [tsum_divisor_inv_normSq_eq_two_mul_abs_BRe hN2 hGRH hprimitive hne hinv hquad]
      ring

/--
Input/assumptions: GRH, a primitive complex Dirichlet character with `χ ≠ 1` and `χ⁻¹ ≠ 1` (no
quadratic hypothesis), and a positive real `x`.
Conclusion: `‖D_ρ x^ρ/ρ²‖ = (D_ρ/normSq ρ) · √x`, where `D_ρ` is the completed-`L` divisor at `ρ`.
Content: identical to `norm_completedLogZeroTerm_eq` but with the zero classification supplied by
the `hquad`-free `DirichletLFunction.completedLFunction_zero_re_eq_half_of_grh`.
Role: the generic application route, the `hquad`-free log-kernel analogue of
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_completedReciprocalZeroTerm_eq_of_grh`.
-/
theorem norm_completedLogZeroTerm_eq_of_grh {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
            (x : ℂ) ^ ρ /
          ρ ^ 2‖ =
      Real.sqrt x *
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ) := by
  set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
  by_cases hD0 : D = 0
  · simp only [hD0, Int.cast_zero, zero_mul, zero_div, norm_zero, mul_zero]
  · have hDnonneg : (0 : ℝ) ≤ (D : ℝ) := by
      have hdiff := DirichletCharacter.differentiable_completedLFunction hne
      have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
        fun z _ => hdiff.analyticAt z
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic ρ
    have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_grh hGRH hprimitive hne hinv hzero
    have hnormsq : ‖ρ ^ 2‖ = Complex.normSq ρ := by rw [norm_pow, ← Complex.normSq_eq_norm_sq]
    have hnormpow : ‖(x : ℂ) ^ ρ‖ = Real.sqrt x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre_half, ← Real.sqrt_eq_rpow]
    rw [norm_div, norm_mul, Complex.norm_intCast, abs_of_nonneg hDnonneg, hnormpow, hnormsq]
    ring

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis), `x > 0`, and an arbitrary `Finset ℂ`.
Conclusion: `∑ ρ ∈ S, ‖D_ρ x^ρ/ρ²‖ ≤ 2√x Z_χ`, where `Z_χ` is the real zero mass
`Σ' ρ, m_ρ(χ) Re(1/ρ)` of `χ` itself.
Content: identical to `sum_norm_completedLogZeroTerm_le` but built on the `hquad`-free
`DirichletLFunction.summable_divisor_div_normSq_of_grh`, `norm_completedLogZeroTerm_eq_of_grh`, and
`DirichletLFunction.tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh` instead, with `Z_χ` as the
witness.
Role: the generic application route, the `hquad`-free log-kernel analogue of
`sum_norm_completedReciprocalZeroTerm_le_of_grh`, uniform in `S`; the finite-`Finset` companion
to the whole-line `tsum` bound (`DirichletLFunction.norm_tsum_logZeroContribution_le_of_grh`),
needed since the
whole-line bound alone cannot dominate an arbitrary finite subset sum.
-/
theorem sum_norm_completedLogZeroTerm_le_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x)
    (S : Finset ℂ) :
    ∑ ρ ∈ S,
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2‖ ≤
      2 * Real.sqrt x *
        (∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re) := by
  have hsummableInv := summable_divisor_div_normSq_of_grh hN2 hGRH hprimitive hne hinv
  have hpt := norm_completedLogZeroTerm_eq_of_grh hGRH hprimitive hne hinv hx
  have hsummableTerm :
    Summable
      (fun ρ : ℂ =>
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2‖) :=
    (hsummableInv.mul_left (Real.sqrt x)).congr (fun ρ => (hpt ρ).symm)
  calc
    ∑ ρ ∈ S,
          ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
                (x : ℂ) ^ ρ /
              ρ ^ 2‖ ≤
        ∑' ρ : ℂ,
          ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
                (x : ℂ) ^ ρ /
              ρ ^ 2‖ :=
      hsummableTerm.sum_le_tsum S (fun _ _ => norm_nonneg _)
    _ =
        ∑' ρ : ℂ,
          Real.sqrt x *
            (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                ℝ) /
              Complex.normSq ρ) :=
      tsum_congr hpt
    _ =
        Real.sqrt x *
          ∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ :=
      tsum_mul_left
    _ =
        2 * Real.sqrt x *
          (∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
              (1 / ρ).re) :=
      by
      rw [tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh hN2 hGRH hprimitive hne hinv]
      ring

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis), `x > 0`, and an arbitrary `Finset ℂ`.
Conclusion: `∑ ρ ∈ S, ‖D_ρ x^ρ/ρ²‖ ≤ 2√x |DirichletLFunction.primitiveBRe χ|`.
Content: `sum_norm_completedLogZeroTerm_le_of_grh` rewritten via
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass_of_grh` from the `Z_χ` witness to the
`|DirichletLFunction.primitiveBRe χ|` witness,
matching the quadratic route's `sum_norm_completedLogZeroTerm_le` verbatim.
Role: the finite-subset logarithmic bound in terms of the shared Hadamard constant.
-/
theorem sum_norm_completedLogZeroTerm_le_abs_BRe_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x)
    (S : Finset ℂ) :
    ∑ ρ ∈ S,
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2‖ ≤
      2 * Real.sqrt x * |primitiveBRe χ| := by
  rw [abs_primitiveBRe_eq_zeroMass_of_grh hN2 hGRH hprimitive hne hinv]
  exact sum_norm_completedLogZeroTerm_le_of_grh hN2 hGRH hprimitive hne hinv hx S

/--
Input/assumptions: `N ≥ 1`, `χ ≠ 1`, `x > 0`, and `ρ ≠ 0`; no GRH,
primitivity, or quadraticity is required.
Conclusion: `(dirichletLFunctionLogZeroContribution x χ ρ).re ≤ ‖D_ρ x^ρ/ρ²‖`.
Content: case split on `gammaFactor χ ρ`. Nonzero: the multiplicity bridge
(`dirichletLFunctionZeroMultiplicity_eq_divisor_completedLFunction_of_gamma_ne_zero`)
identifies
the contribution with `-D_ρ x^ρ/ρ²` exactly, and `Complex.re_le_norm` bounds its real part by its
norm. Zero: `dirichletLFunctionLogZeroContribution_re_nonpos_of_gammaFactor_zero` gives `≤ 0 ≤ ‖·‖`.
Role: the pointwise bound letting a full erased zero ledger be dominated by the completed-zero
term, without splitting the ledger by gamma-factor vanishing.
-/
theorem dirichletLFunctionLogZeroContribution_re_le_completedTerm_norm {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ0 : ρ ≠ 0) :
    (dirichletLFunctionLogZeroContribution x χ ρ).re ≤
      ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
            (x : ℂ) ^ ρ /
          ρ ^ 2‖ := by
  by_cases hΓ : DirichletCharacter.gammaFactor χ ρ = 0
  · exact
      (dirichletLFunctionLogZeroContribution_re_nonpos_of_gammaFactor_zero hx hρ0 hΓ).trans
        (norm_nonneg _)
  · have hmult :=
      dirichletLFunctionZeroMultiplicity_eq_divisor_completedLFunction_of_gamma_ne_zero hne hΓ
    have hmultC :
      ((dirichletLFunctionZeroMultiplicity χ ρ : ℕ) : ℂ) =
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) := by
      exact_mod_cast hmult
    have heq :
      dirichletLFunctionLogZeroContribution x χ ρ =
        -(((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2) := by
      unfold dirichletLFunctionLogZeroContribution
      rw [hmultC]
      ring
    rw [heq, ← norm_neg]
    exact Complex.re_le_norm _

/--
Input/assumptions: `N ≥ 1`, `χ`, `x > 0`, `ρ ≠ 0` with `gammaFactor χ ρ = 0`.
Conclusion: `(dirichletLFunctionReciprocalZeroContribution x χ ρ).re ≤ 0`.
Content: parity dispatch on `Complex.Gammaℝ_eq_zero_iff` shows `ρ` is a genuine negative real
number (`ρ = -2m` even, `m ≠ 0` from `ρ ≠ 0`; `ρ = -2m - 1` odd, always `< 0`); on such `ρ`,
`x ^ (ρ - 1)` is a positive real (`Complex.ofReal_cpow`) and `ρ (ρ - 1)` a positive real (product
of two negatives), so `-mult · x^(ρ-1) / (ρ(ρ-1))` is a real number `≤ 0`.
Role: the reciprocal-kernel trivial-zero sign bound — no exact multiplicity/order classification is
needed at gamma-factor poles, only this sign fact.
-/
theorem dirichletLFunctionReciprocalZeroContribution_re_nonpos_of_gammaFactor_zero {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hΓ : DirichletCharacter.gammaFactor χ ρ = 0) :
    (dirichletLFunctionReciprocalZeroContribution x χ ρ).re ≤ 0 := by
  have hreim : ρ.im = 0 ∧ ρ.re < 0 := by
    rcases χ.even_or_odd with heven | hodd
    · rw [heven.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hΓ
      obtain ⟨m, hm⟩ := hΓ
      have hm0 : m ≠ 0 := by
        rintro rfl
        apply hρ0
        rw [hm]
        simp only [CharP.cast_eq_zero, mul_zero, neg_zero]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
      have hρre : ρ = ((-(2 * (m : ℝ)) : ℝ) : ℂ) := by
        rw [hm]
        push_cast
        ring
      rw [hρre, Complex.ofReal_im, Complex.ofReal_re]
      exact ⟨rfl, by linarith⟩
    · rw [hodd.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hΓ
      obtain ⟨m, hm⟩ := hΓ
      have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hρre : ρ = ((-(2 * (m : ℝ)) - 1 : ℝ) : ℂ) := by
        have : ρ = -(2 * (m : ℂ)) - 1 := by linear_combination hm
        rw [this]
        push_cast
        ring
      rw [hρre, Complex.ofReal_im, Complex.ofReal_re]
      exact ⟨rfl, by linarith⟩
  obtain ⟨him, hre⟩ := hreim
  have hρeq_real : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [him, Complex.ofReal_im]
  set σ : ℝ := ρ.re with hσ_def
  have hxpow : (x : ℂ) ^ (ρ - 1) = ((x ^ (σ - 1) : ℝ) : ℂ) := by
    conv_lhs => rw [hρeq_real]
    rw [show ((σ : ℝ) : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) from by
        push_cast
        ring,
      Complex.ofReal_cpow hx.le]
  have hxpow_pos : (0 : ℝ) < x ^ (σ - 1) := Real.rpow_pos_of_pos hx _
  have hdenom : ρ * (ρ - 1) = ((σ * (σ - 1) : ℝ) : ℂ) := by
    conv_lhs => rw [hρeq_real]
    push_cast; ring
  have hdenom_pos : (0 : ℝ) < σ * (σ - 1) := by nlinarith [hre]
  set m : ℕ := dirichletLFunctionZeroMultiplicity χ ρ with hm_def
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  unfold dirichletLFunctionReciprocalZeroContribution
  rw [← hm_def, hxpow, hdenom,
    show
      -(m : ℂ) * ((x ^ (σ - 1) : ℝ) : ℂ) / ((σ * (σ - 1) : ℝ) : ℂ) =
        ((-(m : ℝ) * x ^ (σ - 1) / (σ * (σ - 1)) : ℝ) : ℂ)
      from by
      push_cast; ring,
    Complex.ofReal_re]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [mul_nonneg hmnn hxpow_pos.le]
  · exact hdenom_pos.le

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive nontrivial quadratic complex Dirichlet character,
`x > 0`, and an arbitrary `Finset ℂ`.
Conclusion: `∑ ρ ∈ S, ‖D_ρ x^{ρ-1}/(ρ(ρ-1))‖ ≤ 2|Re B(χ)|/√x`.
Content: `Finset.sum_le_tsum` (the term is pointwise nonnegative) plus the same calc chain as
`norm_tsum_reciprocalZeroContribution_le` (`DirichletLFunction.norm_completedReciprocalZeroTerm_eq`,
`tsum_div_const`, `DirichletLFunction.tsum_divisor_inv_normSq_eq_two_mul_abs_BRe`) — the finite-sum
bound follows the
whole-line `tsum` bound without needing the norm-of-tsum triangle inequality at all.
Role: a finite completed-zero subset bound, uniform in the choice of `S`.
-/
theorem sum_norm_completedReciprocalZeroTerm_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) (S : Finset ℂ) :
    ∑ ρ ∈ S,
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ (ρ - 1) /
            (ρ * (ρ - 1))‖ ≤
      2 * |primitiveBRe χ| / Real.sqrt x := by
  have hsummableInv :=
    summable_divisor_div_normSq_of_grh_quadratic hN2 hGRH hprimitive hne hinv hquad
  have hpt := norm_completedReciprocalZeroTerm_eq hGRH hprimitive hne hquad hx
  have hsummableTerm :
    Summable
      (fun ρ : ℂ =>
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ (ρ - 1) /
            (ρ * (ρ - 1))‖) :=
    (hsummableInv.div_const (Real.sqrt x)).congr (fun ρ => (hpt ρ).symm)
  calc
    ∑ ρ ∈ S,
          ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
                (x : ℂ) ^ (ρ - 1) /
              (ρ * (ρ - 1))‖ ≤
        ∑' ρ : ℂ,
          ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
                (x : ℂ) ^ (ρ - 1) /
              (ρ * (ρ - 1))‖ :=
      hsummableTerm.sum_le_tsum S (fun _ _ => norm_nonneg _)
    _ =
        ∑' ρ : ℂ,
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ) /
            Real.sqrt x :=
      tsum_congr hpt
    _ =
        (∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ) /
          Real.sqrt x :=
      tsum_div_const
    _ = 2 * |primitiveBRe χ| / Real.sqrt x := by
      rw [tsum_divisor_inv_normSq_eq_two_mul_abs_BRe hN2 hGRH hprimitive hne hinv hquad]

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis), `x > 0`, and an arbitrary `Finset ℂ`.
Conclusion: `∑ ρ ∈ S, ‖D_ρ x^{ρ-1}/(ρ(ρ-1))‖ ≤ 2 Z_χ / √x`, where `Z_χ` is the real zero mass
`Σ' ρ, m_ρ(χ) Re(1/ρ)` of `χ` itself.
Content: identical to `sum_norm_completedReciprocalZeroTerm_le` but built on the `hquad`-free
`DirichletLFunction.summable_divisor_div_normSq_of_grh`,
`DirichletLFunction.norm_completedReciprocalZeroTerm_eq_of_grh`, and
`DirichletLFunction.tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh` instead, with `Z_χ` as the
witness.
Role: the generic application route, the `hquad`-free finite-`Finset` companion to the whole-line
`tsum` bound
(`DirichletLFunction.norm_tsum_reciprocalZeroContribution_le_of_grh`).
-/
theorem sum_norm_completedReciprocalZeroTerm_le_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x)
    (S : Finset ℂ) :
    ∑ ρ ∈ S,
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ (ρ - 1) /
            (ρ * (ρ - 1))‖ ≤
      2 *
          (∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
              (1 / ρ).re) /
        Real.sqrt x := by
  have hsummableInv := summable_divisor_div_normSq_of_grh hN2 hGRH hprimitive hne hinv
  have hpt := norm_completedReciprocalZeroTerm_eq_of_grh hGRH hprimitive hne hinv hx
  have hsummableTerm :
    Summable
      (fun ρ : ℂ =>
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ (ρ - 1) /
            (ρ * (ρ - 1))‖) :=
    (hsummableInv.div_const (Real.sqrt x)).congr (fun ρ => (hpt ρ).symm)
  calc
    ∑ ρ ∈ S,
          ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
                (x : ℂ) ^ (ρ - 1) /
              (ρ * (ρ - 1))‖ ≤
        ∑' ρ : ℂ,
          ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
                (x : ℂ) ^ (ρ - 1) /
              (ρ * (ρ - 1))‖ :=
      hsummableTerm.sum_le_tsum S (fun _ _ => norm_nonneg _)
    _ =
        ∑' ρ : ℂ,
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ) /
            Real.sqrt x :=
      tsum_congr hpt
    _ =
        (∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
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
      by rw [tsum_divisor_inv_normSq_eq_two_mul_zeroMass_of_grh hN2 hGRH hprimitive hne hinv]

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive complex Dirichlet character with `χ ≠ 1` and
`χ⁻¹ ≠ 1` (no quadratic hypothesis), `x > 0`, and an arbitrary `Finset ℂ`.
Conclusion: `∑ ρ ∈ S, ‖D_ρ x^{ρ-1}/(ρ(ρ-1))‖ ≤ 2 |DirichletLFunction.primitiveBRe χ| / √x`.
Content: `sum_norm_completedReciprocalZeroTerm_le_of_grh` rewritten via
`DirichletLFunction.abs_primitiveBRe_eq_zeroMass_of_grh` from the `Z_χ` witness to the
`|DirichletLFunction.primitiveBRe χ|` witness,
matching the quadratic route's `sum_norm_completedReciprocalZeroTerm_le` verbatim.
Role: the finite-subset reciprocal bound in terms of the shared Hadamard constant.
-/
theorem sum_norm_completedReciprocalZeroTerm_le_abs_BRe_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x)
    (S : Finset ℂ) :
    ∑ ρ ∈ S,
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ (ρ - 1) /
            (ρ * (ρ - 1))‖ ≤
      2 * |primitiveBRe χ| / Real.sqrt x := by
  rw [abs_primitiveBRe_eq_zeroMass_of_grh hN2 hGRH hprimitive hne hinv]
  exact sum_norm_completedReciprocalZeroTerm_le_of_grh hN2 hGRH hprimitive hne hinv hx S

/--
Input/assumptions: `N ≥ 1`, `χ ≠ 1`, `x > 0`, and `ρ ≠ 0`; no GRH,
primitivity, or quadraticity is required.
Conclusion: `(dirichletLFunctionReciprocalZeroContribution x χ ρ).re ≤ ‖D_ρ x^{ρ-1}/(ρ(ρ-1))‖`.
Content: case split on `gammaFactor χ ρ`. Nonzero: the multiplicity bridge identifies the
contribution with `-D_ρ x^{ρ-1}/(ρ(ρ-1))` exactly, and `Complex.re_le_norm` bounds its real part by
its norm (`= ‖D_ρ x^{ρ-1}/(ρ(ρ-1))‖` via `norm_neg`). Zero:
`dirichletLFunctionReciprocalZeroContribution_re_nonpos_of_gammaFactor_zero` gives `≤ 0 ≤ ‖·‖`.
Role: the pointwise bound letting a whole erased ledger (both ordinary and trivial zeros together)
be dominated by the completed-zero term, without ever splitting `S` by gamma-factor vanishing.
-/
theorem dirichletLFunctionReciprocalZeroContribution_re_le_completedTerm_norm {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ0 : ρ ≠ 0) :
    (dirichletLFunctionReciprocalZeroContribution x χ ρ).re ≤
      ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
            (x : ℂ) ^ (ρ - 1) /
          (ρ * (ρ - 1))‖ := by
  by_cases hΓ : DirichletCharacter.gammaFactor χ ρ = 0
  · exact
      (dirichletLFunctionReciprocalZeroContribution_re_nonpos_of_gammaFactor_zero hx hρ0 hΓ).trans
        (norm_nonneg _)
  · have hmult :=
      dirichletLFunctionZeroMultiplicity_eq_divisor_completedLFunction_of_gamma_ne_zero hne hΓ
    have hmultC :
      ((dirichletLFunctionZeroMultiplicity χ ρ : ℕ) : ℂ) =
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) := by
      exact_mod_cast hmult
    have heq :
      dirichletLFunctionReciprocalZeroContribution x χ ρ =
        -(((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ (ρ - 1) /
            (ρ * (ρ - 1))) := by
      unfold dirichletLFunctionReciprocalZeroContribution
      rw [hmultC]
      ring
    rw [heq, ← norm_neg]
    exact Complex.re_le_norm _

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
