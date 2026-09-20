/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import PseudoPrime.Analysis.IntegralLimits

/-!
# Basic facts about completed Dirichlet `L`-functions

Fully generic facts about `DirichletCharacter.completedLFunction`/`DirichletCharacter.LFunction`
for an arbitrary Dirichlet character: the functional equation, Gauss-sum and root-number
nonvanishing for primitive characters, the completed/uncompleted comparison via the gamma factor,
gamma-factor values at zero by parity, standard nonvanishing at `1`, zero reflection between a
character and its inverse, and the Euler-product/log-derivative bridge to the twisted von
Mangoldt Dirichlet series. None of this mentions any application-specific contour kernel.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: a primitive complex Dirichlet character.
Conclusion: its completed `L`-function satisfies mathlib's functional equation at every point.
Content: retain the exact root-number and conductor normalization supplied by mathlib.
Role: this is the symmetry input for a primitive completed-`L` zero ledger; no project-local
completed-function convention is introduced.
-/
theorem dirichletCompletedLFunction_one_sub_of_isPrimitive {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (s : ℂ) :
    DirichletCharacter.completedLFunction χ (1 - s) =
      N ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ s :=
  hχ.completedLFunction_one_sub s

/--
Input/assumptions: a primitive complex Dirichlet character.
Conclusion: its standard additive Gauss sum is nonzero.
Content: Fourier inversion makes the discrete Fourier transform injective; the primitive character
Fourier formula would make that transform zero if its Gauss sum vanished, contradicting `χ(1)=1`.
Role: provides the missing composite-modulus Gauss-sum nonvanishing needed by the root number.
-/
theorem dirichletCharacter_gaussSum_ne_zero_of_isPrimitive {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : gaussSum χ ZMod.stdAddChar ≠ 0 := by
  intro hsum
  have hdft : ZMod.dft χ = 0 := by
    ext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum k, hsum, mul_zero]
    simp only [Pi.zero_apply]
  have hzero : (χ : ZMod N → ℂ) = 0 :=
    ZMod.dft.injective (by simpa only [map_zero, EmbeddingLike.map_eq_zero_iff] using hdft)
  have hone := congr_fun hzero 1
  simp only [map_one, Pi.zero_apply, one_ne_zero] at hone

/--
Input/assumptions: a primitive complex Dirichlet character.
Conclusion: its completed-functional-equation root number is nonzero.
Content: unfold the root number and combine Gauss-sum nonvanishing with nonzero Archimedean and
positive-modulus factors.
Role: enables reverse zero reflection and the odd-character analysis at the Mellin point zero.
-/
theorem dirichletCharacter_rootNumber_ne_zero_of_isPrimitive {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : DirichletCharacter.rootNumber χ ≠ 0 := by
  rw [DirichletCharacter.rootNumber]
  refine div_ne_zero (div_ne_zero (dirichletCharacter_gaussSum_ne_zero_of_isPrimitive hχ) ?_) ?_
  · exact pow_ne_zero _ Complex.I_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast NeZero.ne N))

/--
Input/assumptions: a primitive character and a completed zero at a reflected point.
Conclusion: the corresponding point is a completed zero of the inverse character.
Content: cancel the nonzero modulus power and root number from the primitive functional equation.
Role: completes zero reflection between the two finite completed-`L` ledgers.
-/
theorem dirichletCompletedLFunction_inv_zero_of_one_sub_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (s : ℂ)
    (hzero : DirichletCharacter.completedLFunction χ (1 - s) = 0) :
    DirichletCharacter.completedLFunction χ⁻¹ s = 0 := by
  have hfunction := dirichletCompletedLFunction_one_sub_of_isPrimitive hχ s
  have hfactor : (N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ ≠ 0 :=
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast NeZero.ne N)))
      (dirichletCharacter_rootNumber_ne_zero_of_isPrimitive hχ)
  have hproduct :
    ((N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ) *
        DirichletCharacter.completedLFunction χ⁻¹ s =
      0 := by
    simpa only [mul_assoc, hzero, eq_self_iff_true] using hfunction.symm
  exact (mul_eq_zero.mp hproduct).resolve_left hfactor

/--
Input/assumptions: a complex Dirichlet character and a point away from the exceptional
trivial-modulus origin.
Conclusion: its usual `L`-function is the completed function divided by mathlib's gamma factor.
Content: this fixes the normalization comparison needed to pass between Euler-series and completed
contour formulations.
Role: later primitive explicit-formula lemmas should use this identity rather than redefining an
archimedean factor.
-/
theorem dirichletLFunction_eq_completed_div_gammaFactor {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 0 ∨ N ≠ 1) :
    DirichletCharacter.LFunction χ s =
      DirichletCharacter.completedLFunction χ s / DirichletCharacter.gammaFactor χ s :=
  DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s hs

/--
Input/assumptions: a nontrivial Dirichlet character.
Conclusion: its modulus is not one.
Content: modulo one every Dirichlet character is the trivial character.
Role: discharges the exceptional modulus-one branch in the completed-to-uncompleted `L` relation.
-/
theorem dirichletCharacter_level_ne_one_of_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) : N ≠ 1 :=
  hχ ∘ DirichletCharacter.level_one' _

/--
Input/assumptions: an even complex Dirichlet character.
Conclusion: its archimedean gamma factor vanishes at zero.
Content: reduce to `Gammaℝ 0`, one of the explicitly represented gamma zeros in mathlib.
Role: identifies the source of the forced even-character trivial zero in the primitive ledger.
-/
theorem even_gammaFactor_zero {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.Even) :
    DirichletCharacter.gammaFactor χ 0 = 0 := by
  rw [hχ.gammaFactor_def]
  exact Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by norm_num only⟩

/--
Input/assumptions: an odd complex Dirichlet character.
Conclusion: its archimedean gamma factor equals one at zero.
Content: odd parity shifts the factor to `Gammaℝ 1`.
Role: separates the odd case, where no gamma zero forces a zero of the uncompleted `L`-function.
-/
theorem odd_gammaFactor_zero {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) :
    DirichletCharacter.gammaFactor χ 0 = 1 := by
  rw [hχ.gammaFactor_def]
  simp only [zero_add, Complex.Gammaℝ_one]

/--
Input/assumptions: a nontrivial even Dirichlet character.
Conclusion: its continued uncompleted `L`-function vanishes at zero.
Content: at zero the completed-to-uncompleted relation divides by the vanishing even gamma factor.
Role: records the forced Mellin/`L` singularity collision that the completed primitive ledger must
regularize.
-/
theorem dirichletLFunction_zero_of_even {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (heven : χ.Even) : DirichletCharacter.LFunction χ 0 = 0 := by
  rw [dirichletLFunction_eq_completed_div_gammaFactor χ 0
      (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hχ)),
    even_gammaFactor_zero heven]
  simp only [div_zero]

/--
Input/assumptions: a nontrivial Dirichlet character.
Conclusion: its continued `L`-function does not vanish at one.
Content: this is mathlib's nonvanishing theorem on the closed Euler half-plane.
Role: eliminates `s = 1` from the primitive singularity ledger; only the zero-side Mellin point
needs completed-function bookkeeping.
-/
theorem dirichletLFunction_one_ne_zero_of_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) : DirichletCharacter.LFunction χ 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero hχ

/--
Input/assumptions: a nontrivial character.
Conclusion: its completed `L`-function is nonzero at one.
Content: a hypothetical completed zero makes the completed/uncompleted comparison contradict the
standard nonvanishing of `L(χ,1)`.
Role: supplies the reflected endpoint nonvanishing used to resolve the odd `s = 0` case.
-/
theorem dirichletCompletedLFunction_one_ne_zero_of_ne_one {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : DirichletCharacter.completedLFunction χ 1 ≠ 0 := by
  intro hcompleted
  have hL := dirichletLFunction_one_ne_zero_of_ne_one hχ
  rw [dirichletLFunction_eq_completed_div_gammaFactor χ 1 (Or.inl (by norm_num only)),
    hcompleted] at hL
  simp only [zero_div, ne_eq, not_true_eq_false] at hL

/--
Input/assumptions: a nontrivial primitive character.
Conclusion: its completed `L`-function is nonzero at zero.
Content: reverse zero reflection would move a zero at zero to a zero of the inverse character at
one, where Dirichlet `L` nonvanishing rules it out.
Role: establishes completed-function nonvanishing at the lower Mellin endpoint.
-/
theorem dirichletCompletedLFunction_zero_ne_zero_of_primitive {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    DirichletCharacter.completedLFunction χ 0 ≠ 0 := by
  intro hzero
  have hinvzero :=
    dirichletCompletedLFunction_inv_zero_of_one_sub_zero hχ (1 : ℂ)
      (by simpa only [sub_self] using hzero)
  have hinvne : χ⁻¹ ≠ 1 := by
    intro hinv
    apply hne
    rw [← inv_inv χ, hinv, inv_one]
  exact dirichletCompletedLFunction_one_ne_zero_of_ne_one hinvne (by simpa only using hinvzero)

/--
Input/assumptions: a nontrivial primitive odd character.
Conclusion: its uncompleted Dirichlet `L`-function is nonzero at zero.
Content: the odd gamma factor equals one, so the completed value and ordinary value at zero agree.
Role: removes the odd-character `s = 0` deferred branch from the primitive contour construction.
-/
theorem dirichletLFunction_zero_ne_zero_of_primitive_odd {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (hodd : χ.Odd) :
    DirichletCharacter.LFunction χ 0 ≠ 0 := by
  have hcompleted := dirichletCompletedLFunction_zero_ne_zero_of_primitive hχ hne
  have hcomparison :=
    dirichletLFunction_eq_completed_div_gammaFactor χ 0
      (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne))
  rw [odd_gammaFactor_zero hodd, div_one] at hcomparison
  intro hzero
  apply hcompleted
  rw [← hcomparison]
  exact hzero

/--
Input/assumptions: a complex Dirichlet character and a point in the half-plane `Re s > 1`.
Conclusion: the analytically continued Dirichlet `L`-function equals its Dirichlet series there.
Content: expose mathlib's continuation-to-series comparison for downstream use.
Role: this is the Euler-series end of the primitive explicit-formula bridge to weighted Mangoldt
sums.
-/
theorem dirichletLFunction_eq_LSeries_of_one_lt_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) : DirichletCharacter.LFunction χ s = LSeries (χ ·) s :=
  DirichletCharacter.LFunction_eq_LSeries χ hs

/--
Input/assumptions: a complex Dirichlet character and a point in `Re s > 1`.
Conclusion: the derivatives of the continued and Dirichlet-series `L`-functions agree.
Content: continuation equality holds on a neighborhood of the point, so its derivative agrees.
Role: together with the preceding equality this supplies the logarithmic-derivative comparison
needed before introducing the von Mangoldt Dirichlet series.
-/
theorem deriv_dirichletLFunction_eq_deriv_LSeries_of_one_lt_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    deriv (DirichletCharacter.LFunction χ) s = deriv (LSeries (χ ·)) s :=
  DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs

/--
Input/assumptions: a complex Dirichlet character and a point in the Euler half-plane `Re s > 1`.
Conclusion: the `L`-series of `χ · Λ` is the negative derivative-over-value of the continued
Dirichlet `L`-function.
Content: consume mathlib's twisted von Mangoldt Euler-product theorem and the continuation/series
comparisons.
Role: supplies the Euler-series identity used in weighted Mangoldt sum formulas.
-/
theorem lSeries_twist_vonMangoldt_eq_neg_logDeriv_dirichletLFunction_of_one_lt_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ ↦ χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  change
    LSeries ((fun n : ℕ ↦ χ (n : ZMod N)) * fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs, ←
    dirichletLFunction_eq_LSeries_of_one_lt_re χ hs, ←
    deriv_dirichletLFunction_eq_deriv_LSeries_of_one_lt_re χ hs]

/--
Input/assumptions: a character and a vertical line `Re s = τ > 1`.
Conclusion: the negative logarithmic derivative of its `L`-function is uniformly bounded by the
untwisted von Mangoldt Dirichlet series at the real point `τ`.
Content: expand `-L'/L` as the twisted von Mangoldt `L`-series; termwise, `‖χ n‖ ≤ 1` removes
the character and complex powers contribute exactly `n⁻ᵗ` to the norm.
-/
theorem norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {τ : ℝ} (hτ : 1 < τ) (y : ℝ) :
    ‖-deriv (DirichletCharacter.LFunction χ) ((τ : ℂ) + y * Complex.I) /
          DirichletCharacter.LFunction χ ((τ : ℂ) + y * Complex.I)‖ ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ := by
  set s : ℂ := (τ : ℂ) + y * Complex.I with hs_def
  let f : ℕ → ℂ := fun n ↦ χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)
  have hs : (1 : ℝ) < s.re := by
    rw [hs_def]
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hτ
  have hsre : s.re = τ := by
    rw [hs_def]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have heq := lSeries_twist_vonMangoldt_eq_neg_logDeriv_dirichletLFunction_of_one_lt_re χ hs
  have hsumm := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  rw [LSeriesSummable, ← summable_norm_iff] at hsumm
  have hterm : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, CharP.cast_eq_zero,
        zero_div, Std.le_refl, f]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      rw [LSeries.term_of_ne_zero hn0, norm_div,
        show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      have hΛ : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ = ArithmeticFunction.vonMangoldt n := by
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      change
        ‖χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)‖ / (n : ℝ) ^ s.re ≤
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ
      rw [norm_mul, hΛ, hsre]
      have hχ : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
      simpa only [mul_div_assoc] using
        (mul_le_of_le_one_left
          (div_nonneg (ArithmeticFunction.vonMangoldt_nonneg)
            (Real.rpow_nonneg (Nat.cast_nonneg n) _))
          hχ)
  have hsumm' : Summable (fun n ↦ ‖LSeries.term f s n‖) := by
    have hf :
      f = (fun n : ℕ ↦ χ (n : ZMod N)) * fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) := by
      funext n
      simp only [Pi.mul_apply, f]
    rw [hf]
    exact hsumm
  have hmajorTerm :
    ∀ n : ℕ,
      ‖LSeries.term (fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) (τ : ℂ) n‖ =
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, CharP.cast_eq_zero,
        zero_div]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      rw [LSeries.term_of_ne_zero hn0, norm_div,
        show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.ofReal_re]
  have hmajor : Summable (fun n ↦ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ) := by
    have h :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (τ : ℂ))
        (by simpa only [Complex.ofReal_re] using hτ)
    rw [LSeriesSummable, ← summable_norm_iff] at h
    simpa only [hmajorTerm] using h
  calc
    ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
        ‖LSeries f s‖ :=
      by simpa only [Complex.norm_div, norm_neg, f] using congrArg norm heq.symm
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := by
      rw [LSeries]
      exact norm_tsum_le_tsum_norm hsumm'
    _ ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ := hsumm'.tsum_le_tsum hterm hmajor

/-- `logDeriv F` is analytic (hence differentiable) at `0`, since `F` is entire and `F 0 ≠ 0`. -/
theorem analyticAt_logDeriv_completedLFunction_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) :
    AnalyticAt ℂ (logDeriv (DirichletCharacter.completedLFunction χ)) 0 := by
  rw [logDeriv]
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hF0ne := dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  exact (hdiff.analyticAt 0).deriv.div (hdiff.analyticAt 0) hF0ne

/-- For a primitive nontrivial character, analyticity gives differentiability of `logDeriv F`
at zero. This is used when differentiating local factors and finite Hadamard sums. -/
theorem differentiableAt_logDeriv_completedLFunction_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) :
    DifferentiableAt ℂ (logDeriv (DirichletCharacter.completedLFunction χ)) 0 :=
  (analyticAt_logDeriv_completedLFunction_zero hprimitive hne).differentiableAt

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
