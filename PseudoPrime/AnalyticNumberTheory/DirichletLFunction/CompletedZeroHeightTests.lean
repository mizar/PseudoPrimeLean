/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedZeroEquidistribution
public import PseudoPrime.Analysis.CayleyTest

/-!
# Uniform completed-zero sums for compact height tests

Convert continuous circle tests into actual completed-zero height sums.
Cayley transport identifies their limiting coefficient with the real-line integral.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive character with nonprincipal inverse under individual RH, the
shift 3/2-rho of a completed zero equals 1-i*Im(rho). Use its critical-line real
part and compare coordinates. This matches the real-height Cayley parametrization. -/
theorem completedZeroShift_eq_one_sub_I_im {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    (ρ : CompletedZero χ) : (((3 / 2 : ℝ) : ℂ) - (ρ : ℂ)) = 1 - Complex.I * (ρ : ℂ).im := by
  apply Complex.ext
  · rw [Complex.sub_re, Complex.ofReal_re,
      completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv ρ.property]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    norm_num only
  · simp only [Complex.sub_im, Complex.ofReal_im, Complex.one_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]

/-- Under the completed-zero RH hypotheses, its Cayley circle point is the real-height
Cayley point at Im(rho). Substitute the shifted-zero coordinate identity.
This transfers compact height tests to the existing circle functional. -/
theorem completedZeroCayleyPoint_eq_cayleyCircle {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    (ρ : CompletedZero χ) :
    completedZeroCayleyPoint hRH hp hinv ρ = PseudoPrime.Analysis.cayleyCircle (ρ : ℂ).im := by
  apply Subtype.ext
  change ((((3 / 2 : ℝ) : ℂ) - (ρ : ℂ) - 2) / (((3 / 2 : ℝ) : ℂ) - (ρ : ℂ))) = _
  rw [PseudoPrime.Analysis.coe_cayleyCircle, completedZeroShift_eq_one_sub_I_im hRH hp hinv ρ]

/-- Under the completed-zero RH hypotheses, the Poisson weight is its natural
multiplicity divided by 1+Im(rho)^2. Compute the shifted norm square.
This cancels the quadratic factor in the circle extension of a height test. -/
theorem completedZeroPoissonWeight_eq_order_div_one_add_im_sq {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) (ρ : CompletedZero χ) :
    completedZeroPoissonWeight χ ρ =
      (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2) := by
  rw [completedZeroPoissonWeight, completedZeroShift_eq_one_sub_I_im hRH hp hinv ρ]
  congr 1
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero, zero_add]
  ring

/-- For primitive nonprincipal RH data, a circle test pulling back to (1+t^2)*g(t)
has completed-zero functional equal to the multiplicity-weighted height sum.
Rewrite each Cayley point and cancel the positive denominator. This identifies
the arithmetic zero series evaluated by the circle convergence theorem. -/
theorem completedZeroFunctional_eq_height_test {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (g : ℝ → ℂ) (f : C(Circle, ℂ))
    (hf : ∀ t, f (PseudoPrime.Analysis.cayleyCircle t) = ((1 + t ^ 2 : ℝ) : ℂ) * g t) :
    completedZeroFunctional hq hRH hp hne hinv f =
      ∑' ρ : CompletedZero χ,
        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) * g (ρ : ℂ).im := by
  rw [completedZeroFunctional_apply]
  apply tsum_congr
  intro ρ
  rw [completedZeroCayleyPoint_eq_cayleyCircle hRH hp hinv ρ, hf,
    completedZeroPoissonWeight_eq_order_div_one_add_im_sq hRH hp hinv ρ, Complex.ofReal_div,
    Complex.ofReal_natCast]
  rw [← mul_assoc,
    div_mul_cancel₀ _
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _))))]

/-- For primitive nonprincipal RH data at modulus at least two, every continuous
compactly supported complex height test gives an absolutely convergent weighted
completed-zero series. Extend to the circle and cancel the Poisson denominator.
This justifies real-part projection and comparison of compact kernel zero sums. -/
theorem summable_completedZero_height_test {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (g : ℝ → ℂ) (hg : Continuous g) (hc : HasCompactSupport g) :
    Summable
      (fun ρ : CompletedZero χ ↦
        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) * g (ρ : ℂ).im) := by
  obtain ⟨f, hf, _⟩ := PseudoPrime.Analysis.exists_circle_weighted_extension g hg hc
  have hs :=
    PseudoPrime.Analysis.summable_weightedEval (completedZeroCayleyPoint hRH hp hinv)
      (completedZeroPoissonWeight χ) (completedZeroPoissonWeight_nonneg χ)
      (summable_completedZeroPoissonWeight hq hRH hp hne hinv) f
  apply hs.congr
  intro ρ
  rw [completedZeroCayleyPoint_eq_cayleyCircle hRH hp hinv ρ, hf,
    completedZeroPoissonWeight_eq_order_div_one_add_im_sq hRH hp hinv ρ, Complex.ofReal_div,
    Complex.ofReal_natCast]
  rw [← mul_assoc,
    div_mul_cancel₀ _
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _))))]

/-- For a fixed continuous compact height test and any positive error, sufficiently
large moduli make its weighted completed-zero sum differ from log(q)/(2*pi)
times its integral by at most error*log(q), uniformly in primitive nonprincipal
characters satisfying individual RH. Transport through Cayley circle convergence
and remove the logarithmic normalization. This is the compact-height input for
kernel mass estimates, without a source explicit formula as an additional premise. -/
theorem exists_uniform_completedZero_height_test_error_le (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ‖(∑' ρ : CompletedZero χ,
                        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) * g (ρ : ℂ).im) -
                      ((Real.log q / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, g t)‖ ≤
                  ε * Real.log q := by
  obtain ⟨f, hf, ha⟩ := PseudoPrime.Analysis.exists_circle_weighted_extension g hg hc
  obtain ⟨Q, hQ, hb⟩ := exists_uniform_normalizedCompletedZeroFunctional_error_le f hε
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  have hq2 : (2 : ℝ) ≤ q := Nat.cast_le.mpr (hQ.trans hq)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith only [hq2])
  have hh := hb q hq χ hRH hp hne hinv
  rw [normalizedCompletedZeroFunctional, smul_apply, smul_eq_mul,
    completedZeroFunctional_eq_height_test (hQ.trans hq) hRH hp hne hinv g f hf, ha,
    Complex.real_smul] at hh
  have hm := mul_le_mul_of_nonneg_left hh hlog.le
  have heq :
    (Real.log q : ℂ) *
        ((1 / (Real.log q : ℂ)) *
            (∑' ρ : CompletedZero χ,
              (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) * g (ρ : ℂ).im) -
          (1 / 2 : ℂ) * (((1 / Real.pi : ℝ) : ℂ) * (∫ t : ℝ, g t))) =
      (∑' ρ : CompletedZero χ,
          (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) * g (ρ : ℂ).im) -
        ((Real.log q / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, g t) := by
    rw [mul_sub, ← mul_assoc, mul_one_div_cancel (Complex.ofReal_ne_zero.mpr hlog.ne'), one_mul]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
    congr 1
    ring
  have hn :=
    norm_mul (Real.log q : ℂ)
      ((1 / (Real.log q : ℂ)) *
          (∑' ρ : CompletedZero χ,
            (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) * g (ρ : ℂ).im) -
        (1 / 2 : ℂ) * (((1 / Real.pi : ℝ) : ℂ) * (∫ t : ℝ, g t)))
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog] at hn
  rw [← hn] at hm
  simpa only [mul_comm] using hm

/-- For any continuous compactly supported real height test and positive error,
its multiplicity-weighted completed-zero sum is eventually bounded by the
integral divided by 2*pi plus that error, times log(q), uniformly under the
primitive nonprincipal individual-RH hypotheses. Cast to the complex estimate
and take its real upper side. This permits nonnegative kernel majorant tests. -/
theorem exists_uniform_completedZero_real_height_test_upper_bound (g : ℝ → ℝ) (hg : Continuous g)
    (hc : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                (∑' ρ : CompletedZero χ,
                    (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) * g (ρ : ℂ).im) ≤
                  ((∫ t : ℝ, g t) / (2 * Real.pi) + ε) * Real.log q := by
  have hcc : HasCompactSupport (fun t ↦ (g t : ℂ)) := hc.comp_left Complex.ofReal_zero
  obtain ⟨Q, hQ, hb⟩ :=
    exists_uniform_completedZero_height_test_error_le (fun t ↦ (g t : ℂ))
      (Complex.continuous_ofReal.comp hg) hcc hε
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  have hh := hb q hq χ hRH hp hne hinv
  have hi : (∫ t : ℝ, (g t : ℂ)) = ((∫ t : ℝ, g t) : ℝ) :=
    Complex.ofRealCLM.integral_comp_comm (hg.integrable_of_hasCompactSupport hc)
  have hs :
    (∑' ρ : CompletedZero χ,
        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) * (g (ρ : ℂ).im : ℂ)) =
      ((∑' ρ : CompletedZero χ,
          (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) * g (ρ : ℂ).im) :
        ℝ) := by
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_tsum]
  rw [hs, hi, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hh
  calc
    _ ≤ Real.log q / (2 * Real.pi) * (∫ t : ℝ, g t) + ε * Real.log q := by
      linarith only [(abs_le.mp hh).2]
    _ = _ := by ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
