/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangularGamma

/-! # Interior triangular character averages -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, bound the positive, reciprocal and scale-one arithmetic sums
for a primitive nonprincipal character inside the triangular support. Combine
the signed dual formula, the interior Gamma bound and the scale-one zero-mass
estimate. This is the characterwise input to the middle-range comparison. -/
theorem quarter_triangular_interior {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x)
    (hbound : Real.log x ≤ 2 * a) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    (∑' n : ℕ, K.summand χ x n).re + (∑' n : ℕ, K.summand χ⁻¹ x⁻¹ n).re +
        2 * (∑' n : ℕ, K.summand χ 1 n).re ≤
      (4 * a - Real.log x) * Real.log q - 6 * a + (3 / 2 : ℝ) * Real.log x + 18 := by
  let K := LLS.PaperStatements.triangularMellinKernel ha
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have h := LLS.PaperStatements.triangular_dual_signed_central ha hq hGRH hp hne hinv hx
  have hpG :=
    LLS.PaperStatements.triangular_central_gamma_exp_re_le_profile χ ha hl hbound 1 (Or.inl rfl)
  have hmG :=
    LLS.PaperStatements.triangular_central_gamma_exp_re_le_profile χ⁻¹ ha hl hbound (-1)
      (Or.inr rfl)
  simp only [one_mul, neg_one_mul, Real.exp_log (zero_lt_one.trans_le hx), Real.exp_neg] at hpG hmG
  have hm := quarter_triangular_mass_one_bound ha hq hGRH hp hne hinv
  obtain ⟨θ, hθ, he⟩ := K.exists_theta_zero_sum hq hGRH hp hne hinv (zero_lt_one.trans_le hx)
  have hmass : 0 ≤ ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ := tsum_nonneg (fun _ ↦ norm_nonneg _)
  have ht : -1 ≤ θ := (abs_le.mp hθ).1
  have hn := mul_nonneg (show 0 ≤ θ + 1 by linarith only [ht]) hmass
  have hprof : LLS.PaperStatements.triangularKernelProfile a x = 2 * a - Real.log x := by
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [abs_of_nonneg hl, max_eq_right (sub_nonneg.mpr hbound)]
  dsimp only at h hm hpG hmG ⊢
  rw [hprof] at h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re] at hre
  have hc :
    (Complex.log (q : ℂ) * ((2 * a - Real.log x : ℝ) : ℂ)).re =
      (2 * a - Real.log x) * Real.log q := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.log_re, Complex.norm_natCast]
    ring
  rw [hc] at hre
  dsimp only [LLS.PaperStatements.triangularMellinKernel] at hre
  dsimp only [K] at he hn
  dsimp only [LLS.PaperStatements.triangularMellinKernel] at hm he hn ⊢
  nlinarith only [hre, hpG, hmG, hm, he, hn]

/-- Sum the interior triangular comparison over a finite primitive character
family under GRH. The conductor logarithms are retained for the subgroup
annihilator bound used in the large-index argument. -/
theorem quarter_interior_family (ha : 0 < a) {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (χ : ∀ i, DirichletCharacter ℂ (q i))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : ∀ i ∈ s, 2 ≤ q i)
    (hp : ∀ i ∈ s, (χ i).IsPrimitive) (hne : ∀ i ∈ s, χ i ≠ 1) (hinv : ∀ i ∈ s, (χ i)⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) (hbound : Real.log x ≤ 2 * a) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    (∑ i ∈ s, (∑' n : ℕ, K.summand (χ i) x n).re) +
        (∑ i ∈ s, (∑' n : ℕ, K.summand (χ i)⁻¹ x⁻¹ n).re) +
        2 * (∑ i ∈ s, (∑' n : ℕ, K.summand (χ i) 1 n).re) ≤
      (4 * a - Real.log x) * (∑ i ∈ s, Real.log (q i)) +
        (-6 * a + (3 / 2 : ℝ) * Real.log x + 18) * s.card := by
  have hs :=
    Finset.sum_le_sum (s := s)
      (fun i hi ↦
        quarter_triangular_interior ha (hq i hi) hGRH (hp i hi) (hne i hi) (hinv i hi) hx hbound)
  dsimp only at hs ⊢
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at hs
  linarith only [hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
