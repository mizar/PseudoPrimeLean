/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangularSupport
public import PseudoPrime.LLS.PaperStatements.TriangularGammaInteriorBounds
public import PseudoPrime.LLS.PaperStatements.TriangularZeroMassFormula

/-! # Variable-width triangular Gamma bounds at the support endpoint -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For any positive triangular width, the sum of the real central Gamma
contributions of a character and its inverse at scale one is at most
`-3a + 9`. The general interior Gamma estimate supplies each term; this
bound is used with the scale-one arithmetic credit. -/
theorem quarter_triangular_gamma_one {a : ℝ} (ha : 0 < a) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    let G := fun (ψ : DirichletCharacter ℂ q) (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor (Complex.I * t + 1 / 2) *
            (Analysis.triangularMellinFunction a (Complex.I * t) * (y : ℂ) ^ (Complex.I * t)))
    (G χ 1).re + (G χ⁻¹ 1).re ≤ -3 * a + 9 := by
  have hp :=
    LLS.PaperStatements.triangular_central_gamma_exp_re_le_profile χ (a := a) (l := 0) ha
      (by norm_num only) (by linarith only [ha]) 1 (Or.inl rfl)
  have hm :=
    LLS.PaperStatements.triangular_central_gamma_exp_re_le_profile χ⁻¹ (a := a) (l := 0) ha
      (by norm_num only) (by linarith only [ha]) 1 (Or.inl rfl)
  simp only [mul_zero, Real.exp_zero, sub_zero] at hp hm
  dsimp only
  linarith only [hp, hm]

/-- At the positive and reciprocal endpoints of a triangular kernel, the
real central Gamma contributions of a character and its inverse sum to at
most nine. Both endpoint estimates follow from the general interior bound;
the result supplies the variable-width dual-scale comparison. -/
theorem quarter_triangular_gamma_boundary {a x : ℝ} (ha : 0 < a) (hx : 1 ≤ x)
    (hbound : Real.log x = 2 * a) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    let G := fun (ψ : DirichletCharacter ℂ q) (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor (Complex.I * t + 1 / 2) *
            (Analysis.triangularMellinFunction a (Complex.I * t) * (y : ℂ) ^ (Complex.I * t)))
    (G χ x).re + (G χ⁻¹ x⁻¹).re ≤ 9 := by
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hla : Real.log x ≤ 2 * a := hbound.le
  have hp :=
    LLS.PaperStatements.triangular_central_gamma_exp_re_le_profile χ ha hl hla 1 (Or.inl rfl)
  have hm :=
    LLS.PaperStatements.triangular_central_gamma_exp_re_le_profile χ⁻¹ ha hl hla (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul, Real.exp_log (zero_lt_one.trans_le hx), Real.exp_neg] at hp hm
  dsimp only
  linarith only [hp, hm, hbound]

/-- Under GRH, at the triangular support endpoint the real forward
arithmetic sum plus the real oscillating-zero sum is at most nine for a
primitive nonprincipal character. The boundary dual-scale identity and the
paired Gamma bound give the analytic input to the high-index comparison. -/
theorem quarter_triangular_dual_le_nine {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x)
    (hbound : Real.log x = 2 * a) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    (∑' n : ℕ, K.summand χ x n).re + (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ).re ≤ 9 := by
  have h := quarter_triangular_dual_boundary ha hq hGRH hp hne hinv hx hbound.ge
  have hg := quarter_triangular_gamma_boundary ha hx hbound χ
  dsimp only at h hg ⊢
  have hre := congrArg Complex.re h
  simp only [Complex.add_re] at hre
  dsimp only [LLS.PaperStatements.triangularMellinKernel] at hre ⊢
  linarith only [hre, hg]

/-- Under GRH, the real forward arithmetic sum at the triangular support
endpoint is at most nine plus the absolute triangular zero mass. The boundary
dual-scale comparison and the oscillating zero-sum norm bound give the
characterwise estimate for the high-index branch. -/
theorem quarter_triangular_arith_le_mass {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x)
    (hbound : Real.log x = 2 * a) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    (∑' n : ℕ, K.summand χ x n).re ≤ 9 + ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ := by
  let K := LLS.PaperStatements.triangularMellinKernel ha
  have h := quarter_triangular_dual_le_nine ha hq hGRH hp hne hinv hx hbound
  obtain ⟨θ, hθ, he⟩ := K.exists_theta_zero_sum hq hGRH hp hne hinv (zero_lt_one.trans_le hx)
  have hm : 0 ≤ ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ := tsum_nonneg (fun _ ↦ norm_nonneg _)
  have ht : -1 ≤ θ := (abs_le.mp hθ).1
  have hp0 := mul_nonneg (show 0 ≤ θ + 1 by linarith only [ht]) hm
  dsimp only at h ⊢
  linarith only [h, he, hp0]

/-- Under GRH, the absolute triangular zero mass plus twice the real
scale-one arithmetic sum is at most `2a log q - 3a + 9` for a primitive
nonprincipal character. The scale-one dual identity identifies the positive
zero mass, and the paired Gamma bound supplies the negative correction. -/
theorem quarter_triangular_mass_one_bound {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) + 2 * (∑' n : ℕ, K.summand χ 1 n).re ≤
      2 * a * Real.log q - 3 * a + 9 := by
  let K := LLS.PaperStatements.triangularMellinKernel ha
  have h :=
    LLS.PaperStatements.triangular_dual_signed_central ha hq hGRH hp hne hinv (x := 1) le_rfl
  have hg := quarter_triangular_gamma_one ha χ
  have hpos := LLS.PaperStatements.triangular_zeroSum_one_eq_absoluteMass ha hne
  have hinvr :=
    LLS.PaperStatements.MellinKernel.tsum_summand_inv_re_eq K χ (by norm_num only : (0 : ℝ) < 1)
  have hprof : LLS.PaperStatements.triangularKernelProfile a 1 = 2 * a := by
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [Real.log_one, abs_zero, sub_zero, max_eq_right (by linarith only [ha])]
  dsimp only at h hg ⊢
  rw [inv_one, hpos, hprof] at h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re] at hre
  have hc : (Complex.log (q : ℂ) * ((2 * a : ℝ) : ℂ)).re = 2 * a * Real.log q := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.log_re, Complex.norm_natCast]
    ring
  rw [hc] at hre
  dsimp only [K] at hinvr
  rw [hinvr] at hre
  dsimp only [LLS.PaperStatements.triangularMellinKernel] at hre ⊢
  linarith only [hre, hg]

/-- Under GRH, a primitive nonprincipal character satisfies the two-scale
arithmetic bound `Re S(x) + 2 Re S(1) ≤ 2a log q - 3a + 18` at the
triangular support endpoint. Combine the forward-scale estimate with the
scale-one mass bound so that the zero mass cancels. This is the characterwise
analytic inequality used before averaging the high-index branch. -/
theorem quarter_triangular_two_scale_bound {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x)
    (hbound : Real.log x = 2 * a) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    (∑' n : ℕ, K.summand χ x n).re + 2 * (∑' n : ℕ, K.summand χ 1 n).re ≤
      2 * a * Real.log q - 3 * a + 18 := by
  have hscale := quarter_triangular_arith_le_mass ha hq hGRH hp hne hinv hx hbound
  have hmass := quarter_triangular_mass_one_bound ha hq hGRH hp hne hinv
  dsimp only at hscale hmass ⊢
  linarith only [hscale, hmass]

/-- For a finite family of primitive nonprincipal characters, the sum of the
support-endpoint arithmetic terms plus twice the scale-one terms is bounded
by the sum of conductor logarithms and one Gamma allowance per character.
Summing the characterwise two-scale bound preserves individual conductors
for the subsequent annihilator comparison. -/
theorem quarter_triangular_family_bound {a : ℝ} (ha : 0 < a) {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (χ : ∀ i, DirichletCharacter ℂ (q i))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : ∀ i ∈ s, 2 ≤ q i)
    (hp : ∀ i ∈ s, (χ i).IsPrimitive) (hne : ∀ i ∈ s, χ i ≠ 1) (hinv : ∀ i ∈ s, (χ i)⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) (hbound : Real.log x = 2 * a) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    (∑ i ∈ s, (∑' n : ℕ, K.summand (χ i) x n).re) +
        2 * (∑ i ∈ s, (∑' n : ℕ, K.summand (χ i) 1 n).re) ≤
      2 * a * (∑ i ∈ s, Real.log (q i)) + (-3 * a + 18) * s.card := by
  have hs :=
    Finset.sum_le_sum (s := s)
      (fun i hi ↦
        quarter_triangular_two_scale_bound ha (hq i hi) hGRH (hp i hi) (hne i hi) (hinv i hi) hx
          hbound)
  dsimp only at hs ⊢
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at hs
  linarith only [hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
