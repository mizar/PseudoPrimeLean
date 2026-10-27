/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularExplicitZeroTail
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedPoissonHeightMajorants

/-!
# Shifted rational certificates for the triangular low-height zero test

Connect global real height majorants to the low-height oscillating zero series, retaining
signed Gamma terms and explicit Euler error instead of sampled numerical evidence.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The negative of the real alpha-18 oscillating height test below absolute
height one, and zero outside. This is a signed test, not its nonnegative part.
It is total for real scale x; later convergence and numerical bounds assume x>0. -/
noncomputable def triangular18_negativeLowHeightTest (x u : ℝ) : ℝ :=
  if |u| < 1 then
    -(Analysis.triangularMellinFunction 18 (Complex.I * u) * (x : ℂ) ^ (Complex.I * u)).re
  else 0

/-- For every character, scale and point, divisor times the negative low-height
test equals the negative real part of the restricted oscillating zero term.
Expand the real divisor and complex product. This identifies the real test used
in the rational majorant with the actual complex zero series. -/
theorem triangular18_negativeLowHeightTest_divisor_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) (ρ : ℂ) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        triangular18_negativeLowHeightTest x ρ.im =
      -(if |ρ.im| < 1 then K.oscillatingZeroTerm χ x ρ else 0).re := by
  classical
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  dsimp only
  unfold triangular18_negativeLowHeightTest
  by_cases hh : |ρ.im| < 1
  · rw [ite_eq_left hh, ite_eq_left hh]
    simp only [MellinKernel.oscillatingZeroTerm, MellinKernel.kernelZeroTerm,
      triangularMellinKernel, mul_assoc, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      zero_mul, sub_zero, mul_neg]
  · rw [ite_eq_right hh, ite_eq_right hh, mul_zero, Complex.zero_re, neg_zero]

/-- For primitive nonprincipal GRH data, nonprincipal inverse and positive scale,
the alpha-18 oscillating zero series restricted to heights below one is summable.
Dominate its restricted norm by the full summable norm series. This permits real
projection when applying the height-test certificate. -/
theorem summable_triangular18_low_zero_terms {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    Summable (fun ρ : ℂ ↦ if |ρ.im| < 1 then K.oscillatingZeroTerm χ x ρ else 0) := by
  classical
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hs := MellinKernel.summable_oscillatingZeroTerm K hq hGRH hp hne hinv hx
  exact
    hs.norm.of_norm_bounded
      (fun ρ ↦ by
        by_cases hh : |ρ.im| < 1
        · rw [ite_eq_left hh]
        · rw [ite_eq_right hh, norm_zero]; exact norm_nonneg _)

/-- For primitive nonprincipal GRH data and positive scale, a global signed
Poisson-kernel majorant of the negative low-height test gives a lower bound for
the low-height zero real sum. The budget retains the signed conductor coefficient
and Gamma combination, plus absolute-weighted Euler ratios. Establish convergence
and apply the general height-majorant transfer. Constructing the global majorant
and certifying its numerical budget remain separate obligations. -/
theorem triangular18_low_zero_re_lower_of_shifted_majorant {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) {ι : Type*}
    (S : Finset ι) (r t w : ι → ℝ) (hr : ∀ i ∈ S, 0 < r i)
    (hg :
      ∀ u,
        triangular18_negativeLowHeightTest x u ≤
          ∑ i ∈ S,
            w i *
              AnalyticNumberTheory.DirichletLFunction.shiftedPoissonHeightKernel (r i) (t i) u) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18);
    -((∑ i ∈ S, w i) * (Real.log q / 2) +
          (∑ i ∈ S, w i * (logDeriv χ.gammaFactor ((((1 + r i : ℝ) : ℂ) + t i * Complex.I))).re) +
          ∑ i ∈ S, |w i| * (((r i)⁻¹ ^ 2 + (r i + 1)⁻¹) / (1 + (2 : ℝ) ^ (-r i) / r i))) ≤
      (∑' ρ : ℂ, if |ρ.im| < 1 then K.oscillatingZeroTerm χ x ρ else 0).re := by
  classical
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let Lo := fun ρ : ℂ ↦ if |ρ.im| < 1 then K.oscillatingZeroTerm χ x ρ else 0
  have hsLo : Summable Lo := summable_triangular18_low_zero_terms hq hGRH hp hne hinv hx
  have hsre : Summable (fun ρ ↦ -(Lo ρ).re) := (hsLo.map Complex.reCLM Complex.reCLM.continuous).neg
  have hpoint (ρ : ℂ) := triangular18_negativeLowHeightTest_divisor_eq χ x ρ
  have hs := hsre.congr (fun ρ ↦ (hpoint ρ).symm)
  have hb :=
    AnalyticNumberTheory.DirichletLFunction.zero_height_sum_le_shifted_poisson_budget hq
      (hGRH q χ hp) hp hne hinv S r t w hr (triangular18_negativeLowHeightTest x) hg hs
  rw [tsum_congr hpoint, tsum_neg, ← Complex.re_tsum hsLo] at hb
  change -_ ≤ (∑' ρ : ℂ, Lo ρ).re
  linarith only [hb]

end PseudoPrime.LLS.PaperStatements
