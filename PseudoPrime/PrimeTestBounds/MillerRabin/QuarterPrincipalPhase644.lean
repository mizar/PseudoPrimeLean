/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLimit644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseRows644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLowPhase

/-! # Critical-line phase and physical corrections for section 122 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The two physical lower-cutoff corrections for a zero at squared radius
`X`. The first restores the omitted moment and the second retains the
boundary term at physical argument one. -/
noncomputable def quarterPhaseCorrection644 (X : ℝ) (ρ : ℂ) : ℝ :=
  let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
  let p := (X : ℂ) ^ ρ / (Real.sqrt X : ℂ)
  let C := (107 / 100 : ℝ) ^ 5 * Real.exp (-(2687 / 1000 * (107 / 100))) / 120
  3 * C * (m * p * quarterMoment644 (ρ + 57 / 100) (1 / X)).re +
    3 * (-m / ρ).re * quarterWeight644 X 1

/-- On the critical line and for radius at least one, the physical zero
contribution is the certified phase summand plus its two lower-cutoff
corrections. This is the pointwise identity for the rectangular ledgers. -/
theorem quarter_physical_phase_644 {r : ℝ} (hr : 1 ≤ r) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    quarterZeroIntegral644 (r ^ 2) ρ =
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) *
              quarterPhaseKernel644 ρ.im).re +
        quarterPhaseCorrection644 (r ^ 2) ρ := by
  have hp : 0 < r := zero_lt_one.trans_le hr
  have hX := one_le_pow₀ hr (n := 2)
  have hρ' : ρ = (1 / 2 : ℂ) + Complex.I * ρ.im := by
    apply Complex.ext <;>
      simp only [hρ, Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
        Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero, zero_add,
        add_zero, zero_div]
  have hK := quarter_mellin_phase_eq_644 ρ.im
  rw [← hρ'] at hK
  have he :
    ((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ) =
      Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) := by
    conv_lhs => rw [hρ']
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_comm] using
      quarter_cutoff_phase_exp (t := ρ.im) hp
  rw [quarter_zero_phase_split_644 hX (by linarith only [hρ])]
  dsimp only [quarterPhaseCorrection644]
  rw [hK, he, mul_assoc]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, add_assoc]

/-- Under RH the physical sum for any finite family of nontrivial zeros
splits into the certified phase summands and the sum of the corrections.
This equality applies to each rectangle in the Abel limit. -/
theorem quarter_physical_sum_644 (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 ≤ r) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S, quarterZeroIntegral644 (r ^ 2) ρ) =
      (∑ ρ ∈ S,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) *
                quarterPhaseKernel644 ρ.im).re) +
        ∑ ρ ∈ S, quarterPhaseCorrection644 (r ^ 2) ρ := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hx := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
  exact
    quarter_physical_phase_644 hr
      (AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hx)

/-- A uniform loss bound for the corrections transfers the four certified
phase bounds to the full nontrivial-zero Abel contribution under RH.
Only the correction sum has to be estimated for the physical cutoff. -/
theorem quarter_abel_phase_rows_644 (hRH : RiemannHypothesis) {D : ℝ}
    (hD :
      ∀ r ∈ Set.Icc 316 322,
        ∀ S : Finset ℂ,
          (∀ ρ ∈ S, riemannZeta ρ = 0) →
            (∀ ρ ∈ S, 0 ≤ ρ.re) → -D ≤ ∑ ρ ∈ S, quarterPhaseCorrection644 (r ^ 2) ρ) :
    let F := fun r : ℝ ↦
      quarterAbelAction644 (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re)
    (∀ r ∈ Set.Icc 316 320, -0.006631 - D ≤ F r) ∧
      (∀ r ∈ Set.Icc 320 (1287 / 4), -0.003250 - D ≤ F r) ∧
      (∀ r ∈ Set.Icc (1287 / 4) (1609 / 5), -0.002063 - D ≤ F r) ∧
      (∀ r ∈ Set.Icc (1609 / 5) 322, -0.002049 - D ≤ F r) := by
  intro F
  have step {r B : ℝ} (hr : r ∈ Set.Icc 316 322)
    (hB :
      ∀ᶠ k : ℕ in Filter.atTop,
        let S :=
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
                (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower k)
                (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 k)).filter
            (fun ρ ↦ ¬ρ.re < 0)
        B ≤
          ∑ ρ ∈ S,
            (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
              (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) *
                  quarterPhaseKernel644 ρ.im).re) :
    B - D ≤ F r := by
    have hr1 : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 316).trans hr.1
    apply ge_of_tendsto (quarter_zero_integral_limit_644 (one_le_pow₀ hr1 (n := 2)))
    filter_upwards [hB] with k hk
    let S :=
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
            (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower k)
            (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 k)).filter
        (fun ρ ↦ ¬ρ.re < 0)
    have hz (ρ : ℂ) (hρ : ρ ∈ S) : riemannZeta ρ = 0 :=
      (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp
          (Finset.mem_filter.mp hρ).1).2
    have hre (ρ : ℂ) (hρ : ρ ∈ S) : 0 ≤ ρ.re := not_lt.mp (Finset.mem_filter.mp hρ).2
    change B - D ≤ ∑ ρ ∈ S, quarterZeroIntegral644 (r ^ 2) ρ
    rw [quarter_physical_sum_644 hRH hr1 S hz hre]
    exact sub_eq_add_neg B D ▸ add_le_add hk (hD r hr S hz hre)
  have h := quarter_phase_rect_rows_644 hRH
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun r hr ↦ step ⟨hr.1, hr.2.trans (by norm_num only)⟩ (h.mono (fun _ hk ↦ hk.1 r hr))
  · exact fun r hr ↦
      step ⟨(by norm_num only : (316 : ℝ) ≤ 320).trans hr.1, hr.2.trans (by norm_num only)⟩
        (h.mono (fun _ hk ↦ hk.2.1 r hr))
  · exact fun r hr ↦
      step ⟨(by norm_num only : (316 : ℝ) ≤ 1287 / 4).trans hr.1, hr.2.trans (by norm_num only)⟩
        (h.mono (fun _ hk ↦ hk.2.2.1 r hr))
  · exact fun r hr ↦
      step ⟨(by norm_num only : (316 : ℝ) ≤ 1609 / 5).trans hr.1, hr.2⟩
        (h.mono (fun _ hk ↦ hk.2.2.2 r hr))

end PseudoPrime.PrimeTestBounds.MillerRabin
