/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPrincipalEulerBudget
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GaussianPairedEulerIdentity
public import PseudoPrime.AnalyticNumberTheory.Gamma.GaussianSignedResolventBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.GaussianSignedEulerBounds

/-! # Principal Euler budget for Gaussian zero mass -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Input: an even character.
Claim: its signed Gamma contribution is at most -36/25.
Proof: identify each node with the certified even digamma combination.
Role: improve the fixed zero-mass cost for quadratic even characters. -/
theorem gaussianResolvent_gammaFactor_0_le {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum ≤
      -36 / 25 := by
  have ht := Gamma.gaussian_signed_digamma_0_le
  have hm :
    (Analysis.gaussianResolventCoefficients.map
        (fun ab ↦ (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)) =
      (Analysis.gaussianResolventCoefficients.map
        (fun ab ↦
          (ab.2 : ℝ) *
            (((Complex.digamma ((((1 / 2 : ℝ) + (ab.1 : ℝ) + 0) / 2) : ℂ)).re - Real.log Real.pi) /
              2))) := by
    apply List.map_congr_left
    intro ab hab
    have ha :=
      Rat.cast_lt (K := ℝ) |>.mpr
        (List.forall_iff_forall_mem.mp Analysis.gaussianResolvent_scales_gt_half ab hab)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at ha
    have hh := re_gammaFactor_even he (show (0 : ℝ) < 1 / 2 + (ab.1 : ℝ) by linarith only [ha])
    simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.ofReal_zero, add_zero] using congrArg (fun z : ℝ ↦ (ab.2 : ℝ) * z) hh
  rw [hm]
  exact ht

/-- Input: an odd character.
Claim: its signed Gamma contribution is at most -789/1000.
Proof: identify each node with the certified odd digamma combination.
Role: retain a negative archimedean gain for odd characters. -/
theorem gaussianResolvent_gammaFactor_1_le {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Odd) :
    (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum ≤
      -789 / 1000 := by
  have ht := Gamma.gaussian_signed_digamma_1_le
  have hm :
    (Analysis.gaussianResolventCoefficients.map
        (fun ab ↦ (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)) =
      (Analysis.gaussianResolventCoefficients.map
        (fun ab ↦
          (ab.2 : ℝ) *
            (((Complex.digamma ((((1 / 2 : ℝ) + (ab.1 : ℝ) + 1) / 2) : ℂ)).re - Real.log Real.pi) /
              2))) := by
    apply List.map_congr_left
    intro ab hab
    have ha :=
      Rat.cast_lt (K := ℝ) |>.mpr
        (List.forall_iff_forall_mem.mp Analysis.gaussianResolvent_scales_gt_half ab hab)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at ha
    have hh := re_gammaFactor_odd he (show (0 : ℝ) < 1 / 2 + (ab.1 : ℝ) by linarith only [ha])
    simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using congrArg (fun z : ℝ ↦ (ab.2 : ℝ) * z) hh
  rw [hm]
  exact ht

/-- Input: any complex Dirichlet character.
Claim: its signed Gamma contribution is at most -789/1000.
Proof: split by parity and apply the two signed bounds.
Role: supply a parity-uniform primitive zero-mass estimate. -/
theorem gaussianResolvent_gammaFactor_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum ≤
      -789 / 1000 := by
  rcases χ.even_or_odd with he | ho
  · exact (gaussianResolvent_gammaFactor_0_le he).trans (by norm_num only)
  · exact gaussianResolvent_gammaFactor_1_le ho

/-- Under Riemann RH, the nonnegative common Gaussian Euler mass is below 683/50.
The signed pole sum and the even archimedean gain bound the full infinite sum. -/
theorem gaussianResolvent_euler_lt_principal_budget (hRH : RiemannHypothesis) :
    (∑' n : ℕ, Analysis.gaussianResolventMangoldtWeight n) < 683 / 50 := by
  have he := RiemannXi.gaussianResolvent_euler_lt_fifteen_tenth_add_gamma hRH
  have hg := gaussianResolvent_gammaFactor_0_le principal_modulus_one_even
  linarith only [he, hg]

/-- Under primitive nonprincipal individual RH and Riemann RH, the Gaussian
norm zero mass plus its nonnegative paired Euler tail has explicit additive cost
12871/1000, retaining both the prefix gain and the exact character deficit. -/
theorem gaussian_zeroMass_add_pairedTail_lt_principal_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hRiemann : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (B : Finset ℕ) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) +
        Analysis.gaussianPairedEulerTail χ B <
      (20115621 / 50000000 : ℝ) * Real.log q + 12871 / 1000 -
          2 * (∑ n ∈ B, Analysis.gaussianResolventMangoldtWeight n) +
        ∑ n ∈ B, (1 - (χ n).re) * Analysis.gaussianResolventMangoldtWeight n := by
  have hz := gaussian_zeroMass_add_pairedTail_le_prefix hq hRH hp hne hinv B
  have he := gaussianResolvent_euler_lt_principal_budget hRiemann
  have hg := gaussianResolvent_gammaFactor_le χ
  linarith only [hz, he, hg]

/-- Under primitive nonprincipal individual RH and Riemann RH, the actual Gaussian
norm zero mass has additive cost 12871/1000 instead of the coarse 1811.
Apply the exact paired prefix estimate with the empty prefix and remove only
the certified nonnegative complementary prime-power mass. -/
theorem gaussian_zeroMass_lt_principal_uniform {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hRiemann : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) <
      (20115621 / 50000000 : ℝ) * Real.log q + 12871 / 1000 := by
  have h := gaussian_zeroMass_add_pairedTail_lt_principal_prefix hq hRH hRiemann hp hne hinv ∅
  simp only [Finset.sum_empty, mul_zero, sub_zero, add_zero] at h
  have ht := Analysis.gaussianPairedEulerTail_nonneg χ ∅
  linarith only [h, ht]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
