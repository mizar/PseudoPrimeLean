/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaResolventZeroMass
public import PseudoPrime.Analysis.GaussianResolventCompact
public import PseudoPrime.Analysis.GaussianResolventGridCertificate

/-! # Finite-conductor Gaussian Gamma zero mass from the resolvent grid

The signed Poisson combination has coefficient 20115621/50000000 and error below
1811. Global grid domination transfers the allowance to the actual Gaussian norm.
The conditional factories retain the grid input. The final bounds discharge it
with the kernel-checked certificate.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character under individual RH with nonprincipal
inverse and modulus at least two, the signed Gaussian resolvent Poisson sum is below
20115621/50000000 times log q plus 1811. Apply the actual centered baseline estimate
at the twelve certified nodes and retain their signed conductor contribution. -/
theorem gaussianResolvent_poissonSum_lt {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              ∑' ρ : ℂ,
                (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                  ((ab.1 : ℝ) / Complex.normSq ((((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ) - ρ)))).sum <
      (20115621 / 50000000 : ℝ) * Real.log q + 1811 := by
  apply
    Analysis.gaussianResolvent_weighted_lt_of_centered_bounds
      (fun a : ℚ ↦
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ((a : ℝ) / Complex.normSq ((((1 / 2 : ℝ) + (a : ℝ)) : ℂ) - ρ)))
      (Real.log q)
  intro ab hab
  have hal := List.forall_iff_forall_mem.mp Analysis.gaussianResolvent_scales_gt_half ab hab
  have hau := (List.forall_iff_forall_mem.mp Analysis.gaussianResolvent_gamma_arguments ab hab).2.2
  have halR := (Rat.cast_lt (K := ℝ)).mpr hal
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at halR
  have hauR := (Rat.cast_le (K := ℝ)).mpr hau
  norm_num only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat] at hauR
  have hs : 1 < 1 / 2 + (ab.1 : ℝ) := by linarith only [halR]
  have hsu : 1 / 2 + (ab.1 : ℝ) ≤ 15 / 2 := by linarith only [hauR]
  have hb := completed_poissonSum_centered_le_inv_gap hq hRH hp hne hinv hs hsu
  have hn : 1 / 2 + (ab.1 : ℝ) - 1 / 2 = (ab.1 : ℝ) := by ring
  have he : 1 / 2 + (ab.1 : ℝ) - 1 = (ab.1 : ℝ) - 1 / 2 := by ring
  simpa only [hn, he, Complex.ofReal_add] using hb

/-- At each complex point, distribute its completed L-function divisor multiplicity
through the signed finite resolvent sum. Reorder the scalar factors without discarding signs.
This supplies the pointwise identity for finite/infinite sum interchange. -/
theorem gaussianResolvent_weightedTerm_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        Analysis.gaussianResolventMajorant ρ.im =
      (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + ρ.im ^ 2))))).sum := by
  rw [Analysis.gaussianResolventMajorant, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _
  ring

/-- Every certified signed resolvent node gives a summable divisor-weighted series
for a primitive nonprincipal character under individual RH. The certified positive scales
allow the Poisson summability theorem; scalar multiplication preserves convergence.
This is the common input for the finite/infinite sum interchange and total mass convergence. -/
theorem summable_gaussianResolvent_node_terms {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∀ ab ∈ Analysis.gaussianResolventCoefficients,
      Summable
        (fun ρ : ℂ ↦
          (ab.2 : ℝ) *
            ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + ρ.im ^ 2)))) := by
  intro ab hab
  have hal := List.forall_iff_forall_mem.mp Analysis.gaussianResolvent_scales_gt_half ab hab
  have halR := (Rat.cast_lt (K := ℝ)).mpr hal
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at halR
  exact
    (summable_completed_resolvent_terms hq hRH hp hne hinv (by linarith only [halR])).mul_left
      (ab.2 : ℝ)

/-- For a primitive nonprincipal character under individual RH with nonprincipal inverse,
the divisor-weighted signed Gaussian resolvent is summable. Sum the convergent node series
and use the pointwise finite-sum identity.
This permits comparison with a dominated Gaussian kernel. -/
theorem summable_completed_gaussianResolvent_terms {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gaussianResolventMajorant ρ.im) := by
  exact
    (Analysis.summable_list_sum Analysis.gaussianResolventCoefficients _
          (summable_gaussianResolvent_node_terms hq hRH hp hne hinv)).congr
      (fun ρ ↦ (gaussianResolvent_weightedTerm_eq χ ρ).symm)

/-- For a primitive nonprincipal character under individual RH with nonprincipal inverse,
the divisor-weighted Gaussian resolvent mass equals the finite signed combination of real Poisson
sums. Each resolvent series is summable; interchange the finite and infinite sums and
identify the ordinate-only kernels on the critical line. This exposes the exact conductor term. -/
theorem gaussianResolvent_zeroMass_eq_poissonSum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gaussianResolventMajorant ρ.im) =
      (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              ∑' ρ : ℂ,
                (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                  ((ab.1 : ℝ) / Complex.normSq ((((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ) - ρ)))).sum := by
  have hs := summable_gaussianResolvent_node_terms hq hRH hp hne hinv
  rw [tsum_congr (fun ρ ↦ gaussianResolvent_weightedTerm_eq χ ρ),
    Analysis.tsum_list_sum Analysis.gaussianResolventCoefficients _ hs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _
  rw [tsum_mul_left]
  apply congrArg (fun z : ℝ ↦ (ab.2 : ℝ) * z)
  exact tsum_congr (fun ρ ↦ completed_resolventTerm_eq_poisson hRH hp hne hinv (ab.1 : ℝ) ρ)

/-- For a primitive nonprincipal character of modulus at least two under individual RH
and with nonprincipal inverse, the signed resolvent mass is strictly below
20115621/50000000 times log q plus 1811. Identify it with the certified Poisson combination.
The comparison of the actual Gaussian kernel with this resolvent remains a separate theorem. -/
theorem gaussianResolvent_zeroMass_lt {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gaussianResolventMajorant ρ.im) <
      (20115621 / 50000000 : ℝ) * Real.log q + 1811 := by
  rw [gaussianResolvent_zeroMass_eq_poissonSum hq hRH hp hne hinv]
  exact gaussianResolvent_poissonSum_lt hq hRH hp hne hinv

/-- Given global domination by the Gaussian resolvent, individual RH for a
primitive nonprincipal character with nonprincipal inverse yields the actual Gaussian
zero-mass bound with coefficient 20115621/50000000 and additive allowance 1811.
Nonnegative multiplicities and resolvent summability justify the infinite-sum comparison. -/
theorem gaussian_zeroMass_lt_of_resolvent_majorant
    (hK :
      ∀ t : ℝ,
        ‖Analysis.gaussianGammaFunction (Complex.I * (t : ℂ))‖ ≤
          Analysis.gaussianResolventMajorant t)
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) <
      (20115621 / 50000000 : ℝ) * Real.log q + 1811 := by
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn (ρ : ℂ) : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hb (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖ ≤
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        Analysis.gaussianResolventMajorant ρ.im := by
    by_cases hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0
    · simp only [hD, Int.cast_zero, zero_mul, le_refl]
    · have hr :=
        completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
          (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD)
      have he : ρ - 1 / 2 = Complex.I * (ρ.im : ℂ) := by
        calc
          ρ - 1 / 2 = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I - 1 / 2 := by rw [Complex.re_add_im]
          _ = _ := by
            rw [hr]
            norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
            ring
      exact mul_le_mul_of_nonneg_left (by simpa only [he] using hK ρ.im) (hn ρ)
  have hg := summable_completed_gaussianResolvent_terms hq hRH hp hne hinv
  have hsum := hg.of_nonneg_of_le (fun ρ ↦ mul_nonneg (hn ρ) (norm_nonneg _)) hb
  exact (hsum.tsum_le_tsum hb hg).trans_lt (gaussianResolvent_zeroMass_lt hq hRH hp hne hinv)

/-- The 16001 grid inequalities imply the actual Gaussian zero-mass bound
for a primitive nonprincipal character of modulus at least two under individual RH,
with nonprincipal inverse. The grid comparison supplies global domination and the
proved Poisson estimates supply coefficient 20115621/50000000 and additive 1811. -/
theorem gaussian_zeroMass_lt_of_grid
    (hnodes :
      ∀ j : ℕ, j ≤ 16000 → 9 / 100000 ≤ Analysis.gaussianResolventScaledGap ((j : ℝ) / 1000))
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) <
      (20115621 / 50000000 : ℝ) * Real.log q + 1811 := by
  exact
    gaussian_zeroMass_lt_of_resolvent_majorant
      (Analysis.norm_gaussianGammaFunction_le_gaussianResolvent_of_grid hnodes) hq hRH hp hne hinv

/-- Under the same grid and character hypotheses, the Gaussian zero mass is
below 161/400 times log q plus 1811. Enlarge the exact rational coefficient using
log q≥0. This supplies the target conductor coefficient, conditional only on the grid
and the stated character and RH hypotheses. -/
theorem gaussian_zeroMass_lt_target_of_grid
    (hnodes :
      ∀ j : ℕ, j ≤ 16000 → 9 / 100000 ≤ Analysis.gaussianResolventScaledGap ((j : ℝ) / 1000))
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) <
      (161 / 400 : ℝ) * Real.log q + 1811 := by
  have hL : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ((by decide : 1 ≤ 2).trans hq))
  have hM :=
    mul_le_mul_of_nonneg_right (by norm_num only : (20115621 / 50000000 : ℝ) ≤ 161 / 400) hL
  exact (gaussian_zeroMass_lt_of_grid hnodes hq hRH hp hne hinv).trans_le (add_le_add_left hM 1811)

/-- Under primitive nonprincipal individual RH, with nonprincipal inverse and modulus
at least two, the actual Gaussian zero mass is below the exact conductor coefficient
20115621/50000000 times log q plus 1811. The kernel-checked grid supplies global
domination, so no numerical certificate or additional analytic bound remains as a hypothesis. -/
theorem gaussian_zeroMass_lt {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) <
      (20115621 / 50000000 : ℝ) * Real.log q + 1811 := by
  exact gaussian_zeroMass_lt_of_grid Analysis.gaussianResolvent_grid_lower hq hRH hp hne hinv

/-- Under the same character and RH hypotheses, the actual Gaussian zero mass is
below 161/400 times log q plus 1811. Apply the kernel-certified grid and the target
coefficient comparison. This discharges the Gaussian finite-conductor mass input. -/
theorem gaussian_zeroMass_lt_target {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) <
      (161 / 400 : ℝ) * Real.log q + 1811 := by
  exact gaussian_zeroMass_lt_target_of_grid Analysis.gaussianResolvent_grid_lower hq hRH hp hne hinv

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
