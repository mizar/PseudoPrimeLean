/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaResolventCertificate
public import PseudoPrime.Analysis.GammaResolventTail
public import PseudoPrime.Analysis.GammaResolventGridCertificate
public import PseudoPrime.Analysis.ListInfiniteSum
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonNumericalBounds

/-! # The signed Gamma resolvent against completed L-function zeros

The centered Poisson estimates retain the signed conductor coefficient and give
an absolute error less than 24. Kernel-checked domination transfers the bound to Gamma mass.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character satisfying individual RH and with nonprincipal
inverse, the signed finite combination of real Poisson sums has upper bound
11783423/25000000 times log q plus 24. The certified nodes lie in the numerical
gamma-factor interval; apply their unconditional centered errors with absolute coefficient
weights. This proves the resolvent allowance before comparison with the Gamma kernel. -/
theorem gammaResolvent_poissonSum_lt {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              ∑' ρ : ℂ,
                (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                  ((ab.1 : ℝ) / Complex.normSq ((((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ) - ρ)))).sum <
      (11783423 / 25000000 : ℝ) * Real.log q + 24 := by
  apply
    Analysis.gammaResolvent_weighted_lt_of_euler_centered_bounds
      (fun a : ℚ ↦
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ((a : ℝ) / Complex.normSq ((((1 / 2 : ℝ) + (a : ℝ)) : ℂ) - ρ)))
      (Real.log q)
  intro ab hab
  exact completed_poissonSum_centered_le_resolvent_euler hq hRH hp hne hinv ab hab

/-- Under individual RH for a primitive nonprincipal character with nonprincipal inverse,
a divisor-weighted real resolvent term equals its real Poisson term. A nonzero divisor
forces real part one half; a zero divisor makes both sides vanish. This connects the
ordinate-only kernel to the completed Hadamard identity. -/
theorem completed_resolventTerm_eq_poisson {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (a : ℝ) (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (a / (a ^ 2 + ρ.im ^ 2)) =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        (a / Complex.normSq ((((1 / 2 : ℝ) + a) : ℂ) - ρ)) := by
  by_cases hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0
  · simp only [hD, Int.cast_zero, zero_mul]
  · have hr :=
      completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
        (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD)
    have hn : Complex.normSq ((((1 / 2 : ℝ) + a) : ℂ) - ρ) = a ^ 2 + ρ.im ^ 2 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.sub_im, Complex.add_im, Complex.ofReal_im, hr]
      ring
    rw [hn]

/-- Under individual RH, the divisor-weighted resolvent series is summable for positive scale.
Identify each term with a summable Poisson term to the right of one half.
This justifies rearranging signed finite combinations of resolvent series. -/
theorem summable_completed_resolvent_terms {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a : ℝ} (ha : 0 < a) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (a / (a ^ 2 + ρ.im ^ 2))) := by
  have hs : 1 / 2 < ((((1 / 2 : ℝ) + a) : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith only [ha]
  have hpS := summable_completed_poisson_terms hq hRH hp hne hinv hs
  have hn : 1 / 2 + a - 1 / 2 = a := by ring
  simp only [Complex.add_re, Complex.ofReal_re, hn] at hpS
  exact hpS.congr (fun ρ ↦ (completed_resolventTerm_eq_poisson hRH hp hne hinv a ρ).symm)

/-- At each complex point, distribute its completed L-function divisor multiplicity
through the signed finite resolvent sum. Reorder the scalar factors without discarding signs.
This supplies the pointwise identity for finite/infinite sum interchange. -/
theorem gammaResolvent_weightedTerm_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        Analysis.gammaResolventMajorant ρ.im =
      (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + ρ.im ^ 2))))).sum := by
  rw [Analysis.gammaResolventMajorant, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _
  ring

/-- Every certified signed resolvent node gives a summable divisor-weighted series
for a primitive nonprincipal character under individual RH. The certified positive scales
allow the Poisson summability theorem; scalar multiplication preserves convergence.
This is the common input for the finite/infinite sum interchange and total mass convergence. -/
theorem summable_gammaResolvent_node_terms {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∀ ab ∈ Analysis.gammaResolventCoefficients,
      Summable
        (fun ρ : ℂ ↦
          (ab.2 : ℝ) *
            ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + ρ.im ^ 2)))) := by
  intro ab hab
  have hal := List.forall_iff_forall_mem.mp Analysis.gammaResolvent_scales_gt_half ab hab
  have halR := (Rat.cast_lt (K := ℝ)).mpr hal
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at halR
  exact
    (summable_completed_resolvent_terms hq hRH hp hne hinv (by linarith only [halR])).mul_left
      (ab.2 : ℝ)

/-- For a primitive nonprincipal character under individual RH with nonprincipal inverse,
the divisor-weighted signed Gamma resolvent is summable. Sum the convergent node series
and use the pointwise finite-sum identity. This permits comparison with a dominated Gamma kernel. -/
theorem summable_completed_gammaResolvent_terms {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) := by
  exact
    (Analysis.summable_list_sum Analysis.gammaResolventCoefficients _
          (summable_gammaResolvent_node_terms hq hRH hp hne hinv)).congr
      (fun ρ ↦ (gammaResolvent_weightedTerm_eq χ ρ).symm)

/-- For a primitive nonprincipal character under individual RH with nonprincipal inverse,
the divisor-weighted Gamma resolvent mass equals the finite signed combination of real Poisson
sums. Each resolvent series is summable; interchange the finite and infinite sums and
identify the ordinate-only kernels on the critical line. This exposes the exact conductor term. -/
theorem gammaResolvent_zeroMass_eq_poissonSum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) =
      (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              ∑' ρ : ℂ,
                (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                  ((ab.1 : ℝ) / Complex.normSq ((((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ) - ρ)))).sum := by
  have hs := summable_gammaResolvent_node_terms hq hRH hp hne hinv
  rw [tsum_congr (fun ρ ↦ gammaResolvent_weightedTerm_eq χ ρ),
    Analysis.tsum_list_sum Analysis.gammaResolventCoefficients _ hs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _
  rw [tsum_mul_left]
  apply congrArg (fun z : ℝ ↦ (ab.2 : ℝ) * z)
  exact tsum_congr (fun ρ ↦ completed_resolventTerm_eq_poisson hRH hp hne hinv (ab.1 : ℝ) ρ)

/-- For a primitive nonprincipal character of modulus at least two under individual RH
and with nonprincipal inverse, the signed resolvent mass is strictly below
11783423/25000000 times log q plus 24. Identify it with the certified Poisson combination.
The comparison of the actual Gamma kernel with this resolvent remains a separate theorem. -/
theorem gammaResolvent_zeroMass_lt {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) <
      (11783423 / 25000000 : ℝ) * Real.log q + 24 := by
  rw [gammaResolvent_zeroMass_eq_poissonSum hq hRH hp hne hinv]
  exact gammaResolvent_poissonSum_lt hq hRH hp hne hinv

/-- If the real Gamma critical-line norm is globally dominated by the certified resolvent,
a primitive nonprincipal character under individual RH has Gamma zero mass strictly below
11783423/25000000 times log q plus 24. Nonnegative divisor multiplicities permit the
pointwise comparison, and resolvent summability also establishes Gamma mass summability.
The comparison isolates the domination certificate from the Poisson mass calculation. -/
theorem gamma_zeroMass_lt_of_resolvent_majorant
    (hΓ :
      ∀ t : ℝ, ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤ Analysis.gammaResolventMajorant t)
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) <
      (11783423 / 25000000 : ℝ) * Real.log q + 24 := by
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn (ρ : ℂ) : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hb (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖ ≤
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        Analysis.gammaResolventMajorant ρ.im := by
    by_cases hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0
    · simp only [hD, Int.cast_zero, zero_mul, le_refl]
    · have hr :=
        completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
          (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD)
      have he : ρ = (1 / 2 : ℂ) + Complex.I * ρ.im := by
        calc
          ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := (Complex.re_add_im ρ).symm
          _ = _ := by
            rw [hr]
            norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
            ring
      exact mul_le_mul_of_nonneg_left (by simpa only [← he] using hΓ ρ.im) (hn ρ)
  have hg := summable_completed_gammaResolvent_terms hq hRH hp hne hinv
  have hsum := hg.of_nonneg_of_le (fun ρ ↦ mul_nonneg (hn ρ) (norm_nonneg _)) hb
  exact (hsum.tsum_le_tsum hb hg).trans_lt (gammaResolvent_zeroMass_lt hq hRH hp hne hinv)

/-- A Gamma domination certificate on the compact ordinate interval |t|≤16 suffices
for the explicit Gamma zero-mass bound of a primitive nonprincipal character under
individual RH. The proved rational-exponential tail extends the certificate globally,
and the centered Poisson comparison gives the conductor coefficient and constant 24. -/
theorem gamma_zeroMass_lt_of_compact_resolvent_majorant
    (hΓ :
      ∀ t : ℝ,
        |t| ≤ 16 →
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤ Analysis.gammaResolventMajorant t)
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) <
      (11783423 / 25000000 : ℝ) * Real.log q + 24 := by
  exact
    gamma_zeroMass_lt_of_resolvent_majorant
      (Analysis.norm_Gamma_half_add_I_le_gammaResolvent_of_compact hΓ) hq hRH hp hne hinv

/-- For a primitive nonprincipal character under individual RH, with nonprincipal
inverse and modulus at least two, the Gamma zero mass is below
11783423/25000000 times log q plus 24. The kernel-checked resolvent majorant
and signed Poisson comparison supply the estimate without a domination hypothesis. -/
theorem gamma_zeroMass_lt {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) <
      (11783423 / 25000000 : ℝ) * Real.log q + 24 := by
  exact
    gamma_zeroMass_lt_of_resolvent_majorant Analysis.norm_Gamma_half_add_I_le_gammaResolvent hq hRH
      hp hne hinv

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
