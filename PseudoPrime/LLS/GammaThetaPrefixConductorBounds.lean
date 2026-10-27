/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRamifiedDualParameterBounds
public import PseudoPrime.LLS.GammaIntegerPrefixConductorBounds

/-! # Adjustable signed dual budgets for actual Jacobi arithmetic -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The finite signed dual budget at theta/sqrt x and the refined scale x.
Its input is the logarithmic scale L and a parameter theta greater than one.
The cutoff is independent of the input factors; the signed ramp remains
in each finite term. This is the numerical quantity for scale certificates. -/
noncomputable def gammaRefinedThetaDualBudget (θ L : ℝ) : ℝ :=
  Analysis.gammaRamifiedThetaParameter θ (Analysis.gammaRefinedScale L) * L +
    ∑ p ∈ Analysis.gammaRamifiedThetaPrimeSet θ (Analysis.gammaRefinedScale L),
      Real.log p *
        max
          (Analysis.gammaRamifiedSignedCombinedCost p (Analysis.gammaRefinedScale L) -
            Analysis.gammaRamifiedThetaParameter θ (Analysis.gammaRefinedScale L))
          0

/-- At the refined scale with L at least 100 log 10 and theta greater than one,
actual Jacobi square, dyadic and ramified losses share a finite theta dual budget.
Use the existing square/dyadic absorption and the adjustable signed support bound.
This is the parameterized joint local input of the integer-prefix comparison. -/
theorem gamma_jacobi_refined_joint_local_cost_le_finite_signed_dual_theta {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (S R : Finset ℕ) (hS : S ⊆ n.primeFactors) (hR : R ⊆ n.primeFactors)
    (hSχ : ∀ p ∈ S, bridge.character p = -1) (hRχ : ∀ p ∈ R, bridge.character p = 0)
    (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {L : ℝ} (hL : 100 * Real.log 10 ≤ L) {θ : ℝ} (hθ : 1 < θ) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale L)) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 (Analysis.gammaRefinedScale L) +
        (∑ p ∈ R,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale L)) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) +
        Analysis.gammaRamifiedThetaParameter θ (Analysis.gammaRefinedScale L) * Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedThetaPrimeSet θ (Analysis.gammaRefinedScale L),
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p (Analysis.gammaRefinedScale L) -
                Analysis.gammaRamifiedThetaParameter θ (Analysis.gammaRefinedScale L))
              0 := by
  have hs := gamma_jacobi_refined_actual_square_dyadic_cost_le bridge S hS hSχ K K2 hL
  have hr :=
    Analysis.gamma_actual_odd_ramified_signed_cost_le_theta_dual hn R hR bridge.character hRχ K hθ
      (by linarith only [Analysis.gamma_refined_scale_ge_twenty_thousand hL])
  linarith only [hs, hr]

/-- For an odd nonsquare input at least 10^100 and theta greater than one,
all actual local losses obey the finite theta dual budget. Classify the
quadratic values and apply the joint bound to the zero and minus-one sets.
This removes auxiliary branch sets from the adjustable comparison. -/
theorem gamma_jacobi_refined_input_all_local_cost_le_finite_signed_dual_theta {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (K : ℕ → Finset ℕ) (K2 : Finset ℕ) (hlarge : 10 ^ 100 ≤ n) {θ : ℝ} (hθ : 1 < θ) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ n.primeFactors,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale (Real.log n))) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2
          (Analysis.gammaRefinedScale (Real.log n)) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) +
        Analysis.gammaRamifiedThetaParameter θ (Analysis.gammaRefinedScale (Real.log n)) *
          Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedThetaPrimeSet θ (Analysis.gammaRefinedScale (Real.log n)),
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p
                  (Analysis.gammaRefinedScale (Real.log n)) -
                Analysis.gammaRamifiedThetaParameter θ (Analysis.gammaRefinedScale (Real.log n)))
              0 := by
  let S := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = -1)
  let R := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = 0)
  have hL := Analysis.gamma_refined_log_range_of_decimal hlarge
  have hj :=
    gamma_jacobi_refined_joint_local_cost_le_finite_signed_dual_theta bridge S R
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) (fun p hp ↦ (Finset.mem_filter.mp hp).2)
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) K K2 hL hθ
  have hc :=
    gamma_actual_quadratic_local_sum_le_classified hn bridge.character bridge.character_quadratic K
      (by linarith only [Analysis.gamma_refined_scale_ge_twenty_thousand hL])
  change
    (∑ p ∈ n.primeFactors,
        Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
          (Analysis.gammaRefinedScale (Real.log n))) ≤
      (∑ p ∈ S,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale (Real.log n))) +
        ∑ p ∈ R,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale (Real.log n)) at hc
  linarith only [hj, hc]

/-- With theta greater than one, the actual integer-prefix character loss
and ambient ramp obey a single finite theta budget under the unit-prime
one condition. Reindex the prefix and split off two, then apply the actual
local bound. This retains the original prefix in the parameterized API. -/
theorem gamma_jacobi_integer_prefix_local_budget_theta {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {b : ℝ} (hb : 1 ≤ b)
    (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p (4 * n) → bridge.character p = 1)
    (hlarge : 10 ^ 100 ≤ n) {θ : ℝ} (hθ : 1 < θ) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        ((∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
            (1 - (bridge.character m).re) * Analysis.gammaResolventMangoldtWeight m) +
          ∑ p ∈ (4 * n).primeFactors,
            Real.log p *
              ((∑' k : ℕ,
                  Analysis.exponentialRampLocalCorrection (bridge.character p)
                    ((p : ℝ) ^ (k + 1) / Analysis.gammaRefinedScale (Real.log n)) (k + 1)) /
                Real.sqrt (Analysis.gammaRefinedScale (Real.log n)))) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) +
        Analysis.gammaRamifiedThetaParameter θ (Analysis.gammaRefinedScale (Real.log n)) *
          Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedThetaPrimeSet θ (Analysis.gammaRefinedScale (Real.log n)),
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p
                  (Analysis.gammaRefinedScale (Real.log n)) -
                Analysis.gammaRamifiedThetaParameter θ (Analysis.gammaRefinedScale (Real.log n)))
              0 := by
  let K := AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b
  have he :=
    AnalyticNumberTheory.DirichletLFunction.gamma_character_prefix_add_ambient_ramp_eq_local_cost
      bridge.character (Nat.mul_pos (by norm_num only) hn.pos) hb hone
      (Analysis.gammaRefinedScale (Real.log n))
  rw [he, gamma_ambient_four_factor_sum_eq hn]
  simpa only [add_assoc] using
    gamma_jacobi_refined_input_all_local_cost_le_finite_signed_dual_theta bridge K (K 2) hlarge hθ

/-- Absence of negative odd-prime Jacobi witnesses up to b implies the
parameterized integer-prefix local budget for theta greater than one.
Transfer the actual no-witness hypothesis to unit-prime character values.
This is the arithmetic input for the adjustable zero-mass comparison. -/
theorem gamma_jacobi_no_negative_integer_prefix_local_budget_theta {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {b : ℝ}
    (hb : 1 ≤ b) (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ b → jacobiSym n p ≠ -1)
    (hlarge : 10 ^ 100 ≤ n) {θ : ℝ} (hθ : 1 < θ) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        ((∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
            (1 - (bridge.character m).re) * Analysis.gammaResolventMangoldtWeight m) +
          ∑ p ∈ (4 * n).primeFactors,
            Real.log p *
              ((∑' k : ℕ,
                  Analysis.exponentialRampLocalCorrection (bridge.character p)
                    ((p : ℝ) ^ (k + 1) / Analysis.gammaRefinedScale (Real.log n)) (k + 1)) /
                Real.sqrt (Analysis.gammaRefinedScale (Real.log n)))) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) +
        Analysis.gammaRamifiedThetaParameter θ (Analysis.gammaRefinedScale (Real.log n)) *
          Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedThetaPrimeSet θ (Analysis.gammaRefinedScale (Real.log n)),
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p
                  (Analysis.gammaRefinedScale (Real.log n)) -
                Analysis.gammaRamifiedThetaParameter θ (Analysis.gammaRefinedScale (Real.log n)))
              0 := by
  exact
    gamma_jacobi_integer_prefix_local_budget_theta bridge hb
      (gamma_jacobi_no_negative_prefix_prime_one bridge hno) hlarge hθ

/-- Under individual RH, the primitive Jacobi zero mass and actual ambient
ramp satisfy the signed prefix comparison with the finite theta dual budget.
Combine the existing signed Poisson formula and the actual local estimate.
This leaves an explicit numerical target with a parameter chosen per cell. -/
theorem gamma_jacobi_zeroMass_add_ambient_ramp_le_integer_prefix_dual_theta {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis bridge.character) {b : ℝ}
    (hb : 1 ≤ b)
    (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p (4 * n) → bridge.character p = 1)
    (hlarge : 10 ^ 100 ≤ n) {θ : ℝ} (hθ : 1 < θ) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor bridge.character.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gammaResolventMajorant ρ.im) +
        (∑ p ∈ (4 * n).primeFactors,
          Real.log p *
            ((∑' k : ℕ,
                Analysis.exponentialRampLocalCorrection (bridge.character p)
                  ((p : ℝ) ^ (k + 1) / Analysis.gammaRefinedScale (Real.log n)) (k + 1)) /
              Real.sqrt (Analysis.gammaRefinedScale (Real.log n)))) ≤
      (Analysis.gammaResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) *
                    (logDeriv bridge.character.gammaFactor
                        (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
          2 * (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
        (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) +
        (3 / 4 : ℝ) +
        gammaRefinedThetaDualBudget θ (Real.log n) := by
  have hf : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (gamma_jacobi_modulus_eq_discriminant bridge).symm ▸ bridge.discriminant_pos
  let : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor := ⟨hf.ne'⟩
  have hq : 2 ≤ (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (Nat.succ_le_iff.mpr bridge.squarefreePart_gt_one).trans
      (Nat.le_of_dvd hf (gamma_jacobi_modulus_squarefree_data bridge).1)
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_zeroMass_le_signed_prefix hq hRH
      bridge.character_primitive bridge.character_ne_one
      (by
        rw [bridge.character_quadratic.inv]; exact bridge.character_ne_one)
      (Finset.Ioc 0 ⌊b⌋₊)
  have hl := gamma_jacobi_integer_prefix_local_budget_theta bridge hb hone hlarge hθ
  dsimp only [gammaRefinedThetaDualBudget]
  linarith only [hz, hl]

/-- Under individual RH and no negative odd-prime witness up to b, the
primitive zero mass and ambient ramp satisfy the adjustable finite dual
comparison. Transfer the witness condition to unit primes and apply the
parameterized zero-mass bound. The finite prefix gain is retained. -/
theorem gamma_jacobi_no_negative_zeroMass_add_ramp_le_prefix_dual_theta {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis bridge.character) {b : ℝ}
    (hb : 1 ≤ b) (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ b → jacobiSym n p ≠ -1)
    (hlarge : 10 ^ 100 ≤ n) {θ : ℝ} (hθ : 1 < θ) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor bridge.character.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gammaResolventMajorant ρ.im) +
        (∑ p ∈ (4 * n).primeFactors,
          Real.log p *
            ((∑' k : ℕ,
                Analysis.exponentialRampLocalCorrection (bridge.character p)
                  ((p : ℝ) ^ (k + 1) / Analysis.gammaRefinedScale (Real.log n)) (k + 1)) /
              Real.sqrt (Analysis.gammaRefinedScale (Real.log n)))) ≤
      (Analysis.gammaResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) *
                    (logDeriv bridge.character.gammaFactor
                        (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
          2 * (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
        (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) +
        (3 / 4 : ℝ) +
        gammaRefinedThetaDualBudget θ (Real.log n) := by
  exact
    gamma_jacobi_zeroMass_add_ambient_ramp_le_integer_prefix_dual_theta bridge hRH hb
      (gamma_jacobi_no_negative_prefix_prime_one bridge hno) hlarge hθ

/-- At theta=5/4 the parameterized signed budget equals the existing
signed budget at every real scale. Substitute the parameter and finite
prime-set identities. This preserves all existing numerical interfaces. -/
theorem gamma_refined_theta_dual_budget_five_fourths (L : ℝ) :
    gammaRefinedThetaDualBudget (5 / 4) L = gammaRefinedSignedDualBudget L := by
  dsimp only [gammaRefinedThetaDualBudget, gammaRefinedSignedDualBudget]
  rw [Analysis.gamma_ramified_theta_prime_set_five_fourths,
    Analysis.gamma_ramified_theta_parameter_five_fourths]

end PseudoPrime.LLS
