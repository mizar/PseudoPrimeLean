/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaLocalBudgetCertificate
public import PseudoPrime.LLS.GammaScaleJointBudget

/-! # Certified finite-scale local data in the Jacobi witness comparison -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: Jacobi arithmetic data, selected minus-one primes and a local certificate.
Claim: conductor, square and dyadic costs fit mu log(4n)+delta.
Proof: use the actual conductor parity branch and the generic square/dyadic absorptions.
Role: transfer arbitrary certified scales to the actual quadratic character. -/
theorem gamma_jacobi_square_dyadic_of_local_certificate {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hχ : ∀ p ∈ S, bridge.character p = -1) (K : ℕ → Finset ℕ)
    (K2 : Finset ℕ) {x δ : ℝ} (cert : Analysis.GammaLocalBudgetCertificate x δ) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 x ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + δ := by
  have hd := gamma_jacobi_modulus_squarefree_data bridge
  have hf : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (gamma_jacobi_modulus_eq_discriminant bridge).symm ▸ bridge.discriminant_pos
  have hdecomp : n = bridge.squarefreePart * bridge.squareFactor ^ 2 := by
    simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm
  rcases gamma_jacobi_actual_dyadic_branch bridge with ⟨hfd, htwo⟩ | heven
  · have hnf :
      n = (NumberTheory.complexQuadraticCharacter n hn).conductor * bridge.squareFactor ^ 2 := by
      rw [hfd]
      exact hdecomp
    exact
      Analysis.gamma_actual_odd_square_dyadic_of_local_certificate hnf hn hf
        bridge.squareFactor_odd.pos S hS bridge.character hχ htwo K K2 cert
  · exact
      Analysis.gamma_actual_square_dyadic_of_local_certificate hdecomp hn bridge.squarefreePart_pos
        bridge.squareFactor_odd.pos hf hd.1 hd.2 S hS bridge.character hχ
        (Analysis.gamma_even_modulus_character_two_zero bridge.character heven) K K2 cert

/-- Input: Jacobi data, selected minus-one and zero primes and a local certificate.
Claim: their joint costs obey the displayed signed ramified dual bound.
Proof: add the existing finite ramified estimate, valid from scale one.
Role: retain the signed Euler correction instead of taking absolute losses. -/
theorem gamma_jacobi_joint_local_of_certificate {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (S R : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hR : R ⊆ n.primeFactors) (hSχ : ∀ p ∈ S, bridge.character p = -1)
    (hRχ : ∀ p ∈ R, bridge.character p = 0) (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {x δ : ℝ}
    (cert : Analysis.GammaLocalBudgetCertificate x δ) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 x +
        (∑ p ∈ R, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + δ +
        Analysis.gammaRamifiedDualParameter x * Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedDualPrimeSet x,
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
              0 := by
  have hs := gamma_jacobi_square_dyadic_of_local_certificate bridge S hS hSχ K K2 cert
  have hr :=
    Analysis.gamma_actual_odd_ramified_signed_cost_le_finite_dual hn R hR bridge.character hRχ K
      cert.scale_ge_one
  linarith only [hs, hr]

/-- Input: Jacobi data and a local certificate for all positive-power prefixes.
Claim: all ambient local costs fit the signed finite dual budget.
Proof: classify local quadratic values and separate the dyadic factor.
Role: remove factorization and character values from the public numeric interface. -/
theorem gamma_jacobi_all_local_of_certificate {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (K : ℕ → Finset ℕ) {x δ : ℝ}
    (cert : Analysis.GammaLocalBudgetCertificate x δ) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ (4 * n).primeFactors,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + δ +
        Analysis.gammaRamifiedDualParameter x * Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedDualPrimeSet x,
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
              0 := by
  let S := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = -1)
  let R := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = 0)
  have hj :=
    gamma_jacobi_joint_local_of_certificate bridge S R (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) (fun p hp ↦ (Finset.mem_filter.mp hp).2)
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) K (K 2) cert
  have hc :=
    gamma_actual_quadratic_local_sum_le_classified hn bridge.character bridge.character_quadratic K
      (zero_lt_one.trans_le cert.scale_ge_one)
  change
    (∑ p ∈ n.primeFactors, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) ≤
      (∑ p ∈ S, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) +
        ∑ p ∈ R, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x at hc
  rw [gamma_ambient_four_factor_sum_eq hn]
  linarith only [hj, hc]

/-- Input: an odd nonsquare input, a common log cap L and a local certificate.
Claim: the actual joint budget is at most the factor-free budget plus delta-3/4.
Proof: substitute the certificate and enlarge conductor and dual logarithms.
Role: expose the precise cost of changing the dyadic allowance. -/
theorem gamma_joint_prefix_le_of_local_certificate {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    {L b x δ : ℝ} (hlog : Real.log n ≤ L) (cert : Analysis.GammaLocalBudgetCertificate x δ) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      gammaFactorFreeJointBudget L b x + δ - 3 / 4 := by
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns
  let K := AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b
  have hl := gamma_jacobi_all_local_of_certificate bridge K cert
  have he : bridge.character = (NumberTheory.complexQuadraticCharacter n hn).primitiveCharacter :=
    bridge.character_eq
  have hm := mul_le_mul_of_nonneg_left hlog (Analysis.gamma_ramified_dual_parameter_nonneg x)
  have hlog4 : Real.log (4 * (n : ℝ)) ≤ L + 7 / 5 := by
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_pos.mpr hn.pos).ne']
    linarith only [hlog, Analysis.log_four_le_seven_fifths]
  have hlead := mul_le_mul_of_nonneg_left hlog4 (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  rw [gammaJointPrefixLocalBudget, ← he]
  dsimp only [gammaFactorFreeJointBudget, gammaScaleSignedDualBudget]
  linarith only [hl, hm, hlead]

/-- Input: the local certificate and an auxiliary pole log cap.
Claim: factor-free separation is at most actual separation plus delta-3/4.
Proof: compare the local and pole budgets with their signs retained.
Role: determine the exact scalar gap required for witness extraction. -/
theorem gamma_factor_free_separation_of_local_certificate {n Q : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    {L b x δ : ℝ} (hlog : Real.log n ≤ L) (cert : Analysis.GammaLocalBudgetCertificate x δ)
    (hlogQ : Real.log Q ≤ L + 7 / 5) :
    gammaFactorFreeSeparation L b x ≤
      gammaJointPrefixSeparation Q (NumberTheory.complexQuadraticCharacter n hn) b x (-3 / 2) + δ -
        3 / 4 := by
  have hJ := gamma_joint_prefix_le_of_local_certificate (b := b) hn hns hlog cert
  have hN :
    ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x ≤ ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x :=
    div_le_div_of_nonneg_right (by linarith only [hlogQ]) (Real.sqrt_nonneg x)
  dsimp only [gammaFactorFreeSeparation, gammaJointPrefixSeparation]
  linarith only [hJ, hN]

end PseudoPrime.LLS
