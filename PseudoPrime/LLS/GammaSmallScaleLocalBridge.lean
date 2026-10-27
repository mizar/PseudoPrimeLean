/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSmallScaleLocalBounds
public import PseudoPrime.LLS.GammaVariableJacobiComparison

/-! # Factorization-independent Jacobi local budgets from scale 4096 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For any odd nonsquare arithmetic bridge and scale x ≥ 4096, the
actual conductor, selected minus-one input-prime costs and dyadic cost
are bounded by M log(4n)+13/15. Separate odd and even conductor branches,
use the improved square absorption, and pay the actual dyadic branch once.
This replaces a fixed logarithmic input gate with an explicit scale condition. -/
theorem gamma_jacobi_square_dyadic_small_scale {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hχ : ∀ p ∈ S, bridge.character p = -1) (K : ℕ → Finset ℕ)
    (K2 : Finset ℕ) {x : ℝ} (hx : 4096 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 x ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (13 / 15 : ℝ) := by
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
    have hs :=
      Analysis.gamma_actual_odd_square_absorbed_small_scale hnf hn hf bridge.squareFactor_odd.pos S
        hS bridge.character hχ K hx
    have ht :
      Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 x -
          (11783423 / 25000000 : ℝ) * Real.log 4 ≤
        (13 / 15 : ℝ) := by
      rcases htwo with h2 | h2
      · have hc :=
          Analysis.gamma_actual_one_prime_cost_nonpos bridge.character Nat.prime_two
            (by simpa only [Nat.cast_ofNat] using h2) K2 (by linarith only [hx])
        have hl : 0 ≤ (11783423 / 25000000 : ℝ) * Real.log 4 :=
          mul_nonneg (by norm_num only) (Real.log_nonneg (by norm_num only))
        linarith only [hc, hl]
      · exact
          (Analysis.gamma_actual_dyadic_minus_one_cost_small_scale bridge.character h2 K2 hx).trans
            (by norm_num only)
    have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn.pos).ne'
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) hn0]
    linarith only [hs, ht]
  · have hs :=
      Analysis.gamma_actual_square_absorbed_small_scale hdecomp hn bridge.squarefreePart_pos
        bridge.squareFactor_odd.pos hf hd.1 hd.2 S hS bridge.character hχ K hx
    have ht :=
      Analysis.gamma_actual_dyadic_zero_cost_small_scale bridge.character
        (Analysis.gamma_even_modulus_character_two_zero bridge.character heven) K2 hx
    linarith only [hs, ht]

/-- At any x ≥ 4096, selected minus-one and zero input-prime losses of
the actual primitive Jacobi character obey the signed finite dual budget.
Combine the small-scale square/dyadic theorem with the existing ramified
finite-support estimate, valid for x ≥ 1. No fixed input size is assumed. -/
theorem gamma_jacobi_joint_local_small_scale {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (S R : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hR : R ⊆ n.primeFactors) (hSχ : ∀ p ∈ S, bridge.character p = -1)
    (hRχ : ∀ p ∈ R, bridge.character p = 0) (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {x : ℝ}
    (hx : 4096 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 x +
        (∑ p ∈ R, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (13 / 15 : ℝ) +
        Analysis.gammaRamifiedDualParameter x * Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedDualPrimeSet x,
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
              0 := by
  have hs := gamma_jacobi_square_dyadic_small_scale bridge S hS hSχ K K2 hx
  have hr :=
    Analysis.gamma_actual_odd_ramified_signed_cost_le_finite_dual hn R hR bridge.character hRχ K
      (by linarith only [hx])
  linarith only [hs, hr]

/-- All ambient actual local costs at x ≥ 4096, together with M log m,
obey a finite signed budget depending only on n and x. Classify the
quadratic input-prime values, discard only the proven nonpositive one branch,
and split off two from the factors of 4n. This removes unknown factorization
and local-character values from the numerical upper budget. -/
theorem gamma_jacobi_all_local_small_scale {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (K : ℕ → Finset ℕ) {x : ℝ}
    (hx : 4096 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ (4 * n).primeFactors,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (13 / 15 : ℝ) +
        Analysis.gammaRamifiedDualParameter x * Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedDualPrimeSet x,
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
              0 := by
  let S := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = -1)
  let R := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = 0)
  have hj :=
    gamma_jacobi_joint_local_small_scale bridge S R (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) (fun p hp ↦ (Finset.mem_filter.mp hp).2)
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) K (K 2) hx
  have hc :=
    gamma_actual_quadratic_local_sum_le_classified hn bridge.character bridge.character_quadratic K
      (by linarith only [hx])
  change
    (∑ p ∈ n.primeFactors, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) ≤
      (∑ p ∈ S, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) +
        ∑ p ∈ R, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x at hc
  rw [gamma_ambient_four_factor_sum_eq hn]
  linarith only [hj, hc]

/-- Numerical upper budget for an odd nonsquare input n, ambient pole modulus q,
scale x and integer prefix endpoint b. It contains no factorization or character data.
The 13/15 allowance and finite signed ramified excess are valid from x=4096;
the pole modulus and no-negative premises are supplied by the comparison theorem.
Use this budget to certify a strict witness gap on a continuous scale interval. -/
noncomputable def gammaSmallScaleArithmeticBudget (n q : ℕ) (x b : ℝ) : ℝ :=
  (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (13 / 15 : ℝ) +
        Analysis.gammaRamifiedDualParameter x * Real.log n +
        (∑ p ∈ Analysis.gammaRamifiedDualPrimeSet x,
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
              0) +
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
      2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
    43 * x ^ (-9 / 16 : ℝ)

/-- Under GRH, at any scale x ≥ 4096 and prefix 1 ≤ b ≤ 99x/40,
absence of negative odd-prime Jacobi witnesses forces ramp-minus-principal
to be at most the factorization-independent small-scale budget. Combine the
actual signed comparison, exact prefix grouping and all-local upper bound.
Discard the conductor integral only after proving its sign. -/
theorem gamma_jacobi_no_negative_small_scale_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b : ℝ} (hx : 4096 ≤ x)
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * x)
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1) :
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re ≤
      gammaSmallScaleArithmeticBudget n q x b := by
  have hc :=
    gamma_jacobi_no_negative_actual_comparison bridge hGRH hq hmq
      (by linarith only [hx] : (2 : ℝ) ≤ x) (Finset.Ioc 0 ⌊b⌋₊) hno
  have he :=
    gamma_jacobi_prefix_add_ambient_ramp_eq_local_cost bridge hb
      (fun p hp hodd hpb ↦ hno p hp hodd (hpb.trans hbX)) x
  have hu :=
    gamma_jacobi_all_local_small_scale bridge
      (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b) hx
  have hC :=
    Analysis.gammaNegativeConductorTerm_nonpos
      (Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor)
      (by linarith only [hx] : (0 : ℝ) < x)
  dsimp only [gammaJacobiActualBudget] at hc
  dsimp only [gammaSmallScaleArithmeticBudget]
  linarith only [hc, he, hu, hC]

/-- Under GRH and the explicit scale, prefix and ambient pole restrictions,
a strict gap for the factorization-independent budget yields a negative odd-prime
Jacobi witness through 99x/40. Apply the preceding comparison by contradiction.
No local-cost cap is left as a hypothesis; the strict scalar gap still must be certified. -/
theorem exists_odd_prime_negative_of_small_scale_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b : ℝ} (hx : 4096 ≤ x)
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      gammaSmallScaleArithmeticBudget n q x b <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  by_contra hnot
  have hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1 :=
    fun p hp hodd hcut hj ↦ hnot ⟨p, hp, hodd, hcut, hj⟩
  exact
    (not_le_of_gt hgap)
      (gamma_jacobi_no_negative_small_scale_comparison bridge hGRH hq hmq hx hb hbX hno)

end PseudoPrime.LLS
