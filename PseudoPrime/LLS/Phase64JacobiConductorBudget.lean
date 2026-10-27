/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64SquareConductorBounds
public import PseudoPrime.LLS.Phase64JacobiLocalComparison

/-! # First-phase actual Jacobi conductor absorption -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For any finite prime set and signed node list, a quadratic character's
actual local sum is bounded by its minus-one and zero branches at positive scale.
The one branch is nonpositive. This generic classification needs no oddness hypothesis. -/
theorem finiteSigned_quadratic_local_sum_le_classified (l : List (ℚ × ℚ)) {f : ℕ}
    (χ : DirichletCharacter ℂ f) (hq : χ.IsQuadratic) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 0 < x) :
    (∑ p ∈ P, Analysis.finiteSignedActualPrimeLocalCost l χ p (K p) x) ≤
      (∑ p ∈ P.filter (fun p : ℕ ↦ χ p = -1),
          Analysis.finiteSignedActualPrimeLocalCost l χ p (K p) x) +
        ∑ p ∈ P.filter (fun p : ℕ ↦ χ p = 0),
          Analysis.finiteSignedActualPrimeLocalCost l χ p (K p) x := by
  have hpoint (p : ℕ) (hp : p ∈ P) :
    Analysis.finiteSignedActualPrimeLocalCost l χ p (K p) x ≤
      (if χ p = -1 then Analysis.finiteSignedActualPrimeLocalCost l χ p (K p) x else 0) +
        (if χ p = 0 then Analysis.finiteSignedActualPrimeLocalCost l χ p (K p) x else 0) := by
    rcases hq p with h0 | h1 | hm
    · norm_num only [h0]
      simp only [ite_false, ite_true, zero_add, le_refl]
    · norm_num only [h1]
      simp only [ite_false, add_zero]
      exact Analysis.finiteSigned_actual_one_prime_cost_nonpos l χ (hP p hp) h1 (K p) hx
    · norm_num only [hm]
      simp only [ite_true, ite_false, add_zero, le_refl]
  simpa only [Finset.sum_filter, Finset.sum_add_distrib] using Finset.sum_le_sum hpoint

/-- For actual primitive Jacobi data and scales at least 1600, selected minus-one
input-prime costs and the separate dyadic cost fit M log(4n)+427/500. The arithmetic
bridge discharges conductor divisibility, square decomposition and both parity branches. -/
theorem phase64_jacobi_square_dyadic_cost_le {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hχ : ∀ p ∈ S, bridge.character p = -1) (K : ℕ → Finset ℕ)
    (K2 : Finset ℕ) {x : ℝ} (hx : 1600 ≤ x) :
    (90992831 / 200000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S,
          Analysis.finiteSignedActualPrimeLocalCost Analysis.phaseResolvent64Coefficients
            bridge.character p (K p) x) +
        Analysis.finiteSignedActualPrimeLocalCost Analysis.phaseResolvent64Coefficients
          bridge.character 2 K2 x ≤
      (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) + (427 / 500 : ℝ) := by
  have hf : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (gamma_jacobi_modulus_eq_discriminant bridge).symm ▸ bridge.discriminant_pos
  have hd := gamma_jacobi_modulus_squarefree_data bridge
  exact
    Analysis.phase64_actual_all_square_dyadic_cost_le
      (by simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm) hn
      bridge.squarefreePart_pos bridge.squareFactor_odd.pos hf hd.1 hd.2 bridge.character
      (gamma_jacobi_actual_dyadic_branch bridge) S hS hχ K K2 hx

/-- For actual primitive Jacobi data at scales at least 1600, all ambient local
costs and the conductor logarithm are bounded by M log(4n)+427/500 plus only the
ramified odd-prime costs. Exact classification removes all minus-one and one branches. -/
theorem phase64_jacobi_all_local_cost_le_ramified {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (K : ℕ → Finset ℕ) {x : ℝ}
    (hx : 1600 ≤ x) :
    (90992831 / 200000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ (4 * n).primeFactors,
          Analysis.finiteSignedActualPrimeLocalCost Analysis.phaseResolvent64Coefficients
            bridge.character p (K p) x) ≤
      (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) + (427 / 500 : ℝ) +
        ∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = 0),
          Analysis.finiteSignedActualPrimeLocalCost Analysis.phaseResolvent64Coefficients
            bridge.character p (K p) x := by
  have hs :=
    phase64_jacobi_square_dyadic_cost_le bridge
      (n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = -1)) (Finset.filter_subset _ _)
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) K (K 2) hx
  have hc :=
    finiteSigned_quadratic_local_sum_le_classified Analysis.phaseResolvent64Coefficients
      bridge.character bridge.character_quadratic n.primeFactors
      (fun p hp ↦ Nat.prime_of_mem_primeFactors hp) K (by linarith only [hx] : 0 < x)
  rw [gamma_ambient_four_factor_sum_eq hn]
  linarith only [hs, hc]

/-- Input: actual primitive Jacobi data, an ambient pole modulus, scale and prefix
cutoff. Output: the signed Gamma and Euler budget with conductor, minus-one and
dyadic costs replaced by their proved common allowance. Only ramified odd-prime
local costs remain explicit. Role: isolate the quantitative field still to be certified. -/
noncomputable def phase64RamifiedJacobiBudget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (q : ℕ) (x b : ℝ) : ℝ :=
  (Analysis.phaseResolvent64Coefficients.map
            (fun ab ↦
              (ab.2 : ℝ) *
                (logDeriv bridge.character.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        (∑' k : ℕ, Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients k) -
      2 *
        (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊,
          Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients k) +
    (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) +
    (427 / 500 : ℝ) +
    (∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = 0),
      Analysis.finiteSignedActualPrimeLocalCost Analysis.phaseResolvent64Coefficients
        bridge.character p (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b p)
        x) +
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
    43 * x ^ (-9 / 16 : ℝ)

/-- At scales at least 1600, the actual first-phase local budget is at most the
ramified-only budget. Combine the actual conductor absorption with the exact
coefficient mass; no GRH or witness assumption is needed for this budget comparison. -/
theorem phase64_jacobi_local_budget_le_ramified {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (q : ℕ) {x : ℝ} (hx : 1600 ≤ x)
    (b : ℝ) : phase64JacobiLocalBudget bridge q x b ≤ phase64RamifiedJacobiBudget bridge q x b := by
  have hs :=
    phase64_jacobi_all_local_cost_le_ramified bridge
      (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b) hx
  have hm :=
    congrArg (fun z : ℝ ↦ z * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor)
      Analysis.phase64_coefficient_mass
  dsimp only [phase64JacobiLocalBudget, phase64RamifiedJacobiBudget,
    AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget]
  nlinarith only [hs, hm]

/-- Under GRH and the certified first-cell hypotheses, a strict gap for the
ramified-only phase budget gives an odd-prime negative Jacobi witness through L^2.
The conductor and minus-one local numerical premises have been discharged; the
remaining scalar gap is an explicit hypothesis. -/
theorem exists_odd_prime_negative_of_phase64_ramified_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {L : ℝ} (hlo : 64 ≤ L)
    (hhi : L ≤ 64001 / 1000)
    (hgap :
      phase64RamifiedJacobiBudget bridge q (L ^ 2 / (99 / 40)) (L ^ 2) <
        2 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (L ^ 2 / (99 / 40)) /
              Real.sqrt (L ^ 2 / (99 / 40))) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                (L ^ 2 / (99 / 40)) k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ L ^ 2 ∧ jacobiSym n p = -1 := by
  have hx : (1600 : ℝ) ≤ L ^ 2 / (99 / 40) :=
    (by norm_num only : (1600 : ℝ) ≤ 163840 / 99).trans (Analysis.scale64_cell_of_level hlo hhi).1
  exact
    exists_odd_prime_negative_of_phase64_local_gap bridge hGRH hq hmq hlo hhi
      ((phase64_jacobi_local_budget_le_ramified bridge q hx (L ^ 2)).trans_lt hgap)

end PseudoPrime.LLS
