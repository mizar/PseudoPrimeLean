/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaActualConductorBudget
public import PseudoPrime.Analysis.GammaActualRamifiedBudget
public import PseudoPrime.Analysis.GammaRamifiedFiniteSupport
public import PseudoPrime.NumberTheory.JacobiCharacterArithmetic

/-! # Refined local conductor accounting for the actual primitive Jacobi character -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The actual modulus of the bridge character is the positive fundamental
discriminant of the squarefree part. The square decomposition supplies the
required divisibility in the existing conductor theorem. This identifies
the modulus used by the analytic local-cost interfaces. -/
theorem gamma_jacobi_modulus_eq_discriminant {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    (NumberTheory.complexQuadraticCharacter n hn).conductor = bridge.discriminant := by
  exact
    NumberTheory.complexQuadraticCharacter_conductor_eq_discriminant bridge
      ⟨bridge.squareFactor ^ 2, by
        simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm⟩

/-- The primitive Jacobi modulus is either d or 4d, where d is the bridge
squarefree part. Consequently d divides it and it is at most 4d. These
are the arithmetic premises of the even-conductor square absorption. -/
theorem gamma_jacobi_modulus_squarefree_data {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    bridge.squarefreePart ∣ (NumberTheory.complexQuadraticCharacter n hn).conductor ∧
      (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ 4 * bridge.squarefreePart := by
  rw [gamma_jacobi_modulus_eq_discriminant bridge, bridge.discriminant_eq]
  by_cases hd4 : bridge.squarefreePart % 4 = 1
  · rw [NumberTheory.positiveFundamentalDiscriminant_eq_self hd4]
    exact ⟨dvd_refl _, Nat.le_mul_of_pos_left _ (by norm_num only)⟩
  · rw [NumberTheory.positiveFundamentalDiscriminant_eq_four_mul hd4]
    exact ⟨⟨4, by ring⟩, le_refl _⟩

/-- For the actual primitive Jacobi character, the odd modulus equals d
and its value at two is one or minus one; otherwise the modulus is even.
The exact discriminant formula gives the branches, and two is a unit at
the odd modulus. Quadraticity then excludes the zero value. -/
theorem gamma_jacobi_actual_dyadic_branch {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    ((NumberTheory.complexQuadraticCharacter n hn).conductor = bridge.squarefreePart ∧
        (bridge.character 2 = 1 ∨ bridge.character 2 = -1)) ∨
      Even (NumberTheory.complexQuadraticCharacter n hn).conductor := by
  have he := gamma_jacobi_modulus_eq_discriminant bridge
  by_cases hd4 : bridge.squarefreePart % 4 = 1
  · have hf :=
      he.trans
        (bridge.discriminant_eq.trans (NumberTheory.positiveFundamentalDiscriminant_eq_self hd4))
    have hcop : Nat.Coprime 2 (NumberTheory.complexQuadraticCharacter n hn).conductor := by
      rw [hf]
      exact Nat.coprime_two_left.mpr bridge.squarefreePart_odd
    have hu : IsUnit (2 : ZMod (NumberTheory.complexQuadraticCharacter n hn).conductor) :=
      (ZMod.isUnit_iff_coprime 2 _).mpr hcop
    exact
      Or.inl ⟨hf, (bridge.character_quadratic 2).resolve_left (MulChar.apply_ne_zero_iff.mpr hu)⟩
  · have hf :=
      he.trans
        (bridge.discriminant_eq.trans
          (NumberTheory.positiveFundamentalDiscriminant_eq_four_mul hd4))
    exact Or.inr (hf ▸ ⟨2 * bridge.squarefreePart, by ring⟩)

/-- At the prescribed scale for L>=100 log ten, the actual primitive
Jacobi character of an odd nonsquare input satisfies the shared 3/4
square-plus-dyadic budget for arbitrary positive-power prefixes. All
arithmetic and dyadic-branch premises come from the bridge; conductor
differences are allocated once. This feeds the ramified-prime comparison. -/
theorem gamma_jacobi_refined_actual_square_dyadic_cost_le {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hχ : ∀ p ∈ S, bridge.character p = -1) (K : ℕ → Finset ℕ)
    (K2 : Finset ℕ) {L : ℝ} (hL : 100 * Real.log 10 ≤ L) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale L)) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 (Analysis.gammaRefinedScale L) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) := by
  have hf : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (gamma_jacobi_modulus_eq_discriminant bridge).symm ▸ bridge.discriminant_pos
  have hd := gamma_jacobi_modulus_squarefree_data bridge
  exact
    Analysis.gamma_refined_actual_square_dyadic_cost_le
      (by simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm) hn
      bridge.squarefreePart_pos bridge.squareFactor_odd.pos hf hd.1 hd.2 bridge.character
      (gamma_jacobi_actual_dyadic_branch bridge) S hS hχ K K2 hL

/-- For an odd nonsquare n>=10^100, the primitive Jacobi local costs at
the prescribed scale with L=log n obey the shared 3/4 allowance. The
integer input bound supplies the logarithmic range. This is the actual
input interface, rather than an independently chosen conductor or scale. -/
theorem gamma_jacobi_refined_input_square_dyadic_cost_le {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hχ : ∀ p ∈ S, bridge.character p = -1) (K : ℕ → Finset ℕ)
    (K2 : Finset ℕ) (hlarge : 10 ^ 100 ≤ n) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale (Real.log n))) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2
          (Analysis.gammaRefinedScale (Real.log n)) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) := by
  exact
    gamma_jacobi_refined_actual_square_dyadic_cost_le bridge S hS hχ K K2
      (Analysis.gamma_refined_log_range_of_decimal hlarge)

/-- For the actual primitive Jacobi character, the square and dyadic
losses and all selected ramified input-prime losses obey one joint
comparison. Square and dyadic terms spend the conductor gap once;
ramified Euler and ramp terms share the single dual budget mu log n.
Only the numerical finite positive-excess sum remains to be certified. -/
theorem gamma_jacobi_refined_actual_joint_local_cost_le {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (S R : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hR : R ⊆ n.primeFactors) (hSχ : ∀ p ∈ S, bridge.character p = -1)
    (hRχ : ∀ p ∈ R, bridge.character p = 0) (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {L μ : ℝ}
    (hL : 100 * Real.log 10 ≤ L) (hμ : 0 ≤ μ) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale L)) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 (Analysis.gammaRefinedScale L) +
        (∑ p ∈ R,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale L)) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) + μ * Real.log n +
        ∑ p ∈ R,
          Real.log p *
            max (Analysis.gammaRamifiedCombinedCost p (Analysis.gammaRefinedScale L) - μ) 0 := by
  have hs := gamma_jacobi_refined_actual_square_dyadic_cost_le bridge S hS hSχ K K2 hL
  have hr :=
    Analysis.gamma_actual_ramified_joint_cost_le_input_dual_cap hn.pos R hR bridge.character hRχ K
      (by linarith only [Analysis.gamma_refined_scale_ge_twenty_thousand hL]) hμ
  linarith only [hs, hr]

/-- For n>=10^100, take L=log n in the actual primitive-character joint
local comparison. One input logarithmic budget controls the ramified
Euler and ramp costs, after the square and dyadic conductor absorption.
This is the input-scale interface for the remaining numerical certificate. -/
theorem gamma_jacobi_refined_input_joint_local_cost_le {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (S R : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hR : R ⊆ n.primeFactors) (hSχ : ∀ p ∈ S, bridge.character p = -1)
    (hRχ : ∀ p ∈ R, bridge.character p = 0) (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hlarge : 10 ^ 100 ≤ n) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale (Real.log n))) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2
          (Analysis.gammaRefinedScale (Real.log n)) +
        (∑ p ∈ R,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale (Real.log n))) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) + μ * Real.log n +
        ∑ p ∈ R,
          Real.log p *
            max (Analysis.gammaRamifiedCombinedCost p (Analysis.gammaRefinedScale (Real.log n)) - μ)
              0 := by
  exact
    gamma_jacobi_refined_actual_joint_local_cost_le bridge S R hS hR hSχ hRχ K K2
      (Analysis.gamma_refined_log_range_of_decimal hlarge) hμ

/-- At the prescribed scale, the actual primitive Jacobi joint local
loss is bounded by the square-plus-dyadic allowance and a finite signed
ramified dual sum. Its prime set depends only on the scale, not the
input factorization; the signed ramp is retained in every finite term. -/
theorem gamma_jacobi_refined_joint_local_cost_le_finite_signed_dual {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (S R : Finset ℕ) (hS : S ⊆ n.primeFactors) (hR : R ⊆ n.primeFactors)
    (hSχ : ∀ p ∈ S, bridge.character p = -1) (hRχ : ∀ p ∈ R, bridge.character p = 0)
    (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {L : ℝ} (hL : 100 * Real.log 10 ≤ L) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale L)) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 (Analysis.gammaRefinedScale L) +
        (∑ p ∈ R,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale L)) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) +
        Analysis.gammaRamifiedDualParameter (Analysis.gammaRefinedScale L) * Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedDualPrimeSet (Analysis.gammaRefinedScale L),
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p (Analysis.gammaRefinedScale L) -
                Analysis.gammaRamifiedDualParameter (Analysis.gammaRefinedScale L))
              0 := by
  have hs := gamma_jacobi_refined_actual_square_dyadic_cost_le bridge S hS hSχ K K2 hL
  have hr :=
    Analysis.gamma_actual_odd_ramified_signed_cost_le_finite_dual hn R hR bridge.character hRχ K
      (by linarith only [Analysis.gamma_refined_scale_ge_twenty_thousand hL])
  linarith only [hs, hr]

/-- Quadratic local losses over an odd input's prime factors are bounded
by the zero and minus-one branches selected from the same prime set.
The value-one branch is nonpositive, so discarding it is justified by
the actual signed series theorem. This removes branch-set hypotheses. -/
theorem gamma_actual_quadratic_local_sum_le_classified {n f : ℕ} (_hn : Odd n)
    (χ : DirichletCharacter ℂ f) (hq : χ.IsQuadratic) (K : ℕ → Finset ℕ) {x : ℝ} (hx : 0 < x) :
    (∑ p ∈ n.primeFactors, Analysis.gammaActualPrimeLocalCost χ p (K p) x) ≤
      (∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ χ p = -1),
          Analysis.gammaActualPrimeLocalCost χ p (K p) x) +
        ∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ χ p = 0),
          Analysis.gammaActualPrimeLocalCost χ p (K p) x := by
  have hpoint (p : ℕ) (hp : p ∈ n.primeFactors) :
    Analysis.gammaActualPrimeLocalCost χ p (K p) x ≤
      (if χ p = -1 then Analysis.gammaActualPrimeLocalCost χ p (K p) x else 0) +
        (if χ p = 0 then Analysis.gammaActualPrimeLocalCost χ p (K p) x else 0) := by
    rcases hq p with h0 | h1 | hm
    · norm_num only [h0]
      simp only [ite_false, ite_true, zero_add, le_refl]
    · norm_num only [h1]
      simp only [ite_false, add_zero]
      exact
        Analysis.gamma_actual_one_prime_cost_nonpos χ (Nat.prime_of_mem_primeFactors hp) h1 (K p) hx
    · norm_num only [hm]
      simp only [ite_true, ite_false, add_zero, le_refl]
  simpa only [Finset.sum_filter, Finset.sum_add_distrib] using Finset.sum_le_sum hpoint

/-- For an odd nonsquare input n>=10^100, all actual local losses over
its prime factors and the separate dyadic prime obey one finite signed
dual comparison at L=log n. The primitive arithmetic bridge discharges
conductor branches, quadraticity classifies every input prime, and the
finite support removes the unknown factorization from the upper bound. -/
theorem gamma_jacobi_refined_input_all_local_cost_le_finite_signed_dual {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (K : ℕ → Finset ℕ) (K2 : Finset ℕ) (hlarge : 10 ^ 100 ≤ n) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ n.primeFactors,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale (Real.log n))) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2
          (Analysis.gammaRefinedScale (Real.log n)) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) +
        Analysis.gammaRamifiedDualParameter (Analysis.gammaRefinedScale (Real.log n)) * Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedDualPrimeSet (Analysis.gammaRefinedScale (Real.log n)),
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p
                  (Analysis.gammaRefinedScale (Real.log n)) -
                Analysis.gammaRamifiedDualParameter (Analysis.gammaRefinedScale (Real.log n)))
              0 := by
  let S := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = -1)
  let R := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = 0)
  have hL := Analysis.gamma_refined_log_range_of_decimal hlarge
  have hj :=
    gamma_jacobi_refined_joint_local_cost_le_finite_signed_dual bridge S R
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) (fun p hp ↦ (Finset.mem_filter.mp hp).2)
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) K K2 hL
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

end PseudoPrime.LLS
