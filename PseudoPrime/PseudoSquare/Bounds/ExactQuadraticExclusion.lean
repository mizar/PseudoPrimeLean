/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.TightCubicNegativeSupportBounds
public import PseudoPrime.NumberTheory.PrimitiveQuadraticTwo

/-! # Exact primitive quadratic exclusion costs, with ramification counted once -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For a positive squarefree integer, the distinct prime logarithms sum to its
logarithm. Take logarithms of the exact prime product, using positive prime factors.
This identifies the ramified contribution without replacing it by an upper bound. -/
private theorem squarefree_prime_log_sum_eq {d : ℕ} (hd : Squarefree d) :
    (∑ p ∈ d.primeFactors, Real.log p) = Real.log d := by
  have he := congrArg (fun m : ℕ ↦ Real.log (m : ℝ)) (Nat.prod_primeFactors_of_squarefree hd)
  rw [Nat.cast_prod,
    Real.log_prod
      (fun p hp ↦ Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.prime_of_mem_primeFactors hp).pos))] at he
  exact he

/-- The primitive quadratic exclusion cost on the squarefree part equals log(d).
Each ramified prime has primitive value zero and contributes exactly log(p).
Squarefreeness converts that support sum to the full logarithm. -/
theorem primitiveQuadratic_ramified_cost {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    AnalyticNumberTheory.Arithmetic.characterExclusionCost
        (NumberTheory.primitiveQuadraticCharacter n hn) b.squarefreePart =
      Real.log b.squarefreePart := by
  unfold AnalyticNumberTheory.Arithmetic.characterExclusionCost
  calc
    _ = ∑ p ∈ b.squarefreePart.primeFactors, Real.log p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [primitiveQuadraticCharacter_zero_on_squarefreePart b hp, Complex.zero_re]
      ring
    _ = _ := squarefree_prime_log_sum_eq b.squarefreePart_squarefree

/-- On square-factor primes absent from d, the primitive defect sum equals twice
the negative-support logarithm sum. Evaluate every unramified odd prime and show
that primes shared with d have zero Jacobi indicator, so no support is counted twice. -/
theorem primitiveQuadratic_negative_cost_exact {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    (∑ p ∈ b.squareFactor.primeFactors \ b.squarefreePart.primeFactors,
        (1 - (NumberTheory.primitiveQuadraticCharacter n hn p).re) * Real.log p) =
      2 * negativeSquareFactorCost b.squarefreePart b.squareFactor := by
  classical
  have he :
    (∑ p ∈ b.squareFactor.primeFactors \ b.squarefreePart.primeFactors,
        (1 - (NumberTheory.primitiveQuadraticCharacter n hn p).re) * Real.log p) =
      ∑ p ∈ b.squareFactor.primeFactors \ b.squarefreePart.primeFactors,
        if jacobiSym b.squarefreePart p = -1 then 2 * Real.log p else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hm := Finset.mem_sdiff.mp hp
    exact
      primitiveQuadratic_defect_log_eq_negative b (Nat.prime_of_mem_primeFactors hm.1)
        (Odd.of_dvd_nat b.squareFactor_odd (Nat.dvd_of_mem_primeFactors hm.1))
        (fun hd ↦
          hm.2
            (Nat.mem_primeFactors.mpr
              ⟨Nat.prime_of_mem_primeFactors hm.1, hd, b.squarefreePart_pos.ne'⟩))
  rw [he]
  have hs :
    (∑ p ∈ b.squareFactor.primeFactors \ b.squarefreePart.primeFactors,
        if jacobiSym b.squarefreePart p = -1 then 2 * Real.log p else 0) =
      ∑ p ∈ b.squareFactor.primeFactors,
        if jacobiSym b.squarefreePart p = -1 then 2 * Real.log p else 0 := by
    apply Finset.sum_subset Finset.sdiff_subset
    intro p hp hnot
    have hd : p ∈ b.squarefreePart.primeFactors := by
      by_contra hd
      exact hnot (Finset.mem_sdiff.mpr ⟨hp, hd⟩)
    have hz : jacobiSym b.squarefreePart p = 0 :=
      jacobiSym.eq_zero_iff.mpr
        ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero, by
          rw [Int.gcd_natCast_natCast, Nat.gcd_eq_right (Nat.dvd_of_mem_primeFactors hd)]
          exact (Nat.prime_of_mem_primeFactors hp).ne_one⟩
    rw [hz]
    norm_num only [ite_false]
  rw [hs, ← Finset.sum_filter]
  exact (Finset.mul_sum _ _ _).symm

/-- For canonical n=d*s^2, the actual primitive exclusion cost at 2n is exactly
log(d)+(1-Re(chi(2)))log(2)+2E_-(s). Split the disjoint prime two from odd n,
then split squarefree and square-factor supports with their intersection removed.
This is the exact arithmetic input to the conductor-sensitive cubic radius. -/
theorem primitiveQuadratic_exclusion_cost_exact {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    AnalyticNumberTheory.Arithmetic.characterExclusionCost
        (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) =
      Real.log b.squarefreePart +
        (1 - (NumberTheory.primitiveQuadraticCharacter n hn 2).re) * Real.log 2 +
        2 * negativeSquareFactorCost b.squarefreePart b.squareFactor := by
  classical
  let χ := NumberTheory.primitiveQuadraticCharacter n hn
  have hsq :=
    AnalyticNumberTheory.Arithmetic.characterExclusionCost_mul_eq_add_sdiff χ
      b.squarefreePart_pos.ne' (pow_ne_zero 2 b.squareFactor_odd.pos.ne')
  rw [Nat.primeFactors_pow _ (by norm_num only : 2 ≠ 0), mul_comm b.squarefreePart,
    b.squarefreePart_sq_mul] at hsq
  have hcost :
    AnalyticNumberTheory.Arithmetic.characterExclusionCost χ n =
      Real.log b.squarefreePart + 2 * negativeSquareFactorCost b.squarefreePart b.squareFactor := by
    rw [hsq, primitiveQuadratic_ramified_cost b, primitiveQuadratic_negative_cost_exact b]
  have hdisj : Disjoint ({2} : Finset ℕ) n.primeFactors :=
    Finset.disjoint_singleton_left.mpr
      (fun hm ↦ hn.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hm))
  unfold AnalyticNumberTheory.Arithmetic.characterExclusionCost
  rw [Nat.primeFactors_mul (by norm_num only : 2 ≠ 0) hn.pos.ne', Nat.prime_two.primeFactors,
    Finset.sum_union hdisj, Finset.sum_singleton]
  change
    (1 - (χ 2).re) * Real.log 2 + AnalyticNumberTheory.Arithmetic.characterExclusionCost χ n = _
  rw [hcost]
  ring

/-- For the stated residue class of the canonical squarefree part modulo eight,
evaluate the actual primitive exclusion cost at 2n. Substitute the proved exact
value-at-two cost into the support identity; shared ramified support remains counted once. -/
theorem primitiveQuadratic_exclusion_mod_one {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns) (h8 : b.squarefreePart % 8 = 1) :
    AnalyticNumberTheory.Arithmetic.characterExclusionCost
        (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) =
      Real.log b.squarefreePart + 0 +
        2 * negativeSquareFactorCost b.squarefreePart b.squareFactor := by
  rw [primitiveQuadratic_exclusion_cost_exact b, (NumberTheory.quadratic_mod_eight_one_data b h8).2]

/-- For the stated residue class of the canonical squarefree part modulo eight,
evaluate the actual primitive exclusion cost at 2n. Substitute the proved exact
value-at-two cost into the support identity; shared ramified support remains counted once. -/
theorem primitiveQuadratic_exclusion_mod_five {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns) (h8 : b.squarefreePart % 8 = 5) :
    AnalyticNumberTheory.Arithmetic.characterExclusionCost
        (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) =
      Real.log b.squarefreePart + 2 * Real.log 2 +
        2 * negativeSquareFactorCost b.squarefreePart b.squareFactor := by
  rw [primitiveQuadratic_exclusion_cost_exact b,
    (NumberTheory.quadratic_mod_eight_five_data b h8).2]

/-- For the stated residue class of the canonical squarefree part modulo eight,
evaluate the actual primitive exclusion cost at 2n. Substitute the proved exact
value-at-two cost into the support identity; shared ramified support remains counted once. -/
theorem primitiveQuadratic_exclusion_mod_three_seven {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (h8 : b.squarefreePart % 8 = 3 ∨ b.squarefreePart % 8 = 7) :
    AnalyticNumberTheory.Arithmetic.characterExclusionCost
        (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) =
      Real.log b.squarefreePart + Real.log 2 +
        2 * negativeSquareFactorCost b.squarefreePart b.squareFactor := by
  rw [primitiveQuadratic_exclusion_cost_exact b,
    (NumberTheory.quadratic_mod_eight_three_seven b h8).2]

end PseudoPrime.PseudoSquare
