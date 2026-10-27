/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.JacobiCharacterArithmetic

/-! # Exact squarefree reduction of non-one odd-prime Jacobi witnesses -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For an odd nonsquare arithmetic decomposition, the non-one odd-prime
witness set is exactly the union of odd prime divisors of n and the squarefree
part's witness set. On primes not dividing n, the square factor is invisible.
This identifies the full witness set before taking a minimum. -/
theorem primeNeOneWitnessSet_eq_divisor_union_squarefree {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) :
    primeNeOneWitnessSet n =
      {p : ℕ | p.Prime ∧ Odd p ∧ p ∣ n} ∪ primeNeOneWitnessSet bridge.squarefreePart := by
  ext p
  constructor
  · intro hp
    by_cases hd : p ∣ n
    · exact Or.inl ⟨hp.1, hp.2.1, hd⟩
    · apply Or.inr
      have hc := (hp.1.coprime_iff_not_dvd.mpr hd).symm
      have he := jacobiSym_eq_squarefreePart_of_coprime bridge hc
      exact ⟨hp.1, hp.2.1, fun h ↦ hp.2.2 (he.trans h)⟩
  · rintro (hp | hp)
    · exact primeNeOneWitness_mem_of_dvd hp.1 hp.2.1 hp.2.2
    · exact primeNeOneWitness_mem_of_squarefreePart_mem bridge hp

/-- The least non-one odd-prime witness equals the minimum of the least
prime divisor of n and the least witness for its squarefree part. Both witness
sets are assumed nonempty, with no analytic hypothesis. Use the exact union
identity and the least-prime-divisor property. This is an arithmetic equality. -/
theorem primeNeOneWitness_eq_min_minFac_squarefree {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) (hw : (primeNeOneWitnessSet n).Nonempty)
    (hd : (primeNeOneWitnessSet bridge.squarefreePart).Nonempty) :
    primeNeOneWitness n hw = min n.minFac (primeNeOneWitness bridge.squarefreePart hd) := by
  have hn1 : n ≠ 1 := by
    intro h
    apply hns
    exact ⟨1, by rw [h, mul_one]⟩
  have hp := Nat.minFac_prime hn1
  have ho := hp.odd_of_ne_two (hn.ne_two_of_dvd_nat (Nat.minFac_dvd n))
  apply Nat.le_antisymm
  · apply le_min
    · exact primeNeOneWitness_le n hw (primeNeOneWitness_mem_of_dvd hp ho (Nat.minFac_dvd n))
    · exact primeNeOneWitness_le_of_squarefreePart bridge
  · have hm := primeNeOneWitness_mem n hw
    rw [primeNeOneWitnessSet_eq_divisor_union_squarefree bridge] at hm
    rcases hm with hm | hm
    · exact (min_le_left _ _).trans (Nat.minFac_le_of_dvd hm.1.two_le hm.2.2)
    · exact (min_le_right _ _).trans (primeNeOneWitness_le _ hd hm)

/-- The squarefree part in an odd nonsquare decomposition cannot be a
square. A square root would multiply by the removed square factor to give a
square root of the original input. This discharges the reduced witness domain. -/
theorem JacobiCharacterArithmeticData.squarefreePart_not_isSquare {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns) :
    ¬IsSquare bridge.squarefreePart := by
  rintro ⟨k, hk⟩
  apply hns
  refine ⟨bridge.squareFactor * k, ?_⟩
  calc
    n = bridge.squareFactor ^ 2 * bridge.squarefreePart := bridge.squarefreePart_sq_mul.symm
    _ = bridge.squareFactor * k * (bridge.squareFactor * k) := by
      rw [hk]; ring

end PseudoPrime.NumberTheory
