/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsPrimeData

/-! # Indexed prime supplies for the repeated-product envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Pairs of prime cutoff and certified prime count used by the indexed portion of the
repeated-product envelope. The list is independent of the counting degree. -/
def indexedSupplies : List (ℕ × ℕ) :=
  [(11, 5), (13, 6), (19, 8), (29, 10), (31, 11), (43, 14), (53, 16), (67, 19), (71, 20), (83, 23),
    (89, 24), (109, 29), (131, 32), (139, 34), (151, 36), (191, 43), (199, 46), (211, 47),
    (257, 55), (263, 56), (331, 67), (353, 71), (389, 77), (401, 79), (541, 100), (577, 106),
    (653, 119), (701, 126), (709, 127), (797, 139), (863, 150), (919, 157), (967, 163), (1103, 185)]

/-- Each indexed cutoff has the recorded supply of primes. Existing prime-index certificates
prove the entries through 967, and the explicit prime-count result proves the last entry.
This shared supply certificate can be reused by all degrees for each cutoff. -/
theorem indexedSupplies_sound : ∀ x ∈ indexedSupplies, x.2 ≤ x.1.primeCounting := by
  simp only [indexedSupplies, List.forall_mem_cons]
  exact
    ⟨(primeCount_ge_of_index (i := 4) (B := 11) (by rw [NumberTheory.primeByIndex_four])),
      (primeCount_ge_of_index (i := 5) (B := 13) (by rw [NumberTheory.primeByIndex_five])),
      (primeCount_ge_of_index (i := 7) (B := 19) (by rw [NumberTheory.primeByIndex_at_7])),
      (primeCount_ge_of_index (i := 9) (B := 29) (by rw [NumberTheory.primeByIndex_at_9])),
      (primeCount_ge_of_index (i := 10) (B := 31) (by rw [NumberTheory.primeByIndex_at_10])),
      (primeCount_ge_of_index (i := 13) (B := 43) (by rw [NumberTheory.primeByIndex_at_13])),
      (primeCount_ge_of_index (i := 15) (B := 53) (by rw [NumberTheory.primeByIndex_at_15])),
      (primeCount_ge_of_index (i := 18) (B := 67) (by rw [NumberTheory.primeByIndex_at_18])),
      (primeCount_ge_of_index (i := 19) (B := 71) (by rw [NumberTheory.primeByIndex_at_19])),
      (primeCount_ge_of_index (i := 22) (B := 83) (by rw [NumberTheory.primeByIndex_at_22])),
      (primeCount_ge_of_index (i := 23) (B := 89) (by rw [NumberTheory.primeByIndex_at_23])),
      (primeCount_ge_of_index (i := 28) (B := 109) (by rw [NumberTheory.primeByIndex_at_28])),
      (primeCount_ge_of_index (i := 31) (B := 131) (by rw [NumberTheory.primeByIndex_at_31])),
      (primeCount_ge_of_index (i := 33) (B := 139) (by rw [NumberTheory.primeByIndex_at_33])),
      (primeCount_ge_of_index (i := 35) (B := 151) (by rw [NumberTheory.primeByIndex_at_35])),
      (primeCount_ge_of_index (i := 42) (B := 191) (by rw [NumberTheory.primeByIndex_at_42])),
      (primeCount_ge_of_index (i := 45) (B := 199) (by rw [NumberTheory.primeByIndex_at_45])),
      (primeCount_ge_of_index (i := 46) (B := 211) (by rw [NumberTheory.primeByIndex_at_46])),
      (primeCount_ge_of_index (i := 54) (B := 257) (by rw [NumberTheory.primeByIndex_at_54])),
      (primeCount_ge_of_index (i := 55) (B := 263) (by rw [NumberTheory.primeByIndex_at_55])),
      (primeCount_ge_of_index (i := 66) (B := 331) (by rw [NumberTheory.primeByIndex_at_66])),
      (primeCount_ge_of_index (i := 70) (B := 353) (by rw [NumberTheory.primeByIndex_at_70])),
      (primeCount_ge_of_index (i := 76) (B := 389) (by rw [NumberTheory.primeByIndex_at_76])),
      (primeCount_ge_of_index (i := 78) (B := 401) (by rw [NumberTheory.primeByIndex_at_78])),
      (primeCount_ge_of_index (i := 99) (B := 541) (by rw [NumberTheory.primeByIndex_at_99])),
      (primeCount_ge_of_index (i := 105) (B := 577) (by rw [NumberTheory.primeByIndex_at_105])),
      (primeCount_ge_of_index (i := 118) (B := 653) (by rw [NumberTheory.primeByIndex_at_118])),
      (primeCount_ge_of_index (i := 125) (B := 701) (by rw [NumberTheory.primeByIndex_at_125])),
      (primeCount_ge_of_index (i := 126) (B := 709) (by rw [NumberTheory.primeByIndex_at_126])),
      (primeCount_ge_of_index (i := 138) (B := 797) (by rw [NumberTheory.primeByIndex_at_138])),
      (primeCount_ge_of_index (i := 149) (B := 863) (by rw [NumberTheory.primeByIndex_at_149])),
      (primeCount_ge_of_index (i := 156) (B := 919) (by rw [NumberTheory.primeByIndex_at_156])),
      (primeCount_ge_of_index (i := 162) (B := 967) (by rw [NumberTheory.primeByIndex_at_162])),
      primeCount_1103_ge_185, by
      intro x hx; exact (List.not_mem_nil hx).elim⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
