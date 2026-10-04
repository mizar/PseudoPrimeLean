/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Selfridge.MethodAStarEquivalence
import PseudoPrime.PrimeTest.BPSW.PaperSpec

/-! # Selfridge discriminant equality and ordinary Method A/A* list equivalence -/

namespace PseudoPrime.PrimeTest

/-- At an even index, Method A and A* have identical U zero conditions if five is a unit.
Cast the integer identity and cancel its unit power; composite moduli are allowed. -/
theorem lucasU_methodAStar_even_zero {n m : ℕ} (hu : IsUnit ((5 : ℤ) : ZMod n)) :
    lucasUZMod n 5 5 (2 * m) = 0 ↔ lucasUZMod n 1 (-1) (2 * m) = 0 := by
  have he := congrArg (fun z : ℤ ↦ (z : ZMod n)) (lucasU_methodAStar_even m)
  simp only [Int.cast_mul, Int.cast_pow] at he
  change (lucasU 5 5 (2 * m) : ZMod n) = 0 ↔ (lucasU 1 (-1) (2 * m) : ZMod n) = 0
  rw [he]
  exact (hu.pow m).mul_right_eq_zero

/-- For odd inputs selecting D = 5 with Jacobi minus one, the ordinary Lucas tests agree.
The index n + 1 is even and the discriminant Jacobi value makes five a unit. -/
theorem lucas_methodAStar_five_iff {n : ℕ} (ho : Odd n) (hj : jacobiSym 5 n = -1) :
    lucasUZMod n 5 5 (lucasProbablePrimeIndex n 5) = 0 ↔
      lucasUZMod n 1 (-1) (lucasProbablePrimeIndex n 5) = 0 := by
  obtain ⟨m, hm⟩ := ho.add_one
  rw [lucasProbablePrimeIndex_of_jacobi_eq_neg_one hj, hm]
  simpa only [two_mul] using
    lucasU_methodAStar_even_zero (m := m) (lucasDiscriminant_isUnit_of_jacobi_neg_one hj)

/-- Method A and A* have the same ordinary Lucas acceptance for odd inputs with Jacobi minus one.
Use the even-index identity at D = 5; all other parameters are identical. -/
theorem isLucas_methodAStar_iff {n : ℕ} (ho : Odd n) {D : ℤ} (hm : (1 - D) % 4 = 0)
    (hj : jacobiSym D n = -1) :
    IsLucasProbablePrime n (LucasParams.methodAStar D hm) ↔
      IsLucasProbablePrime n (LucasParams.methodA D hm) := by
  by_cases hd : D = 5
  · subst D
    change
      lucasUZMod n 5 5 (lucasProbablePrimeIndex n 5) = 0 ↔
        lucasUZMod n 1 ((1 - 5) / 4) (lucasProbablePrimeIndex n 5) = 0
    exact lucas_methodAStar_five_iff ho hj
  · rw [LucasParams.methodAStar_eq_methodA_of_ne_five hm hd]

/-- The factor-detecting classical and Wheel30 scans have exactly the same signed discriminant
on odd nonsquares. Transport their least-stop equality through the Selfridge sign rule. -/
theorem firstStopD_wheel30_eq_classical {n : ℕ} (ho : Odd n) (hns : ¬IsSquare n)
    (hc : (FirstStopNeOneSet isClassicalCandidate n).Nonempty)
    (hw : (FirstStopNeOneSet isWheel30NeOneCandidate n).Nonempty) :
    selfridgeD (firstStopNeOne isWheel30NeOneCandidate n hw) =
      selfridgeD (firstStopNeOne isClassicalCandidate n hc) := by
  exact congrArg selfridgeD (firstStopNeOne_wheel30_eq_classical ho.pos ho hns hc hw)

/-- The executable ordinary Lucas checks agree between Method A and A* on valid selected inputs.
Transport the zero-condition equivalence through the fast evaluator and Boolean test. -/
theorem lucasWithParams_methodAStar_eq {n : ℕ} (ho : Odd n) {D : ℤ} (hm : (1 - D) % 4 = 0)
    (hj : jacobiSym D n = -1) :
    lucasWithParams n (LucasParams.methodAStar D hm).D (LucasParams.methodAStar D hm).P
        (LucasParams.methodAStar D hm).Q =
      lucasWithParams n (LucasParams.methodA D hm).D (LucasParams.methodA D hm).P
        (LucasParams.methodA D hm).Q := by
  apply Bool.eq_iff_iff.mpr
  simpa only [lucasWithParams, lucasUZModFast_eq_lucasUZMod, decide_eq_true_eq,
    IsLucasProbablePrime] using isLucas_methodAStar_iff ho hm hj

/-- Method A and A* accept the same composite inputs as Lucas probable primes for valid selections.
Retain the nonprime condition while transporting the ordinary Lucas acceptance equivalence. -/
theorem methodA_lpsp_iff {n : ℕ} (ho : Odd n) {D : ℤ} (hm : (1 - D) % 4 = 0)
    (hj : jacobiSym D n = -1) :
    (¬n.Prime ∧ IsLucasProbablePrime n (LucasParams.methodAStar D hm)) ↔
      (¬n.Prime ∧ IsLucasProbablePrime n (LucasParams.methodA D hm)) := by
  exact and_congr Iff.rfl (isLucas_methodAStar_iff ho hm hj)

/-- For any admissible discriminant selection, the sets of ordinary Lucas pseudoprimes agree
between A and A*. Restrict to odd inputs selecting Jacobi minus one and retain nonprimality.
This set equality represents equality of the lpsp lists at every finite enumeration bound. -/
theorem methodA_lpsp_sets_eq (D : ℕ → ℤ) (hm : ∀ n, (1 - D n) % 4 = 0) :
    {n : ℕ |
        Odd n ∧
          jacobiSym (D n) n = -1 ∧
          ¬n.Prime ∧ IsLucasProbablePrime n (LucasParams.methodAStar (D n) (hm n))} =
      {n : ℕ |
        Odd n ∧
          jacobiSym (D n) n = -1 ∧
          ¬n.Prime ∧ IsLucasProbablePrime n (LucasParams.methodA (D n) (hm n))} := by
  apply Set.ext
  intro n
  exact
    ⟨fun h ↦ ⟨h.1, h.2.1, (methodA_lpsp_iff h.1 (hm n) h.2.1).mp h.2.2⟩, fun h ↦
      ⟨h.1, h.2.1, (methodA_lpsp_iff h.1 (hm n) h.2.1).mpr h.2.2⟩⟩

end PseudoPrime.PrimeTest
