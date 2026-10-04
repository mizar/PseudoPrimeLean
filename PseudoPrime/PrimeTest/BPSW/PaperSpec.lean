/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.BPSW.Wheel30

/-! # Independent BFW Section 6 specification and all-input execution equality -/

namespace PseudoPrime.PrimeTest

/-- The paper's Strong Lucas, terminal V, and multiplied Euler conditions.
Use sequence values and ordinary powers, independently of the shared execution state. -/
def BFWLucasConditions (n : ℕ) (param : LucasParams) : Prop :=
  IsStrongLucasProbablePrime n param ∧
    lucasVZMod n param.P param.Q (n + 1) = 2 * (param.Q : ZMod n) ∧
    (param.Q : ZMod n) ^ ((n + 1) / 2) = (param.Q : ZMod n) * (jacobiSym param.Q n : ZMod n)

/-- Valid Jacobi -1 parameters identify the shared evaluator with the paper's Lucas conditions.
The Strong, V, and half-index Q invariants transport each comparison separately. -/
theorem bfwLucas_iff (n : ℕ) (hn : Odd n) (param : LucasParams) (hj : jacobiSym param.D n = -1) :
    strengthenedLucasSharedEulerValid n param = true ↔ BFWLucasConditions n param := by
  have hs := strongLucasWithParams_eq_true_iff n param.D param.P param.Q param.discr
  have hq :=
    lucasStrengthenedState_qk n hn param.D param.P param.Q
      (strongLucasTwoAdicExponent_pos n hn param.D hj)
  simp only [lucasProbablePrimeIndex_of_jacobi_eq_neg_one hj, lucasQPow, Int.cast_pow] at hq
  simp only [strengthenedLucasSharedEulerValid, hn, hj, and_self, ↓reduceIte, Bool.and_eq_true,
    beq_iff_eq, lucasStrengthenedState_strong n hn, lucasStrengthenedState_v n hn,
    lucasProbablePrimeIndex_of_jacobi_eq_neg_one hj, hq, hs, BFWLucasConditions,
    LucasParams.ofDiscriminant]

/-- Unconditional fuel returns the classical first factor-detecting stopping magnitude.
Termination, scan minimality, and Wheel30/classical equality remove the executable search. -/
theorem bfwScan_some {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hc : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) :
    selfridgeNeOneJump n 5 (2 * n) = some (firstStopNeOne isClassicalCandidate n hc) := by
  have hw := wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (selfridgeNeOneScan_total hn hns)
  have he := selfridgeNeOneScan_firstStop hi hw
  rw [selfridgeNeOneJump_eq, hi, he, firstStopNeOne_wheel30_eq_classical hn.pos hn hns hc hw]

/-- Method A* parameters at the least classical factor-detecting stop.
D=5 gives P=Q=5; otherwise P=1 and Q=(1-D)/4. Used by the independent paper specification. -/
noncomputable def BFWParams (n : ℕ) (hc : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) :
    LucasParams :=
  LucasParams.methodAStar (selfridgeD (firstStopNeOne isClassicalCandidate n hc))
    (selfridgeD_methodA_mod_four (firstStopNeOne_mem _ _ hc).1.2)

/-- Accept a classical first stop only if its Jacobi value is -1 and all Lucas checks pass.
A Jacobi-zero factor stop rejects without selecting a later discriminant. -/
def BFWSelectedConditions (n : ℕ) (hc : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) :
    Prop :=
  jacobiSym (selfridgeD (firstStopNeOne isClassicalCandidate n hc)) n = -1 ∧
    BFWLucasConditions n (BFWParams n hc)

/-- On odd nonsquares, certified classification matches the independent paper selection.
A common classification congruence preserves the first stop; factor results reject. -/
theorem bfwAccepted_iff {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hc : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) :
    (selfridgeNeOneResult n (2 * n)).accepted true = true ↔ BFWSelectedConditions n hc := by
  have hi := bfwScan_some hn hns hc
  have he :=
    selfridgeNeOneClassify_congr n _ _ (fun _ h ↦ selfridgeNeOneJump_sound h)
      (fun _ h ↦ selfridgeNeOneJump_sound (hi.trans h)) hi
  rw [selfridgeNeOneResult, he]
  by_cases hj : jacobiSym (selfridgeD (firstStopNeOne isClassicalCandidate n hc)) n = -1
  · have hd : (BFWParams n hc).D = selfridgeD (firstStopNeOne isClassicalCandidate n hc) := by
      dsimp only [BFWParams, LucasParams.methodAStar]
      split <;> rfl
    simp only [selfridgeNeOneClassify, hn.pos, ↓reduceDIte, hj, SelfridgeScanResult.accepted,
      ↓reduceIte, BFWSelectedConditions, true_and]
    exact bfwLucas_iff n hn (BFWParams n hc) (hd.symm ▸ hj)
  · simp only [selfridgeNeOneClassify, hn.pos, ↓reduceDIte, hj, SelfridgeScanResult.accepted,
      Bool.false_eq_true, BFWSelectedConditions, false_and]

/-- The paper's five-stage acceptance, extended to every natural input.
Small inputs use the conventional answers; even numbers and squares reject.
Odd nonsquares use base-2 Strong MR and the least classical stop with Method A* and Lucas checks. -/
def BFWPass (n : ℕ) : Prop :=
  if n < 2 then False
  else
    if n = 2 then True
    else
      if hn : Odd n then
        if hns : ¬IsSquare n then
          IsStrongMillerRabinProbablePrime n 2 ∧
            BFWSelectedConditions n (classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns)
        else False
      else False

/-- On the odd nonsquare branch, MR and the classical selected conditions describe acceptance.
Boolean conjunction separates the MR comparison from the independently specified Lucas checks. -/
theorem bfwOddNonsquare_iff {n : ℕ} (hl : ¬n < 2) (ht : n ≠ 2) (hn : Odd n) (hns : ¬IsSquare n) :
    strengthenedBPSWWheel30 n = true ↔ BFWPass n := by
  have he := Nat.not_even_iff_odd.mpr hn
  have hc := classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  simp only [strengthenedBPSWWheel30, bpswWheel30, BFWPass, hl, ht, hn, he, hns, ↓reduceIte,
    ↓reduceDIte, natIsSquare_false_of_not_isSquare hns, Bool.false_eq_true, not_false_eq_true]
  have hx :
    (if strongMillerRabinWithBaseLoop n 2 then (selfridgeNeOneResult n (2 * n)).accepted true
      else false) =
      (strongMillerRabinWithBaseLoop n 2 && (selfridgeNeOneResult n (2 * n)).accepted true) := by
    cases strongMillerRabinWithBaseLoop n 2 <;> rfl
  rw [hx, Bool.and_eq_true, strongMillerRabinWithBaseLoop_eq, strongMillerRabinWithBase_eq_true_iff,
    bfwAccepted_iff hn hns hc]

/-- Square inputs satisfy the executable square predicate.
Represent the square by a natural root and use the exact square-root identity. -/
theorem bfwSquare_precheck {n : ℕ} (hsquare : IsSquare n) : natIsSquare n = true := by
  obtain ⟨k, hk⟩ := (isSquare_iff_exists_sq n).mp hsquare
  simp only [natIsSquare, hk, Nat.sqrt_eq', beq_self_eq_true]

/-- Odd squares above the small-input exceptions reject in both specifications.
The MR-first order does not alter the rejected Boolean result. -/
theorem bfwOddSquare_iff {n : ℕ} (hl : ¬n < 2) (ht : n ≠ 2) (hn : Odd n) (hsquare : IsSquare n) :
    strengthenedBPSWWheel30 n = true ↔ BFWPass n := by
  have he := Nat.not_even_iff_odd.mpr hn
  have hns : ¬¬IsSquare n := fun h ↦ h hsquare
  simp only [strengthenedBPSWWheel30, bpswWheel30, BFWPass, hl, ht, hn, he, hns, ↓reduceIte,
    ↓reduceDIte, bfwSquare_precheck hsquare]
  split <;> simp only [Bool.false_eq_true]

/-- For every natural input, the executable strengthened Wheel30 entry accepts exactly BFWPass.
Precheck cases reduce directly; the odd nonsquare case uses independent MR and selection bridges. -/
theorem strengthenedBPSWWheel30_iff_bfw (n : ℕ) : strengthenedBPSWWheel30 n = true ↔ BFWPass n := by
  by_cases hl : n < 2
  · simp only [strengthenedBPSWWheel30, bpswWheel30, BFWPass, hl, ↓reduceIte, Bool.false_eq_true]
  · by_cases ht : n = 2
    · subst n
      simp only [strengthenedBPSWWheel30, bpswWheel30, BFWPass, Nat.lt_irrefl, ↓reduceIte]
    · by_cases hn : Odd n
      · by_cases hns : ¬IsSquare n
        · exact bfwOddNonsquare_iff hl ht hn hns
        · exact bfwOddSquare_iff hl ht hn (Classical.not_not.mp hns)
      · have he := Nat.not_odd_iff_even.mp hn
        simp only [strengthenedBPSWWheel30, bpswWheel30, BFWPass, hl, ht, hn, he, ↓reduceIte,
          ↓reduceDIte, Bool.false_eq_true]

/-- The Boolean form of the independent all-input paper specification.
Classical decision makes this a proof-side specification, not an additional executable evaluator. -/
noncomputable def bfwEnhancedBPSW (n : ℕ) : Bool := by classical exact decide (BFWPass n)

/-- The executable and independent paper Booleans agree on every natural input.
Boolean extensionality converts the acceptance equivalence into exact result equality. -/
theorem strengthenedBPSWWheel30_eq_bfw (n : ℕ) : strengthenedBPSWWheel30 n = bfwEnhancedBPSW n := by
  apply Bool.eq_iff_iff.mpr
  simp only [bfwEnhancedBPSW, decide_eq_true_eq, strengthenedBPSWWheel30_iff_bfw]

/-- The paper specification inherits unconditional prime completeness and basic-input behavior.
Transport the existing public contract through all-input Boolean equality. -/
theorem bfwEnhancedBPSW_spec : PrimalityTestSpec bfwEnhancedBPSW := by
  rw [← funext strengthenedBPSWWheel30_eq_bfw]
  exact strengthenedBPSWWheel30_spec

/-- Every prime satisfies the extended paper specification.
Executable prime acceptance and the five-stage bridge provide the proof. -/
theorem bfwPass_of_prime {n : ℕ} (hp : n.Prime) : BFWPass n :=
  (strengthenedBPSWWheel30_iff_bfw n).mp (bpswWheel30_of_prime hp true)

/-- Failure of the extended paper specification certifies non-primality.
Prime completeness gives the contrapositive; acceptance alone does not certify primality. -/
theorem not_prime_of_not_bfwPass {n : ℕ} (h : ¬BFWPass n) : ¬n.Prime := fun hp ↦
  h (bfwPass_of_prime hp)

end PseudoPrime.PrimeTest
