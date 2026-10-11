/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Kronecker.Properties
public import PseudoPrime.NumberTheory.Jacobi.Gcd

/-! # Simultaneous Kronecker symbol and gcd computation on integer inputs -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- The Fibonacci round budget selected by the integer entry point.
Zero inputs require no kernel rounds; otherwise take the odd numerator modulo the odd denominator.
This standalone budget query repeats normalization; the shared execution path does not call it. -/
def kroneckerFuel (a n : ℤ) : ℕ :=
  if a = 0 ∨ n = 0 then 0
  else Euclid.stepBound (Nat.divMaxPow a.natAbs 2 % Nat.divMaxPow n.natAbs 2)

/-- Shared computation after excluding zero inputs.
Each absolute input is decomposed once into its two-adic exponent and odd quotient.
The initial remainder is shared by fuel selection and the starting state.
The odd kernel uses its certified Fibonacci budget, then restores the common two-power.
The optional correction repeats the factor at two for natural-Jacobi compatibility.
The default pair only represents an unreachable exhausted result; it invokes no fallback. -/
def kroneckerGcdNonzero (a n : ℤ) (jacobiCorrection : Bool := false) : ℤ × ℕ :=
  let (ea, da) := Nat.maxPowDvdDiv 2 a.natAbs
  let (en, dn) := Nat.maxPowDvdDiv 2 n.natAbs
  let s := kroneckerNormalizationSign a n ea en dn
  let r := da % dn
  let out := (Jacobi.Gcd.runFuel (Euclid.stepBound r) ⟨dn, r, s⟩).getD (0, 0)
  (if jacobiCorrection then kroneckerTwoPowerFactor a en * out.1 else out.1, 2 ^ min ea en * out.2)

/-- Executable Kronecker symbol and exact gcd for every integer input.
Zero inputs return the specified boundary pair directly. Nonzero inputs share one
odd-part Euclidean trajectory, including when the accumulated symbol coefficient is zero. -/
def kroneckerGcd (a n : ℤ) : ℤ × ℕ :=
  if n = 0 then (if a.natAbs = 1 then 1 else 0, a.natAbs)
  else if a = 0 then (if n.natAbs = 1 then 1 else 0, n.natAbs) else kroneckerGcdNonzero a n

/-- The nonzero-input execution returns the independent symbol specification and exact gcd.
Sufficient normalized fuel identifies the shared output; the two normalization identities
restore the original signs and common two-power. No executable Jacobi or gcd fallback is used. -/
theorem kroneckerGcdNonzero_spec (a n : ℤ) (ha : a ≠ 0) (hn : n ≠ 0) :
    kroneckerGcdNonzero a n = (kroneckerSym a n, Nat.gcd a.natAbs n.natAbs) := by
  simp only [kroneckerGcdNonzero, Nat.fst_maxPowDvdDiv, Nat.snd_maxPowDvdDiv]
  rw [Jacobi.Gcd.runFuel_normalized _ _ _
      (Nat.odd_iff.mpr (TwoAdic.oddPart_odd n.natAbs (Int.natAbs_ne_zero.mpr hn)))]
  simp only [Option.getD_some]
  exact Prod.ext (kroneckerSym_two_adic a n hn).symm (TwoAdic.gcd_natAbs_two_adic a n ha hn).symm

/-- Every integer input returns the Kronecker symbol and exact absolute-input gcd.
The two zero-input branches use the specification's boundary identities; nonzero inputs
use the shared odd kernel and exact two-adic restoration. -/
theorem kroneckerGcd_spec (a n : ℤ) :
    kroneckerGcd a n = (kroneckerSym a n, Nat.gcd a.natAbs n.natAbs) := by
  exact
    if hn : n = 0 then
      (show _ by
        subst n
        simp only [kroneckerGcd, ite_true, kroneckerSym_zero_right, Int.natAbs_zero,
          Nat.gcd_zero_right])
    else
      if ha : a = 0 then
        (show _ by
          subst a
          simp only [kroneckerGcd, hn, ite_false, ite_true, kroneckerSym_zero_left n hn,
            Int.natAbs_zero, Nat.gcd_zero_left])
      else
        (show _ by
          rw [kroneckerGcd, ite_eq_right hn, ite_eq_right ha]
          exact kroneckerGcdNonzero_spec a n ha hn)

/-- The first executable component is the independent Kronecker symbol specification.
Project the simultaneous correctness theorem; this supplies symbol-only consumers. -/
theorem kroneckerGcd_fst (a n : ℤ) : (kroneckerGcd a n).1 = kroneckerSym a n := by
  exact congrArg Prod.fst (kroneckerGcd_spec a n)

/-- The second executable component is the exact gcd of the absolute integer inputs.
Project the simultaneous correctness theorem; no additional gcd computation is required. -/
theorem kroneckerGcd_snd (a n : ℤ) : (kroneckerGcd a n).2 = Nat.gcd a.natAbs n.natAbs := by
  exact congrArg Prod.snd (kroneckerGcd_spec a n)

/-- With the natural-Jacobi correction enabled, the same trajectory returns a corrected symbol.
The correction reuses the denominator exponent already extracted by the shared procedure.
Both components still come from one trajectory, with no repeated maximal-power decomposition. -/
theorem kroneckerGcdNonzero_corrected_spec (a n : ℤ) (ha : a ≠ 0) (hn : n ≠ 0) :
    kroneckerGcdNonzero a n true =
      (kroneckerTwoPowerFactor a (padicValNat 2 n.natAbs) * kroneckerSym a n,
        Nat.gcd a.natAbs n.natAbs) := by
  simp only [kroneckerGcdNonzero, Nat.fst_maxPowDvdDiv, Nat.snd_maxPowDvdDiv]
  rw [Jacobi.Gcd.runFuel_normalized _ _ _
      (Nat.odd_iff.mpr (TwoAdic.oddPart_odd n.natAbs (Int.natAbs_ne_zero.mpr hn)))]
  simp only [Option.getD_some]
  exact
    Prod.ext
      (congrArg (fun z ↦ kroneckerTwoPowerFactor a (padicValNat 2 n.natAbs) * z)
        (kroneckerSym_two_adic a n hn).symm)
      (TwoAdic.gcd_natAbs_two_adic a n ha hn).symm

/-- The public integer budget obeys a denominator-only logarithmic upper bound.
Zero inputs use zero rounds; the positive odd denominator bounds the normalized remainder.
This controls batched rounds rather than total bit operations. -/
theorem kroneckerFuel_le_log2 (a n : ℤ) :
    kroneckerFuel a n ≤ 2 * (Nat.divMaxPow n.natAbs 2).log2 + 1 := by
  exact
    if hz : a = 0 ∨ n = 0 then
      (show _ by
        rw [kroneckerFuel, ite_eq_left hz]
        exact Nat.zero_le _)
    else
      (show _ by
        rw [kroneckerFuel, ite_eq_right hz]
        exact
          Jacobi.Gcd.normalizedFuel_le_log2 _ _
            (TwoAdic.oddPart_pos n.natAbs (Int.natAbs_ne_zero.mpr (fun hn ↦ hz (Or.inr hn)))))

/-- At an odd natural denominator, the executable first component is the Jacobi symbol.
Combine simultaneous correctness with the independent odd-denominator specification identity.
This preserves the established prime-test meaning on odd moduli. -/
theorem kroneckerGcd_eq_jacobiSym (a : ℤ) (n : ℕ) (hn : Odd n) :
    (kroneckerGcd a (n : ℤ)).1 = jacobiSym a n := by
  exact (kroneckerGcd_fst a (n : ℤ)).trans (kroneckerSym_eq_jacobiSym a n hn)

/-- A zero executable symbol is equivalent to a returned gcd different from one.
Both projections are exact, and the independent Kronecker zero criterion proves the equivalence.
No assumption excluding simultaneous zero inputs is needed. -/
theorem kroneckerGcd_zero_iff (a n : ℤ) : (kroneckerGcd a n).1 = 0 ↔ (kroneckerGcd a n).2 ≠ 1 := by
  rw [kroneckerGcd_fst, kroneckerGcd_snd]
  exact kroneckerSym_zero_iff a n

end PseudoPrime.NumberTheory
