/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Kronecker.Computation
public import PseudoPrime.NumberTheory.Jacobi.GcdFast

/-! # Fuel-free Kronecker symbol and gcd execution -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Shared computation after excluding zero inputs.
Each absolute input is decomposed once into its two-adic exponent and odd quotient.
The odd kernel terminates by decreasing its numerator, without computing a fuel budget.
The common two-power is restored after completing the shared trajectory.
The optional correction repeats the factor at two for natural-Jacobi compatibility. -/
def kroneckerGcdNonzeroFast (a n : ℤ) (jacobiCorrection : Bool := false) : ℤ × ℕ :=
  let (ea, da) := Nat.maxPowDvdDiv 2 a.natAbs
  let (en, dn) := Nat.maxPowDvdDiv 2 n.natAbs
  let s := kroneckerNormalizationSign a n ea en dn
  let r := da % dn
  let out := Jacobi.Gcd.runFast ⟨dn, r, s⟩
  (if jacobiCorrection then kroneckerTwoPowerFactor a en * out.1 else out.1, 2 ^ min ea en * out.2)

/-- Executable Kronecker symbol and exact gcd for every integer input.
Zero inputs return the specified boundary pair directly. Nonzero inputs share one
odd-part Euclidean trajectory, including when the accumulated symbol coefficient is zero. -/
def kroneckerGcdFast (a n : ℤ) : ℤ × ℕ :=
  if n = 0 then (if a.natAbs = 1 then 1 else 0, a.natAbs)
  else if a = 0 then (if n.natAbs = 1 then 1 else 0, n.natAbs) else kroneckerGcdNonzeroFast a n

/-- The nonzero-input execution returns the independent symbol specification and exact gcd.
Fuel-free normalized correctness identifies the shared output; the two normalization identities
restore the original signs and common two-power. No executable Jacobi or gcd fallback is used. -/
theorem kroneckerGcdNonzeroFast_spec (a n : ℤ) (ha : a ≠ 0) (hn : n ≠ 0) :
    kroneckerGcdNonzeroFast a n = (kroneckerSym a n, Nat.gcd a.natAbs n.natAbs) := by
  simp only [kroneckerGcdNonzeroFast, Nat.fst_maxPowDvdDiv, Nat.snd_maxPowDvdDiv]
  rw [Jacobi.Gcd.runFast_normalized _ _ _
      (Nat.odd_iff.mpr (TwoAdic.oddPart_odd n.natAbs (Int.natAbs_ne_zero.mpr hn)))]
  exact Prod.ext (kroneckerSym_two_adic a n hn).symm (TwoAdic.gcd_natAbs_two_adic a n ha hn).symm

/-- Every integer input returns the Kronecker symbol and exact absolute-input gcd.
The two zero-input branches use the specification's boundary identities; nonzero inputs
use the shared odd kernel and exact two-adic restoration. -/
theorem kroneckerGcdFast_spec (a n : ℤ) :
    kroneckerGcdFast a n = (kroneckerSym a n, Nat.gcd a.natAbs n.natAbs) := by
  exact
    if hn : n = 0 then
      (show _ by
        subst n
        simp only [kroneckerGcdFast, ite_true, kroneckerSym_zero_right, Int.natAbs_zero,
          Nat.gcd_zero_right])
    else
      if ha : a = 0 then
        (show _ by
          subst a
          simp only [kroneckerGcdFast, hn, ite_false, ite_true, kroneckerSym_zero_left n hn,
            Int.natAbs_zero, Nat.gcd_zero_left])
      else
        (show _ by
          rw [kroneckerGcdFast, ite_eq_right hn, ite_eq_right ha]
          exact kroneckerGcdNonzeroFast_spec a n ha hn)

/-- The first executable component is the independent Kronecker symbol specification.
Project the simultaneous correctness theorem; this supplies symbol-only consumers. -/
theorem kroneckerGcdFast_fst (a n : ℤ) : (kroneckerGcdFast a n).1 = kroneckerSym a n := by
  exact congrArg Prod.fst (kroneckerGcdFast_spec a n)

/-- The second executable component is the exact gcd of the absolute integer inputs.
Project the simultaneous correctness theorem; no additional gcd computation is required. -/
theorem kroneckerGcdFast_snd (a n : ℤ) : (kroneckerGcdFast a n).2 = Nat.gcd a.natAbs n.natAbs := by
  exact congrArg Prod.snd (kroneckerGcdFast_spec a n)

/-- With the natural-Jacobi correction enabled, the same trajectory returns a corrected symbol.
The correction reuses the denominator exponent already extracted by the shared procedure.
Both components still come from one trajectory, with no repeated maximal-power decomposition. -/
theorem kroneckerGcdNonzeroFast_corrected_spec (a n : ℤ) (ha : a ≠ 0) (hn : n ≠ 0) :
    kroneckerGcdNonzeroFast a n true =
      (kroneckerTwoPowerFactor a (padicValNat 2 n.natAbs) * kroneckerSym a n,
        Nat.gcd a.natAbs n.natAbs) := by
  simp only [kroneckerGcdNonzeroFast, Nat.fst_maxPowDvdDiv, Nat.snd_maxPowDvdDiv]
  rw [Jacobi.Gcd.runFast_normalized _ _ _
      (Nat.odd_iff.mpr (TwoAdic.oddPart_odd n.natAbs (Int.natAbs_ne_zero.mpr hn)))]
  exact
    Prod.ext
      (congrArg (fun z ↦ kroneckerTwoPowerFactor a (padicValNat 2 n.natAbs) * z)
        (kroneckerSym_two_adic a n hn).symm)
      (TwoAdic.gcd_natAbs_two_adic a n ha hn).symm

/-- Fuel-free and fuel-based integer entries agree for all inputs.
Both return the same independent symbol specification and exact gcd.
This allows callers to choose either execution strategy without changing their result. -/
theorem kroneckerGcdFast_eq (a n : ℤ) : kroneckerGcdFast a n = kroneckerGcd a n := by
  exact (kroneckerGcdFast_spec a n).trans (kroneckerGcd_spec a n).symm

end PseudoPrime.NumberTheory
