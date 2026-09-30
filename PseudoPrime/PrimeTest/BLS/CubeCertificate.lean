/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.BLS.Cube

/-! # Cubic BLS certificate verification -/

namespace PseudoPrime.PrimeTest.BLS

/-- Data for the cube-root BLS branch, with a factored part of `n - 1` and an unresolved
cofactor. The checker validates the factors, witnesses, cubic bound, and arithmetic branch. -/
structure CubeCertificate where
  n : ℕ
  factorization : PartialFactorizationData
  witnesses : List (ℕ × ℕ)
  deriving DecidableEq, Repr

/-- Decide the cube-root certificate conditions. Failure means only that this certificate
does not establish primality. -/
def checkCubeCertificate (c : CubeCertificate) : Bool :=
  decide (1 < c.n) &&
    decide (c.n = factorProduct c.factorization.factors * c.factorization.cofactor + 1) &&
    decide (c.n < factorProduct c.factorization.factors ^ 3) &&
    checkPartialFactorization c.n c.factorization &&
    checkWitnesses c.n c.factorization c.witnesses &&
    (decide (cubeQuotient c.factorization.cofactor (factorProduct c.factorization.factors) = 0) ||
      decide
        (cubeDiscriminantIsSquare c.factorization.cofactor (factorProduct c.factorization.factors) =
          false))

/-- Mathematical meaning of a checked cube-root certificate. -/
def ValidCubeCertificate (c : CubeCertificate) : Prop :=
  1 < c.n ∧
    c.n = factorProduct c.factorization.factors * c.factorization.cofactor + 1 ∧
    c.n < factorProduct c.factorization.factors ^ 3 ∧
    ValidPartialFactorization c.n c.factorization ∧
    ValidWitnesses c.n c.factorization c.witnesses ∧
    (cubeQuotient c.factorization.cofactor (factorProduct c.factorization.factors) = 0 ∨
      cubeDiscriminantIsSquare c.factorization.cofactor (factorProduct c.factorization.factors) =
        false)

/-- The Boolean checker agrees with the mathematical certificate conditions. -/
theorem checkCubeCertificate_eq_true_iff (c : CubeCertificate) :
    checkCubeCertificate c = true ↔ ValidCubeCertificate c := by
  simp only [checkCubeCertificate, ValidCubeCertificate, ValidPartialFactorization, ValidWitnesses,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_assoc]

/-- Acceptance proves primality through the cube-root criterion, including its zero-quotient
branch; no square-root size bound is assumed. -/
theorem prime_of_valid_cube_certificate (c : CubeCertificate)
    (hcheck : checkCubeCertificate c = true) : Nat.Prime c.n := by
  rcases (checkCubeCertificate_eq_true_iff c).mp hcheck with
    ⟨hn, hdecomp, hbound, hfactor, hwitness, harithmetic⟩
  have hFpos : 0 < factorProduct c.factorization.factors :=
    Nat.zero_lt_of_lt (checkPartialFactorization_eq_true_iff c.n c.factorization |>.mp hfactor).1
  have hlarge :=
    primeDivisorsAbove_of_valid_bls_data hn c.factorization c.witnesses hfactor hwitness
  exact
    (prime_iff_cubeDiscriminantIsSquare_false_or_quotient_zero_of_primeDivisorsAbove hn hFpos
          hdecomp hbound hlarge).2
      harithmetic

end PseudoPrime.PrimeTest.BLS
