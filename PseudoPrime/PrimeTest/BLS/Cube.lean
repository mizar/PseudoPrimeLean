/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.BLS.Basic
import Mathlib.Data.Int.Basic

/-!
# Arithmetic data for the cube-root BLS criterion

This module begins the cube-root branch by defining the Euclidean quotient, remainder, and
integer discriminant, and by proving the exact quotient-remainder decomposition used downstream.
-/

namespace PseudoPrime.PrimeTest.BLS

/-- Quotient of the BLS cofactor `R` by the certified factor product `F`. -/
def cubeQuotient (R F : ℕ) : ℕ := R / F

/-- Remainder of the BLS cofactor `R` modulo the certified factor product `F`. -/
def cubeRemainder (R F : ℕ) : ℕ := R % F

/-- Integer discriminant `(R mod F)^2 - 4 * (R / F)` for the cube-root criterion. -/
def cubeDiscriminant (R F : ℕ) : ℤ :=
  (cubeRemainder R F : ℤ) ^ 2 - 4 * (cubeQuotient R F : ℤ)

/-- Executable square test for the integer cube discriminant, using the natural square root.
The sign check is needed because `Int.toNat` maps negative values to zero. -/
def cubeDiscriminantIsSquare (R F : ℕ) : Bool :=
  let d := cubeDiscriminant R F
  decide (0 ≤ d) && decide (Nat.sqrt d.toNat ^ 2 = d.toNat)

/-- The square test accepts exactly when the integer discriminant has an integer square root. -/
theorem cubeDiscriminantIsSquare_eq_true_iff (R F : ℕ) :
    cubeDiscriminantIsSquare R F = true ↔ ∃ z : ℤ, cubeDiscriminant R F = z ^ 2 := by
  unfold cubeDiscriminantIsSquare
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hd, hroot⟩
    refine ⟨(Nat.sqrt (cubeDiscriminant R F).toNat : ℕ), ?_⟩
    calc
      cubeDiscriminant R F = ((cubeDiscriminant R F).toNat : ℤ) :=
        (Int.toNat_of_nonneg hd).symm
      _ = ((Nat.sqrt (cubeDiscriminant R F).toNat ^ 2 : ℕ) : ℤ) := by rw [hroot]
      _ = (Nat.sqrt (cubeDiscriminant R F).toNat : ℤ) ^ 2 := by
        rw [pow_two, Nat.cast_mul, pow_two]
  · rintro ⟨z, hz⟩
    have hd : 0 ≤ cubeDiscriminant R F := by
      rw [hz]
      exact Int.sq_nonneg z
    have hnat : (z ^ 2).toNat = z.natAbs ^ 2 := by
      have hsqnonneg : 0 ≤ z ^ 2 := Int.sq_nonneg z
      have hcast := (Int.toNat_of_nonneg hsqnonneg).trans
        (Int.natAbs_of_nonneg hsqnonneg).symm
      rw [Int.natAbs_pow] at hcast
      exact_mod_cast hcast
    have htoNat : (cubeDiscriminant R F).toNat = z.natAbs * z.natAbs := by
      calc
        (cubeDiscriminant R F).toNat = (z ^ 2).toNat := congrArg Int.toNat hz
        _ = z.natAbs ^ 2 := hnat
        _ = z.natAbs * z.natAbs := by rw [pow_two]
    refine ⟨hd, ?_⟩
    rw [htoNat, Nat.sqrt_eq, pow_two]

/-- The square test rejects exactly when the discriminant has no integer square root. -/
theorem cubeDiscriminantIsSquare_eq_false_iff (R F : ℕ) :
    cubeDiscriminantIsSquare R F = false ↔
      ∀ z : ℤ, cubeDiscriminant R F ≠ z ^ 2 := by
  constructor
  · intro hfalse z hz
    have htrue : cubeDiscriminantIsSquare R F = true :=
      (cubeDiscriminantIsSquare_eq_true_iff R F).2 ⟨z, hz⟩
    rw [hfalse] at htrue
    exact Bool.noConfusion htrue
  · intro hnsquare
    cases h : cubeDiscriminantIsSquare R F with
    | false => rfl
    | true =>
        obtain ⟨z, hz⟩ := (cubeDiscriminantIsSquare_eq_true_iff R F).1 h
        exact False.elim (hnsquare z hz)

/-- Return the nonnegative integer square root when the discriminant is a square.
The option is `none` exactly when the executable square test rejects. -/
def findCubeDiscriminantSquareRoot (R F : ℕ) : Option ℤ :=
  if cubeDiscriminantIsSquare R F then
    some (Nat.sqrt (cubeDiscriminant R F).toNat : ℤ)
  else
    none

/-- A returned discriminant root is a valid square-root certificate. -/
theorem findCubeDiscriminantSquareRoot_some_spec (R F : ℕ) (z : ℤ)
    (hfind : findCubeDiscriminantSquareRoot R F = some z) :
    cubeDiscriminant R F = z ^ 2 := by
  unfold findCubeDiscriminantSquareRoot at hfind
  split at hfind
  · injection hfind with hz
    subst z
    rename_i htest
    unfold cubeDiscriminantIsSquare at htest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
    rcases htest with ⟨hd, hroot⟩
    calc
      cubeDiscriminant R F = ((cubeDiscriminant R F).toNat : ℤ) :=
        (Int.toNat_of_nonneg hd).symm
      _ = ((Nat.sqrt (cubeDiscriminant R F).toNat ^ 2 : ℕ) : ℤ) := by rw [hroot]
      _ = (Nat.sqrt (cubeDiscriminant R F).toNat : ℤ) ^ 2 := by
        rw [pow_two, Nat.cast_mul, pow_two]
  · cases hfind

/-- The root search succeeds exactly when the discriminant square test accepts. -/
theorem findCubeDiscriminantSquareRoot_isSome_iff (R F : ℕ) :
    (findCubeDiscriminantSquareRoot R F).isSome = true ↔
      cubeDiscriminantIsSquare R F = true := by
  exact Option.isSome_ite

/-- The root-search `Option` is empty exactly when the executable square test rejects. This
equivalence does not require any quotient, size, or factorization hypotheses. -/
theorem findCubeDiscriminantSquareRoot_none_iff_square_false (R F : ℕ) :
    findCubeDiscriminantSquareRoot R F = none ↔
      cubeDiscriminantIsSquare R F = false := by
  constructor
  · intro hnone
    cases htest : cubeDiscriminantIsSquare R F with
    | false => rfl
    | true =>
        have hsome := (findCubeDiscriminantSquareRoot_isSome_iff R F).2 htest
        rw [hnone] at hsome
        exact Bool.noConfusion hsome
  · intro hfalse
    cases hroot : findCubeDiscriminantSquareRoot R F with
    | none => rfl
    | some z =>
        have hsome : (findCubeDiscriminantSquareRoot R F).isSome = true := by
          rw [hroot]
          rfl
        have htest := (findCubeDiscriminantSquareRoot_isSome_iff R F).1 hsome
        rw [hfalse] at htest
        exact Bool.noConfusion htest

/-- Executable check of a supplied integer square root for the cube discriminant.
This validates a certificate value; it does not search for a root. -/
def checkCubeDiscriminantSquareWitness (R F : ℕ) (z : ℤ) : Bool :=
  decide (cubeDiscriminant R F = z ^ 2)

/-- The square-root checker accepts exactly when its supplied integer is a root. -/
theorem checkCubeDiscriminantSquareWitness_eq_true_iff (R F : ℕ) (z : ℤ) :
    checkCubeDiscriminantSquareWitness R F z = true ↔ cubeDiscriminant R F = z ^ 2 := by
  simp only [checkCubeDiscriminantSquareWitness, decide_eq_true_eq]

/-- Euclidean division decomposes the cofactor into quotient and remainder. -/
theorem cubeQuotient_mul_add_remainder (R F : ℕ) :
    R = cubeQuotient R F * F + cubeRemainder R F := by
  change R = R / F * F + R % F
  calc
    R = F * (R / F) + R % F := (Nat.div_add_mod R F).symm
    _ = R / F * F + R % F := by rw [Nat.mul_comm]

/-- A positive factor product bounds the Euclidean remainder strictly below that factor. -/
theorem cubeRemainder_lt {R F : ℕ} (hF : 0 < F) : cubeRemainder R F < F := by
  exact Nat.mod_lt R hF

/-- If the cofactor is below `F^2`, its quotient by `F` is below `F`. -/
theorem cubeQuotient_lt_of_lt_square {R F : ℕ} (hF : 0 < F) (hR : R < F ^ 2) :
    cubeQuotient R F < F := by
  change R / F < F
  apply (Nat.div_lt_iff_lt_mul hF).2
  simpa only [pow_two] using hR

/-- The BLS factorization `n = F * R + 1` and bound `n < F^3` force `R < F^2`.
This is an initial cofactor bound; deriving the sharper `u + v < F` condition remains separate. -/
theorem cubeCofactor_lt_square_of_factorization_bound {n F R : ℕ}
    (hdecomp : n = F * R + 1) (hbound : n < F ^ 3) : R < F ^ 2 := by
  have hmul : F * R < F ^ 3 := by
    calc
      F * R ≤ F * R + 1 := Nat.le_add_right _ _
      _ = n := hdecomp.symm
      _ < F ^ 3 := hbound
  have hpow : F ^ 3 = F * F ^ 2 := by
    rw [Nat.pow_succ, Nat.pow_succ]
    ac_rfl
  rw [hpow] at hmul
  exact Nat.lt_of_mul_lt_mul_left hmul

/-- Under the cube-root size bound, the quotient coefficient is strictly below `F`. -/
theorem cubeQuotient_lt_of_factorization_cube_bound {n F R : ℕ}
    (hF : 0 < F) (hdecomp : n = F * R + 1) (hbound : n < F ^ 3) :
    cubeQuotient R F < F := by
  exact cubeQuotient_lt_of_lt_square hF
    (cubeCofactor_lt_square_of_factorization_bound hdecomp hbound)

/-- A remainder-form decomposition exposes its quotient and remainder as the cube coefficients. -/
theorem cubeCoefficients_of_euclidean_form {F q r : ℕ} (hr : r < F) :
    cubeQuotient (F * q + r) F = q ∧ cubeRemainder (F * q + r) F = r := by
  constructor
  · change (F * q + r) / F = q
    apply Nat.div_eq_of_lt_le
    · calc
        q * F = F * q := Nat.mul_comm q F
        _ ≤ F * q + r := Nat.le_add_right (F * q) r
    · calc
        F * q + r < F * q + F := Nat.add_lt_add_left hr (F * q)
        _ = (q + 1) * F := by
          rw [Nat.succ_mul]
          ac_rfl
  · change (F * q + r) % F = r
    calc
      (F * q + r) % F = ((F * q) % F + r % F) % F := Nat.add_mod _ _ _
      _ = (0 + r % F) % F := by rw [Nat.mul_mod_right]
      _ = r := by simp only [Nat.zero_add, Nat.mod_eq_of_lt hr]

/-- Expanding two nontrivial factors gives the coefficient form used by the cube-root criterion. -/
theorem cubeFactorProduct_expansion (F u v : ℕ) :
    (u * F + 1) * (v * F + 1) = F * (u * v * F + u + v) + 1 := by
  ring

/-- A factorization `n = (uF+1)(vF+1)` determines the cofactor `(n-1)/F` exactly. -/
theorem cubeCofactor_eq_factor_coefficients {n F R u v : ℕ} (hF : 0 < F)
    (hdecomp : n = F * R + 1) (hfactor : (u * F + 1) * (v * F + 1) = n) :
    R = u * v * F + u + v := by
  have hexpand := cubeFactorProduct_expansion F u v
  have hmuladd : F * R + 1 = F * (u * v * F + u + v) + 1 := by
    calc
      F * R + 1 = n := hdecomp.symm
      _ = (u * F + 1) * (v * F + 1) := hfactor.symm
      _ = F * (u * v * F + u + v) + 1 := hexpand
  have hmul : F * R = F * (u * v * F + u + v) := Nat.add_right_cancel hmuladd
  exact Nat.mul_left_cancel hF hmul

/-- If `u+v<F`, the product factorization exposes `uv` and `u+v` as quotient and remainder. -/
theorem cubeCoefficients_of_factorization {n F R u v : ℕ} (hF : 0 < F)
    (hdecomp : n = F * R + 1) (hfactor : (u * F + 1) * (v * F + 1) = n)
    (hsum : u + v < F) :
    cubeQuotient R F = u * v ∧ cubeRemainder R F = u + v := by
  have hcofactor := cubeCofactor_eq_factor_coefficients hF hdecomp hfactor
  have hlinear : R = F * (u * v) + (u + v) := by
    rw [hcofactor]
    ac_rfl
  rw [hlinear]
  exact cubeCoefficients_of_euclidean_form hsum

/-- Positive coefficients satisfy `u + v ≤ u * v + 1`. -/
theorem add_le_mul_add_one_of_pos {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    u + v ≤ u * v + 1 := by
  obtain ⟨u', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hu))
  obtain ⟨v', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hv))
  calc
    u' + 1 + (v' + 1) = u' + v' + 2 := Nat.add_add_add_comm _ _ _ _
    _ ≤ u' * v' + u' + v' + 2 := by
      calc
        u' + v' + 2 ≤ u' * v' + (u' + v' + 2) := Nat.le_add_left _ _
        _ = u' * v' + u' + v' + 2 := by ac_rfl
    _ = (u' + 1) * (v' + 1) + 1 := by ring

/-- The cofactor bound and positive factors force the no-carry condition `u + v < F`. -/
theorem cubeSum_lt_of_cofactor_bound {F R u v : ℕ} (hR : R < F ^ 2)
    (hcofactor : R = u * v * F + u + v) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    u + v < F := by
  by_contra hnot
  have hFle : F ≤ u + v := Nat.le_of_not_gt hnot
  have huv : u + v ≤ u * v + 1 := add_le_mul_add_one_of_pos hu hv
  have hmul : F * F ≤ F * (u * v + 1) :=
    Nat.mul_le_mul_left F (le_trans hFle huv)
  have hRlow : F ^ 2 ≤ R := by
    calc
      F ^ 2 = F * F := by rw [pow_two]
      _ ≤ F * (u * v + 1) := hmul
      _ = F * (u * v) + F := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ F * (u * v) + (u + v) := Nat.add_le_add_left hFle (F * (u * v))
      _ = R := by
        calc
          F * (u * v) + (u + v) = u * v * F + u + v := by ac_rfl
          _ = R := hcofactor.symm
  exact (Nat.not_le_of_gt hR) hRlow

/-- The cube-root size bound yields the coefficient remainder bound and exact BLS coefficients. -/
theorem cubeCoefficients_of_factorization_cube_bound {n F R u v : ℕ}
    (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hfactor : (u * F + 1) * (v * F + 1) = n) (hbound : n < F ^ 3)
    (hu : 1 ≤ u) (hv : 1 ≤ v) :
    cubeQuotient R F = u * v ∧ cubeRemainder R F = u + v := by
  have hRbound := cubeCofactor_lt_square_of_factorization_bound hdecomp hbound
  have hcofactor := cubeCofactor_eq_factor_coefficients hF hdecomp hfactor
  have hsum := cubeSum_lt_of_cofactor_bound hRbound hcofactor hu hv
  exact cubeCoefficients_of_factorization hF hdecomp hfactor hsum

/-- The cube-root discriminant is a square for a factorization below the `F^3` bound. -/
theorem cubeDiscriminant_eq_square_of_factorization_cube_bound {n F R u v : ℕ}
    (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hfactor : (u * F + 1) * (v * F + 1) = n) (hbound : n < F ^ 3)
    (hu : 1 ≤ u) (hv : 1 ≤ v) : cubeDiscriminant R F = ((u : ℤ) - v) ^ 2 := by
  have hcoeff := cubeCoefficients_of_factorization_cube_bound hF hdecomp hfactor hbound hu hv
  rcases hcoeff with ⟨hquot, hrem⟩
  unfold cubeDiscriminant
  rw [hrem, hquot, Nat.cast_add, Nat.cast_mul]
  ring

/-- The discriminant differs from the squared remainder by four times the quotient.
This exact integer identity is the algebraic starting point for reversing a square discriminant. -/
theorem cubeDiscriminant_add_four_quotient (R F : ℕ) :
    cubeDiscriminant R F + 4 * (cubeQuotient R F : ℤ) =
      (cubeRemainder R F : ℤ) ^ 2 := by
  unfold cubeDiscriminant
  ring

/-- A square discriminant forces the quotient and remainder to satisfy the usual
quadratic-root identity, prior to parity and nonnegativity reconstruction. -/
theorem quotient_remainder_identity_of_cubeDiscriminant_eq_square
    (R F : ℕ) (z : ℤ) (hsquare : cubeDiscriminant R F = z ^ 2) :
    z ^ 2 + 4 * (cubeQuotient R F : ℤ) = (cubeRemainder R F : ℤ) ^ 2 := by
  have hid := cubeDiscriminant_add_four_quotient R F
  rw [hsquare] at hid
  exact hid

/-- A square discriminant forces the remainder and its square root to have the
same parity, so their sum is even. This is the first integrality condition for root recovery. -/
theorem even_remainder_add_sub_root_of_cubeDiscriminant_eq_square
    (R F : ℕ) (z : ℤ) (hsquare : cubeDiscriminant R F = z ^ 2) :
    Even ((cubeRemainder R F : ℤ) + z) ∧ Even ((cubeRemainder R F : ℤ) - z) := by
  have hid := quotient_remainder_identity_of_cubeDiscriminant_eq_square R F z hsquare
  have hdiff : (cubeRemainder R F : ℤ) ^ 2 - z ^ 2 =
      4 * (cubeQuotient R F : ℤ) := by
    calc
      (cubeRemainder R F : ℤ) ^ 2 - z ^ 2 =
          (z ^ 2 + 4 * (cubeQuotient R F : ℤ)) - z ^ 2 := by rw [← hid]
      _ = 4 * (cubeQuotient R F : ℤ) := by ring
  have heven : Even ((cubeRemainder R F : ℤ) ^ 2 - z ^ 2) := by
    rw [hdiff]
    exact ⟨2 * (cubeQuotient R F : ℤ), by ring⟩
  have hsq : Even ((cubeRemainder R F : ℤ) ^ 2) ↔ Even (z ^ 2) :=
    (Int.even_sub).mp heven
  have hparity : Even (cubeRemainder R F : ℤ) ↔ Even z := by
    constructor
    · intro hr
      have hr2 : Even ((cubeRemainder R F : ℤ) ^ 2) :=
        (Int.even_pow).mpr ⟨hr, by decide⟩
      have hz2 : Even (z ^ 2) := hsq.mp hr2
      exact ((Int.even_pow).mp hz2).1
    · intro hz
      have hz2 : Even (z ^ 2) := (Int.even_pow).mpr ⟨hz, by decide⟩
      have hr2 : Even ((cubeRemainder R F : ℤ) ^ 2) := hsq.mpr hz2
      exact ((Int.even_pow).mp hr2).1
  exact ⟨Int.even_add.mpr hparity, Int.even_sub.mpr hparity⟩

/-- A nonnegative quotient in the square-discriminant identity bounds the absolute
value of its integer square root by the nonnegative Euclidean remainder. -/
theorem abs_root_le_remainder_of_cubeDiscriminant_eq_square
    (R F : ℕ) (z : ℤ) (hsquare : cubeDiscriminant R F = z ^ 2) :
    - (cubeRemainder R F : ℤ) ≤ z ∧ z ≤ (cubeRemainder R F : ℤ) := by
  have hid := quotient_remainder_identity_of_cubeDiscriminant_eq_square R F z hsquare
  have hr2 : z ^ 2 ≤ (cubeRemainder R F : ℤ) ^ 2 := by
    calc
      z ^ 2 ≤ z ^ 2 + 4 * (cubeQuotient R F : ℤ) :=
        Int.le_add_of_nonneg_right
          (Int.mul_nonneg (by decide) (Int.natCast_nonneg (cubeQuotient R F)))
      _ = (cubeRemainder R F : ℤ) ^ 2 := hid
  have hrnonneg : 0 ≤ (cubeRemainder R F : ℤ) :=
    Int.natCast_nonneg (cubeRemainder R F)
  constructor
  · nlinarith only [hr2, hrnonneg]
  · nlinarith only [hr2, hrnonneg]

/-- Parity and the absolute-value bound reconstruct nonnegative quadratic roots.
Their sum, difference, and product are the Euclidean remainder, chosen root, and quotient. -/
theorem quadratic_roots_of_discriminant_identity (r q z : ℤ)
    (hid : z ^ 2 + 4 * q = r ^ 2)
    (hparity : Even (r + z) ∧ Even (r - z))
    (hlower : -r ≤ z) (hupper : z ≤ r) :
    ∃ u v : ℤ, 0 ≤ u ∧ 0 ≤ v ∧ r = u + v ∧ z = u - v ∧ q = u * v := by
  rcases hparity with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  have hsum_nonneg : 0 ≤ r + z := by
    linarith only [hlower]
  have hsub_nonneg : 0 ≤ r - z := by
    linarith only [hupper]
  have hu_nonneg : 0 ≤ u := by
    linarith only [hsum_nonneg, hu]
  have hv_nonneg : 0 ≤ v := by
    linarith only [hsub_nonneg, hv]
  have hr_eq : r = u + v := by
    linarith only [hu, hv]
  have hz_eq : z = u - v := by
    linarith only [hu, hv]
  have hquad : (u + v) ^ 2 - (u - v) ^ 2 = 4 * (u * v) := by
    ring
  have hquad' : r ^ 2 - z ^ 2 = 4 * (u * v) := by
    rw [hr_eq, hz_eq]
    exact hquad
  have hq_eq : q = u * v := by
    linarith only [hid, hquad']
  exact ⟨u, v, hu_nonneg, hv_nonneg, hr_eq, hz_eq, hq_eq⟩

/-- Every integer square root of the BLS discriminant reconstructs nonnegative
integer roots with sum equal to the remainder and product equal to the quotient. -/
theorem quadratic_roots_of_cubeDiscriminant_eq_square
    (R F : ℕ) (z : ℤ) (hsquare : cubeDiscriminant R F = z ^ 2) :
    ∃ u v : ℤ, 0 ≤ u ∧ 0 ≤ v ∧
      (cubeRemainder R F : ℤ) = u + v ∧ z = u - v ∧
      (cubeQuotient R F : ℤ) = u * v := by
  have hid := quotient_remainder_identity_of_cubeDiscriminant_eq_square R F z hsquare
  have hparity := even_remainder_add_sub_root_of_cubeDiscriminant_eq_square R F z hsquare
  have hbound := abs_root_le_remainder_of_cubeDiscriminant_eq_square R F z hsquare
  exact quadratic_roots_of_discriminant_identity
    (cubeRemainder R F : ℤ) (cubeQuotient R F : ℤ) z hid hparity hbound.1 hbound.2

/-- A positive quotient and square discriminant reconstruct a nontrivial factorization
of `n = F * R + 1`. This is the arithmetic converse to the forward discriminant theorem. -/
theorem factorization_of_positive_quotient_and_cubeDiscriminant_square
    {n F R : ℕ} (hdecomp : n = F * R + 1)
    (hquotient : 0 < cubeQuotient R F) (z : ℤ)
    (hsquare : cubeDiscriminant R F = z ^ 2) :
    ∃ u v : ℕ, 1 ≤ u ∧ 1 ≤ v ∧ n = (u * F + 1) * (v * F + 1) := by
  obtain ⟨u, v, hu0, hv0, hrEq, _, hqEq⟩ :=
    quadratic_roots_of_cubeDiscriminant_eq_square R F z hsquare
  have hquotientInt : 0 < (cubeQuotient R F : ℤ) := by
    exact_mod_cast hquotient
  have huPos : 0 < u := by
    by_contra huNot
    have huZero : u = 0 := Int.le_antisymm (Int.not_lt.mp huNot) hu0
    rw [huZero, Int.zero_mul] at hqEq
    exact (Int.ne_of_gt hquotientInt) hqEq
  have hvPos : 0 < v := by
    by_contra hvNot
    have hvZero : v = 0 := Int.le_antisymm (Int.not_lt.mp hvNot) hv0
    rw [hvZero, Int.mul_zero] at hqEq
    exact (Int.ne_of_gt hquotientInt) hqEq
  let uNat := u.toNat
  let vNat := v.toNat
  have huCast : (uNat : ℤ) = u := Int.toNat_of_nonneg hu0
  have hvCast : (vNat : ℤ) = v := Int.toNat_of_nonneg hv0
  have huNat : 1 ≤ uNat := Nat.succ_le_iff.mpr (Int.pos_iff_toNat_pos.mp huPos)
  have hvNat : 1 ≤ vNat := Nat.succ_le_iff.mpr (Int.pos_iff_toNat_pos.mp hvPos)
  have hrNat : cubeRemainder R F = uNat + vNat := by
    rw [← huCast, ← hvCast] at hrEq
    exact_mod_cast hrEq
  have hqNat : cubeQuotient R F = uNat * vNat := by
    rw [← huCast, ← hvCast] at hqEq
    exact_mod_cast hqEq
  have hcofactor : R = uNat * vNat * F + uNat + vNat := by
    rw [cubeQuotient_mul_add_remainder R F, hqNat, hrNat]
    ac_rfl
  refine ⟨uNat, vNat, huNat, hvNat, ?_⟩
  calc
    n = F * R + 1 := hdecomp
    _ = F * (uNat * vNat * F + uNat + vNat) + 1 := by rw [hcofactor]
    _ = (uNat * F + 1) * (vNat * F + 1) := by ring

/-- A square discriminant with positive quotient gives a proper divisor, hence
proves compositeness. No prime-divisor congruence or cube-size bound is needed here. -/
theorem not_prime_of_positive_quotient_and_cubeDiscriminant_square
    {n F R : ℕ} (hn : 1 < n) (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hquotient : 0 < cubeQuotient R F) (z : ℤ)
    (hsquare : cubeDiscriminant R F = z ^ 2) : ¬ Nat.Prime n := by
  obtain ⟨u, v, hu, hv, hfactor⟩ :=
    factorization_of_positive_quotient_and_cubeDiscriminant_square
      hdecomp hquotient z hsquare
  have huProd : 1 ≤ u * F :=
    Nat.succ_le_iff.mpr (Nat.mul_pos (Nat.zero_lt_of_lt hu) hF)
  have hvProd : 1 ≤ v * F :=
    Nat.succ_le_iff.mpr (Nat.mul_pos (Nat.zero_lt_of_lt hv) hF)
  have hu2 : 2 ≤ u * F + 1 := by
    calc
      2 = 1 + 1 := by decide
      _ ≤ u * F + 1 := Nat.add_le_add_right huProd 1
  have hv2 : 2 ≤ v * F + 1 := by
    calc
      2 = 1 + 1 := by decide
      _ ≤ v * F + 1 := Nat.add_le_add_right hvProd 1
  have huPos : 0 < u * F + 1 := Nat.zero_lt_of_lt hu2
  have huLt : u * F + 1 < n := by
    calc
      u * F + 1 < (u * F + 1) * (v * F + 1) := by
        have hmul := Nat.mul_lt_mul_of_pos_left
          (Nat.lt_of_lt_of_le (by decide : 1 < 2) hv2) huPos
        simpa only [Nat.mul_one] using hmul
      _ = n := hfactor.symm
  exact (Nat.not_prime_iff_exists_dvd_lt (Nat.succ_le_iff.mpr hn)).mpr
    ⟨u * F + 1, ⟨v * F + 1, hfactor⟩, hu2, huLt⟩

/-- A checked square-root certificate proves compositeness when the quotient is positive. -/
theorem not_prime_of_checkCubeDiscriminantSquareWitness
    {n F R : ℕ} (hn : 1 < n) (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hquotient : 0 < cubeQuotient R F) (z : ℤ)
    (hcheck : checkCubeDiscriminantSquareWitness R F z = true) : ¬ Nat.Prime n := by
  apply not_prime_of_positive_quotient_and_cubeDiscriminant_square
    hn hF hdecomp hquotient z
  exact (checkCubeDiscriminantSquareWitness_eq_true_iff R F z).mp hcheck

/-- The complete square-root search supplies the certificate consumed by the BLS
compositeness theorem whenever the quotient is positive. -/
theorem not_prime_of_findCubeDiscriminantSquareRoot
    {n F R : ℕ} (hn : 1 < n) (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hquotient : 0 < cubeQuotient R F) (z : ℤ)
    (hfind : findCubeDiscriminantSquareRoot R F = some z) : ¬ Nat.Prime n := by
  apply not_prime_of_positive_quotient_and_cubeDiscriminant_square
    hn hF hdecomp hquotient z
  exact findCubeDiscriminantSquareRoot_some_spec R F z hfind

/-- The quotient-remainder decomposition is preserved as an integer identity. -/
theorem cubeQuotient_mul_add_remainder_int (R F : ℕ) :
    (R : ℤ) = (cubeQuotient R F : ℤ) * F + cubeRemainder R F := by
  exact_mod_cast cubeQuotient_mul_add_remainder R F

/-- If every prime divisor of `m` is congruent to `1` modulo `F`, then so is `m`.
The proof factors off a prime divisor and applies strong induction to the quotient. -/
theorem exists_factor_form_of_prime_divisors_congruent (m F : ℕ) (hm : 0 < m)
    (hprime : ∀ p, Nat.Prime p → p ∣ m → F ∣ p - 1) :
    ∃ u, m = F * u + 1 := by
  induction m using Nat.strong_induction_on generalizing F with
  | h m ih =>
      by_cases hmone : m = 1
      · refine ⟨0, ?_⟩
        rw [hmone]
        simp only [Nat.mul_zero, Nat.zero_add]
      · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hmone
        have hpform : ∃ a, p = F * a + 1 := by
          have hdvd := hprime p hp hpm
          have hmod : (p - 1) % F = 0 := Nat.mod_eq_zero_of_dvd hdvd
          have hdiv := Nat.mod_add_div (p - 1) F
          rw [hmod] at hdiv
          have hdiv' : F * ((p - 1) / F) = p - 1 := by
            simpa only [Nat.zero_add] using hdiv
          refine ⟨(p - 1) / F, ?_⟩
          calc
            p = p - 1 + 1 := (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne_zero)).symm
            _ = F * ((p - 1) / F) + 1 := by rw [hdiv']
        let q := m / p
        have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos
        have hqLt : q < m := Nat.div_lt_self hm hp.one_lt
        have hpq : p * q = m := Nat.mul_div_cancel' hpm
        have hqdiv : q ∣ m := by
          exact ⟨p, by
            rw [← hpq]
            ac_rfl⟩
        obtain ⟨b, hqform⟩ := ih q hqLt F hqpos
          (fun r hr hrq => hprime r hr (dvd_trans hrq hqdiv))
        obtain ⟨a, hap⟩ := hpform
        refine ⟨F * a * b + a + b, ?_⟩
        calc
          m = p * q := hpq.symm
          _ = (F * a + 1) * (F * b + 1) := by rw [hap, hqform]
          _ = F * (F * a * b + a + b) + 1 := by ring

/-- Every positive divisor of an input satisfying `PrimeDivisorsAbove` has the same
`F * u + 1` form. This is the factor-shape interface needed for the cube-root branch. -/
theorem exists_factor_form_of_primeDivisorsAbove {n F m : ℕ}
    (hlarge : PrimeDivisorsAbove n F) (hmn : m ∣ n) (hm : 0 < m) :
    ∃ u, m = F * u + 1 :=
  exists_factor_form_of_prime_divisors_congruent m F hm
    (fun p hp hpm => hlarge p hp (dvd_trans hpm hmn))

/-- A composite input with all prime divisors above `F` splits into two nontrivial
factors of the BLS form. This supplies the factorization consumed by the cube discriminant. -/
theorem exists_bls_factorization_of_composite_of_primeDivisorsAbove {n F : ℕ}
    (hn : 1 < n) (hnot : ¬ Nat.Prime n) (hlarge : PrimeDivisorsAbove n F) :
    ∃ u v, n = (u * F + 1) * (v * F + 1) ∧ 1 ≤ u ∧ 1 ≤ v := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hn)
  have hpne : p ≠ n := by
    intro heq
    apply hnot
    rw [← heq]
    exact hp
  have hp_le : p ≤ n := Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hpn
  let q := n / p
  have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hpn) hp.pos
  have hpq : p * q = n := Nat.mul_div_cancel' hpn
  have hqne : q ≠ 1 := by
    intro hq
    apply hpne
    calc
      p = p * 1 := (Nat.mul_one p).symm
      _ = p * q := congrArg (fun x : ℕ => p * x) hq.symm
      _ = n := hpq
  have hqdiv : q ∣ n := ⟨p, by
    rw [← hpq]
    ac_rfl⟩
  obtain ⟨u, huform⟩ := exists_factor_form_of_primeDivisorsAbove hlarge hpn hp.pos
  obtain ⟨v, hvform⟩ := exists_factor_form_of_primeDivisorsAbove hlarge hqdiv hqpos
  have hu : 1 ≤ u := by
    by_contra h
    have hu0 : u = 0 := Nat.eq_zero_of_not_pos (fun huPos => h (Nat.succ_le_iff.mpr huPos))
    rw [hu0] at huform
    have hp1 : p = 1 := by simpa only [Nat.mul_zero, Nat.zero_add] using huform
    exact (Nat.ne_of_gt hp.one_lt) hp1
  have hv : 1 ≤ v := by
    by_contra h
    have hv0 : v = 0 := Nat.eq_zero_of_not_pos (fun hvPos => h (Nat.succ_le_iff.mpr hvPos))
    rw [hv0] at hvform
    have hq1 : q = 1 := by simpa only [Nat.mul_zero, Nat.zero_add] using hvform
    exact hqne hq1
  refine ⟨u, v, ?_, hu, hv⟩
  calc
    n = p * q := hpq.symm
    _ = (u * F + 1) * (v * F + 1) := by
      rw [huform, hvform]
      ac_rfl

/-- Below the cube-root bound, a composite input satisfying the BLS prime-divisor
condition has square discriminant. Thus nonsquareness is a sound compositeness exclusion. -/
theorem cubeDiscriminant_eq_square_of_composite_of_primeDivisorsAbove
    {n F R : ℕ} (hF : 0 < F) (hn : 1 < n) (hnot : ¬ Nat.Prime n)
    (hlarge : PrimeDivisorsAbove n F) (hdecomp : n = F * R + 1)
    (hbound : n < F ^ 3) :
    ∃ u v : ℕ, 1 ≤ u ∧ 1 ≤ v ∧
      cubeDiscriminant R F = ((u : ℤ) - v) ^ 2 := by
  obtain ⟨u, v, hfactor, hu, hv⟩ :=
    exists_bls_factorization_of_composite_of_primeDivisorsAbove hn hnot hlarge
  exact ⟨u, v, hu, hv,
    cubeDiscriminant_eq_square_of_factorization_cube_bound hF hdecomp hfactor.symm hbound hu hv⟩

/-- Under the cube bound and BLS prime-divisor condition, a nonsquare discriminant
proves primality. -/
theorem prime_of_nonsquare_cubeDiscriminant_of_primeDivisorsAbove
    {n F R : ℕ} (hF : 0 < F) (hn : 1 < n)
    (hdecomp : n = F * R + 1) (hbound : n < F ^ 3)
    (hlarge : PrimeDivisorsAbove n F)
    (hnsquare : ∀ z : ℤ, cubeDiscriminant R F ≠ z ^ 2) : Nat.Prime n := by
  by_contra hnot
  obtain ⟨u, v, _, _, hsquare⟩ :=
    cubeDiscriminant_eq_square_of_composite_of_primeDivisorsAbove hF hn hnot hlarge
      hdecomp hbound
  exact hnsquare ((u : ℤ) - v) hsquare

/-- With positive quotient, the cube-root BLS arithmetic conditions characterize
primality exactly by nonsquareness of the discriminant. -/
theorem prime_iff_nonsquare_cubeDiscriminant_of_primeDivisorsAbove
    {n F R : ℕ} (hn : 1 < n) (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hquotient : 0 < cubeQuotient R F) (hbound : n < F ^ 3)
    (hlarge : PrimeDivisorsAbove n F) :
    Nat.Prime n ↔ ∀ z : ℤ, cubeDiscriminant R F ≠ z ^ 2 := by
  constructor
  · intro hprime z hsquare
    exact (not_prime_of_positive_quotient_and_cubeDiscriminant_square
      hn hF hdecomp hquotient z hsquare) hprime
  · intro hnsquare
    exact prime_of_nonsquare_cubeDiscriminant_of_primeDivisorsAbove
      hF hn hdecomp hbound hlarge hnsquare

/-- The cube-root BLS primality criterion as an executable square-test specification. -/
theorem prime_iff_cubeDiscriminantIsSquare_false_of_primeDivisorsAbove
    {n F R : ℕ} (hn : 1 < n) (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hquotient : 0 < cubeQuotient R F) (hbound : n < F ^ 3)
    (hlarge : PrimeDivisorsAbove n F) :
    Nat.Prime n ↔ cubeDiscriminantIsSquare R F = false := by
  constructor
  · intro hprime
    apply (cubeDiscriminantIsSquare_eq_false_iff R F).2
    exact (prime_iff_nonsquare_cubeDiscriminant_of_primeDivisorsAbove
      hn hF hdecomp hquotient hbound hlarge).mp hprime
  · intro htest
    apply (prime_iff_nonsquare_cubeDiscriminant_of_primeDivisorsAbove
      hn hF hdecomp hquotient hbound hlarge).mpr
    exact (cubeDiscriminantIsSquare_eq_false_iff R F).1 htest

/-- Under the BLS prime-divisor condition, a zero quotient forces primality. A composite input
would factor as `(uF+1)(vF+1)` with positive `u` and `v`, forcing the cofactor `R` to be at least
`F` and hence its quotient by `F` to be positive. -/
private theorem prime_of_cubeQuotient_eq_zero_of_primeDivisorsAbove
    {n F R : ℕ} (hn : 1 < n) (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hlarge : PrimeDivisorsAbove n F)
    (hquotient : cubeQuotient R F = 0) : Nat.Prime n := by
  by_contra hprime
  have hnot : ¬ Nat.Prime n := by
    intro hp
    exact hprime hp
  obtain ⟨u, v, hfactor, hu, hv⟩ :=
    exists_bls_factorization_of_composite_of_primeDivisorsAbove hn hnot hlarge
  have hcofactor := cubeCofactor_eq_factor_coefficients hF hdecomp hfactor.symm
  have huvpos : 0 < u * v := Nat.mul_pos (Nat.zero_lt_of_lt hu) (Nat.zero_lt_of_lt hv)
  have huv : 1 ≤ u * v := Nat.succ_le_iff.mpr huvpos
  have hFle : F ≤ R := by
    rw [hcofactor]
    calc
      F = 1 * F := by rw [Nat.one_mul]
      _ ≤ u * v * F := Nat.mul_le_mul_right F huv
      _ ≤ u * v * F + u := Nat.le_add_right _ _
      _ ≤ u * v * F + u + v := Nat.le_add_right _ _
  have hquotientPos : 0 < cubeQuotient R F := Nat.div_pos hFle hF
  exact (Nat.ne_of_gt hquotientPos) hquotient

/-- The executable cube-discriminant test has the exact BLS classification when the zero-quotient
branch is kept explicit: under the prime-divisor condition and cubic size bound, primality is
equivalent to a zero quotient or a nonsquare discriminant. The zero branch is necessary because
prime inputs can have a square discriminant when `R < F`. -/
theorem prime_iff_cubeDiscriminantIsSquare_false_or_quotient_zero_of_primeDivisorsAbove
    {n F R : ℕ} (hn : 1 < n) (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hbound : n < F ^ 3) (hlarge : PrimeDivisorsAbove n F) :
    Nat.Prime n ↔ cubeQuotient R F = 0 ∨ cubeDiscriminantIsSquare R F = false := by
  constructor
  · intro hprime
    by_cases hqzero : cubeQuotient R F = 0
    · exact Or.inl hqzero
    · right
      apply (cubeDiscriminantIsSquare_eq_false_iff R F).2
      intro z hz
      have hqpos : 0 < cubeQuotient R F := Nat.pos_of_ne_zero hqzero
      exact (not_prime_of_positive_quotient_and_cubeDiscriminant_square
        hn hF hdecomp hqpos z hz) hprime
  · rintro (hqzero | hfalse)
    · exact prime_of_cubeQuotient_eq_zero_of_primeDivisorsAbove
        hn hF hdecomp hlarge hqzero
    · apply prime_of_nonsquare_cubeDiscriminant_of_primeDivisorsAbove
        hF hn hdecomp hbound hlarge
      exact (cubeDiscriminantIsSquare_eq_false_iff R F).1 hfalse

/-- The cube-root BLS result contract with its degenerate quotient branch made explicit. Under
the prime-divisor and cubic-size conditions, the input is prime exactly when the quotient is zero
or the complete discriminant-root search returns `none`. -/
theorem prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero
    {n F R : ℕ} (hn : 1 < n) (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hbound : n < F ^ 3) (hlarge : PrimeDivisorsAbove n F) :
    Nat.Prime n ↔ cubeQuotient R F = 0 ∨
      findCubeDiscriminantSquareRoot R F = none := by
  rw [prime_iff_cubeDiscriminantIsSquare_false_or_quotient_zero_of_primeDivisorsAbove
    hn hF hdecomp hbound hlarge]
  constructor
  · rintro (hz | hfalse)
    · exact Or.inl hz
    · exact Or.inr
        ((findCubeDiscriminantSquareRoot_none_iff_square_false R F).2 hfalse)
  · rintro (hz | hnone)
    · exact Or.inl hz
    · exact Or.inr
        ((findCubeDiscriminantSquareRoot_none_iff_square_false R F).1 hnone)

/-- Under the cube-root BLS hypotheses, the complete discriminant-root search returns `none`
exactly for prime inputs. -/
theorem prime_iff_cubeDiscriminantSquareRootSearch_none_of_primeDivisorsAbove
    {n F R : ℕ} (hn : 1 < n) (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hquotient : 0 < cubeQuotient R F) (hbound : n < F ^ 3)
    (hlarge : PrimeDivisorsAbove n F) :
    Nat.Prime n ↔ findCubeDiscriminantSquareRoot R F = none := by
  constructor
  · intro hprime
    have hfalse :=
      (prime_iff_cubeDiscriminantIsSquare_false_of_primeDivisorsAbove
        hn hF hdecomp hquotient hbound hlarge).mp hprime
    cases hroot : findCubeDiscriminantSquareRoot R F with
    | none => rfl
    | some z =>
        have hsome : (findCubeDiscriminantSquareRoot R F).isSome = true := by
          rw [hroot]
          rfl
        have htrue := (findCubeDiscriminantSquareRoot_isSome_iff R F).mp hsome
        rw [hfalse] at htrue
        exact Bool.noConfusion htrue
  · intro hnone
    apply (prime_iff_cubeDiscriminantIsSquare_false_of_primeDivisorsAbove
      hn hF hdecomp hquotient hbound hlarge).mpr
    cases htest : cubeDiscriminantIsSquare R F with
    | false => rfl
    | true =>
        have hsome := (findCubeDiscriminantSquareRoot_isSome_iff R F).2 htest
        rw [hnone] at hsome
        exact Bool.noConfusion hsome

/-- Valid BLS factor and witness data supply the prime-divisor condition for the cube criterion.
Together with the Euclidean decomposition and cube bound, the executable square-root search
returns `none` exactly for prime inputs. -/
theorem prime_iff_cubeDiscriminantSquareRootSearch_none_of_valid_bls_data
    {n F R : ℕ} (hn : 1 < n) (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hquotient : 0 < cubeQuotient R F) (hbound : n < F ^ 3)
    (data : PartialFactorizationData) (witnesses : List (ℕ × ℕ))
    (hfactor : ValidPartialFactorization n data) (hwitness : ValidWitnesses n data witnesses)
    (hproduct : factorProduct data.factors = F) :
    Nat.Prime n ↔ findCubeDiscriminantSquareRoot R F = none := by
  have hlargeData := primeDivisorsAbove_of_valid_bls_data hn data witnesses hfactor hwitness
  have hlarge : PrimeDivisorsAbove n F := by
    intro p hp hpn
    rw [← hproduct]
    exact hlargeData p hp hpn
  exact prime_iff_cubeDiscriminantSquareRootSearch_none_of_primeDivisorsAbove
    hn hF hdecomp hquotient hbound hlarge

/-- Valid BLS factor and witness data also support the zero-quotient branch: the prime criterion
is the disjunction of a zero quotient and failure of the complete square-root search. -/
theorem prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_valid_bls_data
    {n F R : ℕ} (hn : 1 < n) (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hbound : n < F ^ 3)
    (data : PartialFactorizationData) (witnesses : List (ℕ × ℕ))
    (hfactor : ValidPartialFactorization n data) (hwitness : ValidWitnesses n data witnesses)
    (hproduct : factorProduct data.factors = F) :
    Nat.Prime n ↔ cubeQuotient R F = 0 ∨
      findCubeDiscriminantSquareRoot R F = none := by
  have hlargeData := primeDivisorsAbove_of_valid_bls_data hn data witnesses hfactor hwitness
  have hlarge : PrimeDivisorsAbove n F := by
    intro p hp hpn
    rw [← hproduct]
    exact hlargeData p hp hpn
  exact prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero
    hn hF hdecomp hbound hlarge

/-- Every accepted square-root certificate also satisfies the branch-sensitive cube-root result.
The certificate's stronger square-root bound implies the cubic bound required by the latter. -/
theorem prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_valid_square_certificate
    (c : SquareCertificate) (hcheck : verifySquareCertificate c = true) :
    Nat.Prime c.n ↔
      cubeQuotient c.factorization.cofactor
        (factorProduct c.factorization.factors) = 0 ∨
      findCubeDiscriminantSquareRoot c.factorization.cofactor
        (factorProduct c.factorization.factors) = none := by
  simp only [verifySquareCertificate, checkSquareCertificate,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hn5, hbound⟩, hfactor⟩, hwitness⟩
  have hdata := (checkPartialFactorization_eq_true_iff c.n c.factorization).mp hfactor
  have hn : 1 < c.n := lt_of_lt_of_le (by decide : 1 < 5) hn5
  have hFpos : 0 < factorProduct c.factorization.factors :=
    lt_trans (by decide : 0 < 1) hdata.1
  have hdecomp : c.n = factorProduct c.factorization.factors *
      c.factorization.cofactor + 1 := by
    calc
      c.n = (c.n - 1) + 1 := (Nat.sub_add_cancel (Nat.le_of_lt hn)).symm
      _ = factorProduct c.factorization.factors * c.factorization.cofactor + 1 := by
        rw [hdata.2.1]
  have hFone : 1 ≤ factorProduct c.factorization.factors := Nat.le_of_lt hdata.1
  have hF2le : factorProduct c.factorization.factors ^ 2 ≤
      factorProduct c.factorization.factors ^ 3 := by
    calc
      factorProduct c.factorization.factors ^ 2 =
          factorProduct c.factorization.factors ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ factorProduct c.factorization.factors ^ 2 *
          factorProduct c.factorization.factors := Nat.mul_le_mul_left _ hFone
      _ = factorProduct c.factorization.factors ^ 3 := (pow_succ _ 2).symm
  have hbound3 : c.n < factorProduct c.factorization.factors ^ 3 :=
    lt_of_lt_of_le hbound hF2le
  exact prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_valid_bls_data
    hn hFpos hdecomp hbound3 c.factorization c.witnesses hfactor hwitness rfl

/-- An accepted square-root certificate with zero cube quotient already certifies primality.
This is the degenerate branch of the certificate's three-way cube-root result. -/
theorem prime_of_cubeQuotient_eq_zero_of_valid_square_certificate
    (c : SquareCertificate) (hcheck : verifySquareCertificate c = true)
    (hzero : cubeQuotient c.factorization.cofactor
      (factorProduct c.factorization.factors) = 0) : Nat.Prime c.n := by
  exact (prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_valid_square_certificate
    c hcheck).mpr (Or.inl hzero)

/-- Away from the zero-quotient branch, an accepted square-root certificate is prime exactly
when the complete discriminant square-root search returns `none`. -/
theorem prime_iff_cubeDiscriminantSquareRootSearch_none_of_valid_square_certificate
    (c : SquareCertificate) (hcheck : verifySquareCertificate c = true)
    (hquotient : 0 < cubeQuotient c.factorization.cofactor
      (factorProduct c.factorization.factors)) :
    Nat.Prime c.n ↔
      findCubeDiscriminantSquareRoot c.factorization.cofactor
        (factorProduct c.factorization.factors) = none := by
  rw [prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_valid_square_certificate
    c hcheck]
  constructor
  · intro hprime
    rcases hprime with hzero | hnone
    · exact False.elim (Nat.ne_of_gt hquotient hzero)
    · exact hnone
  · intro hnone
    exact Or.inr hnone

/-- For an accepted certificate with positive cube quotient, a found discriminant square root
proves that the certified input is composite. -/
theorem not_prime_of_findCubeDiscriminantSquareRoot_some_of_valid_square_certificate
    (c : SquareCertificate) (hcheck : verifySquareCertificate c = true)
    (hquotient : 0 < cubeQuotient c.factorization.cofactor
      (factorProduct c.factorization.factors)) {z : ℤ}
    (hroot : findCubeDiscriminantSquareRoot c.factorization.cofactor
      (factorProduct c.factorization.factors) = some z) :
    ¬ Nat.Prime c.n := by
  intro hprime
  have hnone :=
    (prime_iff_cubeDiscriminantSquareRootSearch_none_of_valid_square_certificate
      c hcheck hquotient).mp hprime
  rw [hroot] at hnone
  cases hnone

end PseudoPrime.PrimeTest.BLS
