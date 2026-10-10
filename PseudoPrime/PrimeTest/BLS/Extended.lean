/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.BLS.Cube

/-!
# Arithmetic data for the extended BLS criterion

This module establishes the quotient, remainder, and parity interface for the BLS5 branch.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.BLS

/-- Quotient in the Euclidean decomposition of the BLS cofactor by `2 * F`. -/
def bls5Quotient (R F : ℕ) : ℕ :=
  R / (2 * F)

/-- Remainder in the Euclidean decomposition `R = 2 * F * bls5Quotient R F + bls5Remainder R F`. -/
def bls5Remainder (R F : ℕ) : ℕ :=
  R % (2 * F)

/-- Integer discriminant `r^2 - 8s` for the extended BLS criterion, with `r` and `s` read from
the Euclidean decomposition of `R` by `2 * F`. -/
def bls5Discriminant (R F : ℕ) : ℤ :=
  (bls5Remainder R F : ℤ) ^ 2 - 8 * (bls5Quotient R F : ℤ)

/-- Executable square test for the integer BLS5 discriminant, using the natural square root.
The sign check is needed because `Int.toNat` maps negative values to zero. -/
def bls5DiscriminantIsSquare (R F : ℕ) : Bool :=
  let d := bls5Discriminant R F
  decide (0 ≤ d) && decide (Nat.sqrt d.toNat ^ 2 = d.toNat)

/-- The square test accepts exactly when the integer discriminant has an integer square root. -/
theorem bls5DiscriminantIsSquare_eq_true_iff (R F : ℕ) :
    bls5DiscriminantIsSquare R F = true ↔ ∃ z : ℤ, bls5Discriminant R F = z ^ 2 := by
  unfold bls5DiscriminantIsSquare
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hd, hroot⟩
    refine ⟨(Nat.sqrt (bls5Discriminant R F).toNat : ℕ), ?_⟩
    calc
      bls5Discriminant R F = ((bls5Discriminant R F).toNat : ℤ) := (Int.toNat_of_nonneg hd).symm
      _ = ((Nat.sqrt (bls5Discriminant R F).toNat ^ 2 : ℕ) : ℤ) := by rw [hroot]
      _ = (Nat.sqrt (bls5Discriminant R F).toNat : ℤ) ^ 2 := by rw [pow_two, Nat.cast_mul, pow_two]
  · rintro ⟨z, hz⟩
    have hd : 0 ≤ bls5Discriminant R F := by
      rw [hz]
      exact Int.sq_nonneg z
    have hnat : (z ^ 2).toNat = z.natAbs ^ 2 := by
      have hsqnonneg : 0 ≤ z ^ 2 := Int.sq_nonneg z
      have hcast := (Int.toNat_of_nonneg hsqnonneg).trans (Int.natAbs_of_nonneg hsqnonneg).symm
      rw [Int.natAbs_pow] at hcast
      exact_mod_cast hcast
    have htoNat : (bls5Discriminant R F).toNat = z.natAbs * z.natAbs := by
      calc
        (bls5Discriminant R F).toNat = (z ^ 2).toNat := congrArg Int.toNat hz
        _ = z.natAbs ^ 2 := hnat
        _ = z.natAbs * z.natAbs := by rw [pow_two]
    refine ⟨hd, ?_⟩
    rw [htoNat, Nat.sqrt_eq, pow_two]

/-- The square test rejects exactly when the discriminant has no integer square root. -/
theorem bls5DiscriminantIsSquare_eq_false_iff (R F : ℕ) :
    bls5DiscriminantIsSquare R F = false ↔ ∀ z : ℤ, bls5Discriminant R F ≠ z ^ 2 := by
  constructor
  · intro hfalse z hz
    have htrue : bls5DiscriminantIsSquare R F = true :=
      (bls5DiscriminantIsSquare_eq_true_iff R F).2 ⟨z, hz⟩
    rw [hfalse] at htrue
    exact Bool.noConfusion htrue
  · intro hnsquare
    cases h : bls5DiscriminantIsSquare R F with
    | false => rfl
    | true =>
      obtain ⟨z, hz⟩ := (bls5DiscriminantIsSquare_eq_true_iff R F).1 h
      exact False.elim (hnsquare z hz)

/-- Return the nonnegative integer square root when the discriminant is a square.
The option is `none` exactly when the executable square test rejects. -/
def findBls5DiscriminantSquareRoot (R F : ℕ) : Option ℤ :=
  if bls5DiscriminantIsSquare R F then some (Nat.sqrt (bls5Discriminant R F).toNat : ℤ) else none

/-- A returned discriminant root is a valid square-root certificate. -/
theorem findBls5DiscriminantSquareRoot_some_spec (R F : ℕ) (z : ℤ)
    (hfind : findBls5DiscriminantSquareRoot R F = some z) : bls5Discriminant R F = z ^ 2 := by
  unfold findBls5DiscriminantSquareRoot at hfind
  split at hfind
  · injection hfind with hz
    subst z
    rename_i htest
    unfold bls5DiscriminantIsSquare at htest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
    rcases htest with ⟨hd, hroot⟩
    calc
      bls5Discriminant R F = ((bls5Discriminant R F).toNat : ℤ) := (Int.toNat_of_nonneg hd).symm
      _ = ((Nat.sqrt (bls5Discriminant R F).toNat ^ 2 : ℕ) : ℤ) := by rw [hroot]
      _ = (Nat.sqrt (bls5Discriminant R F).toNat : ℤ) ^ 2 := by rw [pow_two, Nat.cast_mul, pow_two]
  · cases hfind

/-- The root search succeeds exactly when the discriminant square test accepts. -/
theorem findBls5DiscriminantSquareRoot_isSome_iff (R F : ℕ) :
    (findBls5DiscriminantSquareRoot R F).isSome = true ↔ bls5DiscriminantIsSquare R F = true := by
  exact Option.isSome_ite

/-- The root-search `Option` is empty exactly when the executable square test rejects. This
equivalence does not require any quotient, size, or factorization hypotheses. -/
theorem findBls5DiscriminantSquareRoot_none_iff_square_false (R F : ℕ) :
    findBls5DiscriminantSquareRoot R F = none ↔ bls5DiscriminantIsSquare R F = false := by
  constructor
  · intro hnone
    cases htest : bls5DiscriminantIsSquare R F with
    | false => rfl
    | true =>
      have hsome := (findBls5DiscriminantSquareRoot_isSome_iff R F).2 htest
      rw [hnone] at hsome
      exact Bool.noConfusion hsome
  · intro hfalse
    cases hroot : findBls5DiscriminantSquareRoot R F with
    | none => rfl
    | some
      z =>
      have hsome : (findBls5DiscriminantSquareRoot R F).isSome = true := by
        rw [hroot]
        rfl
      have htest := (findBls5DiscriminantSquareRoot_isSome_iff R F).1 hsome
      rw [hfalse] at htest
      exact Bool.noConfusion htest

/-- Executable check of a supplied integer square root for the BLS5 discriminant.
This validates a certificate value; it does not search for a root. -/
def checkBls5DiscriminantSquareWitness (R F : ℕ) (z : ℤ) : Bool :=
  decide (bls5Discriminant R F = z ^ 2)

/-- The square-root checker accepts exactly when its supplied integer is a root. -/
theorem checkBls5DiscriminantSquareWitness_eq_true_iff (R F : ℕ) (z : ℤ) :
    checkBls5DiscriminantSquareWitness R F z = true ↔ bls5Discriminant R F = z ^ 2 := by
  simp only [checkBls5DiscriminantSquareWitness, decide_eq_true_eq]

/-- Executable arithmetic BLS5 branch: accept a zero quotient or a nonsquare discriminant. -/
def bls5PassesArithmeticCriterion (R F : ℕ) : Bool :=
  decide (bls5Quotient R F = 0) || decide (bls5DiscriminantIsSquare R F = false)

/-- The executable BLS5 arithmetic branch accepts exactly its zero-quotient or nonsquare cases. -/
theorem bls5PassesArithmeticCriterion_eq_true_iff (R F : ℕ) :
    bls5PassesArithmeticCriterion R F = true ↔
      bls5Quotient R F = 0 ∨ bls5DiscriminantIsSquare R F = false := by
  unfold bls5PassesArithmeticCriterion
  simp only [Bool.or_eq_true, decide_eq_true_eq]

/-- For positive `F`, the zero-quotient branch is exactly the boundary `R < 2 * F`. -/
theorem bls5Quotient_eq_zero_iff_lt {R F : ℕ} (hF : 0 < F) : bls5Quotient R F = 0 ↔ R < 2 * F := by
  unfold bls5Quotient
  exact Nat.div_eq_zero_iff_lt (Nat.mul_pos (by decide) hF)

/-- Every even natural number is divisible by two. This converts additive parity to divisibility
for the coprimality argument below. -/
private theorem two_dvd_of_even {n : ℕ} (h : Even n) : 2 ∣ n := by
  rcases h with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  calc
    n = a + a := ha
    _ = 2 * a := (Nat.two_mul a).symm

/-- If `F` is even and coprime to `R`, then `R` is odd. A common factor of two would contradict
`Nat.Coprime F R`. -/
theorem odd_of_even_factor_coprime {F R : ℕ} (hF : Even F) (hcop : Nat.Coprime F R) : Odd R := by
  rcases Nat.even_or_odd R with hR | hR
  · have hcommon : 2 ∣ F.gcd R := Nat.dvd_gcd (two_dvd_of_even hF) (two_dvd_of_even hR)
    rw [hcop] at hcommon
    exact False.elim ((by decide : ¬2 ∣ 1) hcommon)
  · exact hR

/-- Euclidean division gives the exact coefficients `s` and `r` in `R = 2 * F * s + r`. -/
theorem bls5Quotient_mul_add_remainder (R F : ℕ) :
    2 * F * bls5Quotient R F + bls5Remainder R F = R := by exact Nat.div_add_mod R (2 * F)

/-- In the zero-quotient branch, the remainder is `R` and the discriminant is the square `R²`.
This records why the BLS5 criterion must handle this boundary separately. -/
theorem bls5Discriminant_of_zero_quotient {R F : ℕ} (h : bls5Quotient R F = 0) :
    bls5Discriminant R F = (R : ℤ) ^ 2 := by
  have hdecomp := bls5Quotient_mul_add_remainder R F
  rw [h] at hdecomp
  have hrem : bls5Remainder R F = R := by simpa only [Nat.mul_zero, Nat.zero_add] using hdecomp
  unfold bls5Discriminant
  rw [hrem, h]
  simp only [Nat.cast_zero, mul_zero, sub_zero]

/-- The BLS5 remainder is strictly below `2 * F` whenever `F` is positive. -/
theorem bls5Remainder_lt {R F : ℕ} (hF : 0 < F) : bls5Remainder R F < 2 * F := by
  exact Nat.mod_lt R (Nat.mul_pos (by decide) hF)

/-- The Euclidean data agree with any decomposition `R = 2 * F * s + r` whose remainder is
below `2 * F`. -/
theorem bls5Coefficients_of_euclidean_form {R F s r : ℕ} (hR : R = 2 * F * s + r) (hr : r < 2 * F) :
    bls5Quotient R F = s ∧ bls5Remainder R F = r := by
  constructor
  · unfold bls5Quotient
    apply Nat.div_eq_of_lt_le
    · rw [hR]
      calc
        s * (2 * F) = 2 * F * s := by ring
        _ ≤ 2 * F * s + r := Nat.le_add_right _ _
    · rw [hR]
      calc
        2 * F * s + r < 2 * F * s + 2 * F := Nat.add_lt_add_left hr _
        _ = (s + 1) * (2 * F) := by ring
  · unfold bls5Remainder
    rw [hR, Nat.add_mod, Nat.mul_mod_right]
    simp only [Nat.zero_add, Nat.mod_eq_of_lt hr]

/-- An odd sum has factors with an even product, proved by splitting on the parity of the first
factor. -/
theorem even_mul_of_odd_add {u v : ℕ} (hsum : Odd (u + v)) : Even (u * v) := by
  rcases Nat.even_or_odd u with hu | hu
  · exact Even.mul_right hu v
  · exact Even.mul_left ((Nat.odd_add (m := u) (n := v)).mp hsum |>.mp hu) u

/-- If `R = uvF + u + v`, `uv` is even, and `u+v < 2F`, the BLS5 quotient and remainder are
`uv/2` and `u+v`. -/
theorem bls5Coefficients_of_factor_form {R F u v : ℕ} (hform : R = u * v * F + u + v)
    (huvEven : Even (u * v)) (hsum : u + v < 2 * F) :
    bls5Quotient R F = u * v / 2 ∧ bls5Remainder R F = u + v := by
  have hmod : u * v % 2 = 0 := Nat.even_iff.mp huvEven
  have hprod : 2 * (u * v / 2) = u * v := by
    calc
      2 * (u * v / 2) = 2 * (u * v / 2) + u * v % 2 := by rw [hmod, Nat.add_zero]
      _ = u * v := Nat.div_add_mod (u * v) 2
  have hlinear : R = 2 * F * (u * v / 2) + (u + v) := by
    calc
      R = u * v * F + u + v := hform
      _ = (2 * (u * v / 2)) * F + u + v := by rw [hprod]
      _ = 2 * F * (u * v / 2) + (u + v) := by ring
  exact bls5Coefficients_of_euclidean_form hlinear hsum

/-- Oddness of `u+v` supplies the even-product premise needed to recover the BLS5 coefficients. -/
theorem bls5Coefficients_of_factor_form_odd_sum {R F u v : ℕ} (hform : R = u * v * F + u + v)
    (hsumOdd : Odd (u + v)) (hsumBound : u + v < 2 * F) :
    bls5Quotient R F = u * v / 2 ∧ bls5Remainder R F = u + v :=
  bls5Coefficients_of_factor_form hform (even_mul_of_odd_add hsumOdd) hsumBound

/-- With even `F` and odd `R`, a factor form `R = uvF + u + v` forces `u+v` odd, so its
bounded sum gives the exact BLS5 quotient and remainder. -/
theorem bls5Coefficients_of_factor_form_of_even {R F u v : ℕ} (hF : Even F) (hR : Odd R)
    (hform : R = u * v * F + u + v) (hsumBound : u + v < 2 * F) :
    bls5Quotient R F = u * v / 2 ∧ bls5Remainder R F = u + v := by
  have hterm : Even (u * v * F) := Even.mul_left hF (u * v)
  have hform' : R = u * v * F + (u + v) := by
    calc
      R = (u * v * F + u) + v := hform
      _ = u * v * F + (u + v) := Nat.add_assoc _ _ _
  have hsumOdd : Odd (u + v) :=
    ((Nat.odd_add' (m := u * v * F) (n := u + v)).mp (hform'.symm ▸ hR)).mpr hterm
  exact bls5Coefficients_of_factor_form_odd_sum hform hsumOdd hsumBound

/-- If `R` is odd, its remainder modulo `2 * F` is odd because the quotient term is even. -/
theorem bls5Remainder_odd {R F : ℕ} (hR : Odd R) : Odd (bls5Remainder R F) := by
  have hterm : Even (2 * F * bls5Quotient R F) :=
    Even.mul_right (show Even (2 * F) from ⟨F, Nat.two_mul F⟩) (bls5Quotient R F)
  have hdecomp := bls5Quotient_mul_add_remainder R F
  have hsum : Odd (2 * F * bls5Quotient R F + bls5Remainder R F) := hdecomp.symm ▸ hR
  exact ((Nat.odd_add' (m := 2 * F * bls5Quotient R F) (n := bls5Remainder R F)).mp hsum).mpr hterm

/-- Under the standard BLS5 hypotheses, the Euclidean remainder is odd. -/
theorem bls5Remainder_odd_of_coprime {R F : ℕ} (hF : Even F) (hcop : Nat.Coprime F R) :
    Odd (bls5Remainder R F) :=
  bls5Remainder_odd (odd_of_even_factor_coprime hF hcop)

/-- If `u + v = 2 * F * a + r` with positive `a` and `r`, the expanded BLS5 upper bound is
bounded by the factor expression for `n`. The proof uses `u + v ≤ u * v + 1` for positive
factors and multiplies the Euclidean sum bound by `F * (F + 1)`. -/
theorem bls5ExpandedBound_le_factorExpression {F u v a r : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (ha : 1 ≤ a)
    (hr : 1 ≤ r) (hsum : u + v = 2 * F * a + r) :
    (F + 1) * (2 * F ^ 2 + (r - 1) * F + 1) ≤ F * (u * v * F + u + v) + 1 := by
  have hsumLower : 2 * F + r ≤ u + v := by
    calc
      2 * F + r = 2 * F * 1 + r := by ring
      _ ≤ 2 * F * a + r := Nat.add_le_add_right (Nat.mul_le_mul_left (2 * F) ha) r
      _ = u + v := hsum.symm
  have hsumProduct := Nat.mul_le_mul_right (F * (F + 1)) hsumLower
  have huvBound : u + v ≤ u * v + 1 := add_le_mul_add_one_of_pos hu hv
  have hmul := Nat.mul_le_mul_left (F ^ 2) huvBound
  have hplus :
    (F + 1) * (2 * F ^ 2 + (r - 1) * F + 1) + F ^ 2 ≤ F * (u * v * F + u + v) + 1 + F ^ 2 := by
    have hrEq : r - 1 + 1 = r := Nat.sub_add_cancel hr
    have hrepr :
      (F + 1) * (2 * F ^ 2 + (r - 1) * F + 1) + F ^ 2 =
        (2 * F + (r - 1 + 1)) * (F * (F + 1)) + 1 := by
      ring
    rw [hrEq] at hrepr
    calc
      _ = (2 * F + r) * (F * (F + 1)) + 1 := hrepr
      _ ≤ (u + v) * (F * (F + 1)) + 1 := Nat.add_le_add_right hsumProduct 1
      _ = F ^ 2 * (u + v) + F * (u + v) + 1 := by ring
      _ ≤ F ^ 2 * (u * v + 1) + F * (u + v) + 1 := Nat.add_le_add_right hmul (F * (u + v) + 1)
      _ = F * (u * v * F + u + v) + 1 + F ^ 2 := by ring
  exact Nat.le_of_add_le_add_right hplus

/-- Under the BLS5 factor form and expanded upper bound, the sum of the two factors is less than
`2 * F`. Otherwise Euclidean division by `2 * F` gives a positive quotient and an odd positive
remainder, forcing the factor expression to meet or exceed the assumed upper bound for `n`. -/
theorem bls5FactorSum_lt_two_F_of_expandedBound {n F u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (hF : 0 < F)
    (hodd : Odd (u + v)) (hfactor : n = F * (u * v * F + u + v) + 1)
    (hupper : n < (F + 1) * (2 * F ^ 2 + (((u * v * F + u + v) % (2 * F)) - 1) * F + 1)) :
    u + v < 2 * F := by
  have huvEven : Even (u * v) := even_mul_of_odd_add hodd
  have hmod : u * v % 2 = 0 := Nat.even_iff.mp huvEven
  have hhalf : 2 * (u * v / 2) = u * v := by
    calc
      2 * (u * v / 2) = 2 * (u * v / 2) + u * v % 2 := by rw [hmod, Nat.add_zero]
      _ = u * v := Nat.div_add_mod (u * v) 2
  have hprod : u * v * F = 2 * F * (u * v / 2) := by
    calc
      u * v * F = 2 * (u * v / 2) * F := by rw [hhalf]
      _ = 2 * F * (u * v / 2) := by ring
  have hform : u * v * F + u + v = 2 * F * (u * v / 2) + (u + v) := by
    rw [hprod]
    ring
  have hremEq : (u * v * F + u + v) % (2 * F) = (u + v) % (2 * F) := by
    rw [hform, Nat.add_mod, Nat.mul_mod_right]
    simp only [Nat.zero_add, Nat.mod_mod]
  have hupperSum := hupper
  rw [hremEq] at hupperSum
  by_contra hnot
  have hlarge : 2 * F ≤ u + v := Nat.le_of_not_gt hnot
  let a := (u + v) / (2 * F)
  let r := (u + v) % (2 * F)
  have hden : 0 < 2 * F := Nat.mul_pos (by decide) hF
  have haPos : 0 < a := by
    dsimp only [a]
    exact Nat.div_pos hlarge hden
  have ha : 1 ≤ a := haPos
  have hdecomp : u + v = 2 * F * a + r := by
    dsimp only [a, r]
    calc
      u + v = 2 * F * ((u + v) / (2 * F)) + (u + v) % (2 * F) :=
        (Nat.div_add_mod (u + v) (2 * F)).symm
      _ = 2 * F * ((u + v) / (2 * F)) + (u + v) % (2 * F) := rfl
  have hbaseEven : Even (2 * F * a) := ⟨F * a, by ring⟩
  have hoddRem : Odd r := by
    have hsumOdd : Odd (2 * F * a + r) := hdecomp ▸ hodd
    exact ((Nat.odd_add' (m := 2 * F * a) (n := r)).mp hsumOdd).mpr hbaseEven
  have hr : 1 ≤ r := by
    rcases hoddRem with ⟨k, hk⟩
    rw [hk]
    exact Nat.le_add_left 1 (2 * k)
  have hbound := bls5ExpandedBound_le_factorExpression hu hv ha hr hdecomp
  have hboundN : (F + 1) * (2 * F ^ 2 + (r - 1) * F + 1) ≤ n := by
    calc
      (F + 1) * (2 * F ^ 2 + (r - 1) * F + 1) ≤ F * (u * v * F + u + v) + 1 := hbound
      _ = n := hfactor.symm
  exact (Nat.not_lt_of_ge hboundN) (by simpa only [r] using hupperSum)

/-- For a factorization `n = F * R + 1` with `R = uvF + u + v`, the BLS5 upper bound forces
the Euclidean coefficients of `R` by `2 * F` to be `uv / 2` and `u + v`. Coprimality with even
`F` supplies the oddness needed both for the sum bound and for the coefficient reconstruction. -/
theorem bls5Coefficients_of_factorization_of_expandedBound {n R F u v : ℕ} (hFeven : Even F)
    (hFpos : 0 < F) (hcop : Nat.Coprime F R) (hform : R = u * v * F + u + v) (hn : n = F * R + 1)
    (hupper : n < (F + 1) * (2 * F ^ 2 + (R % (2 * F) - 1) * F + 1)) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    bls5Quotient R F = u * v / 2 ∧ bls5Remainder R F = u + v := by
  have hRodd := odd_of_even_factor_coprime hFeven hcop
  have hterm : Even (u * v * F) := Even.mul_left hFeven (u * v)
  have hform' : R = u * v * F + (u + v) := by
    calc
      R = (u * v * F + u) + v := hform
      _ = u * v * F + (u + v) := Nat.add_assoc _ _ _
  have hsumOdd : Odd (u + v) :=
    ((Nat.odd_add' (m := u * v * F) (n := u + v)).mp (hform'.symm ▸ hRodd)).mpr hterm
  have hnFactor : n = F * (u * v * F + u + v) + 1 := by
    rw [hform] at hn
    exact hn
  have hupperFactor := hupper
  rw [hform] at hupperFactor
  have hsumBound :=
    bls5FactorSum_lt_two_F_of_expandedBound hu hv hFpos hsumOdd hnFactor hupperFactor
  exact bls5Coefficients_of_factor_form_of_even hFeven hRodd hform hsumBound

/-- Once the BLS5 coefficients have been recovered and `u + v` is odd, the discriminant is the
square of the factor difference. Oddness makes `u * v` even, which accounts for the quotient by
two in the recovered coefficient. -/
theorem bls5Discriminant_eq_factorDifferenceSq {R F u v : ℕ} (hsumOdd : Odd (u + v))
    (hcoeff : bls5Quotient R F = u * v / 2 ∧ bls5Remainder R F = u + v) :
    bls5Discriminant R F = ((u : ℤ) - (v : ℤ)) ^ 2 := by
  have huvEven := even_mul_of_odd_add hsumOdd
  have hmod : u * v % 2 = 0 := Nat.even_iff.mp huvEven
  have hhalf : 2 * (u * v / 2) = u * v := by
    calc
      2 * (u * v / 2) = 2 * (u * v / 2) + u * v % 2 := by rw [hmod, Nat.add_zero]
      _ = u * v := Nat.div_add_mod (u * v) 2
  have hInt : (2 : ℤ) * ((u * v / 2 : ℕ) : ℤ) = (u * v : ℤ) := by exact_mod_cast hhalf
  have h8 : (8 : ℤ) * ((u * v / 2 : ℕ) : ℤ) = 4 * (u * v : ℤ) := by
    calc
      (8 : ℤ) * ((u * v / 2 : ℕ) : ℤ) = 4 * ((2 : ℤ) * ((u * v / 2 : ℕ) : ℤ)) := by ring
      _ = 4 * (u * v : ℤ) := congrArg (fun z : ℤ => 4 * z) hInt
  rcases hcoeff with ⟨hs, hr⟩
  unfold bls5Discriminant
  rw [hs, hr, h8, Nat.cast_add]
  ring

/-- Under the BLS5 expanded upper bound, a factor form forces the discriminant to be the square
of the factor difference. The coefficient recovery theorem supplies the exact quotient and
remainder consumed by the discriminant identity. -/
theorem bls5Discriminant_eq_factorDifferenceSq_of_expandedBound {n R F u v : ℕ} (hFeven : Even F)
    (hFpos : 0 < F) (hcop : Nat.Coprime F R) (hform : R = u * v * F + u + v) (hn : n = F * R + 1)
    (hupper : n < (F + 1) * (2 * F ^ 2 + (R % (2 * F) - 1) * F + 1)) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    bls5Discriminant R F = ((u : ℤ) - (v : ℤ)) ^ 2 := by
  have hcoeff :=
    bls5Coefficients_of_factorization_of_expandedBound hFeven hFpos hcop hform hn hupper hu hv
  have hRodd := odd_of_even_factor_coprime hFeven hcop
  have hterm : Even (u * v * F) := Even.mul_left hFeven (u * v)
  have hform' : R = u * v * F + (u + v) := by
    calc
      R = (u * v * F + u) + v := hform
      _ = u * v * F + (u + v) := Nat.add_assoc _ _ _
  have hsumOdd : Odd (u + v) :=
    ((Nat.odd_add' (m := u * v * F) (n := u + v)).mp (hform'.symm ▸ hRodd)).mpr hterm
  exact bls5Discriminant_eq_factorDifferenceSq hsumOdd hcoeff

/-- A composite input with the BLS prime-divisor lower bound and expanded upper bound has
positive BLS5 quotient and square discriminant. The factor shape and coefficient recovery provide
the concrete factors and discriminant root. -/
theorem bls5Coefficients_and_discriminant_of_composite_of_primeDivisorsAbove {n R F : ℕ}
    (hFeven : Even F) (hFpos : 0 < F) (hn : 1 < n) (hnot : ¬Nat.Prime n) (hcop : Nat.Coprime F R)
    (hdecomp : n = F * R + 1) (hupper : n < (F + 1) * (2 * F ^ 2 + (R % (2 * F) - 1) * F + 1))
    (hlarge : PrimeDivisorsAbove n F) :
    ∃ u v : ℕ,
      1 ≤ u ∧
        1 ≤ v ∧
        bls5Quotient R F = u * v / 2 ∧
        bls5Remainder R F = u + v ∧ bls5Discriminant R F = ((u : ℤ) - (v : ℤ)) ^ 2 := by
  obtain ⟨u, v, hfactor, hu, hv⟩ :=
    exists_bls_factorization_of_composite_of_primeDivisorsAbove hn hnot hlarge
  have hfactorR : n = F * (u * v * F + u + v) + 1 := by
    rw [hfactor]
    ring
  have hform : R = u * v * F + u + v := by
    apply Nat.eq_of_mul_eq_mul_left hFpos
    apply Nat.add_right_cancel
    exact hdecomp.symm.trans hfactorR
  have hcoeff :=
    bls5Coefficients_of_factorization_of_expandedBound hFeven hFpos hcop hform hdecomp hupper hu hv
  have hRodd := odd_of_even_factor_coprime hFeven hcop
  have hterm : Even (u * v * F) := Even.mul_left hFeven (u * v)
  have hform' : R = u * v * F + (u + v) := by
    calc
      R = (u * v * F + u) + v := hform
      _ = u * v * F + (u + v) := Nat.add_assoc _ _ _
  have hsumOdd : Odd (u + v) :=
    ((Nat.odd_add' (m := u * v * F) (n := u + v)).mp (hform'.symm ▸ hRodd)).mpr hterm
  have hdiscriminant := bls5Discriminant_eq_factorDifferenceSq hsumOdd hcoeff
  exact ⟨u, v, hu, hv, hcoeff.1, hcoeff.2, hdiscriminant⟩

/-- A square BLS5 discriminant reconstructs nonnegative integer roots whose sum is the
remainder and whose product is twice the quotient. -/
theorem bls5QuadraticRoots_of_discriminant_eq_square (R F : ℕ) (z : ℤ)
    (hsquare : bls5Discriminant R F = z ^ 2) :
    ∃ u v : ℤ,
      0 ≤ u ∧
        0 ≤ v ∧
        (bls5Remainder R F : ℤ) = u + v ∧ z = u - v ∧ 2 * (bls5Quotient R F : ℤ) = u * v := by
  have hid : z ^ 2 + 4 * (2 * (bls5Quotient R F : ℤ)) = (bls5Remainder R F : ℤ) ^ 2 := by
    unfold bls5Discriminant at hsquare
    rw [← hsquare]
    ring
  have hdiff : (bls5Remainder R F : ℤ) ^ 2 - z ^ 2 = 4 * (2 * (bls5Quotient R F : ℤ)) := by
    calc
      (bls5Remainder R F : ℤ) ^ 2 - z ^ 2 = (z ^ 2 + 4 * (2 * (bls5Quotient R F : ℤ))) - z ^ 2 := by
        rw [← hid]
      _ = 4 * (2 * (bls5Quotient R F : ℤ)) := by ring
  have heven : Even ((bls5Remainder R F : ℤ) ^ 2 - z ^ 2) := by
    rw [hdiff]
    exact ⟨2 * (2 * (bls5Quotient R F : ℤ)), by ring⟩
  have hsq : Even ((bls5Remainder R F : ℤ) ^ 2) ↔ Even (z ^ 2) := (Int.even_sub).mp heven
  have hparity : Even (bls5Remainder R F : ℤ) ↔ Even z := by
    constructor
    · intro hr
      have hr2 : Even ((bls5Remainder R F : ℤ) ^ 2) := (Int.even_pow).mpr ⟨hr, by decide⟩
      have hz2 : Even (z ^ 2) := hsq.mp hr2
      exact ((Int.even_pow).mp hz2).1
    · intro hz
      have hz2 : Even (z ^ 2) := (Int.even_pow).mpr ⟨hz, by decide⟩
      have hr2 : Even ((bls5Remainder R F : ℤ) ^ 2) := hsq.mpr hz2
      exact ((Int.even_pow).mp hr2).1
  have hrootParity : Even ((bls5Remainder R F : ℤ) + z) ∧ Even ((bls5Remainder R F : ℤ) - z) :=
    ⟨Int.even_add.mpr hparity, Int.even_sub.mpr hparity⟩
  have hbound : -(bls5Remainder R F : ℤ) ≤ z ∧ z ≤ (bls5Remainder R F : ℤ) := by
    have hsqBound : z ^ 2 ≤ (bls5Remainder R F : ℤ) ^ 2 := by
      calc
        z ^ 2 ≤ z ^ 2 + 4 * (2 * (bls5Quotient R F : ℤ)) :=
          Int.le_add_of_nonneg_right
            (Int.mul_nonneg (by decide)
              (Int.mul_nonneg (by decide) (Int.natCast_nonneg (bls5Quotient R F))))
        _ = (bls5Remainder R F : ℤ) ^ 2 := hid
    have hremNonneg : 0 ≤ (bls5Remainder R F : ℤ) := Int.natCast_nonneg _
    exact abs_le_of_sq_le_sq' hsqBound hremNonneg
  exact
    quadratic_roots_of_discriminant_identity (bls5Remainder R F : ℤ) (2 * (bls5Quotient R F : ℤ)) z
      hid hrootParity hbound.1 hbound.2

/-- A positive quotient and square BLS5 discriminant produce a nontrivial factorization of
`n = F * R + 1`. The quadratic roots recover the two factors after using `uv = 2s`. -/
theorem bls5Factorization_of_positive_quotient_and_discriminant_square {n F R : ℕ}
    (hdecomp : n = F * R + 1) (hquotient : 0 < bls5Quotient R F) (z : ℤ)
    (hsquare : bls5Discriminant R F = z ^ 2) :
    ∃ u v : ℕ, 1 ≤ u ∧ 1 ≤ v ∧ n = (u * F + 1) * (v * F + 1) := by
  obtain ⟨u, v, hu0, hv0, hrEq, _, hprod⟩ :=
    bls5QuadraticRoots_of_discriminant_eq_square R F z hsquare
  have hquotientInt : 0 < (bls5Quotient R F : ℤ) := by exact_mod_cast hquotient
  have hprodPos : 0 < u * v := by
    rw [← hprod]
    exact mul_pos (by decide) hquotientInt
  have huPos : 0 < u := by
    by_contra huNot
    have huZero : u = 0 := le_antisymm (Int.not_lt.mp huNot) hu0
    rw [huZero, Int.zero_mul] at hprodPos
    exact (Int.ne_of_gt hprodPos) rfl
  have hvPos : 0 < v := by
    by_contra hvNot
    have hvZero : v = 0 := le_antisymm (Int.not_lt.mp hvNot) hv0
    rw [hvZero, Int.mul_zero] at hprodPos
    exact (Int.ne_of_gt hprodPos) rfl
  let uNat := u.toNat
  let vNat := v.toNat
  have huCast : (uNat : ℤ) = u := Int.toNat_of_nonneg hu0
  have hvCast : (vNat : ℤ) = v := Int.toNat_of_nonneg hv0
  have huNat : 1 ≤ uNat := Nat.succ_le_iff.mpr (Int.pos_iff_toNat_pos.mp huPos)
  have hvNat : 1 ≤ vNat := Nat.succ_le_iff.mpr (Int.pos_iff_toNat_pos.mp hvPos)
  have hremNat : bls5Remainder R F = uNat + vNat := by
    rw [← huCast, ← hvCast] at hrEq
    exact_mod_cast hrEq
  have hprodNat : 2 * bls5Quotient R F = uNat * vNat := by
    rw [← huCast, ← hvCast] at hprod
    exact_mod_cast hprod
  have hcofactor : R = uNat * vNat * F + uNat + vNat := by
    have hdivision := (bls5Quotient_mul_add_remainder R F).symm
    rw [hremNat] at hdivision
    calc
      R = 2 * F * bls5Quotient R F + (uNat + vNat) := hdivision
      _ = uNat * vNat * F + uNat + vNat := by
        rw [← hprodNat]
        ring
  refine ⟨uNat, vNat, huNat, hvNat, ?_⟩
  calc
    n = F * R + 1 := hdecomp
    _ = F * (uNat * vNat * F + uNat + vNat) + 1 := by rw [hcofactor]
    _ = (uNat * F + 1) * (vNat * F + 1) := by ring

/-- A positive BLS5 quotient and square discriminant prove compositeness. The factorization
above gives a proper divisor, with both reconstructed factors at least two. -/
theorem bls5NotPrime_of_positive_quotient_and_discriminant_square {n F R : ℕ} (hn : 1 < n)
    (hF : 0 < F) (hdecomp : n = F * R + 1) (hquotient : 0 < bls5Quotient R F) (z : ℤ)
    (hsquare : bls5Discriminant R F = z ^ 2) : ¬Nat.Prime n := by
  obtain ⟨u, v, hu, hv, hfactor⟩ :=
    bls5Factorization_of_positive_quotient_and_discriminant_square hdecomp hquotient z hsquare
  have huProd : 1 ≤ u * F := Nat.succ_le_iff.mpr (Nat.mul_pos (Nat.zero_lt_of_lt hu) hF)
  have hvProd : 1 ≤ v * F := Nat.succ_le_iff.mpr (Nat.mul_pos (Nat.zero_lt_of_lt hv) hF)
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
        have hmul := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_lt_of_le (by decide : 1 < 2) hv2) huPos
        simpa only [Nat.mul_one] using hmul
      _ = n := hfactor.symm
  exact
    (Nat.not_prime_iff_exists_dvd_lt (Nat.succ_le_iff.mpr hn)).mpr
      ⟨u * F + 1, ⟨v * F + 1, hfactor⟩, hu2, huLt⟩

/-- Under the BLS5 factor-divisor and expanded-bound hypotheses, primality is equivalent to a
zero quotient or a nonsquare discriminant. The zero-quotient branch is kept explicit because a
square discriminant there does not imply compositeness. -/
theorem bls5_prime_iff_zero_quotient_or_nonsquare {n R F : ℕ} (hFeven : Even F) (hFpos : 0 < F)
    (hn : 1 < n) (hcop : Nat.Coprime F R) (hdecomp : n = F * R + 1)
    (hupper : n < (F + 1) * (2 * F ^ 2 + (R % (2 * F) - 1) * F + 1))
    (hlarge : PrimeDivisorsAbove n F) :
    Nat.Prime n ↔ bls5Quotient R F = 0 ∨ ∀ z : ℤ, bls5Discriminant R F ≠ z ^ 2 := by
  constructor
  · intro hnprime
    by_cases hzero : bls5Quotient R F = 0
    · exact Or.inl hzero
    · right
      intro z hsquare
      have hnotprime :=
        bls5NotPrime_of_positive_quotient_and_discriminant_square (Nat.succ_le_iff.mpr hn) hFpos
          hdecomp (Nat.pos_of_ne_zero hzero) z hsquare
      exact hnotprime hnprime
  · intro hcriterion
    by_contra hnotprime
    obtain ⟨u, v, hu, hv, hquotient, hremainder, hdiscriminant⟩ :=
      bls5Coefficients_and_discriminant_of_composite_of_primeDivisorsAbove hFeven hFpos hn hnotprime
        hcop hdecomp hupper hlarge
    rcases hcriterion with hzero | hnsquare
    · have hremOdd := bls5Remainder_odd_of_coprime hFeven hcop
      rw [hremainder] at hremOdd
      have huvEven := even_mul_of_odd_add hremOdd
      have huvPos : 0 < u * v := Nat.mul_pos (Nat.zero_lt_of_lt hu) (Nat.zero_lt_of_lt hv)
      have huvDiv : 2 ∣ u * v := Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp huvEven)
      have huvLower : 2 ≤ u * v := Nat.le_of_dvd huvPos huvDiv
      have hquotientPos : 0 < bls5Quotient R F := by
        rw [hquotient]
        exact Nat.div_pos huvLower (by decide)
      rw [hzero] at hquotientPos
      exact (Nat.lt_irrefl 0) hquotientPos
    · exact hnsquare ((u : ℤ) - v) hdiscriminant

/-- Under the BLS5 number-theoretic hypotheses, the executable arithmetic branch accepts exactly
the prime inputs. -/
theorem bls5_prime_iff_passesArithmeticCriterion {n R F : ℕ} (hFeven : Even F) (hFpos : 0 < F)
    (hn : 1 < n) (hcop : Nat.Coprime F R) (hdecomp : n = F * R + 1)
    (hupper : n < (F + 1) * (2 * F ^ 2 + (R % (2 * F) - 1) * F + 1))
    (hlarge : PrimeDivisorsAbove n F) : Nat.Prime n ↔ bls5PassesArithmeticCriterion R F = true := by
  rw [bls5PassesArithmeticCriterion_eq_true_iff, bls5DiscriminantIsSquare_eq_false_iff]
  exact bls5_prime_iff_zero_quotient_or_nonsquare hFeven hFpos hn hcop hdecomp hupper hlarge

/-- A BLS5 certificate reuses verified prime powers and witnesses from the ordinary BLS
certificate, and supplies the cofactor and arithmetic data required by the extended criterion.
The checker below requires this cofactor to be the one in the partial factorization. -/
structure BLS5Certificate where
  /-- Integer whose primality is certified. -/
  n : ℕ
  /-- Distinct prime powers dividing `n - 1`, together with their remaining cofactor. -/
  factorization : PartialFactorizationData
  /-- One BLS witness base for every prime key in `factorization`. -/
  witnesses : List (ℕ × ℕ)
  /-- The cofactor `R` in `n = F * R + 1`, where `F` is the known prime-power product. -/
  cofactor : ℕ
  deriving DecidableEq, Repr

/-- Check all arithmetic hypotheses for BLS5, the reused factor and witness certificates, and
the executable quotient/discriminant criterion. -/
def checkBLS5Certificate (c : BLS5Certificate) : Bool :=
  decide (5 ≤ c.n) && decide (c.cofactor = c.factorization.cofactor) &&
    decide (c.n = factorProduct c.factorization.factors * c.cofactor + 1) &&
    decide (Even (factorProduct c.factorization.factors)) &&
    decide (Nat.Coprime (factorProduct c.factorization.factors) c.cofactor) &&
    decide
      (c.n <
        (factorProduct c.factorization.factors + 1) *
          (2 * factorProduct c.factorization.factors ^ 2 +
            (c.cofactor % (2 * factorProduct c.factorization.factors) - 1) *
              factorProduct c.factorization.factors +
            1)) &&
    checkPartialFactorization c.n c.factorization &&
    checkWitnesses c.n c.factorization c.witnesses &&
    bls5PassesArithmeticCriterion c.cofactor (factorProduct c.factorization.factors)

/-- Proof-relevant meaning of an accepted BLS5 certificate. -/
def ValidBLS5Certificate (c : BLS5Certificate) : Prop :=
  5 ≤ c.n ∧
    c.cofactor = c.factorization.cofactor ∧
    c.n = factorProduct c.factorization.factors * c.cofactor + 1 ∧
    Even (factorProduct c.factorization.factors) ∧
    Nat.Coprime (factorProduct c.factorization.factors) c.cofactor ∧
    c.n <
      (factorProduct c.factorization.factors + 1) *
        (2 * factorProduct c.factorization.factors ^ 2 +
          (c.cofactor % (2 * factorProduct c.factorization.factors) - 1) *
            factorProduct c.factorization.factors +
          1) ∧
    ValidPartialFactorization c.n c.factorization ∧
    ValidWitnesses c.n c.factorization c.witnesses ∧
    bls5PassesArithmeticCriterion c.cofactor (factorProduct c.factorization.factors) = true

/-- The executable BLS5 checker accepts exactly certificates satisfying its documented fields. -/
theorem checkBLS5Certificate_eq_true_iff (c : BLS5Certificate) :
    checkBLS5Certificate c = true ↔ ValidBLS5Certificate c := by
  simp only [checkBLS5Certificate, ValidBLS5Certificate, ValidPartialFactorization, ValidWitnesses,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- Every accepted BLS5 certificate proves its original input prime. Factor and witness
verification imply `PrimeDivisorsAbove`; the BLS5 arithmetic equivalence then applies to the
supplied cofactor and factor product. -/
theorem prime_of_valid_bls5_certificate (c : BLS5Certificate)
    (hcheck : checkBLS5Certificate c = true) : Nat.Prime c.n := by
  rcases (checkBLS5Certificate_eq_true_iff c).mp hcheck with
    ⟨hn5, _, hdecomp, hFeven, hcop, hupper, hfactor, hwitness, harithmetic⟩
  have hn : 1 < c.n := lt_of_lt_of_le (by decide : 1 < 5) hn5
  have hFpos : 0 < factorProduct c.factorization.factors :=
    Nat.zero_lt_of_lt (checkPartialFactorization_eq_true_iff c.n c.factorization |>.mp hfactor).1
  have hlarge :=
    primeDivisorsAbove_of_valid_bls_data hn c.factorization c.witnesses hfactor hwitness
  exact
    (bls5_prime_iff_passesArithmeticCriterion hFeven hFpos hn hcop hdecomp hupper hlarge).2
      harithmetic

end PseudoPrime.PrimeTest.BLS
