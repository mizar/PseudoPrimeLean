/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import PseudoPrime.PrimeTest.APRCL.CyclotomicRing
import PseudoPrime.PrimeTest.APRCL.Parameters

/-!
# Finite Jacobi-sum coefficient aggregation

This file groups a finite sum of root powers by their exponents modulo a positive period.
For APR-CL, the input exponent is `a * x + b * f_q x`, where `f_q x` is supplied by the
auxiliary-prime discrete-log table. The proved identity is the coefficient-counting step from
that exponent list to the corresponding finite Jacobi-sum formula; constructing the logarithm
data and reducing the resulting polynomial in the cyclotomic quotient remain separate steps.
-/

namespace PseudoPrime.PrimeTest.APRCL

/-- Construct the multiplicative character whose value at a selected generator is the supplied
root of unity. The period divides `q - 1`, so the root satisfies the order required by Mathlib's
`MulChar.ofRootOfUnity`; the discrete-log table proves that the selected generator spans all
units modulo the prime `q`. -/
noncomputable def jacobiPowerCharacter {q P : ℕ} {R : Type*} [CommRing R] (hq : Nat.Prime q)
    (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ) (hζ : (ζ : R) ^ P = 1)
    (hP : P ∣ q - 1) : MulChar (ZMod q) R := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hperiod : (ζ : R) ^ (q - 1) = 1 := by
    obtain ⟨m, hm⟩ := hP
    rw [hm, pow_mul, hζ]
    exact one_pow m
  have hcard : ζ ^ Fintype.card (ZMod q)ˣ = 1 := by
    apply Units.ext
    change (ζ : R) ^ Fintype.card (ZMod q)ˣ = 1
    rw [ZMod.card_units]
    exact hperiod
  have hroot : ζ ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R := (mem_rootsOfUnity _ ζ).mpr hcard
  have hspan : ∀ x : (ZMod q)ˣ, x ∈ Subgroup.zpowers g := by
    intro x
    have hsome := discreteLogTableSearch_isSome_of_prime hq g x hg
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨_, hpow⟩ := discreteLogTableSearch_some_spec he
    rw [← hpow]
    exact Subgroup.npow_mem_zpowers g e
  exact MulChar.ofRootOfUnity hroot hspan

/-- The constructed character takes the prescribed value at the primitive-root generator. -/
theorem jacobiPowerCharacter_apply_generator {q P : ℕ} {R : Type*} [CommRing R] (hq : Nat.Prime q)
    (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ) (hζ : (ζ : R) ^ P = 1)
    (hP : P ∣ q - 1) : jacobiPowerCharacter hq g hg ζ hζ hP g = (ζ : R) := by
  unfold jacobiPowerCharacter
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hperiod : (ζ : R) ^ (q - 1) = 1 := by
    obtain ⟨m, hm⟩ := hP
    rw [hm, pow_mul, hζ]
    exact one_pow m
  have hcard : ζ ^ Fintype.card (ZMod q)ˣ = 1 := by
    apply Units.ext
    change (ζ : R) ^ Fintype.card (ZMod q)ˣ = 1
    rw [ZMod.card_units]
    exact hperiod
  have hroot : ζ ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R := (mem_rootsOfUnity _ ζ).mpr hcard
  have hspan : ∀ x : (ZMod q)ˣ, x ∈ Subgroup.zpowers g := by
    intro x
    have hsome := discreteLogTableSearch_isSome_of_prime hq g x hg
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨_, hpow⟩ := discreteLogTableSearch_some_spec he
    rw [← hpow]
    exact Subgroup.npow_mem_zpowers g e
  exact MulChar.ofRootOfUnity_spec hroot hspan

/-- Evaluation on every power of the selected generator is the corresponding root power.
This is the term-level interface needed to compare the executable discrete-log exponent with a
multiplicative character inside the Jacobi sum. -/
theorem jacobiPowerCharacter_apply_generator_pow {q P x : ℕ} {R : Type*} [CommRing R]
    (hq : Nat.Prime q) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hP : P ∣ q - 1) :
    jacobiPowerCharacter hq g hg ζ hζ hP ((g ^ x : (ZMod q)ˣ) : ZMod q) = (ζ : R) ^ x := by
  change jacobiPowerCharacter hq g hg ζ hζ hP ((g : ZMod q) ^ x) = _
  rw [map_pow]
  rw [jacobiPowerCharacter_apply_generator hq g hg ζ hζ hP]

/-- A successful executable discrete-log lookup is evaluated by the character as the matching
root power. This connects the Option table certificate to the mathematical character value. -/
theorem jacobiPowerCharacter_apply_of_discreteLogTableSearch {q P e : ℕ} {R : Type*} [CommRing R]
    (hq : Nat.Prime q) (g target : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hP : P ∣ q - 1) (hlookup : discreteLogTableSearch g target = some e) :
    jacobiPowerCharacter hq g hg ζ hζ hP (target : ZMod q) = (ζ : R) ^ e := by
  obtain ⟨_, hpow⟩ := discreteLogTableSearch_some_spec hlookup
  rw [← hpow]
  exact jacobiPowerCharacter_apply_generator_pow hq g hg ζ hζ hP

/-- A ring endomorphism sending the chosen root to its `i`-th power sends the constructed
character to its `i`-th power. Every unit is a generator power by the certified log search. -/
theorem jacobiPowerCharacter_ringHomComp_eq_pow {q P : ℕ} {R : Type*} [CommRing R]
    (hq : Nat.Prime q) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hP : P ∣ q - 1) (f : R →+* R) (i : ℕ) (hf : f (ζ : R) = (ζ : R) ^ i) :
    (jacobiPowerCharacter hq g hg ζ hζ hP).ringHomComp f =
      jacobiPowerCharacter hq g hg ζ hζ hP ^ i := by
  apply MulChar.ext
  intro x
  have hsome := discreteLogTableSearch_isSome_of_prime hq g x hg
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨_, hpow⟩ := discreteLogTableSearch_some_spec he
  rw [← hpow]
  rw [MulChar.ringHomComp_apply, MulChar.pow_apply_coe]
  rw [jacobiPowerCharacter_apply_generator_pow hq g hg ζ hζ hP]
  rw [map_pow, hf]
  ring

/-- The constructed character has period dividing the supplied root period. -/
theorem jacobiPowerCharacter_pow_period {q P : ℕ} {R : Type*} [CommRing R] (hq : Nat.Prime q)
    (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ) (hζ : (ζ : R) ^ P = 1)
    (hP : P ∣ q - 1) : jacobiPowerCharacter hq g hg ζ hζ hP ^ P = 1 := by
  apply MulChar.ext
  intro x
  have hsome := discreteLogTableSearch_isSome_of_prime hq g x hg
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨_, hpow⟩ := discreteLogTableSearch_some_spec he
  rw [← hpow]
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe,
    jacobiPowerCharacter_apply_generator_pow hq g hg ζ hζ hP]
  rw [← pow_mul, Nat.mul_comm, pow_mul, hζ, one_pow]

/-- Congruent exponents modulo the root period yield the same powered character. -/
theorem jacobiPowerCharacter_pow_eq_of_zmod {q P a b : ℕ} {R : Type*} [CommRing R]
    (hq : Nat.Prime q) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hP : P ∣ q - 1) (h : (a : ZMod P) = (b : ZMod P)) :
    jacobiPowerCharacter hq g hg ζ hζ hP ^ a = jacobiPowerCharacter hq g hg ζ hζ hP ^ b := by
  have hmod : a % P = b % P := (ZMod.natCast_eq_natCast_iff' a b P).mp h
  rw [pow_eq_pow_mod a (jacobiPowerCharacter_pow_period hq g hg ζ hζ hP),
    pow_eq_pow_mod b (jacobiPowerCharacter_pow_period hq g hg ζ hζ hP), hmod]

/-- The same root-power action multiplies both character exponents in a Jacobi sum. -/
theorem jacobiPowerCharacter_jacobiSum_ringHomComp {q P a b : ℕ} {R : Type*} [CommRing R]
    [Fintype (ZMod q)] (hq : Nat.Prime q) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hP : P ∣ q - 1) (f : R →+* R) (i : ℕ) (hf : f (ζ : R) = (ζ : R) ^ i) :
    f
        (jacobiSum (jacobiPowerCharacter hq g hg ζ hζ hP ^ a)
          (jacobiPowerCharacter hq g hg ζ hζ hP ^ b)) =
      jacobiSum (jacobiPowerCharacter hq g hg ζ hζ hP ^ (i * a))
        (jacobiPowerCharacter hq g hg ζ hζ hP ^ (i * b)) := by
  rw [← jacobiSum_ringHomComp]
  rw [← MulChar.ringHomComp_pow, ← MulChar.ringHomComp_pow]
  rw [jacobiPowerCharacter_ringHomComp_eq_pow hq g hg ζ hζ hP f i hf]
  rw [pow_mul, pow_mul]

/-- Count how often a bounded exponent value occurs in a finite input set. -/
def jacobiExponentCount {α : Type*} [DecidableEq α] (xs : Finset α) (exponent : α → ℕ) (r : ℕ) :
    ℕ :=
  (xs.filter (fun x => exponent x = r)).card

/-- Evaluate an exponent histogram as a finite linear combination of powers of `z`. The period
`P` bounds the histogram indices, and the count is a natural-number coefficient acting by `nsmul`.
-/
def jacobiCoefficientSum {α : Type*} [DecidableEq α] (P : ℕ) (xs : Finset α) (exponent : α → ℕ)
    {R : Type*} [Semiring R] (z : R) : R :=
  ∑ r ∈ Finset.range P, jacobiExponentCount xs exponent r • z ^ r

/-- Reindex the bounded coefficient formula by `Fin P`. This exposes the exact finite shape used
by the fixed-size cyclotomic coefficient array, with each histogram count retained as a scalar. -/
theorem jacobiCoefficientSum_eq_fin_sum {α : Type*} [DecidableEq α] (P : ℕ) (xs : Finset α)
    (exponent : α → ℕ) {R : Type*} [Semiring R] (z : R) :
    jacobiCoefficientSum P xs exponent z =
      ∑ r : Fin P, jacobiExponentCount xs exponent r.val • z ^ r.val := by
  rw [jacobiCoefficientSum]
  rw [← Fin.sum_univ_eq_sum_range (fun r : ℕ => jacobiExponentCount xs exponent r • z ^ r) P]

/-- Grouping a finite sum by its bounded exponent preserves its value. The hypothesis states that
every exponent on the input set lies in the represented range; `Finset.sum_fiberwise_of_maps_to`
then identifies the grouped sum with the direct sum term by term. -/
theorem jacobiCoefficientSum_eq_direct {α : Type*} [DecidableEq α] (P : ℕ) (xs : Finset α)
    (exponent : α → ℕ) (hbound : ∀ x ∈ xs, exponent x < P) {R : Type*} [Semiring R] (z : R) :
    jacobiCoefficientSum P xs exponent z = ∑ x ∈ xs, z ^ exponent x := by
  unfold jacobiCoefficientSum jacobiExponentCount
  calc
    _ = ∑ r ∈ Finset.range P, ∑ x ∈ xs with exponent x = r, z ^ r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_const]
    _ = ∑ r ∈ Finset.range P, ∑ x ∈ xs with exponent x = r, z ^ exponent x := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x ∈ xs, z ^ exponent x := by
      exact
        Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_range.mpr (hbound x hx))
          (fun x => z ^ exponent x)

/-- The reduced Jacobi exponent `(a*x + b*f(x)) mod P` is in the required coefficient range
whenever the period is positive. -/
theorem jacobiExponent_mod_lt {P a b x fx : ℕ} (hP : 0 < P) : (a * x + b * fx) % P < P :=
  Nat.mod_lt _ hP

/-- Compute one reduced Jacobi exponent from the optional discrete-log table lookup for its
target unit. A missing logarithm remains `none`, so a failed lookup cannot silently introduce a
default exponent into the Jacobi sum. -/
def jacobiExponentFromTable {q P : ℕ} (g target : (ZMod q)ˣ) (a b x : ℕ) : Option ℕ :=
  (discreteLogTableSearch g target).map (fun fx => (a * x + b * fx) % P)

/-- A returned Jacobi exponent records the table's logarithm range and power equation as well as
the reduced arithmetic exponent. This is the pointwise interface used when assembling the finite
Jacobi exponent list from successful table lookups. -/
theorem jacobiExponentFromTable_some_spec {q P a b x e : ℕ} (g target : (ZMod q)ˣ)
    (h : jacobiExponentFromTable (P := P) g target a b x = some e) :
    ∃ fx,
      discreteLogTableSearch g target = some fx ∧
        fx < q - 1 ∧ g ^ fx = target ∧ e = (a * x + b * fx) % P := by
  unfold jacobiExponentFromTable at h
  cases htable : discreteLogTableSearch g target with
  | none =>
    rw [htable] at h
    cases h
  | some fx =>
    rw [htable] at h
    injection h with he
    obtain ⟨hbound, hpow⟩ := discreteLogTableSearch_some_spec htable
    exact ⟨fx, rfl, hbound, hpow, he.symm⟩

/-- Search a finite ordered list of Jacobi inputs using the discrete-log power table. The result
is `none` if any required logarithm is missing; a successful result stores one reduced exponent
for each input, in the original order. -/
def jacobiExponentTableSearch {q P : ℕ} (g : (ZMod q)ˣ) (a b : ℕ) :
    List (ℕ × (ZMod q)ˣ) → Option (List ℕ)
  | [] => some []
  | entry :: entries =>
    match jacobiExponentFromTable (P := P) g entry.2 a b entry.1 with
    | none => none
    | some exponent =>
      match jacobiExponentTableSearch (P := P) g a b entries with
      | none => none
      | some exponents => some (exponent :: exponents)

/-- A successful batch exponent search gives a matching discrete logarithm certificate for every
input entry and preserves list order. -/
theorem jacobiExponentTableSearch_some_spec {q P a b : ℕ} (g : (ZMod q)ˣ)
    {entries : List (ℕ × (ZMod q)ˣ)} {exponents : List ℕ}
    (h : jacobiExponentTableSearch (P := P) g a b entries = some exponents) :
    List.Forall₂
      (fun entry exponent =>
        ∃ fx,
          discreteLogTableSearch g entry.2 = some fx ∧
            fx < q - 1 ∧ g ^ fx = entry.2 ∧ exponent = (a * entry.1 + b * fx) % P)
      entries exponents := by
  induction entries generalizing exponents with
  | nil =>
    change some [] = some exponents at h
    injection h with hexponents
    subst exponents
    exact List.Forall₂.nil
  | cons entry entries
    ih =>
    change
      (match jacobiExponentFromTable (P := P) g entry.2 a b entry.1 with
        | none => none
        | some exponent =>
          match jacobiExponentTableSearch (P := P) g a b entries with
          | none => none
          | some exponents => some (exponent :: exponents)) =
        some exponents at h
    split at h
    · cases h
    · split at h
      · cases h
      · injection h with hEq
        subst exponents
        refine List.Forall₂.cons ?_ ?_
        · exact
            jacobiExponentFromTable_some_spec (P := P) g entry.2 (a := a) (b := b) (x := entry.1)
              (by assumption)
        · exact ih (by assumption)

/-- Lift `1 - g^x` to a unit when its natural representative is coprime to `q`. The coprimality
test is executable for every modulus, and failure remains `none`; the prime-modulus coverage
theorem below proves success on the Jacobi index range for a primitive root. -/
def jacobiOneSubUnitSearch {q : ℕ} (g : (ZMod q)ˣ) (x : ℕ) : Option (ZMod q)ˣ :=
  let y := 1 - (g : ZMod q) ^ x
  if h : Nat.Coprime y.val q then some (ZMod.unitOfCoprime y.val h) else none

/-- For a primitive root modulo a prime, every exponent strictly between zero and `q - 1` has
`1 - g^x` nonzero. Its representative is therefore coprime to `q`, so the executable unit lift
returns the required Jacobi logarithm target. -/
theorem jacobiOneSubUnitSearch_some_of_primitiveRoot {q : ℕ} (hq : Nat.Prime q) (g : (ZMod q)ˣ)
    (hg : IsPrimitiveRoot g (q - 1)) {x : ℕ} (hx0 : 0 < x) (hx : x < q - 1) :
    ∃ target,
      jacobiOneSubUnitSearch g x = some target ∧ (target : ZMod q) = 1 - (g : ZMod q) ^ x := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have hpowNe : (g : ZMod q) ^ x ≠ 1 := by
    intro hpow
    have hunit : g ^ x = 1 := Units.ext hpow
    have hdiv : q - 1 ∣ x := hg.dvd_of_pow_eq_one x hunit
    have hle : q - 1 ≤ x := Nat.le_of_dvd hx0 hdiv
    exact (Nat.not_lt_of_ge hle) hx
  have hy : 1 - (g : ZMod q) ^ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hpowNe)
  let y : ZMod q := 1 - (g : ZMod q) ^ x
  have hyval : y.val ≠ 0 := by
    intro hzero
    have hyZero : y = 0 := by
      calc
        y = (y.val : ZMod q) := (ZMod.natCast_zmod_val y).symm
        _ = 0 := by
          rw [hzero]
          exact Nat.cast_zero
    apply hy
    exact hyZero
  have hnotdvd : ¬q ∣ y.val := by
    intro hdvd
    have hle : q ≤ y.val := Nat.le_of_dvd (Nat.pos_of_ne_zero hyval) hdvd
    exact (Nat.not_lt_of_ge hle) (ZMod.val_lt y)
  have hcop : Nat.Coprime y.val q :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hnotdvd)
  refine ⟨ZMod.unitOfCoprime y.val hcop, ?_, ?_⟩
  · unfold jacobiOneSubUnitSearch
    change (if h : Nat.Coprime y.val q then some (ZMod.unitOfCoprime y.val h) else none) = _
    rw [dite_eq_left hcop]
  · rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]

/-- Look up the discrete logarithm of the unit represented by `1 - g^x`. The result is optional
because the unit lift and bounded power table are both finite searches. -/
def jacobiOneSubLogFromTable {q : ℕ} (g : (ZMod q)ˣ) (x : ℕ) : Option ℕ :=
  (jacobiOneSubUnitSearch g x).bind (fun target => discreteLogTableSearch g target)

/-- A primitive root modulo a prime supplies the discrete logarithm of `1 - g^x` at every
Jacobi index strictly between zero and `q - 1`. The returned logarithm is in the table range and
its power is the lifted target unit. -/
theorem jacobiOneSubLogFromTable_some_of_primitiveRoot {q : ℕ} (hq : Nat.Prime q) (g : (ZMod q)ˣ)
    (hg : IsPrimitiveRoot g (q - 1)) {x : ℕ} (hx0 : 0 < x) (hx : x < q - 1) :
    ∃ target fx,
      jacobiOneSubUnitSearch g x = some target ∧
        jacobiOneSubLogFromTable g x = some fx ∧ fx < q - 1 ∧ g ^ fx = target := by
  obtain ⟨target, htarget, _⟩ := jacobiOneSubUnitSearch_some_of_primitiveRoot hq g hg hx0 hx
  have htableSome : (discreteLogTableSearch g target).isSome = true :=
    discreteLogTableSearch_isSome_of_prime hq g target hg
  obtain ⟨fx, hfx⟩ := Option.isSome_iff_exists.mp htableSome
  have hlog : jacobiOneSubLogFromTable g x = some fx := by
    unfold jacobiOneSubLogFromTable
    rw [htarget]
    exact hfx
  obtain ⟨hbound, hpow⟩ := discreteLogTableSearch_some_spec hfx
  exact ⟨target, fx, htarget, hlog, hbound, hpow⟩

/-- On a valid Jacobi index, the character value at `1 - g^x` is the root power selected by
the executable one-subtraction logarithm search. -/
theorem jacobiPowerCharacter_apply_oneSub_of_success {q P x e : ℕ} {R : Type*} [CommRing R]
    (hq : Nat.Prime q) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hP : P ∣ q - 1) (hx0 : 0 < x) (hx : x < q - 1)
    (hlog : jacobiOneSubLogFromTable g x = some e) :
    jacobiPowerCharacter hq g hg ζ hζ hP (1 - (g : ZMod q) ^ x) = (ζ : R) ^ e := by
  obtain ⟨target, htarget, hvalue⟩ := jacobiOneSubUnitSearch_some_of_primitiveRoot hq g hg hx0 hx
  have htable : discreteLogTableSearch g target = some e := by
    simp only [jacobiOneSubLogFromTable, htarget, Option.bind_some] at hlog
    exact hlog
  rw [← hvalue]
  exact jacobiPowerCharacter_apply_of_discreteLogTableSearch hq g target hg ζ hζ hP htable

/-- The two character factors in one Jacobi summand combine to the reduced exponent used by
the executable coefficient search. -/
theorem jacobiPowerCharacter_jacobiTerm_eq {q P a b x e : ℕ} {R : Type*} [CommRing R]
    (hq : Nat.Prime q) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hP : P ∣ q - 1) (hx0 : 0 < x) (hx : x < q - 1)
    (hlog : jacobiOneSubLogFromTable g x = some e) :
    (jacobiPowerCharacter hq g hg ζ hζ hP ((g ^ x : (ZMod q)ˣ) : ZMod q)) ^ a *
        (jacobiPowerCharacter hq g hg ζ hζ hP (1 - (g : ZMod q) ^ x)) ^ b =
      (ζ : R) ^ (a * x + b * e) := by
  rw [jacobiPowerCharacter_apply_generator_pow hq g hg ζ hζ hP,
    jacobiPowerCharacter_apply_oneSub_of_success hq g hg ζ hζ hP hx0 hx hlog]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm x a, Nat.mul_comm e b, ← pow_add]

/-- Compute the reduced Jacobi exponent by lifting `1 - g^x` to a unit and looking up its
discrete logarithm. Either missing unit lifts or missing table entries propagate as `none`. -/
def jacobiExponentFromOneSubTable {q P : ℕ} (g : (ZMod q)ˣ) (a b x : ℕ) : Option ℕ :=
  (jacobiOneSubUnitSearch g x).bind (fun target => jacobiExponentFromTable (P := P) g target a b x)

/-- For a prime auxiliary modulus and a primitive-root generator, the combined unit-lift and
table pipeline succeeds throughout the Jacobi index range. Its result is the prescribed reduced
exponent and remains in the coefficient interval when the period is positive. -/
theorem jacobiExponentFromOneSubTable_some_of_primitiveRoot {q P a b : ℕ} (hq : Nat.Prime q)
    (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) {x : ℕ} (hx0 : 0 < x) (hx : x < q - 1)
    (hP : 0 < P) :
    ∃ target fx e,
      jacobiOneSubUnitSearch g x = some target ∧
        discreteLogTableSearch g target = some fx ∧
        jacobiExponentFromOneSubTable (P := P) g a b x = some e ∧
        fx < q - 1 ∧ g ^ fx = target ∧ e = (a * x + b * fx) % P ∧ e < P := by
  obtain ⟨target, htarget, _⟩ := jacobiOneSubUnitSearch_some_of_primitiveRoot hq g hg hx0 hx
  have htableSome : (discreteLogTableSearch g target).isSome = true :=
    discreteLogTableSearch_isSome_of_prime hq g target hg
  obtain ⟨fx, hfx⟩ := Option.isSome_iff_exists.mp htableSome
  have hpoint : jacobiExponentFromTable (P := P) g target a b x = some ((a * x + b * fx) % P) := by
    unfold jacobiExponentFromTable
    rw [hfx]
    rfl
  have hpipeline :
    jacobiExponentFromOneSubTable (P := P) g a b x = some ((a * x + b * fx) % P) := by
    unfold jacobiExponentFromOneSubTable
    rw [htarget]
    change jacobiExponentFromTable (P := P) g target a b x = _
    exact hpoint
  obtain ⟨hfxBound, hpow⟩ := discreteLogTableSearch_some_spec hfx
  refine ⟨target, fx, (a * x + b * fx) % P, htarget, hfx, hpipeline, hfxBound, hpow, rfl, ?_⟩
  exact Nat.mod_lt _ hP

/-- Search all requested Jacobi indices, preserving their order and returning `none` when any
unit lift or discrete-log table lookup fails. -/
def jacobiExponentBatchSearch {q P : ℕ} (g : (ZMod q)ˣ) (a b : ℕ) : List ℕ → Option (List ℕ)
  | [] => some []
  | x :: xs =>
    match jacobiExponentFromOneSubTable (P := P) g a b x with
    | none => none
    | some exponent =>
      match jacobiExponentBatchSearch (P := P) g a b xs with
      | none => none
      | some exponents => some (exponent :: exponents)

/-- A prime auxiliary modulus and primitive-root generator make the batch search succeed for any
finite list of indices lying strictly between zero and `q - 1`. This is the executable finite
Option interface used before assembling the Jacobi coefficient sum. -/
theorem jacobiExponentBatchSearch_exists_of_valid_indices {q P a b : ℕ} (hq : Nat.Prime q)
    (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (hP : 0 < P) {xs : List ℕ}
    (hvalid : ∀ x, x ∈ xs → 0 < x ∧ x < q - 1) :
    ∃ exponents, jacobiExponentBatchSearch (P := P) g a b xs = some exponents := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    have hxmem : x ∈ x :: xs := List.mem_cons.mpr (Or.inl rfl)
    obtain ⟨target, fx, exponent, _, _, hpoint, _, _, _, _⟩ :=
      jacobiExponentFromOneSubTable_some_of_primitiveRoot (a := a) (b := b) hq g hg
        (hvalid x hxmem).1 (hvalid x hxmem).2 hP
    have htail : ∀ y, y ∈ xs → 0 < y ∧ y < q - 1 := by
      intro y hy
      exact hvalid y (List.mem_cons.mpr (Or.inr hy))
    obtain ⟨exponents, hexponents⟩ := ih htail
    refine ⟨exponent :: exponents, ?_⟩
    change
      (match jacobiExponentFromOneSubTable (P := P) g a b x with
        | none => none
        | some exponent =>
          match jacobiExponentBatchSearch (P := P) g a b xs with
          | none => none
          | some exponents => some (exponent :: exponents)) =
        _
    rw [hpoint, hexponents]

/-- Search for all logarithms associated with a finite list of Jacobi indices. -/
def jacobiOneSubLogBatchSearch {q : ℕ} (g : (ZMod q)ˣ) : List ℕ → Option (List ℕ)
  | [] => some []
  | x :: xs =>
    match jacobiOneSubLogFromTable g x with
    | none => none
    | some logarithm =>
      match jacobiOneSubLogBatchSearch g xs with
      | none => none
      | some logarithms => some (logarithm :: logarithms)

/-- A successful logarithm batch returns one successful pointwise lookup at each input position.
The `Forall₂` relation records both list length and order. -/
theorem jacobiOneSubLogBatchSearch_some_spec {q : ℕ} (g : (ZMod q)ˣ) {xs logarithms : List ℕ}
    (h : jacobiOneSubLogBatchSearch g xs = some logarithms) :
    List.Forall₂ (fun x logarithm => jacobiOneSubLogFromTable g x = some logarithm) xs
      logarithms := by
  induction xs generalizing logarithms with
  | nil =>
    change some [] = some logarithms at h
    injection h with hEq
    subst logarithms
    exact List.Forall₂.nil
  | cons x xs
    ih =>
    change
      (match jacobiOneSubLogFromTable g x with
        | none => none
        | some logarithm =>
          match jacobiOneSubLogBatchSearch g xs with
          | none => none
          | some logarithms => some (logarithm :: logarithms)) =
        some logarithms at h
    split at h
    · cases h
    · split at h
      · cases h
      · injection h with hEq
        subst logarithms
        refine List.Forall₂.cons ?_ ?_
        · assumption
        · exact ih (by assumption)

/-- Under a prime auxiliary modulus and primitive-root generator, every finite list of valid
Jacobi indices has a complete ordered list of discrete logarithms. -/
theorem jacobiOneSubLogBatchSearch_exists_of_valid_indices {q : ℕ} (hq : Nat.Prime q)
    (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) {xs : List ℕ}
    (hvalid : ∀ x, x ∈ xs → 0 < x ∧ x < q - 1) :
    ∃ logarithms, jacobiOneSubLogBatchSearch g xs = some logarithms := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    have hxmem : x ∈ x :: xs := List.mem_cons.mpr (Or.inl rfl)
    obtain ⟨target, logarithm, _, hpoint, _, _⟩ :=
      jacobiOneSubLogFromTable_some_of_primitiveRoot hq g hg (hvalid x hxmem).1 (hvalid x hxmem).2
    have htail : ∀ y, y ∈ xs → 0 < y ∧ y < q - 1 := by
      intro y hy
      exact hvalid y (List.mem_cons.mpr (Or.inr hy))
    obtain ⟨logarithms, hlogarithms⟩ := ih htail
    refine ⟨logarithm :: logarithms, ?_⟩
    change
      (match jacobiOneSubLogFromTable g x with
        | none => none
        | some logarithm =>
          match jacobiOneSubLogBatchSearch g xs with
          | none => none
          | some logarithms => some (logarithm :: logarithms)) =
        _
    rw [hpoint, hlogarithms]

/-- The standard Jacobi range `1, …, q - 2` is represented in increasing order by this list. -/
def jacobiIndexList (q : ℕ) : List ℕ :=
  List.range' 1 (q - 2) 1

/-- Every member of the explicit Jacobi index list is strictly between zero and `q - 1`. -/
theorem jacobiIndexList_mem_valid {q x : ℕ} (h : x ∈ jacobiIndexList q) : 0 < x ∧ x < q - 1 := by
  unfold jacobiIndexList at h
  obtain ⟨i, hi, hxi⟩ := List.mem_range'.mp h
  have hq2 : 2 ≤ q := Nat.le_of_lt (Nat.sub_pos_iff_lt.mp (lt_of_le_of_lt (Nat.zero_le i) hi))
  have hqsub : q - 2 + 2 = q := Nat.sub_add_cancel hq2
  have hq1 : q - 2 + 1 = q - 1 := by
    calc
      q - 2 + 1 = q - 2 + 2 - 1 := by rw [Nat.add_sub_assoc (by decide : 1 ≤ 2)]
      _ = q - 1 := by rw [hqsub]
  constructor
  · rw [hxi]
    simp only [one_mul]
    exact Nat.zero_lt_one.trans_le (Nat.le_add_right 1 i)
  · rw [hxi]
    simp only [one_mul]
    calc
      1 + i = i + 1 := Nat.add_comm _ _
      _ < (q - 2) + 1 := Nat.add_lt_add_right hi 1
      _ = q - 1 := hq1

/-- Map a nonzero exponent below `q - 1` to the corresponding nonidentity unit. The primitive
root condition makes the image avoid one, which is the exceptional Jacobi input. -/
def jacobiGeneratorPowerOnJacobiIndex {q : ℕ} (hq : Nat.Prime q) (g : (ZMod q)ˣ)
    (hg : IsPrimitiveRoot g (q - 1)) (x : { x : ℕ // 0 < x ∧ x < q - 1 }) :
    { u : (ZMod q)ˣ // u ≠ 1 } := by
  have hperiod : 0 < q - 1 := Nat.sub_pos_of_lt hq.one_lt
  refine ⟨g ^ x.1, ?_⟩
  intro hpow
  have hzero : x.1 = 0 := hg.pow_inj x.2.2 hperiod (by simpa only [pow_zero] using hpow)
  exact (Nat.ne_of_gt x.2.1) hzero

/-- On the complete Jacobi exponent interval, primitive-root powers give a bijection to the
units other than one. This is the finite reindexing core for identifying the computed exponent
sum with the unit part of Mathlib's Jacobi sum. -/
theorem jacobiGeneratorPowerOnJacobiIndex_bijective {q : ℕ} (hq : Nat.Prime q) (g : (ZMod q)ˣ)
    (hg : IsPrimitiveRoot g (q - 1)) :
    Function.Bijective (jacobiGeneratorPowerOnJacobiIndex hq g hg) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply hg.pow_inj x.2.2 y.2.2
    exact congrArg Subtype.val hxy
  · intro u
    have hsome := discreteLogTableSearch_isSome_of_prime hq g u.1 hg
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨helt, hpow⟩ := discreteLogTableSearch_some_spec he
    have hepos : 0 < e := by
      by_cases he0 : e = 0
      · subst e
        exact False.elim (u.2 (by simpa only [pow_zero] using hpow.symm))
      · exact Nat.pos_of_ne_zero he0
    refine ⟨⟨e, hepos, helt⟩, ?_⟩
    apply Subtype.ext
    exact hpow

/-- The bijective generator-power map packaged as an equivalence, for reindexing finite sums. -/
noncomputable def jacobiGeneratorPowerEquiv {q : ℕ} (hq : Nat.Prime q) (g : (ZMod q)ˣ)
    (hg : IsPrimitiveRoot g (q - 1)) :
    { x : ℕ // 0 < x ∧ x < q - 1 } ≃ { u : (ZMod q)ˣ // u ≠ 1 } :=
  Equiv.ofBijective (jacobiGeneratorPowerOnJacobiIndex hq g hg)
    (jacobiGeneratorPowerOnJacobiIndex_bijective hq g hg)

/-- Reindex a sum over the Jacobi exponent interval as a sum over all nonidentity units. -/
theorem jacobiGeneratorPower_sum_eq_unit_sum {q : ℕ} (hq : Nat.Prime q) (g : (ZMod q)ˣ)
    (hg : IsPrimitiveRoot g (q - 1)) [Fintype { x : ℕ // 0 < x ∧ x < q - 1 }]
    [Fintype { u : (ZMod q)ˣ // u ≠ 1 }] {R : Type*} [AddCommMonoid R] (f : (ZMod q)ˣ → R) :
    (∑ x : { x : ℕ // 0 < x ∧ x < q - 1 }, f (g ^ x.1)) =
      ∑ u : { u : (ZMod q)ˣ // u ≠ 1 }, f u.1 := by
  apply Fintype.sum_equiv (jacobiGeneratorPowerEquiv hq g hg)
  intro x
  rfl

/-- Over the prime field `ZMod q`, nonzero elements other than one are equivalent to units
other than one. The forward map uses `Units.mk0`; its inverse is the unit coercion. -/
noncomputable def zmodNonidentityUnitEquiv {q : ℕ} (hq : Nat.Prime q) :
    { x : ZMod q // x ≠ 0 ∧ x ≠ 1 } ≃ { u : (ZMod q)ˣ // u ≠ 1 } := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  let f : { x : ZMod q // x ≠ 0 ∧ x ≠ 1 } → { u : (ZMod q)ˣ // u ≠ 1 } := fun x =>
    ⟨Units.mk0 x.1 x.2.1, by
      intro heq
      have hval := congrArg Units.val heq
      change x.1 = 1 at hval
      exact x.2.2 hval⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have hunit : Units.mk0 x.1 x.2.1 = Units.mk0 y.1 y.2.1 := congrArg Subtype.val hxy
      have hval := congrArg Units.val hunit
      simpa only [Units.val_mk0] using hval
    · intro u
      refine ⟨⟨u.1, ?_⟩, ?_⟩
      · constructor
        · exact Units.ne_zero u.1
        · intro heq
          exact u.2 (Units.ext heq)
      · apply Subtype.ext
        apply Units.ext
        rfl
  exact Equiv.ofBijective f hf

/-- Rewrite the full Jacobi sum as a sum over nonidentity units. The removed inputs `0` and `1`
contribute zero because multiplicative characters vanish at nonunits. -/
theorem jacobiSum_eq_nonidentityUnitSum {q : ℕ} (hq : Nat.Prime q) {R : Type*} [CommRing R]
    [Fintype (ZMod q)] (χ ψ : MulChar (ZMod q) R) :
    jacobiSum χ ψ =
      ∑ u : { u : (ZMod q)ˣ // u ≠ 1 }, χ (u.1 : ZMod q) * ψ (1 - (u.1 : ZMod q)) := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  let S : Finset (ZMod q) := Finset.univ.filter (fun x => x ≠ 0 ∧ x ≠ 1)
  have hχ0 : χ (0 : ZMod q) = 0 := by
    change χ.toMonoidHom 0 = 0
    exact MulChar.map_nonunit' χ 0 not_isUnit_zero
  have hψ0 : ψ (0 : ZMod q) = 0 := by
    change ψ.toMonoidHom 0 = 0
    exact MulChar.map_nonunit' ψ 0 not_isUnit_zero
  have hfiltered : (∑ x ∈ S, χ x * ψ (1 - x)) = ∑ x : ZMod q, χ x * ψ (1 - x) := by
    apply Finset.sum_subset
    · intro x hx
      exact Finset.mem_univ x
    · intro x hx hxS
      have hnot : ¬(x ≠ 0 ∧ x ≠ 1) := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hxS
      have hxout : x = 0 ∨ x = 1 := by
        by_cases h0 : x = 0
        · exact Or.inl h0
        · right
          by_contra h1
          exact hnot ⟨h0, h1⟩
      rcases hxout with hx0 | hx1
      · rw [hx0, hχ0]
        exact zero_mul _
      · rw [hx1, sub_self, hψ0]
        exact mul_zero _
  have hsubtype :
    (∑ x ∈ S, χ x * ψ (1 - x)) = ∑ x : { x : ZMod q // x ≠ 0 ∧ x ≠ 1 }, χ x.1 * ψ (1 - x.1) := by
    apply Finset.sum_subtype S
    intro x
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hunit :
    (∑ x : { x : ZMod q // x ≠ 0 ∧ x ≠ 1 }, χ x.1 * ψ (1 - x.1)) =
      ∑ u : { u : (ZMod q)ˣ // u ≠ 1 }, χ (u.1 : ZMod q) * ψ (1 - (u.1 : ZMod q)) := by
    apply Fintype.sum_equiv (zmodNonidentityUnitEquiv hq)
    intro x
    rfl
  rw [jacobiSum]
  exact hfiltered.symm.trans (hsubtype.trans hunit)

/-- The natural-number interval used by Jacobi's sum is exactly the positive exponent range of
the primitive-root parametrization when the auxiliary modulus is prime. -/
theorem mem_jacobiIcc_iff_valid {q x : ℕ} (hq : Nat.Prime q) :
    x ∈ Finset.Icc 1 (q - 2) ↔ 0 < x ∧ x < q - 1 := by
  have hq1 : 0 < q - 1 := Nat.sub_pos_of_lt hq.one_lt
  have hsub : q - 1 - 1 = q - 2 := by rw [Nat.sub_sub, one_add_one_eq_two]
  constructor
  · intro hx
    have hmem := Finset.mem_Icc.mp hx
    constructor
    · exact Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hmem.1)
    · rw [← hsub] at hmem
      exact (Nat.le_sub_one_iff_lt hq1).mp hmem.2
  · intro hx
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hx.1)
    · rw [← hsub]
      exact (Nat.le_sub_one_iff_lt hq1).mpr hx.2

/-- Identify the finite Jacobi interval with positive exponents below the group order. -/
noncomputable def jacobiValidIndexEquivIcc {q : ℕ} (hq : Nat.Prime q) :
    { x : ℕ // 0 < x ∧ x < q - 1 } ≃ { x : ℕ // x ∈ Finset.Icc 1 (q - 2) } := by
  let f : { x : ℕ // 0 < x ∧ x < q - 1 } → { x : ℕ // x ∈ Finset.Icc 1 (q - 2) } := fun x =>
    ⟨x.1, (mem_jacobiIcc_iff_valid hq).mpr x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have hv := congrArg Subtype.val hxy
      change x.1 = y.1 at hv
      exact hv
    · intro y
      refine ⟨⟨y.1, (mem_jacobiIcc_iff_valid hq).mp y.2⟩, ?_⟩
      apply Subtype.ext
      rfl
  exact Equiv.ofBijective f hf

/-- Reindex a sum over valid Jacobi exponents as a `Finset.Icc` sum. -/
theorem jacobiValidIndex_sum_eq_Icc {q : ℕ} (hq : Nat.Prime q)
    [Fintype { x : ℕ // 0 < x ∧ x < q - 1 }] {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑ x : { x : ℕ // 0 < x ∧ x < q - 1 }, f x.1) = ∑ x ∈ Finset.Icc 1 (q - 2), f x := by
  calc
    (∑ x : { x : ℕ // 0 < x ∧ x < q - 1 }, f x.1) =
        ∑ x : { x : ℕ // x ∈ Finset.Icc 1 (q - 2) }, f x.1 :=
      by
      apply Fintype.sum_equiv (jacobiValidIndexEquivIcc hq)
      intro x
      rfl
    _ = ∑ x ∈ Finset.Icc 1 (q - 2), f x := by
      symm
      apply Finset.sum_subtype (Finset.Icc 1 (q - 2))
      intro x
      rfl

/-- The ordered index list contains exactly the elements of the finite Jacobi interval. -/
theorem mem_jacobiIndexList_iff {q x : ℕ} : x ∈ jacobiIndexList q ↔ x ∈ Finset.Icc 1 (q - 2) := by
  constructor
  · intro hx
    change x ∈ List.range' 1 (q - 2) 1 at hx
    obtain ⟨i, hi, hxi⟩ := List.mem_range'.mp hx
    apply Finset.mem_Icc.mpr
    constructor
    · rw [hxi]
      simp only [one_mul]
      exact Nat.le_add_right 1 i
    · rw [hxi]
      simp only [one_mul]
      have hlt : 1 + i < Nat.succ (q - 2) := by
        have h := Nat.add_lt_add_left hi 1
        simpa only [Nat.add_comm 1 (q - 2), Nat.add_one] using h
      exact Nat.lt_succ_iff.mp hlt
  · intro hx
    have hinterval := Finset.mem_Icc.mp hx
    change x ∈ List.range' 1 (q - 2) 1
    rw [List.mem_range']
    refine ⟨x - 1, ?_, ?_⟩
    · exact lt_of_lt_of_le (Nat.sub_lt_self (by decide) hinterval.1) hinterval.2
    · calc
        x = x - 1 + 1 := (Nat.sub_add_cancel hinterval.1).symm
        _ = 1 + 1 * (x - 1) := by simp only [one_mul, Nat.add_comm]

/-- Sum a function over the explicit ordered Jacobi index list. -/
def jacobiIndexListSum {R : Type*} [AddCommMonoid R] (q : ℕ) (f : ℕ → R) : R :=
  (jacobiIndexList q).map f |>.sum

/-- The list sum over the explicit Jacobi indices is the finite sum over `1 ≤ x ≤ q - 2`.
This is the index-conversion consumer used to transfer the logarithm list to the coefficient sum.
-/
theorem jacobiIndexListSum_eq_finset {R : Type*} [AddCommMonoid R] (q : ℕ) (f : ℕ → R) :
    jacobiIndexListSum q f = ∑ x ∈ Finset.Icc 1 (q - 2), f x := by
  unfold jacobiIndexListSum
  have hnodup : (jacobiIndexList q).Nodup := List.nodup_range' (s := 1) (n := q - 2) 1
  rw [← List.sum_toFinset f hnodup]
  have hindices : (jacobiIndexList q).toFinset = Finset.Icc 1 (q - 2) := by
    apply Finset.ext
    intro x
    rw [List.mem_toFinset, mem_jacobiIndexList_iff]
  rw [hindices]

/-- A primitive root modulo a prime supplies the complete ordered logarithm list over the
standard Jacobi index range. -/
theorem jacobiOneSubLogBatchSearch_exists_of_prime_range {q : ℕ} (hq : Nat.Prime q) (g : (ZMod q)ˣ)
    (hg : IsPrimitiveRoot g (q - 1)) :
    ∃ logarithms,
      jacobiOneSubLogBatchSearch g (jacobiIndexList q) = some logarithms ∧
        List.Forall₂ (fun x logarithm => jacobiOneSubLogFromTable g x = some logarithm)
          (jacobiIndexList q) logarithms := by
  obtain ⟨logarithms, hsearch⟩ :=
    jacobiOneSubLogBatchSearch_exists_of_valid_indices hq g hg
      (fun x hx => jacobiIndexList_mem_valid hx)
  exact ⟨logarithms, hsearch, jacobiOneSubLogBatchSearch_some_spec g hsearch⟩

/-- Coefficient-counted Jacobi sum associated with a supplied discrete-log exponent function.
The summation range omits `x = 0` and `x = 1`, whose character terms vanish in the Jacobi-sum
definition; `logOneSub` supplies the exponent of `1 - g^x` for each remaining index. -/
def jacobiSumFromLogCoefficients {R : Type*} [Semiring R] (q P a b : ℕ) (logOneSub : ℕ → ℕ)
    (z : R) : R :=
  jacobiCoefficientSum P (Finset.Icc 1 (q - 2)) (fun x => (a * x + b * logOneSub x) % P) z

/-- The coefficient-count implementation equals its direct finite root-power sum. This isolates
the histogram identity from the separate theorem that the supplied `logOneSub` values are the
discrete logarithms of `1 - g^x` modulo an auxiliary prime. -/
theorem jacobiSumFromLogCoefficients_eq_direct {R : Type*} [Semiring R] {q P a b : ℕ} (hP : 0 < P)
    (logOneSub : ℕ → ℕ) (z : R) :
    jacobiSumFromLogCoefficients q P a b logOneSub z =
      ∑ x ∈ Finset.Icc 1 (q - 2), z ^ ((a * x + b * logOneSub x) % P) := by
  unfold jacobiSumFromLogCoefficients
  apply jacobiCoefficientSum_eq_direct
  intro x hx
  exact jacobiExponent_mod_lt hP

/-- The coefficient-count implementation can be consumed as an ordered sum over the same index
list used by the executable discrete-log search. -/
theorem jacobiSumFromLogCoefficients_eq_indexListSum {R : Type*} [Semiring R] {q P a b : ℕ}
    (hP : 0 < P) (logOneSub : ℕ → ℕ) (z : R) :
    jacobiSumFromLogCoefficients q P a b logOneSub z =
      jacobiIndexListSum q (fun x => z ^ ((a * x + b * logOneSub x) % P)) := by
  rw [jacobiSumFromLogCoefficients_eq_direct hP]
  exact (jacobiIndexListSum_eq_finset q _).symm

/-- Read a pointwise table search as a natural-number logarithm, using zero only as the value
outside the validated Jacobi interval. The Option-valued search remains the computational API. -/
def jacobiOneSubLogValue {q : ℕ} (g : (ZMod q)ˣ) (x : ℕ) : ℕ :=
  (jacobiOneSubLogFromTable g x).getD 0

/-- On every valid prime-modulus Jacobi index, the totalized logarithm value is exactly the
successful Option result, and its power is the lifted `1 - g^x` unit. -/
theorem jacobiOneSubLogValue_spec {q : ℕ} (hq : Nat.Prime q) (g : (ZMod q)ˣ)
    (hg : IsPrimitiveRoot g (q - 1)) {x : ℕ} (hx0 : 0 < x) (hx : x < q - 1) :
    ∃ target,
      jacobiOneSubLogFromTable g x = some (jacobiOneSubLogValue g x) ∧
        jacobiOneSubUnitSearch g x = some target ∧ g ^ jacobiOneSubLogValue g x = target := by
  obtain ⟨target, fx, htarget, hlog, _, hpow⟩ :=
    jacobiOneSubLogFromTable_some_of_primitiveRoot hq g hg hx0 hx
  refine ⟨target, ?_, htarget, ?_⟩
  · unfold jacobiOneSubLogValue
    rw [hlog]
    rfl
  · unfold jacobiOneSubLogValue
    rw [hlog]
    exact hpow

/-- A root whose `P`-th power is one only depends on an exponent modulo `P`. -/
theorem rootPower_eq_rootPower_mod {P m : ℕ} {R : Type*} [Monoid R] (ζ : R) (hζ : ζ ^ P = 1) :
    ζ ^ m = ζ ^ (m % P) := by
  calc
    ζ ^ m = ζ ^ (m % P + P * (m / P)) := by rw [Nat.mod_add_div]
    _ = ζ ^ (m % P) * (ζ ^ P) ^ (m / P) := by rw [pow_add, pow_mul]
    _ = ζ ^ (m % P) := by rw [hζ, one_pow, mul_one]

/-- The finite Jacobi exponent interval's powered character sum is the coefficient-counted
Jacobi sum supplied by the successful one-subtraction logarithm values. -/
theorem jacobiPowerCharacter_finiteSum_eq_coefficients {q P a b : ℕ} {R : Type*} [CommRing R]
    (hq : Nat.Prime q) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hPdiv : P ∣ q - 1) (hPpos : 0 < P) :
    (∑ x ∈ Finset.Icc 1 (q - 2),
        (jacobiPowerCharacter hq g hg ζ hζ hPdiv ((g ^ x : (ZMod q)ˣ) : ZMod q)) ^ a *
          (jacobiPowerCharacter hq g hg ζ hζ hPdiv (1 - (g : ZMod q) ^ x)) ^ b) =
      jacobiSumFromLogCoefficients q P a b (jacobiOneSubLogValue g) (ζ : R) := by
  rw [jacobiSumFromLogCoefficients_eq_direct hPpos (jacobiOneSubLogValue g) (ζ : R)]
  apply Finset.sum_congr rfl
  intro x hx
  have hxvalid : 0 < x ∧ x < q - 1 := jacobiIndexList_mem_valid ((mem_jacobiIndexList_iff).2 hx)
  obtain ⟨_, hlog, _, _⟩ := jacobiOneSubLogValue_spec hq g hg hxvalid.1 hxvalid.2
  calc
    _ = (ζ : R) ^ (a * x + b * jacobiOneSubLogValue g x) :=
      jacobiPowerCharacter_jacobiTerm_eq hq g hg ζ hζ hPdiv hxvalid.1 hxvalid.2 hlog
    _ = (ζ : R) ^ ((a * x + b * jacobiOneSubLogValue g x) % P) :=
      rootPower_eq_rootPower_mod (ζ : R) hζ

/-- The actual finite-field Jacobi sum of the powered characters equals the executable
coefficient-counted sum. The proof removes the zero terms, parametrizes the remaining units by
primitive-root exponents, and changes that exponent subtype to the standard finite interval. -/
theorem jacobiPowerCharacter_jacobiSum_eq_coefficients {q P a b : ℕ} {R : Type*} [CommRing R]
    [Fintype (ZMod q)] (hq : Nat.Prime q) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hPdiv : P ∣ q - 1) (hPpos : 0 < P)
    [Finite { x : ℕ // 0 < x ∧ x < q - 1 }] :
    jacobiSum (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ a)
        (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ b) =
      jacobiSumFromLogCoefficients q P a b (jacobiOneSubLogValue g) (ζ : R) := by
  have : Fintype { x : ℕ // 0 < x ∧ x < q - 1 } := Fintype.ofFinite _
  let χ : MulChar (ZMod q) R := jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ a
  let ψ : MulChar (ZMod q) R := jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ b
  calc
    jacobiSum (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ a)
          (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ b) =
        ∑ u : { u : (ZMod q)ˣ // u ≠ 1 }, χ (u.1 : ZMod q) * ψ (1 - (u.1 : ZMod q)) :=
      by exact jacobiSum_eq_nonidentityUnitSum hq χ ψ
    _ =
        ∑ x : { x : ℕ // 0 < x ∧ x < q - 1 },
          χ ((g ^ x.1 : (ZMod q)ˣ) : ZMod q) * ψ (1 - (g ^ x.1 : (ZMod q)ˣ) : ZMod q) :=
      by
      symm
      exact
        jacobiGeneratorPower_sum_eq_unit_sum hq g hg
          (fun u => χ (u : ZMod q) * ψ (1 - (u : ZMod q)))
    _ =
        ∑ x ∈ Finset.Icc 1 (q - 2),
          χ ((g ^ x : (ZMod q)ˣ) : ZMod q) * ψ (1 - (g ^ x : (ZMod q)ˣ) : ZMod q) :=
      by
      exact
        jacobiValidIndex_sum_eq_Icc hq
          (fun x => χ ((g ^ x : (ZMod q)ˣ) : ZMod q) * ψ (1 - (g ^ x : (ZMod q)ˣ) : ZMod q))
    _ =
        ∑ x ∈ Finset.Icc 1 (q - 2),
          (jacobiPowerCharacter hq g hg ζ hζ hPdiv ((g ^ x : (ZMod q)ˣ) : ZMod q)) ^ a *
            (jacobiPowerCharacter hq g hg ζ hζ hPdiv (1 - (g : ZMod q) ^ x)) ^ b :=
      by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [χ, ψ]
      have hxvalid := (mem_jacobiIcc_iff_valid hq).mp hx
      obtain ⟨target, _, htarget⟩ :=
        jacobiOneSubUnitSearch_some_of_primitiveRoot hq g hg hxvalid.1 hxvalid.2
      have hfirst :
        (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ a) ((g ^ x : (ZMod q)ˣ) : ZMod q) =
          (jacobiPowerCharacter hq g hg ζ hζ hPdiv ((g ^ x : (ZMod q)ˣ) : ZMod q)) ^ a :=
        MulChar.pow_apply_coe (jacobiPowerCharacter hq g hg ζ hζ hPdiv) a (g ^ x)
      have hsecond :
        (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ b) (1 - ((g ^ x : (ZMod q)ˣ) : ZMod q)) =
          (jacobiPowerCharacter hq g hg ζ hζ hPdiv (1 - (g : ZMod q) ^ x)) ^ b := by
        calc
          _ = (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ b) (target : ZMod q) := by
            rw [Units.val_pow_eq_pow_val, ← htarget]
          _ = (jacobiPowerCharacter hq g hg ζ hζ hPdiv (target : ZMod q)) ^ b :=
            MulChar.pow_apply_coe (jacobiPowerCharacter hq g hg ζ hζ hPdiv) b target
          _ = _ := by rw [htarget]
      rw [hfirst, hsecond]
    _ = jacobiSumFromLogCoefficients q P a b (jacobiOneSubLogValue g) (ζ : R) :=
      jacobiPowerCharacter_finiteSum_eq_coefficients (a := a) (b := b) hq g hg ζ hζ hPdiv hPpos

/-- Over the full valid exponent interval, the powered character terms sum to exactly the
root-power sum indexed by the totalized values of the successful Option logarithm search. -/
theorem jacobiPowerCharacter_weightedTermSum_eq_logPowerSum {q P a b : ℕ} {R : Type*} [CommRing R]
    (hq : Nat.Prime q) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hP : P ∣ q - 1) [Fintype { x : ℕ // 0 < x ∧ x < q - 1 }] :
    (∑ x : { x : ℕ // 0 < x ∧ x < q - 1 },
        (jacobiPowerCharacter hq g hg ζ hζ hP ((g ^ x.1 : (ZMod q)ˣ) : ZMod q)) ^ a *
          (jacobiPowerCharacter hq g hg ζ hζ hP (1 - (g : ZMod q) ^ x.1)) ^ b) =
      ∑ x : { x : ℕ // 0 < x ∧ x < q - 1 },
        (ζ : R) ^ (a * x.1 + b * jacobiOneSubLogValue g x.1) := by
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨_, hlog, _, _⟩ := jacobiOneSubLogValue_spec hq g hg x.2.1 x.2.2
  exact jacobiPowerCharacter_jacobiTerm_eq hq g hg ζ hζ hP x.2.1 x.2.2 hlog

/-- For a prime auxiliary modulus, the ordered Option batch search returns exactly the list of
pointwise logarithm values on every list of valid Jacobi indices. -/
theorem jacobiOneSubLogBatchSearch_exists_value_map_of_valid_indices {q : ℕ} (hq : Nat.Prime q)
    (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) {xs : List ℕ}
    (hvalid : ∀ x, x ∈ xs → 0 < x ∧ x < q - 1) :
    ∃ logarithms,
      jacobiOneSubLogBatchSearch g xs = some logarithms ∧
        logarithms = xs.map (jacobiOneSubLogValue g) := by
  induction xs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons x xs ih =>
    have hxmem : x ∈ x :: xs := List.mem_cons.mpr (Or.inl rfl)
    obtain ⟨target, logarithm, _, hlookup, _, _⟩ :=
      jacobiOneSubLogFromTable_some_of_primitiveRoot hq g hg (hvalid x hxmem).1 (hvalid x hxmem).2
    have htailvalid : ∀ y, y ∈ xs → 0 < y ∧ y < q - 1 := by
      intro y hy
      exact hvalid y (List.mem_cons.mpr (Or.inr hy))
    obtain ⟨logarithms, htailsearch, htailmap⟩ := ih htailvalid
    have hvalue : logarithm = jacobiOneSubLogValue g x := by
      unfold jacobiOneSubLogValue
      rw [hlookup]
      rfl
    refine ⟨logarithm :: logarithms, ?_, ?_⟩
    · change
        (match jacobiOneSubLogFromTable g x with
          | none => none
          | some logarithm =>
            match jacobiOneSubLogBatchSearch g xs with
            | none => none
            | some logarithms => some (logarithm :: logarithms)) =
          _
      rw [hlookup, htailsearch]
    · rw [List.map_cons, hvalue, htailmap]

/-- On the complete Jacobi index range, the Option batch result is the ordered list of the
pointwise `1 - g^x` logarithm values consumed by the coefficient-sum interface. -/
theorem jacobiOneSubLogBatchSearch_exists_value_map_of_prime_range {q : ℕ} (hq : Nat.Prime q)
    (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) :
    ∃ logarithms,
      jacobiOneSubLogBatchSearch g (jacobiIndexList q) = some logarithms ∧
        logarithms = (jacobiIndexList q).map (jacobiOneSubLogValue g) := by
  exact
    jacobiOneSubLogBatchSearch_exists_value_map_of_valid_indices hq g hg
      (fun x hx => jacobiIndexList_mem_valid hx)

/-- The executable Jacobi-exponent batch returns the pointwise coefficient exponents computed
from `jacobiOneSubLogValue` on every finite list of valid indices. -/
theorem jacobiExponentBatchSearch_exists_value_map_of_valid_indices {q P a b : ℕ} (hq : Nat.Prime q)
    (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (hP : 0 < P) {xs : List ℕ}
    (hvalid : ∀ x, x ∈ xs → 0 < x ∧ x < q - 1) :
    ∃ exponents,
      jacobiExponentBatchSearch (P := P) g a b xs = some exponents ∧
        exponents = xs.map (fun x => (a * x + b * jacobiOneSubLogValue g x) % P) := by
  induction xs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons x xs ih =>
    have hxmem : x ∈ x :: xs := List.mem_cons.mpr (Or.inl rfl)
    obtain ⟨target, fx, exponent, htarget, htable, hpoint, _, _, hformula, _⟩ :=
      jacobiExponentFromOneSubTable_some_of_primitiveRoot (a := a) (b := b) hq g hg
        (hvalid x hxmem).1 (hvalid x hxmem).2 hP
    have hlog : jacobiOneSubLogFromTable g x = some fx := by
      unfold jacobiOneSubLogFromTable
      rw [htarget]
      exact htable
    have hvalue : fx = jacobiOneSubLogValue g x := by
      unfold jacobiOneSubLogValue
      rw [hlog]
      rfl
    have htailvalid : ∀ y, y ∈ xs → 0 < y ∧ y < q - 1 := by
      intro y hy
      exact hvalid y (List.mem_cons.mpr (Or.inr hy))
    obtain ⟨exponents, htailsearch, htailmap⟩ := ih htailvalid
    have hexponent : exponent = (a * x + b * jacobiOneSubLogValue g x) % P := by
      rw [hformula, hvalue]
    refine ⟨exponent :: exponents, ?_, ?_⟩
    · change
        (match jacobiExponentFromOneSubTable (P := P) g a b x with
          | none => none
          | some exponent =>
            match jacobiExponentBatchSearch (P := P) g a b xs with
            | none => none
            | some exponents => some (exponent :: exponents)) =
          _
      rw [hpoint, htailsearch]
    · rw [List.map_cons, hexponent, htailmap]

/-- The standard Jacobi range therefore supplies the exact ordered exponent list consumed by
the coefficient-counted Jacobi sum. -/
theorem jacobiExponentBatchSearch_exists_value_map_of_prime_range {q P a b : ℕ} (hq : Nat.Prime q)
    (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (hP : 0 < P) :
    ∃ exponents,
      jacobiExponentBatchSearch (P := P) g a b (jacobiIndexList q) = some exponents ∧
        exponents =
          (jacobiIndexList q).map (fun x => (a * x + b * jacobiOneSubLogValue g x) % P) := by
  exact
    jacobiExponentBatchSearch_exists_value_map_of_valid_indices hq g hg hP
      (fun x hx => jacobiIndexList_mem_valid hx)

/-- Sum the root powers in a successful executable Jacobi exponent batch, retaining repeated
exponents as repeated summands. -/
def jacobiExponentListSum {R : Type*} [Semiring R] (exponents : List ℕ) (z : R) : R :=
  (exponents.map (fun e => z ^ e)).sum

/-- A successful prime-range exponent batch computes the coefficient-counted Jacobi sum exactly.
This connects the executable Option result to the finite coefficient formula while preserving
the multiplicity and order of every index. -/
theorem jacobiExponentBatchSearch_exists_sum_eq_jacobiSum {q P a b : ℕ} (hq : Nat.Prime q)
    (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (hP : 0 < P) {R : Type*} [Semiring R] (z : R) :
    ∃ exponents,
      jacobiExponentBatchSearch (P := P) g a b (jacobiIndexList q) = some exponents ∧
        jacobiExponentListSum exponents z =
          jacobiSumFromLogCoefficients q P a b (jacobiOneSubLogValue g) z := by
  obtain ⟨exponents, hsearch, hmap⟩ :=
    jacobiExponentBatchSearch_exists_value_map_of_prime_range (a := a) (b := b) hq g hg hP
  refine ⟨exponents, hsearch, ?_⟩
  rw [jacobiExponentListSum, hmap, List.map_map]
  exact (jacobiSumFromLogCoefficients_eq_indexListSum hP (jacobiOneSubLogValue g) z).symm

/-- For every prime auxiliary modulus and primitive-root generator, the complete interval of
powered character terms is computed by the executable Option exponent batch. -/
theorem jacobiPowerCharacter_finiteSum_eq_executableBatch {q P a b : ℕ} {R : Type*} [CommRing R]
    (hq : Nat.Prime q) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hPdiv : P ∣ q - 1) (hPpos : 0 < P) :
    ∃ exponents,
      jacobiExponentBatchSearch (P := P) g a b (jacobiIndexList q) = some exponents ∧
        (∑ x ∈ Finset.Icc 1 (q - 2),
            (jacobiPowerCharacter hq g hg ζ hζ hPdiv ((g ^ x : (ZMod q)ˣ) : ZMod q)) ^ a *
              (jacobiPowerCharacter hq g hg ζ hζ hPdiv (1 - (g : ZMod q) ^ x)) ^ b) =
          jacobiExponentListSum exponents (ζ : R) := by
  obtain ⟨exponents, hsearch, hsum⟩ :=
    jacobiExponentBatchSearch_exists_sum_eq_jacobiSum (a := a) (b := b) hq g hg hPpos (ζ : R)
  refine ⟨exponents, hsearch, ?_⟩
  rw [jacobiPowerCharacter_finiteSum_eq_coefficients hq g hg ζ hζ hPdiv hPpos]
  exact hsum.symm

/-- The actual finite-field Jacobi sum is computed by a successful executable exponent batch.
The finite-field character sum, coefficient aggregation, and ordered Option batch all have the
same value at the supplied root of unity. -/
theorem jacobiPowerCharacter_jacobiSum_eq_executableBatch {q P a b : ℕ} {R : Type*} [CommRing R]
    [Fintype (ZMod q)] (hq : Nat.Prime q) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hPdiv : P ∣ q - 1) (hPpos : 0 < P)
    [Finite { x : ℕ // 0 < x ∧ x < q - 1 }] :
    ∃ exponents,
      jacobiExponentBatchSearch (P := P) g a b (jacobiIndexList q) = some exponents ∧
        jacobiSum (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ a)
            (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ b) =
          jacobiExponentListSum exponents (ζ : R) := by
  have : Fintype { x : ℕ // 0 < x ∧ x < q - 1 } := Fintype.ofFinite _
  obtain ⟨exponents, hsearch, hsum⟩ :=
    jacobiPowerCharacter_finiteSum_eq_executableBatch (a := a) (b := b) hq g hg ζ hζ hPdiv hPpos
  refine ⟨exponents, hsearch, ?_⟩
  calc
    jacobiSum (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ a)
          (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ b) =
        jacobiSumFromLogCoefficients q P a b (jacobiOneSubLogValue g) (ζ : R) :=
      jacobiPowerCharacter_jacobiSum_eq_coefficients (a := a) (b := b) hq g hg ζ hζ hPdiv hPpos
    _ =
        ∑ x ∈ Finset.Icc 1 (q - 2),
          (jacobiPowerCharacter hq g hg ζ hζ hPdiv ((g ^ x : (ZMod q)ˣ) : ZMod q)) ^ a *
            (jacobiPowerCharacter hq g hg ζ hζ hPdiv (1 - (g : ZMod q) ^ x)) ^ b :=
      (jacobiPowerCharacter_finiteSum_eq_coefficients (a := a) (b := b) hq g hg ζ hζ hPdiv
          hPpos).symm
    _ = jacobiExponentListSum exponents (ζ : R) := hsum

/-- The actual powered-character Jacobi sum is represented by a `Fin P` coefficient array before
cyclotomic reduction. This is the direct interface from the proved Jacobi-sum formula to the
fixed-size coefficient-array implementation. -/
theorem jacobiPowerCharacter_jacobiSum_eq_fin_coefficients {q P a b : ℕ} {R : Type*} [CommRing R]
    [Fintype (ZMod q)] (hq : Nat.Prime q) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) (ζ : Rˣ)
    (hζ : (ζ : R) ^ P = 1) (hPdiv : P ∣ q - 1) (hPpos : 0 < P)
    [Finite { x : ℕ // 0 < x ∧ x < q - 1 }] :
    jacobiSum (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ a)
        (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ b) =
      ∑ r : Fin P,
        jacobiExponentCount (Finset.Icc 1 (q - 2))
            (fun x => (a * x + b * jacobiOneSubLogValue g x) % P) r.val •
          (ζ : R) ^ r.val := by
  calc
    jacobiSum (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ a)
          (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ b) =
        jacobiSumFromLogCoefficients q P a b (jacobiOneSubLogValue g) (ζ : R) :=
      jacobiPowerCharacter_jacobiSum_eq_coefficients hq g hg ζ hζ hPdiv hPpos
    _ =
        ∑ r : Fin P,
          jacobiExponentCount (Finset.Icc 1 (q - 2))
              (fun x => (a * x + b * jacobiOneSubLogValue g x) % P) r.val •
            (ζ : R) ^ r.val :=
      by
      unfold jacobiSumFromLogCoefficients
      exact
        jacobiCoefficientSum_eq_fin_sum P (Finset.Icc 1 (q - 2))
          (fun x => (a * x + b * jacobiOneSubLogValue g x) % P) (ζ : R)

/-- Materialize a bounded Jacobi exponent histogram as a fixed-size coefficient array over
`ZMod n`. Its length is the prime-power cyclotomic degree; counts outside that represented
degree are excluded by taking the cyclotomic period as the histogram bound. -/
def jacobiCoefficientFixedArray (n p k : ℕ) (hp : Nat.Prime p) {α : Type*} [DecidableEq α]
    (xs : Finset α) (exponent : α → ℕ) : cyclotomicFixedArray n p k :=
  ∑ r : Fin (primePowerIndex p k),
    cyclotomicFixedArrayScale n p k (jacobiExponentCount xs exponent r.val : ZMod n)
      (cyclotomicFixedArrayMonomialReduce n hp r.val)

/-- The coefficient array represents the same Jacobi histogram in the cyclotomic quotient.
This proves that array evaluation is a homomorphic image of the bounded coefficient sum. -/
theorem jacobiCoefficientFixedArray_class {n p k : ℕ} (hp : Nat.Prime p) {α : Type*} [DecidableEq α]
    (xs : Finset α) (exponent : α → ℕ) :
    cyclotomicFixedArrayClass n p k (jacobiCoefficientFixedArray n p k hp xs exponent) =
      jacobiCoefficientSum (primePowerIndex p k) xs exponent (cyclotomicRoot n p k) := by
  unfold jacobiCoefficientFixedArray
  rw [cyclotomicFixedArrayClass_sum]
  rw [jacobiCoefficientSum]
  rw [←
    Fin.sum_univ_eq_sum_range
      (fun e : ℕ => jacobiExponentCount xs exponent e • cyclotomicRoot n p k ^ e)
      (primePowerIndex p k)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [cyclotomicFixedArrayClass_scale]
  rw [cyclotomicFixedArrayMonomialReduce_correct]
  simp only [nsmul_eq_mul, map_natCast]

/-- Binary exponentiation of the coefficient array represents the corresponding power of its
Jacobi coefficient sum in the cyclotomic quotient. This is the power interface for weighted
Jacobi products. -/
theorem jacobiCoefficientFixedArray_pow_class {n p k : ℕ} (hp : Nat.Prime p) {α : Type*}
    [DecidableEq α] (xs : Finset α) (exponent : α → ℕ) (u : ℕ) :
    cyclotomicFixedArrayClass n p k
        (cyclotomicFixedArrayPowBySquaring n hp (jacobiCoefficientFixedArray n p k hp xs exponent)
          u) =
      (jacobiCoefficientSum (primePowerIndex p k) xs exponent (cyclotomicRoot n p k)) ^ u := by
  rw [cyclotomicFixedArrayPowBySquaring_class]
  rw [jacobiCoefficientFixedArray_class]

/-- Multiply finitely many ring elements raised to the APR-CL weight `⌊n*x/P⌋`. -/
def aprclFiniteWeightedProduct {M : Type*} [CommMonoid M] (xs : Finset ℕ) (term : ℕ → M)
    (exponent : ℕ → ℕ) : M :=
  ∏ x ∈ xs, term x ^ exponent x

/-- Split one APR-CL weight after writing `n = u*P+r`. The positive period condition is required
for the natural-number quotient identity. -/
theorem aprclWeightedExponentSplit {n P u r x : ℕ} (hP : 0 < P) (hn : n = u * P + r) :
    n * x / P = u * x + r * x / P := by
  calc
    n * x / P = ((u * P + r) * x) / P := by rw [hn]
    _ = (u * P * x + r * x) / P := by rw [Nat.add_mul]
    _ = (P * (u * x) + r * x) / P := by
      have hmul : u * P * x = P * (u * x) := by
        calc
          u * P * x = u * (P * x) := Nat.mul_assoc u P x
          _ = P * (u * x) := Nat.mul_left_comm u P x
      exact congrArg (fun z : ℕ ↦ z / P) (congrArg (fun z : ℕ ↦ z + r * x) hmul)
    _ = u * x + r * x / P := Nat.mul_add_div hP (u * x) (r * x)

/-- The finite weighted product factors as one shared large power and a residual product when
`n = u*P+r`. This is the product identity used by the APR-CL implementation's `A^u B` rewrite. -/
theorem aprclFiniteWeightedProduct_eq_power_mul_remainder {M : Type*} [CommMonoid M] (xs : Finset ℕ)
    (term : ℕ → M) (n P u r : ℕ) (hP : 0 < P) (hn : n = u * P + r) :
    aprclFiniteWeightedProduct xs term (fun x ↦ n * x / P) =
      aprclFiniteWeightedProduct xs term (fun x ↦ x) ^ u *
        aprclFiniteWeightedProduct xs term (fun x ↦ r * x / P) := by
  unfold aprclFiniteWeightedProduct
  calc
    (∏ x ∈ xs, term x ^ (n * x / P)) = ∏ x ∈ xs, (term x ^ (u * x) * term x ^ (r * x / P)) := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [aprclWeightedExponentSplit hP hn, pow_add]
    _ = (∏ x ∈ xs, (term x ^ x) ^ u) * ∏ x ∈ xs, term x ^ (r * x / P) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      · apply Finset.prod_congr rfl
        intro x hx
        exact (congrArg (fun e : ℕ ↦ term x ^ e) (Nat.mul_comm u x)).trans (pow_mul (term x) x u)
    _ = (∏ x ∈ xs, term x ^ x) ^ u * ∏ x ∈ xs, term x ^ (r * x / P) := by rw [← Finset.prod_pow]

/-- Specialize the weighted-product factorization to Euclidean quotient and remainder. The
indexing period must be positive; the update uses the ordinary natural-number remainder. -/
theorem aprclFiniteWeightedProduct_eq_power_mul_mod {M : Type*} [CommMonoid M] (xs : Finset ℕ)
    (term : ℕ → M) (n P : ℕ) (hP : 0 < P) :
    aprclFiniteWeightedProduct xs term (fun x ↦ n * x / P) =
      aprclFiniteWeightedProduct xs term (fun x ↦ x) ^ (n / P) *
        aprclFiniteWeightedProduct xs term (fun x ↦ n % P * x / P) := by
  have hn : n = n / P * P + n % P := by
    calc
      n = n % P + P * (n / P) := (Nat.mod_add_div n P).symm
      _ = n / P * P + n % P := by
        rw [Nat.mul_comm P (n / P)]
        rw [Nat.add_comm]
  exact aprclFiniteWeightedProduct_eq_power_mul_remainder xs term n P (n / P) (n % P) hP hn

/-- The same quotient-remainder update specialized to the APR-CL cyclotomic quotient. Here each
term may be a Jacobi sum or one of its substituted images, so the result is the ring-level
`W = A^u B` interface consumed by later local tests. -/
theorem aprclCyclotomicWeightedProduct_eq_power_mul_mod {n p k : ℕ} (xs : Finset ℕ)
    (term : ℕ → cyclotomicQuotient n p k) (input : ℕ) (hP : 0 < primePowerIndex p k) :
    aprclFiniteWeightedProduct xs term (fun x ↦ input * x / primePowerIndex p k) =
      aprclFiniteWeightedProduct xs term (fun x ↦ x) ^ (input / primePowerIndex p k) *
        aprclFiniteWeightedProduct xs term
          (fun x ↦ input % primePowerIndex p k * x / primePowerIndex p k) :=
  aprclFiniteWeightedProduct_eq_power_mul_mod xs term input (primePowerIndex p k) hP

/-- Evaluate the weighted product over an ordered, duplicate-free input list. This form aligns
with executable array products while preserving the same quotient-remainder update as the Finset
specification. -/
def aprclListWeightedProduct {M : Type*} [CommMonoid M] (xs : List ℕ) (term : ℕ → M)
    (weight : ℕ → ℕ) : M :=
  (xs.map (fun x => term x ^ weight x)).prod

/-- A duplicate-free list implementation of the APR-CL weighted product satisfies the `A^u B`
update, by converting the list product to its finite-set product and using Euclidean division. -/
theorem aprclListWeightedProduct_eq_power_mul_mod {M : Type*} [CommMonoid M] (xs : List ℕ)
    (hxs : xs.Nodup) (term : ℕ → M) (input P : ℕ) (hP : 0 < P) :
    aprclListWeightedProduct xs term (fun x => input * x / P) =
      aprclListWeightedProduct xs term (fun x => x) ^ (input / P) *
        aprclListWeightedProduct xs term (fun x => input % P * x / P) := by
  unfold aprclListWeightedProduct
  rw [← List.prod_toFinset (fun x => term x ^ (input * x / P)) hxs]
  rw [← List.prod_toFinset (fun x => term x ^ x) hxs]
  rw [← List.prod_toFinset (fun x => term x ^ (input % P * x / P)) hxs]
  exact aprclFiniteWeightedProduct_eq_power_mul_mod xs.toFinset term input P hP

/-- Combine a powered Jacobi coefficient array with a second coefficient array using the
executable expansion multiplication. The result is the fixed-size representation of a weighted
product and is consumed by the APR-CL cyclotomic-product interface. -/
def jacobiWeightedProductFixedArray (n p k : ℕ) (hp : Nat.Prime p) {α : Type*} [DecidableEq α]
    (xs : Finset α) (exponent₁ exponent₂ : α → ℕ) (u : ℕ) : cyclotomicFixedArray n p k :=
  cyclotomicFixedArrayMulByExpansion n hp
    (cyclotomicFixedArrayPowBySquaring n hp (jacobiCoefficientFixedArray n p k hp xs exponent₁) u)
    (jacobiCoefficientFixedArray n p k hp xs exponent₂)

/-- The weighted fixed-array product evaluates to the matching product of coefficient sums in
the cyclotomic quotient. This is the array-level multiplication and power contract. -/
theorem jacobiWeightedProductFixedArray_class {n p k : ℕ} (hp : Nat.Prime p) {α : Type*}
    [DecidableEq α] (xs : Finset α) (exponent₁ exponent₂ : α → ℕ) (u : ℕ) :
    cyclotomicFixedArrayClass n p k
        (jacobiWeightedProductFixedArray n p k hp xs exponent₁ exponent₂ u) =
      (jacobiCoefficientSum (primePowerIndex p k) xs exponent₁ (cyclotomicRoot n p k)) ^ u *
        jacobiCoefficientSum (primePowerIndex p k) xs exponent₂ (cyclotomicRoot n p k) := by
  unfold jacobiWeightedProductFixedArray
  rw [cyclotomicFixedArrayMulByExpansion_class_eq_mul]
  rw [cyclotomicFixedArrayPowBySquaring_class]
  rw [jacobiCoefficientFixedArray_class]
  rw [jacobiCoefficientFixedArray_class]

/-- Multiply the fixed arrays of a finite family of Jacobi coefficient sums. The family is a
list of exponent functions over one finite-field summation set, matching the outer finite product
used in APR-CL weighted Jacobi expressions. -/
def jacobiCoefficientProductFixedArray (n p k : ℕ) (hp : Nat.Prime p) {α : Type*} [DecidableEq α]
    (xs : Finset α) (exponents : List (α → ℕ)) : cyclotomicFixedArray n p k :=
  cyclotomicFixedArrayProductList n hp (exponents.map (jacobiCoefficientFixedArray n p k hp xs))

/-- The list product of Jacobi coefficient arrays evaluates to the product of their coefficient
sums in the cyclotomic quotient. -/
theorem jacobiCoefficientProductFixedArray_class {n p k : ℕ} (hp : Nat.Prime p) {α : Type*}
    [DecidableEq α] (xs : Finset α) (exponents : List (α → ℕ)) :
    cyclotomicFixedArrayClass n p k (jacobiCoefficientProductFixedArray n p k hp xs exponents) =
      (exponents.map
          (fun exponent =>
            jacobiCoefficientSum (primePowerIndex p k) xs exponent
              (cyclotomicRoot n p k))).prod := by
  unfold jacobiCoefficientProductFixedArray
  rw [cyclotomicFixedArrayProductList_class]
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro exponent _
  exact jacobiCoefficientFixedArray_class hp xs exponent

/-- Build a finite product of powered Jacobi coefficient arrays. Each outer index selects its own
Jacobi exponent function and natural power, while the inner finite field sum set is shared. -/
def jacobiCoefficientWeightedProductFixedArray (n p k : ℕ) (hp : Nat.Prime p) {α β : Type*}
    [DecidableEq β] (sumIndices : Finset β) (productIndices : List α) (exponent : α → β → ℕ)
    (weight : α → ℕ) : cyclotomicFixedArray n p k :=
  cyclotomicFixedArrayWeightedProductList n hp productIndices
    (fun x => jacobiCoefficientFixedArray n p k hp sumIndices (exponent x)) weight

/-- The weighted coefficient-array product decodes to the matching product of powered Jacobi
coefficient sums in the cyclotomic quotient. -/
theorem jacobiCoefficientWeightedProductFixedArray_class {n p k : ℕ} (hp : Nat.Prime p)
    {α β : Type*} [DecidableEq β] (sumIndices : Finset β) (productIndices : List α)
    (exponent : α → β → ℕ) (weight : α → ℕ) :
    cyclotomicFixedArrayClass n p k
        (jacobiCoefficientWeightedProductFixedArray n p k hp sumIndices productIndices exponent
          weight) =
      (productIndices.map
          (fun x =>
            jacobiCoefficientSum (primePowerIndex p k) sumIndices (exponent x)
                (cyclotomicRoot n p k) ^
              weight x)).prod := by
  unfold jacobiCoefficientWeightedProductFixedArray
  rw [cyclotomicFixedArrayWeightedProductList_class]
  apply congrArg List.prod
  apply List.map_congr_left
  intro x _
  rw [jacobiCoefficientFixedArray_class]

/-- The fixed-array backend for a finite family of Jacobi coefficient sums evaluates the large
floor-weighted product as one quotient power and the smaller remainder-weighted product. -/
theorem jacobiCoefficientWeightedProductFixedArray_eq_power_mul_mod {n p k : ℕ} (hp : Nat.Prime p)
    {β : Type*} [DecidableEq β] (sumIndices : Finset β) (productIndices : List ℕ)
    (hindices : productIndices.Nodup) (exponent : ℕ → β → ℕ) (input : ℕ)
    (hP : 0 < primePowerIndex p k) :
    cyclotomicFixedArrayClass n p k
        (jacobiCoefficientWeightedProductFixedArray n p k hp sumIndices productIndices exponent
          (fun x => input * x / primePowerIndex p k)) =
      aprclListWeightedProduct productIndices
            (fun x =>
              jacobiCoefficientSum (primePowerIndex p k) sumIndices (exponent x)
                (cyclotomicRoot n p k))
            (fun x => x) ^
          (input / primePowerIndex p k) *
        aprclListWeightedProduct productIndices
          (fun x =>
            jacobiCoefficientSum (primePowerIndex p k) sumIndices (exponent x)
              (cyclotomicRoot n p k))
          (fun x => input % primePowerIndex p k * x / primePowerIndex p k) := by
  rw [jacobiCoefficientWeightedProductFixedArray_class]
  exact
    aprclListWeightedProduct_eq_power_mul_mod productIndices hindices
      (fun x =>
        jacobiCoefficientSum (primePowerIndex p k) sumIndices (exponent x) (cyclotomicRoot n p k))
      input (primePowerIndex p k) hP

/-- Evaluate the actual powered-character Jacobi sum in the prime-power cyclotomic quotient by
the executable fixed coefficient array. This closes the finite-field sum to quotient-array bridge;
the hypotheses retain the explicit root-of-unity order and auxiliary-prime range conditions. -/
theorem jacobiPowerCharacter_jacobiSum_eq_cyclotomicArray {q a b n p k : ℕ} [Fintype (ZMod q)]
    (hq : Nat.Prime q) (hp : Nat.Prime p) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1))
    (ζ : (cyclotomicQuotient n p k)ˣ)
    (hζ : (ζ : cyclotomicQuotient n p k) ^ primePowerIndex p k = 1)
    (hζroot : (ζ : cyclotomicQuotient n p k) = cyclotomicRoot n p k)
    (hPdiv : primePowerIndex p k ∣ q - 1) (hPpos : 0 < primePowerIndex p k)
    [Finite { x : ℕ // 0 < x ∧ x < q - 1 }] :
    jacobiSum (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ a)
        (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ b) =
      cyclotomicFixedArrayClass n p k
        (jacobiCoefficientFixedArray n p k hp (Finset.Icc 1 (q - 2))
          (fun x => (a * x + b * jacobiOneSubLogValue g x) % primePowerIndex p k)) := by
  calc
    jacobiSum (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ a)
          (jacobiPowerCharacter hq g hg ζ hζ hPdiv ^ b) =
        jacobiSumFromLogCoefficients (q := q) (P := primePowerIndex p k) a b
          (jacobiOneSubLogValue g) (ζ : cyclotomicQuotient n p k) :=
      jacobiPowerCharacter_jacobiSum_eq_coefficients hq g hg ζ hζ hPdiv hPpos
    _ =
        jacobiCoefficientSum (primePowerIndex p k) (Finset.Icc 1 (q - 2))
          (fun x => (a * x + b * jacobiOneSubLogValue g x) % primePowerIndex p k)
          (cyclotomicRoot n p k) :=
      by
      rw [jacobiSumFromLogCoefficients]
      rw [← hζroot]
    _ =
        cyclotomicFixedArrayClass n p k
          (jacobiCoefficientFixedArray n p k hp (Finset.Icc 1 (q - 2))
            (fun x => (a * x + b * jacobiOneSubLogValue g x) % primePowerIndex p k)) :=
      by
      exact
        (jacobiCoefficientFixedArray_class hp (Finset.Icc 1 (q - 2))
            (fun x => (a * x + b * jacobiOneSubLogValue g x) % primePowerIndex p k)).symm

/-- The canonical cyclotomic root itself supplies the root-of-unity character value, so the
finite-field Jacobi sum reaches the coefficient array without an externally supplied root. -/
theorem jacobiPowerCharacter_jacobiSum_eq_cyclotomicArray_of_canonicalRoot {q a b n p k : ℕ}
    [Fintype (ZMod q)] (hq : Nat.Prime q) (hp : Nat.Prime p) (g : (ZMod q)ˣ)
    (hg : IsPrimitiveRoot g (q - 1)) (hPdiv : primePowerIndex p k ∣ q - 1)
    [Finite { x : ℕ // 0 < x ∧ x < q - 1 }] :
    jacobiSum
        (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
            (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
          a)
        (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
            (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
          b) =
      cyclotomicFixedArrayClass n p k
        (jacobiCoefficientFixedArray n p k hp (Finset.Icc 1 (q - 2))
          (fun x => (a * x + b * jacobiOneSubLogValue g x) % primePowerIndex p k)) := by
  exact
    jacobiPowerCharacter_jacobiSum_eq_cyclotomicArray hq hp g hg (cyclotomicRootUnit n hp)
      (cyclotomicRoot_pow_index_eq_one n hp) (cyclotomicRootUnit_val n hp) hPdiv
      (Nat.pow_pos hp.pos)

/-- A natural power of the canonical powered-character Jacobi sum is computed by binary
exponentiation of its fixed coefficient array. This exposes the powered factor used in the
APR-CL weighted-product branches. -/
theorem jacobiPowerCharacter_jacobiSum_pow_eq_cyclotomicArrayPow {q a b n p k : ℕ}
    [Fintype (ZMod q)] (hq : Nat.Prime q) (hp : Nat.Prime p) (g : (ZMod q)ˣ)
    (hg : IsPrimitiveRoot g (q - 1)) (hPdiv : primePowerIndex p k ∣ q - 1) (u : ℕ)
    [Finite { x : ℕ // 0 < x ∧ x < q - 1 }] :
    (jacobiSum
          (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
              (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
            a)
          (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
              (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
            b)) ^
        u =
      cyclotomicFixedArrayClass n p k
        (cyclotomicFixedArrayPowBySquaring n hp
          (jacobiCoefficientFixedArray n p k hp (Finset.Icc 1 (q - 2))
            (fun x => (a * x + b * jacobiOneSubLogValue g x) % primePowerIndex p k))
          u) := by
  rw [jacobiPowerCharacter_jacobiSum_eq_cyclotomicArray_of_canonicalRoot hq hp g hg hPdiv]
  rw [jacobiCoefficientFixedArray_class]
  rw [← jacobiCoefficientFixedArray_pow_class]

/-- Evaluate a power of one powered-character Jacobi sum times a second one through the fixed
coefficient arrays. This is the executable weighted-product bridge used by the APR-CL criterion. -/
theorem jacobiPowerCharacter_weightedJacobiProduct_eq_cyclotomicArray {q a b c d n p k : ℕ}
    [Fintype (ZMod q)] (hq : Nat.Prime q) (hp : Nat.Prime p) (g : (ZMod q)ˣ)
    (hg : IsPrimitiveRoot g (q - 1)) (hPdiv : primePowerIndex p k ∣ q - 1) (u : ℕ)
    [Finite { x : ℕ // 0 < x ∧ x < q - 1 }] :
    (jacobiSum
            (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
                (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
              a)
            (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
                (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
              b)) ^
          u *
        jacobiSum
          (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
              (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
            c)
          (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
              (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
            d) =
      cyclotomicFixedArrayClass n p k
        (jacobiWeightedProductFixedArray n p k hp (Finset.Icc 1 (q - 2))
          (fun x => (a * x + b * jacobiOneSubLogValue g x) % primePowerIndex p k)
          (fun x => (c * x + d * jacobiOneSubLogValue g x) % primePowerIndex p k) u) := by
  rw [jacobiPowerCharacter_jacobiSum_pow_eq_cyclotomicArrayPow hq hp g hg hPdiv]
  rw [jacobiPowerCharacter_jacobiSum_eq_cyclotomicArray_of_canonicalRoot hq hp g hg hPdiv]
  rw [jacobiCoefficientFixedArray_pow_class]
  rw [jacobiCoefficientFixedArray_class]
  rw [← jacobiWeightedProductFixedArray_class]

/-- Evaluate an ordered weighted product of actual finite-field Jacobi sums by its executable
fixed coefficient array. Each list index selects the two character exponents of one Jacobi sum. -/
theorem jacobiPowerCharacterWeightedProductFixedArray_class {q n p k : ℕ} [Fintype (ZMod q)]
    (hq : Nat.Prime q) (hp : Nat.Prime p) (g : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1))
    (hPdiv : primePowerIndex p k ∣ q - 1) (productIndices : List ℕ)
    (exponent₁ exponent₂ weight : ℕ → ℕ) [Finite { x : ℕ // 0 < x ∧ x < q - 1 }] :
    (productIndices.map
          (fun x =>
            (jacobiSum
                (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
                    (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
                  exponent₁ x)
                (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
                    (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
                  exponent₂ x)) ^
              weight x)).prod =
      cyclotomicFixedArrayClass n p k
        (jacobiCoefficientWeightedProductFixedArray n p k hp (Finset.Icc 1 (q - 2)) productIndices
          (fun x y =>
            (exponent₁ x * y + exponent₂ x * jacobiOneSubLogValue g y) % primePowerIndex p k)
          weight) := by
  rw [jacobiCoefficientWeightedProductFixedArray_class]
  apply congrArg List.prod
  apply List.map_congr_left
  intro x _
  apply congrArg (fun z : cyclotomicQuotient n p k => z ^ weight x)
  calc
    jacobiSum
          (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
              (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
            exponent₁ x)
          (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
              (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
            exponent₂ x) =
        cyclotomicFixedArrayClass n p k
          (jacobiCoefficientFixedArray n p k hp (Finset.Icc 1 (q - 2))
            (fun y =>
              (exponent₁ x * y + exponent₂ x * jacobiOneSubLogValue g y) % primePowerIndex p k)) :=
      jacobiPowerCharacter_jacobiSum_eq_cyclotomicArray_of_canonicalRoot hq hp g hg hPdiv
    _ =
        jacobiCoefficientSum (primePowerIndex p k) (Finset.Icc 1 (q - 2))
          (fun y =>
            (exponent₁ x * y + exponent₂ x * jacobiOneSubLogValue g y) % primePowerIndex p k)
          (cyclotomicRoot n p k) :=
      jacobiCoefficientFixedArray_class hp (Finset.Icc 1 (q - 2)) _

/-- The list of actual APR-CL Jacobi sums follows the quotient-remainder `A^u B` update through
the fixed-array backend, with each index carrying its floor weight. -/
theorem jacobiPowerCharacterWeightedProductFixedArray_eq_power_mul_mod {q n p k : ℕ}
    [Fintype (ZMod q)] (hq : Nat.Prime q) (hp : Nat.Prime p) (g : (ZMod q)ˣ)
    (hg : IsPrimitiveRoot g (q - 1)) (hPdiv : primePowerIndex p k ∣ q - 1) (productIndices : List ℕ)
    (hindices : productIndices.Nodup) (exponent₁ exponent₂ : ℕ → ℕ) (input : ℕ)
    (hP : 0 < primePowerIndex p k) [Finite { x : ℕ // 0 < x ∧ x < q - 1 }] :
    (productIndices.map
          (fun x =>
            (jacobiSum
                (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
                    (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
                  exponent₁ x)
                (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
                    (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
                  exponent₂ x)) ^
              (input * x / primePowerIndex p k))).prod =
      (productIndices.map
              (fun x =>
                jacobiSum
                    (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
                        (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
                      exponent₁ x)
                    (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
                        (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
                      exponent₂ x) ^
                  x)).prod ^
          (input / primePowerIndex p k) *
        (productIndices.map
            (fun x =>
              (jacobiSum
                  (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
                      (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
                    exponent₁ x)
                  (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
                      (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
                    exponent₂ x)) ^
                (input % primePowerIndex p k * x / primePowerIndex p k))).prod := by
  calc
    _ =
        cyclotomicFixedArrayClass n p k
          (jacobiCoefficientWeightedProductFixedArray n p k hp (Finset.Icc 1 (q - 2)) productIndices
            (fun x y =>
              (exponent₁ x * y + exponent₂ x * jacobiOneSubLogValue g y) % primePowerIndex p k)
            (fun x => input * x / primePowerIndex p k)) :=
      jacobiPowerCharacterWeightedProductFixedArray_class hq hp g hg hPdiv productIndices exponent₁
        exponent₂ (fun x => input * x / primePowerIndex p k)
    _ =
        aprclListWeightedProduct productIndices
              (fun x =>
                jacobiCoefficientSum (primePowerIndex p k) (Finset.Icc 1 (q - 2))
                  (fun y =>
                    (exponent₁ x * y + exponent₂ x * jacobiOneSubLogValue g y) %
                      primePowerIndex p k)
                  (cyclotomicRoot n p k))
              (fun x => x) ^
            (input / primePowerIndex p k) *
          aprclListWeightedProduct productIndices
            (fun x =>
              jacobiCoefficientSum (primePowerIndex p k) (Finset.Icc 1 (q - 2))
                (fun y =>
                  (exponent₁ x * y + exponent₂ x * jacobiOneSubLogValue g y) % primePowerIndex p k)
                (cyclotomicRoot n p k))
            (fun x => input % primePowerIndex p k * x / primePowerIndex p k) :=
      by
      exact
        jacobiCoefficientWeightedProductFixedArray_eq_power_mul_mod hp (Finset.Icc 1 (q - 2))
          productIndices hindices
          (fun x y =>
            (exponent₁ x * y + exponent₂ x * jacobiOneSubLogValue g y) % primePowerIndex p k)
          input hP
    _ = _ := by
      have hrepr (weight : ℕ → ℕ) :
        aprclListWeightedProduct productIndices
            (fun x =>
              jacobiCoefficientSum (primePowerIndex p k) (Finset.Icc 1 (q - 2))
                (fun y =>
                  (exponent₁ x * y + exponent₂ x * jacobiOneSubLogValue g y) % primePowerIndex p k)
                (cyclotomicRoot n p k))
            weight =
          (productIndices.map
              (fun x =>
                jacobiSum
                    (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
                        (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
                      exponent₁ x)
                    (jacobiPowerCharacter hq g hg (cyclotomicRootUnit n hp)
                        (cyclotomicRoot_pow_index_eq_one n hp) hPdiv ^
                      exponent₂ x) ^
                  weight x)).prod := by
        unfold aprclListWeightedProduct
        calc
          _ =
              cyclotomicFixedArrayClass n p k
                (jacobiCoefficientWeightedProductFixedArray n p k hp (Finset.Icc 1 (q - 2))
                  productIndices
                  (fun x y =>
                    (exponent₁ x * y + exponent₂ x * jacobiOneSubLogValue g y) %
                      primePowerIndex p k)
                  weight) :=
            by
            exact
              (jacobiCoefficientWeightedProductFixedArray_class hp (Finset.Icc 1 (q - 2))
                  productIndices
                  (fun x y =>
                    (exponent₁ x * y + exponent₂ x * jacobiOneSubLogValue g y) %
                      primePowerIndex p k)
                  weight).symm
          _ = _ :=
            (jacobiPowerCharacterWeightedProductFixedArray_class hq hp g hg hPdiv productIndices
                exponent₁ exponent₂ weight).symm
      rw [hrepr (fun x => x),
        hrepr (fun x => input % primePowerIndex p k * x / primePowerIndex p k)]

/-- A list-indexed form of the APR-CL quotient-remainder update. The weight uses a natural index
attached to each item, so items may carry data from different auxiliary finite fields. -/
theorem aprclListIndexedWeightedProduct_eq_power_mul_mod {α M : Type*} [CommMonoid M] (xs : List α)
    (term : α → M) (index : α → ℕ) (input P : ℕ) (hP : 0 < P) :
    (xs.map (fun x => term x ^ (input * index x / P))).prod =
      (xs.map (fun x => term x ^ index x)).prod ^ (input / P) *
        (xs.map (fun x => term x ^ (input % P * index x / P))).prod := by
  have hn : input = input / P * P + input % P := by
    calc
      input = input % P + P * (input / P) := (Nat.mod_add_div input P).symm
      _ = input / P * P + input % P := by rw [Nat.mul_comm P (input / P), Nat.add_comm]
  induction xs with
  | nil => simp only [List.map_nil, List.prod_nil, one_pow, one_mul]
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [aprclWeightedExponentSplit hP hn, pow_add, ih, mul_pow]
    rw [Nat.mul_comm (input / P) (index x), pow_mul]
    ac_rfl

/-- Input data for one APR-CL Jacobi factor. It records the auxiliary prime, a primitive root of
its finite field, the two character exponents, the APR-CL index, and the period divisibility needed
to evaluate the factor in the common prime-power cyclotomic quotient. -/
structure APRCLJacobiDatum (p k : ℕ) where
  /-- Auxiliary prime defining the finite field. -/
  q : ℕ
  /-- Primality of the auxiliary field characteristic. -/
  qPrime : Nat.Prime q
  /-- The finite-field structure used by Mathlib's Jacobi sum. -/
  fieldFinite : Fintype (ZMod q)
  /-- Finiteness of the nonzero exponent range used by the Jacobi-sum formula. -/
  unitIndexFinite : Finite { x : ℕ // 0 < x ∧ x < q - 1 }
  /-- Primitive root used to parameterize the nonzero field elements. -/
  generator : (ZMod q)ˣ
  /-- The generator has order `q - 1`. -/
  generatorPrimitive : IsPrimitiveRoot generator (q - 1)
  /-- First exponent of the powered character. -/
  exponent₁ : ℕ
  /-- Second exponent of the powered character. -/
  exponent₂ : ℕ
  /-- APR-CL product index attached to this Jacobi factor. -/
  index : ℕ
  /-- The common cyclotomic period divides the finite-field unit-group order. -/
  periodDivides : primePowerIndex p k ∣ q - 1

/-- An APR-CL Jacobi datum carrying the branch parameters it is supposed to represent.

The exponent equalities identify the two powered characters. The inherited `periodDivides`
field gives divisibility by `p^(k+1)`; `nextPower_not_dvd` excludes `p^(k+2)`, so the
auxiliary-prime order has exactly the required p-adic valuation. -/
structure APRCLJacobiDatumWithParameters (p k a b : ℕ) where
  /-- Primality of the cyclotomic index prime. -/
  indexPrime : Nat.Prime p
  /-- Underlying finite-field Jacobi-sum data. -/
  datum : APRCLJacobiDatum p k
  /-- The first character exponent is the specified branch exponent. -/
  exponent₁_eq : datum.exponent₁ = a
  /-- The second character exponent is the specified branch exponent. -/
  exponent₂_eq : datum.exponent₂ = b
  /-- The next p-power does not divide the auxiliary-prime unit-group order. -/
  nextPower_not_dvd : ¬primePowerIndex p (k + 1) ∣ datum.q - 1

/-- The actual Mathlib Jacobi sum associated to one APR-CL datum, represented in the common
prime-power cyclotomic quotient. -/
noncomputable def APRCLJacobiDatum.jacobiSumValue {p k : ℕ} (n : ℕ) (hp : Nat.Prime p)
    (datum : APRCLJacobiDatum p k) : cyclotomicQuotient n p k := by
  letI : Fintype (ZMod datum.q) := datum.fieldFinite
  exact
    jacobiSum
      (jacobiPowerCharacter datum.qPrime datum.generator datum.generatorPrimitive
          (cyclotomicRootUnit n hp) (cyclotomicRoot_pow_index_eq_one n hp) datum.periodDivides ^
        datum.exponent₁)
      (jacobiPowerCharacter datum.qPrime datum.generator datum.generatorPrimitive
          (cyclotomicRootUnit n hp) (cyclotomicRoot_pow_index_eq_one n hp) datum.periodDivides ^
        datum.exponent₂)

/-- The coprime root-power automorphism multiplies the two character exponents in the
actual Jacobi-sum value. The auxiliary field, generator, and product index are preserved. -/
theorem APRCLJacobiDatum.rootPowerSubstitution_jacobiSumValue {n p k i : ℕ} (hp : Nat.Prime p)
    (hpn : Nat.Coprime p n) (hi : Nat.Coprime i (primePowerIndex p k))
    (datum : APRCLJacobiDatum p k) :
    cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hi (datum.jacobiSumValue n hp) =
      ({ datum with
              exponent₁ := i * datum.exponent₁
              exponent₂ := i * datum.exponent₂ } :
            APRCLJacobiDatum p k).jacobiSumValue
        n hp := by
  let f := (cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hi).toRingHom
  have hf :
    f (cyclotomicRootUnit n (p := p) (k := k) hp : cyclotomicQuotient n p k) =
      (cyclotomicRootUnit n (p := p) (k := k) hp : cyclotomicQuotient n p k) ^ i := by
    rw [cyclotomicRootUnit_val]
    exact cyclotomicRootPowerSubstitutionEquiv_of_coprime_map_root n hp hpn hi
  change f (datum.jacobiSumValue n hp) = _
  simpa only [APRCLJacobiDatum.jacobiSumValue] using
    (@jacobiPowerCharacter_jacobiSum_ringHomComp datum.q (primePowerIndex p k) datum.exponent₁
      datum.exponent₂ (cyclotomicQuotient n p k) _ datum.fieldFinite datum.qPrime datum.generator
      datum.generatorPrimitive (cyclotomicRootUnit n hp) (cyclotomicRoot_pow_index_eq_one n hp)
      datum.periodDivides f i hf)

/-- The executable coefficient array for one APR-CL Jacobi datum. Its exponent function is the
logarithmic coefficient formula `a*y + b*f_q(y)` reduced modulo the common period. -/
def APRCLJacobiDatum.coefficientArray {p k : ℕ} (n : ℕ) (hp : Nat.Prime p)
    (datum : APRCLJacobiDatum p k) : cyclotomicFixedArray n p k :=
  jacobiCoefficientFixedArray n p k hp (Finset.Icc 1 (datum.q - 2))
    (fun y =>
      (datum.exponent₁ * y + datum.exponent₂ * jacobiOneSubLogValue datum.generator y) %
        primePowerIndex p k)

/-- The Jacobi value of a datum equals the quotient image of its finite coefficient array. -/
theorem APRCLJacobiDatum.jacobiSumValue_eq_coefficientArray {p k : ℕ} (n : ℕ) (hp : Nat.Prime p)
    (datum : APRCLJacobiDatum p k) :
    datum.jacobiSumValue n hp = cyclotomicFixedArrayClass n p k (datum.coefficientArray n hp) := by
  exact
    @jacobiPowerCharacter_jacobiSum_eq_cyclotomicArray_of_canonicalRoot datum.q datum.exponent₁
      datum.exponent₂ n p k datum.fieldFinite datum.qPrime hp datum.generator
      datum.generatorPrimitive datum.periodDivides datum.unitIndexFinite

/-- The fixed-array product of a list of APR-CL data, allowing each factor to use its own
auxiliary finite field. -/
def aprclJacobiDatumWeightedArray {p k : ℕ} (n : ℕ) (hp : Nat.Prime p)
    (data : List (APRCLJacobiDatum p k)) (weight : APRCLJacobiDatum p k → ℕ) :
    cyclotomicFixedArray n p k :=
  cyclotomicFixedArrayWeightedProductList n hp data (fun datum => datum.coefficientArray n hp)
    weight

/-- Decode the executable weighted product of per-prime Jacobi arrays to the corresponding list of
actual Mathlib Jacobi sums. Unlike the fixed-field interface, each datum may have its own `q`. -/
theorem aprclJacobiDatumWeightedArray_class {n p k : ℕ} (hp : Nat.Prime p)
    (data : List (APRCLJacobiDatum p k)) (weight : APRCLJacobiDatum p k → ℕ) :
    cyclotomicFixedArrayClass n p k (aprclJacobiDatumWeightedArray n hp data weight) =
      (data.map (fun datum => datum.jacobiSumValue n hp ^ weight datum)).prod := by
  unfold aprclJacobiDatumWeightedArray
  rw [cyclotomicFixedArrayWeightedProductList_class]
  apply congrArg List.prod
  apply List.map_congr_left
  intro datum _
  exact
    congrArg (fun z : cyclotomicQuotient n p k => z ^ weight datum)
      (datum.jacobiSumValue_eq_coefficientArray n hp).symm

/-- Evaluate a weighted product of Jacobi data after attaching branch-exponent and exact-valuation
evidence to each entry. The evidence restricts inputs; coefficient evaluation uses the underlying
datum unchanged. -/
def aprclValidatedJacobiDatumWeightedArray {p k a b n : ℕ} (hp : Nat.Prime p)
    (data : List (APRCLJacobiDatumWithParameters p k a b)) (weight : APRCLJacobiDatum p k → ℕ) :
    cyclotomicFixedArray n p k :=
  aprclJacobiDatumWeightedArray n hp (data.map fun item => item.datum) weight

/-- Decode the validated weighted array to the corresponding product of actual Jacobi sums. -/
theorem aprclValidatedJacobiDatumWeightedArray_class {p k a b n : ℕ} (hp : Nat.Prime p)
    (data : List (APRCLJacobiDatumWithParameters p k a b)) (weight : APRCLJacobiDatum p k → ℕ) :
    cyclotomicFixedArrayClass n p k (aprclValidatedJacobiDatumWeightedArray hp data weight) =
      ((data.map fun item => item.datum).map fun datum =>
          datum.jacobiSumValue n hp ^ weight datum).prod := by
  change
    cyclotomicFixedArrayClass n p k
        (aprclJacobiDatumWeightedArray n hp (data.map fun item => item.datum) weight) =
      ((data.map fun item => item.datum).map fun datum =>
          datum.jacobiSumValue n hp ^ weight datum).prod
  exact aprclJacobiDatumWeightedArray_class hp (data.map fun item => item.datum) weight

/-- The executable outer product of APR-CL Jacobi data obeys the `A^u B` update, even when its
factors come from different auxiliary primes. Duplicate data items are allowed and retain their
multiplicity in the ordered product. -/
theorem aprclJacobiDatumWeightedArray_eq_power_mul_mod {n p k : ℕ} (hp : Nat.Prime p)
    (data : List (APRCLJacobiDatum p k)) (input : ℕ) (hP : 0 < primePowerIndex p k) :
    cyclotomicFixedArrayClass n p k
        (aprclJacobiDatumWeightedArray n hp data
          (fun datum => input * datum.index / primePowerIndex p k)) =
      (data.map (fun datum => datum.jacobiSumValue n hp ^ datum.index)).prod ^
          (input / primePowerIndex p k) *
        (data.map
            (fun datum =>
              datum.jacobiSumValue n hp ^
                (input % primePowerIndex p k * datum.index / primePowerIndex p k))).prod := by
  calc
    _ =
        (data.map
            (fun datum =>
              datum.jacobiSumValue n hp ^ (input * datum.index / primePowerIndex p k))).prod :=
      aprclJacobiDatumWeightedArray_class hp data
        (fun datum => input * datum.index / primePowerIndex p k)
    _ = _ :=
      aprclListIndexedWeightedProduct_eq_power_mul_mod data (fun datum => datum.jacobiSumValue n hp)
        (fun datum => datum.index) input (primePowerIndex p k) hP

/-- One Jacobi factor together with its exponent in an APR-CL product. Keeping the product index
separate from the Jacobi datum allows the same computed Jacobi sum to occur at several positions
of a branch's finite exponent family. -/
structure APRCLIndexedJacobiDatum (p k : ℕ) where
  /-- Finite-field Jacobi sum and its character data. -/
  jacobi : APRCLJacobiDatum p k
  /-- Exponent index attached to this occurrence in the outer product. -/
  productIndex : ℕ

/-- A repeated APR-CL Jacobi factor with its branch-exponent and exact-valuation evidence intact.

Each list entry keeps its own `productIndex`, so repeated factors remain distinct occurrences in
the weighted outer product. -/
structure APRCLIndexedJacobiDatumWithParameters (p k a b : ℕ) where
  /-- Validated Jacobi datum for the selected branch exponents. -/
  jacobi : APRCLJacobiDatumWithParameters p k a b
  /-- Exponent index attached to this outer-product occurrence. -/
  productIndex : ℕ

/-- Forget the branch-validity evidence only when passing one occurrence to the coefficient-array
backend. -/
def APRCLIndexedJacobiDatumWithParameters.toIndexed {p k a b : ℕ}
    (entry : APRCLIndexedJacobiDatumWithParameters p k a b) : APRCLIndexedJacobiDatum p k :=
  ⟨entry.jacobi.datum, entry.productIndex⟩

/-- Repeat validated Jacobi data over an explicit ordered index list. -/
def aprclValidatedIndexedJacobiFamily {p k a b : ℕ} (datum : APRCLJacobiDatumWithParameters p k a b)
    (indices : List ℕ) : List (APRCLIndexedJacobiDatumWithParameters p k a b) :=
  indices.map fun i => ⟨datum, i⟩

/-- Repeat a Jacobi datum over an explicit ordered exponent list. Repetitions in `indices` remain
repetitions in the resulting list, matching the APR-CL outer product multiplicity. -/
def aprclIndexedJacobiFamily {p k : ℕ} (datum : APRCLJacobiDatum p k) (indices : List ℕ) :
    List (APRCLIndexedJacobiDatum p k) :=
  indices.map (fun i => ⟨datum, i⟩)

/-- Replace both character exponents by their product with the inverse of `i` modulo the
root period. On unit indices this gives the character parameters for the inverse Galois action;
the auxiliary field and its chosen generator are preserved. -/
def APRCLJacobiDatum.inverseConjugate {p k : ℕ} (datum : APRCLJacobiDatum p k) (i : ℕ) :
    APRCLJacobiDatum p k :=
  { datum with
    exponent₁ := datum.exponent₁ * ((i : ZMod (primePowerIndex p k))⁻¹).val
    exponent₂ := datum.exponent₂ * ((i : ZMod (primePowerIndex p k))⁻¹).val }

/-- For a unit index, multiplying either transformed character exponent by that index
recovers the original exponent modulo the prime-power cyclotomic period. -/
theorem APRCLJacobiDatum.inverseConjugate_spec {p k : ℕ} (hp : Nat.Prime p)
    (datum : APRCLJacobiDatum p k) (i : ℕ) (hi : Nat.Coprime i (primePowerIndex p k)) :
    (i : ZMod (primePowerIndex p k)) *
          ((datum.inverseConjugate i).exponent₁ : ZMod (primePowerIndex p k)) =
        datum.exponent₁ ∧
      (i : ZMod (primePowerIndex p k)) *
          ((datum.inverseConjugate i).exponent₂ : ZMod (primePowerIndex p k)) =
        datum.exponent₂ := by
  have hP : primePowerIndex p k ≠ 0 := by
    unfold primePowerIndex
    exact pow_ne_zero _ hp.ne_zero
  have : NeZero (primePowerIndex p k) := ⟨hP⟩
  constructor
  · simp only [APRCLJacobiDatum.inverseConjugate, Nat.cast_mul, ZMod.natCast_zmod_val]
    calc
      _ =
          ((i : ZMod (primePowerIndex p k)) * (i : ZMod (primePowerIndex p k))⁻¹) *
            (datum.exponent₁ : ZMod (primePowerIndex p k)) :=
        by ring
      _ = datum.exponent₁ := by rw [ZMod.coe_mul_inv_eq_one i hi, one_mul]
  · simp only [APRCLJacobiDatum.inverseConjugate, Nat.cast_mul, ZMod.natCast_zmod_val]
    calc
      _ =
          ((i : ZMod (primePowerIndex p k)) * (i : ZMod (primePowerIndex p k))⁻¹) *
            (datum.exponent₂ : ZMod (primePowerIndex p k)) :=
        by ring
      _ = datum.exponent₂ := by rw [ZMod.coe_mul_inv_eq_one i hi, one_mul]

/-- Applying the index power substitution to an inverse-index Jacobi datum recovers the
original Jacobi-sum value. Both character exponents are compared modulo the root period. -/
theorem APRCLJacobiDatum.rootPowerSubstitution_inverseConjugate {n p k i : ℕ} (hp : Nat.Prime p)
    (hpn : Nat.Coprime p n) (hi : Nat.Coprime i (primePowerIndex p k))
    (datum : APRCLJacobiDatum p k) :
    cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hi
        ((datum.inverseConjugate i).jacobiSumValue n hp) =
      datum.jacobiSumValue n hp := by
  have hspec := datum.inverseConjugate_spec hp i hi
  rw [APRCLJacobiDatum.rootPowerSubstitution_jacobiSumValue]
  have hchar₁ :=
    jacobiPowerCharacter_pow_eq_of_zmod (a := i * (datum.inverseConjugate i).exponent₁) (b :=
      datum.exponent₁) datum.qPrime datum.generator datum.generatorPrimitive
      (cyclotomicRootUnit n hp) (cyclotomicRoot_pow_index_eq_one n hp) datum.periodDivides
      (by simpa only [Nat.cast_mul] using hspec.1)
  have hchar₂ :=
    jacobiPowerCharacter_pow_eq_of_zmod (a := i * (datum.inverseConjugate i).exponent₂) (b :=
      datum.exponent₂) datum.qPrime datum.generator datum.generatorPrimitive
      (cyclotomicRootUnit n hp) (cyclotomicRoot_pow_index_eq_one n hp) datum.periodDivides
      (by simpa only [Nat.cast_mul] using hspec.2)
  let χ : MulChar (ZMod datum.q) (cyclotomicQuotient n p k) :=
    jacobiPowerCharacter datum.qPrime datum.generator datum.generatorPrimitive
      (cyclotomicRootUnit n hp) (cyclotomicRoot_pow_index_eq_one n hp) datum.periodDivides
  change
    @jacobiSum (ZMod datum.q) (cyclotomicQuotient n p k) _ datum.fieldFinite _
        (χ ^ (i * (datum.inverseConjugate i).exponent₁))
        (χ ^ (i * (datum.inverseConjugate i).exponent₂)) =
      @jacobiSum (ZMod datum.q) (cyclotomicQuotient n p k) _ datum.fieldFinite _
        (χ ^ datum.exponent₁) (χ ^ datum.exponent₂)
  rw [hchar₁, hchar₂]

/-- The odd-prime APR-CL exponent family `1 ≤ i < P` with `p ∤ i`, in ascending order. -/
def aprclOddPrimeJacobiIndexFamily (p k : ℕ) (_hpOdd : 2 < p) (datum : APRCLJacobiDatum p k) :
    List (APRCLIndexedJacobiDatum p k) :=
  ((List.range (primePowerIndex p k)).filter (fun i => decide (0 < i ∧ ¬p ∣ i))).map
    (fun i => ⟨datum.inverseConjugate i, i⟩)

/-- The high two-adic APR-CL exponent family `1 ≤ i < P` with residue `1` or `3` modulo `8`,
in ascending order. -/
def aprclTwoAdicHighJacobiIndexFamily (k : ℕ) (_hk : 2 ≤ k)
    (datum₁₁ datum₂₁ : APRCLJacobiDatum 2 k) : List (APRCLIndexedJacobiDatum 2 k) :=
  ((List.range (primePowerIndex 2 k)).filter
        (fun i => decide (0 < i ∧ (i % 8 = 1 ∨ i % 8 = 3)))).flatMap
    (fun i => [⟨datum₁₁.inverseConjugate i, i⟩, ⟨datum₂₁.inverseConjugate i, i⟩])

/-- Every odd-prime branch entry has a unit index and two character exponents
that recover the base datum's exponents after multiplication by that index. -/
theorem aprclOddPrimeJacobiIndexFamily_character_spec {p k : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p)
    (datum : APRCLJacobiDatum p k) (entry : APRCLIndexedJacobiDatum p k)
    (hentry : entry ∈ aprclOddPrimeJacobiIndexFamily p k hpOdd datum) :
    entry.productIndex < primePowerIndex p k ∧
      0 < entry.productIndex ∧
      ¬p ∣ entry.productIndex ∧
      (entry.productIndex : ZMod (primePowerIndex p k)) *
          (entry.jacobi.exponent₁ : ZMod (primePowerIndex p k)) =
        datum.exponent₁ ∧
      (entry.productIndex : ZMod (primePowerIndex p k)) *
          (entry.jacobi.exponent₂ : ZMod (primePowerIndex p k)) =
        datum.exponent₂ := by
  obtain ⟨i, hi, heq⟩ := List.mem_map.mp hentry
  obtain ⟨hrange, hfilter⟩ := List.mem_filter.mp hi
  have hbound : i < primePowerIndex p k := List.mem_range.mp hrange
  have hguard : 0 < i ∧ ¬p ∣ i := by simpa only [decide_eq_true_eq] using hfilter
  cases heq
  have hcop : Nat.Coprime i (primePowerIndex p k) := by
    unfold primePowerIndex
    exact hp.coprime_pow_of_not_dvd hguard.2
  have hspec := datum.inverseConjugate_spec hp i hcop
  exact ⟨hbound, hguard.1, hguard.2, hspec.1, hspec.2⟩

/- The residue classes selected for the high two-adic product have odd indices. -/
private theorem mod_two_eq_one_of_mod_eight {i : ℕ} (h : i % 8 = 1 ∨ i % 8 = 3) : i % 2 = 1 := by
  calc
    i % 2 = (i % 8) % 2 := (Nat.mod_mod_of_dvd i (by decide : 2 ∣ 8)).symm
    _ = 1 := by
      rcases h with h1 | h3
      · rw [h1]
      · rw [h3]

/- Every such index is a unit modulo the high two-adic root period. -/
private theorem coprime_two_power_of_mod_eight {k i : ℕ} (h : i % 8 = 1 ∨ i % 8 = 3) :
    Nat.Coprime i (primePowerIndex 2 k) := by
  have hnot : ¬2 ∣ i := by
    intro hdiv
    have hz : i % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    rw [mod_two_eq_one_of_mod_eight h] at hz
    exact Nat.zero_ne_one hz.symm
  unfold primePowerIndex
  exact (by decide : Nat.Prime 2).coprime_pow_of_not_dvd hnot

/-- Every high two-adic entry has residue one or three modulo eight and retains the
corresponding base datum's character after its inverse-index transform. -/
theorem aprclTwoAdicHighJacobiIndexFamily_character_spec {k : ℕ} (hk : 2 ≤ k)
    (datum₁₁ datum₂₁ : APRCLJacobiDatum 2 k) (entry : APRCLIndexedJacobiDatum 2 k)
    (hentry : entry ∈ aprclTwoAdicHighJacobiIndexFamily k hk datum₁₁ datum₂₁) :
    entry.productIndex < primePowerIndex 2 k ∧
      (entry.productIndex % 8 = 1 ∨ entry.productIndex % 8 = 3) ∧
      ((entry.productIndex : ZMod (primePowerIndex 2 k)) *
              (entry.jacobi.exponent₁ : ZMod (primePowerIndex 2 k)) =
            datum₁₁.exponent₁ ∧
          (entry.productIndex : ZMod (primePowerIndex 2 k)) *
              (entry.jacobi.exponent₂ : ZMod (primePowerIndex 2 k)) =
            datum₁₁.exponent₂ ∨
        (entry.productIndex : ZMod (primePowerIndex 2 k)) *
              (entry.jacobi.exponent₁ : ZMod (primePowerIndex 2 k)) =
            datum₂₁.exponent₁ ∧
          (entry.productIndex : ZMod (primePowerIndex 2 k)) *
              (entry.jacobi.exponent₂ : ZMod (primePowerIndex 2 k)) =
            datum₂₁.exponent₂) := by
  obtain ⟨i, hi, hpair⟩ := List.mem_flatMap.mp hentry
  obtain ⟨hrange, hfilter⟩ := List.mem_filter.mp hi
  have hbound : i < primePowerIndex 2 k := List.mem_range.mp hrange
  have hguard : 0 < i ∧ (i % 8 = 1 ∨ i % 8 = 3) := by simpa only [decide_eq_true_eq] using hfilter
  have hcop : Nat.Coprime i (primePowerIndex 2 k) := coprime_two_power_of_mod_eight hguard.2
  simp only [List.mem_cons] at hpair
  rcases hpair with hfirst | hsecond
  · cases hfirst
    have hspec := datum₁₁.inverseConjugate_spec (by decide : Nat.Prime 2) i hcop
    exact ⟨hbound, hguard.2, Or.inl hspec⟩
  · rcases hsecond with hsecond | hnil
    · cases hsecond
      have hspec := datum₂₁.inverseConjugate_spec (by decide : Nat.Prime 2) i hcop
      exact ⟨hbound, hguard.2, Or.inr hspec⟩
    · exact False.elim (List.not_mem_nil hnil)

/-- Each odd-prime family entry is an inverse-index Jacobi value: its index automorphism
recovers the selected base Jacobi sum. -/
theorem aprclOddPrimeJacobiIndexFamily_value_spec {n p k : ℕ} (hp : Nat.Prime p)
    (hpn : Nat.Coprime p n) (hpOdd : 2 < p) (datum : APRCLJacobiDatum p k)
    (entry : APRCLIndexedJacobiDatum p k)
    (hentry : entry ∈ aprclOddPrimeJacobiIndexFamily p k hpOdd datum) :
    ∃ hcop : Nat.Coprime entry.productIndex (primePowerIndex p k),
      cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop
          (entry.jacobi.jacobiSumValue n hp) =
        datum.jacobiSumValue n hp := by
  obtain ⟨i, hi, heq⟩ := List.mem_map.mp hentry
  obtain ⟨_, hfilter⟩ := List.mem_filter.mp hi
  have hguard : 0 < i ∧ ¬p ∣ i := by simpa only [decide_eq_true_eq] using hfilter
  cases heq
  have hcop : Nat.Coprime i (primePowerIndex p k) := by
    unfold primePowerIndex
    exact hp.coprime_pow_of_not_dvd hguard.2
  exact ⟨hcop, datum.rootPowerSubstitution_inverseConjugate hp hpn hcop⟩

/-- Each high two-adic family entry is an inverse-index Jacobi value for one of its two
base data, and its residue condition supplies the required unit index. -/
theorem aprclTwoAdicHighJacobiIndexFamily_value_spec {n k : ℕ} (hpn : Nat.Coprime 2 n) (hk : 2 ≤ k)
    (datum₁₁ datum₂₁ : APRCLJacobiDatum 2 k) (entry : APRCLIndexedJacobiDatum 2 k)
    (hentry : entry ∈ aprclTwoAdicHighJacobiIndexFamily k hk datum₁₁ datum₂₁) :
    ∃ hcop : Nat.Coprime entry.productIndex (primePowerIndex 2 k),
      (cyclotomicRootPowerSubstitutionEquiv_of_coprime n (by decide : Nat.Prime 2) hpn hcop
            (entry.jacobi.jacobiSumValue n (by decide : Nat.Prime 2)) =
          datum₁₁.jacobiSumValue n (by decide : Nat.Prime 2) ∨
        cyclotomicRootPowerSubstitutionEquiv_of_coprime n (by decide : Nat.Prime 2) hpn hcop
            (entry.jacobi.jacobiSumValue n (by decide : Nat.Prime 2)) =
          datum₂₁.jacobiSumValue n (by decide : Nat.Prime 2)) := by
  obtain ⟨i, hi, hpair⟩ := List.mem_flatMap.mp hentry
  obtain ⟨_, hfilter⟩ := List.mem_filter.mp hi
  have hguard : 0 < i ∧ (i % 8 = 1 ∨ i % 8 = 3) := by simpa only [decide_eq_true_eq] using hfilter
  have hcop : Nat.Coprime i (primePowerIndex 2 k) := coprime_two_power_of_mod_eight hguard.2
  simp only [List.mem_cons] at hpair
  rcases hpair with hfirst | hsecond
  · cases hfirst
    exact
      ⟨hcop,
        Or.inl (datum₁₁.rootPowerSubstitution_inverseConjugate (by decide : Nat.Prime 2) hpn hcop)⟩
  · rcases hsecond with hsecond | hnil
    · cases hsecond
      exact
        ⟨hcop,
          Or.inr
            (datum₂₁.rootPowerSubstitution_inverseConjugate (by decide : Nat.Prime 2) hpn hcop)⟩
    · exact False.elim (List.not_mem_nil hnil)

/-- Rewrite an odd-prime family factor as the inverse root-substitution image of its
base Jacobi value. This is the form used by the weighted product. -/
theorem aprclOddPrimeJacobiIndexFamily_inverse_value {n p k : ℕ} (hp : Nat.Prime p)
    (hpn : Nat.Coprime p n) (hpOdd : 2 < p) (datum : APRCLJacobiDatum p k)
    (entry : APRCLIndexedJacobiDatum p k)
    (hentry : entry ∈ aprclOddPrimeJacobiIndexFamily p k hpOdd datum) :
    ∃ hcop : Nat.Coprime entry.productIndex (primePowerIndex p k),
      entry.jacobi.jacobiSumValue n hp =
        (cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop).symm
          (datum.jacobiSumValue n hp) := by
  obtain ⟨hcop, hvalue⟩ := aprclOddPrimeJacobiIndexFamily_value_spec hp hpn hpOdd datum entry hentry
  refine ⟨hcop, ?_⟩
  exact
    ((RingEquiv.symm_apply_eq (cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop)).mpr
        hvalue.symm).symm

/-- Rewrite each high two-adic family factor as an inverse root-substitution image
of one of the two base Jacobi values. -/
theorem aprclTwoAdicHighJacobiIndexFamily_inverse_value {n k : ℕ} (hpn : Nat.Coprime 2 n)
    (hk : 2 ≤ k) (datum₁₁ datum₂₁ : APRCLJacobiDatum 2 k) (entry : APRCLIndexedJacobiDatum 2 k)
    (hentry : entry ∈ aprclTwoAdicHighJacobiIndexFamily k hk datum₁₁ datum₂₁) :
    ∃ hcop : Nat.Coprime entry.productIndex (primePowerIndex 2 k),
      (entry.jacobi.jacobiSumValue n (by decide : Nat.Prime 2) =
          (cyclotomicRootPowerSubstitutionEquiv_of_coprime n (by decide : Nat.Prime 2) hpn
                hcop).symm
            (datum₁₁.jacobiSumValue n (by decide : Nat.Prime 2)) ∨
        entry.jacobi.jacobiSumValue n (by decide : Nat.Prime 2) =
          (cyclotomicRootPowerSubstitutionEquiv_of_coprime n (by decide : Nat.Prime 2) hpn
                hcop).symm
            (datum₂₁.jacobiSumValue n (by decide : Nat.Prime 2))) := by
  obtain ⟨hcop, hvalue⟩ :=
    aprclTwoAdicHighJacobiIndexFamily_value_spec hpn hk datum₁₁ datum₂₁ entry hentry
  refine ⟨hcop, ?_⟩
  rcases hvalue with hfirst | hsecond
  · left
    exact
      ((RingEquiv.symm_apply_eq
              (cyclotomicRootPowerSubstitutionEquiv_of_coprime n (by decide : Nat.Prime 2) hpn
                hcop)).mpr
          hfirst.symm).symm
  · right
    exact
      ((RingEquiv.symm_apply_eq
              (cyclotomicRootPowerSubstitutionEquiv_of_coprime n (by decide : Nat.Prime 2) hpn
                hcop)).mpr
          hsecond.symm).symm

/-- Evaluate an indexed list of APR-CL Jacobi factors in the fixed coefficient array. The weight
is the floor exponent `input * productIndex / P` from the APR-CL weighted product. -/
def aprclIndexedJacobiWeightedArray {n p k : ℕ} (hp : Nat.Prime p)
    (data : List (APRCLIndexedJacobiDatum p k)) (input P : ℕ) : cyclotomicFixedArray n p k :=
  cyclotomicFixedArrayWeightedProductList n hp
    (data.map (fun entry => { entry.jacobi with index := entry.productIndex }))
    (fun datum => datum.coefficientArray n hp) (fun datum => input * datum.index / P)

/-- The indexed coefficient product decodes to the corresponding actual Jacobi sums with their
APR-CL floor exponents. -/
theorem aprclIndexedJacobiWeightedArray_class {n p k : ℕ} (hp : Nat.Prime p)
    (data : List (APRCLIndexedJacobiDatum p k)) (input P : ℕ) :
    cyclotomicFixedArrayClass n p k (aprclIndexedJacobiWeightedArray hp data input P) =
      (data.map
          (fun entry =>
            entry.jacobi.jacobiSumValue n hp ^ (input * entry.productIndex / P))).prod := by
  unfold aprclIndexedJacobiWeightedArray
  rw [cyclotomicFixedArrayWeightedProductList_class]
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro entry _
  exact
    congrArg (fun z : cyclotomicQuotient n p k => z ^ (input * entry.productIndex / P))
      (entry.jacobi.jacobiSumValue_eq_coefficientArray n hp).symm

/-- Evaluate a weighted outer product whose entries retain APR-CL exponent and exact-valuation
evidence. The branch evidence is preserved until each entry is converted to the existing array
evaluator. -/
def aprclValidatedIndexedJacobiWeightedArray {n p k a b : ℕ} (hp : Nat.Prime p)
    (data : List (APRCLIndexedJacobiDatumWithParameters p k a b)) (input P : ℕ) :
    cyclotomicFixedArray n p k :=
  aprclIndexedJacobiWeightedArray hp (data.map APRCLIndexedJacobiDatumWithParameters.toIndexed)
    input P

/-- Decode the validated indexed array to its Jacobi-sum outer product. -/
theorem aprclValidatedIndexedJacobiWeightedArray_class {n p k a b : ℕ} (hp : Nat.Prime p)
    (data : List (APRCLIndexedJacobiDatumWithParameters p k a b)) (input P : ℕ) :
    cyclotomicFixedArrayClass n p k (aprclValidatedIndexedJacobiWeightedArray hp data input P) =
      ((data.map APRCLIndexedJacobiDatumWithParameters.toIndexed).map fun entry =>
          entry.jacobi.jacobiSumValue n hp ^ (input * entry.productIndex / P)).prod := by
  change
    cyclotomicFixedArrayClass n p k
        (aprclIndexedJacobiWeightedArray hp
          (data.map APRCLIndexedJacobiDatumWithParameters.toIndexed) input P) =
      ((data.map APRCLIndexedJacobiDatumWithParameters.toIndexed).map fun entry =>
          entry.jacobi.jacobiSumValue n hp ^ (input * entry.productIndex / P)).prod
  exact
    aprclIndexedJacobiWeightedArray_class hp
      (data.map APRCLIndexedJacobiDatumWithParameters.toIndexed) input P

/-- The indexed APR-CL factor list satisfies the common-period quotient/remainder update. This is
the representation theorem used to instantiate the odd-prime and two-adic branch exponent lists. -/
theorem aprclIndexedJacobiWeightedArray_eq_power_mul_mod {n p k : ℕ} (hp : Nat.Prime p)
    (data : List (APRCLIndexedJacobiDatum p k)) (input P : ℕ) (hP : 0 < P) :
    cyclotomicFixedArrayClass n p k (aprclIndexedJacobiWeightedArray hp data input P) =
      (data.map (fun entry => entry.jacobi.jacobiSumValue n hp ^ entry.productIndex)).prod ^
          (input / P) *
        (data.map
            (fun entry =>
              entry.jacobi.jacobiSumValue n hp ^ (input % P * entry.productIndex / P))).prod := by
  calc
    _ =
        (data.map
            (fun entry =>
              entry.jacobi.jacobiSumValue n hp ^ (input * entry.productIndex / P))).prod :=
      aprclIndexedJacobiWeightedArray_class hp data input P
    _ = _ :=
      aprclListIndexedWeightedProduct_eq_power_mul_mod data
        (fun entry => entry.jacobi.jacobiSumValue n hp) (fun entry => entry.productIndex) input P hP

/-- Fixed-array implementation of the odd-prime weighted product `W` for one auxiliary prime.
The filtered index list is exactly the branch's condition `1 ≤ i < p^(k+1)` and `p ∤ i`. -/
def aprclOddPrimeJacobiWeightedArray {n p k : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p)
    (datum : APRCLJacobiDatum p k) : cyclotomicFixedArray n p k :=
  aprclIndexedJacobiWeightedArray hp (aprclOddPrimeJacobiIndexFamily p k hpOdd datum) n
    (primePowerIndex p k)

/-- Decode the odd-prime branch's executable weighted product to actual Jacobi sums. -/
theorem aprclOddPrimeJacobiWeightedArray_class {n p k : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p)
    (datum : APRCLJacobiDatum p k) :
    cyclotomicFixedArrayClass n p k (aprclOddPrimeJacobiWeightedArray hp hpOdd datum) =
      ((aprclOddPrimeJacobiIndexFamily p k hpOdd datum).map
          (fun entry =>
            entry.jacobi.jacobiSumValue n hp ^
              (n * entry.productIndex / primePowerIndex p k))).prod := by
  exact
    aprclIndexedJacobiWeightedArray_class hp (aprclOddPrimeJacobiIndexFamily p k hpOdd datum) n
      (primePowerIndex p k)

/-- Odd-prime branch evaluator whose input certifies the `(1,1)` character exponents and exact
auxiliary-prime valuation. -/
def aprclValidatedOddPrimeJacobiWeightedArray {n p k : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p)
    (_hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) :
    cyclotomicFixedArray n p k :=
  aprclOddPrimeJacobiWeightedArray hp hpOdd datum.datum

/-- The validated odd-prime evaluator decodes to the indexed Jacobi product. -/
theorem aprclValidatedOddPrimeJacobiWeightedArray_class {n p k : ℕ} (hp : Nat.Prime p)
    (hpOdd : 2 < p) (_hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) :
    cyclotomicFixedArrayClass n p k
        (aprclValidatedOddPrimeJacobiWeightedArray hp hpOdd _hB2 datum) =
      ((aprclOddPrimeJacobiIndexFamily p k hpOdd datum.datum).map
          (fun entry =>
            entry.jacobi.jacobiSumValue n hp ^
              (n * entry.productIndex / primePowerIndex p k))).prod := by
  exact aprclOddPrimeJacobiWeightedArray_class hp hpOdd datum.datum

/-- Search the complete cyclotomic root period for the validated odd-prime Jacobi product. -/
noncomputable def aprclValidatedOddPrimeCheck {n p k : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p)
    (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) : Option ℕ :=
  rootExponent n p k
    (cyclotomicFixedArrayClass n p k (aprclValidatedOddPrimeJacobiWeightedArray hp hpOdd hB2 datum))

/-- A successful odd-prime Jacobi check returns the least exponent in the full root period whose
cyclotomic root equals the validated weighted Jacobi product. -/
theorem aprclValidatedOddPrimeCheck_eq_some_iff {n p k h : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p)
    (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) :
    aprclValidatedOddPrimeCheck (n := n) hp hpOdd hB2 datum = some h ↔
      h < primePowerIndex p k ∧
        cyclotomicRoot n p k ^ h =
          cyclotomicFixedArrayClass n p k
            (aprclValidatedOddPrimeJacobiWeightedArray hp hpOdd hB2 datum) ∧
        ∀ j < h,
          cyclotomicRoot n p k ^ j ≠
            cyclotomicFixedArrayClass n p k
              (aprclValidatedOddPrimeJacobiWeightedArray hp hpOdd hB2 datum) := by
  exact
    rootExponent_eq_some_iff n p k
      (cyclotomicFixedArrayClass n p k
        (aprclValidatedOddPrimeJacobiWeightedArray hp hpOdd hB2 datum))
      h

/-- Filter the odd-prime root specification by the branch condition `p ∤ h`.
An exact-order conclusion additionally needs the standard root to have full period. -/
noncomputable def aprclValidatedOddPrimeBranchCheck {n p k : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p)
    (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) : Option ℕ :=
  Option.filter (fun h => decide (h % p ≠ 0))
    (aprclValidatedOddPrimeCheck (n := n) hp hpOdd hB2 datum)

/-- The odd-prime branch check succeeds exactly when the product matches a root and its exponent
is not divisible by `p`. -/
theorem aprclValidatedOddPrimeBranchCheck_eq_some_iff {n p k h : ℕ} (hp : Nat.Prime p)
    (hpOdd : 2 < p) (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) :
    aprclValidatedOddPrimeBranchCheck (n := n) hp hpOdd hB2 datum = some h ↔
      aprclValidatedOddPrimeCheck (n := n) hp hpOdd hB2 datum = some h ∧ h % p ≠ 0 := by
  rw [aprclValidatedOddPrimeBranchCheck, Option.filter_eq_some_iff]
  simp only [decide_eq_true_eq]

/-- Compute the odd-prime Jacobi root exponent by comparing reduced monomial arrays
over the complete prime-power period. The result is an optional least exponent. -/
def aprclValidatedOddPrimeArrayCheck {n p k : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p)
    (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) : Option ℕ :=
  cyclotomicFixedArrayRootExponent n hp
    (aprclValidatedOddPrimeJacobiWeightedArray hp hpOdd hB2 datum)

/-- For inputs above one, the executable odd-prime array search equals the
cyclotomic quotient specification. -/
theorem aprclValidatedOddPrimeArrayCheck_eq_check {n p k : ℕ} (hn : 1 < n) (hp : Nat.Prime p)
    (hpOdd : 2 < p) (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) :
    aprclValidatedOddPrimeArrayCheck (n := n) hp hpOdd hB2 datum =
      aprclValidatedOddPrimeCheck (n := n) hp hpOdd hB2 datum := by
  exact
    cyclotomicFixedArrayRootExponent_eq_rootExponent n hn hp
      (aprclValidatedOddPrimeJacobiWeightedArray hp hpOdd hB2 datum)

/-- Compute the odd-prime branch result from arrays, keeping only a root
exponent not divisible by `p`. -/
def aprclValidatedOddPrimeArrayBranchCheck {n p k : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p)
    (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) : Option ℕ :=
  Option.filter (fun h => decide (h % p ≠ 0))
    (aprclValidatedOddPrimeArrayCheck (n := n) hp hpOdd hB2 datum)

/-- The executable odd-prime branch and quotient specification return the same result. -/
theorem aprclValidatedOddPrimeArrayBranchCheck_eq_check {n p k : ℕ} (hn : 1 < n) (hp : Nat.Prime p)
    (hpOdd : 2 < p) (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) :
    aprclValidatedOddPrimeArrayBranchCheck (n := n) hp hpOdd hB2 datum =
      aprclValidatedOddPrimeBranchCheck (n := n) hp hpOdd hB2 datum := by
  unfold aprclValidatedOddPrimeArrayBranchCheck aprclValidatedOddPrimeBranchCheck
  rw [aprclValidatedOddPrimeArrayCheck_eq_check hn hp hpOdd hB2 datum]

/-- Decode a successful odd-prime branch result as an equality with the actual finite product of
Jacobi sums. This connects the noncomputable root specification and its `p ∤ h` guard to the
mathematical branch expression. -/
theorem aprclValidatedOddPrimeBranchCheck_success_product {n p k h : ℕ} (hp : Nat.Prime p)
    (hpOdd : 2 < p) (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1)
    (hcheck : aprclValidatedOddPrimeBranchCheck (n := n) hp hpOdd hB2 datum = some h) :
    h % p ≠ 0 ∧
      h < primePowerIndex p k ∧
      cyclotomicRoot n p k ^ h =
        ((aprclOddPrimeJacobiIndexFamily p k hpOdd datum.datum).map
            (fun entry =>
              entry.jacobi.jacobiSumValue n hp ^
                (n * entry.productIndex / primePowerIndex p k))).prod ∧
      ∀ j < h,
        cyclotomicRoot n p k ^ j ≠
          ((aprclOddPrimeJacobiIndexFamily p k hpOdd datum.datum).map
              (fun entry =>
                entry.jacobi.jacobiSumValue n hp ^
                  (n * entry.productIndex / primePowerIndex p k))).prod := by
  have hbranch := (aprclValidatedOddPrimeBranchCheck_eq_some_iff hp hpOdd hB2 datum).mp hcheck
  rcases hbranch with ⟨hroot, hnotdiv⟩
  have hrootSpec := (aprclValidatedOddPrimeCheck_eq_some_iff hp hpOdd hB2 datum).mp hroot
  rcases hrootSpec with ⟨hbound, hmatch, hminimal⟩
  rw [aprclValidatedOddPrimeJacobiWeightedArray_class] at hmatch
  rw [aprclValidatedOddPrimeJacobiWeightedArray_class] at hminimal
  exact ⟨hnotdiv, hbound, hmatch, hminimal⟩

/-- An executable odd-prime array branch result satisfies the mathematical
Jacobi-product equation, its guard, and least-root condition. -/
theorem aprclValidatedOddPrimeArrayBranchCheck_success_product {n p k h : ℕ} (hn : 1 < n)
    (hp : Nat.Prime p) (hpOdd : 2 < p) (hB2 : aprclB2Condition p)
    (datum : APRCLJacobiDatumWithParameters p k 1 1)
    (hcheck : aprclValidatedOddPrimeArrayBranchCheck (n := n) hp hpOdd hB2 datum = some h) :
    h % p ≠ 0 ∧
      h < primePowerIndex p k ∧
      cyclotomicRoot n p k ^ h =
        ((aprclOddPrimeJacobiIndexFamily p k hpOdd datum.datum).map
            (fun entry =>
              entry.jacobi.jacobiSumValue n hp ^
                (n * entry.productIndex / primePowerIndex p k))).prod ∧
      ∀ j < h,
        cyclotomicRoot n p k ^ j ≠
          ((aprclOddPrimeJacobiIndexFamily p k hpOdd datum.datum).map
              (fun entry =>
                entry.jacobi.jacobiSumValue n hp ^
                  (n * entry.productIndex / primePowerIndex p k))).prod := by
  rw [aprclValidatedOddPrimeArrayBranchCheck_eq_check hn hp hpOdd hB2 datum] at hcheck
  exact aprclValidatedOddPrimeBranchCheck_success_product hp hpOdd hB2 datum hcheck

/-- A successful odd-prime branch retains the `p ∤ h` guard and identifies each factor
in its checked product as the inverse-index conjugate of the base Jacobi value. -/
theorem aprclValidatedOddPrimeBranchCheck_success_factor {n p k h : ℕ} (hp : Nat.Prime p)
    (hpn : Nat.Coprime p n) (hpOdd : 2 < p) (hB2 : aprclB2Condition p)
    (datum : APRCLJacobiDatumWithParameters p k 1 1)
    (hcheck : aprclValidatedOddPrimeBranchCheck (n := n) hp hpOdd hB2 datum = some h)
    (entry : APRCLIndexedJacobiDatum p k)
    (hentry : entry ∈ aprclOddPrimeJacobiIndexFamily p k hpOdd datum.datum) :
    h % p ≠ 0 ∧
      ∃ hcop : Nat.Coprime entry.productIndex (primePowerIndex p k),
        cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop
            (entry.jacobi.jacobiSumValue n hp) =
          datum.datum.jacobiSumValue n hp := by
  have hbranch := aprclValidatedOddPrimeBranchCheck_success_product hp hpOdd hB2 datum hcheck
  exact ⟨hbranch.1, aprclOddPrimeJacobiIndexFamily_value_spec hp hpn hpOdd datum.datum entry hentry⟩

/-- On a successful odd-prime branch, each checked Jacobi factor is the inverse
root-substitution image of the selected base value. -/
theorem aprclValidatedOddPrimeBranchCheck_success_factor_inverse {n p k h : ℕ} (hp : Nat.Prime p)
    (hpn : Nat.Coprime p n) (hpOdd : 2 < p) (hB2 : aprclB2Condition p)
    (datum : APRCLJacobiDatumWithParameters p k 1 1)
    (hcheck : aprclValidatedOddPrimeBranchCheck (n := n) hp hpOdd hB2 datum = some h)
    (entry : APRCLIndexedJacobiDatum p k)
    (hentry : entry ∈ aprclOddPrimeJacobiIndexFamily p k hpOdd datum.datum) :
    h % p ≠ 0 ∧
      ∃ hcop : Nat.Coprime entry.productIndex (primePowerIndex p k),
        entry.jacobi.jacobiSumValue n hp =
          (cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop).symm
            (datum.datum.jacobiSumValue n hp) := by
  have hguard := (aprclValidatedOddPrimeBranchCheck_success_product hp hpOdd hB2 datum hcheck).1
  exact ⟨hguard, aprclOddPrimeJacobiIndexFamily_inverse_value hp hpn hpOdd datum.datum entry hentry⟩

/-- A successful executable odd-prime branch yields the inverse root-substitution
value of each Jacobi factor together with the exponent guard. -/
theorem aprclValidatedOddPrimeArrayBranchCheck_success_factor_inverse {n p k h : ℕ} (hn : 1 < n)
    (hp : Nat.Prime p) (hpn : Nat.Coprime p n) (hpOdd : 2 < p) (hB2 : aprclB2Condition p)
    (datum : APRCLJacobiDatumWithParameters p k 1 1)
    (hcheck : aprclValidatedOddPrimeArrayBranchCheck (n := n) hp hpOdd hB2 datum = some h)
    (entry : APRCLIndexedJacobiDatum p k)
    (hentry : entry ∈ aprclOddPrimeJacobiIndexFamily p k hpOdd datum.datum) :
    h % p ≠ 0 ∧
      ∃ hcop : Nat.Coprime entry.productIndex (primePowerIndex p k),
        entry.jacobi.jacobiSumValue n hp =
          (cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop).symm
            (datum.datum.jacobiSumValue n hp) := by
  rw [aprclValidatedOddPrimeArrayBranchCheck_eq_check hn hp hpOdd hB2 datum] at hcheck
  exact
    aprclValidatedOddPrimeBranchCheck_success_factor_inverse hp hpn hpOdd hB2 datum hcheck entry
      hentry

/-- Fixed-array implementation of the weighted `J₃` product for the high two-adic branch.
The separate `J₂` correction factor from (C-2k) is represented by its own factor family. -/
def aprclTwoAdicHighJacobiWeightedArray {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (datum₁₁ datum₂₁ : APRCLJacobiDatum 2 k) : cyclotomicFixedArray n 2 k :=
  aprclIndexedJacobiWeightedArray hp (aprclTwoAdicHighJacobiIndexFamily k hk datum₁₁ datum₂₁) n
    (primePowerIndex 2 k)

/-- Decode the high two-adic branch's `J₃` weighted product to actual Jacobi sums. -/
theorem aprclTwoAdicHighJacobiWeightedArray_class {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (datum₁₁ datum₂₁ : APRCLJacobiDatum 2 k) :
    cyclotomicFixedArrayClass n 2 k (aprclTwoAdicHighJacobiWeightedArray hp hk datum₁₁ datum₂₁) =
      ((aprclTwoAdicHighJacobiIndexFamily k hk datum₁₁ datum₂₁).map
          (fun entry =>
            entry.jacobi.jacobiSumValue n hp ^
              (n * entry.productIndex / primePowerIndex 2 k))).prod := by
  exact
    aprclIndexedJacobiWeightedArray_class hp
      (aprclTwoAdicHighJacobiIndexFamily k hk datum₁₁ datum₂₁) n (primePowerIndex 2 k)

/-- Fixed-array representation of the high two-adic branch's separate squared `J₂` correction.
The Boolean indicates whether the input residue class requires this correction. -/
def aprclTwoAdicHighJ2CorrectionArray {n k : ℕ} (hp : Nat.Prime 2) (datum₂ : APRCLJacobiDatum 2 k)
    (includeCorrection : Bool) : cyclotomicFixedArray n 2 k :=
  aprclJacobiDatumWeightedArray n hp [datum₂] (fun _ => if includeCorrection then 2 else 0)

/-- Decode the optional squared `J₂` correction to its actual Jacobi-sum power. -/
theorem aprclTwoAdicHighJ2CorrectionArray_class {n k : ℕ} (hp : Nat.Prime 2)
    (datum₂ : APRCLJacobiDatum 2 k) (includeCorrection : Bool) :
    cyclotomicFixedArrayClass n 2 k
        (aprclTwoAdicHighJ2CorrectionArray hp datum₂ includeCorrection) =
      datum₂.jacobiSumValue n hp ^ (if includeCorrection then 2 else 0) := by
  rw [aprclTwoAdicHighJ2CorrectionArray, aprclJacobiDatumWeightedArray_class]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-- Multiply the `J₃` weighted product by the optional squared `J₂` correction in the fixed
cyclotomic coefficient-array representation. -/
def aprclTwoAdicHighCombinedArray {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (datum₁₁ datum₂₁ datum₂ : APRCLJacobiDatum 2 k) (includeCorrection : Bool) :
    cyclotomicFixedArray n 2 k :=
  cyclotomicFixedArrayMulByExpansion n hp
    (aprclTwoAdicHighJacobiWeightedArray hp hk datum₁₁ datum₂₁)
    (aprclTwoAdicHighJ2CorrectionArray hp datum₂ includeCorrection)

/-- The high two-adic branch's combined coefficient array decodes to the prescribed `J₃` product
times its `J₂²` correction. The caller supplies the residue-class Boolean and character data. -/
theorem aprclTwoAdicHighCombinedArray_class {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (datum₁₁ datum₂₁ datum₂ : APRCLJacobiDatum 2 k) (includeCorrection : Bool) :
    cyclotomicFixedArrayClass n 2 k
        (aprclTwoAdicHighCombinedArray hp hk datum₁₁ datum₂₁ datum₂ includeCorrection) =
      ((aprclTwoAdicHighJacobiIndexFamily k hk datum₁₁ datum₂₁).map
            (fun entry =>
              entry.jacobi.jacobiSumValue n hp ^
                (n * entry.productIndex / primePowerIndex 2 k))).prod *
        datum₂.jacobiSumValue n hp ^ (if includeCorrection then 2 else 0) := by
  calc
    _ =
        cyclotomicFixedArrayClass n 2 k
            (aprclTwoAdicHighJacobiWeightedArray hp hk datum₁₁ datum₂₁) *
          cyclotomicFixedArrayClass n 2 k
            (aprclTwoAdicHighJ2CorrectionArray hp datum₂ includeCorrection) :=
      cyclotomicFixedArrayMulByExpansion_class_eq_mul n hp _ _
    _ = _ := by
      rw [aprclTwoAdicHighJacobiWeightedArray_class, aprclTwoAdicHighJ2CorrectionArray_class]

/-- Select the high two-adic `J₂²` correction exactly in residue classes `5` and `7` modulo 8. -/
def aprclTwoAdicHighCorrectionFlag (n : ℕ) : Bool :=
  decide (n % 8 = 5 ∨ n % 8 = 7)

/-- The executable high two-adic correction flag is true exactly in the two corrected residue
classes from the APR-CL formula. -/
theorem aprclTwoAdicHighCorrectionFlag_eq_true_iff (n : ℕ) :
    aprclTwoAdicHighCorrectionFlag n = true ↔ n % 8 = 5 ∨ n % 8 = 7 := by
  unfold aprclTwoAdicHighCorrectionFlag
  exact decide_eq_true_iff

/-- For odd inputs, the false correction flag is exactly the two uncorrected residue classes. -/
theorem aprclTwoAdicHighCorrectionFlag_eq_false_iff {n : ℕ} (hn : Odd n) :
    aprclTwoAdicHighCorrectionFlag n = false ↔ n % 8 = 1 ∨ n % 8 = 3 := by
  constructor
  · intro hflag
    unfold aprclTwoAdicHighCorrectionFlag at hflag
    have hnot := (decide_eq_false_iff_not).mp hflag
    rcases hn with ⟨m, rfl⟩
    let r := (2 * m + 1) % 8
    change ¬(r = 5 ∨ r = 7) at hnot
    change r = 1 ∨ r = 3
    have hr : r < 8 := Nat.mod_lt _ (by decide)
    have hrOdd : r % 2 = 1 := by
      calc
        r % 2 = (2 * m + 1) % 2 := Nat.mod_mod_of_dvd _ ⟨4, rfl⟩
        _ = 1 := by
          rw [Nat.add_mod, Nat.mul_mod]
          norm_num only [Nat.zero_mul, Nat.zero_mod, Nat.one_mod]
    interval_cases hcase : r
    · norm_num only at hrOdd
    · exact Or.inl rfl
    · norm_num only at hrOdd
    · exact Or.inr rfl
    · norm_num only at hrOdd
    · simp only [true_or, not_true] at hnot
    · norm_num only at hrOdd
    · simp only [or_true, not_true] at hnot
  · intro hres
    unfold aprclTwoAdicHighCorrectionFlag
    apply (decide_eq_false_iff_not).2
    rcases hn with ⟨m, rfl⟩
    rcases hres with hres | hres
    · intro hbad
      rcases hbad with hbad | hbad
      · norm_num only [hres] at hbad
      · norm_num only [hres] at hbad
    · intro hbad
      rcases hbad with hbad | hbad
      · norm_num only [hres] at hbad
      · norm_num only [hres] at hbad

/-- The low two-adic branch value from (C-21), computed in `ZMod n` as `(-q)^((n-1)/2)`. -/
def aprclTwoAdicKOneValue (n q : ℕ) : ZMod n :=
  (-(q : ZMod n)) ^ ((n - 1) / 2)

/-- Return the exponent `h ∈ {0,1}` when the (C-21) value is respectively `1` or `-1` in
`ZMod n`; return `none` when it is neither residue. -/
def aprclTwoAdicKOneCheck (n q : ℕ) : Option ℕ :=
  if aprclTwoAdicKOneValue n q = 1 then some 0
  else if aprclTwoAdicKOneValue n q = -1 then some 1 else none

/-- A successful low two-adic check returns the exponent and the corresponding sign equation. -/
theorem aprclTwoAdicKOneCheck_some_spec {n q h : ℕ} (hcheck : aprclTwoAdicKOneCheck n q = some h) :
    (h = 0 ∧ aprclTwoAdicKOneValue n q = 1) ∨ (h = 1 ∧ aprclTwoAdicKOneValue n q = -1) := by
  unfold aprclTwoAdicKOneCheck at hcheck
  by_cases hpos : aprclTwoAdicKOneValue n q = 1
  · simp only [hpos, ite_true] at hcheck
    have hh : 0 = h := Option.some.inj hcheck
    subst h
    exact Or.inl ⟨rfl, hpos⟩
  · simp only [hpos, ite_false] at hcheck
    by_cases hneg : aprclTwoAdicKOneValue n q = -1
    · simp only [hneg, ite_true] at hcheck
      have hh : 1 = h := Option.some.inj hcheck
      subst h
      exact Or.inr ⟨rfl, hneg⟩
    · simp only [hneg, ite_false] at hcheck
      cases hcheck

/-- A low two-adic check fails exactly when its value is neither sign. -/
theorem aprclTwoAdicKOneCheck_eq_none_iff {n q : ℕ} :
    aprclTwoAdicKOneCheck n q = none ↔
      aprclTwoAdicKOneValue n q ≠ 1 ∧ aprclTwoAdicKOneValue n q ≠ -1 := by
  constructor
  · intro hcheck
    unfold aprclTwoAdicKOneCheck at hcheck
    by_cases hpos : aprclTwoAdicKOneValue n q = 1
    · simp only [hpos, ite_true] at hcheck
      cases hcheck
    · simp only [hpos, ite_false] at hcheck
      by_cases hneg : aprclTwoAdicKOneValue n q = -1
      · simp only [hneg, ite_true] at hcheck
        cases hcheck
      · exact ⟨hpos, hneg⟩
  · rintro ⟨hpos, hneg⟩
    unfold aprclTwoAdicKOneCheck
    simp only [hpos, ite_false, hneg, ite_false]

/-- Require the low two-adic test to return the APR-CL exponent `h=1` and the residue class
`n ≡ 1 mod 4`; failures of either condition remain `none`. -/
def aprclTwoAdicKOneBranchCheck (n q : ℕ) : Option ℕ :=
  Option.filter (fun h => decide (h = 1 ∧ n % 4 = 1)) (aprclTwoAdicKOneCheck n q)

/-- The low two-adic branch accepts exactly the `h=1` sign result in residue class `1 mod 4`. -/
theorem aprclTwoAdicKOneBranchCheck_eq_some_iff {n q h : ℕ} :
    aprclTwoAdicKOneBranchCheck n q = some h ↔
      aprclTwoAdicKOneCheck n q = some h ∧ h = 1 ∧ n % 4 = 1 := by
  rw [aprclTwoAdicKOneBranchCheck, Option.filter_eq_some_iff]
  simp only [decide_eq_true_eq]

/-- The low two-adic branch returns `none` exactly when every sign-check result fails its
`h=1` and residue-class condition. -/
theorem aprclTwoAdicKOneBranchCheck_eq_none_iff {n q : ℕ} :
    aprclTwoAdicKOneBranchCheck n q = none ↔
      ∀ h, aprclTwoAdicKOneCheck n q = some h → ¬decide (h = 1 ∧ n % 4 = 1) = true := by
  rw [aprclTwoAdicKOneBranchCheck, Option.filter_eq_none_iff]

/-- A successful low two-adic branch check at exponent one certifies both the residue class and
the negative sign in the original (C-21) value. -/
theorem aprclTwoAdicKOneBranchCheck_some_value_eq_neg_one {n q : ℕ}
    (hcheck : aprclTwoAdicKOneBranchCheck n q = some 1) :
    n % 4 = 1 ∧ aprclTwoAdicKOneValue n q = -1 := by
  have hbranch := (aprclTwoAdicKOneBranchCheck_eq_some_iff).mp hcheck
  have hsign := aprclTwoAdicKOneCheck_some_spec hbranch.1
  rcases hsign with ⟨hh, hvalue⟩ | ⟨hh, hvalue⟩
  · cases hh
  · exact ⟨hbranch.2.2, hvalue⟩

/-- Represent the low two-adic `(C-21)` scalar in the `p=2,k=1` cyclotomic coefficient array.
Its quotient interpretation is the scalar embedded in the corresponding cyclotomic quotient. -/
def aprclTwoAdicKOneCoefficientArray (n q : ℕ) : cyclotomicFixedArray n 2 0 :=
  cyclotomicFixedArrayScale n 2 0 (aprclTwoAdicKOneValue n q) (cyclotomicFixedArrayOne n 2 0)

/-- Decode the `p=2,k=1` coefficient array to its scalar value in the cyclotomic quotient. -/
theorem aprclTwoAdicKOneCoefficientArray_class (n q : ℕ) :
    cyclotomicFixedArrayClass n 2 0 (aprclTwoAdicKOneCoefficientArray n q) =
      AdjoinRoot.of (primePowerCyclotomic 2 0 (ZMod n)) (aprclTwoAdicKOneValue n q) := by
  rw [aprclTwoAdicKOneCoefficientArray, cyclotomicFixedArrayClass_scale,
    cyclotomicFixedArrayOne_class n (by decide : Nat.Prime 2), mul_one]

/-- A successful low two-adic branch check is `-1` after translation to the `p=2,k=1`
cyclotomic quotient. This connects the scalar test to the common coefficient-array interface. -/
theorem aprclTwoAdicKOneBranchCheck_coefficientArray_class_eq_neg_one {n q : ℕ}
    (hcheck : aprclTwoAdicKOneBranchCheck n q = some 1) :
    cyclotomicFixedArrayClass n 2 0 (aprclTwoAdicKOneCoefficientArray n q) = -1 := by
  rw [aprclTwoAdicKOneCoefficientArray_class]
  have hvalue := aprclTwoAdicKOneBranchCheck_some_value_eq_neg_one hcheck
  rw [hvalue.2]
  exact map_neg (AdjoinRoot.of (primePowerCyclotomic 2 0 (ZMod n))) 1

/-- Compute the `J²` factor used by the `p=2,k=2` branch from one Jacobi datum. -/
def aprclTwoAdicKTwoJacobiSquareArray {n : ℕ} (hp : Nat.Prime 2) (datum : APRCLJacobiDatum 2 1) :
    cyclotomicFixedArray n 2 1 :=
  cyclotomicFixedArrayMulByExpansion n hp (datum.coefficientArray n hp)
    (datum.coefficientArray n hp)

/-- The `p=2,k=2` fixed-array expression for `(q J²)^(n/4) J^(2δ)`, where the residue correction
is selected by `n mod 4 = 3`. -/
def aprclTwoAdicKTwoArray {n : ℕ} (hp : Nat.Prime 2) (datum : APRCLJacobiDatum 2 1) :
    cyclotomicFixedArray n 2 1 :=
  let jSquared := aprclTwoAdicKTwoJacobiSquareArray hp datum
  let base := cyclotomicFixedArrayScale n 2 1 (datum.q : ZMod n) jSquared
  let basePower := cyclotomicFixedArrayPowBySquaring n hp base (n / 4)
  let correction := cyclotomicFixedArrayPowBySquaring n hp jSquared (if n % 4 = 3 then 1 else 0)
  cyclotomicFixedArrayMulByExpansion n hp basePower correction

/-- The `p=2,k=2` coefficient array decodes to the stated Jacobi-sum expression. -/
theorem aprclTwoAdicKTwoArray_class {n : ℕ} (hp : Nat.Prime 2) (datum : APRCLJacobiDatum 2 1) :
    cyclotomicFixedArrayClass n 2 1 (aprclTwoAdicKTwoArray hp datum) =
      ((AdjoinRoot.of (primePowerCyclotomic 2 1 (ZMod n)) (datum.q : ZMod n) *
            datum.jacobiSumValue n hp ^ 2) ^
          (n / 4)) *
        datum.jacobiSumValue n hp ^ (2 * (if n % 4 = 3 then 1 else 0)) := by
  simp only [aprclTwoAdicKTwoArray, aprclTwoAdicKTwoJacobiSquareArray,
    cyclotomicFixedArrayMulByExpansion_class_eq_mul, cyclotomicFixedArrayPowBySquaring_class,
    cyclotomicFixedArrayClass_scale, APRCLJacobiDatum.jacobiSumValue_eq_coefficientArray, pow_mul,
    pow_two]

/-- The checked `p=2,k=2` coefficient array. Its datum certifies the character exponents `(1,1)`
and the exact auxiliary-prime valuation required by the branch. -/
def aprclValidatedTwoAdicKTwoArray {n : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) : cyclotomicFixedArray n 2 1 :=
  aprclTwoAdicKTwoArray hp datum.datum

/-- The cyclotomic quotient value decoded from the checked `p=2,k=2` array. -/
noncomputable def aprclValidatedTwoAdicKTwoValue {n : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) : cyclotomicQuotient n 2 1 :=
  cyclotomicFixedArrayClass n 2 1 (aprclValidatedTwoAdicKTwoArray hp datum)

/-- Search the complete formal root-exponent period for the checked `p=2,k=2` value. `none`
means no exponent in that period represents the value; it does not by itself decide primality. -/
noncomputable def aprclValidatedTwoAdicKTwoCheck {n : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) : Option ℕ :=
  rootExponent n 2 1 (aprclValidatedTwoAdicKTwoValue hp datum)

/-- A successful `p=2,k=2` search returns the least exponent in the complete root period. -/
theorem aprclValidatedTwoAdicKTwoCheck_eq_some_iff {n h : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) :
    aprclValidatedTwoAdicKTwoCheck (n := n) hp datum = some h ↔
      h < primePowerIndex 2 1 ∧
        cyclotomicRoot n 2 1 ^ h = aprclValidatedTwoAdicKTwoValue hp datum ∧
        ∀ j < h, cyclotomicRoot n 2 1 ^ j ≠ aprclValidatedTwoAdicKTwoValue hp datum := by
  exact rootExponent_eq_some_iff n 2 1 (aprclValidatedTwoAdicKTwoValue hp datum) h

/-- A failed `p=2,k=2` search means no exponent in the formal period represents the value. -/
theorem aprclValidatedTwoAdicKTwoCheck_eq_none_iff {n : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) :
    aprclValidatedTwoAdicKTwoCheck (n := n) hp datum = none ↔
      ∀ h < primePowerIndex 2 1,
        cyclotomicRoot n 2 1 ^ h ≠ aprclValidatedTwoAdicKTwoValue hp datum := by
  exact rootExponent_eq_none_iff n 2 1 (aprclValidatedTwoAdicKTwoValue hp datum)

/-- Apply the remaining arithmetic conditions for the `p=2,k=2` branch to a successful
cyclotomic root search: the least exponent must be odd and `q^((n-1)/2)` must be `-1` modulo n.
Failure to meet either condition is represented by `none`. -/
noncomputable def aprclValidatedTwoAdicKTwoBranchCheck {n : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) : Option ℕ :=
  Option.filter (fun h => decide (h % 2 = 1 ∧ (datum.datum.q : ZMod n) ^ ((n - 1) / 2) = -1))
    (aprclValidatedTwoAdicKTwoCheck (n := n) hp datum)

/-- The `p=2,k=2` branch check succeeds exactly when the root search returns that exponent and
both additional arithmetic conditions hold. -/
theorem aprclValidatedTwoAdicKTwoBranchCheck_eq_some_iff {n h : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) :
    aprclValidatedTwoAdicKTwoBranchCheck (n := n) hp datum = some h ↔
      aprclValidatedTwoAdicKTwoCheck (n := n) hp datum = some h ∧
        h % 2 = 1 ∧ (datum.datum.q : ZMod n) ^ ((n - 1) / 2) = -1 := by
  rw [aprclValidatedTwoAdicKTwoBranchCheck, Option.filter_eq_some_iff]
  simp only [decide_eq_true_eq]

/-- The `p=2,k=2` branch check fails exactly when the root search finds nothing or its found
exponent fails at least one of the two arithmetic conditions. -/
theorem aprclValidatedTwoAdicKTwoBranchCheck_eq_none_iff {n : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) :
    aprclValidatedTwoAdicKTwoBranchCheck (n := n) hp datum = none ↔
      ∀ h,
        aprclValidatedTwoAdicKTwoCheck (n := n) hp datum = some h →
          decide (h % 2 = 1 ∧ (datum.datum.q : ZMod n) ^ ((n - 1) / 2) = -1) ≠ true := by
  rw [aprclValidatedTwoAdicKTwoBranchCheck, Option.filter_eq_none_iff]

/-- Compute the four-period root exponent of the validated `p=2,k=2` array. -/
def aprclValidatedTwoAdicKTwoArrayCheck {n : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) : Option ℕ :=
  cyclotomicFixedArrayRootExponent n hp (aprclValidatedTwoAdicKTwoArray hp datum)

/-- For inputs above one, the four-period array search equals the quotient specification. -/
theorem aprclValidatedTwoAdicKTwoArrayCheck_eq_check {n : ℕ} (hn : 1 < n) (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) :
    aprclValidatedTwoAdicKTwoArrayCheck (n := n) hp datum =
      aprclValidatedTwoAdicKTwoCheck (n := n) hp datum := by
  exact
    cyclotomicFixedArrayRootExponent_eq_rootExponent n hn hp
      (aprclValidatedTwoAdicKTwoArray hp datum)

/-- Compute the `p=2,k=2` branch result from arrays and its odd-exponent and Euler guards. -/
def aprclValidatedTwoAdicKTwoArrayBranchCheck {n : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) : Option ℕ :=
  Option.filter (fun h => decide (h % 2 = 1 ∧ (datum.datum.q : ZMod n) ^ ((n - 1) / 2) = -1))
    (aprclValidatedTwoAdicKTwoArrayCheck (n := n) hp datum)

/-- The executable four-period branch equals the quotient-based specification. -/
theorem aprclValidatedTwoAdicKTwoArrayBranchCheck_eq_check {n : ℕ} (hn : 1 < n) (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) :
    aprclValidatedTwoAdicKTwoArrayBranchCheck (n := n) hp datum =
      aprclValidatedTwoAdicKTwoBranchCheck (n := n) hp datum := by
  unfold aprclValidatedTwoAdicKTwoArrayBranchCheck aprclValidatedTwoAdicKTwoBranchCheck
  rw [aprclValidatedTwoAdicKTwoArrayCheck_eq_check hn hp datum]

/-- The executable four-period branch returns exactly the least matching root
subject to its odd-exponent and Euler guards. -/
theorem aprclValidatedTwoAdicKTwoArrayBranchCheck_eq_some_iff {n h : ℕ} (hn : 1 < n)
    (hp : Nat.Prime 2) (datum : APRCLJacobiDatumWithParameters 2 1 1 1) :
    aprclValidatedTwoAdicKTwoArrayBranchCheck (n := n) hp datum = some h ↔
      h < primePowerIndex 2 1 ∧
        cyclotomicRoot n 2 1 ^ h = aprclValidatedTwoAdicKTwoValue hp datum ∧
        (∀ j < h, cyclotomicRoot n 2 1 ^ j ≠ aprclValidatedTwoAdicKTwoValue hp datum) ∧
        h % 2 = 1 ∧ (datum.datum.q : ZMod n) ^ ((n - 1) / 2) = -1 := by
  rw [aprclValidatedTwoAdicKTwoArrayBranchCheck_eq_check hn hp datum]
  rw [aprclValidatedTwoAdicKTwoBranchCheck_eq_some_iff]
  rw [aprclValidatedTwoAdicKTwoCheck_eq_some_iff]
  simp only [and_assoc]

/-- The complete high two-adic branch coefficient-array expression, with the `J₂²` correction
selected from `n mod 8` rather than supplied by the caller. -/
def aprclTwoAdicHighBranchArray {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (datum₁₁ datum₂₁ datum₂ : APRCLJacobiDatum 2 k) : cyclotomicFixedArray n 2 k :=
  aprclTwoAdicHighCombinedArray hp hk datum₁₁ datum₂₁ datum₂ (aprclTwoAdicHighCorrectionFlag n)

/-- Decode the full high two-adic expression to its `J₃` product and residue-selected `J₂²`
correction. -/
theorem aprclTwoAdicHighBranchArray_class {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (datum₁₁ datum₂₁ datum₂ : APRCLJacobiDatum 2 k) :
    cyclotomicFixedArrayClass n 2 k (aprclTwoAdicHighBranchArray hp hk datum₁₁ datum₂₁ datum₂) =
      ((aprclTwoAdicHighJacobiIndexFamily k hk datum₁₁ datum₂₁).map
            (fun entry =>
              entry.jacobi.jacobiSumValue n hp ^
                (n * entry.productIndex / primePowerIndex 2 k))).prod *
        datum₂.jacobiSumValue n hp ^ (if aprclTwoAdicHighCorrectionFlag n then 2 else 0) := by
  exact
    aprclTwoAdicHighCombinedArray_class hp hk datum₁₁ datum₂₁ datum₂
      (aprclTwoAdicHighCorrectionFlag n)

/-- The high two-adic branch array with checked character exponents and exact auxiliary-prime
valuations: `(1,1)`, `(2,1)`, and `(2^(k-2), 3*2^(k-2))`. -/
def aprclValidatedTwoAdicHighBranchArray {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (datum₁₁ : APRCLJacobiDatumWithParameters 2 k 1 1)
    (datum₂₁ : APRCLJacobiDatumWithParameters 2 k 2 1)
    (datum₂ : APRCLJacobiDatumWithParameters 2 k (2 ^ (k - 2)) (3 * 2 ^ (k - 2))) :
    cyclotomicFixedArray n 2 k :=
  aprclTwoAdicHighBranchArray hp hk datum₁₁.datum datum₂₁.datum datum₂.datum

/-- Decode the high two-adic validated array using the established branch expression. -/
theorem aprclValidatedTwoAdicHighBranchArray_class {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (datum₁₁ : APRCLJacobiDatumWithParameters 2 k 1 1)
    (datum₂₁ : APRCLJacobiDatumWithParameters 2 k 2 1)
    (datum₂ : APRCLJacobiDatumWithParameters 2 k (2 ^ (k - 2)) (3 * 2 ^ (k - 2))) :
    cyclotomicFixedArrayClass n 2 k
        (aprclValidatedTwoAdicHighBranchArray hp hk datum₁₁ datum₂₁ datum₂) =
      ((aprclTwoAdicHighJacobiIndexFamily k hk datum₁₁.datum datum₂₁.datum).map
            (fun entry =>
              entry.jacobi.jacobiSumValue n hp ^
                (n * entry.productIndex / primePowerIndex 2 k))).prod *
        datum₂.datum.jacobiSumValue n hp ^ (if aprclTwoAdicHighCorrectionFlag n then 2 else 0) := by
  exact aprclTwoAdicHighBranchArray_class hp hk datum₁₁.datum datum₂₁.datum datum₂.datum

/-- The validated Jacobi data for one high two-adic branch.

Each datum certifies its prescribed character exponents and exact auxiliary-prime valuation.
The prime equalities and generator equalities require a common underlying character.
The backend index is one less than the mathematical valuation: the period is `2^(k+1)`.
The record is the input boundary for the high two-adic root and branch checks. -/
structure APRCLTwoAdicHighBranchData (k : ℕ) where
  /-- Common auxiliary prime used by all three Jacobi sums. -/
  auxiliaryPrime : ℕ
  /-- Checked character exponents `(1,1)`. -/
  datum₁₁ : APRCLJacobiDatumWithParameters 2 k 1 1
  /-- Checked character exponents `(2,1)`. -/
  datum₂₁ : APRCLJacobiDatumWithParameters 2 k 2 1
  /-- Checked character exponents `(2^(k-2),3*2^(k-2))`. -/
  datum₂ : APRCLJacobiDatumWithParameters 2 k (2 ^ (k - 2)) (3 * 2 ^ (k - 2))
  /-- The first datum uses the common auxiliary prime. -/
  datum₁₁_q_eq : datum₁₁.datum.q = auxiliaryPrime
  /-- The second datum uses the common auxiliary prime. -/
  datum₂₁_q_eq : datum₂₁.datum.q = auxiliaryPrime
  /-- The third datum uses the common auxiliary prime. -/
  datum₂_q_eq : datum₂.datum.q = auxiliaryPrime
  /-- The second Jacobi sum uses the first datum's primitive generator. -/
  datum₂₁_generator_eq : HEq datum₂₁.datum.generator datum₁₁.datum.generator
  /-- The correction Jacobi sum uses the same primitive generator. -/
  datum₂_generator_eq : HEq datum₂.datum.generator datum₁₁.datum.generator

/-- Search the complete root-exponent period for the validated high two-adic Jacobi product. -/
noncomputable def aprclValidatedTwoAdicHighCheck {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (data : APRCLTwoAdicHighBranchData k) : Option ℕ :=
  rootExponent n 2 k
    (cyclotomicFixedArrayClass n 2 k
      (aprclValidatedTwoAdicHighBranchArray hp hk data.datum₁₁ data.datum₂₁ data.datum₂))

/-- A successful high two-adic check returns the least exponent in the complete root period whose
cyclotomic root equals the validated Jacobi product. -/
theorem aprclValidatedTwoAdicHighCheck_eq_some_iff {n k h : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (data : APRCLTwoAdicHighBranchData k) :
    aprclValidatedTwoAdicHighCheck (n := n) hp hk data = some h ↔
      h < primePowerIndex 2 k ∧
        cyclotomicRoot n 2 k ^ h =
          cyclotomicFixedArrayClass n 2 k
            (aprclValidatedTwoAdicHighBranchArray hp hk data.datum₁₁ data.datum₂₁ data.datum₂) ∧
        ∀ j < h,
          cyclotomicRoot n 2 k ^ j ≠
            cyclotomicFixedArrayClass n 2 k
              (aprclValidatedTwoAdicHighBranchArray hp hk data.datum₁₁ data.datum₂₁
                data.datum₂) := by
  exact
    rootExponent_eq_some_iff n 2 k
      (cyclotomicFixedArrayClass n 2 k
        (aprclValidatedTwoAdicHighBranchArray hp hk data.datum₁₁ data.datum₂₁ data.datum₂))
      h

/-- Keep a high two-adic root match only when its exponent is odd and the Euler value at the
common auxiliary prime is `-1` modulo `n`. -/
noncomputable def aprclValidatedTwoAdicHighBranchCheck {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (data : APRCLTwoAdicHighBranchData k) : Option ℕ :=
  Option.filter (fun h => decide (h % 2 = 1 ∧ (data.auxiliaryPrime : ZMod n) ^ ((n - 1) / 2) = -1))
    (aprclValidatedTwoAdicHighCheck (n := n) hp hk data)

/-- The high two-adic branch check succeeds exactly when the root matches and both arithmetic
conditions on its exponent and common auxiliary prime hold. -/
theorem aprclValidatedTwoAdicHighBranchCheck_eq_some_iff {n k h : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (data : APRCLTwoAdicHighBranchData k) :
    aprclValidatedTwoAdicHighBranchCheck (n := n) hp hk data = some h ↔
      aprclValidatedTwoAdicHighCheck (n := n) hp hk data = some h ∧
        h % 2 = 1 ∧ (data.auxiliaryPrime : ZMod n) ^ ((n - 1) / 2) = -1 := by
  rw [aprclValidatedTwoAdicHighBranchCheck, Option.filter_eq_some_iff]
  simp only [decide_eq_true_eq]

/-- A failed high two-adic branch check means every matching root exponent fails an additional
arithmetic condition; it does not assert that the input is composite. -/
theorem aprclValidatedTwoAdicHighBranchCheck_eq_none_iff {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (data : APRCLTwoAdicHighBranchData k) :
    aprclValidatedTwoAdicHighBranchCheck (n := n) hp hk data = none ↔
      ∀ h,
        aprclValidatedTwoAdicHighCheck (n := n) hp hk data = some h →
          decide (h % 2 = 1 ∧ (data.auxiliaryPrime : ZMod n) ^ ((n - 1) / 2) = -1) ≠ true := by
  rw [aprclValidatedTwoAdicHighBranchCheck, Option.filter_eq_none_iff]

/-- Compute the high two-adic Jacobi root exponent from its validated coefficient array. -/
def aprclValidatedTwoAdicHighArrayCheck {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (data : APRCLTwoAdicHighBranchData k) : Option ℕ :=
  cyclotomicFixedArrayRootExponent n hp
    (aprclValidatedTwoAdicHighBranchArray hp hk data.datum₁₁ data.datum₂₁ data.datum₂)

/-- For inputs above one, the high two-adic array search equals the quotient specification. -/
theorem aprclValidatedTwoAdicHighArrayCheck_eq_check {n k : ℕ} (hn : 1 < n) (hp : Nat.Prime 2)
    (hk : 2 ≤ k) (data : APRCLTwoAdicHighBranchData k) :
    aprclValidatedTwoAdicHighArrayCheck (n := n) hp hk data =
      aprclValidatedTwoAdicHighCheck (n := n) hp hk data := by
  exact
    cyclotomicFixedArrayRootExponent_eq_rootExponent n hn hp
      (aprclValidatedTwoAdicHighBranchArray hp hk data.datum₁₁ data.datum₂₁ data.datum₂)

/-- Compute the high two-adic branch result from arrays, keeping only the
odd-exponent root with the required Euler value. -/
def aprclValidatedTwoAdicHighArrayBranchCheck {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (data : APRCLTwoAdicHighBranchData k) : Option ℕ :=
  Option.filter (fun h => decide (h % 2 = 1 ∧ (data.auxiliaryPrime : ZMod n) ^ ((n - 1) / 2) = -1))
    (aprclValidatedTwoAdicHighArrayCheck (n := n) hp hk data)

/-- The executable high two-adic branch equals the quotient-based specification. -/
theorem aprclValidatedTwoAdicHighArrayBranchCheck_eq_check {n k : ℕ} (hn : 1 < n) (hp : Nat.Prime 2)
    (hk : 2 ≤ k) (data : APRCLTwoAdicHighBranchData k) :
    aprclValidatedTwoAdicHighArrayBranchCheck (n := n) hp hk data =
      aprclValidatedTwoAdicHighBranchCheck (n := n) hp hk data := by
  unfold aprclValidatedTwoAdicHighArrayBranchCheck aprclValidatedTwoAdicHighBranchCheck
  rw [aprclValidatedTwoAdicHighArrayCheck_eq_check hn hp hk data]

/-- Decode a successful high two-adic branch result to the transformed Jacobi-data product,
including the separate correction, its odd root exponent, and minimality in the root period.
The inverse-index value of each factor is exposed by the following consumer theorem. -/
theorem aprclValidatedTwoAdicHighBranchCheck_success_product {n k h : ℕ} (hp : Nat.Prime 2)
    (hk : 2 ≤ k) (data : APRCLTwoAdicHighBranchData k)
    (hcheck : aprclValidatedTwoAdicHighBranchCheck (n := n) hp hk data = some h) :
    h % 2 = 1 ∧
      (data.auxiliaryPrime : ZMod n) ^ ((n - 1) / 2) = -1 ∧
      h < primePowerIndex 2 k ∧
      cyclotomicRoot n 2 k ^ h =
        ((aprclTwoAdicHighJacobiIndexFamily k hk data.datum₁₁.datum data.datum₂₁.datum).map
              (fun entry =>
                entry.jacobi.jacobiSumValue n hp ^
                  (n * entry.productIndex / primePowerIndex 2 k))).prod *
          data.datum₂.datum.jacobiSumValue n hp ^
            (if aprclTwoAdicHighCorrectionFlag n then 2 else 0) ∧
      ∀ j < h,
        cyclotomicRoot n 2 k ^ j ≠
          ((aprclTwoAdicHighJacobiIndexFamily k hk data.datum₁₁.datum data.datum₂₁.datum).map
                (fun entry =>
                  entry.jacobi.jacobiSumValue n hp ^
                    (n * entry.productIndex / primePowerIndex 2 k))).prod *
            data.datum₂.datum.jacobiSumValue n hp ^
              (if aprclTwoAdicHighCorrectionFlag n then 2 else 0) := by
  have hbranch := (aprclValidatedTwoAdicHighBranchCheck_eq_some_iff hp hk data).mp hcheck
  rcases hbranch with ⟨hroot, hodd, heuler⟩
  have hrootSpec := (aprclValidatedTwoAdicHighCheck_eq_some_iff hp hk data).mp hroot
  rcases hrootSpec with ⟨hbound, hmatch, hminimal⟩
  rw [aprclValidatedTwoAdicHighBranchArray_class] at hmatch hminimal
  exact ⟨hodd, heuler, hbound, hmatch, hminimal⟩

/-- An executable high two-adic array branch result satisfies the full
Jacobi-product equation, Euler guard, and least-root condition. -/
theorem aprclValidatedTwoAdicHighArrayBranchCheck_success_product {n k h : ℕ} (hn : 1 < n)
    (hp : Nat.Prime 2) (hk : 2 ≤ k) (data : APRCLTwoAdicHighBranchData k)
    (hcheck : aprclValidatedTwoAdicHighArrayBranchCheck (n := n) hp hk data = some h) :
    h % 2 = 1 ∧
      (data.auxiliaryPrime : ZMod n) ^ ((n - 1) / 2) = -1 ∧
      h < primePowerIndex 2 k ∧
      cyclotomicRoot n 2 k ^ h =
        ((aprclTwoAdicHighJacobiIndexFamily k hk data.datum₁₁.datum data.datum₂₁.datum).map
              (fun entry =>
                entry.jacobi.jacobiSumValue n hp ^
                  (n * entry.productIndex / primePowerIndex 2 k))).prod *
          data.datum₂.datum.jacobiSumValue n hp ^
            (if aprclTwoAdicHighCorrectionFlag n then 2 else 0) ∧
      ∀ j < h,
        cyclotomicRoot n 2 k ^ j ≠
          ((aprclTwoAdicHighJacobiIndexFamily k hk data.datum₁₁.datum data.datum₂₁.datum).map
                (fun entry =>
                  entry.jacobi.jacobiSumValue n hp ^
                    (n * entry.productIndex / primePowerIndex 2 k))).prod *
            data.datum₂.datum.jacobiSumValue n hp ^
              (if aprclTwoAdicHighCorrectionFlag n then 2 else 0) := by
  rw [aprclValidatedTwoAdicHighArrayBranchCheck_eq_check hn hp hk data] at hcheck
  exact aprclValidatedTwoAdicHighBranchCheck_success_product hp hk data hcheck

/-- A successful high two-adic branch retains its odd-exponent and Euler guards, while
each factor of its checked product is an inverse-index conjugate of one base Jacobi value. -/
theorem aprclValidatedTwoAdicHighBranchCheck_success_factor {n k h : ℕ} (hp : Nat.Prime 2)
    (hpn : Nat.Coprime 2 n) (hk : 2 ≤ k) (data : APRCLTwoAdicHighBranchData k)
    (hcheck : aprclValidatedTwoAdicHighBranchCheck (n := n) hp hk data = some h)
    (entry : APRCLIndexedJacobiDatum 2 k)
    (hentry :
      entry ∈ aprclTwoAdicHighJacobiIndexFamily k hk data.datum₁₁.datum data.datum₂₁.datum) :
    h % 2 = 1 ∧
      (data.auxiliaryPrime : ZMod n) ^ ((n - 1) / 2) = -1 ∧
      ∃ hcop : Nat.Coprime entry.productIndex (primePowerIndex 2 k),
        (cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop
              (entry.jacobi.jacobiSumValue n hp) =
            data.datum₁₁.datum.jacobiSumValue n hp ∨
          cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop
              (entry.jacobi.jacobiSumValue n hp) =
            data.datum₂₁.datum.jacobiSumValue n hp) := by
  have hbranch := aprclValidatedTwoAdicHighBranchCheck_success_product hp hk data hcheck
  have hvalue :=
    aprclTwoAdicHighJacobiIndexFamily_value_spec hpn hk data.datum₁₁.datum data.datum₂₁.datum entry
      hentry
  exact ⟨hbranch.1, hbranch.2.1, hvalue⟩

/-- On a successful high two-adic branch, each checked Jacobi factor is an inverse
root-substitution image of one of the two base values. -/
theorem aprclValidatedTwoAdicHighBranchCheck_success_factor_inverse {n k h : ℕ} (hp : Nat.Prime 2)
    (hpn : Nat.Coprime 2 n) (hk : 2 ≤ k) (data : APRCLTwoAdicHighBranchData k)
    (hcheck : aprclValidatedTwoAdicHighBranchCheck (n := n) hp hk data = some h)
    (entry : APRCLIndexedJacobiDatum 2 k)
    (hentry :
      entry ∈ aprclTwoAdicHighJacobiIndexFamily k hk data.datum₁₁.datum data.datum₂₁.datum) :
    h % 2 = 1 ∧
      (data.auxiliaryPrime : ZMod n) ^ ((n - 1) / 2) = -1 ∧
      ∃ hcop : Nat.Coprime entry.productIndex (primePowerIndex 2 k),
        (entry.jacobi.jacobiSumValue n hp =
            (cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop).symm
              (data.datum₁₁.datum.jacobiSumValue n hp) ∨
          entry.jacobi.jacobiSumValue n hp =
            (cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop).symm
              (data.datum₂₁.datum.jacobiSumValue n hp)) := by
  have hbranch := aprclValidatedTwoAdicHighBranchCheck_success_product hp hk data hcheck
  have hvalue :=
    aprclTwoAdicHighJacobiIndexFamily_inverse_value hpn hk data.datum₁₁.datum data.datum₂₁.datum
      entry hentry
  exact ⟨hbranch.1, hbranch.2.1, hvalue⟩

/-- A successful executable high two-adic branch yields each inverse
root-substitution Jacobi factor together with its odd-exponent and Euler guards. -/
theorem aprclValidatedTwoAdicHighArrayBranchCheck_success_factor_inverse {n k h : ℕ} (hn : 1 < n)
    (hp : Nat.Prime 2) (hpn : Nat.Coprime 2 n) (hk : 2 ≤ k) (data : APRCLTwoAdicHighBranchData k)
    (hcheck : aprclValidatedTwoAdicHighArrayBranchCheck (n := n) hp hk data = some h)
    (entry : APRCLIndexedJacobiDatum 2 k)
    (hentry :
      entry ∈ aprclTwoAdicHighJacobiIndexFamily k hk data.datum₁₁.datum data.datum₂₁.datum) :
    h % 2 = 1 ∧
      (data.auxiliaryPrime : ZMod n) ^ ((n - 1) / 2) = -1 ∧
      ∃ hcop : Nat.Coprime entry.productIndex (primePowerIndex 2 k),
        (entry.jacobi.jacobiSumValue n hp =
            (cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop).symm
              (data.datum₁₁.datum.jacobiSumValue n hp) ∨
          entry.jacobi.jacobiSumValue n hp =
            (cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop).symm
              (data.datum₂₁.datum.jacobiSumValue n hp)) := by
  rw [aprclValidatedTwoAdicHighArrayBranchCheck_eq_check hn hp hk data] at hcheck
  exact
    aprclValidatedTwoAdicHighBranchCheck_success_factor_inverse hp hpn hk data hcheck entry hentry

end PseudoPrime.PrimeTest.APRCL
