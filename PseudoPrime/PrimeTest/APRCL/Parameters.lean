/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Finite APR-CL auxiliary-prime parameters

This file defines the finite auxiliary-prime set `Q(t)` and the APR-CL modulus used by the
fixed-modulus development. The executable definition enumerates divisors of `t`, then maps each
divisor `d` to the candidate prime `d + 1`. The modulus agrees with the paper's `e(t)` for even
`t`, the range used by the main period theorem; odd `t` is retained only as a total extension.
-/

namespace PseudoPrime.PrimeTest.APRCL

/-- The fixed-`J₁,₁` APR-CL restriction on an odd auxiliary prime: `2^(p-1)` is not `1` modulo
`p^2`. This is a parameter condition, not a condition on the input being tested. -/
def aprclB2Condition (p : ℕ) : Prop := 2 ^ (p - 1) % p ^ 2 ≠ 1

/-- Executable Boolean test for the fixed-`J₁,₁` APR-CL B2 parameter condition. -/
def aprclB2Check (p : ℕ) : Bool := decide (2 ^ (p - 1) % p ^ 2 ≠ 1)

/-- The B2 Boolean accepts exactly when the auxiliary-prime parameter satisfies its proposition.
-/
theorem aprclB2Check_eq_true_iff (p : ℕ) :
    aprclB2Check p = true ↔ aprclB2Condition p := by
  simp only [aprclB2Check, decide_eq_true_eq, aprclB2Condition]

/-- Every prime-modulus unit group has a primitive root of order `q - 1`. This existence lemma
is the mathematical coverage premise for a later finite primitive-root search; it does not itself
provide an executable search result. -/
theorem exists_primitiveRoot_unit_of_prime {q : ℕ} (hq : Nat.Prime q) :
    ∃ a : (ZMod q)ˣ, IsPrimitiveRoot a (q - 1) := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod q)ˣ)
  have hcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  refine ⟨a, ?_⟩
  rw [IsPrimitiveRoot.iff_orderOf]
  exact ha.trans hcard

/-- Executable bounded test for whether `a` generates all nonzero residues modulo `q`.
It checks the `(q - 1)`-st power and excludes every smaller positive exponent by a finite scan.
The result is Boolean so the candidate search below does not depend on noncomputable `orderOf`.
-/
def primitiveRootCandidateTest (q a : ℕ) : Bool :=
  decide ((a : ZMod q) ^ (q - 1) = 1) &&
    (List.range (q - 1)).all
      (fun l => decide (l = 0 ∨ (a : ZMod q) ^ l ≠ 1))

/-- The finite power test accepts exactly the primitive roots of order `q - 1` modulo a prime.
The proof uses the minimal-period characterization and the complete list of smaller exponents.
-/
theorem primitiveRootCandidateTest_eq_true_iff {q a : ℕ} (hq : Nat.Prime q) :
    primitiveRootCandidateTest q a = true ↔
      IsPrimitiveRoot (a : ZMod q) (q - 1) := by
  rw [primitiveRootCandidateTest, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  constructor
  · rintro ⟨hpow, hsmall⟩
    apply IsPrimitiveRoot.mk_of_lt (a : ZMod q) (Nat.sub_pos_of_lt hq.one_lt) hpow
    intro l hl hk hEq
    have hmem : l ∈ List.range (q - 1) := List.mem_range.mpr hk
    have h := hsmall l hmem
    exact (Or.resolve_left (of_decide_eq_true h) (Nat.ne_of_gt hl)) hEq
  · intro hroot
    constructor
    · exact hroot.pow_eq_one
    · intro l hmem
      have hl : l < q - 1 := List.mem_range.mp hmem
      by_cases hzero : l = 0
      · exact decide_eq_true_eq.mpr (Or.inl hzero)
      · have hnot : (a : ZMod q) ^ l ≠ 1 := by
          intro hEq
          have hdiv := hroot.dvd_of_pow_eq_one l hEq
          exact (Nat.not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hzero) hdiv)) hl
        exact decide_eq_true_eq.mpr (Or.inr hnot)

/-- Search residues in increasing order and return the first candidate passing the finite
primitive-root test. `none` means no candidate in `[0, q)` passed; it makes no claim outside
that complete residue range. -/
def primitiveRootSearch (q : ℕ) : Option ℕ :=
  (List.range q).find? (primitiveRootCandidateTest q)

/-- A successful primitive-root search returns an in-range genuine primitive root. -/
theorem primitiveRootSearch_some_spec {q a : ℕ} (hq : Nat.Prime q)
    (h : primitiveRootSearch q = some a) :
    a < q ∧ IsPrimitiveRoot (a : ZMod q) (q - 1) := by
  rw [primitiveRootSearch, List.find?_range_eq_some] at h
  rcases h with ⟨htest, hmem, _⟩
  exact ⟨List.mem_range.mp hmem, (primitiveRootCandidateTest_eq_true_iff hq).mp htest⟩

/-- A successful natural-residue search value lifts to a unit-group primitive root.
The primitive-root power condition proves nonzeroness, so this lift is valid even though the
executable search itself enumerates natural representatives. -/
theorem primitiveRootSearch_some_unit_spec {q a : ℕ} (hq : Nat.Prime q)
    (hsearch : primitiveRootSearch q = some a) :
    ∃ g : (ZMod q)ˣ, (g : ZMod q) = (a : ZMod q) ∧
      IsPrimitiveRoot g (q - 1) := by
  obtain ⟨_, hroot⟩ := primitiveRootSearch_some_spec hq hsearch
  have hne : q - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hq.one_lt
  have hunit : IsUnit (a : ZMod q) := hroot.isUnit hne
  refine ⟨hunit.unit, hunit.unit_spec, ?_⟩
  exact (IsPrimitiveRoot.coe_units_iff).mp (by
    rw [hunit.unit_spec]
    exact hroot)

/-- Search failure is equivalent to rejection of every candidate in the specified residue range.
-/
theorem primitiveRootSearch_none_iff (q : ℕ) :
    primitiveRootSearch q = none ↔
      ∀ a, a < q → primitiveRootCandidateTest q a = false := by
  rw [primitiveRootSearch, List.find?_range_eq_none]
  simp only [Bool.not_eq_true_eq_eq_false]

/-- For every prime modulus the exhaustive candidate scan finds a primitive root.
The cyclicity theorem proves coverage, while `List.find?_isSome` connects that witness to the
executable Option result. -/
theorem primitiveRootSearch_isSome_of_prime {q : ℕ} (hq : Nat.Prime q) :
    (primitiveRootSearch q).isSome = true := by
  have : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨u, hu⟩ := exists_primitiveRoot_unit_of_prime hq
  let a := (u : ZMod q).val
  have hlt : a < q := ZMod.val_lt (u : ZMod q)
  have hcast : (a : ZMod q) = (u : ZMod q) := ZMod.natCast_zmod_val (u : ZMod q)
  have hinj : Function.Injective (Units.coeHom (ZMod q)) := by
    intro x y h
    exact Units.ext h
  have hroot : IsPrimitiveRoot (a : ZMod q) (q - 1) := by
    rw [hcast]
    exact IsPrimitiveRoot.map_of_injective hu hinj
  have htest := (primitiveRootCandidateTest_eq_true_iff hq).mpr hroot
  exact (List.find?_isSome).2 ⟨a, List.mem_range.mpr hlt, htest⟩

/-- Every prime modulus has a concrete residue returned by the bounded primitive-root search.
The theorem converts the `isSome` coverage contract into an explicit successful Option value. -/
theorem primitiveRootSearch_exists_of_prime {q : ℕ} (hq : Nat.Prime q) :
    ∃ a, primitiveRootSearch q = some a := by
  exact Option.isSome_iff_exists.mp (primitiveRootSearch_isSome_of_prime hq)

/-- Search the complete exponent range below `q - 1` for a discrete logarithm in the supplied
unit-group generator. The result is optional because a nonprimitive generator or a non-prime
modulus need not represent every target in this bounded range; for prime moduli and primitive
generators, coverage is proved below. -/
def discreteLogSearch {q : ℕ} (g x : (ZMod q)ˣ) : Option ℕ :=
  (List.range (q - 1)).find? (fun e => decide (g ^ e = x))

/-- A successful discrete-log search returns an exponent in range with the required power value.
This is the soundness contract consumed by the APR-CL logarithm table. -/
theorem discreteLogSearch_some_spec {q e : ℕ} {g x : (ZMod q)ˣ}
    (h : discreteLogSearch g x = some e) :
    e < q - 1 ∧ g ^ e = x := by
  rw [discreteLogSearch, List.find?_range_eq_some] at h
  rcases h with ⟨htest, hmem, _⟩
  exact ⟨List.mem_range.mp hmem, of_decide_eq_true htest⟩

/-- Search failure means that no exponent in the bounded table represents the target unit. -/
theorem discreteLogSearch_none_iff {q : ℕ} (g x : (ZMod q)ˣ) :
    discreteLogSearch g x = none ↔
      ∀ e, e < q - 1 → g ^ e ≠ x := by
  rw [discreteLogSearch, List.find?_range_eq_none]
  simp only [Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]

/-- For a prime modulus, a unit-group primitive root represents every unit in the bounded exponent
range. Fermat's theorem places the target unit among the `(q - 1)`-st roots of unity; the
primitive-root theorem then supplies the exponent, proving this executable search cannot fail. -/
theorem discreteLogSearch_isSome_of_prime {q : ℕ} (hq : Nat.Prime q)
    (g x : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) :
    (discreteLogSearch g x).isSome = true := by
  have hfact : Fact (Nat.Prime q) := ⟨hq⟩
  have hne : q - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hq.one_lt
  have hneZero : NeZero (q - 1) := ⟨hne⟩
  have hpowval : (x : ZMod q) ^ (q - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one (Units.ne_zero x)
  have hpow : x ^ (q - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hpowval
  have hroot := (mem_rootsOfUnity (q - 1) x).2 hpow
  obtain ⟨e, he, heq⟩ :=
    @IsPrimitiveRoot.eq_pow_of_mem_rootsOfUnity (ZMod q) _ _ (q - 1)
      hneZero g x hg hroot
  exact (List.find?_isSome).2
    ⟨e, List.mem_range.mpr he, decide_eq_true_eq.mpr heq⟩

/-- Materialize the bounded power-to-exponent table for a proposed generator. Every row stores
the unit `g ^ e` together with its exponent, in increasing exponent order; duplicate powers are
retained so the first-match convention agrees with `discreteLogSearch`. -/
def discreteLogPowerTable {q : ℕ} (g : (ZMod q)ˣ) : List ((ZMod q)ˣ × ℕ) :=
  (List.range (q - 1)).map (fun e => (g ^ e, e))

/-- Look up a target unit in the materialized bounded power table. `none` means that the target
does not occur among the listed powers; for a prime modulus and a primitive-root generator, the
coverage theorem below rules this out. -/
def discreteLogTableSearch {q : ℕ} (g x : (ZMod q)ˣ) : Option ℕ :=
  ((discreteLogPowerTable g).find? (fun entry => decide (entry.1 = x))).map Prod.snd

/-- Searching the materialized table returns exactly the result of the executable bounded
discrete-log search, including its first-match behavior. -/
theorem discreteLogTableSearch_eq_discreteLogSearch {q : ℕ} (g x : (ZMod q)ˣ) :
    discreteLogTableSearch g x = discreteLogSearch g x := by
  unfold discreteLogTableSearch discreteLogPowerTable discreteLogSearch
  rw [List.find?_map]
  simp only [Function.comp_def]
  rw [Option.map_map]
  change Option.map (fun e : ℕ => Prod.snd (g ^ e, e)) _ = _
  simp only [Option.map_id']

/-- A successful table lookup returns an in-range exponent whose power is the target unit. -/
theorem discreteLogTableSearch_some_spec {q e : ℕ} {g x : (ZMod q)ˣ}
    (h : discreteLogTableSearch g x = some e) :
    e < q - 1 ∧ g ^ e = x := by
  rw [discreteLogTableSearch_eq_discreteLogSearch] at h
  exact discreteLogSearch_some_spec h

/-- The materialized table contains every unit when its modulus is prime and its generator is
primitive, so the table lookup has a successful `Option` result. -/
theorem discreteLogTableSearch_isSome_of_prime {q : ℕ} (hq : Nat.Prime q)
    (g x : (ZMod q)ˣ) (hg : IsPrimitiveRoot g (q - 1)) :
    (discreteLogTableSearch g x).isSome = true := by
  rw [discreteLogTableSearch_eq_discreteLogSearch]
  exact discreteLogSearch_isSome_of_prime hq g x hg

/-- The root search and materialized power table compose: every prime modulus supplies a searched
primitive root and every target unit then has a returned exponent from its finite table. -/
theorem primitiveRootSearch_discreteLogTableSearch_exists_of_prime {q : ℕ}
    (hq : Nat.Prime q) (x : (ZMod q)ˣ) :
    ∃ a, ∃ g : (ZMod q)ˣ, ∃ e, primitiveRootSearch q = some a ∧
      (g : ZMod q) = (a : ZMod q) ∧ IsPrimitiveRoot g (q - 1) ∧
      discreteLogTableSearch g x = some e := by
  obtain ⟨a, hsearch⟩ := primitiveRootSearch_exists_of_prime hq
  obtain ⟨g, hcast, hroot⟩ := primitiveRootSearch_some_unit_spec hq hsearch
  have hsome := discreteLogTableSearch_isSome_of_prime hq g x hroot
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨a, g, e, hsearch, hcast, hroot, he⟩

/-- The auxiliary primes `q` satisfying `q - 1 ∣ t`, enumerated from divisors of `t`. -/
def auxiliaryPrimes (t : ℕ) : Finset ℕ :=
  ((Nat.divisors t).image (fun d => d + 1)).filter Nat.Prime

/-- Executable finite scan of all primes whose predecessor may divide `t`. -/
def auxiliaryPrimeSearch (t : ℕ) : List ℕ :=
  (List.range (t + 2)).filter (fun q => decide (Nat.Prime q ∧ q - 1 ∣ t))

/-- The executable scan returns exactly the in-range elements of `Q(t)`. -/
theorem mem_auxiliaryPrimeSearch_iff {t q : ℕ} :
    q ∈ auxiliaryPrimeSearch t ↔ q < t + 2 ∧ Nat.Prime q ∧ q - 1 ∣ t := by
  simp only [auxiliaryPrimeSearch, List.mem_filter, List.mem_range, decide_eq_true_eq]

/-- For positive `t`, the finite scan needs no extra cutoff hypothesis. -/
theorem mem_auxiliaryPrimeSearch_iff_prime_sub_dvd {t q : ℕ} (ht : t ≠ 0) :
    q ∈ auxiliaryPrimeSearch t ↔ Nat.Prime q ∧ q - 1 ∣ t := by
  rw [mem_auxiliaryPrimeSearch_iff]
  constructor
  · exact fun h => ⟨h.2.1, h.2.2⟩
  · rintro ⟨hq, hdvd⟩
    have hpos : 0 < t := Nat.pos_of_ne_zero ht
    have hle : q - 1 ≤ t := Nat.le_of_dvd hpos hdvd
    exact ⟨Nat.lt_succ_of_le (Nat.sub_le_iff_le_add.mp hle), hq, hdvd⟩

/-- For even `t`, the APR-CL modulus `e(t) = 2 ∏ q^(1+v_q(t))` over auxiliary primes.
This formula is extended to odd `t` for a total executable definition; the paper instead sets
`e(t) = 2` when `t` is odd. The proved global unit-period theorem uses even `t`. -/
def modulus (t : ℕ) : ℕ :=
  2 * (auxiliaryPrimes t).prod (fun q => q ^ (1 + Nat.factorization t q))

/-- The APR-CL modulus is positive for every natural parameter.
Each indexed factor is a positive prime power, so its finite product is nonzero. This bound
supplies the modulus lower bound used by the final divisor-orbit criterion. -/
theorem modulus_pos (t : ℕ) : 0 < modulus t := by
  have hblocks : ∀ q ∈ auxiliaryPrimes t,
      q ^ (1 + Nat.factorization t q) ≠ 0 := by
    intro q hq
    have hqprime : Nat.Prime q := (Finset.mem_filter.mp hq).2
    exact (Nat.pow_pos hqprime.pos).ne'
  unfold modulus
  exact Nat.mul_pos (by norm_num only) (Nat.pos_of_ne_zero
    (Finset.prod_ne_zero_iff.mpr hblocks))

/-- Membership in the auxiliary-prime set exposes the divisor that generated the prime. -/
theorem mem_auxiliaryPrimes_iff {t q : ℕ} (ht : t ≠ 0) :
    q ∈ auxiliaryPrimes t ↔ ∃ d, d ∣ t ∧ q = d + 1 ∧ Nat.Prime q := by
  simp only [auxiliaryPrimes, Finset.mem_filter, Finset.mem_image, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨d, hd, rfl⟩, hprime⟩
    exact ⟨d, hd.1, rfl, hprime⟩
  · rintro ⟨d, hd, rfl, hprime⟩
    exact ⟨⟨d, ⟨hd, ht⟩, rfl⟩, hprime⟩

/-- The auxiliary-prime set is exactly the primes whose predecessor divides `t`. -/
theorem mem_auxiliaryPrimes_iff_prime_sub_dvd {t q : ℕ} (ht : t ≠ 0) :
    q ∈ auxiliaryPrimes t ↔ Nat.Prime q ∧ q - 1 ∣ t := by
  rw [mem_auxiliaryPrimes_iff ht]
  constructor
  · rintro ⟨d, hd, hq, hprime⟩
    subst q
    exact ⟨hprime, by simpa only [Nat.add_sub_cancel_right] using hd⟩
  · rintro ⟨hprime, hd⟩
    have hq : 1 ≤ q := Nat.Prime.pos hprime
    refine ⟨q - 1, hd, ?_, hprime⟩
    exact (Nat.sub_add_cancel hq).symm

/-- The factor `2` occurs in `Q(t)` for every positive parameter. -/
theorem two_mem_auxiliaryPrimes {t : ℕ} (ht : t ≠ 0) : 2 ∈ auxiliaryPrimes t := by
  rw [mem_auxiliaryPrimes_iff_prime_sub_dvd ht]
  exact ⟨Nat.prime_two, one_dvd t⟩

/-- Each prime-power block contributes to the 2-adic valuation only when its prime is `2`. -/
private theorem auxiliaryPrimePower_factorization_two {t q : ℕ}
    (ht : t ≠ 0) (hq : q ∈ auxiliaryPrimes t) :
    (q ^ (1 + Nat.factorization t q)).factorization 2 =
      if q = 2 then 1 + Nat.factorization t q else 0 := by
  rcases (mem_auxiliaryPrimes_iff (t := t) (q := q) ht).mp hq with
    ⟨d, _, hqeq, hprime⟩
  rw [Nat.Prime.factorization_pow hprime]
  by_cases hq2 : q = 2
  · subst q
    have hd1 : d = 1 := Nat.succ.inj hq2
    subst d
    simp only [Finsupp.single_add, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, reduceIte]
  · have hdne : d ≠ 1 := by
      intro hd
      subst d
      apply hq2
      rw [hqeq]
    simp only [Finsupp.single_apply, hq2]

/-- A prime-power block has a nonzero valuation only at its own auxiliary prime. -/
private theorem auxiliaryPrimePower_factorization {t r p : ℕ}
    (ht : t ≠ 0) (hr : r ∈ auxiliaryPrimes t) :
    (r ^ (1 + Nat.factorization t r)).factorization p =
      if r = p then 1 + Nat.factorization t r else 0 := by
  rcases (mem_auxiliaryPrimes_iff (t := t) (q := r) ht).mp hr with
    ⟨d, _, hreq, hrprime⟩
  rw [Nat.Prime.factorization_pow hrprime]
  by_cases hrp : r = p <;> simp only [hrp, Finsupp.single_apply]

/-- The prime factorization of the APR-CL modulus is exactly the leading factor `2`
plus the prime-power blocks indexed by `Q(t)`. -/
theorem factorization_modulus {t : ℕ} (ht : t ≠ 0) :
    (modulus t).factorization = Finsupp.single 2 1 +
      ∑ q ∈ auxiliaryPrimes t,
        Finsupp.single q (1 + Nat.factorization t q) := by
  have hprod :
      ∀ q ∈ auxiliaryPrimes t, q ^ (1 + Nat.factorization t q) ≠ 0 := by
    intro q hq
    rcases (mem_auxiliaryPrimes_iff (t := t) (q := q) ht).mp hq with
      ⟨d, _, _, hqprime⟩
    exact (Nat.pow_pos hqprime.pos).ne'
  have hfactorization_two : Nat.factorization 2 = Finsupp.single 2 1 := by
    simpa only [pow_one] using
      (Nat.Prime.factorization_pow (p := 2) (k := 1) Nat.prime_two)
  rw [modulus, Nat.factorization_mul (by norm_num only) (Finset.prod_ne_zero_iff.mpr hprod),
    Nat.factorization_prod hprod]
  rw [hfactorization_two]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rcases (mem_auxiliaryPrimes_iff (t := t) (q := q) ht).mp hq with
    ⟨d, _, _, hqprime⟩
  rw [Nat.Prime.factorization_pow hqprime]

/-- The prime factorization exponent of any auxiliary prime in the full modulus is
its block exponent, with one extra factor of `2` for the leading modulus factor. -/
theorem factorization_modulus_auxiliaryPrime {t q : ℕ} (ht : t ≠ 0)
    (hq : q ∈ auxiliaryPrimes t) :
    (modulus t).factorization q = (if q = 2 then 1 else 0) +
      (1 + Nat.factorization t q) := by
  have hblocks :
      ∑ r ∈ auxiliaryPrimes t,
        (r ^ (1 + Nat.factorization t r)).factorization q =
          1 + Nat.factorization t q := by
    rw [Finset.sum_eq_single q]
    · rw [auxiliaryPrimePower_factorization ht hq]
      simp only [reduceIte]
    · intro r hr hrne
      rw [auxiliaryPrimePower_factorization ht hr]
      simp only [hrne, reduceIte]
    · intro hnot
      exact (hnot hq).elim
  have hprod :
      ∀ r ∈ auxiliaryPrimes t, r ^ (1 + Nat.factorization t r) ≠ 0 := by
    intro r hr
    rcases (mem_auxiliaryPrimes_iff (t := t) (q := r) ht).mp hr with
      ⟨d, _, _, hrprime⟩
    exact (Nat.pow_pos hrprime.pos).ne'
  rw [modulus, Nat.factorization_mul (by norm_num only) (Finset.prod_ne_zero_iff.mpr hprod)]
  have hfactorprod := Nat.factorization_prod_apply
    (p := q) (S := auxiliaryPrimes t)
    (g := fun r => r ^ (1 + Nat.factorization t r)) hprod
  change (Nat.factorization 2) q +
      ((auxiliaryPrimes t).prod (fun r => r ^ (1 + Nat.factorization t r))).factorization q = _
  rw [hfactorprod, hblocks]
  have hfactorization_two : Nat.factorization 2 = Finsupp.single 2 1 := by
    simpa only [pow_one] using
      (Nat.Prime.factorization_pow (p := 2) (k := 1) Nat.prime_two)
  rw [hfactorization_two]
  simp only [Finsupp.single_apply, eq_comm]

/-- The exponent of `2` in the full APR-CL modulus includes both the leading factor
and the `q = 2` auxiliary-prime block. -/
theorem factorization_modulus_two {t : ℕ} (ht : t ≠ 0) :
    (modulus t).factorization 2 = 2 + Nat.factorization t 2 := by
  have htwo : 2 ∈ auxiliaryPrimes t := two_mem_auxiliaryPrimes ht
  have hblocks :
      ∑ q ∈ auxiliaryPrimes t,
        (q ^ (1 + Nat.factorization t q)).factorization 2 =
          1 + Nat.factorization t 2 := by
    rw [Finset.sum_eq_single 2]
    · rw [Nat.Prime.factorization_pow Nat.prime_two]
      simp only [Finsupp.single_add, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
    · intro q hq hqne
      rw [auxiliaryPrimePower_factorization_two ht hq]
      simp only [hqne, reduceIte]
    · intro hnot
      exact (hnot htwo).elim
  have hprod :
      ∀ q ∈ auxiliaryPrimes t, q ^ (1 + Nat.factorization t q) ≠ 0 := by
    intro q hq
    rcases (mem_auxiliaryPrimes_iff (t := t) (q := q) ht).mp hq with
      ⟨d, _, _, hqprime⟩
    have hqpos := Nat.Prime.pos hqprime
    exact (Nat.pow_pos hqpos).ne'
  rw [modulus, Nat.factorization_mul (by norm_num only) (Finset.prod_ne_zero_iff.mpr hprod)]
  have hfactorprod := Nat.factorization_prod_apply
    (p := 2) (S := auxiliaryPrimes t)
    (g := fun q => q ^ (1 + Nat.factorization t q)) hprod
  change (Nat.factorization 2) 2 +
      ((auxiliaryPrimes t).prod (fun q => q ^ (1 + Nat.factorization t q))).factorization 2 = _
  rw [hfactorprod, hblocks]
  have hfactorization_two : Nat.factorization 2 = Finsupp.single 2 1 := by
    simpa only [pow_one] using
      (Nat.Prime.factorization_pow (p := 2) (k := 1) Nat.prime_two)
  rw [hfactorization_two]
  simp only [Finsupp.single_eq_same]
  simp only [← Nat.add_assoc, Nat.reduceAdd]

/-- The integer `4` is not prime, as it has a proper divisor. -/
private theorem notPrimeFour : ¬ Nat.Prime 4 := by
  intro h
  rcases Nat.prime_def_lt.mp h with ⟨_, hdiv⟩
  have hh := hdiv 2 (by norm_num only) (by norm_num only)
  norm_num only at hh

/-- Thirteen is prime, checked against every smaller possible divisor. -/
private theorem primeThirteen : Nat.Prime 13 := by
  rw [Nat.prime_def_lt]
  constructor
  · norm_num only
  · intro m hm hd
    interval_cases m <;> norm_num only at *

/-- The auxiliary primes for `t = 2` are exactly `2` and `3`. -/
private theorem auxiliaryPrimes_two : auxiliaryPrimes 2 = {2, 3} := by
  ext q
  rw [mem_auxiliaryPrimes_iff_prime_sub_dvd (by norm_num only)]
  constructor
  · rintro ⟨hp, hd⟩
    have hqhi : q - 1 ≤ 2 := Nat.le_of_dvd (by norm_num only) hd
    have hq : q ≤ 3 := by exact (Nat.sub_le_iff_le_add.mp hqhi)
    interval_cases q
    · have h : 2 ≤ (0 : ℕ) := hp.two_le
      exact False.elim ((Nat.not_succ_le_zero 1) h)
    · have h : 2 ≤ (1 : ℕ) := hp.two_le
      exact False.elim ((Nat.not_succ_le_self 1) h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    · simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact ⟨Nat.prime_two, by decide⟩
    · exact ⟨Nat.prime_three, by decide⟩

/-- The auxiliary primes for `t = 12` are exactly `2, 3, 5, 7, 13`. -/
private theorem auxiliaryPrimes_twelve : auxiliaryPrimes 12 = {2, 3, 5, 7, 13} := by
  ext q
  rw [mem_auxiliaryPrimes_iff_prime_sub_dvd (by norm_num only)]
  constructor
  · rintro ⟨hp, hd⟩
    have hqhi : q - 1 ≤ 12 := Nat.le_of_dvd (by norm_num only) hd
    have hq : q ≤ 13 := by exact (Nat.sub_le_iff_le_add.mp hqhi)
    interval_cases q
    · have h : 2 ≤ (0 : ℕ) := hp.two_le
      exact False.elim ((Nat.not_succ_le_zero 1) h)
    · have h : 2 ≤ (1 : ℕ) := hp.two_le
      exact False.elim ((Nat.not_succ_le_self 1) h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exact False.elim (notPrimeFour hp)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · norm_num only at hd
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · norm_num only at hd
    · norm_num only at hd
    · norm_num only at hd
    · norm_num only at hd
    · norm_num only at hd
    · simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact ⟨Nat.prime_two, by decide⟩
    · exact ⟨Nat.prime_three, by decide⟩
    · exact ⟨Nat.prime_five, by decide⟩
    · exact ⟨Nat.prime_seven, by decide⟩
    · exact ⟨primeThirteen, by decide⟩

/-- The prime factorization of `2` is the singleton factor at `2`. -/
private theorem factorization_two : Nat.factorization 2 = Finsupp.single 2 1 := by
  simpa only [pow_one] using
    (Nat.Prime.factorization_pow (p := 2) (k := 1) Nat.prime_two)

/-- The prime factorization of `12` is `2² * 3`. -/
private theorem factorization_twelve :
    Nat.factorization 12 = Finsupp.single 2 2 + Finsupp.single 3 1 := by
  rw [show 12 = 2 ^ 2 * 3 ^ 1 by norm_num only,
    Nat.factorization_mul (by norm_num only) (by norm_num only),
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.Prime.factorization_pow Nat.prime_three]

/-- The full APR-CL modulus at `t = 2` is `24`. -/
theorem modulus_two : modulus 2 = 24 := by
  rw [modulus, auxiliaryPrimes_two]
  have h2 : Nat.factorization 2 2 = 1 := by
    simp only [factorization_two, Finsupp.single_eq_same]
  have h3 : Nat.factorization 2 3 = 0 := by
    simp only [factorization_two, Finsupp.single_eq_of_ne (by decide : 3 ≠ 2)]
  simp only [Finset.mem_singleton, Nat.reduceEqDiff, not_false_eq_true,
    Finset.prod_insert, Finset.prod_singleton]
  norm_num only [h2, h3]

/-- The full APR-CL modulus at `t = 12` is `65520`. -/
theorem modulus_twelve : modulus 12 = 65520 := by
  rw [modulus, auxiliaryPrimes_twelve]
  have h2 : Nat.factorization 12 2 = 2 := by
    simp only [factorization_twelve, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : 2 ≠ 3),
      Nat.add_zero]
  have h3 : Nat.factorization 12 3 = 1 := by
    simp only [factorization_twelve, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : 3 ≠ 2),
      Nat.zero_add]
  have h5 : Nat.factorization 12 5 = 0 := by
    simp only [factorization_twelve, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_eq_of_ne (by decide : 5 ≠ 2),
      Finsupp.single_eq_of_ne (by decide : 5 ≠ 3), Nat.add_zero]
  have h7 : Nat.factorization 12 7 = 0 := by
    simp only [factorization_twelve, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_eq_of_ne (by decide : 7 ≠ 2),
      Finsupp.single_eq_of_ne (by decide : 7 ≠ 3), Nat.add_zero]
  have h13 : Nat.factorization 12 13 = 0 := by
    simp only [factorization_twelve, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_eq_of_ne (by decide : 13 ≠ 2),
      Finsupp.single_eq_of_ne (by decide : 13 ≠ 3), Nat.add_zero]
  simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
    not_false_eq_true, Finset.prod_insert, Finset.prod_singleton]
  norm_num only [h2, h3, h5, h7, h13]

/-- Every auxiliary prime-power block is a divisor of the full APR-CL modulus. -/
theorem auxiliaryPrimePower_dvd_modulus {t q : ℕ} (hq : q ∈ auxiliaryPrimes t) :
    q ^ (1 + Nat.factorization t q) ∣ modulus t := by
  unfold modulus
  exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hq) 2

/-- Every auxiliary prime itself divides the full APR-CL modulus. -/
theorem auxiliaryPrime_dvd_modulus {t q : ℕ} (hq : q ∈ auxiliaryPrimes t) :
  q ∣ modulus t := by
  apply dvd_trans (dvd_pow_self q (n := 1 + Nat.factorization t q)
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0)
      (Nat.le_add_right 1 _))))
  exact auxiliaryPrimePower_dvd_modulus hq

/-- Coprimality with the full APR-CL modulus implies coprimality with each
auxiliary prime. This supplies the coefficient-modulus condition for the
cyclotomic substitution denominator. -/
theorem auxiliaryPrime_coprime_left_of_modulus {t q n : ℕ}
    (hq : q ∈ auxiliaryPrimes t) (hn : Nat.Coprime n (modulus t)) :
    Nat.Coprime q n :=
  Nat.Coprime.of_dvd_left (auxiliaryPrime_dvd_modulus hq) hn.symm

/-- The leading factor `2` is always retained in the APR-CL modulus. -/
theorem two_dvd_modulus (t : ℕ) : 2 ∣ modulus t := by
  unfold modulus
  exact ⟨(auxiliaryPrimes t).prod (fun q => q ^ (1 + Nat.factorization t q)), rfl⟩

/-- The Euler exponent of an auxiliary prime-power block divides the parameter `t`. -/
theorem auxiliaryPrimePower_totient_dvd {t q : ℕ} (ht : t ≠ 0)
    (hq : q ∈ auxiliaryPrimes t) :
    (q ^ (1 + Nat.factorization t q)).totient ∣ t := by
  have hmem := (mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hq
  obtain ⟨hqprime, hqsub⟩ := hmem
  let v := Nat.factorization t q
  have hqp : q ^ v ∣ t :=
    (Nat.Prime.pow_dvd_iff_le_factorization hqprime ht).2 (by rfl)
  have hqcop : Nat.Coprime q (q - 1) := by
    apply hqprime.coprime_iff_not_dvd.mpr
    intro hdiv
    have hqge := hqprime.two_le
    have hpos : 0 < q - 1 :=
      Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hqge)
    have hle := Nat.le_of_dvd hpos hdiv
    have hqpos : 0 < q :=
      Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hqge)
    have hsub : q - 1 < q := Nat.sub_lt hqpos (Nat.lt_succ_self 0)
    exact Nat.not_le_of_gt hsub hle
  have hpowcop : Nat.Coprime (q ^ v) (q - 1) := Nat.Coprime.pow_left v hqcop
  have hprod : q ^ v * (q - 1) ∣ t :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hpowcop hqp hqsub
  rw [Nat.totient_prime_pow hqprime (Nat.add_pos_left (by decide : 0 < 1) v)]
  have hexp : 1 + v - 1 = v := Nat.add_sub_cancel_left 1 v
  rw [hexp]
  exact hprod

/-- A unit modulo an auxiliary prime is one modulo its prescribed prime-power block
after raising it to the APR-CL parameter `t`. -/
theorem pow_modEq_one_auxiliaryPrimePower {t q a : ℕ} (ht : t ≠ 0)
    (hq : q ∈ auxiliaryPrimes t) (ha : Nat.Coprime a q) :
    a ^ t ≡ 1 [MOD q ^ (1 + Nat.factorization t q)] := by
  let m := q ^ (1 + Nat.factorization t q)
  have ham : Nat.Coprime a m := by
    dsimp only [m]
    exact Nat.Coprime.pow_right _ ha
  have heuler : a ^ m.totient ≡ 1 [MOD m] := Nat.ModEq.pow_totient ham
  obtain ⟨k, hk⟩ := auxiliaryPrimePower_totient_dvd ht hq
  calc
    a ^ t = (a ^ m.totient) ^ k := by rw [hk, pow_mul]
    _ ≡ 1 ^ k [MOD m] := heuler.pow k
    _ = 1 := by simp only [one_pow]

/-- Congruences modulo coprime moduli combine into a congruence modulo their product.
Inputs are coprime moduli and two congruences with the same endpoints. The conclusion is the
corresponding congruence modulo the product; the proof combines the two divisibility statements.
This is the CRT interface used to assemble APR-CL's local unit periods. -/
theorem modEq_mul_of_coprime_moduli {m n a b : ℕ} (hmn : Nat.Coprime m n)
    (ha : Nat.ModEq m a b) (hb : Nat.ModEq n a b) : Nat.ModEq (m * n) a b := by
  rw [Nat.modEq_iff_dvd] at ha hb ⊢
  exact IsCoprime.mul_dvd (Nat.Coprime.cast hmn) ha hb

/-- Local congruences at distinct odd auxiliary prime-power blocks combine over their product.
The finite set is a subset of the APR-CL auxiliary primes other than two. -/
theorem modEq_auxiliaryPrimePowerProduct_of_local {t a b : ℕ} (ht : t ≠ 0)
    (S : Finset ℕ) (hS : S ⊆ (auxiliaryPrimes t).erase 2)
    (hlocal : ∀ q ∈ S, Nat.ModEq (q ^ (1 + Nat.factorization t q)) a b) :
    Nat.ModEq (S.prod (fun q => q ^ (1 + Nat.factorization t q))) a b := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Nat.ModEq, Nat.mod_one]
  | @insert q S hqnot ih =>
    have hS' : S ⊆ (auxiliaryPrimes t).erase 2 := by
      intro r hr
      exact hS (Finset.mem_insert_of_mem hr)
    have hlocal' : ∀ r ∈ S,
        Nat.ModEq (r ^ (1 + Nat.factorization t r)) a b := by
      intro r hr
      exact hlocal r (Finset.mem_insert_of_mem hr)
    have hprev := ih hS' hlocal'
    have hqerase : q ∈ (auxiliaryPrimes t).erase 2 :=
      hS (Finset.mem_insert_self q S)
    have hqmem : q ∈ auxiliaryPrimes t := (Finset.mem_erase.mp hqerase).2
    have hqprime := (mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hqmem |>.1
    have hblockscoprime :
        (q ^ (1 + Nat.factorization t q)).Coprime
          (S.prod (fun r => r ^ (1 + Nat.factorization t r))) := by
      apply Nat.Coprime.prod_right
      intro r hr
      have hrErase : r ∈ (auxiliaryPrimes t).erase 2 := hS' hr
      have hrmem : r ∈ auxiliaryPrimes t := (Finset.mem_erase.mp hrErase).2
      have hrprime := (mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hrmem |>.1
      have hqrne : q ≠ r := by
        intro hqr
        subst r
        exact hqnot hr
      have hqr : Nat.Coprime q r := by
        apply hqprime.coprime_iff_not_dvd.mpr
        intro hdiv
        have hqNeOne : q ≠ 1 := Nat.ne_of_gt hqprime.two_le
        have heq : r = q := (Nat.Prime.dvd_iff_eq hrprime hqNeOne).mp hdiv
        exact hqrne heq.symm
      exact (Nat.Coprime.pow_left _ hqr).pow_right _
    have hcombined := modEq_mul_of_coprime_moduli hblockscoprime
      (hlocal q (Finset.mem_insert_self q S)) hprev
    simpa only [Finset.prod_insert hqnot] using hcombined

/-- Local auxiliary-prime-power periods combine across any finite set of distinct
odd auxiliary primes. Inputs are a positive parameter, a finite subset of `Q(t) \ {2}`, and
coprimality of the base with every indexed prime. The conclusion gives period `t` modulo the
product of the selected blocks. Distinctness follows from primality; CRT combines the local
Euler periods. This is the odd-part consumer for the full APR-CL modulus theorem. -/
theorem pow_modEq_one_auxiliaryPrimePowerProduct {t a : ℕ} (ht : t ≠ 0)
    (S : Finset ℕ) (hS : S ⊆ (auxiliaryPrimes t).erase 2)
    (ha : ∀ q ∈ S, Nat.Coprime a q) :
    Nat.ModEq (S.prod (fun q => q ^ (1 + Nat.factorization t q))) (a ^ t) 1 := by
  apply modEq_auxiliaryPrimePowerProduct_of_local ht S hS
  intro q hq
  have hqmem : q ∈ auxiliaryPrimes t := (Finset.mem_erase.mp (hS hq)).2
  exact pow_modEq_one_auxiliaryPrimePower ht hqmem (ha q hq)

/-- The modulus separates into its complete 2-primary block and the product of
the odd auxiliary-prime-power blocks. For positive `t`, the result identifies the exact modulus
factors; `two_mem_auxiliaryPrimes` inserts the `q = 2` block and exponent arithmetic absorbs the
leading factor 2. This decomposition is used by the global CRT period proof. -/
theorem modulus_eq_twoPrimary_mul_oddAuxiliaryPrimePowerProduct {t : ℕ}
    (ht : t ≠ 0) :
    modulus t = 2 ^ (2 + Nat.factorization t 2) *
      ((auxiliaryPrimes t).erase 2).prod
        (fun q => q ^ (1 + Nat.factorization t q)) := by
  have htwo := two_mem_auxiliaryPrimes ht
  have hnot : 2 ∉ (auxiliaryPrimes t).erase 2 := by
    intro hmem
    exact (Finset.mem_erase.mp hmem).1 rfl
  have hprod :
      (auxiliaryPrimes t).prod (fun q => q ^ (1 + Nat.factorization t q)) =
        2 ^ (1 + Nat.factorization t 2) *
          ((auxiliaryPrimes t).erase 2).prod
            (fun q => q ^ (1 + Nat.factorization t q)) := by
    calc
      _ = (insert 2 ((auxiliaryPrimes t).erase 2)).prod
          (fun q => q ^ (1 + Nat.factorization t q)) := by
            rw [Finset.insert_erase htwo]
      _ = 2 ^ (1 + Nat.factorization t 2) *
          ((auxiliaryPrimes t).erase 2).prod
            (fun q => q ^ (1 + Nat.factorization t q)) := by
            rw [Finset.prod_insert hnot]
  rw [modulus, hprod]
  have hpow : 2 * 2 ^ (1 + Nat.factorization t 2) =
      2 ^ (2 + Nat.factorization t 2) := by
    rw [show 1 + Nat.factorization t 2 = Nat.factorization t 2 + 1 by
        exact Nat.add_comm 1 _,
      pow_succ, show 2 + Nat.factorization t 2 = Nat.factorization t 2 + 2 by
        exact Nat.add_comm 2 _,
      pow_add]
    norm_num only
    ring
  rw [← Nat.mul_assoc, hpow]

/-- Congruences on the full two-primary block and every odd auxiliary block determine
congruence modulo the complete APR-CL modulus. This is the local-to-global A6 interface. -/
theorem modEq_modulus_of_local {t a b : ℕ} (ht : t ≠ 0)
    (htwo : Nat.ModEq (2 ^ (2 + Nat.factorization t 2)) a b)
    (hodd : ∀ q ∈ (auxiliaryPrimes t).erase 2,
      Nat.ModEq (q ^ (1 + Nat.factorization t q)) a b) :
    Nat.ModEq (modulus t) a b := by
  have hoddBlocks :
      Nat.ModEq (((auxiliaryPrimes t).erase 2).prod
        (fun q => q ^ (1 + Nat.factorization t q))) a b :=
    modEq_auxiliaryPrimePowerProduct_of_local ht
      ((auxiliaryPrimes t).erase 2) (by
        intro q hq
        exact hq) hodd
  have hcop :
      Nat.Coprime (2 ^ (2 + Nat.factorization t 2))
        (((auxiliaryPrimes t).erase 2).prod
          (fun q => q ^ (1 + Nat.factorization t q))) := by
    apply Nat.Coprime.prod_right
    intro q hq
    have hqmem : q ∈ auxiliaryPrimes t := (Finset.mem_erase.mp hq).2
    have hqne2 : q ≠ 2 := (Finset.mem_erase.mp hq).1
    have hqprime := (mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hqmem |>.1
    have h2q : Nat.Coprime 2 q := by
      rw [Nat.prime_two.coprime_iff_not_dvd]
      intro hdiv
      have hqeq : q = 2 :=
        (Nat.Prime.dvd_iff_eq hqprime (by decide : 2 ≠ 1)).mp hdiv
      exact hqne2 hqeq
    exact (Nat.Coprime.pow_left _ h2q).pow_right _
  have hcombined := modEq_mul_of_coprime_moduli hcop htwo hoddBlocks
  rw [modulus_eq_twoPrimary_mul_oddAuxiliaryPrimePowerProduct ht]
  exact hcombined

/-- Congruence modulo the APR-CL modulus is equivalent to simultaneous congruence
on its two-primary block and every odd auxiliary-prime-power block. The forward
direction restricts the modulus; the reverse direction combines coprime blocks.
This is the exact local/global interface for prime-factor orbit conditions. -/
theorem modEq_modulus_iff_local {t a b : ℕ} (ht : t ≠ 0) :
    Nat.ModEq (modulus t) a b ↔
      Nat.ModEq (2 ^ (2 + Nat.factorization t 2)) a b ∧
      ∀ q ∈ (auxiliaryPrimes t).erase 2,
        Nat.ModEq (q ^ (1 + Nat.factorization t q)) a b := by
  constructor
  · intro hfull
    have hmod := modulus_eq_twoPrimary_mul_oddAuxiliaryPrimePowerProduct ht
    constructor
    · apply Nat.ModEq.of_dvd _ hfull
      exact ⟨_, hmod⟩
    · intro q hq
      have hqprod : q ^ (1 + Nat.factorization t q) ∣
          ((auxiliaryPrimes t).erase 2).prod
            (fun r => r ^ (1 + Nat.factorization t r)) :=
        Finset.dvd_prod_of_mem _ hq
      obtain ⟨k, hk⟩ := hqprod
      apply Nat.ModEq.of_dvd _ hfull
      refine ⟨2 ^ (2 + Nat.factorization t 2) * k, ?_⟩
      rw [hmod, hk]
      ac_rfl
  · rintro ⟨htwo, hodd⟩
    exact modEq_modulus_of_local ht htwo hodd

/-- Given one target residue for each prime divisor of a nonzero parameter,
the finite Chinese remainder theorem chooses a single exponent `i < t` with
those residues modulo the full prime-power factors of `t`. The input function
records the local exponents; the result is used by the APR-CL orbit assembly. -/
theorem exists_commonExponent_mod_primePowers {t : ℕ} (ht : t ≠ 0)
    (a : ℕ → ℕ) :
    ∃ i, i < t ∧ ∀ p ∈ t.primeFactors,
      Nat.ModEq (p ^ Nat.factorization t p) i (a p) := by
  have hnz : ∀ p ∈ t.primeFactors, p ^ Nat.factorization t p ≠ 0 := by
    intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hpair : (↑t.primeFactors : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime (fun p => p ^ Nat.factorization t p)) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  let i := Nat.chineseRemainderOfFinset a
    (fun p => p ^ Nat.factorization t p) t.primeFactors hnz hpair
  refine ⟨i, ?_, ?_⟩
  · calc
      (i : ℕ) < ∏ p ∈ t.primeFactors, p ^ Nat.factorization t p :=
        Nat.chineseRemainderOfFinset_lt_prod a
          (fun p => p ^ Nat.factorization t p) hnz hpair
      _ = t := (Nat.prod_primeFactors_pow_factorization ht).symm
  · intro p hp
    exact i.property p hp

/-- Squaring a residue congruent to one modulo an even modulus doubles the modulus. -/
theorem modEq_square_double_of_even_modulus {m x : ℕ} (hm : Even m)
    (hxm : Nat.ModEq m x 1) : Nat.ModEq (2 * m) (x ^ 2) 1 := by
  rcases hm with ⟨j, hj⟩
  by_cases hj0 : j = 0
  · subst j
    have hm0 : m = 0 := by exact hj
    subst m
    simp only [Nat.ModEq] at hxm ⊢
    simp only [Nat.zero_add, Nat.mul_zero, Nat.mod_zero] at hxm ⊢
    rw [hxm]
    exact one_pow 2
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hjle : 1 ≤ j := Nat.succ_le_iff.mpr hjpos
    have hsum : 1 + 1 ≤ j + j := Nat.add_le_add hjle hjle
    have hmpos : 1 < j + j := Nat.lt_of_lt_of_le (by decide) hsum
    rw [hj] at hxm ⊢
    simp only [Nat.ModEq] at hxm ⊢
    have hxmod : x % (j + j) = 1 := by
      simpa only [Nat.mod_eq_of_lt hmpos] using hxm
    have hx : x = (j + j) * (x / (j + j)) + 1 := by
      have hdecomp := Nat.mod_add_div x (j + j)
      rw [hxmod] at hdecomp
      exact hdecomp.symm.trans (Nat.add_comm _ _)
    rw [hx]
    have hpow : ((j + j) * (x / (j + j)) + 1) ^ 2 =
        2 * (j + j) * (j * (x / (j + j)) ^ 2 + x / (j + j)) + 1 := by
      ring
    rw [hpow]
    rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]

/-- Every odd natural number has square congruent to one modulo eight. This is the
base case for the extra 2-adic modulus factor in `e(t)`. -/
theorem odd_square_modEq_eight {a : ℕ} (ha : Odd a) :
    Nat.ModEq 8 (a ^ 2) 1 := by
  rcases ha with ⟨k, hk⟩
  rw [hk]
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [hm]
    change (2 * (m + m) + 1) ^ 2 % 8 = 1
    have h : (2 * (m + m) + 1) ^ 2 = 8 * (2 * m ^ 2 + m) + 1 := by ring
    rw [h]
    rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
  · rw [hm]
    change (2 * (2 * m + 1) + 1) ^ 2 % 8 = 1
    have h : (2 * (2 * m + 1) + 1) ^ 2 = 8 * (2 * m ^ 2 + 3 * m + 1) + 1 := by ring
    rw [h]
    rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]

/-- Repeated squaring gives the exact 2-primary unit exponent for every positive
valuation: an odd base satisfies `a^(2^v) = 1` modulo `2^(v+2)` for `v ≥ 1`. -/
theorem odd_pow_two_modEq_one {a v : ℕ} (ha : Odd a) (hv : 1 ≤ v) :
    Nat.ModEq (2 ^ (v + 2)) (a ^ (2 ^ v)) 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) hv))
  induction k with
  | zero =>
      change Nat.ModEq 8 (a ^ 2) 1
      exact odd_square_modEq_eight ha
  | succ k ih =>
      have hEven : Even (2 ^ (k + 3)) := by
        refine ⟨2 ^ (k + 2), ?_⟩
        rw [pow_succ]
        rw [Nat.mul_two]
      have hstep := modEq_square_double_of_even_modulus hEven
        (ih (Nat.zero_lt_succ k))
      convert hstep using 1
      · simp only [pow_succ, Nat.mul_assoc]
        calc
          _ = (2 ^ k * 2) * (2 * (2 * 2)) := by rw [Nat.mul_assoc]
          _ = (2 * 2 ^ k) * (2 * (2 * 2)) := by rw [Nat.mul_comm (2 ^ k) 2]
          _ = 2 * (2 ^ k * (2 * (2 * 2))) := by rw [Nat.mul_assoc]
      · calc
          a ^ (2 ^ (k + 1).succ) = a ^ (2 ^ k.succ * 2) := by rw [Nat.pow_succ]
          _ = (a ^ (2 ^ k.succ)) ^ 2 := Nat.pow_mul a (2 ^ k.succ) 2

/-- An odd base raised to any positive parameter `t` is one modulo the full
2-primary block of `e(t)`, whose exponent is `2 + v₂(t)`. -/
theorem pow_modEq_one_twoPrimaryBlock {t a : ℕ} (ht : t ≠ 0)
    (hv : 0 < Nat.factorization t 2) (ha : Odd a) :
    Nat.ModEq (2 ^ (2 + Nat.factorization t 2)) (a ^ t) 1 := by
  obtain ⟨v, hvEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hv)
  have hdiv : 2 ^ v.succ ∣ t := by
    apply (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two ht).2
    rw [hvEq]
  obtain ⟨k, hk⟩ := hdiv
  have hlocal := odd_pow_two_modEq_one ha
    (Nat.succ_le_iff.mpr (Nat.zero_lt_succ v))
  rw [hvEq]
  calc
    a ^ t = (a ^ (2 ^ v.succ)) ^ k := by rw [hk, pow_mul]
    _ ≡ 1 ^ k [MOD 2 ^ (2 + v.succ)] := by
      simpa only [Nat.add_comm] using hlocal.pow k
    _ = 1 := by exact one_pow k

/-- If `v₂(t) = 1`, an odd base has its `t`-th power equal to one modulo
the full 2-primary block `2^(2 + v₂(t)) = 8`. -/
theorem pow_modEq_one_twoBlock_of_factorization_eq_one {t a : ℕ}
    (ht : t ≠ 0) (hv : Nat.factorization t 2 = 1) (ha : Odd a) :
    Nat.ModEq 8 (a ^ t) 1 := by
  have hmain := pow_modEq_one_twoPrimaryBlock ht (by rw [hv]; norm_num only) ha
  simpa only [hv, Nat.reduceAdd, Nat.reducePow] using hmain

/-- A unit raised to a positive even parameter is one modulo the full APR-CL modulus.
Inputs are `t > 0`, positive 2-adic valuation, and a base coprime to `e(t)`. The conclusion is
the period congruence modulo `e(t)`. Coprimality gives an odd base and local units; the 2-primary
lemma and finite odd-block product are combined by CRT. This is the unit-period interface for A1. -/
theorem pow_modEq_one_modulus_of_factorization_pos {t a : ℕ} (ht : t ≠ 0)
    (hv : 0 < Nat.factorization t 2) (ha : Nat.Coprime a (modulus t)) :
    Nat.ModEq (modulus t) (a ^ t) 1 := by
  have hodd : Odd a := Nat.Coprime.odd_of_right
    (Nat.Coprime.of_dvd_right (two_dvd_modulus t) ha)
  have htwo := pow_modEq_one_twoPrimaryBlock ht hv hodd
  have hoddBlocks := pow_modEq_one_auxiliaryPrimePowerProduct ht
    ((auxiliaryPrimes t).erase 2) (by
      intro q hq
      exact hq) (by
      intro q hq
      have hqmem : q ∈ auxiliaryPrimes t := (Finset.mem_erase.mp hq).2
      exact Nat.Coprime.of_dvd_right (auxiliaryPrime_dvd_modulus hqmem) ha)
  have hcop :
      Nat.Coprime (2 ^ (2 + Nat.factorization t 2))
        (((auxiliaryPrimes t).erase 2).prod
          (fun q => q ^ (1 + Nat.factorization t q))) := by
    apply Nat.Coprime.prod_right
    intro q hq
    have hqmem : q ∈ auxiliaryPrimes t := (Finset.mem_erase.mp hq).2
    have hqne2 : q ≠ 2 := (Finset.mem_erase.mp hq).1
    have hqprime := (mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hqmem |>.1
    have h2q : Nat.Coprime 2 q := by
      rw [Nat.prime_two.coprime_iff_not_dvd]
      intro hdiv
      have hqeq : q = 2 :=
        (Nat.Prime.dvd_iff_eq hqprime (by decide : 2 ≠ 1)).mp hdiv
      exact hqne2 hqeq
    exact (Nat.Coprime.pow_left _ h2q).pow_right _
  have hcombined := modEq_mul_of_coprime_moduli hcop htwo hoddBlocks
  rw [modulus_eq_twoPrimary_mul_oddAuxiliaryPrimePowerProduct ht]
  exact hcombined

/-- For every positive even APR-CL parameter, each unit raised to the parameter is
one modulo the full modulus `e(t)`. Evenness supplies a factor `2` in `t`, hence positive
2-adic valuation; the preceding CRT theorem then gives the conclusion. This is the public
even-parameter form of the APR-CL unit-period result. -/
theorem pow_modEq_one_modulus_of_even {t a : ℕ} (ht : t ≠ 0) (heven : Even t)
    (ha : Nat.Coprime a (modulus t)) : Nat.ModEq (modulus t) (a ^ t) 1 := by
  have hdiv : 2 ∣ t := by
    rcases heven with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    exact hk.trans (Nat.two_mul k).symm
  have hpow : 2 ^ 1 ∣ t := by simpa only [Nat.reducePow] using hdiv
  have hvle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two ht).mp hpow
  exact pow_modEq_one_modulus_of_factorization_pos ht
    (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) hvle) ha

end PseudoPrime.PrimeTest.APRCL
