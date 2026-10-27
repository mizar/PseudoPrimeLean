/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Finset.NatDivisors
public import PseudoPrime.AnalyticNumberTheory.AGP.SeedModulus

/-! # ExceptionalModuli

Finite removal of prime factors that make auxiliary divisors exceptional.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Select the smallest prime factor of each exceptional modulus that divides
`L`. These selected factors are the factors removed from `L` in the finite
exception-avoidance argument of paper95, Theorem 3.1.
-/
def selectedExceptionalPrimeFactors (L : ℕ) (E : Finset ℕ) : Finset ℕ :=
  (E.filter (fun e => e ∣ L)).image Nat.minFac

/--
The selected smallest prime factors belong to the prime-factor set of `L`.
Each selected value is prime and divides an exceptional modulus dividing `L`.
-/
theorem selectedExceptionalPrimeFactors_subset (L : ℕ) (E : Finset ℕ) (hL : L ≠ 0)
    (hE : ∀ e ∈ E, 1 < e) : selectedExceptionalPrimeFactors L E ⊆ L.primeFactors := by
  intro p hp
  unfold selectedExceptionalPrimeFactors at hp
  rcases Finset.mem_image.mp hp with ⟨e, he, rfl⟩
  simp only [Finset.mem_filter] at he
  have hprime : Nat.Prime (Nat.minFac e) := Nat.minFac_prime (Nat.ne_of_gt (hE e he.1))
  have hdiv : Nat.minFac e ∣ e := Nat.minFac_dvd e
  exact Nat.mem_primeFactors.mpr ⟨hprime, dvd_trans hdiv he.2, hL⟩

/--
The selected exceptional prime factors are no more numerous than the exceptional
moduli. Repeated choices may remove the same prime factor, so this is an upper
bound that includes possible overlap.
-/
theorem selectedExceptionalPrimeFactors_card_le (L : ℕ) (E : Finset ℕ) :
    (selectedExceptionalPrimeFactors L E).card ≤ E.card := by
  unfold selectedExceptionalPrimeFactors
  exact (Finset.card_image_le).trans (Finset.card_filter_le _ _)

/--
Purpose: list prime factors of an exceptional modulus that divide `L` but do
not divide the fixed progression modulus `m`.

Definition: this is the prime-factor set of `e` filtered by `q ∣ L` and
`q ∤ m`.

Role: any such factor is forced into the divisor variable when `e ∣ d * m`
and `d` is coprime to `m`.
-/
def exceptionalPrimeFactorsOutsideModulus (L m e : ℕ) : Finset ℕ :=
  e.primeFactors.filter (fun q => q ∣ L ∧ ¬q ∣ m)

/--
Purpose: choose one prime factor of `e` that divides `L` and avoids `m`.

Definition: take the least element of `exceptionalPrimeFactorsOutsideModulus`
when that set is nonempty, and use zero otherwise.

Role: the chosen factor is the single factor removed for this exceptional
modulus, so the number of removed factors is bounded by the number of moduli.
-/
noncomputable def selectedPrimeFactorOutsideModulus (L m e : ℕ) : ℕ :=
  if h : (exceptionalPrimeFactorsOutsideModulus L m e).Nonempty then
    (exceptionalPrimeFactorsOutsideModulus L m e).min' h
  else 0

/--
Purpose: select at most one exceptional prime factor for each `e ∈ E` that
can divide `L` without dividing the fixed modulus `m`.

Definition: take the image of the exceptional moduli with a nonempty eligible
prime-factor set under `selectedPrimeFactorOutsideModulus`.

Role: this is the set removed from `L` to avoid exceptional divisors of `d*m`.
-/
noncomputable def selectedExceptionalPrimeFactorsForModulus (L : ℕ) (E : Finset ℕ) (m : ℕ) :
    Finset ℕ :=
  (E.filter (fun e => (exceptionalPrimeFactorsOutsideModulus L m e).Nonempty)).image
    (selectedPrimeFactorOutsideModulus L m)

/--
Inputs: a nonempty eligible prime-factor set for `e`.

Claim: the selected factor belongs to that set.

Role: this exposes the divisibility, primality, and coprimality properties of
each selected factor.
-/
theorem selectedPrimeFactorOutsideModulus_mem (L m e : ℕ)
    (h : (exceptionalPrimeFactorsOutsideModulus L m e).Nonempty) :
    selectedPrimeFactorOutsideModulus L m e ∈ exceptionalPrimeFactorsOutsideModulus L m e := by
  unfold selectedPrimeFactorOutsideModulus
  rw [dite_eq_left h]
  exact Finset.min'_mem _ h

/-- The number of selected factors is at most the number of exceptional moduli. -/
theorem selectedExceptionalPrimeFactorsForModulus_card_le (L : ℕ) (E : Finset ℕ) (m : ℕ) :
    (selectedExceptionalPrimeFactorsForModulus L E m).card ≤ E.card := by
  unfold selectedExceptionalPrimeFactorsForModulus
  exact (Finset.card_image_le).trans (Finset.card_filter_le _ _)

/--
The selected factors for the fixed modulus belong to `L.primeFactors` and do
not divide `m`.
-/
theorem selectedExceptionalPrimeFactorsForModulus_properties (L : ℕ) (E : Finset ℕ) (m : ℕ)
    (hL : L ≠ 0) :
    selectedExceptionalPrimeFactorsForModulus L E m ⊆ L.primeFactors ∧
      (∀ q ∈ selectedExceptionalPrimeFactorsForModulus L E m, Nat.Prime q) ∧
      ∀ q ∈ selectedExceptionalPrimeFactorsForModulus L E m, ¬q ∣ m := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    unfold selectedExceptionalPrimeFactorsForModulus at hq
    rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
    have hF : (exceptionalPrimeFactorsOutsideModulus L m e).Nonempty := (Finset.mem_filter.mp he).2
    have hqF := selectedPrimeFactorOutsideModulus_mem L m e hF
    have hqmem := Finset.mem_filter.mp hqF
    exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hqmem.1).1, hqmem.2.1, hL⟩
  · intro q hq
    unfold selectedExceptionalPrimeFactorsForModulus at hq
    rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
    have hF : (exceptionalPrimeFactorsOutsideModulus L m e).Nonempty := (Finset.mem_filter.mp he).2
    have hqF := selectedPrimeFactorOutsideModulus_mem L m e hF
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hqF).1).1
  · intro q hq
    unfold selectedExceptionalPrimeFactorsForModulus at hq
    rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
    have hF : (exceptionalPrimeFactorsOutsideModulus L m e).Nonempty := (Finset.mem_filter.mp he).2
    have hqF := selectedPrimeFactorOutsideModulus_mem L m e hF
    exact (Finset.mem_filter.mp hqF).2.2

/--
The selected prime factors form a valid exceptional-modulus set for the
existing divisor-removal construction.
-/
theorem selectedExceptionalPrimeFactorsForModulus_fixed (L : ℕ) (E : Finset ℕ) (m : ℕ)
    (hL : L ≠ 0) :
    selectedExceptionalPrimeFactors L (selectedExceptionalPrimeFactorsForModulus L E m) =
      selectedExceptionalPrimeFactorsForModulus L E m := by
  let Q := selectedExceptionalPrimeFactorsForModulus L E m
  have hQsubset : Q ⊆ L.primeFactors :=
    (selectedExceptionalPrimeFactorsForModulus_properties L E m hL).1
  have hQprime : ∀ q ∈ Q, Nat.Prime q :=
    (selectedExceptionalPrimeFactorsForModulus_properties L E m hL).2.1
  ext q
  constructor
  · intro hq
    unfold selectedExceptionalPrimeFactors at hq
    rcases Finset.mem_image.mp hq with ⟨e, he, hqe⟩
    have he' := Finset.mem_filter.mp he
    have heL := (Nat.mem_primeFactors.mp (hQsubset he'.1)).2.1
    have hePrime := hQprime e he'.1
    have hminPrime := Nat.minFac_prime (Nat.ne_of_gt hePrime.one_lt)
    have hminDvd := Nat.minFac_dvd e
    rcases hePrime.eq_one_or_self_of_dvd (Nat.minFac e) hminDvd with hminOne | hminEq
    · exact False.elim (Nat.ne_of_gt hminPrime.one_lt hminOne)
    · rw [hminEq] at hqe
      exact hqe ▸ he'.1
  · intro hq
    have hqL := (Nat.mem_primeFactors.mp (hQsubset hq)).2.1
    have hqPrime := hQprime q hq
    have hminPrime := Nat.minFac_prime (Nat.ne_of_gt hqPrime.one_lt)
    have hminDvd := Nat.minFac_dvd q
    rcases hqPrime.eq_one_or_self_of_dvd (Nat.minFac q) hminDvd with hminOne | hminEq
    · exact False.elim (Nat.ne_of_gt hminPrime.one_lt hminOne)
    · unfold selectedExceptionalPrimeFactors
      apply Finset.mem_image.mpr
      refine ⟨q, Finset.mem_filter.mpr ⟨hq, hqL⟩, ?_⟩
      exact hminEq

/--
If a prime divisor of `e` does not divide `m`, then `e ∣ d * m` forces it to
divide `d`.
-/
theorem prime_factor_dvd_left_of_exceptional_dvd_mul (e d m q : ℕ) (hq : q ∈ e.primeFactors)
    (he : e ∣ d * m) (hq_not_m : ¬q ∣ m) : q ∣ d := by
  have hqPrime := (Nat.mem_primeFactors.mp hq).1
  have hqe := (Nat.mem_primeFactors.mp hq).2.1
  have hqdm : q ∣ d * m := dvd_trans hqe he
  rcases hqPrime.dvd_mul.mp hqdm with hqd | hqm
  · exact hqd
  · exact False.elim (hq_not_m hqm)

/--
Inputs: `d ∣ L`, `Nat.Coprime d m`, an exceptional modulus `e > 1`,
`e ∣ d * m`, and `e ∤ m`.

Claim: `e` has a prime factor that divides `L` but not `m`.

Proof: if no such factor existed, every prime factor of `e` would divide `m`.
Then `e` would be coprime to `d`, and `e ∣ d * m` would imply `e ∣ m`.

Role: this supplies the factor removed from `L` when the progression modulus
includes the fixed multiplier `m`.
-/
theorem exists_prime_factor_outside_modulus_of_dvd_mul (e d m L : ℕ) (hdL : d ∣ L)
    (hdm : Nat.Coprime d m) (hegt : 1 < e) (he : e ∣ d * m) (hne : ¬e ∣ m) :
    (exceptionalPrimeFactorsOutsideModulus L m e).Nonempty := by
  by_contra hEmpty
  have hepos : 0 < e := lt_trans (by norm_num only) hegt
  have hcop : Nat.Coprime e d :=
    Nat.coprime_of_dvd
      (by
        intro q hqPrime hqe
        by_cases hqm : q ∣ m
        · exact fun hqd => by
            have hqgcd : q ∣ Nat.gcd d m := Nat.dvd_gcd hqd hqm
            rw [hdm.gcd_eq_one] at hqgcd
            exact hqPrime.not_dvd_one hqgcd
        · have hq : q ∈ e.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hqPrime, hqe, Nat.ne_of_gt hepos⟩
          have hqd := prime_factor_dvd_left_of_exceptional_dvd_mul e d m q hq he hqm
          have hqL := dvd_trans hqd hdL
          have hqmem : q ∈ exceptionalPrimeFactorsOutsideModulus L m e :=
            Finset.mem_filter.mpr ⟨hq, hqL, hqm⟩
          exact False.elim (hEmpty ⟨q, hqmem⟩))
  have hem : e ∣ m := (Nat.Coprime.dvd_mul_left hcop).mp he
  exact hne hem

/--
Remove the selected exceptional prime factors from the squarefree factor set of
`L`, and take the product of the remaining primes.
-/
def exceptionalFreePart (L : ℕ) (E : Finset ℕ) : ℕ :=
  (L.primeFactors \ selectedExceptionalPrimeFactors L E).prod id

open PseudoPrime.NumberTheory.PrimeProducts in
/--
The exceptional-free part is squarefree, divides `L`, and is divisible by no
member of `E` greater than one. Its prime factors are exactly those left after
the selected factors are removed.
-/
theorem exceptionalFreePart_properties (L : ℕ) (E : Finset ℕ) (hL : L ≠ 0)
    (hSquarefree : Squarefree L) (hE : ∀ e ∈ E, 1 < e) :
    Squarefree (exceptionalFreePart L E) ∧
      (exceptionalFreePart L E).primeFactors =
        L.primeFactors \ selectedExceptionalPrimeFactors L E ∧
      exceptionalFreePart L E ∣ L ∧ ∀ e ∈ E, ¬e ∣ exceptionalFreePart L E := by
  let P := L.primeFactors \ selectedExceptionalPrimeFactors L E
  have hprimeP : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact (Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp hp).1).1
  have hprod := squarefree_prime_product_primeFactors P hprimeP
  have hPsubset : P ⊆ L.primeFactors := Finset.sdiff_subset
  have hQsubset : selectedExceptionalPrimeFactors L E ⊆ L.primeFactors :=
    selectedExceptionalPrimeFactors_subset L E hL hE
  have hLprod : L.primeFactors.prod id = L := by
    change (∏ p ∈ L.primeFactors, p) = L
    exact Nat.prod_primeFactors_of_squarefree hSquarefree
  have hdivProd : P.prod id ∣ L.primeFactors.prod id :=
    Finset.prod_dvd_prod_of_subset P L.primeFactors id hPsubset
  have hdivL : P.prod id ∣ L := by
    rw [← hLprod]
    exact hdivProd
  change
    Squarefree (P.prod id) ∧ (P.prod id).primeFactors = P ∧ P.prod id ∣ L ∧ ∀ e ∈ E, ¬e ∣ P.prod id
  refine ⟨hprod.1, hprod.2, hdivL, ?_⟩
  intro e he hediv
  have heL : e ∣ L := dvd_trans hediv hdivL
  let q := Nat.minFac e
  have hqPrime : Nat.Prime q := Nat.minFac_prime (Nat.ne_of_gt (hE e he))
  have hqE : q ∈ selectedExceptionalPrimeFactors L E := by
    unfold selectedExceptionalPrimeFactors
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨he, heL⟩, rfl⟩
  have hqProd : q ∣ P.prod id := dvd_trans (Nat.minFac_dvd e) hediv
  obtain ⟨p, hp, hqp⟩ :=
    (Prime.dvd_finsetProd_iff ((Nat.prime_iff).mp hqPrime) (fun p : ℕ => p)).mp hqProd
  rcases (hprimeP p hp).eq_one_or_self_of_dvd q hqp with hqOne | hqpEq
  · exact (Nat.ne_of_gt hqPrime.one_lt) hqOne
  · exact (Finset.mem_sdiff.mp hp).2 (hqpEq ▸ hqE)

/--
Removing the selected prime factors loses at most one distinct prime factor
per exceptional modulus. This is the factor-count estimate used for the
`2 ^ (-D_B)` loss in paper95, equation (3.1).
-/
theorem exceptionalFreePart_primeFactors_card_lower_bound (L : ℕ) (E : Finset ℕ) (hL : L ≠ 0)
    (hSquarefree : Squarefree L) (hE : ∀ e ∈ E, 1 < e) :
    L.primeFactors.card ≤ (exceptionalFreePart L E).primeFactors.card + E.card := by
  have hQsubset := selectedExceptionalPrimeFactors_subset L E hL hE
  have hQcard := selectedExceptionalPrimeFactors_card_le L E
  have hcard := Finset.card_sdiff_add_card_eq_card hQsubset
  have hfactor := (exceptionalFreePart_properties L E hL hSquarefree hE).2.1
  rw [← hfactor] at hcard
  omega

/--
The full squarefree divisor count decreases by at most a factor of
`2 ^ E.card` after exceptional factors are removed. This is the unrestricted
divisor-count form of the loss in paper95, equation (3.1).
-/
theorem two_pow_primeFactors_card_le_exceptional_loss_mul (L : ℕ) (E : Finset ℕ) (hL : L ≠ 0)
    (hSquarefree : Squarefree L) (hE : ∀ e ∈ E, 1 < e) :
    2 ^ L.primeFactors.card ≤ 2 ^ E.card * 2 ^ (exceptionalFreePart L E).primeFactors.card := by
  have hcount := exceptionalFreePart_primeFactors_card_lower_bound L E hL hSquarefree hE
  calc
    2 ^ L.primeFactors.card ≤ 2 ^ ((exceptionalFreePart L E).primeFactors.card + E.card) :=
      Nat.pow_le_pow_right (by norm_num only) hcount
    _ = 2 ^ (exceptionalFreePart L E).primeFactors.card * 2 ^ E.card := by rw [Nat.pow_add]
    _ = 2 ^ E.card * 2 ^ (exceptionalFreePart L E).primeFactors.card := Nat.mul_comm _ _

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Among the divisors below any cutoff, removing the selected exceptional factors
loses at most a factor of `2 ^ E.card`. Project a divisor to its remaining
factor in `exceptionalFreePart L E`; each fiber is controlled by a divisor of
the removed prime product.
-/
theorem restrictedDivisors_card_le_exceptional_loss (L : ℕ) (E : Finset ℕ) (y : ℕ) (hL : L ≠ 0)
    (hSquarefree : Squarefree L) (hE : ∀ e ∈ E, 1 < e) :
    (restrictedDivisors L y).card ≤
      2 ^ E.card * (restrictedDivisors (exceptionalFreePart L E) y).card := by
  let Q := selectedExceptionalPrimeFactors L E
  let R := Q.prod id
  have hQsubset : Q ⊆ L.primeFactors := selectedExceptionalPrimeFactors_subset L E hL hE
  have hQprime : ∀ q ∈ Q, Nat.Prime q := by
    intro q hq
    exact (Nat.mem_primeFactors.mp (hQsubset hq)).1
  have hRprod := squarefree_prime_product_primeFactors Q hQprime
  have hRpos : 0 < R := by
    change 0 < Q.prod id
    apply Finset.prod_pos
    intro q hq
    exact (hQprime q hq).pos
  let L' := exceptionalFreePart L E
  have hL'pos : 0 < L' := by
    change 0 < (L.primeFactors \ Q).prod id
    apply Finset.prod_pos
    intro p hp
    exact ((Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp hp).1).1).pos
  have hLR : L' * R = L := by
    change (L.primeFactors \ Q).prod id * Q.prod id = L
    calc
      (L.primeFactors \ Q).prod id * Q.prod id = L.primeFactors.prod id :=
        Finset.prod_sdiff hQsubset
      _ = L := by
        change (∏ p ∈ L.primeFactors, p) = L
        exact Nat.prod_primeFactors_of_squarefree hSquarefree
  have hDivisors : L.divisors = Finset.image₂ Nat.mul L'.divisors R.divisors := by
    rw [← hLR, Nat.divisors_mul]
    rfl
  have hRcount : R.divisors.card = 2 ^ Q.card := by
    change (Q.prod id).divisors.card = 2 ^ Q.card
    rw [card_divisors_eq_two_pow_primeFactors_card (Nat.ne_of_gt hRpos) hRprod.1, hRprod.2]
  have hQcard := selectedExceptionalPrimeFactors_card_le L E
  have hRcard : R.divisors.card ≤ 2 ^ E.card := by
    rw [hRcount]
    exact Nat.pow_le_pow_right (by norm_num only) hQcard
  have hsmallSubset :
    restrictedDivisors L y ⊆ Finset.image₂ Nat.mul (restrictedDivisors L' y) R.divisors := by
    intro d hd
    have hdmem := (mem_restrictedDivisors hL).mp hd
    have hdlDiv : d ∈ L.divisors := Nat.mem_divisors.mpr ⟨hdmem.1, hL⟩
    have hdprod : d ∈ Finset.image₂ Nat.mul L'.divisors R.divisors := by
      rw [← hDivisors]
      exact hdlDiv
    rcases Finset.mem_image₂.mp hdprod with ⟨a, ha, b, hb, hab⟩
    have haCut : a ≤ y := by
      calc
        a ≤ a * b := Nat.le_mul_of_pos_right a (Nat.pos_of_mem_divisors hb)
        _ = d := hab
        _ ≤ y := hdmem.2
    have haSmall : a ∈ restrictedDivisors L' y :=
      (mem_restrictedDivisors (Nat.ne_of_gt hL'pos)).mpr ⟨(Nat.mem_divisors.mp ha).1, haCut⟩
    exact Finset.mem_image₂.mpr ⟨a, haSmall, b, hb, hab⟩
  calc
    (restrictedDivisors L y).card ≤
        (Finset.image₂ Nat.mul (restrictedDivisors L' y) R.divisors).card :=
      Finset.card_le_card hsmallSubset
    _ ≤ (restrictedDivisors L' y).card * R.divisors.card := Finset.card_image₂_le Nat.mul _ _
    _ ≤ (restrictedDivisors L' y).card * 2 ^ E.card := Nat.mul_le_mul_left _ hRcard
    _ = 2 ^ E.card * (restrictedDivisors L' y).card := Nat.mul_comm _ _

/--
Remove one selected prime factor for each exceptional modulus that has a
factor in `L` outside the fixed progression modulus `m`.
-/
noncomputable def exceptionalFreePartForModulus (L : ℕ) (E : Finset ℕ) (m : ℕ) : ℕ :=
  exceptionalFreePart L (selectedExceptionalPrimeFactorsForModulus L E m)

/--
The modulus-adjusted exceptional-free part is squarefree, divides `L`, and
has exactly the prime factors left after the selected factors are removed.
-/
theorem exceptionalFreePartForModulus_properties (L : ℕ) (E : Finset ℕ) (m : ℕ) (hL : L ≠ 0)
    (hSquarefree : Squarefree L) :
    Squarefree (exceptionalFreePartForModulus L E m) ∧
      (exceptionalFreePartForModulus L E m).primeFactors =
        L.primeFactors \ selectedExceptionalPrimeFactorsForModulus L E m ∧
      exceptionalFreePartForModulus L E m ∣ L ∧
      ∀ q ∈ selectedExceptionalPrimeFactorsForModulus L E m,
        ¬q ∣ exceptionalFreePartForModulus L E m := by
  let Q := selectedExceptionalPrimeFactorsForModulus L E m
  have hQone : ∀ q ∈ Q, 1 < q := fun q hq =>
    (selectedExceptionalPrimeFactorsForModulus_properties L E m hL).2.1 q hq |>.one_lt
  have hQfixed : selectedExceptionalPrimeFactors L Q = Q :=
    selectedExceptionalPrimeFactorsForModulus_fixed L E m hL
  have hbase := exceptionalFreePart_properties L Q hL hSquarefree hQone
  have hnew : exceptionalFreePartForModulus L E m = exceptionalFreePart L Q := by
    unfold exceptionalFreePartForModulus
    rfl
  rw [hnew]
  constructor
  · exact hbase.1
  constructor
  · rw [hbase.2.1, hQfixed]
  constructor
  · exact hbase.2.2.1
  · exact hbase.2.2.2

/--
Inputs: a squarefree `L` coprime to `m`, exceptional moduli `e > 1` none of
which divide `m`, and a divisor `d` of `exceptionalFreePartForModulus L E m`.

Claim: no exceptional modulus divides the progression modulus `d * m`.

Proof: if `e ∣ d * m`, choose a prime factor of `e` outside `m`. The selected
factor was removed from `L`, but the divisibility would force it to divide
`d`, contradicting `d ∣ exceptionalFreePartForModulus L E m`.

Role: this is the finite exceptional-modulus condition required to apply
paper95, Theorem 2.1 to the CRT progression modulo `d * m`.
-/
theorem exceptionalFreePartForModulus_divisors_avoid (L : ℕ) (E : Finset ℕ) (m : ℕ) (hL : L ≠ 0)
    (hSquarefree : Squarefree L) (hE : ∀ e ∈ E, 1 < e) (hEm : ∀ e ∈ E, ¬e ∣ m)
    (hLm : Nat.Coprime L m) (d : ℕ) (hd : d ∣ exceptionalFreePartForModulus L E m) :
    ∀ e ∈ E, ¬e ∣ d * m := by
  have hprops := exceptionalFreePartForModulus_properties L E m hL hSquarefree
  have hdL : d ∣ L := dvd_trans hd hprops.2.2.1
  have hdm : Nat.Coprime d m := Nat.Coprime.coprime_dvd_left hdL hLm
  let Q := selectedExceptionalPrimeFactorsForModulus L E m
  intro e he hedm
  have hF :=
    exists_prime_factor_outside_modulus_of_dvd_mul e d m L hdL hdm (hE e he) hedm (hEm e he)
  let q := selectedPrimeFactorOutsideModulus L m e
  have hqF : q ∈ exceptionalPrimeFactorsOutsideModulus L m e :=
    selectedPrimeFactorOutsideModulus_mem L m e hF
  have hqData := Finset.mem_filter.mp hqF
  have hqd := prime_factor_dvd_left_of_exceptional_dvd_mul e d m q hqData.1 hedm hqData.2.2
  have hqQ : q ∈ Q := by
    unfold Q selectedExceptionalPrimeFactorsForModulus
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hF⟩, rfl⟩
  exact (hprops.2.2.2 q hqQ) (dvd_trans hqd hd)

/--
The selected-factor construction has the same divisor-count loss as removing
one factor per exceptional modulus.
-/
theorem restrictedDivisors_card_le_exceptional_modulus_loss (L : ℕ) (E : Finset ℕ) (m y : ℕ)
    (hL : L ≠ 0) (hSquarefree : Squarefree L) :
    (restrictedDivisors L y).card ≤
      2 ^ E.card * (restrictedDivisors (exceptionalFreePartForModulus L E m) y).card := by
  let Q := selectedExceptionalPrimeFactorsForModulus L E m
  have hQsubset : Q ⊆ L.primeFactors :=
    (selectedExceptionalPrimeFactorsForModulus_properties L E m hL).1
  have hQprime : ∀ q ∈ Q, Nat.Prime q :=
    (selectedExceptionalPrimeFactorsForModulus_properties L E m hL).2.1
  have hQone : ∀ q ∈ Q, 1 < q := fun q hq => (hQprime q hq).one_lt
  have hQcard : Q.card ≤ E.card := selectedExceptionalPrimeFactorsForModulus_card_le L E m
  have hQfixed : selectedExceptionalPrimeFactors L Q = Q :=
    selectedExceptionalPrimeFactorsForModulus_fixed L E m hL
  have hcount := restrictedDivisors_card_le_exceptional_loss L Q y hL hSquarefree hQone
  unfold exceptionalFreePart at hcount
  rw [hQfixed] at hcount
  have hfree : exceptionalFreePartForModulus L E m = (L.primeFactors \ Q).prod id := by
    unfold exceptionalFreePartForModulus exceptionalFreePart
    rw [hQfixed]
  rw [← hfree] at hcount
  have hpow : 2 ^ Q.card ≤ 2 ^ E.card := Nat.pow_le_pow_right (by norm_num only) hQcard
  calc
    (restrictedDivisors L y).card ≤
        2 ^ Q.card * (restrictedDivisors (exceptionalFreePartForModulus L E m) y).card :=
      hcount
    _ = (restrictedDivisors (exceptionalFreePartForModulus L E m) y).card * 2 ^ Q.card :=
      Nat.mul_comm _ _
    _ ≤ (restrictedDivisors (exceptionalFreePartForModulus L E m) y).card * 2 ^ E.card :=
      Nat.mul_le_mul_left _ hpow
    _ = 2 ^ E.card * (restrictedDivisors (exceptionalFreePartForModulus L E m) y).card :=
      Nat.mul_comm _ _

/--
Inputs: a squarefree modulus `L`, an exceptional set `E`, a cutoff `y`, and
an upper bound `D` for the number of exceptional moduli.

Claim: removing exceptional prime factors costs at most `2^D` in the divisor
count below `y`.

Proof: apply the existing loss bound with `E.card`, then use monotonicity of
natural powers and multiplication with the hypothesis `E.card ≤ D`.

Role: this exposes the divisor-loss bound using the uniform exceptional-set
size parameter from paper95 Theorem 2.1.
-/
theorem restrictedDivisors_card_le_exceptional_modulus_count_bound (L : ℕ) (E : Finset ℕ)
    (m y D : ℕ) (hL : L ≠ 0) (hSquarefree : Squarefree L) (hEcard : E.card ≤ D) :
    (restrictedDivisors L y).card ≤
      2 ^ D * (restrictedDivisors (exceptionalFreePartForModulus L E m) y).card := by
  have hcount := restrictedDivisors_card_le_exceptional_modulus_loss L E m y hL hSquarefree
  have hpowNat : 2 ^ E.card ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num only) hEcard
  exact le_trans hcount (Nat.mul_le_mul_right _ hpowNat)

/--
Inputs: a nonnegative coefficient `c` and a strict lower bound for the divisor
count of `L`, scaled by the exceptional-modulus loss.

Claim: the same threshold holds for `exceptionalFreePartForModulus L E m`.

Proof: cast the finite divisor-count loss to `ℝ`, multiply by `c`, and cancel
the positive factor `2 ^ E.card`.

Role: this supplies the count threshold for the modulus-adjusted prime-set
construction.
-/
theorem exists_lt_exceptionalFreePartForModulus_card_of_scaled_bound (L : ℕ) (E : Finset ℕ)
    (m y : ℕ) (hL : L ≠ 0) (hSquarefree : Squarefree L) (t c : ℝ) (hc : 0 ≤ c)
    (htarget : t * (2 ^ E.card : ℝ) < c * ((restrictedDivisors L y).card : ℝ)) :
    t < c * ((restrictedDivisors (exceptionalFreePartForModulus L E m) y).card : ℝ) := by
  have hcount := restrictedDivisors_card_le_exceptional_modulus_loss L E m y hL hSquarefree
  have hcountReal :
    ((restrictedDivisors L y).card : ℝ) ≤
      (2 ^ E.card : ℝ) *
        ((restrictedDivisors (exceptionalFreePartForModulus L E m) y).card : ℝ) := by
    exact_mod_cast hcount
  have hpow : 0 < (2 ^ E.card : ℝ) := pow_pos (by norm_num only : (0 : ℝ) < 2) _
  have hscaled := mul_le_mul_of_nonneg_left hcountReal hc
  nlinarith only [htarget, hscaled, hpow]

/--
Inputs: a nonnegative target `t`, a nonnegative coefficient `c`, and a lower
bound for the divisor count of `L` after scaling by the exceptional loss.

Claim: the same target is bounded by the coefficient times the count for the
exception-free part of `L`.

Proof: cast the finite divisor-loss inequality to `ℝ`, multiply it by `c`, and
compare both sides after cancelling the positive factor `2 ^ E.card`.

Role: this transfers a global divisor-count threshold to the family on which
the exceptional-modulus estimate can be applied.
-/
theorem exists_lt_exceptionalFreePart_card_of_scaled_bound (L : ℕ) (E : Finset ℕ) (y : ℕ)
    (hL : L ≠ 0) (hSquarefree : Squarefree L) (hE : ∀ e ∈ E, 1 < e) (t c : ℝ) (hc : 0 ≤ c)
    (htarget : t * (2 ^ E.card : ℝ) < c * ((restrictedDivisors L y).card : ℝ)) :
    t < c * ((restrictedDivisors (exceptionalFreePart L E) y).card : ℝ) := by
  have hcount := restrictedDivisors_card_le_exceptional_loss L E y hL hSquarefree hE
  have hcountReal :
    ((restrictedDivisors L y).card : ℝ) ≤
      (2 ^ E.card : ℝ) * ((restrictedDivisors (exceptionalFreePart L E) y).card : ℝ) := by
    exact_mod_cast hcount
  have hpow : 0 < (2 ^ E.card : ℝ) := pow_pos (by norm_num only : (0 : ℝ) < 2) _
  have hscaled := mul_le_mul_of_nonneg_left hcountReal hc
  nlinarith only [htarget, hscaled, hpow]

/--
Inputs: a squarefree modulus `L`, a finite exceptional set `E`, a modulus `m`,
and cutoffs `y` and `q`.

Claim: the original restricted-divisor count is bounded by the exceptional
factor times the count of exceptional-free divisors above `q`, with a loss of
at most `q + 1` divisors.

Proof: combine the exceptional-factor count bound with the finite threshold
loss for `largeRestrictedDivisors`.

Role: this gives a single finite count estimate for the large-modulus branch.
-/
theorem restrictedDivisors_card_le_exceptional_modulus_loss_after_threshold (L : ℕ) (E : Finset ℕ)
    (m y q : ℕ) (hL : L ≠ 0) (hSquarefree : Squarefree L) :
    (restrictedDivisors L y).card ≤
      2 ^ E.card *
        ((largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q).card + (q + 1)) := by
  have hcount := restrictedDivisors_card_le_exceptional_modulus_loss L E m y hL hSquarefree
  have hlarge :=
    restrictedDivisors_card_sub_threshold_le_large (exceptionalFreePartForModulus L E m) y q
  have hfree := Nat.sub_le_iff_le_add.mp hlarge
  calc
    (restrictedDivisors L y).card ≤
        2 ^ E.card * (restrictedDivisors (exceptionalFreePartForModulus L E m) y).card :=
      hcount
    _ ≤
        2 ^ E.card *
          ((largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q).card + (q + 1)) :=
      Nat.mul_le_mul_left (2 ^ E.card) hfree

/--
Inputs: a strict real threshold, a nonnegative coefficient, and enough original
divisors to absorb both exceptional-modulus and small-divisor losses.

Claim: the exceptional-free divisors above `q` exceed the requested threshold
after scaling by `c`.

Proof: cast the combined finite count bound to `ℝ`, multiply by `c`, and cancel
the positive exceptional factor.

Role: this supplies the large-modulus count premise for the prime-set
construction directly from a lower bound on the original divisor count.
-/
theorem exists_lt_largeExceptionalFreePart_card_of_scaled_bound (L : ℕ) (E : Finset ℕ) (m y q : ℕ)
    (hL : L ≠ 0) (hSquarefree : Squarefree L) (t c : ℝ) (hc : 0 ≤ c)
    (htarget : (t + c * (q + 1 : ℝ)) * (2 ^ E.card : ℝ) < c * ((restrictedDivisors L y).card : ℝ)) :
    t < c * ((largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q).card : ℝ) := by
  have hbound :=
    restrictedDivisors_card_le_exceptional_modulus_loss_after_threshold L E m y q hL hSquarefree
  have hboundReal :
    ((restrictedDivisors L y).card : ℝ) ≤
      (2 ^ E.card : ℝ) *
        ((largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q).card + (q + 1) :
          ℕ) := by
    exact_mod_cast hbound
  have hscaled := mul_le_mul_of_nonneg_left hboundReal hc
  have hfactor : 0 < (2 ^ E.card : ℝ) := pow_pos (by norm_num only : (0 : ℝ) < 2) _
  have hcombined :
    (t + c * (q + 1 : ℝ)) * (2 ^ E.card : ℝ) <
      (c *
          ((largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q).card + (q + 1) :
            ℕ)) *
        (2 ^ E.card : ℝ) := by
    calc
      (t + c * (q + 1 : ℝ)) * (2 ^ E.card : ℝ) < c * ((restrictedDivisors L y).card : ℝ) := htarget
      _ ≤
          c *
            ((2 ^ E.card : ℝ) *
              ((largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q).card + (q + 1) :
                ℕ)) :=
        hscaled
      _ =
          (c *
              ((largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q).card + (q + 1) :
                ℕ)) *
            (2 ^ E.card : ℝ) :=
        by ring
  have hcancel := (mul_lt_mul_iff_of_pos_right hfactor).mp hcombined
  simp only [Nat.cast_add, Nat.cast_one] at hcancel
  nlinarith only [hcancel]

/--
Inputs: a nonnegative threshold `t`, a nonnegative coefficient `c`, an upper
bound `D` for `E.card`, and an original divisor-count lower bound scaled by
`2^D` and the small-divisor loss `q + 1`.

Claim: after multiplying its large exceptional-free divisor count by `c`, the
result exceeds the target `t`.

Proof: lower the loss factor from `2^D` to `2^E.card`, then apply
`exists_lt_largeExceptionalFreePart_card_of_scaled_bound`.

Role: this uses the uniform exceptional-set cardinality from paper95 directly
in the finite averaging threshold.
-/
theorem exists_lt_largeExceptionalFreePart_card_of_exceptional_count_bound (L : ℕ) (E : Finset ℕ)
    (m y q D : ℕ) (hL : L ≠ 0) (hSquarefree : Squarefree L) (hEcard : E.card ≤ D) (t c : ℝ)
    (hc : 0 ≤ c) (ht : 0 ≤ t)
    (htarget : (t + c * (q + 1 : ℝ)) * (2 ^ D : ℝ) < c * ((restrictedDivisors L y).card : ℝ)) :
    t < c * ((largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q).card : ℝ) := by
  have hpowNat : 2 ^ E.card ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num only) hEcard
  have hpow : (2 ^ E.card : ℝ) ≤ (2 ^ D : ℝ) := by exact_mod_cast hpowNat
  have hqnonneg : (0 : ℝ) ≤ (q + 1 : ℝ) := by exact_mod_cast Nat.zero_le (q + 1)
  have hbase : 0 ≤ t + c * (q + 1 : ℝ) := add_nonneg ht (mul_nonneg hc hqnonneg)
  have hscale : (t + c * (q + 1 : ℝ)) * (2 ^ E.card : ℝ) ≤ (t + c * (q + 1 : ℝ)) * (2 ^ D : ℝ) :=
    mul_le_mul_of_nonneg_left hpow hbase
  exact
    exists_lt_largeExceptionalFreePart_card_of_scaled_bound L E m y q hL hSquarefree t c hc
      (lt_of_le_of_lt hscale htarget)

/--
Inputs: a finite averaging parameter set, a target prime count, and an original
divisor-count lower bound that includes exceptional and cutoff losses.

Claim: the large exceptional-free divisor count exceeds the threshold required
by the finite averaging theorem.

Proof: instantiate the scaled large-divisor bound with the parameter-count
multiple of the target as its real threshold.

Role: this is the count premise consumed by the variable-cutoff progression
average.
-/
theorem exists_lt_largeExceptionalFreePart_card_of_positiveCoprimeParameters_bound (L : ℕ)
    (E : Finset ℕ) (m y q K T : ℕ) (hL : L ≠ 0) (hSquarefree : Squarefree L) (c : ℝ) (hc : 0 ≤ c)
    (htarget :
      ((((positiveCoprimeParameters L K).card * T : ℕ) : ℝ) + c * (q + 1 : ℝ)) * (2 ^ E.card : ℝ) <
        c * ((restrictedDivisors L y).card : ℝ)) :
    (((positiveCoprimeParameters L K).card * T : ℕ) : ℝ) <
      c * ((largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q).card : ℝ) := by
  exact
    exists_lt_largeExceptionalFreePart_card_of_scaled_bound L E m y q hL hSquarefree
      (((positiveCoprimeParameters L K).card * T : ℕ) : ℝ) c hc htarget

end PseudoPrime.AnalyticNumberTheory.AGP
