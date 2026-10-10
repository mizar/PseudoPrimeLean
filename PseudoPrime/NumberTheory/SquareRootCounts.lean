/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Square-root counts for residue classes

Odd prime-power unit groups give at most two residue roots. Two-power unit groups
have a cyclic kernel modulo four, giving at most four roots. A residue-and-quotient
injection converts these bounds into finite counts, and the Chinese remainder
map assembles coprime local root estimates.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Every power fiber injects into the power kernel by translation by one root.
An empty fiber has zero cardinality. This transfers kernel bounds to all unit residues. -/
private theorem card_pow_fiber_le_card_ker {G : Type*} [CommGroup G] [Finite G] (a : G) (k : ℕ) :
    Nat.card { x : G // x ^ k = a } ≤ Nat.card (powMonoidHom k : G →* G).ker := by
  classical
  by_cases hex : ∃ x : G, x ^ k = a
  · obtain ⟨b, hb⟩ := hex
    let f : { x : G // x ^ k = a } → (powMonoidHom k : G →* G).ker := fun x ↦
      ⟨b⁻¹ * x.val, by
        change (b⁻¹ * x.val) ^ k = 1
        rw [mul_pow, inv_pow, hb, x.property, inv_mul_cancel]⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact mul_left_cancel (congrArg Subtype.val hxy)
    exact Nat.card_le_card_of_injective f hf
  · let : IsEmpty { x : G // x ^ k = a } := ⟨fun x ↦ hex ⟨x.val, x.property⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- In a finite commutative cyclic group, each positive power fiber has at most
its exponent many elements. The power kernel has cardinality the gcd of the group
order and exponent. This bounds the local odd-prime root sets. -/
private theorem card_pow_fiber_le {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] (a : G) {k : ℕ}
    (hk : 0 < k) : Nat.card { x : G // x ^ k = a } ≤ k := by
  have hc := card_pow_fiber_le_card_ker a k
  rw [IsCyclic.card_powMonoidHom_ker G k] at hc
  exact hc.trans (Nat.gcd_le_right _ hk)

/-- A square root of a unit is a unit, giving an injection from residue roots
into the corresponding square fiber of the unit group. -/
private theorem card_sq_roots_le_unit_fiber {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) :
    Nat.card { x : ZMod q // x ^ 2 = (a : ZMod q) } ≤ Nat.card { u : (ZMod q)ˣ // u ^ 2 = a } := by
  classical
  have hu (x : ZMod q) (hx : x ^ 2 = (a : ZMod q)) : IsUnit x :=
    (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp (hx.symm ▸ a.isUnit)
  let f : { x : ZMod q // x ^ 2 = (a : ZMod q) } → { u : (ZMod q)ˣ // u ^ 2 = a } := fun x ↦
    ⟨(hu x.val x.property).unit, by
      apply Units.val_injective
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
      exact x.property⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hv := congrArg (fun u ↦ (u.val : ZMod q)) hxy
    simpa only [f, IsUnit.unit_spec] using hv
  exact Nat.card_le_card_of_injective f hf

/-- For an odd prime power, a unit residue has at most two square roots, including
exponent zero. Every square root is a unit; inject the residue roots into the square
fiber of the cyclic unit group. This supplies the odd-prime local factor for
counting square congruences in arithmetic progressions. -/
theorem card_sq_roots_odd_prime_power {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ)
    (a : (ZMod (p ^ n))ˣ) : Nat.card { x : ZMod (p ^ n) // x ^ 2 = (a : ZMod (p ^ n)) } ≤ 2 := by
  let : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  let : IsCyclic (ZMod (p ^ n))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 n
  exact (card_sq_roots_le_unit_fiber a).trans (card_pow_fiber_le a (by decide : (0 : ℕ) < 2))

/-- For a nonzero modulus and a natural cutoff, the number of square congruence solutions
through the cutoff is at most the residue-root count times one plus the cutoff quotient.
Inject each solution into its residue and quotient, recovering it by division with remainder.
This turns local square-root counts into the finite counts used in the prime-power estimate. -/
theorem card_sq_congruence_le {q : ℕ} [NeZero q] (a : ZMod q) (N : ℕ) :
    Nat.card { n : ℕ // n ≤ N ∧ (n : ZMod q) ^ 2 = a } ≤
      Nat.card { x : ZMod q // x ^ 2 = a } * (N / q + 1) := by
  classical
  let f :
    { n : ℕ // n ≤ N ∧ (n : ZMod q) ^ 2 = a } → { x : ZMod q // x ^ 2 = a } × Fin (N / q + 1) :=
    fun n ↦
    (⟨(n.val : ZMod q), n.property.2⟩,
      ⟨n.val / q, Nat.lt_succ_of_le (Nat.div_le_div_right n.property.1)⟩)
  have hf : Function.Injective f := by
    intro m n hmn
    apply Subtype.ext
    have hm : (m.val : ZMod q) = (n.val : ZMod q) := congrArg (fun r ↦ r.1.val) hmn
    have hd : m.val / q = n.val / q := congrArg (fun r ↦ r.2.val) hmn
    have hr : m.val % q = n.val % q := by
      have hv := congrArg ZMod.val hm
      simpa only [ZMod.val_natCast] using hv
    calc
      m.val = m.val % q + q * (m.val / q) := (Nat.mod_add_div _ _).symm
      _ = n.val % q + q * (n.val / q) := by rw [hr, hd]
      _ = n.val := Nat.mod_add_div _ _
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod, Nat.card_fin] using hc

/-- For an odd prime power and a unit residue, there are at most twice one plus the cutoff
quotient many square congruence solutions through a natural cutoff. Combine the residue-root
bound with the residue-and-quotient injection. This gives the finite counting interface
for the even prime-power contribution in a reduced residue class. -/
theorem card_sq_congruence_odd_prime_power_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n N : ℕ)
    (a : (ZMod (p ^ n))ˣ) :
    Nat.card { m : ℕ // m ≤ N ∧ (m : ZMod (p ^ n)) ^ 2 = (a : ZMod (p ^ n)) } ≤
      2 * (N / (p ^ n) + 1) := by
  let : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  exact
    (card_sq_congruence_le (a : ZMod (p ^ n)) N).trans
      (Nat.mul_le_mul_right _ (card_sq_roots_odd_prime_power hp hp2 n a))

/-- For a homomorphism of finite commutative groups with cyclic kernel, the power
kernel has at most the exponent times the target order many elements. Restrict the
homomorphism to the power kernel and inject its kernel into a power fiber of the
original cyclic kernel. This bounds the square kernel of a two-power unit group. -/
private theorem card_power_kernel_le_of_cyclic_ker {G T : Type*} [CommGroup G] [CommGroup T]
    [Finite G] [Finite T] (f : G →* T) [IsCyclic f.ker] {k : ℕ} (hk : 0 < k) :
    Nat.card (powMonoidHom k : G →* G).ker ≤ k * Nat.card T := by
  let P := (powMonoidHom k : G →* G).ker
  let f0 : P →* T := f.comp P.subtype
  let j : f0.ker → { y : f.ker // y ^ k = 1 } := fun x ↦
    ⟨⟨x.val.val, x.property⟩, by
      apply Subtype.ext
      exact x.val.property⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z ↦ z.val.val) hxy
  have hker : Nat.card f0.ker ≤ k :=
    (Nat.card_le_card_of_injective j hj).trans (card_pow_fiber_le 1 hk)
  have hrange : Nat.card f0.range ≤ Nat.card T :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hc := Subgroup.card_ker_mul_card_range f0
  exact hc.symm.trans_le (Nat.mul_le_mul hker hrange)

/-- For modulus two to the power n plus two, the kernel of reduction of units modulo
four is cyclic. Surjectivity gives its cardinality two to the power n; the unit five
has this order and lies in the kernel. This isolates the cyclic part for root counting. -/
private theorem two_power_mod_four_kernel_cyclic (n : ℕ) (hd : 4 ∣ 2 ^ (n + 2)) :
    IsCyclic (ZMod.unitsMap hd).ker := by
  let : NeZero (2 ^ (n + 2)) := ⟨pow_ne_zero _ (by decide)⟩
  let f := ZMod.unitsMap hd
  have hc := Subgroup.card_ker_mul_card_of_surjective (ZMod.unitsMap_surjective hd)
  have hfour : Nat.card (ZMod 4)ˣ = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  have htot : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ (n + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (Nat.zero_lt_succ _)]
    simp only [Nat.succ_sub_one, mul_one]
  rw [hfour, htot] at hc
  have hcard : Nat.card f.ker = 2 ^ n :=
    Nat.eq_of_mul_eq_mul_right (by decide) (hc.trans (pow_succ 2 n))
  let u : (ZMod (2 ^ (n + 2)))ˣ := ZMod.unitOfCoprime 5 ((by decide : Nat.Coprime 5 2).pow_right _)
  have hu : f u = 1 := by
    apply Units.val_injective
    change (ZMod.castHom hd (ZMod 4)) (u : ZMod (2 ^ (n + 2))) = (1 : ZMod 4)
    rw [ZMod.coe_unitOfCoprime, ZMod.castHom_apply, ZMod.cast_natCast hd]
    decide
  let v : f.ker := ⟨u, hu⟩
  have hv : orderOf v = 2 ^ n := by
    rw [← orderOf_injective f.ker.subtype f.ker.subtype_injective, ←
      orderOf_injective (Units.coeHom _) Units.coeHom_injective]
    change orderOf (u : ZMod (2 ^ (n + 2))) = 2 ^ n
    rw [ZMod.coe_unitOfCoprime]
    exact ZMod.orderOf_five n
  exact isCyclic_of_orderOf_eq_card v (hv.trans hcard.symm)

/-- For a unit modulo a power of two with exponent at least two, there are at most
four square roots. Reduction to the two units modulo four has cyclic kernel, so its
square kernel has at most four elements. Translation bounds every square fiber. -/
private theorem card_sq_roots_two_power_add_two {n : ℕ} (a : (ZMod (2 ^ (n + 2)))ˣ) :
    Nat.card { x : ZMod (2 ^ (n + 2)) // x ^ 2 = (a : ZMod (2 ^ (n + 2))) } ≤ 4 := by
  let : NeZero (2 ^ (n + 2)) := ⟨pow_ne_zero _ (by decide)⟩
  have hd : 4 ∣ 2 ^ (n + 2) := (by norm_num only : 4 = 2 ^ 2) ▸ pow_dvd_pow 2 (Nat.le_add_left 2 n)
  let f := ZMod.unitsMap hd
  let : IsCyclic f.ker := two_power_mod_four_kernel_cyclic n hd
  have hfour : Nat.card (ZMod 4)ˣ = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  have hc := card_power_kernel_le_of_cyclic_ker f (by decide : (0 : ℕ) < 2)
  rw [hfour] at hc
  exact (card_sq_roots_le_unit_fiber a).trans ((card_pow_fiber_le_card_ker a 2).trans hc)

/-- For every power of two, a unit residue has at most four square roots. Moduli one
and two are bounded by their full cardinality; higher powers use the cyclic kernel
of reduction modulo four. This supplies the exceptional even-prime local root factor. -/
theorem card_sq_roots_two_power (n : ℕ) (a : (ZMod (2 ^ n))ˣ) :
    Nat.card { x : ZMod (2 ^ n) // x ^ 2 = (a : ZMod (2 ^ n)) } ≤ 4 := by
  let : NeZero (2 ^ n) := ⟨pow_ne_zero _ (by decide)⟩
  cases n with
  | zero =>
    have hc :=
      Nat.card_le_card_of_injective
        (Subtype.val : { x : ZMod (2 ^ 0) // x ^ 2 = (a : ZMod (2 ^ 0)) } → ZMod (2 ^ 0))
        Subtype.val_injective
    norm_num only [pow_zero, Nat.card_eq_fintype_card, ZMod.card] at hc ⊢
    exact hc.trans (by decide : (1 : ℕ) ≤ 4)
  | succ n =>
    cases n with
    | zero =>
      have hc :=
        Nat.card_le_card_of_injective
          (Subtype.val : { x : ZMod (2 ^ 1) // x ^ 2 = (a : ZMod (2 ^ 1)) } → ZMod (2 ^ 1))
          Subtype.val_injective
      norm_num only [pow_one, Nat.card_eq_fintype_card, ZMod.card] at hc ⊢
      exact hc.trans (by decide : (2 : ℕ) ≤ 4)
    | succ n => exact card_sq_roots_two_power_add_two a

/-- For a unit modulo a power of two, retain the exact local root bounds at
exponents zero, one, and two: respectively one, one, and two roots.
These finite rings are checked in the kernel; larger exponents use the cyclic-kernel
bound of four. This avoids the uniform factor four at small even prime powers. -/
theorem card_sq_roots_two_power_sharp (n : ℕ) (a : (ZMod (2 ^ n))ˣ) :
    Nat.card { x : ZMod (2 ^ n) // x ^ 2 = (a : ZMod (2 ^ n)) } ≤
      (match n with
      | 0 => 1
      | 1 => 1
      | 2 => 2
      | _ => 4) := by
  match n with
  | 0 =>
    rw [Nat.card_eq_fintype_card]
    exact
      (by decide +kernel : ∀ a : (ZMod 1)ˣ, Fintype.card { x : ZMod 1 // x ^ 2 = (a : ZMod 1) } ≤ 1)
        a
  | 1 =>
    rw [Nat.card_eq_fintype_card]
    exact
      (by decide +kernel : ∀ a : (ZMod 2)ˣ, Fintype.card { x : ZMod 2 // x ^ 2 = (a : ZMod 2) } ≤ 1)
        a
  | 2 =>
    rw [Nat.card_eq_fintype_card]
    exact
      (by decide +kernel : ∀ a : (ZMod 4)ˣ, Fintype.card { x : ZMod 4 // x ^ 2 = (a : ZMod 4) } ≤ 2)
        a
  | n + 3 => exact card_sq_roots_two_power (n + 3) a

/-- For a power of two and a unit residue, there are at most four times one plus the
cutoff quotient many square congruence solutions through a natural cutoff. Combine
the residue-root bound and division-with-remainder injection. This is the finite
counting interface for the even local factor. -/
theorem card_sq_congruence_two_power_le (n N : ℕ) (a : (ZMod (2 ^ n))ˣ) :
    Nat.card { m : ℕ // m ≤ N ∧ (m : ZMod (2 ^ n)) ^ 2 = (a : ZMod (2 ^ n)) } ≤
      4 * (N / (2 ^ n) + 1) := by
  let : NeZero (2 ^ n) := ⟨pow_ne_zero _ (by decide)⟩
  exact
    (card_sq_congruence_le (a : ZMod (2 ^ n)) N).trans
      (Nat.mul_le_mul_right _ (card_sq_roots_two_power n a))

/-- For coprime nonzero moduli, the square-root count is at most the product of the
projected root counts. The Chinese remainder equivalence injects each root into
its pair of local roots. This assembles prime-power estimates for residue classes. -/
theorem card_sq_roots_coprime_mul_le {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (a : ZMod (m * n)) :
    Nat.card { x : ZMod (m * n) // x ^ 2 = a } ≤
      Nat.card { x : ZMod m // x ^ 2 = ((ZMod.chineseRemainder h) a).1 } *
        Nat.card { x : ZMod n // x ^ 2 = ((ZMod.chineseRemainder h) a).2 } := by
  classical
  let e := ZMod.chineseRemainder h
  let f :
    { x : ZMod (m * n) // x ^ 2 = a } →
      { x : ZMod m // x ^ 2 = (e a).1 } × { x : ZMod n // x ^ 2 = (e a).2 } :=
    fun x ↦
    (⟨(e x.val).1, by
        have he := congrArg (fun z ↦ (e z).1) x.property
        rw [map_pow] at he
        exact he⟩,
      ⟨(e x.val).2, by
        have he := congrArg (fun z ↦ (e z).2) x.property
        rw [map_pow] at he
        exact he⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact Prod.ext (congrArg (fun z ↦ z.1.val) hxy) (congrArg (fun z ↦ z.2.val) hxy)
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod] using hc

/-- A unit residue modulo a prime power has at most four roots at the prime two and
at most two roots at every odd prime. Specialize the two local counting theorems.
This supplies each factor of the global prime-factor product. -/
private theorem card_sq_roots_prime_power_factor {p : ℕ} (hp : p.Prime) (n : ℕ) (a : ZMod (p ^ n))
    (ha : IsUnit a) : Nat.card { x : ZMod (p ^ n) // x ^ 2 = a } ≤ (if p = 2 then 4 else 2) := by
  by_cases hp2 : p = 2
  · subst p
    simpa only [ite_eq_left_iff, ite_true, IsUnit.unit_spec] using card_sq_roots_two_power n ha.unit
  · simpa only [ite_false, hp2, IsUnit.unit_spec] using
      card_sq_roots_odd_prime_power hp hp2 n ha.unit

/-- For a nonzero modulus and unit residue, the square-root count is bounded by the
product of the local prime factors, using four for two and two for odd primes.
Induct over coprime prime-power factors and apply the Chinese remainder injection.
This retains the even-prime correction only once. -/
private theorem card_sq_roots_le_local_product (q : ℕ) :
    q ≠ 0 →
      ∀ a : ZMod q,
        IsUnit a →
          Nat.card { x : ZMod q // x ^ 2 = a } ≤
            ∏ p ∈ q.primeFactors, (if p = 2 then 4 else 2) := by
  induction q using Nat.recOnPrimePow with
  | zero =>
    intro hq; exact False.elim (hq rfl)
  | one =>
    intro _ a _
    have hc :=
      Nat.card_le_card_of_injective (Subtype.val : { x : ZMod 1 // x ^ 2 = a } → ZMod 1)
        Subtype.val_injective
    have hcard : Nat.card (ZMod 1) = 1 := by rw [Nat.card_eq_fintype_card, ZMod.card]
    simpa only [Nat.primeFactors_one, Finset.prod_empty] using hc.trans_eq hcard
  | prime_pow_mul b p n hp hpb hn ih =>
    intro hq a ha
    have hb : b ≠ 0 := by
      intro hb
      apply hq
      rw [hb, mul_zero]
    let : NeZero b := ⟨hb⟩
    let : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
    have hcop : (p ^ n).Coprime b := (hp.coprime_iff_not_dvd.mpr hpb).pow_left n
    let e := ZMod.chineseRemainder hcop
    have h1 : IsUnit (e a).1 := ha.map ((RingHom.fst _ _).comp e.toRingHom)
    have h2 : IsUnit (e a).2 := ha.map ((RingHom.snd _ _).comp e.toRingHom)
    have hc := card_sq_roots_coprime_mul_le hcop a
    have hl := card_sq_roots_prime_power_factor hp n (e a).1 h1
    have hr := ih hb (e a).2 h2
    have he :
      (∏ r ∈ (p ^ n * b).primeFactors, (if r = 2 then 4 else 2)) =
        (if p = 2 then 4 else 2) * ∏ r ∈ b.primeFactors, (if r = 2 then 4 else 2) := by
      rw [Nat.primeFactors_mul (pow_ne_zero n hp.ne_zero) hb,
        Finset.prod_union hcop.disjoint_primeFactors, Nat.primeFactors_prime_pow hn.ne' hp,
        Finset.prod_singleton]
    exact hc.trans ((Nat.mul_le_mul hl hr).trans_eq he.symm)

/-- For any finite set of primes, the product with factor four at two and factor two
elsewhere is at most two to one plus the set cardinality. Separate the factor two
when it occurs; all remaining factors are two. This bounds the global local-root product. -/
private theorem local_root_product_le (s : Finset ℕ) :
    (∏ p ∈ s, (if p = 2 then 4 else 2)) ≤ 2 ^ (s.card + 1) := by
  classical
  by_cases h2 : 2 ∈ s
  · have he : (∏ p ∈ s.erase 2, (if p = 2 then 4 else 2)) = 2 ^ (s.erase 2).card := by
      calc
        (∏ p ∈ s.erase 2, (if p = 2 then 4 else 2)) = ∏ _ ∈ s.erase 2, 2 := by
          apply Finset.prod_congr rfl
          intro p hp
          exact ite_eq_right ((Finset.mem_erase.mp hp).1)
        _ = 2 ^ (s.erase 2).card := Finset.prod_const 2
    have hc := Finset.card_erase_add_one h2
    rw [← Finset.mul_prod_erase _ _ h2]
    simp only [ite_true, he]
    rw [← hc, Nat.add_assoc, pow_add]
    norm_num only
    exact (mul_comm (4 : ℕ) (2 ^ (s.erase 2).card)).le
  · have he : (∏ p ∈ s, (if p = 2 then 4 else 2)) = 2 ^ s.card := by
      calc
        (∏ p ∈ s, (if p = 2 then 4 else 2)) = ∏ _ ∈ s, 2 := by
          apply Finset.prod_congr rfl
          intro p hp
          have hn : p ≠ 2 := by
            intro heq
            exact h2 (heq ▸ hp)
          exact ite_eq_right hn
        _ = 2 ^ s.card := Finset.prod_const 2
    rw [he]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ _)

/-- For an odd nonzero modulus and unit residue, the square-root count is at most
two to the number of distinct prime factors. Every local prime is odd, so the
Chinese remainder product has only factors two.
This retains the sharper root count in odd-modulus residue-weight estimates. -/
theorem card_sq_roots_odd_le_primeFactors {q : ℕ} [NeZero q] (hq : Odd q) (a : (ZMod q)ˣ) :
    Nat.card { x : ZMod q // x ^ 2 = (a : ZMod q) } ≤ 2 ^ q.primeFactors.card := by
  have he : (∏ p ∈ q.primeFactors, (if p = 2 then 4 else 2)) = 2 ^ q.primeFactors.card := by
    calc
      (∏ p ∈ q.primeFactors, (if p = 2 then 4 else 2)) = ∏ _ ∈ q.primeFactors, 2 := by
        apply Finset.prod_congr rfl
        intro p hp
        have hn : p ≠ 2 := by
          intro h
          exact hq.not_two_dvd_nat (h ▸ (Nat.mem_primeFactors.mp hp).2.1)
        exact ite_eq_right hn
      _ = 2 ^ q.primeFactors.card := Finset.prod_const 2
  exact (card_sq_roots_le_local_product q (NeZero.ne q) (a : ZMod q) a.isUnit).trans_eq he

/-- For every nonzero modulus and unit residue, there are at most two to one plus the
number of distinct prime divisors many square roots. Assemble the odd-prime and
two-power local counts by Chinese remaindering and count the exceptional factor once.
This is the residue-root estimate used in Section 4.1 for Corollary 1.2. -/
theorem card_sq_roots_le_primeFactors {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) :
    Nat.card { x : ZMod q // x ^ 2 = (a : ZMod q) } ≤ 2 ^ (q.primeFactors.card + 1) := by
  exact
    (card_sq_roots_le_local_product q (NeZero.ne q) (a : ZMod q) a.isUnit).trans
      (local_root_product_le q.primeFactors)

/-- For a nonzero modulus and unit residue, the number of square congruence solutions
through a natural cutoff is at most two to one plus the prime-factor count times
one plus the cutoff quotient. Combine the global residue-root estimate with the
residue-and-quotient injection. This supplies the finite count for even prime powers. -/
theorem card_sq_congruence_le_primeFactors {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (N : ℕ) :
    Nat.card { n : ℕ // n ≤ N ∧ (n : ZMod q) ^ 2 = (a : ZMod q) } ≤
      2 ^ (q.primeFactors.card + 1) * (N / q + 1) := by
  exact
    (card_sq_congruence_le (a : ZMod q) N).trans
      (Nat.mul_le_mul_right _ (card_sq_roots_le_primeFactors a))

/-- For coprime nonzero factors with odd second factor, a supplied first-factor
root bound multiplies by two to the second factor's number of prime divisors.
The Chinese remainder map transports a unit to units in both factors and bounds
the root fiber by the product of their fibers. This assembles refined even-modulus bounds. -/
theorem card_sq_roots_coprime_odd_mul_le {n m r : ℕ} [NeZero n] [NeZero m] (hcop : n.Coprime m)
    (hm : Odd m) (hroot : ∀ b : (ZMod n)ˣ, Nat.card { x : ZMod n // x ^ 2 = (b : ZMod n) } ≤ r)
    (a : (ZMod (n * m))ˣ) :
    Nat.card { x : ZMod (n * m) // x ^ 2 = (a : ZMod (n * m)) } ≤ r * 2 ^ m.primeFactors.card := by
  let e := ZMod.chineseRemainder hcop
  have h1 : IsUnit (e (a : ZMod (n * m))).1 := a.isUnit.map ((RingHom.fst _ _).comp e.toRingHom)
  have h2 : IsUnit (e (a : ZMod (n * m))).2 := a.isUnit.map ((RingHom.snd _ _).comp e.toRingHom)
  have hl : Nat.card { x : ZMod n // x ^ 2 = (e (a : ZMod (n * m))).1 } ≤ r := by
    simpa only [IsUnit.unit_spec] using hroot h1.unit
  have hr :
    Nat.card { x : ZMod m // x ^ 2 = (e (a : ZMod (n * m))).2 } ≤ 2 ^ m.primeFactors.card := by
    simpa only [IsUnit.unit_spec] using card_sq_roots_odd_le_primeFactors hm h2.unit
  exact (card_sq_roots_coprime_mul_le hcop (a : ZMod (n * m))).trans (Nat.mul_le_mul hl hr)

/-- Uniform bound for the square roots of a unit modulo a power of two.
At exponents zero and one the bound is one, at exponent two it is two, and thereafter
it is four. This coefficient combines with the odd-modulus bound by CRT. -/
def twoPowerSquareRootBound (v : ℕ) : ℕ :=
  match v with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | _ => 4

/-- A unit modulo two to the supplied exponent times an odd nonzero modulus has at
most the local two-power bound times two to the number of odd prime factors many
square roots. Coprimality follows from oddness; apply the local sharp bound and CRT.
This certifies the refined square-root coefficient for every two-adic exponent. -/
theorem card_sq_roots_two_pow_mul_odd_le {m : ℕ} [NeZero m] (v : ℕ) (hm : Odd m)
    (a : (ZMod (2 ^ v * m))ˣ) :
    Nat.card { z : ZMod (2 ^ v * m) // z ^ 2 = (a : ZMod (2 ^ v * m)) } ≤
      twoPowerSquareRootBound v * 2 ^ m.primeFactors.card := by
  apply
    card_sq_roots_coprime_odd_mul_le
      ((Nat.prime_two.coprime_iff_not_dvd.mpr hm.not_two_dvd_nat).pow_left v) hm
  intro b
  rcases v with _ | _ | _ | v <;>
    simpa only [twoPowerSquareRootBound] using card_sq_roots_two_power_sharp _ b

/-- For twice an odd nonzero modulus, each unit has at most two to the number
of odd prime factors many square roots. The factor modulo two has at most one root.
This gives the refined square-root coefficient when the two-adic exponent is one. -/
theorem card_sq_roots_two_mul_odd_le {m : ℕ} [NeZero m] (hm : Odd m) (a : (ZMod (2 * m))ˣ) :
    Nat.card { x : ZMod (2 * m) // x ^ 2 = (a : ZMod (2 * m)) } ≤ 2 ^ m.primeFactors.card := by
  have hs :=
    card_sq_roots_coprime_odd_mul_le (Nat.prime_two.coprime_iff_not_dvd.mpr hm.not_two_dvd_nat) hm
      (fun b ↦ card_sq_roots_two_power_sharp 1 b) a
  simpa only [one_mul] using hs

/-- For four times an odd nonzero modulus, each unit has at most twice two to the
number of odd prime factors many square roots. The factor modulo four has at most two roots.
This gives the refined square-root coefficient when the two-adic exponent is two. -/
theorem card_sq_roots_four_mul_odd_le {m : ℕ} [NeZero m] (hm : Odd m) (a : (ZMod (4 * m))ˣ) :
    Nat.card { x : ZMod (4 * m) // x ^ 2 = (a : ZMod (4 * m)) } ≤ 2 * 2 ^ m.primeFactors.card := by
  exact
    card_sq_roots_coprime_odd_mul_le
      ((Nat.prime_two.coprime_iff_not_dvd.mpr hm.not_two_dvd_nat).pow_left 2) hm
      (fun b ↦ card_sq_roots_two_power_sharp 2 b) a

/-- For modulus greater than two, a unit is distinct from its negative.
Cancellation would otherwise make minus one equal one, forcing modulus one or two.
This excludes fixed points in the square-root pairing. -/
private theorem unit_neg_ne_self_of_two_lt {q : ℕ} (hq : 2 < q) (u : (ZMod q)ˣ) :
    -(u : ZMod q) ≠ (u : ZMod q) := by
  have hn : (-1 : ZMod q) ≠ 1 := by
    intro h
    rcases ZMod.neg_one_eq_one_iff.mp h with h1 | h2
    · exact (by norm_num only : ¬(2 : ℕ) < 1) (h1 ▸ hq)
    · exact (lt_irrefl 2) (h2 ▸ hq)
  intro h
  apply hn
  apply u.isUnit.mul_right_cancel
  rw [neg_one_mul, one_mul]
  exact h

/-- For a unit modulo a nonzero modulus greater than two, negation exchanges
the strict lower half of the representatives with its complement.
A unit cannot be zero or lie at the midpoint; its negative has value `q - val`.
This gives the pairing used to count square roots in each half period. -/
theorem unit_neg_val_lower_half_iff {q : ℕ} [NeZero q] (hq : 2 < q) {x : ZMod q} (hu : IsUnit x) :
    2 * (-x).val < q ↔ ¬2 * x.val < q := by
  have hn : -x ≠ x := by simpa only [IsUnit.unit_spec] using unit_neg_ne_self_of_two_lt hq hu.unit
  have hx0 : x ≠ 0 := by
    intro h
    apply hn
    rw [h, neg_zero]
  have hmid : 2 * x.val ≠ q := fun h ↦ hn ((ZMod.neg_eq_self_iff x).mpr (Or.inr h))
  have hs : (-x).val + x.val = q := by
    rw [ZMod.neg_val, ite_eq_right hx0]
    exact Nat.sub_add_cancel x.val_le
  constructor
  · intro hl hx
    nlinarith only [hl, hx, hs]
  · intro h
    have hgt : q < 2 * x.val := lt_of_le_of_ne (Nat.le_of_not_gt h) hmid.symm
    nlinarith only [hgt, hs]

open Classical in
/-- For a unit residue and modulus greater than two, exactly half the square roots
have representatives strictly below half the modulus.
Negation preserves the root equation and bijects the lower half with its complement.
The resulting cardinality identity supports the half-period square-weight bound. -/
theorem two_mul_card_sq_roots_lower_half {q : ℕ} [NeZero q] (hq : 2 < q) (a : (ZMod q)ˣ) :
    2 *
        (Finset.univ.filter
            (fun x : { x : ZMod q // x ^ 2 = (a : ZMod q) } ↦ 2 * x.val.val < q)).card =
      Nat.card { x : ZMod q // x ^ 2 = (a : ZMod q) } := by
  let R := { x : ZMod q // x ^ 2 = (a : ZMod q) }
  let P := fun x : R ↦ 2 * x.val.val < q
  let f : R → R := fun x ↦ ⟨-x.val, by rw [neg_sq, x.property]⟩
  have hf (x : R) : P (f x) ↔ ¬P x := by
    exact
      unit_neg_val_lower_half_iff hq
        ((isUnit_pow_iff (by norm_num only : (2 : ℕ) ≠ 0)).mp (x.property.symm ▸ a.isUnit))
  have hff (x : R) : f (f x) = x := Subtype.ext (neg_neg x.val)
  have hc : (Finset.univ.filter P).card = (Finset.univ.filter (fun x : R ↦ ¬P x)).card := by
    apply Finset.card_bij (fun x _ ↦ f x)
    · intro x hx
      exact
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h ↦ (hf x).mp h (Finset.mem_filter.mp hx).2⟩
    · intro x _ y _ h
      have he := congrArg f h
      rw [hff, hff] at he
      exact he
    · intro y hy
      have hp : P (f y) := (hf y).mpr (Finset.mem_filter.mp hy).2
      exact ⟨f y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, hff y⟩
  have ht := Finset.card_filter_add_card_filter_not (s := Finset.univ) P
  rw [Finset.card_univ] at ht
  change 2 * (Finset.univ.filter P).card = Nat.card R
  rw [Nat.card_eq_fintype_card]
  nlinarith only [hc, ht]

/-- In one fixed quotient period, square roots satisfying a residue predicate
inject into the residue roots satisfying that predicate.
Equal residue and quotient recover the original natural number by division with remainder.
This separates interval counting from the lower and upper half-period root counts. -/
theorem card_sq_congruence_period_filter_le {q : ℕ} [NeZero q] (a : ZMod q) (k : ℕ)
    (P : ZMod q → Prop) :
    Nat.card { n : ℕ // n / q = k ∧ (n : ZMod q) ^ 2 = a ∧ P (n : ZMod q) } ≤
      Nat.card { x : { x : ZMod q // x ^ 2 = a } // P x.val } := by
  let f :
    { n : ℕ // n / q = k ∧ (n : ZMod q) ^ 2 = a ∧ P (n : ZMod q) } →
      { x : { x : ZMod q // x ^ 2 = a } // P x.val } :=
    fun n ↦ ⟨⟨(n.val : ZMod q), n.property.2.1⟩, n.property.2.2⟩
  have hf : Function.Injective f := by
    intro m n h
    apply Subtype.ext
    have hm : (m.val : ZMod q) = (n.val : ZMod q) := congrArg (fun r ↦ r.val.val) h
    have hd : m.val / q = n.val / q := m.property.1.trans n.property.1.symm
    have hr : m.val % q = n.val % q := by
      have hv := congrArg ZMod.val hm
      simpa only [ZMod.val_natCast] using hv
    calc
      m.val = m.val % q + q * (m.val / q) := (Nat.mod_add_div _ _).symm
      _ = n.val % q + q * (n.val / q) := by rw [hr, hd]
      _ = n.val := Nat.mod_add_div _ _
  exact Nat.card_le_card_of_injective f hf

/-- For modulus greater than two and a unit residue, twice the number of integer
roots in a fixed quotient period and its lower half is at most the residue-root count.
Inject roots into lower-half residue representatives and apply the exact pairing count.
This supplies the cardinality for lower half-period square-weight blocks. -/
theorem two_mul_card_sq_congruence_lower_half_period_le {q : ℕ} [NeZero q] (hq : 2 < q)
    (a : (ZMod q)ˣ) (k : ℕ) :
    2 * Nat.card { n : ℕ // n / q = k ∧ (n : ZMod q) ^ 2 = (a : ZMod q) ∧ 2 * (n % q) < q } ≤
      Nat.card { x : ZMod q // x ^ 2 = (a : ZMod q) } := by
  classical
  have hc := card_sq_congruence_period_filter_le (a : ZMod q) k (fun x ↦ 2 * x.val < q)
  have he :
    Nat.card { x : { x : ZMod q // x ^ 2 = (a : ZMod q) } // 2 * x.val.val < q } =
      (Finset.univ.filter
          (fun x : { x : ZMod q // x ^ 2 = (a : ZMod q) } ↦ 2 * x.val.val < q)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [he] at hc
  simp only [ZMod.val_natCast] at hc
  exact (Nat.mul_le_mul_left 2 hc).trans_eq (two_mul_card_sq_roots_lower_half hq a)

open Classical in
/-- For a unit residue and modulus greater than two, exactly half the square roots
lie in the complement of the strict lower half of representatives.
Subtract the lower-half count from the total count.
This is the complementary cardinality needed for upper half-period blocks. -/
theorem two_mul_card_sq_roots_upper_half {q : ℕ} [NeZero q] (hq : 2 < q) (a : (ZMod q)ˣ) :
    2 *
        (Finset.univ.filter
            (fun x : { x : ZMod q // x ^ 2 = (a : ZMod q) } ↦ ¬2 * x.val.val < q)).card =
      Nat.card { x : ZMod q // x ^ 2 = (a : ZMod q) } := by
  have hl := two_mul_card_sq_roots_lower_half hq a
  have ht :=
    Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : { x : ZMod q // x ^ 2 = (a : ZMod q) } ↦ 2 * x.val.val < q)
  rw [Finset.card_univ] at ht
  rw [Nat.card_eq_fintype_card] at hl ⊢
  nlinarith only [hl, ht]

/-- For modulus greater than two and a unit residue, twice the number of integer
roots in a fixed quotient period and its upper half is at most the residue-root count.
Inject roots into upper-half residue representatives and apply the complementary pairing count.
This supplies the cardinality for upper half-period square-weight blocks. -/
theorem two_mul_card_sq_congruence_upper_half_period_le {q : ℕ} [NeZero q] (hq : 2 < q)
    (a : (ZMod q)ˣ) (k : ℕ) :
    2 * Nat.card { n : ℕ // n / q = k ∧ (n : ZMod q) ^ 2 = (a : ZMod q) ∧ ¬2 * (n % q) < q } ≤
      Nat.card { x : ZMod q // x ^ 2 = (a : ZMod q) } := by
  classical
  have hc := card_sq_congruence_period_filter_le (a : ZMod q) k (fun x ↦ ¬2 * x.val < q)
  have he :
    Nat.card { x : { x : ZMod q // x ^ 2 = (a : ZMod q) } // ¬2 * x.val.val < q } =
      (Finset.univ.filter
          (fun x : { x : ZMod q // x ^ 2 = (a : ZMod q) } ↦ ¬2 * x.val.val < q)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [he] at hc
  simp only [ZMod.val_natCast] at hc
  exact (Nat.mul_le_mul_left 2 hc).trans_eq (two_mul_card_sq_roots_upper_half hq a)

end PseudoPrime.NumberTheory
