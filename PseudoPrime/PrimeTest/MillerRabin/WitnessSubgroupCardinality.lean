/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnitPowerCardinality
public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroup

/-! # Cardinality and index of the Miller–Rabin sign subgroup -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- For a nonzero modulus and distinct signs, if -1 has an E-power preimage, the sign
subgroup has twice the cardinality of the E-power kernel. Its two fibers are disjoint
and have equal cardinality by translation. Only one common sign is counted, which
prevents an erroneous independent-sign factor in a CRT product. -/
theorem card_signSubgroup_of_neg_one_mem_image {n E : ℕ} [NeZero n] (hne : (-1 : (ZMod n)ˣ) ≠ 1)
    (hroot : ∃ u : (ZMod n)ˣ, u ^ E = -1) :
    Nat.card (signSubgroup n E) = 2 * Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).ker := by
  classical
  have hd :
    Disjoint (Finset.univ.filter fun u : (ZMod n)ˣ ↦ u ^ E = 1)
      (Finset.univ.filter fun u : (ZMod n)ˣ ↦ u ^ E = -1) :=
    Finset.disjoint_filter.mpr fun u _ hpos hneg ↦ hne (hneg.symm.trans hpos)
  have hc :=
    MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ) (x :=
      (-1 : (ZMod n)ˣ)) (y := 1) hroot ⟨1, one_pow E⟩
  simp only [powMonoidHom_apply] at hc
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [signSubgroup, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_ofPred_eq]
  rw [Finset.filter_or, Finset.card_union_of_disjoint hd, hc, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  change _ = 2 * (Finset.univ.filter fun u : (ZMod n)ˣ ↦ u ^ E = 1).card
  exact (two_mul _).symm

/-- If the unit group is cyclic, the signs are distinct, and its E-power image has
even cardinality, the sign subgroup has index phi(n)/(2*gcd(phi(n),E)). The image
condition supplies a negative preimage; the two-fiber count and the cyclic kernel
formula then determine the index. This is the cyclic local index used in MR bounds. -/
theorem index_signSubgroup_of_cyclic_even_image {n E : ℕ} [NeZero n] [IsCyclic (ZMod n)ˣ]
    (hne : (-1 : (ZMod n)ˣ) ≠ 1) (heven : 2 ∣ n.totient / n.totient.gcd E) :
    (signSubgroup n E).index = n.totient / (2 * n.totient.gcd E) := by
  rw [Subgroup.index_eq_card_div,
    card_signSubgroup_of_neg_one_mem_image hne
      (NumberTheory.exists_unit_pow_eq_neg_one_of_even_image hne heven),
    IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- The Fermat subgroup is exactly the kernel of the (n-1)-power map on units.
Unfolding both membership predicates identifies them. This lets power-kernel
cardinality formulas supply its index without duplicating the group calculation. -/
theorem fermatSubgroup_eq_powerKernel (n : ℕ) :
    fermatSubgroup n = (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker := by
  ext u
  simp only [fermatSubgroup, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_ofPred_eq, MonoidHom.mem_ker, powMonoidHom_apply]

/-- For an odd prime p and positive exponent a, the Fermat subgroup modulo p^a
has index p^(a-1). Cyclicity, the local power-kernel cardinality, and the gcd of
the totient with p^a-1 determine the quotient. This handles the prime-power MR branch. -/
theorem index_fermatSubgroup_prime_pow {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) :
    (fermatSubgroup (p ^ a)).index = p ^ (a - 1) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  rw [Subgroup.index_eq_card_div, fermatSubgroup_eq_powerKernel,
    NumberTheory.card_unitPowerKernel_prime_pow hp hp2 ha,
    NumberTheory.gcd_totient_prime_pow_sub_one hp ha, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime_pow hp ha,
    Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hp.one_lt)]

/-- For an odd prime-power composite p^a other than 9, the Fermat subgroup has
index at least four. The index formula is at least p when p exceeds 3; for p=3,
excluding 9 forces a at least 3. This supplies the uniform MR index bound in this branch. -/
theorem four_le_index_fermatSubgroup_prime_pow {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 2 ≤ a)
    (hn9 : p ^ a ≠ 9) : 4 ≤ (fermatSubgroup (p ^ a)).index := by
  rw [index_fermatSubgroup_prime_pow hp hp2 (lt_of_lt_of_le (by decide : 0 < 2) ha)]
  have hp3 : 3 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hp.two_le hp2.symm)
  by_cases heq : p = 3
  · have ha2 : a ≠ 2 := by
      intro h
      apply hn9
      rw [heq, h]
      rfl
    have ha3 : 3 ≤ a := Nat.succ_le_of_lt (lt_of_le_of_ne ha ha2.symm)
    have hex : 2 ≤ a - 1 := Nat.sub_le_sub_right ha3 1
    have hpow := Nat.pow_le_pow_right hp.pos hex
    rw [heq] at hpow ⊢
    exact le_trans (by decide : 4 ≤ 3 ^ 2) hpow
  · have hp4 : 4 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hp3 (Ne.symm heq))
    have hex : 1 ≤ a - 1 := Nat.sub_le_sub_right ha 1
    exact hp4.trans (Nat.le_self_pow (Nat.ne_zero_of_lt hex) p)

/-- For coprime moduli with distinct global signs and local negative E-power
preimages, the global sign subgroup has twice the product of the local E-power
kernel cardinalities. CRT multiplies the kernels and lifts one common negative
sign. This preserves the factor two required by the MR index formula. -/
theorem card_signSubgroup_coprime_mul {m n E : ℕ} [NeZero (m * n)] (hc : m.Coprime n)
    (hne : (-1 : (ZMod (m * n))ˣ) ≠ 1) (hm : ∃ u : (ZMod m)ˣ, u ^ E = -1)
    (hn : ∃ v : (ZMod n)ˣ, v ^ E = -1) :
    Nat.card (signSubgroup (m * n) E) =
      2 *
        (Nat.card (powMonoidHom E : (ZMod m)ˣ →* (ZMod m)ˣ).ker *
          Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).ker) := by
  rw [card_signSubgroup_of_neg_one_mem_image hne
      (NumberTheory.exists_unit_pow_eq_neg_one_coprime_mul hc hm hn),
    NumberTheory.card_unitPowerKernel_coprime_mul hc]

/-- For coprime moduli with cyclic unit groups and even local E-power images,
the global sign subgroup has index phi(m)*phi(n)/(2*gcd(phi(m),E)*gcd(phi(n),E)).
Distinct local signs and m*n>2 permit the two-fiber count; CRT and cyclic kernel
cardinalities then yield the exact index for the two-factor MR branch. -/
theorem index_signSubgroup_coprime_mul_of_cyclic_even_images {m n E : ℕ} [NeZero m] [NeZero n]
    [NeZero (m * n)] [IsCyclic (ZMod m)ˣ] [IsCyclic (ZMod n)ˣ] (hc : m.Coprime n) (hgt : 2 < m * n)
    (hmne : (-1 : (ZMod m)ˣ) ≠ 1) (hnne : (-1 : (ZMod n)ˣ) ≠ 1)
    (hme : 2 ∣ m.totient / m.totient.gcd E) (hne : 2 ∣ n.totient / n.totient.gcd E) :
    (signSubgroup (m * n) E).index =
      (m.totient * n.totient) / (2 * (m.totient.gcd E * n.totient.gcd E)) := by
  let : Fact (2 < m * n) := ⟨hgt⟩
  have hsign : (-1 : (ZMod (m * n))ˣ) ≠ 1 := by
    intro h
    apply ZMod.neg_one_ne_one (n := m * n)
    exact congrArg Units.val h
  rw [Subgroup.index_eq_card_div,
    card_signSubgroup_coprime_mul hc hsign
      (NumberTheory.exists_unit_pow_eq_neg_one_of_even_image hmne hme)
      (NumberTheory.exists_unit_pow_eq_neg_one_of_even_image hnne hne),
    IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_mul hc]

/-- With coprime nonzero moduli, distinct global signs, and local negative
E-power preimages, twice the global sign-subgroup index equals the product of the
local power-image cardinalities. Multiply the kernel-image identities and cancel
the nonzero kernel cardinalities. This avoids division in the MR index comparison. -/
theorem two_mul_index_signSubgroup_coprime_mul {m n E : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hc : m.Coprime n) (hne : (-1 : (ZMod (m * n))ˣ) ≠ 1) (hm : ∃ u : (ZMod m)ˣ, u ^ E = -1)
    (hn : ∃ v : (ZMod n)ˣ, v ^ E = -1) :
    2 * (signSubgroup (m * n) E).index =
      Nat.card (powMonoidHom E : (ZMod m)ˣ →* (ZMod m)ˣ).range *
        Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).range := by
  let K := Nat.card (powMonoidHom E : (ZMod m)ˣ →* (ZMod m)ˣ).ker
  let L := Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).ker
  let A := Nat.card (powMonoidHom E : (ZMod m)ˣ →* (ZMod m)ˣ).range
  let B := Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).range
  have hcard := (signSubgroup (m * n) E).card_mul_index
  rw [card_signSubgroup_coprime_mul hc hne hm hn, Nat.card_eq_fintype_card (α := (ZMod (m * n))ˣ),
    ZMod.card_units_eq_totient, Nat.totient_mul hc] at hcard
  have hmcard := Subgroup.card_ker_mul_card_range (powMonoidHom E : (ZMod m)ˣ →* (ZMod m)ˣ)
  have hncard := Subgroup.card_ker_mul_card_range (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ)
  rw [Nat.card_eq_fintype_card (α := (ZMod m)ˣ), ZMod.card_units_eq_totient] at hmcard
  rw [Nat.card_eq_fintype_card (α := (ZMod n)ˣ), ZMod.card_units_eq_totient] at hncard
  have heq : (K * L) * (2 * (signSubgroup (m * n) E).index) = (K * L) * (A * B) := by
    calc
      _ = (2 * (K * L)) * (signSubgroup (m * n) E).index := by ring
      _ = m.totient * n.totient := hcard
      _ = (K * A) * (L * B) := congrArg₂ (· * ·) hmcard.symm hncard.symm
      _ = _ := by ring
  exact
    Nat.eq_of_mul_eq_mul_left
      (Nat.mul_pos (Nat.card_pos (α := (powMonoidHom E : (ZMod m)ˣ →* (ZMod m)ˣ).ker))
        (Nat.card_pos (α := (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).ker)))
      heq

/-- If both local power images have at least two elements and one has at least
four, the sign subgroup of their coprime product has index at least four, provided
the global signs are distinct and the negative fibers exist. The exact twice-index
identity converts the local bounds into the uniform MR index lower bound. -/
theorem four_le_index_signSubgroup_coprime_mul {m n E : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hc : m.Coprime n) (hne : (-1 : (ZMod (m * n))ˣ) ≠ 1) (hm : ∃ u : (ZMod m)ˣ, u ^ E = -1)
    (hn : ∃ v : (ZMod n)ˣ, v ^ E = -1)
    (hA : 2 ≤ Nat.card (powMonoidHom E : (ZMod m)ˣ →* (ZMod m)ˣ).range)
    (hB : 2 ≤ Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).range)
    (hlarge :
      4 ≤ Nat.card (powMonoidHom E : (ZMod m)ˣ →* (ZMod m)ˣ).range ∨
        4 ≤ Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).range) :
    4 ≤ (signSubgroup (m * n) E).index := by
  have heq := two_mul_index_signSubgroup_coprime_mul hc hne hm hn
  have hprod :
    8 ≤
      Nat.card (powMonoidHom E : (ZMod m)ˣ →* (ZMod m)ˣ).range *
        Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).range := by
    rcases hlarge with hlarge | hlarge
    · exact Nat.mul_le_mul hlarge hB
    · exact Nat.mul_le_mul hA hlarge
  linarith only [heq, hprod]

/-- A positive even cardinality different from two is at least four.
Write it as twice a positive integer and exclude the multiplier one.
This converts even power-image cardinalities into the MR index lower bound. -/
private theorem four_of_even_ne_two {c : ℕ} (hpos : 0 < c) (heven : 2 ∣ c) (hne : c ≠ 2) :
    4 ≤ c := by
  obtain ⟨k, hk⟩ := heven
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hk
    exact hpos.ne' hk
  have hk1 : k ≠ 1 := by
    intro h
    apply hne
    rw [hk, h, mul_one]
  have hk2 : 2 ≤ k :=
    Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hk0) (Ne.symm hk1))
  rw [hk]
  exact Nat.mul_le_mul_left 2 hk2

/-- For distinct odd primes p<q, if 2*E divides p*q-1 and both local power images
are even, the sign subgroup modulo p*q has index at least four. A two-element
image at q would force q-1 to divide p*q-1, which is impossible for p<q.
The common-sign CRT index identity then gives the bound for the squarefree two-prime branch. -/
theorem four_le_index_signSubgroup_two_primes {p q E : ℕ} [NeZero p] [NeZero q] [NeZero (p * q)]
    (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p < q) (hE : 2 * E ∣ p * q - 1)
    (hpe : 2 ∣ p.totient / p.totient.gcd E) (hqe : 2 ∣ q.totient / q.totient.gcd E) :
    4 ≤ (signSubgroup (p * q) E).index := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hgt : 2 < p * q := by nlinarith only [hp.two_le, hq.two_le]
  let : Fact (2 < p * q) := ⟨hgt⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le hp2.symm⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le hq2.symm⟩
  have hpne : (-1 : (ZMod p)ˣ) ≠ 1 := fun h ↦ ZMod.neg_one_ne_one (n := p) (congrArg Units.val h)
  have hqne : (-1 : (ZMod q)ˣ) ≠ 1 := fun h ↦ ZMod.neg_one_ne_one (n := q) (congrArg Units.val h)
  have hnne : (-1 : (ZMod (p * q))ˣ) ≠ 1 := fun h ↦
    ZMod.neg_one_ne_one (n := p * q) (congrArg Units.val h)
  have hpc : 2 ∣ Nat.card (powMonoidHom E : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
    rw [IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact hpe
  have hqc : 2 ∣ Nat.card (powMonoidHom E : (ZMod q)ˣ →* (ZMod q)ˣ).range := by
    rw [IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact hqe
  have hqnot : Nat.card (powMonoidHom E : (ZMod q)ˣ →* (ZMod q)ˣ).range ≠ 2 := by
    intro h
    have hd := NumberTheory.totient_dvd_exponent_mul_card_unitPowerImage (n := q) (E := E)
    rw [h, Nat.totient_prime hq, Nat.mul_comm E 2] at hd
    exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq (hd.trans hE)
  apply
    four_le_index_signSubgroup_coprime_mul
      (hp.coprime_iff_not_dvd.mpr fun h ↦
        (ne_of_lt hpq) ((hq.eq_one_or_self_of_dvd p h).resolve_left hp.ne_one))
      hnne (NumberTheory.exists_unit_pow_eq_neg_one_of_even_image hpne hpe)
      (NumberTheory.exists_unit_pow_eq_neg_one_of_even_image hqne hqe)
      (Nat.le_of_dvd Nat.card_pos hpc) (Nat.le_of_dvd Nat.card_pos hqc)
  exact Or.inr (four_of_even_ne_two Nat.card_pos hqc hqnot)

/-- For a nonzero modulus with distinct signs and a negative E-power preimage,
twice the sign-subgroup index equals the cardinality of the E-power image.
Use the two equal fibers and cancel the positive kernel cardinality from the
kernel-image identity. This converts global small-image classifications into MR index bounds. -/
theorem two_mul_index_signSubgroup_of_neg_one_mem_image {n E : ℕ} [NeZero n]
    (hne : (-1 : (ZMod n)ˣ) ≠ 1) (hroot : ∃ u : (ZMod n)ˣ, u ^ E = -1) :
    2 * (signSubgroup n E).index = Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).range := by
  let K := Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).ker
  have hcard := (signSubgroup n E).card_mul_index
  rw [card_signSubgroup_of_neg_one_mem_image hne hroot] at hcard
  have hkr := Subgroup.card_ker_mul_card_range (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ)
  have heq :
    K * (2 * (signSubgroup n E).index) =
      K * Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).range := by
    calc
      _ = (2 * K) * (signSubgroup n E).index := by ring
      _ = Nat.card (ZMod n)ˣ := hcard
      _ = _ := hkr.symm
  exact
    Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).ker))
      heq

end PseudoPrime.PrimeTest
