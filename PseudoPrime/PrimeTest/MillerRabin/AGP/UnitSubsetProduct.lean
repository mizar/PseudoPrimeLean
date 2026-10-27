/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import PseudoPrime.Combinatorics.Additive.FiniteAbelianZeroSum

/-! # Prime subsets with product one in a modular unit group

This file specializes the finite abelian group zero-sum theorem to units modulo
an integer, using the Carmichael function to bound the exponent.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.MillerRabin.AGP

open PseudoPrime.Combinatorics.Additive.FiniteAbelianZeroSum in
/--
Inputs: `L > 2`, a finite set `P` of integers coprime to `L`, and
`#P > λ(L) log L`.

Claim: some nonempty subset of `P` has product one in `(ZMod L)ˣ`.

Content: the unit group has exponent `λ(L)` and at most `L` characters, so the
label-preserving Fourier zero-sum theorem applies to the list of elements of
`P`.

Proof: identify the exponent with the Carmichael function, bound the character
count by the size of the unit group, then convert the selected zero-sum labels
to a product identity.

Role: supplies the modular product condition used by the AGP Korselt
construction.
-/
theorem exists_nonempty_unit_product_eq_one_of_card_gt_carmichael_log (L : ℕ) [NeZero L]
    (hL : 2 < L) (hlambda : 3 ≤ ArithmeticFunction.carmichael L)
    [NeZero (ArithmeticFunction.carmichael L)] (P : Finset ℕ) (hcoprime : ∀ p ∈ P, Nat.Coprime p L)
    (hlarge : (ArithmeticFunction.carmichael L : ℝ) * Real.log L < P.card) :
    ∃ U : Finset ℕ,
      U ⊆ P ∧
        U.Nonempty ∧
        (∏ p ∈ U, (if h : Nat.Coprime p L then ZMod.unitOfCoprime p h else 1)) = 1 ∧
        (∏ p ∈ U, (p : ZMod L)) = 1 ∧ ∀ p ∈ U, Nat.Coprime p L := by
  classical
  have hLpos : 0 < L := Nat.lt_trans (by decide : 0 < 2) hL
  let m := ArithmeticFunction.carmichael L
  have hmpos : 0 < m := by
    dsimp [m]
    exact Nat.lt_of_lt_of_le (by decide : 0 < 3) hlambda
  have hmN : m ≤ L := by
    dsimp [m]
    exact
      Nat.le_trans
        (Nat.le_of_dvd (Nat.totient_pos.mpr hLpos) (ArithmeticFunction.carmichael_dvd_totient L))
        (Nat.totient_le L)
  let G := Additive (Units (ZMod L))
  have hzero : ∀ x : G, m • x = 0 := by
    intro x
    rw [show m = AddMonoid.exponent G by
        dsimp [m, G]
        exact
          (ArithmeticFunction.carmichael_eq_exponent' L).trans
            (AddMonoid.exponent_additive (G := Units (ZMod L))).symm]
    exact AddMonoid.exponent_nsmul_eq_zero x
  have hcharCard : Fintype.card (AddChar G ℂ) ≤ L := by
    calc
      Fintype.card (AddChar G ℂ) = Fintype.card G := AddChar.card_eq
      _ = Fintype.card (Units (ZMod L)) := Fintype.card_congr Additive.toMul
      _ ≤ L - 1 := Nat.card_units_zmod_lt_sub_one (by exact Nat.lt_trans (by decide : 1 < 2) hL)
      _ ≤ L := Nat.sub_le L 1
  have hchars : (Finset.univ : Finset (AddChar G ℂ)).card ≤ L := by
    simpa only [Finset.card_univ] using hcharCard
  have hlen : (m : ℝ) * Real.log L < P.toList.length := by
    rw [Finset.length_toList]
    exact hlarge
  have hm3 : 3 ≤ m := by simpa only [m] using hlambda
  let unitMap : ℕ → Units (ZMod L) := fun p =>
    if h : Nat.Coprime p L then ZMod.unitOfCoprime p h else 1
  obtain ⟨U, hUNe, hUP, hsum⟩ :=
    exists_nonempty_zero_sum_label_subset_of_long_list m L L hm3 hmN (by rfl) hzero hchars P.toList
      (Finset.nodup_toList P) (fun p => Additive.ofMul (unitMap p)) hlen
  have hprod := prod_eq_one_of_additive_sum_eq_zero U (fun p => unitMap p) hsum
  refine ⟨U, ?_, hUNe, ?_, ?_, ?_⟩
  · intro p hp
    have hpin : p ∈ P.toList.toFinset := hUP p hp
    simpa only [Finset.toList_toFinset] using hpin
  · have hprod' : (∏ p ∈ U, unitMap p) = 1 := hprod
    rw [show
        (∏ p ∈ U, unitMap p) =
          (∏ p ∈ U, (if h : Nat.Coprime p L then ZMod.unitOfCoprime p h else 1))
        by
        apply Finset.prod_congr rfl
        intro p hp
        dsimp [unitMap]]
    exact hprod'
  · have hval : ∀ p ∈ U, (unitMap p : ZMod L) = (p : ZMod L) := by
      intro p hp
      have hpP : p ∈ P := by
        have hpin : p ∈ P.toList.toFinset := hUP p hp
        simpa only [Finset.toList_toFinset] using hpin
      dsimp [unitMap]
      rw [dite_eq_left (hcoprime p hpP)]
      exact ZMod.coe_unitOfCoprime p (hcoprime p hpP)
    calc
      (∏ p ∈ U, (p : ZMod L)) = ∏ p ∈ U, (unitMap p : ZMod L) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact (hval p hp).symm
      _ = (∏ p ∈ U, unitMap p : Units (ZMod L)) := by
        symm
        exact map_prod (Units.coeHom (ZMod L)) unitMap U
      _ = 1 := congrArg (Units.coeHom (ZMod L)) hprod
  · intro p hp
    have hpP : p ∈ P := by
      have hpin : p ∈ P.toList.toFinset := hUP p hp
      simpa only [Finset.toList_toFinset] using hpin
    exact hcoprime p hpP

open PseudoPrime.Combinatorics.Additive.FiniteAbelianZeroSum in
/--
Inputs: a finite set `P` of integers coprime to `L`, an excluded label `x`,
and `#P > λ(L) log L`.

Claim: after removing `x`, a nonempty subset has product one in
`(ZMod L)ˣ`, with the same residue identity in `ZMod L`.

Content: the sharp prefix-tail length has room for one removed label under the
AGP cardinality threshold.

Proof: compare the paper95 prefix-tail length with `floor(λ(L) log L)`, use
the strict cardinality bound to absorb the deletion, and apply the
label-preserving zero-sum theorem.

Role: this is the subset-product input with the exceptional prime removed as
in reliable.pdf Proposition 1.3.
-/
theorem exists_nonempty_unit_product_eq_one_of_card_gt_carmichael_log_erase (L : ℕ) [NeZero L]
    (hL : 2 < L) (hlambda : 3 ≤ ArithmeticFunction.carmichael L)
    [NeZero (ArithmeticFunction.carmichael L)] (P : Finset ℕ) (hcoprime : ∀ p ∈ P, Nat.Coprime p L)
    (x : ℕ) (hlarge : (ArithmeticFunction.carmichael L : ℝ) * Real.log L < P.card) :
    ∃ U : Finset ℕ,
      U ⊆ P.erase x ∧
        U.Nonempty ∧
        (∏ p ∈ U, (if h : Nat.Coprime p L then ZMod.unitOfCoprime p h else 1)) = 1 ∧
        (∏ p ∈ U, (p : ZMod L)) = 1 ∧ ∀ p ∈ U, Nat.Coprime p L := by
  classical
  have hLpos : 0 < L := Nat.lt_trans (by decide : 0 < 2) hL
  let m := ArithmeticFunction.carmichael L
  have hmN : m ≤ L := by
    dsimp [m]
    exact
      Nat.le_trans
        (Nat.le_of_dvd (Nat.totient_pos.mpr hLpos) (ArithmeticFunction.carmichael_dvd_totient L))
        (Nat.totient_le L)
  let G := Additive (Units (ZMod L))
  have hzero : ∀ y : G, m • y = 0 := by
    intro y
    rw [show m = AddMonoid.exponent G by
        dsimp [m, G]
        exact
          (ArithmeticFunction.carmichael_eq_exponent' L).trans
            (AddMonoid.exponent_additive (G := Units (ZMod L))).symm]
    exact AddMonoid.exponent_nsmul_eq_zero y
  have hcharCard : Fintype.card (AddChar G ℂ) ≤ L := by
    calc
      Fintype.card (AddChar G ℂ) = Fintype.card G := AddChar.card_eq
      _ = Fintype.card (Units (ZMod L)) := Fintype.card_congr Additive.toMul
      _ ≤ L - 1 := Nat.card_units_zmod_lt_sub_one (by exact Nat.lt_trans (by decide : 1 < 2) hL)
      _ ≤ L := Nat.sub_le L 1
  have hchars : (Finset.univ : Finset (AddChar G ℂ)).card ≤ L := by
    simpa only [Finset.card_univ] using hcharCard
  have hm3 : 3 ≤ m := by simpa only [m] using hlambda
  have hfloor : Nat.floor ((m : ℝ) * Real.log L) < P.card := by
    apply (Nat.floor_lt (by positivity)).2
    exact_mod_cast hlarge
  have hneeded : Nat.floor ((m : ℝ) * Real.log ((L : ℝ) / m)) + m ≤ P.card - 1 :=
    (log_length_with_tail_le_floor_log m L L hm3 hmN (by rfl)).trans (Nat.le_sub_one_of_lt hfloor)
  have herase : P.card - 1 ≤ (P.erase x).card := by
    by_cases hx : x ∈ P
    · rw [Finset.card_erase_of_mem hx]
    · rw [Finset.erase_eq_of_notMem hx]
      exact Nat.sub_le P.card 1
  have hlen : Nat.floor ((m : ℝ) * Real.log ((L : ℝ) / m)) + m ≤ (P.erase x).toList.length := by
    rw [Finset.length_toList]
    exact hneeded.trans herase
  let unitMap : ℕ → Units (ZMod L) := fun p =>
    if h : Nat.Coprime p L then ZMod.unitOfCoprime p h else 1
  obtain ⟨U, hUNe, hUP, hsum⟩ :=
    exists_nonempty_zero_sum_label_subset_of_segmented_length m L
      (Nat.lt_of_lt_of_le (by decide : 0 < 3) hm3) hmN hzero hchars (P.erase x).toList
      (Finset.nodup_toList (P.erase x)) (fun p => Additive.ofMul (unitMap p)) hlen
  have hprod := prod_eq_one_of_additive_sum_eq_zero U (fun p => unitMap p) hsum
  have hUP' : ∀ p ∈ U, p ∈ P.erase x := by
    intro p hp
    have hpin : p ∈ (P.erase x).toList.toFinset := hUP p hp
    simpa only [Finset.toList_toFinset] using hpin
  refine ⟨U, ?_, hUNe, ?_, ?_, ?_⟩
  · intro p hp
    exact hUP' p hp
  · have hprod' : (∏ p ∈ U, unitMap p) = 1 := hprod
    rw [show
        (∏ p ∈ U, unitMap p) =
          (∏ p ∈ U, (if h : Nat.Coprime p L then ZMod.unitOfCoprime p h else 1))
        by
        apply Finset.prod_congr rfl
        intro p hp
        dsimp [unitMap]]
    exact hprod'
  · have hval : ∀ p ∈ U, (unitMap p : ZMod L) = (p : ZMod L) := by
      intro p hp
      have hpP : p ∈ P := (Finset.mem_erase.mp (hUP' p hp)).2
      dsimp [unitMap]
      rw [dite_eq_left (hcoprime p hpP)]
      exact ZMod.coe_unitOfCoprime p (hcoprime p hpP)
    calc
      (∏ p ∈ U, (p : ZMod L)) = ∏ p ∈ U, (unitMap p : ZMod L) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact (hval p hp).symm
      _ = (∏ p ∈ U, unitMap p : Units (ZMod L)) := by
        symm
        exact map_prod (Units.coeHom (ZMod L)) unitMap U
      _ = 1 := congrArg (Units.coeHom (ZMod L)) hprod
  · intro p hp
    exact hcoprime p ((Finset.mem_erase.mp (hUP' p hp)).2)

/--
Inputs: `p = d * k + 1`, `d ∣ L`, and `k` coprime to `L`.

Claim: if the unit represented by `p` is one modulo `L`, then
`p = k * L + 1`.

Content: the unit equality gives `L ∣ p - 1`; coprimality cancels `k`, and
the two divisibilities between `d` and `L` force equality.

Proof: convert the `ZMod` equality to a natural congruence, cancel the coprime
factor, and compare `d ∣ L` with the resulting `L ∣ d`.

Role: identifies the unique progression prime excluded in Proposition 1.3.
-/
theorem eq_exception_of_unit_eq_one_of_progression {L k d p : ℕ} (hkL : Nat.Coprime k L)
    (hdL : d ∣ L) (hp : p = d * k + 1) (hcoprime : Nat.Coprime p L)
    (hunit : ZMod.unitOfCoprime p hcoprime = 1) : p = k * L + 1 := by
  have hcast := congrArg (fun u : Units (ZMod L) => (u : ZMod L)) hunit
  rw [ZMod.coe_unitOfCoprime p hcoprime, Units.val_one] at hcast
  have hmod : p ≡ 1 [MOD L] :=
    (ZMod.natCast_eq_natCast_iff p 1 L).mp (hcast.trans (Nat.cast_one.symm))
  have hpone : 1 ≤ p := by
    rw [hp]
    exact Nat.le_add_left 1 (d * k)
  have hLd : L ∣ p - 1 := by
    have hmod' : 1 ≡ p [MOD L] := hmod.symm
    exact (Nat.modEq_iff_dvd' hpone).mp hmod'
  have hLd' : L ∣ d * k := by
    rw [hp, Nat.add_sub_cancel] at hLd
    exact hLd
  have hLdvdD : L ∣ d := (hkL.symm.dvd_mul_right).mp hLd'
  have hdEq : d = L := Nat.dvd_antisymm hdL hLdvdD
  rw [hp, hdEq]
  ac_rfl

/--
Inputs: a sufficiently large finite set `P` of labels coprime to `L`, with
each label equal to `d * k + 1` for some `d ∣ L`, and `k` coprime to `L`.

Claim: after excluding `k * L + 1`, a subset of at least two labels has
product one modulo `L`.

Content: any singleton with unit product one would have to be the excluded
exceptional label.

Proof: apply the erased subset-product theorem and rule out cardinalities zero
and one using nonemptiness and the progression lemma.

Role: supplies the composite-product input for the Carmichael construction.
-/
theorem exists_two_or_more_unit_product_eq_one_of_progression (L : ℕ) [NeZero L] (hL : 2 < L)
    (hlambda : 3 ≤ ArithmeticFunction.carmichael L) [NeZero (ArithmeticFunction.carmichael L)]
    (P : Finset ℕ) (k : ℕ) (hkL : Nat.Coprime k L) (hcoprime : ∀ p ∈ P, Nat.Coprime p L)
    (hprogression : ∀ p ∈ P, ∃ d, d ∣ L ∧ p = d * k + 1)
    (hlarge : (ArithmeticFunction.carmichael L : ℝ) * Real.log L < P.card) :
    ∃ U : Finset ℕ,
      U ⊆ P.erase (k * L + 1) ∧
        2 ≤ U.card ∧
        (∏ p ∈ U, (if h : Nat.Coprime p L then ZMod.unitOfCoprime p h else 1)) = 1 ∧
        (∏ p ∈ U, (p : ZMod L)) = 1 := by
  obtain ⟨U, hUP, hUn, hprod, hres, _⟩ :=
    exists_nonempty_unit_product_eq_one_of_card_gt_carmichael_log_erase L hL hlambda P hcoprime
      (k * L + 1) hlarge
  have hcard : 2 ≤ U.card := by
    by_contra hnot
    have hlt : U.card < 2 := Nat.lt_of_not_ge hnot
    have hle : U.card ≤ 1 := Nat.le_of_lt_succ hlt
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hz | hone
    · obtain ⟨q, hq⟩ := hUn
      rw [Finset.card_eq_zero.mp hz] at hq
      exact Finset.notMem_empty q hq
    · obtain ⟨q, hUeq⟩ := Finset.card_eq_one.mp hone
      have hqU : q ∈ U := by
        rw [hUeq]
        simp only [Finset.mem_singleton]
      have hqP : q ∈ P := (Finset.mem_erase.mp (hUP hqU)).2
      obtain ⟨d, hd, hform⟩ := hprogression q hqP
      have hqunit : ZMod.unitOfCoprime q (hcoprime q hqP) = 1 := by
        have hqprod := hprod
        rw [hUeq, Finset.prod_singleton, dite_eq_left (hcoprime q hqP)] at hqprod
        exact hqprod
      have hqexception :=
        eq_exception_of_unit_eq_one_of_progression hkL hd hform (hcoprime q hqP) hqunit
      exact (Finset.mem_erase.mp (hUP hqU)).1 hqexception
  refine ⟨U, ?_⟩
  constructor
  · exact hUP
  constructor
  · exact hcard
  constructor
  · exact hprod
  · exact hres

/--
Inputs: a finite set `U`, a map into `(ZMod L)ˣ`, and a product identity for
that map, with each unit reducing to its label modulo `L`.

Claim: the natural-number product of the labels is congruent to one modulo
`L`.

Content: the coercion from units to `ZMod L` is multiplicative.

Proof: map the unit product through `Units.coeHom` and replace each factor by
the specified residue.

Role: turns the subset product in the unit group into the residue condition
used alongside the progression modulo `k`.
-/
theorem zmod_product_eq_one_of_unit_product_eq_one (L : ℕ) [NeZero L] (U : Finset ℕ)
    (f : ℕ → Units (ZMod L)) (hprod : (∏ p ∈ U, f p) = 1)
    (hval : ∀ p ∈ U, (f p : ZMod L) = (p : ZMod L)) : (∏ p ∈ U, (p : ZMod L)) = 1 := by
  classical
    calc
    (∏ p ∈ U, (p : ZMod L)) = ∏ p ∈ U, (f p : ZMod L) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (hval p hp).symm
    _ = (∏ p ∈ U, f p : Units (ZMod L)) := by
      symm
      exact map_prod (Units.coeHom (ZMod L)) f U
    _ = 1 := congrArg (Units.coeHom (ZMod L)) hprod

end PseudoPrime.PrimeTest.MillerRabin.AGP
