/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.CosetNormalization

/-! # Exact Heilbronn correlation mass and an initial additive energy bound -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For prime p each shifted coset is equivalent to the nonzero residues via reduction.
The inverse takes the shifted Teichmuller lift; used to count cosets. -/
noncomputable def shiftedTeichCosetEquivResidues {p : ℕ} [Fact p.Prime] (i : ZMod p) :
    shiftedTeichCoset p i ≃ { b : ZMod p // b ≠ 0 }
    where
  toFun x :=
    ⟨squareReduction p x.val, by
      obtain ⟨b, hb, he⟩ := x.property
      rw [he, reduction_shifted_teichLift]
      exact hb⟩
  invFun b := ⟨principalShift p i * teichLift p b.val, b.val, b.property, rfl⟩
  left_inv x := by
    apply Subtype.ext
    change principalShift p i * teichLift p (squareReduction p x.val) = x.val
    obtain ⟨b, hb, he⟩ := x.property
    rw [he, reduction_shifted_teichLift]
  right_inv b := Subtype.ext (reduction_shifted_teichLift i b.val)

/-- For prime p every shifted Heilbronn coset has p-1 elements.
Use its equivalence with nonzero residues and the finite-field cardinality. -/
theorem card_shiftedTeichCoset {p : ℕ} [Fact p.Prime] (i : ZMod p) :
    Nat.card (shiftedTeichCoset p i) = p - 1 := by
  classical
    rw [Nat.card_congr (shiftedTeichCosetEquivResidues i), Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun b : ZMod p ↦ b = 0), ZMod.card, Fintype.card_subtype_eq]

/-- For prime p the difference-pair set is the fiber of subtraction on the product
of the two source cosets. This interface enables exact sums over all differences. -/
noncomputable def cosetDifferenceFiberEquiv {p : ℕ} [Fact p.Prime] (i j : ZMod p)
    (c : ZMod (p ^ 2)) :
    cosetDifferenceAt p i j c ≃
      { z : shiftedTeichCoset p i × shiftedTeichCoset p j // z.1.val - z.2.val = c }
    where
  toFun z := ⟨(⟨z.val.1, z.property.1⟩, ⟨z.val.2, z.property.2.1⟩), z.property.2.2⟩
  invFun z := ⟨(z.val.1.val, z.val.2.val), z.val.1.property, z.val.2.property, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- For prime p, the correlations summed over all differences total (p-1)^2.
Partition the product of the two cosets into subtraction fibers. -/
theorem sum_card_cosetDifferenceAt {p : ℕ} [Fact p.Prime] (i j : ZMod p) :
    ∑ c : ZMod (p ^ 2), Nat.card (cosetDifferenceAt p i j c) = (p - 1) ^ 2 := by
  classical
  have he :=
    Nat.card_congr
      (Equiv.sigmaFiberEquiv
        (fun z : shiftedTeichCoset p i × shiftedTeichCoset p j ↦ z.1.val - z.2.val))
  rw [Nat.card_sigma, Nat.card_prod, card_shiftedTeichCoset, card_shiftedTeichCoset] at he
  exact
    (Finset.sum_congr rfl (fun c hc ↦ Nat.card_congr (cosetDifferenceFiberEquiv i j c))).trans
      (he.trans (pow_two (p - 1)).symm)

/-- For prime p the zero-difference pairs in a single coset are equivalent to that coset,
by taking the first entry and using the diagonal as inverse. -/
theorem cosetDifferenceAt_zero_equiv {p : ℕ} [Fact p.Prime] (i : ZMod p) :
    Nonempty (cosetDifferenceAt p i i 0 ≃ shiftedTeichCoset p i) := by
  refine
    ⟨{  toFun := fun z ↦ ⟨z.val.1, z.property.1⟩
        invFun := fun x ↦ ⟨(x.val, x.val), x.property, x.property, sub_self _⟩
        left_inv := ?_
        right_inv := fun _ ↦ rfl }⟩
  intro z
  apply Subtype.ext
  change (z.val.1, z.val.1) = z.val
  apply Prod.ext
  · rfl
  · exact sub_eq_zero.mp z.property.2.2

/-- For prime p the zero-difference correlation in a single coset equals p-1. -/
theorem card_cosetDifferenceAt_zero {p : ℕ} [Fact p.Prime] (i : ZMod p) :
    Nat.card (cosetDifferenceAt p i i 0) = p - 1 :=
  (Nat.card_congr (cosetDifferenceAt_zero_equiv i).some).trans (card_shiftedTeichCoset i)

/-- For prime p a nonzero nonunit cannot occur as a difference within a single coset.
Its zero reduction forces the two residues, hence the two elements, to coincide. -/
theorem cosetDifferenceAt_nonunit_empty {p : ℕ} [Fact p.Prime] (i : ZMod p) (c : ZMod (p ^ 2))
    (hc : c ≠ 0) (hu : ¬IsUnit c) : cosetDifferenceAt p i i c = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨b, hb, hxb⟩ := hz.1
  obtain ⟨d, hd, hyd⟩ := hz.2.1
  have hred : squareReduction p c = 0 :=
    not_not.mp (fun hn ↦ hu ((isUnit_iff_reduction_ne_zero c).mpr hn))
  have hbd : b = d := by
    have he := congrArg (squareReduction p) hz.2.2
    rw [map_sub, hxb, hyd, reduction_shifted_teichLift, reduction_shifted_teichLift, hred] at he
    exact sub_eq_zero.mp he
  apply hc
  rw [← hz.2.2, hxb, hyd, hbd, sub_self]

/-- Additive energy of the Heilbronn subgroup, defined as the sum of squares of
its ordered difference correlations. The quadruple equivalence proves
the standard counting meaning. -/
noncomputable def heilbronnEnergy (p : ℕ) [Fact p.Prime] : ℕ :=
  ∑ c : ZMod (p ^ 2), Nat.card (cosetDifferenceAt p 0 0 c) ^ 2

/-- For odd prime p and positive t with 64t^3<=p, bound the energy times t by
the exact diagonal contribution plus the nonzero correlation mass times 32t+4p.
Nonzero nonunit differences contribute nothing; normalize all unit differences. -/
theorem heilbronnEnergy_scaled {p t : ℕ} [Fact p.Prime] (hodd : Odd p) (ht : 0 < t)
    (hsize : 64 * t ^ 3 ≤ p) :
    heilbronnEnergy p * t ≤ (p - 1) ^ 2 * t + ((p - 1) ^ 2 - (p - 1)) * (32 * t + 4 * p) := by
  classical
  let N := fun c : ZMod (p ^ 2) ↦ Nat.card (cosetDifferenceAt p 0 0 c)
  have hN0 : N 0 = p - 1 := card_cosetDifferenceAt_zero 0
  have hpoint : ∀ c : ZMod (p ^ 2), c ≠ 0 → N c ^ 2 * t ≤ N c * (32 * t + 4 * p) := by
    intro c hc
    by_cases hu : IsUnit c
    · have he := card_cosetDifferenceAt_scaled hodd 0 0 c hu ht hsize
      have hm := Nat.mul_le_mul_left (N c) he
      convert hm using 1
      ring
    · have hz : N c = 0 := by
        dsimp only [N]
        rw [cosetDifferenceAt_nonunit_empty 0 c hc hu]
        exact Nat.card_of_isEmpty
      rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_mul]
  have hsum : (∑ c ∈ Finset.univ.erase 0, N c) = (p - 1) ^ 2 - (p - 1) := by
    have he := Finset.sum_erase_add (Finset.univ : Finset (ZMod (p ^ 2))) N (Finset.mem_univ 0)
    rw [hN0, sum_card_cosetDifferenceAt 0 0] at he
    exact Nat.eq_sub_of_add_eq he
  have he : heilbronnEnergy p * t = (p - 1) ^ 2 * t + ∑ c ∈ Finset.univ.erase 0, N c ^ 2 * t := by
    rw [heilbronnEnergy, Finset.sum_mul]
    have hs :=
      Finset.sum_erase_add (Finset.univ : Finset (ZMod (p ^ 2))) (fun c ↦ N c ^ 2 * t)
        (Finset.mem_univ 0)
    rw [hN0] at hs
    exact hs.symm.trans (Nat.add_comm _ _)
  rw [he]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ c ∈ Finset.univ.erase 0, N c * (32 * t + 4 * p) := by
      apply Finset.sum_le_sum
      intro c hc
      exact hpoint c (Finset.mem_erase.mp hc).1
    _ = _ := by rw [← Finset.sum_mul, hsum]

/-- Ordered quadruples of nonzero Teichmuller lifts with equal differences.
These count the additive energy, equivalently the usual equal-sum quadruples after rearrangement. -/
def equalDifferenceQuadruples (p : ℕ) :
    Set ((ZMod (p ^ 2) × ZMod (p ^ 2)) × (ZMod (p ^ 2) × ZMod (p ^ 2))) :=
  {z |
    z.1.1 ∈ shiftedTeichCoset p 0 ∧
      z.1.2 ∈ shiftedTeichCoset p 0 ∧
      z.2.1 ∈ shiftedTeichCoset p 0 ∧ z.2.2 ∈ shiftedTeichCoset p 0 ∧ z.1.1 - z.1.2 = z.2.1 - z.2.2}

/-- For prime p partition equal-difference quadruples by their common difference.
Each fiber is a product of two correlation sets, proving the squared-correlation formula. -/
noncomputable def equalDifferenceQuadruplesEquiv {p : ℕ} [Fact p.Prime] :
    equalDifferenceQuadruples p ≃
      Σ c : ZMod (p ^ 2), cosetDifferenceAt p 0 0 c × cosetDifferenceAt p 0 0 c
    where
  toFun z :=
    ⟨z.val.1.1 - z.val.1.2, ⟨z.val.1, z.property.1, z.property.2.1, rfl⟩,
      ⟨z.val.2, z.property.2.2.1, z.property.2.2.2.1, z.property.2.2.2.2.symm⟩⟩
  invFun z :=
    ⟨(z.2.1.val, z.2.2.val), z.2.1.property.1, z.2.1.property.2.1, z.2.2.property.1,
      z.2.2.property.2.1, z.2.1.property.2.2.trans z.2.2.property.2.2.symm⟩
  left_inv _ := rfl
  right_inv z := by
    obtain ⟨c, a, b⟩ := z
    obtain ⟨a, hai, haj, ha⟩ := a
    obtain ⟨b, hbi, hbj, hb⟩ := b
    dsimp only
    subst c
    rfl

/-- For prime p the energy is exactly the number of equal-difference quadruples.
Apply the explicit fiber-product equivalence and sum the product cardinalities. -/
theorem heilbronnEnergy_eq_card_quadruples {p : ℕ} [Fact p.Prime] :
    heilbronnEnergy p = Nat.card (equalDifferenceQuadruples p) := by
  classical
  have he := Nat.card_congr (equalDifferenceQuadruplesEquiv (p := p))
  rw [Nat.card_sigma] at he
  rw [he, heilbronnEnergy]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Nat.card_prod, pow_two]

/-- For odd prime p and positive t with 64t^3<=p, E*t<=33p^2*t+4p^3.
Coarsen the exact diagonal and nonzero mass bounds; no unproved energy estimate is used. -/
theorem heilbronnEnergy_scaled_coarse {p t : ℕ} [Fact p.Prime] (hodd : Odd p) (ht : 0 < t)
    (hsize : 64 * t ^ 3 ≤ p) : heilbronnEnergy p * t ≤ 33 * p ^ 2 * t + 4 * p ^ 3 := by
  have hb := heilbronnEnergy_scaled hodd ht hsize
  have hp : (p - 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (Nat.sub_le p 1) 2
  have hq : (p - 1) ^ 2 - (p - 1) ≤ p ^ 2 := (Nat.sub_le _ _).trans hp
  have he := Nat.add_le_add (Nat.mul_le_mul_right t hp) (Nat.mul_le_mul_right (32 * t + 4 * p) hq)
  exact hb.trans (he.trans_eq (by ring))

/-- For every natural p>=64, choose a positive integer t<=p with 64t^3<=p<512t^3.
Take the largest admissible t and compare its successor to twice t;
no input enumeration is needed. -/
theorem exists_cubic_scale {p : ℕ} (hp : 64 ≤ p) :
    ∃ t : ℕ, 0 < t ∧ t ≤ p ∧ 64 * t ^ 3 ≤ p ∧ p < 512 * t ^ 3 := by
  let t := Nat.findGreatest (fun u ↦ 64 * u ^ 3 ≤ p) p
  have hp1 : 1 ≤ p := (by decide : 1 ≤ 64).trans hp
  have h1 : 64 * 1 ^ 3 ≤ p := by simpa only [one_pow, mul_one] using hp
  have ht1 : 1 ≤ t := Nat.le_findGreatest hp1 h1
  have hsize : 64 * t ^ 3 ≤ p := Nat.findGreatest_spec (P := fun u ↦ 64 * u ^ 3 ≤ p) hp1 h1
  have htple : t ≤ p := Nat.findGreatest_le p
  have htp : t < p := by
    apply lt_of_le_of_ne htple
    intro he
    rw [he] at hsize
    have hp3 : p ≤ p ^ 3 := Nat.le_pow (by decide : 0 < 3)
    nlinarith only [hsize, hp3, hp]
  have hnext : p < 64 * (t + 1) ^ 3 :=
    Nat.lt_of_not_ge
      (Nat.findGreatest_is_greatest (P := fun u ↦ 64 * u ^ 3 ≤ p) (Nat.lt_succ_self t) htp)
  have ht2 : t + 1 ≤ 2 * t := by linarith only [ht1]
  have hpow := Nat.pow_le_pow_left ht2 3
  refine ⟨t, ht1, htple, hsize, ?_⟩
  exact hnext.trans_le ((Nat.mul_le_mul_left 64 hpow).trans_eq (by ring))

/-- For odd prime p>=64, the Heilbronn energy satisfies E^3<=25934336*p^8.
Choose a cubic scale, cube the scaled energy inequality and cancel the positive p.
This intermediate 8/3 bound is weaker than the refined energy target. -/
theorem heilbronnEnergy_cube_le {p : ℕ} [Fact p.Prime] (hodd : Odd p) (hp : 64 ≤ p) :
    heilbronnEnergy p ^ 3 ≤ 25934336 * p ^ 8 := by
  obtain ⟨t, ht, htp, hsize, hlarge⟩ := exists_cubic_scale hp
  have hb := heilbronnEnergy_scaled_coarse hodd ht hsize
  have hc : heilbronnEnergy p * t ≤ 37 * p ^ 3 := by
    have he := Nat.mul_le_mul_left (33 * p ^ 2) htp
    nlinarith only [hb, he]
  have hc3 := Nat.pow_le_pow_left hc 3
  have hmul := Nat.mul_le_mul_left (heilbronnEnergy p ^ 3) hlarge.le
  have hupper : heilbronnEnergy p ^ 3 * p ≤ 25934336 * p ^ 9 := by
    calc
      _ ≤ 512 * ((heilbronnEnergy p * t) ^ 3) := by
        convert hmul using 1
        ring
      _ ≤ 512 * ((37 * p ^ 3) ^ 3) := Nat.mul_le_mul_left 512 hc3
      _ = _ := by ring
  have hfact : heilbronnEnergy p ^ 3 * p ≤ (25934336 * p ^ 8) * p := by
    convert hupper using 1
    ring
  exact Nat.le_of_mul_le_mul_right hfact (Nat.Prime.pos Fact.out)

/-- For prime p each correlation is at most p-1. Projection to the first entry
is injective because the second entry is determined by the fixed difference. -/
theorem card_cosetDifferenceAt_le {p : ℕ} [Fact p.Prime] (i j : ZMod p) (c : ZMod (p ^ 2)) :
    Nat.card (cosetDifferenceAt p i j c) ≤ p - 1 := by
  let f : cosetDifferenceAt p i j c → shiftedTeichCoset p i := fun z ↦ ⟨z.val.1, z.property.1⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val h
    · have hx : a.val.1 = b.val.1 := congrArg Subtype.val h
      linear_combination b.property.2.2 - a.property.2.2 + hx
  exact (Nat.card_le_card_of_injective f hf).trans_eq (card_shiftedTeichCoset i)

/-- For prime p the additive energy is at most (p-1)^3.
Bound one factor of each squared correlation and use the exact total mass. -/
theorem heilbronnEnergy_le_cube {p : ℕ} [Fact p.Prime] : heilbronnEnergy p ≤ (p - 1) ^ 3 := by
  have he :
    heilbronnEnergy p ≤ ∑ c : ZMod (p ^ 2), (p - 1) * Nat.card (cosetDifferenceAt p 0 0 c) := by
    apply Finset.sum_le_sum
    intro c hc
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (card_cosetDifferenceAt_le 0 0 c)
  rw [← Finset.mul_sum, sum_card_cosetDifferenceAt 0 0] at he
  exact he.trans_eq (by ring)

/-- For every odd prime p the energy satisfies E^3<=25934336*p^8.
Use the cubic-scale bound above 64; below 64 the general cubic energy bound suffices,
without enumerating the primes. -/
theorem heilbronnEnergy_cube_le_uniform {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    heilbronnEnergy p ^ 3 ≤ 25934336 * p ^ 8 := by
  by_cases hp : 64 ≤ p
  · exact heilbronnEnergy_cube_le hodd hp
  · have hsmall : p ≤ 64 := (Nat.lt_of_not_ge hp).le
    have he : heilbronnEnergy p ≤ p ^ 3 :=
      heilbronnEnergy_le_cube.trans (Nat.pow_le_pow_left (Nat.sub_le p 1) 3)
    have he3 := Nat.pow_le_pow_left he 3
    calc
      _ ≤ (p ^ 3) ^ 3 := he3
      _ = p ^ 8 * p := by ring
      _ ≤ p ^ 8 * 64 := Nat.mul_le_mul_left _ hsmall
      _ ≤ _ := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_right _ (by decide : 64 ≤ 25934336)

end PseudoPrime.NumberTheory.Heilbronn
