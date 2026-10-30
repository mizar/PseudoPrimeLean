/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.SubgroupAnnihilator
public import PseudoPrime.NumberTheory.DirichletCharacter

/-! # Subgroup residues, eligible prime sets and arithmetic orthogonality -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Membership of a natural residue in the image of a subgroup of units.
Nonunits are outside this image. Used for the subgroup prime bounds. -/
def residueInSubgroup (q : ℕ) (H : Subgroup (ZMod q)ˣ) (n : ℕ) : Prop :=
  ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (n : ZMod q)

/-- The eligible primes outside `H`: prime divisors of the modulus are excluded.
Its least element is the prime appearing in Theorems 1.1--1.3. -/
def primesOutside (q : ℕ) (H : Subgroup (ZMod q)ˣ) : Set ℕ :=
  {p | p.Prime ∧ ¬p ∣ q ∧ ¬residueInSubgroup q H p}

/-- Prime residues in the coset `aH`, described by the quotient of units.
Used to express the least prime in Theorem 1.4. -/
def primesInCoset (q : ℕ) (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) : Set ℕ :=
  {p | p.Prime ∧ ∃ u : (ZMod q)ˣ, a⁻¹ * u ∈ H ∧ (u : ZMod q) = (p : ZMod q)}

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- For a unit natural residue, subgroup membership is membership of its canonical unit.
Injectivity of the coercion from units identifies any witness with that unit.
This converts the paper's residue predicate to the orthogonality hypotheses. -/
theorem residueInSubgroup_iff_unit_mem (H : Subgroup (ZMod q)ˣ) {n : ℕ} (hn : IsUnit (n : ZMod q)) :
    residueInSubgroup q H n ↔ hn.unit ∈ H := by
  constructor
  · rintro ⟨u, hu, he⟩
    have hunit : u = hn.unit := Units.val_injective (he.trans hn.unit_spec.symm)
    exact hunit ▸ hu
  · intro hu
    exact ⟨hn.unit, hu, hn.unit_spec⟩

omit [NeZero q] in
/-- A nonunit natural residue cannot belong to the image of `H`.
A witness would express it as the value of a unit. This handles primes dividing
the modulus when the character average is written as a subgroup indicator. -/
theorem not_residueInSubgroup_of_not_isUnit (H : Subgroup (ZMod q)ˣ) {n : ℕ}
    (hn : ¬IsUnit (n : ZMod q)) : ¬residueInSubgroup q H n := by
  rintro ⟨u, _, he⟩
  apply hn
  rw [← he]
  exact u.isUnit

/-- The annihilator sum vanishes at every nonunit natural residue.
Every Dirichlet character vanishes there. This removes nonunits from the
smoothed sum, independently of subgroup membership or GRH. -/
theorem sum_subgroupAnnihilator_eq_zero_of_not_isUnit (H : Subgroup (ZMod q)ˣ) {n : ℕ}
    (hn : ¬IsUnit (n : ZMod q)) : ∑ χ : subgroupAnnihilator H, χ.val (n : ZMod q) = 0 := by
  exact Finset.sum_eq_zero (fun χ _ ↦ χ.val.map_nonunit hn)

/-- At a natural residue in `H`, the annihilator sum equals the subgroup index.
Use its witness unit and the unit orthogonality formula. This is the selected
part of the arithmetic sum in Proposition 6.1. -/
theorem sum_subgroupAnnihilator_eq_index_of_residue (H : Subgroup (ZMod q)ˣ) {n : ℕ}
    (hn : residueInSubgroup q H n) :
    ∑ χ : subgroupAnnihilator H, χ.val (n : ZMod q) = (H.index : ℂ) := by
  obtain ⟨u, hu, he⟩ := hn
  rw [← he]
  exact sum_subgroupAnnihilator_eq_index H hu

/-- At a natural residue outside the image of `H`, the annihilator sum is zero.
For a unit, use character cancellation; for a nonunit, every character vanishes.
This excludes all other arithmetic terms from the averaged sum. -/
theorem sum_subgroupAnnihilator_eq_zero_of_not_residue (H : Subgroup (ZMod q)ˣ) {n : ℕ}
    (hm : ¬residueInSubgroup q H n) : ∑ χ : subgroupAnnihilator H, χ.val (n : ZMod q) = 0 := by
  by_cases hn : IsUnit (n : ZMod q)
  · rw [← hn.unit_spec]
    exact
      sum_subgroupAnnihilator_eq_zero H (fun hu ↦ hm ((residueInSubgroup_iff_unit_mem H hn).mpr hu))
  · exact sum_subgroupAnnihilator_eq_zero_of_not_isUnit H hn

/-- The complete subgroup orthogonality relation at every natural index: the
annihilator sum is the index times the subgroup indicator. Combine the membership
and cancellation clauses. This identity is valid without GRH. -/
theorem sum_subgroupAnnihilator_eq_indicator (H : Subgroup (ZMod q)ˣ) (n : ℕ) :
    ∑ χ : subgroupAnnihilator H, χ.val (n : ZMod q) =
      {m : ℕ | residueInSubgroup q H m}.indicator (fun _ ↦ (H.index : ℂ)) n := by
  classical
  by_cases hm : residueInSubgroup q H n
  · rw [Set.indicator_of_mem (s := {m : ℕ | residueInSubgroup q H m}) hm]
    exact sum_subgroupAnnihilator_eq_index_of_residue H hm
  · rw [Set.indicator_of_notMem (s := {m : ℕ | residueInSubgroup q H m}) hm]
    exact sum_subgroupAnnihilator_eq_zero_of_not_residue H hm

omit [NeZero q] in
/-- Subgroup membership of a natural residue is preserved by taking any natural power.
Raise its witness unit to the same power and use subgroup closure. This extends
prime membership to every prime-power term in the Mangoldt support. -/
theorem residueInSubgroup_pow (H : Subgroup (ZMod q)ˣ) {n : ℕ} (hn : residueInSubgroup q H n)
    (k : ℕ) : residueInSubgroup q H (n ^ k) := by
  obtain ⟨u, hu, he⟩ := hn
  refine ⟨u ^ k, H.pow_mem hu k, ?_⟩
  rw [Units.val_pow_eq_pow_val, he, Nat.cast_pow]

omit [NeZero q] in
/-- If all eligible primes up to `X` lie in `H`, every prime power up to `X`
coprime to the modulus also lies in `H`. Its prime base is no larger and remains
coprime to the modulus; subgroup closure then handles the exponent. This identifies
all nonzero principal-character Mangoldt terms below the cutoff. -/
theorem residueInSubgroup_of_primePow_of_noSmallPrimes (H : Subgroup (ZMod q)ˣ) {X : ℝ}
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) {n : ℕ}
    (hn : IsPrimePow n) (hc : n.Coprime q) (hbound : (n : ℝ) ≤ X) : residueInSubgroup q H n := by
  obtain ⟨p, k, hp, hk, he⟩ := (isPrimePow_nat_iff n).mp hn
  have hpc : p.Coprime q := Nat.Coprime.of_dvd_left (he ▸ dvd_pow_self p (Nat.ne_of_gt hk)) hc
  have hple : (p : ℝ) ≤ X := (Nat.cast_le.mpr ((Nat.le_pow hk).trans_eq he)).trans hbound
  exact he ▸ residueInSubgroup_pow H (hsmall p hp (hp.coprime_iff_not_dvd.mp hpc) hple) k

end PseudoPrime.NumberTheory
