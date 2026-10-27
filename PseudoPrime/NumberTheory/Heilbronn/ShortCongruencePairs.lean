/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.FermatCountingBudget

/-! # Short integer coordinates and unique Heilbronn congruence multipliers -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For prime p and nonzero integer x with natAbs(x)<p, its cast modulo p^2
is a unit. A zero reduction would make p divide its smaller positive absolute value. -/
theorem intCast_isUnit_of_natAbs_lt {p : ℕ} [Fact p.Prime] (x : ℤ) (hx : x ≠ 0)
    (hxp : x.natAbs < p) : IsUnit (x : ZMod (p ^ 2)) := by
  apply (isUnit_iff_reduction_ne_zero _).mpr
  rw [map_intCast]
  intro hz
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hz
  have hn : p ∣ x.natAbs := by
    have he := Int.natAbs_dvd_natAbs.mpr hd
    simpa only [Int.natAbs_natCast] using he
  exact (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hx) hxp) hn

/-- For prime p and a short nonzero integer x, the multiplier in u*x=y modulo p^2
is unique. Cancel the explicitly proved unit cast of x. -/
theorem multiplier_eq_of_short_congruence {p : ℕ} [Fact p.Prime] (x : ℤ) (hx : x ≠ 0)
    (hxp : x.natAbs < p) {u v y : ZMod (p ^ 2)} (hu : u * (x : ZMod (p ^ 2)) = y)
    (hv : v * (x : ZMod (p ^ 2)) = y) : u = v :=
  (intCast_isUnit_of_natAbs_lt x hx hxp).mul_right_cancel (hu.trans hv.symm)

/-- For prime p unfold membership in the finite congruence set into subgroup,
integer interval, nonzero and congruence conditions. This is the external counting interface. -/
theorem mem_boundedHeilbronnCongruences_iff {p H : ℕ} [Fact p.Prime] (z : ZMod (p ^ 2) × ℤ × ℤ) :
    z ∈ boundedHeilbronnCongruences p H ↔
      z.1 ∈ shiftedTeichCoset p 0 ∧
        (-(H : ℤ) ≤ z.2.1 ∧ z.2.1 ≤ H) ∧
        (-(H : ℤ) ≤ z.2.2 ∧ z.2.2 ≤ H) ∧
        z.2.1 ≠ 0 ∧ z.2.2 ≠ 0 ∧ z.1 * (z.2.1 : ZMod (p ^ 2)) = (z.2.2 : ZMod (p ^ 2)) := by
  classical
    simp only [boundedHeilbronnCongruences, Finset.mem_filter, Finset.mem_product, Set.mem_toFinset,
    Finset.mem_Icc, and_assoc]

/-- For prime p and H<p, every first integer coordinate in the bounded
congruence set has absolute value less than p. Use its interval membership. -/
theorem boundedCongruence_first_natAbs_lt {p H : ℕ} [Fact p.Prime] (hHp : H < p)
    {z : ZMod (p ^ 2) × ℤ × ℤ} (hz : z ∈ boundedHeilbronnCongruences p H) : z.2.1.natAbs < p := by
  have hb := (mem_boundedHeilbronnCongruences_iff z).mp hz
  have hc : (z.2.1.natAbs : ℤ) ≤ (H : ℤ) := by
    rw [Int.natCast_natAbs]
    exact abs_le.mpr hb.2.1
  have he : z.2.1.natAbs ≤ H := Int.ofNat_le.mp hc
  exact he.trans_lt hHp

/-- Integer coordinate pairs obtained by forgetting the Heilbronn multiplier.
For H<p the multiplier is unique, so the image cardinality equals the original congruence count.
These are integer pairs, not a quotient identifying equal rational numbers. -/
noncomputable def boundedRatioPairs (p H : ℕ) [Fact p.Prime] : Finset (ℤ × ℤ) :=
  (boundedHeilbronnCongruences p H).image Prod.snd

/-- For prime p and H<p, projection of bounded congruence triples to their
integer coordinates is injective, by cancellation of the first nonzero short coordinate. -/
theorem boundedCongruence_projection_injective {p H : ℕ} [Fact p.Prime] (hHp : H < p) :
    Set.InjOn (Prod.snd : ZMod (p ^ 2) × ℤ × ℤ → ℤ × ℤ) (boundedHeilbronnCongruences p H) := by
  intro a ha b hb hab
  have hpa := (mem_boundedHeilbronnCongruences_iff a).mp ha
  have hpb := (mem_boundedHeilbronnCongruences_iff b).mp hb
  apply Prod.ext
  · apply
      multiplier_eq_of_short_congruence a.2.1 hpa.2.2.2.1 (boundedCongruence_first_natAbs_lt hHp ha)
        hpa.2.2.2.2.2
    rw [hab]
    exact hpb.2.2.2.2.2
  · exact hab

/-- For prime p and H<p the actual congruence count equals the number of
projected integer pairs. Apply the projection injectivity; no analytic bound is assumed. -/
theorem boundedCongruenceCount_eq_ratioPairs_card {p H : ℕ} [Fact p.Prime] (hHp : H < p) :
    boundedCongruenceCount p H = (boundedRatioPairs p H).card := by
  classical exact (Finset.card_image_of_injOn (boundedCongruence_projection_injective hHp)).symm

/-- For prime p and H<p, both integer coordinates of a bounded solution
are units modulo p^2. The first is short and nonzero;
the second is its product with a subgroup unit. -/
theorem boundedCongruence_member_units {p H : ℕ} [Fact p.Prime] (hHp : H < p)
    {z : ZMod (p ^ 2) × ℤ × ℤ} (hz : z ∈ boundedHeilbronnCongruences p H) :
    IsUnit (z.2.1 : ZMod (p ^ 2)) ∧ IsUnit (z.2.2 : ZMod (p ^ 2)) := by
  have hb := (mem_boundedHeilbronnCongruences_iff z).mp hz
  have hx := intCast_isUnit_of_natAbs_lt z.2.1 hb.2.2.2.1 (boundedCongruence_first_natAbs_lt hHp hz)
  have hu : IsUnit z.1 := by
    obtain ⟨b, hb, he⟩ := hb.1
    rw [he]
    exact (principalShift_isUnit 0).mul (teichLift_isUnit b hb)
  refine ⟨hx, ?_⟩
  rw [← hb.2.2.2.2.2]
  exact hu.mul hx

/-- For odd prime p and H<p, a bound on projected integer pairs and the sixth-power
budget imply p*E*count<k^2. Transfer the exact count identity to the proved energy budget. -/
theorem boundedRatioPairs_energy_budget {p H k B : ℕ} [Fact p.Prime] (hodd : Odd p) (hHp : H < p)
    (hcount : (boundedRatioPairs p H).card * k ≤ B) (hgap : 18874370 * p ^ 7 * B ^ 2 < k ^ 6) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  apply boundedCongruenceCount_energy_budget hodd _ hgap
  rw [boundedCongruenceCount_eq_ratioPairs_card hHp]
  exact hcount

end PseudoPrime.NumberTheory.Heilbronn
