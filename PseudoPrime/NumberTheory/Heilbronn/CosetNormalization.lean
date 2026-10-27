/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.CosetDifferences

/-! # Heilbronn subgroup cosets and normalization of unit differences -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For prime p, every element in the reduction kernel is an additive lift.
Factor out p and use the reduction-lift identity; used to parametrize principal units. -/
theorem primeLift_surjective_kernel {p : ℕ} [Fact p.Prime] (x : ZMod (p ^ 2))
    (hx : squareReduction p x = 0) : ∃ a : ZMod p, primeLift p a = x := by
  obtain ⟨y, hy⟩ := (squareReduction_eq_zero_iff_dvd x).mp hx
  exact ⟨squareReduction p y, (primeLift_reduction y).trans hy.symm⟩

/-- The principal shift with parameter zero is one. -/
theorem principalShift_zero {p : ℕ} : principalShift p 0 = 1 := by
  rw [principalShift, primeLift_zero, add_zero]

/-- For prime p, every element reducing to one is a principal shift,
by applying the kernel parametrization to x-1. -/
theorem exists_principalShift_of_reduction_one {p : ℕ} [Fact p.Prime] (x : ZMod (p ^ 2))
    (hx : squareReduction p x = 1) : ∃ a : ZMod p, principalShift p a = x := by
  have hz : squareReduction p (x - 1) = 0 := by rw [map_sub, hx, map_one, sub_self]
  obtain ⟨a, ha⟩ := primeLift_surjective_kernel (x - 1) hz
  refine ⟨a, ?_⟩
  rw [principalShift, ha]
  ring

/-- For prime p and nonzero a, the lifts of a and its inverse multiply to one. -/
theorem teichLift_mul_inv {p : ℕ} [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    teichLift p a * teichLift p a⁻¹ = 1 := by
  rw [← teichLift_mul, mul_inv_cancel₀ ha, teichLift_one]

/-- For prime p, the Teichmuller lift of a nonzero residue is a unit,
with inverse the lift of the residue inverse. -/
theorem teichLift_isUnit {p : ℕ} [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    IsUnit (teichLift p a) :=
  IsUnit.of_mul_eq_one _ (teichLift_mul_inv a ha)

/-- For prime p, every principal shift is a unit, with inverse the opposite shift. -/
theorem principalShift_isUnit {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    IsUnit (principalShift p a) := by
  apply IsUnit.of_mul_eq_one (principalShift p (-a))
  rw [principalShift_mul, add_neg_cancel, principalShift_zero]

/-- For prime p, any x with nonzero reduction is a principal shift times
the lift of its reduction. Divide by that lift and parametrize the resulting principal unit. -/
theorem exists_principalShift_mul_teichLift {p : ℕ} [Fact p.Prime] (x : ZMod (p ^ 2))
    (hx : squareReduction p x ≠ 0) :
    ∃ a : ZMod p, x = principalShift p a * teichLift p (squareReduction p x) := by
  have hr : squareReduction p (x * teichLift p (squareReduction p x)⁻¹) = 1 := by
    rw [map_mul, squareReduction_teichLift, mul_inv_cancel₀ hx]
  obtain ⟨a, ha⟩ := exists_principalShift_of_reduction_one _ hr
  refine ⟨a, ?_⟩
  rw [ha, mul_assoc, mul_comm (teichLift p (squareReduction p x)⁻¹), teichLift_mul_inv _ hx,
    mul_one]

/-- For prime p, an element modulo p^2 is a unit exactly when its reduction is nonzero.
Use preservation of units and the explicit principal-times-Teichmuller decomposition. -/
theorem isUnit_iff_reduction_ne_zero {p : ℕ} [Fact p.Prime] (x : ZMod (p ^ 2)) :
    IsUnit x ↔ squareReduction p x ≠ 0 := by
  constructor
  · intro hx
    exact (hx.map (squareReduction p)).ne_zero
  · intro hx
    obtain ⟨a, ha⟩ := exists_principalShift_mul_teichLift x hx
    rw [ha]
    exact (principalShift_isUnit a).mul (teichLift_isUnit _ hx)

/-- The Heilbronn subgroup of units modulo p^2: the image of the p-th power homomorphism.
For prime p its underlying elements are exactly nonzero Teichmuller lifts. -/
def heilbronnSubgroup (p : ℕ) : Subgroup (ZMod (p ^ 2))ˣ :=
  (powMonoidHom p).range

/-- For prime p, membership in the p-th power subgroup is equivalent to being a
nonzero Teichmuller lift. Power-lifting invariance and the fixed-power identity
prove both directions. -/
theorem mem_heilbronnSubgroup_iff {p : ℕ} [Fact p.Prime] (u : (ZMod (p ^ 2))ˣ) :
    u ∈ heilbronnSubgroup p ↔ ∃ b : ZMod p, b ≠ 0 ∧ (u : ZMod (p ^ 2)) = teichLift p b := by
  constructor
  · intro hu
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hu
    refine ⟨squareReduction p (v : ZMod (p ^ 2)), (isUnit_iff_reduction_ne_zero _).mp v.isUnit, ?_⟩
    have he := congrArg (fun w : (ZMod (p ^ 2))ˣ ↦ (w : ZMod (p ^ 2))) hv
    exact he.symm.trans (teichLift_reduction _).symm
  · rintro ⟨b, hb, hu⟩
    let v := (teichLift_isUnit b hb).unit
    apply MonoidHom.mem_range.mpr
    refine ⟨v, ?_⟩
    apply Units.ext
    change (v : ZMod (p ^ 2)) ^ p = u
    rw [IsUnit.unit_spec, teichLift_pow, hu]

/-- For prime p, the parametrized shifted lifts are exactly the principal-unit
multiples of the Heilbronn subgroup. This identifies the counting sets with actual group cosets. -/
theorem shiftedTeichCoset_eq_heilbronn_coset {p : ℕ} [Fact p.Prime] (i : ZMod p)
    (x : ZMod (p ^ 2)) :
    x ∈ shiftedTeichCoset p i ↔
      ∃ u : (ZMod (p ^ 2))ˣ,
        u ∈ heilbronnSubgroup p ∧ x = principalShift p i * (u : ZMod (p ^ 2)) := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    let u := (teichLift_isUnit b hb).unit
    refine ⟨u, (mem_heilbronnSubgroup_iff u).mpr ⟨b, hb, ?_⟩, ?_⟩
    · exact IsUnit.unit_spec _
    · rw [IsUnit.unit_spec]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨b, hb, he⟩ := (mem_heilbronnSubgroup_iff u).mp hu
    exact ⟨b, hb, congrArg (fun z ↦ principalShift p i * z) he⟩

/-- For prime p, multiplication by a nonzero Teichmuller lift preserves each shifted coset.
Multiply the nonzero residue parameters and use multiplicativity of the lift. -/
theorem mul_teichLift_mem_shiftedTeichCoset {p : ℕ} [Fact p.Prime] {i : ZMod p} {x : ZMod (p ^ 2)}
    (hx : x ∈ shiftedTeichCoset p i) (g : ZMod p) (hg : g ≠ 0) :
    x * teichLift p g ∈ shiftedTeichCoset p i := by
  obtain ⟨b, hb, rfl⟩ := hx
  refine ⟨b * g, mul_ne_zero hb hg, ?_⟩
  rw [teichLift_mul, mul_assoc]

/-- Ordered pairs from cosets i,j with arbitrary difference c modulo p^2.
The normalized case c=principalShift(tau) is cosetDifferencePairs. -/
def cosetDifferenceAt (p : ℕ) (i j : ZMod p) (c : ZMod (p ^ 2)) :
    Set (ZMod (p ^ 2) × ZMod (p ^ 2)) :=
  {z | z.1 ∈ shiftedTeichCoset p i ∧ z.2 ∈ shiftedTeichCoset p j ∧ z.1 - z.2 = c}

/-- For prime p and nonzero g, multiply both entries of a difference pair by T(g).
This preserves the source cosets and scales the difference, with inverse scaling by T(g inverse). -/
noncomputable def scaleCosetDifference {p : ℕ} [Fact p.Prime] (i j : ZMod p) (c : ZMod (p ^ 2))
    (g : ZMod p) (hg : g ≠ 0) :
    cosetDifferenceAt p i j c → cosetDifferenceAt p i j (c * teichLift p g) := fun z ↦
  ⟨(z.val.1 * teichLift p g, z.val.2 * teichLift p g),
    mul_teichLift_mem_shiftedTeichCoset z.property.1 g hg,
    mul_teichLift_mem_shiftedTeichCoset z.property.2.1 g hg,
    (sub_mul _ _ _).symm.trans (congrArg (fun x ↦ x * teichLift p g) z.property.2.2)⟩

/-- For prime p and nonzero g, scaling difference pairs by T(g) is bijective.
Cancel the unit T(g) for injectivity and multiply by T(g inverse) for surjectivity. -/
theorem scaleCosetDifference_bijective {p : ℕ} [Fact p.Prime] (i j : ZMod p) (c : ZMod (p ^ 2))
    (g : ZMod p) (hg : g ≠ 0) : Function.Bijective (scaleCosetDifference i j c g hg) := by
  have hu := teichLift_isUnit g hg
  constructor
  · intro a b h
    apply Subtype.ext
    apply Prod.ext
    · exact hu.mul_right_cancel (congrArg (fun z ↦ z.val.1) h)
    · exact hu.mul_right_cancel (congrArg (fun z ↦ z.val.2) h)
  · intro z
    have hd : z.val.1 * teichLift p g⁻¹ - z.val.2 * teichLift p g⁻¹ = c := by
      rw [← sub_mul, z.property.2.2, mul_assoc, teichLift_mul_inv g hg, mul_one]
    let a : cosetDifferenceAt p i j c :=
      ⟨(z.val.1 * teichLift p g⁻¹, z.val.2 * teichLift p g⁻¹),
        mul_teichLift_mem_shiftedTeichCoset z.property.1 g⁻¹ (inv_ne_zero hg),
        mul_teichLift_mem_shiftedTeichCoset z.property.2.1 g⁻¹ (inv_ne_zero hg), hd⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> change (_ * teichLift p g⁻¹) * teichLift p g = _
    · rw [mul_assoc, mul_comm (teichLift p g⁻¹), teichLift_mul_inv g hg, mul_one]
    · rw [mul_assoc, mul_comm (teichLift p g⁻¹), teichLift_mul_inv g hg, mul_one]

/-- For prime p and nonzero g, multiplying the difference by T(g) preserves its correlation.
Apply the explicitly proved scaling bijection. -/
theorem card_cosetDifferenceAt_mul_teichLift {p : ℕ} [Fact p.Prime] (i j : ZMod p)
    (c : ZMod (p ^ 2)) (g : ZMod p) (hg : g ≠ 0) :
    Nat.card (cosetDifferenceAt p i j (c * teichLift p g)) = Nat.card (cosetDifferenceAt p i j c) :=
  (Nat.card_congr (Equiv.ofBijective _ (scaleCosetDifference_bijective i j c g hg))).symm

/-- For odd prime p, a unit difference c and positive t with 64t^3<=p,
the correlation times t is at most 32t+4p. Normalize c using its nonzero reduction
and transfer the proved bound for principal-shift differences. -/
theorem card_cosetDifferenceAt_scaled {p t : ℕ} [Fact p.Prime] (hodd : Odd p) (i j : ZMod p)
    (c : ZMod (p ^ 2)) (hc : IsUnit c) (ht : 0 < t) (hsize : 64 * t ^ 3 ≤ p) :
    Nat.card (cosetDifferenceAt p i j c) * t ≤ 32 * t + 4 * p := by
  obtain ⟨τ, hτ⟩ := exists_principalShift_mul_teichLift c ((isUnit_iff_reduction_ne_zero c).mp hc)
  rw [hτ, card_cosetDifferenceAt_mul_teichLift _ _ _ _ ((isUnit_iff_reduction_ne_zero c).mp hc)]
  exact card_cosetDifferencePairs_scaled hodd i j τ ht hsize

/-- For odd prime p, distinct normalized targets and nonzero scaling residues,
the sum of correlations at the corresponding unit differences satisfies the same Stepanov bound.
Normalize each difference separately; no common scaling residue is required. -/
theorem sum_card_cosetDifferenceAt_scaled {p s t : ℕ} [Fact p.Prime] (hodd : Odd p) (i j : ZMod p)
    (τ g : Fin s → ZMod p) (hτ : Function.Injective τ) (hg : ∀ k, g k ≠ 0) (hs : 0 < s) (ht : 0 < t)
    (hsize : 64 * s ^ 2 * t ^ 3 ≤ p) :
    (∑ k : Fin s, Nat.card (cosetDifferenceAt p i j (principalShift p (τ k) * teichLift p (g k)))) *
        t ≤
      32 * t + 4 * p := by
  have he :
    (∑ k : Fin s, Nat.card (cosetDifferenceAt p i j (principalShift p (τ k) * teichLift p (g k)))) =
      ∑ k : Fin s, Nat.card (cosetDifferencePairs p i j (τ k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact card_cosetDifferenceAt_mul_teichLift i j _ (g k) (hg k)
  rw [he]
  exact sum_card_cosetDifferencePairs_scaled hodd i j τ hτ hs ht hsize

end PseudoPrime.NumberTheory.Heilbronn
