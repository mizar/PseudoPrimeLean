/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.SmallSignedResidue
public import PseudoPrime.NumberTheory.SignedPrimeProductCounting

/-! # Generation of prime-modulus subgroups by small primes -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A subgroup of the units modulo a prime that contains `-1` and every
prime through `B` is the whole unit group when `q < (B+1)²`. A small signed
residue represents each unit as a quotient of two small integers. -/
theorem subgroup_eq_top_of_small_primes {q B : ℕ} (hq : q.Prime) (hB : 0 < B)
    (hsize : q < (B + 1) ^ 2) (H : Subgroup (ZMod q)ˣ) (hneg : (-1 : (ZMod q)ˣ) ∈ H)
    (hmem : ∀ p : ℕ, p.Prime → p ≤ B → ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q)) :
    H = ⊤ := by
  let : Fact q.Prime := ⟨hq⟩
  apply top_unique
  intro x hx
  let a : ℕ := (x : ZMod q).val
  obtain ⟨v, hv0, hvB, u, j, huB, he⟩ := exists_small_signed_residue (a := a) hq.pos hB hsize
  obtain ⟨V, hV⟩ := small_nat_mem_subgroup H hv0 hvB hmem
  have hmod : (v : ZMod q) * (x : ZMod q) = (u : ZMod q) := by
    have hh := congrArg (fun z : ℤ ↦ (z : ZMod q)) he
    simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, ZMod.natCast_self, mul_zero,
      add_zero] at hh
    dsimp only [a] at hh
    rw [ZMod.natCast_zmod_val] at hh
    exact hh
  have hvne : (v : ZMod q) ≠ 0 := by
    rw [← hV]
    exact Units.ne_zero (V : (ZMod q)ˣ)
  have hune : u ≠ 0 := by
    intro hu
    rw [hu, Int.cast_zero] at hmod
    exact (mul_ne_zero hvne (Units.ne_zero x)) hmod
  have hu0 : 0 < u.natAbs := Nat.pos_of_ne_zero (fun h ↦ hune (Int.natAbs_eq_zero.mp h))
  obtain ⟨U, hU⟩ := small_nat_mem_subgroup H hu0 huB hmem
  have habs : ((u.natAbs : ℕ) : ZMod q) = ((|u| : ℤ) : ZMod q) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ ↦ (z : ZMod q)) (Int.natCast_natAbs u)
  have hrepr : ∃ W : H, ((W : (ZMod q)ˣ) : ZMod q) = (u : ZMod q) := by
    by_cases hnonneg : 0 ≤ u
    · refine ⟨U, ?_⟩
      rw [hU, habs, abs_of_nonneg hnonneg]
    · refine
        ⟨⟨-((U : H) : (ZMod q)ˣ), by simpa only [neg_one_mul] using H.mul_mem hneg U.property⟩, ?_⟩
      simp only [Units.val_neg, hU, habs, abs_of_neg (lt_of_not_ge hnonneg), Int.cast_neg, neg_neg]
  obtain ⟨W, hW⟩ := hrepr
  have hunit : (V : (ZMod q)ˣ) * x = W := by
    apply Units.ext
    simpa only [Units.val_mul, hV, hW] using hmod
  have hxW : x = (V : (ZMod q)ˣ)⁻¹ * W := by rw [← hunit, inv_mul_cancel_left]
  rw [hxW]
  exact H.mul_mem (H.inv_mem V.property) W.property

end PseudoPrime.NumberTheory
