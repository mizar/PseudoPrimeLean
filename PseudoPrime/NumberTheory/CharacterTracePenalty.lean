/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.CharacterKernelOrder
public import PseudoPrime.NumberTheory.CharacterWeights
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.IntegralDomain

/-! # Finite character images and normalized trace penalties

These statements concern actual unit values and finite Fourier sums independently of
GRH, smoothing kernels and numerical prime-bound coefficients. A primitive value can be
chosen from each finite complex character image, so trace constraints can be tested on
realized unit values rather than merely possible scalar patterns.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A complex character attains a unit value of its full character order.
Input: any character at nonzero level. Its finite image in the complex units is cyclic;
choose an element of full image order and lift it through the unit homomorphism.
This supplies primitive values for finite Fourier identities and trace necessity tests. -/
theorem exists_unit_character_order {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ u : (ZMod q)ˣ, orderOf (χ.toUnitHom u) = orderOf χ :=
  Exists.elim (IsCyclic.exists_ofOrder_eq_natCard (α := χ.toUnitHom.range)) fun v hv ↦
    Exists.elim v.property fun u hu ↦
      ⟨u,
        hu ▸
          (orderOf_injective _ χ.toUnitHom.range.subtype_injective v).trans
            (hv.trans ((Subgroup.index_ker χ.toUnitHom).symm.trans (index_kernel_eq_order χ)))⟩

/-- Coercing a character's unit value to the complex numbers preserves its order.
Input: any character and ambient unit. The complex-unit inclusion is an injective monoid
homomorphism. This connects image-order statements with actual complex evaluations. -/
theorem character_unit_value_order {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    orderOf (χ (u : ZMod q)) = orderOf (χ.toUnitHom u) :=
  (congrArg orderOf (MulChar.coe_toUnitHom χ u).symm).trans
    (orderOf_injective (Units.coeHom ℂ) Units.val_injective (χ.toUnitHom u))

/-- A nonprincipal complex character has zero sum over the ambient unit group.
Input: nonprincipality at nonzero level. Translate the finite unit sum by a unit where the
character differs from one and cancel the resulting nonidentity factor. This is finite
Fourier orthogonality independently of analytic kernels. -/
theorem sum_character_units_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    (∑ u : (ZMod q)ˣ, χ (u : ZMod q)) = 0 := by
  obtain ⟨b, hb⟩ := MulChar.ne_one_iff.mp hχ
  apply eq_zero_of_mul_eq_self_left hb
  rw [Finset.mul_sum]
  have he := Equiv.sum_comp (Equiv.mulLeft b) (fun u : (ZMod q)ˣ ↦ χ (u : ZMod q))
  change (∑ u : (ZMod q)ˣ, χ ((b * u : (ZMod q)ˣ) : ZMod q)) = _ at he
  simpa only [Units.val_mul, map_mul] using he

/-- An annihilating character family's trace equals its total weight on the subgroup.
Input: annihilator membership for every family member and a subgroup unit. Every character
value there is one, so expand the finite sum. This normalizes finite Fourier test functions. -/
theorem weighted_trace_on_subgroup {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset (DirichletCharacter ℂ q)) (w : DirichletCharacter ℂ q → ℝ)
    (hS : ∀ χ ∈ S, χ ∈ subgroupAnnihilator H) {u : (ZMod q)ˣ} (hu : u ∈ H) :
    weightedCharacterTrace S w (u : ZMod q) = characterWeightTotal S w :=
  Finset.sum_congr rfl fun χ hχ ↦
    (congrArg (fun v : ℂ ↦ w χ * v.re) ((mem_subgroupAnnihilator_iff H χ).mp (hS χ hχ) u hu)).trans
      (mul_one (w χ))

/-- A weighted sum of nonprincipal character real traces has zero unit average.
Input: any finite nonprincipal family and arbitrary real weights. Interchange finite sums,
take real parts of unit orthogonality and factor each weight. No positivity is needed. -/
theorem sum_weighted_trace_units_eq_zero {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℝ) (hnp : ∀ χ ∈ S, χ ≠ 1) :
    (∑ u : (ZMod q)ˣ, weightedCharacterTrace S w (u : ZMod q)) = 0 := by
  change (∑ u : (ZMod q)ˣ, ∑ χ ∈ S, w χ * (χ (u : ZMod q)).re) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro χ hχ
  have hr := map_sum Complex.reCLM (fun u : (ZMod q)ˣ ↦ χ (u : ZMod q)) Finset.univ
  change (∑ u : (ZMod q)ˣ, χ (u : ZMod q)).re = ∑ u : (ZMod q)ˣ, (χ (u : ZMod q)).re at hr
  rw [← Finset.mul_sum, ← hr, sum_character_units_eq_zero χ (hnp χ hχ), Complex.zero_re, mul_zero]

/-- A normalized finite-group test function has an index-controlled negative trace barrier.
Input: unit total sum zero, value one on a subgroup and global lower bound minus m.
Split subgroup and complement, count the two parts, use the subgroup card-index identity
and cancel its positive cardinality. This is the counting step behind the Fourier bound. -/
private theorem finite_group_trace_barrier {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (f : G → ℝ) {m : ℝ} (hsum : ∑ u : G, f u = 0) (hH : ∀ u ∈ H, f u = 1)
    (hlo : ∀ u : G, -m ≤ f u) : 1 ≤ ((H.index : ℝ) - 1) * m := by
  classical
  have hA : (∑ u : H, f u.val) = (Fintype.card H : ℝ) := by
    calc
      _ = ∑ _u : H, (1 : ℝ) := Finset.sum_congr rfl fun u _ ↦ hH u.val u.property
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hB : (Fintype.card { u : G // u ∉ H } : ℝ) * (-m) ≤ ∑ u : { u : G // u ∉ H }, f u.val := by
    calc
      _ = ∑ _u : { u : G // u ∉ H }, (-m) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun u _ ↦ hlo u.val
  have hC := Fintype.sum_subtype_add_sum_subtype (fun u : G ↦ u ∈ H) f
  have hN := Fintype.sum_subtype_add_sum_subtype (fun u : G ↦ u ∈ H) (fun _ ↦ (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hN
  rw [hA, hsum] at hC
  have hI := congrArg (fun n : ℕ ↦ (n : ℝ)) H.card_mul_index
  simp only [Nat.cast_mul, Nat.card_eq_fintype_card] at hI
  have hO : (Fintype.card { u : G // u ∉ H } : ℝ) = (Fintype.card H : ℝ) * ((H.index : ℝ) - 1) := by
    linarith only [hN, hI]
  rw [hO] at hB
  have hpos : 0 < (Fintype.card H : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hpos).mp
  nlinarith only [hB, hC]

/-- A normalized nonprincipal annihilator trace forces one at most index minus one times m.
Input: any finite family annihilating a subgroup, total weight one and actual global trace
lower bound minus m. Its unit sum is zero and its subgroup value is one; apply finite group
counting. The statement has no GRH, smoothing kernel, selected index or numerical coefficient. -/
theorem normalized_trace_penalty {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset (DirichletCharacter ℂ q)) (w : DirichletCharacter ℂ q → ℝ) (hnp : ∀ χ ∈ S, χ ≠ 1)
    (hS : ∀ χ ∈ S, χ ∈ subgroupAnnihilator H) (hW : characterWeightTotal S w = 1) {m : ℝ}
    (htrace : ∀ z : ZMod q, -m ≤ weightedCharacterTrace S w z) : 1 ≤ ((H.index : ℝ) - 1) * m :=
  finite_group_trace_barrier H (fun u ↦ weightedCharacterTrace S w (u : ZMod q))
    (sum_weighted_trace_units_eq_zero S w hnp)
    (fun _ hu ↦ (weighted_trace_on_subgroup H S w hS hu).trans hW) (fun u ↦ htrace (u : ZMod q))

end PseudoPrime.NumberTheory
