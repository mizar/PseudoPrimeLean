/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.CyclicCharacterTraces

/-! # Actual cyclic-six character traces and weighted costs

The family consists of the five nonprincipal powers of an actual order-six character.
Weights are arbitrary; only their conjugate-pair totals enter the real trace and conductor
cost. The affine trace constraints are checked against actual unit values, and numerical
prime-bound coefficients remain in the downstream endpoint consumers.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A character value at a unit has power one at the character order.
Input: an exact order and a unit. Evaluate the character power identity at that unit.
This supplies finite root-of-unity equations for the trace classification. -/
private theorem character_unit_power {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {k : ℕ}
    (ho : orderOf χ = k) (u : (ZMod q)ˣ) : χ (u : ZMod q) ^ k = 1 :=
  (MulChar.pow_apply_coe χ k u).symm.trans
    ((congrArg (fun ψ : DirichletCharacter ℂ q ↦ ψ (u : ZMod q)) (ho ▸ pow_orderOf_eq_one χ)).trans
      (MulChar.one_apply_coe u))

/-- An inverse complex character has the same real value at every residue.
Input: any character and residue. Complex character inversion is conjugation.
This combines conjugate-pair terms without assuming equal weights. -/
private theorem inverse_character_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ZMod q) :
    (χ⁻¹ z).re = (χ z).re :=
  (congrArg Complex.re (MulChar.star_apply' χ z).symm).trans (Complex.conj_re _)

/-- A nonidentity complex cube root satisfies the quadratic cyclotomic equation.
Input: cube one and nonidentity. Factor the cubic polynomial and cancel its nonzero factor.
This identifies the nontrivial cubic real values. -/
private theorem cubic_factor {z : ℂ} (hz : z ^ 3 = 1) (hn : z ≠ 1) : z ^ 2 + z + 1 = 0 := by
  have hf : (z - 1) * (z ^ 2 + z + 1) = z ^ 3 - 1 := by ring
  exact (mul_eq_zero.mp (hf.trans (sub_eq_zero.mpr hz))).resolve_left (sub_ne_zero.mpr hn)

/-- The square of an order-three character has the same real value.
Input: exact order three and any residue. The square is the inverse, hence conjugate.
This reduces cubic-value classification to a real linear equation. -/
private theorem cubic_square_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 3)
    (z : ZMod q) : ((χ ^ 2) z).re = (χ z).re :=
  let hi : χ ^ 2 = χ⁻¹ :=
    eq_inv_iff_mul_eq_one.mpr
      ((pow_succ χ 2).symm.trans (show χ ^ 3 = 1 from ho ▸ pow_orderOf_eq_one χ))
  (congrArg (fun ψ : DirichletCharacter ℂ q ↦ (ψ z).re) hi).trans (inverse_character_re χ z)

/-- A nonidentity value of an order-three character has real part minus one half.
Input: exact order three, a unit and nonidentity value. Combine the cyclotomic equation
with the conjugate square identity. This gives the actual cubic trace value. -/
private theorem cubic_nontrivial_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 3) (u : (ZMod q)ˣ) (hn : χ (u : ZMod q) ≠ 1) :
    (χ (u : ZMod q)).re = -1 / 2 := by
  have hs : (χ (u : ZMod q) ^ 2).re = (χ (u : ZMod q)).re :=
    (congrArg Complex.re (MulChar.pow_apply_coe χ 2 u).symm).trans (cubic_square_re χ ho u)
  have hr := congrArg Complex.re (cubic_factor (character_unit_power χ ho u) hn)
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re, hs] at hr
  linarith only [hr]

/-- A character factors as its cube times the inverse of its square.
Input: any character. Rearrange its commuting powers. This separates the quadratic sign
from the cubic real value in order-six families. -/
private theorem six_value_factor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ = χ ^ 3 * (χ ^ 2)⁻¹ :=
  eq_mul_inv_iff_mul_eq.mpr (pow_succ' χ 2).symm

/-- The real value of an order-six character splits into quadratic and cubic real values.
Input: exact order six and a unit. Its cube has value one or minus one, so evaluating the
factorization and taking real parts gives the product. This classifies the grouped trace. -/
private theorem six_unit_real_factor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 6) (u : (ZMod q)ˣ) :
    (χ (u : ZMod q)).re = ((χ ^ 3) (u : ZMod q)).re * ((χ ^ 2) (u : ZMod q)).re := by
  have ho3 : orderOf (χ ^ 3) = 2 :=
    (orderOf_pow χ).trans (congrArg (fun n : ℕ ↦ n / Nat.gcd n 3) ho)
  have hv :=
    (congrArg (fun ψ : DirichletCharacter ℂ q ↦ ψ (u : ZMod q)) (six_value_factor χ)).trans
      (MulChar.mul_apply _ _ _)
  rcases sq_eq_one_iff.mp (character_unit_power (χ ^ 3) ho3 u) with hc | hc
  · rw [hv, hc]
    simp only [one_mul, Complex.one_re, inverse_character_re]
  · rw [hv, hc]
    simp only [neg_one_mul, Complex.neg_re, Complex.one_re, inverse_character_re]

/-- The three affine cyclic-six penalties bound the grouped trace at every unit.
Input: normalized group totals and a penalty above all three affine values. The cubic
value is identity or has real part minus one half; the quadratic value has either sign.
Check these four realized possibilities to obtain the lower bound. -/
private theorem six_grouped_unit_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 6) (u : (ZMod q)ˣ) {a b c m : ℝ} (hw : a + b + c = 1)
    (hm1 : -(1 / 2 : ℝ) + b + 3 / 2 * c ≤ m) (hm2 : 1 / 2 - 3 / 2 * c ≤ m) (hm3 : 1 - 2 * b ≤ m) :
    -m ≤
      a * (χ (u : ZMod q)).re + b * ((χ ^ 2) (u : ZMod q)).re + c * ((χ ^ 3) (u : ZMod q)).re := by
  have ho2 : orderOf (χ ^ 2) = 3 :=
    (orderOf_pow χ).trans (congrArg (fun n : ℕ ↦ n / Nat.gcd n 2) ho)
  have ho3 : orderOf (χ ^ 3) = 2 :=
    (orderOf_pow χ).trans (congrArg (fun n : ℕ ↦ n / Nat.gcd n 3) ho)
  rw [six_unit_real_factor χ ho u]
  rcases sq_eq_one_iff.mp (character_unit_power (χ ^ 3) ho3 u) with h3 | h3
  · rw [h3, Complex.one_re, one_mul]
    by_cases h2 : (χ ^ 2) (u : ZMod q) = 1
    · rw [h2, Complex.one_re]
      nlinarith only [hw, hm1, hm2, hm3]
    · rw [cubic_nontrivial_re (χ ^ 2) ho2 u h2]
      nlinarith only [hw, hm2]
  · rw [h3, Complex.neg_re, Complex.one_re, neg_one_mul]
    by_cases h2 : (χ ^ 2) (u : ZMod q) = 1
    · rw [h2, Complex.one_re]
      nlinarith only [hw, hm3]
    · rw [cubic_nontrivial_re (χ ^ 2) ho2 u h2]
      nlinarith only [hw, hm1]

/-- The five nonprincipal powers of a selected cyclic-six generator.
Input: a character; output: the finite image of exponents one through five. Exact order six
is imposed by the consuming theorems, which ensures distinctness and nonprincipality.
This is the actual finite family used by the weighted prime criterion. -/
noncomputable def cyclicSixFamily {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Finset (DirichletCharacter ℂ q) :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  (Finset.range 5).image (fun k : ℕ ↦ χ ^ (k + 1))

/-- The first five positive powers of an order-six character are distinct.
Input: exact order six. Use injectivity of powers below the order and cancel successors.
This validates finite-family reindexing. -/
private theorem six_powers_inj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 6) : Set.InjOn (fun k : ℕ ↦ χ ^ (k + 1)) (Finset.range 5 : Set ℕ) :=
  fun _ hi _ hj he ↦
  Nat.succ_injective
    (pow_injOn_Iio_orderOf (ho.symm ▸ Nat.succ_lt_succ (Finset.mem_range.mp hi))
      (ho.symm ▸ Nat.succ_lt_succ (Finset.mem_range.mp hj)) he)

/-- A sum over the cyclic-six family expands into its five distinct powers.
Input: an order-six character and any additive summand. Reindex through the injective power
map and expand the finite range. This supplies actual trace, cost and total identities. -/
private theorem sum_six_family {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 6)
    {A : Type*} [AddCommMonoid A] (f : DirichletCharacter ℂ q → A) :
    (∑ ψ ∈ cyclicSixFamily χ, f ψ) = f χ + f (χ ^ 2) + f (χ ^ 3) + f (χ ^ 4) + f (χ ^ 5) := by
  classical
  rw [cyclicSixFamily, Finset.sum_image (six_powers_inj χ ho)]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_one, zero_add]

/-- The fifth and fourth powers of an order-six character are the two inverses.
Input: exact order six. Multiply by the generator or its square and use the sixth power.
This pairs the full nonprincipal family into its real conjugate contributions. -/
private theorem six_inverse_powers {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 6) : χ ^ 5 = χ⁻¹ ∧ χ ^ 4 = (χ ^ 2)⁻¹ :=
  let h6 : χ ^ 6 = 1 := ho ▸ pow_orderOf_eq_one χ
  ⟨eq_inv_iff_mul_eq_one.mpr ((pow_succ χ 5).symm.trans h6),
    eq_inv_iff_mul_eq_one.mpr ((pow_add χ 4 2).symm.trans h6)⟩

/-- The actual cyclic-six trace depends only on conjugate-pair weight totals.
Input: exact order six, arbitrary weights and a residue. Expand all five terms, pair inverse
real values and collect coefficients. No equality between conjugate weights is assumed. -/
theorem cyclic_six_trace_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 6)
    (w : DirichletCharacter ℂ q → ℝ) (z : ZMod q) :
    NumberTheory.weightedCharacterTrace (cyclicSixFamily χ) w z =
      (w χ + w (χ ^ 5)) * (χ z).re + (w (χ ^ 2) + w (χ ^ 4)) * ((χ ^ 2) z).re +
        w (χ ^ 3) * ((χ ^ 3) z).re := by
  have hp := six_inverse_powers χ ho
  rw [NumberTheory.weightedCharacterTrace, sum_six_family χ ho, hp.1, hp.2,
    inverse_character_re χ z, inverse_character_re (χ ^ 2) z]
  ring

/-- The actual cyclic-six conductor cost depends only on conjugate-pair totals.
Input: exact order six and arbitrary weights. Inverse characters have equal conductors;
expand the five terms and collect them. This supplies exact endpoint costs. -/
theorem cyclic_six_weight_cost {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 6)
    (w : DirichletCharacter ℂ q → ℝ) :
    NumberTheory.weightedConductorLogSum (cyclicSixFamily χ) w =
      (w χ + w (χ ^ 5)) * Real.log χ.conductor +
        (w (χ ^ 2) + w (χ ^ 4)) * Real.log (χ ^ 2).conductor +
        w (χ ^ 3) * Real.log (χ ^ 3).conductor := by
  have hp := six_inverse_powers χ ho
  rw [NumberTheory.weightedConductorLogSum, sum_six_family χ ho, hp.1, hp.2,
    DirichletCharacter.conductor_inv, DirichletCharacter.conductor_inv]
  ring

/-- The actual cyclic-six total is the sum of its two pair totals and quadratic weight.
Input: exact order six and arbitrary weights. Expand the five-character finite sum.
This transfers normalization to the grouped trace coordinates. -/
theorem cyclic_six_weight_total {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 6)
    (w : DirichletCharacter ℂ q → ℝ) :
    NumberTheory.characterWeightTotal (cyclicSixFamily χ) w =
      (w χ + w (χ ^ 5)) + (w (χ ^ 2) + w (χ ^ 4)) + w (χ ^ 3) := by
  rw [NumberTheory.characterWeightTotal, sum_six_family χ ho]
  ring

/-- The actual cyclic-six weighted trace satisfies the three affine penalty constraints.
Input: a normalized arbitrary weight function and a penalty above the three affine values.
Use the finite unit-value classification; nonunit values all vanish. This supplies the
actual trace certificate independently of smoothing or a chosen analytic coefficient. -/
theorem cyclic_six_trace_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 6)
    (w : DirichletCharacter ℂ q → ℝ)
    (hw : NumberTheory.characterWeightTotal (cyclicSixFamily χ) w = 1) {m : ℝ}
    (hm1 : -(1 / 2 : ℝ) + (w (χ ^ 2) + w (χ ^ 4)) + 3 / 2 * w (χ ^ 3) ≤ m)
    (hm2 : 1 / 2 - 3 / 2 * w (χ ^ 3) ≤ m) (hm3 : 1 - 2 * (w (χ ^ 2) + w (χ ^ 4)) ≤ m) (z : ZMod q) :
    -m ≤ NumberTheory.weightedCharacterTrace (cyclicSixFamily χ) w z := by
  rw [cyclic_six_trace_eq χ ho w]
  by_cases hu : IsUnit z
  · rcases hu with ⟨u, rfl⟩
    exact six_grouped_unit_lower χ ho u ((cyclic_six_weight_total χ ho w).symm.trans hw) hm1 hm2 hm3
  · simp only [χ.map_nonunit hu, (χ ^ 2).map_nonunit hu, (χ ^ 3).map_nonunit hu, Complex.zero_re,
      mul_zero, add_zero]
    linarith only [hm1, hm2, hm3]

/-- An order-six character attains the primitive cubic and quadratic unit pattern.
Input: exact order six. Lift a full-order image element, so its square is nontrivial cubic
and its cube is nontrivial quadratic. This supplies actual extremal trace test units. -/
private theorem six_unit_patterns {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 6) :
    ∃ u : (ZMod q)ˣ, ((χ ^ 2) (u : ZMod q)).re = -1 / 2 ∧ (χ ^ 3) (u : ZMod q) = -1 := by
  obtain ⟨u, hu⟩ := NumberTheory.exists_unit_character_order χ
  have hv := (NumberTheory.character_unit_value_order χ u).trans (hu.trans ho)
  have ho2 : orderOf (χ ^ 2) = 3 :=
    (orderOf_pow χ).trans (congrArg (fun n : ℕ ↦ n / Nat.gcd n 2) ho)
  have h3o : orderOf ((χ ^ 3) (u : ZMod q)) = 2 :=
    (congrArg orderOf (MulChar.pow_apply_coe χ 3 u)).trans
      ((orderOf_pow' (χ (u : ZMod q)) (show (3 : ℕ) ≠ 0 from of_decide_eq_true rfl)).trans
        (congrArg (fun n : ℕ ↦ n / Nat.gcd n 3) hv))
  have h3 : (χ ^ 3) (u : ZMod q) = -1 :=
    (sq_eq_one_iff.mp (orderOf_eq_prime_iff.mp h3o).1).resolve_left (orderOf_eq_prime_iff.mp h3o).2
  have hn2 : (χ ^ 2) (u : ZMod q) ≠ 1 :=
    (MulChar.pow_apply_coe χ 2 u).symm ▸
      pow_ne_one_of_lt_orderOf (of_decide_eq_true rfl)
        (hv.symm ▸ (show 2 < 6 from of_decide_eq_true rfl))
  exact ⟨u, cubic_nontrivial_re (χ ^ 2) ho2 u hn2, h3⟩

/-- Evaluating a character at a unit power equals evaluating its character power.
Input: any character, unit and natural exponent. Use multiplicativity and the pointwise
power formula. This evaluates the powers of an extremal unit without a new image search. -/
private theorem character_unit_pow_apply {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (u : (ZMod q)ˣ) (k : ℕ) : χ ((u ^ k : (ZMod q)ˣ) : ZMod q) = (χ ^ k) (u : ZMod q) :=
  (map_pow χ (u : ZMod q) k).trans (MulChar.pow_apply_coe χ k u).symm

/-- A primitive unit realizes the first cyclic-six affine trace penalty.
Input: normalized arbitrary weights, cubic real part minus one half and quadratic sign
minus one. Use the exact grouped trace and its real factorization, then normalize weights. -/
private theorem six_trace_first {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 6)
    (w : DirichletCharacter ℂ q → ℝ)
    (hw : NumberTheory.characterWeightTotal (cyclicSixFamily χ) w = 1) (u : (ZMod q)ˣ)
    (h2 : ((χ ^ 2) (u : ZMod q)).re = -1 / 2) (h3 : (χ ^ 3) (u : ZMod q) = -1) :
    NumberTheory.weightedCharacterTrace (cyclicSixFamily χ) w (u : ZMod q) =
      -(-(1 / 2 : ℝ) + (w (χ ^ 2) + w (χ ^ 4)) + 3 / 2 * w (χ ^ 3)) := by
  have hn := (cyclic_six_weight_total χ ho w).symm.trans hw
  rw [cyclic_six_trace_eq χ ho, six_unit_real_factor χ ho u, h3, Complex.neg_re, Complex.one_re, h2]
  nlinarith only [hn]

/-- The square of a primitive unit realizes the second cyclic-six penalty.
Input: normalized arbitrary weights and the nontrivial cubic real value. Character powers
make the quadratic sign one while preserving the cubic real part. Normalize the trace. -/
private theorem six_trace_second {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 6) (w : DirichletCharacter ℂ q → ℝ)
    (hw : NumberTheory.characterWeightTotal (cyclicSixFamily χ) w = 1) (u : (ZMod q)ˣ)
    (h2 : ((χ ^ 2) (u : ZMod q)).re = -1 / 2) :
    NumberTheory.weightedCharacterTrace (cyclicSixFamily χ) w ((u ^ 2 : (ZMod q)ˣ) : ZMod q) =
      -(1 / 2 - 3 / 2 * w (χ ^ 3)) := by
  have ho2 : orderOf (χ ^ 2) = 3 :=
    (orderOf_pow χ).trans (congrArg (fun n : ℕ ↦ n / Nat.gcd n 2) ho)
  have ho3 : orderOf (χ ^ 3) = 2 :=
    (orderOf_pow χ).trans (congrArg (fun n : ℕ ↦ n / Nat.gcd n 3) ho)
  have hn := (cyclic_six_weight_total χ ho w).symm.trans hw
  rw [cyclic_six_trace_eq χ ho, character_unit_pow_apply χ u 2,
    character_unit_pow_apply (χ ^ 2) u 2, character_unit_pow_apply (χ ^ 3) u 2,
    cubic_square_re (χ ^ 2) ho2 u, show (χ ^ 3) ^ 2 = 1 from ho3 ▸ pow_orderOf_eq_one _,
    MulChar.one_apply_coe, Complex.one_re, h2]
  nlinarith only [hn]

/-- The cube of a primitive unit realizes the third cyclic-six penalty.
Input: normalized arbitrary weights and quadratic sign minus one. The cubic contribution
becomes one and the generator sign stays minus one. Evaluate the exact grouped trace. -/
private theorem six_trace_third {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 6)
    (w : DirichletCharacter ℂ q → ℝ)
    (hw : NumberTheory.characterWeightTotal (cyclicSixFamily χ) w = 1) (u : (ZMod q)ˣ)
    (h3 : (χ ^ 3) (u : ZMod q) = -1) :
    NumberTheory.weightedCharacterTrace (cyclicSixFamily χ) w ((u ^ 3 : (ZMod q)ˣ) : ZMod q) =
      -(1 - 2 * (w (χ ^ 2) + w (χ ^ 4))) := by
  have ho2 : orderOf (χ ^ 2) = 3 :=
    (orderOf_pow χ).trans (congrArg (fun n : ℕ ↦ n / Nat.gcd n 2) ho)
  have hn := (cyclic_six_weight_total χ ho w).symm.trans hw
  rw [cyclic_six_trace_eq χ ho, character_unit_pow_apply χ u 3,
    character_unit_pow_apply (χ ^ 2) u 3, show (χ ^ 2) ^ 3 = 1 from ho2 ▸ pow_orderOf_eq_one _,
    MulChar.one_apply_coe, Units.val_pow_eq_pow_val, map_pow (χ ^ 3) (u : ZMod q) 3, h3]
  norm_num only [Complex.neg_re, Complex.one_re]
  nlinarith only [hn]

/-- An actual cyclic-six trace certificate forces all three affine penalty constraints.
Input: arbitrary normalized weights and a global trace lower bound. Choose a full-image-order
unit and evaluate the certificate at that unit, its square and its cube. Thus each scalar
constraint is necessary for the actual character trace, not an extra optimization assumption. -/
theorem cyclic_six_penalty_necessary {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 6) (w : DirichletCharacter ℂ q → ℝ)
    (hw : NumberTheory.characterWeightTotal (cyclicSixFamily χ) w = 1) {m : ℝ}
    (htrace : ∀ z : ZMod q, -m ≤ NumberTheory.weightedCharacterTrace (cyclicSixFamily χ) w z) :
    -(1 / 2 : ℝ) + (w (χ ^ 2) + w (χ ^ 4)) + 3 / 2 * w (χ ^ 3) ≤ m ∧
      1 / 2 - 3 / 2 * w (χ ^ 3) ≤ m ∧ 1 - 2 * (w (χ ^ 2) + w (χ ^ 4)) ≤ m :=
  Exists.elim (six_unit_patterns χ ho) fun u hu ↦
    ⟨neg_le_neg_iff.mp ((htrace u).trans_eq (six_trace_first χ ho w hw u hu.1 hu.2)),
      neg_le_neg_iff.mp ((htrace (u ^ 2 : (ZMod q)ˣ)).trans_eq (six_trace_second χ ho w hw u hu.1)),
      neg_le_neg_iff.mp ((htrace (u ^ 3 : (ZMod q)ˣ)).trans_eq (six_trace_third χ ho w hw u hu.2))⟩

/-- The three cyclic-six affine constraints exactly characterize the actual trace bound.
Input: an order-six character and arbitrary normalized weights. Finite value classification
proves sufficiency; the three realized unit patterns prove necessity. Conjugate weights
need not be equal, since their pair totals determine both directions. -/
theorem cyclic_six_trace_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 6)
    (w : DirichletCharacter ℂ q → ℝ)
    (hw : NumberTheory.characterWeightTotal (cyclicSixFamily χ) w = 1) {m : ℝ} :
    (∀ z : ZMod q, -m ≤ NumberTheory.weightedCharacterTrace (cyclicSixFamily χ) w z) ↔
      -(1 / 2 : ℝ) + (w (χ ^ 2) + w (χ ^ 4)) + 3 / 2 * w (χ ^ 3) ≤ m ∧
        1 / 2 - 3 / 2 * w (χ ^ 3) ≤ m ∧ 1 - 2 * (w (χ ^ 2) + w (χ ^ 4)) ≤ m :=
  ⟨cyclic_six_penalty_necessary χ ho w hw, fun hm z ↦
    cyclic_six_trace_lower χ ho w hw hm.1 hm.2.1 hm.2.2 z⟩

/-- Each positive exponent below six belongs to the selected finite family.
Input: an exponent index below five. Use its defining image witness. This supplies the
individual nonnegative weights used by grouped endpoint comparisons. -/
private theorem mem_six_power_succ {q : ℕ} (χ : DirichletCharacter ℂ q) {i : ℕ} (hi : i < 5) :
    χ ^ (i + 1) ∈ cyclicSixFamily χ :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

/-- Nonnegative weights on the cyclic-six family give nonnegative pair totals.
Input: actual family weight nonnegativity. Apply it at the five defining powers and add
the two pairs. This supplies the nonnegative coordinates of the scalar simplex. -/
private theorem six_group_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    (w : DirichletCharacter ℂ q → ℝ) (hw : ∀ ψ ∈ cyclicSixFamily χ, 0 ≤ w ψ) :
    0 ≤ w χ + w (χ ^ 5) ∧ 0 ≤ w (χ ^ 2) + w (χ ^ 4) ∧ 0 ≤ w (χ ^ 3) :=
  ⟨add_nonneg
      (hw χ
        (Eq.mp (congrArg (fun ψ ↦ ψ ∈ cyclicSixFamily χ) (pow_one χ))
          (mem_six_power_succ χ (show 0 < 5 from of_decide_eq_true rfl))))
      (hw _ (mem_six_power_succ χ (show 4 < 5 from of_decide_eq_true rfl))),
    add_nonneg (hw _ (mem_six_power_succ χ (show 1 < 5 from of_decide_eq_true rfl)))
      (hw _ (mem_six_power_succ χ (show 3 < 5 from of_decide_eq_true rfl))),
    hw _ (mem_six_power_succ χ (show 2 < 5 from of_decide_eq_true rfl))⟩

/-- A character power has no larger kernel-mass conductor cost at the same allowance.
Input: a positive Mellin kernel, any exponent and allowance. Conductor divisibility gives
the log ordering, and positive kernel mass preserves it. This supplies both partial costs. -/
private theorem power_effective_cost_le (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ℕ) (E : ℝ) :
    K.mass * Real.log (χ ^ k).conductor + E ≤ K.mass * Real.log χ.conductor + E :=
  add_le_add
    (mul_le_mul_of_nonneg_left
      (Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (χ ^ k).conductor_ne_zero))
        (Nat.cast_le.mpr
          (Nat.le_of_dvd (Nat.pos_of_ne_zero χ.conductor_ne_zero) (χ.conductor_pow_dvd k))))
      (MellinKernel.mass_pos K).le)
    (le_refl E)

/-- The three cyclic-six endpoints dominate every actual normalized weighted prefix deficit.
Input: arbitrary nonnegative family weights, actual total one and an actual trace certificate.
Derive the affine penalty constraints from realized units, use actual conductor cost ordering
and the nonnegative principal tail, then apply the scalar endpoint reduction. No separate
affine trace assumptions, equal conjugate weights or sampled estimates are required. -/
theorem cyclic_six_prefix_endpoint (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 6) (w : DirichletCharacter ℂ q → ℝ)
    (hw : ∀ ψ ∈ cyclicSixFamily χ, 0 ≤ w ψ)
    (hW : NumberTheory.characterWeightTotal (cyclicSixFamily χ) w = 1) {m x : ℝ}
    (htrace : ∀ z : ZMod q, -m ≤ NumberTheory.weightedCharacterTrace (cyclicSixFamily χ) w z)
    (hx : 0 < x) (E : ℝ) (T : Finset ℕ) :
    let P := ∑ n ∈ T, (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
    let F := (∑' n : ℕ, MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
    let c₂ := K.mass * Real.log (χ ^ 3).conductor + E
    let c₃ := K.mass * Real.log (χ ^ 2).conductor + E
    let c₆ := K.mass * Real.log χ.conductor + E
    min (c₂ - P + (F - P))
        (min (c₃ - P + (F - P) / 2) ((2 * c₆ + 2 * c₃ + c₂) / 5 - P + (F - P) / 5)) ≤
      K.mass * NumberTheory.weightedConductorLogSum (cyclicSixFamily χ) w + E - P +
        m * (F - P) := by
  dsimp only
  have hg := six_group_nonneg χ w hw
  have hn := (cyclic_six_weight_total χ ho w).symm.trans hW
  have hm := cyclic_six_penalty_necessary χ ho w hW htrace
  have hb :=
    cyclic_six_endpoint (c₂ := K.mass * Real.log (χ ^ 3).conductor + E) (c₃ :=
      K.mass * Real.log (χ ^ 2).conductor + E) (c₆ := K.mass * Real.log χ.conductor + E) (P :=
      ∑ n ∈ T, (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re) hg.1 hg.2.1 hg.2.2 hn
      (principal_tail_nonneg K (q := q) hx T) (power_effective_cost_le K χ 3 E)
      (power_effective_cost_le K χ 2 E) hm.1 hm.2.1 hm.2.2
  rw [cyclic_six_weight_cost χ ho w]
  nlinarith only [hb, congrArg (fun v : ℝ ↦ E * v) hn]

/-- Every member of the cyclic-six family is nonprincipal at exact order six.
Input: exact order six and actual family membership. Positive powers below the order cannot
be one. This supplies the nonprincipality hypothesis of the analytic prime criterion. -/
private theorem six_family_nonprincipal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 6) : ∀ ψ ∈ cyclicSixFamily χ, ψ ≠ 1 :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  fun _ hψ ↦
  Exists.elim (Finset.mem_image.mp hψ) fun i hi ↦
    hi.2 ▸
      pow_ne_one_of_lt_orderOf (Nat.succ_ne_zero i)
        (ho.symm ▸ Nat.succ_lt_succ (Finset.mem_range.mp hi.1))

/-- Every selected cyclic-six power annihilates the generator's unit kernel.
Input: a character and family membership. Its kernel annihilator consists of its powers,
so all selected positive powers belong. This supplies the actual subgroup comparison. -/
private theorem six_family_annihilates {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∀ ψ ∈ cyclicSixFamily χ, ψ ∈ NumberTheory.subgroupAnnihilator χ.toUnitHom.ker :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  fun _ hψ ↦
  Exists.elim (Finset.mem_image.mp hψ) fun i hi ↦
    hi.2 ▸
      (NumberTheory.kernel_annihilator_zpowers χ).symm ▸
      (Subgroup.zpowers χ).pow_mem (Subgroup.mem_zpowers χ) (i + 1)

/-- A negative actual cyclic-six deficit yields an actual least outside prime under GRH.
Input: arbitrary nonnegative normalized family weights and a supported principal prefix.
Use the exact optimal affine trace penalty, proved family nonprincipality and annihilation,
and the general weighted criterion. Constants and thresholds are uniform in the modulus
and weights. The strict gap remains explicit, unlike the separate closed conductor radii. -/
theorem cyclic_six_least_criterion (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ η : ℝ,
          0 < η →
            ∃ Q : ℕ,
              20000 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ χ : DirichletCharacter ℂ q,
                      orderOf χ = 6 →
                        ∀ w : DirichletCharacter ℂ q → ℝ,
                          (∀ ψ ∈ cyclicSixFamily χ, 0 ≤ w ψ) →
                            NumberTheory.characterWeightTotal (cyclicSixFamily χ) w = 1 →
                              ∀ X x : ℝ,
                                2 ≤ x →
                                  ∀ T : Finset ℕ,
                                    (∀ n ∈ T, (n : ℝ) ≤ X) →
                                      let P :=
                                        ∑ n ∈ T,
                                          (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x
                                              n).re
                                      let F :=
                                        (∑' n : ℕ,
                                            MellinKernel.summand K (1 : DirichletCharacter ℂ q) x
                                              n).re
                                      let E :=
                                        η * Real.log q +
                                          C * (1 + Real.log q * Real.log x / Real.sqrt x)
                                      let m :=
                                        max
                                          (-(1 / 2 : ℝ) + (w (χ ^ 2) + w (χ ^ 4)) +
                                            3 / 2 * w (χ ^ 3))
                                          (max (1 / 2 - 3 / 2 * w (χ ^ 3))
                                            (1 - 2 * (w (χ ^ 2) + w (χ ^ 4))))
                                      K.mass *
                                                  NumberTheory.weightedConductorLogSum
                                                    (cyclicSixFamily χ) w +
                                                E -
                                              P +
                                            m * (F - P) <
                                          0 →
                                        ∃ p : ℕ,
                                          IsLeast (NumberTheory.primesOutside q χ.toUnitHom.ker) p ∧
                                            (p : ℝ) ≤ X := by
  obtain ⟨C, hC, hb⟩ := weighted_least_prime_criterion K hg
  refine ⟨C, hC, fun η hη ↦ ?_⟩
  obtain ⟨Q, hQ, hb⟩ := hb η hη
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq χ ho w hw hW X x hx T hT P F E m hgap
  have htrace : ∀ z : ZMod q, -m ≤ NumberTheory.weightedCharacterTrace (cyclicSixFamily χ) w z :=
    cyclic_six_trace_lower χ ho w hW (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
  apply
    hb q hq χ.toUnitHom.ker (cyclicSixFamily χ) w hw (six_family_nonprincipal χ ho)
      (six_family_annihilates χ) m X x hx htrace T hT
  rw [hW, mul_one]
  change
    K.mass * NumberTheory.weightedConductorLogSum (cyclicSixFamily χ) w + E < (1 + m) * P - m * F
  nlinarith only [hgap]

end PseudoPrime.LLS.PaperStatements
