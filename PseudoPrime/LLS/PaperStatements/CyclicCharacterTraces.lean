/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.WeightedEndpointReduction
public import PseudoPrime.LLS.PaperStatements.WeightedCyclicEndpoints
public import PseudoPrime.NumberTheory.CharacterKernelPowers
public import PseudoPrime.NumberTheory.CharacterTracePenalty

/-! # Actual cyclic character traces and endpoint costs

The trace certificates refer to actual characters and normalized nonnegative weight
profiles. Finite unit-value classifications and conjugate pairs determine their penalties.
These application-specific profiles feed the common principal-prefix endpoint comparison;
the coefficients are not asserted to prove unrestricted small-index prime bounds.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A complex fourth root of unity is one of the four explicit roots.
Input: its fourth power is one. Apply the square-root dichotomy twice, using the square
of the imaginary unit. This is the finite unit-value classification for cyclic-four traces. -/
private theorem fourth_root_cases {z : ℂ} (hz : z ^ 4 = 1) :
    z = 1 ∨ z = -1 ∨ z = Complex.I ∨ z = -Complex.I :=
  Or.elim (sq_eq_one_iff.mp ((pow_mul z 2 2).symm.trans hz))
    (fun h ↦ Or.elim (sq_eq_one_iff.mp h) Or.inl (fun hn ↦ Or.inr (Or.inl hn)))
    (fun h ↦ Or.inr (Or.inr (sq_eq_sq_iff_eq_or_eq_neg.mp (h.trans Complex.I_sq.symm))))

/-- The cyclic-four grouped trace is bounded by its two affine penalties.
Input: a fourth root of unity and a penalty above t and 1-2t. Enumerate its four values
and check the linear inequalities. This avoids assuming an unproved trace estimate. -/
private theorem fourth_root_trace {z : ℂ} (hz : z ^ 4 = 1) {t m : ℝ} (hm1 : t ≤ m)
    (hm2 : 1 - 2 * t ≤ m) : -m ≤ (1 - t) * z.re + t * (z ^ 2).re := by
  rcases fourth_root_cases hz with h | h | h | h
  all_goals subst z
  all_goals
    norm_num only [one_pow, neg_one_sq, Complex.one_re, Complex.neg_re, Complex.I_sq, Complex.I_re,
      neg_sq, mul_zero, mul_one, add_zero]
  all_goals linarith only [hm1, hm2]

/-- The first three powers of an order-four character are pairwise distinct.
Input: exact order four. Injectivity below the order separates exponents one, two and three.
This validates the actual three-character weight sum and conductor cost. -/
private theorem four_power_distinct {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) : χ ≠ χ ^ 2 ∧ χ ≠ χ * χ ^ 2 ∧ χ ^ 2 ≠ χ * χ ^ 2 :=
  let hn (i j : ℕ) (hi : i < 4) (hj : j < 4) (hij : i ≠ j) : χ ^ i ≠ χ ^ j := fun h ↦
    hij (pow_injOn_Iio_orderOf (ho.symm ▸ hi) (ho.symm ▸ hj) h)
  let h3 : χ * χ ^ 2 = χ ^ 3 := (pow_succ' χ 2).symm
  ⟨fun h ↦
    hn 1 2 (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_true rfl)
      ((pow_one χ).trans h),
    fun h ↦
    hn 1 3 (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_true rfl)
      ((pow_one χ).trans (h.trans h3)),
    fun h ↦
    hn 2 3 (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_true rfl) (h.trans h3)⟩

/-- The third power of an order-four character has the generator's real value.
Input: exact order four and any residue. Identify the third power with the inverse and use
complex character conjugation. This combines the actual conjugate-pair terms. -/
private theorem four_inverse_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 4)
    (z : ZMod q) : ((χ ^ 3) z).re = (χ z).re :=
  let h3 : χ ^ 3 = χ⁻¹ :=
    eq_inv_iff_mul_eq_one.mpr
      ((pow_succ χ 3).symm.trans (show χ ^ 4 = 1 from ho ▸ pow_orderOf_eq_one χ))
  (congrArg Complex.re
        ((congrArg (fun ψ : DirichletCharacter ℂ q ↦ ψ z) h3).trans
          (MulChar.star_apply' χ z).symm)).trans
    (Complex.conj_re _)

/-- The value of an order-four character at a unit is a fourth root of unity.
Input: exact order four and an ambient unit. Evaluate the character power identity at it.
This supplies the premise of the finite trace classification. -/
private theorem four_unit_value {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 4)
    (u : (ZMod q)ˣ) : χ (u : ZMod q) ^ 4 = 1 :=
  (MulChar.pow_apply_coe χ 4 u).symm.trans
    ((congrArg (fun ψ : DirichletCharacter ℂ q ↦ ψ (u : ZMod q)) (ho ▸ pow_orderOf_eq_one χ)).trans
      (MulChar.one_apply_coe u))

/-- The actual three-character trace equals its grouped conjugate-pair expression.
Input: an order-four character, any weight parameter and residue. Expand the finite weight
sum and identify the third-power real part with the generator. This connects the grouped
scalar trace to the common weighted-character prime criterion. -/
theorem cyclic_four_trace_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 4)
    (t : ℝ) (z : ZMod q) :
    NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple χ (χ ^ 2))
        (NumberTheory.quadraticTripleWeight χ (χ ^ 2) ((1 - t) / 2) t ((1 - t) / 2)) z =
      (1 - t) * (χ z).re + t * ((χ ^ 2) z).re := by
  have hd := four_power_distinct χ ho
  rw [NumberTheory.quadraticTripleTrace_eq χ (χ ^ 2) hd.1 hd.2.1 hd.2.2,
    show χ * χ ^ 2 = χ ^ 3 from (pow_succ' χ 2).symm, four_inverse_re χ ho z]
  ring

/-- The actual cyclic-four trace has the two-pattern lower bound on every residue.
Input: nonnegative t and a penalty above t and 1-2t. At units use the fourth-root cases;
at nonunits every character value vanishes. This supplies an actual trace certificate. -/
theorem cyclic_four_trace_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 4)
    {t m : ℝ} (ht : 0 ≤ t) (hm1 : t ≤ m) (hm2 : 1 - 2 * t ≤ m) (z : ZMod q) :
    -m ≤
      NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple χ (χ ^ 2))
        (NumberTheory.quadraticTripleWeight χ (χ ^ 2) ((1 - t) / 2) t ((1 - t) / 2)) z := by
  rw [cyclic_four_trace_eq χ ho]
  by_cases hu : IsUnit z
  · rcases hu with ⟨u, rfl⟩
    simpa only [MulChar.pow_apply_coe] using fourth_root_trace (four_unit_value χ ho u) hm1 hm2
  · rw [χ.map_nonunit hu, (χ ^ 2).map_nonunit hu, Complex.zero_re, mul_zero, mul_zero, zero_add]
    exact neg_nonpos.mpr (ht.trans hm1)

/-- The actual cyclic-four weighted cost is the normalized pair of conductor logs.
Input: an order-four character and weight parameter. Expand the finite conductor sum and
use conductor invariance of the third power. This supplies the actual endpoint cost. -/
theorem cyclic_four_weight_cost {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 4)
    (t : ℝ) :
    NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple χ (χ ^ 2))
        (NumberTheory.quadraticTripleWeight χ (χ ^ 2) ((1 - t) / 2) t ((1 - t) / 2)) =
      (1 - t) * Real.log χ.conductor + t * Real.log (χ ^ 2).conductor := by
  have hd := four_power_distinct χ ho
  have hc :=
    NumberTheory.conductor_pow_coprime χ
      (ho.symm ▸ (show Nat.Coprime 3 4 from of_decide_eq_true rfl))
  rw [NumberTheory.quadraticTripleWeight_cost χ (χ ^ 2) hd.1 hd.2.1 hd.2.2,
    show χ * χ ^ 2 = χ ^ 3 from (pow_succ' χ 2).symm, hc]
  ring

/-- The actual cyclic-four weight profile has total one.
Input: exact character order four and any weight parameter. Expand its three distinct
weights and collect terms. This is the normalization used by the prime criterion. -/
theorem cyclic_four_weight_total {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) (t : ℝ) :
    NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple χ (χ ^ 2))
        (NumberTheory.quadraticTripleWeight χ (χ ^ 2) ((1 - t) / 2) t ((1 - t) / 2)) =
      1 := by
  have hd := four_power_distinct χ ho
  rw [NumberTheory.quadraticTripleWeight_total χ (χ ^ 2) hd.1 hd.2.1 hd.2.2]
  ring

/-- The conductor log of a power does not exceed the original conductor log.
Input: any character at nonzero level and any exponent. Use conductor divisibility,
positive conductors and monotonicity of log. This supplies the endpoint cost ordering. -/
private theorem power_log_conductor_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (k : ℕ) :
    Real.log (χ ^ k).conductor ≤ Real.log χ.conductor :=
  Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (χ ^ k).conductor_ne_zero))
    (Nat.cast_le.mpr
      (Nat.le_of_dvd (Nat.pos_of_ne_zero χ.conductor_ne_zero) (χ.conductor_pow_dvd k)))

/-- The cyclic-four endpoints dominate its actual normalized weighted principal deficit.
Input: a kernel, order-four character, nonnegative normalized pair weights, valid trace
penalty and positive scale. The principal tail is nonnegative and the square conductor
cost is no larger. Apply the scalar endpoint theorem with these actual quantities.
This removes continuous cyclic-four weight search from the common prefix criterion. -/
theorem cyclic_four_prefix_endpoint (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 4) {t m x : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hm1 : t ≤ m) (hm2 : 1 - 2 * t ≤ m) (hx : 0 < x) (E : ℝ) (T : Finset ℕ) :
    let P := ∑ n ∈ T, (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
    let F := (∑' n : ℕ, MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
    let c₂ := K.mass * Real.log (χ ^ 2).conductor + E
    let c₄ := K.mass * Real.log χ.conductor + E
    min (c₂ - P + (F - P)) ((2 * c₄ + c₂) / 3 - P + (F - P) / 3) ≤
      K.mass *
              NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple χ (χ ^ 2))
                (NumberTheory.quadraticTripleWeight χ (χ ^ 2) ((1 - t) / 2) t ((1 - t) / 2)) +
            E -
          P +
        m * (F - P) := by
  dsimp only
  have hc :=
    add_le_add (mul_le_mul_of_nonneg_left (power_log_conductor_le χ 2) (MellinKernel.mass_pos K).le)
      (le_refl E)
  have hb :=
    cyclic_four_endpoint (c₂ := K.mass * Real.log (χ ^ 2).conductor + E) (c₄ :=
      K.mass * Real.log χ.conductor + E) (P :=
      ∑ n ∈ T, (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re) ht ht1
      (principal_tail_nonneg K (q := q) hx T) hc hm1 hm2
  rw [cyclic_four_weight_cost χ ho t]
  nlinarith only [hb]

/-- A complex value of exact order four has square minus one.
Input: exact order four. Its square squares to one and cannot already be one.
This identifies the realized extremal unit values for cyclic-four traces. -/
private theorem fourth_order_square {z : ℂ} (ho : orderOf z = 4) : z ^ 2 = -1 :=
  (sq_eq_one_iff.mp
        ((pow_mul z 2 2).symm.trans (show z ^ 4 = 1 from ho ▸ pow_orderOf_eq_one z))).resolve_left
    (pow_ne_one_of_lt_orderOf (of_decide_eq_true rfl)
      (ho.symm ▸ (show 2 < 4 from of_decide_eq_true rfl)))

/-- A complex value of exact order four has zero real part.
Input: exact order four. Its square is minus one, so it equals the imaginary unit or its
negative. This supplies the first actual extremal trace pattern. -/
private theorem fourth_order_re {z : ℂ} (ho : orderOf z = 4) : z.re = 0 :=
  Or.elim (sq_eq_sq_iff_eq_or_eq_neg.mp ((fourth_order_square ho).trans Complex.I_sq.symm))
    (fun h ↦ (congrArg Complex.re h).trans Complex.I_re)
    (fun h ↦
      (congrArg Complex.re h).trans
        ((Complex.neg_re Complex.I).trans ((congrArg Neg.neg Complex.I_re).trans neg_zero)))

/-- An order-four character realizes both nontrivial grouped trace patterns.
Input: exact order four. Choose a unit of full image order and also use its square.
The first has zero real value and square minus one; the second has character value minus one. -/
private theorem four_unit_patterns {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) :
    ∃ u : (ZMod q)ˣ,
      (χ (u : ZMod q)).re = 0 ∧ χ (u : ZMod q) ^ 2 = -1 ∧ χ ((u ^ 2 : (ZMod q)ˣ) : ZMod q) = -1 :=
  Exists.elim (NumberTheory.exists_unit_character_order χ) fun u hu ↦
    let hv := (NumberTheory.character_unit_value_order χ u).trans (hu.trans ho)
    ⟨u, fourth_order_re hv, fourth_order_square hv,
      (map_pow χ (u : ZMod q) 2).trans (fourth_order_square hv)⟩

/-- Every actual cyclic-four trace certificate bounds both affine penalties.
Input: exact order four and a lower trace bound at every residue. Evaluate it at a unit of
full character-image order and its square. These realize penalties t and 1-2t, so the
scalar endpoint constraints follow from the certificate instead of extra assumptions. -/
theorem cyclic_four_penalty_necessary {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) {t m : ℝ}
    (htrace :
      ∀ z : ZMod q,
        -m ≤
          NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple χ (χ ^ 2))
            (NumberTheory.quadraticTripleWeight χ (χ ^ 2) ((1 - t) / 2) t ((1 - t) / 2)) z) :
    t ≤ m ∧ 1 - 2 * t ≤ m := by
  obtain ⟨u, hr, hz, hu2⟩ := four_unit_patterns χ ho
  have h1 := htrace (u : ZMod q)
  rw [cyclic_four_trace_eq χ ho, MulChar.pow_apply_coe, hz, hr, Complex.neg_re, Complex.one_re,
    mul_zero, zero_add] at h1
  have h2 := htrace ((u ^ 2 : (ZMod q)ˣ) : ZMod q)
  rw [cyclic_four_trace_eq χ ho, MulChar.pow_apply_coe, hu2, neg_one_sq, Complex.neg_re,
    Complex.one_re] at h2
  constructor <;> nlinarith only [h1, h2]

/-- A real sum over an order-four character family expands into its first three powers.
Input: exact order four and any real summand. The three characters are distinct, so expand
the finite insertions. This supports arbitrary original weights, including unequal pairs. -/
private theorem sum_four_family {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 4)
    (f : DirichletCharacter ℂ q → ℝ) :
    (∑ ψ ∈ NumberTheory.quadraticTriple χ (χ ^ 2), f ψ) = f χ + f (χ ^ 2) + f (χ ^ 3) := by
  classical
  have hd := four_power_distinct χ ho
  have hA : χ ∉ ({χ ^ 2, χ * χ ^ 2} : Finset (DirichletCharacter ℂ q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, hd.1, hd.2.1, or_self, not_false_eq_true]
  have hB : χ ^ 2 ∉ ({χ * χ ^ 2} : Finset (DirichletCharacter ℂ q)) := fun h ↦
    hd.2.2 (Finset.mem_singleton.mp h)
  rw [NumberTheory.quadraticTriple, Finset.sum_insert hA, Finset.sum_insert hB,
    Finset.sum_singleton, show χ * χ ^ 2 = χ ^ 3 from (pow_succ' χ 2).symm, add_assoc]

/-- The total of arbitrary cyclic-four weights is their three individual weights.
Input: exact order four and any weight function. Expand the actual family sum.
This transfers normalization to the quadratic coordinate and conjugate-pair total. -/
theorem cyclic_four_arbitrary_total {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) (w : DirichletCharacter ℂ q → ℝ) :
    NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple χ (χ ^ 2)) w =
      w χ + w (χ ^ 2) + w (χ ^ 3) :=
  sum_four_family χ ho w

/-- Normalization identifies the conjugate-pair total with one minus the quadratic weight.
Input: arbitrary actual cyclic-four weights of total one. Rearrange the exact three-term
sum. This removes any equality assumption between conjugate weights. -/
private theorem four_pair_total {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 4)
    (w : DirichletCharacter ℂ q → ℝ)
    (hw : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple χ (χ ^ 2)) w = 1) :
    w χ + w (χ ^ 3) = 1 - w (χ ^ 2) :=
  eq_sub_iff_add_eq.mpr
    ((add_right_comm (w χ) (w (χ ^ 3)) (w (χ ^ 2))).trans
      ((cyclic_four_arbitrary_total χ ho w).symm.trans hw))

/-- The normalized actual cyclic-four trace depends only on its quadratic weight.
Input: arbitrary weights with actual total one and any residue. The inverse pair has equal
real values, so combine its two weights. This justifies reducing all normalized profiles. -/
theorem cyclic_four_arbitrary_trace {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) (w : DirichletCharacter ℂ q → ℝ)
    (hw : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple χ (χ ^ 2)) w = 1)
    (z : ZMod q) :
    NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple χ (χ ^ 2)) w z =
      (1 - w (χ ^ 2)) * (χ z).re + w (χ ^ 2) * ((χ ^ 2) z).re := by
  rw [NumberTheory.weightedCharacterTrace, sum_four_family χ ho, four_inverse_re χ ho z]
  nlinarith only [congrArg (fun v : ℝ ↦ v * (χ z).re) (four_pair_total χ ho w hw)]

/-- The normalized actual cyclic-four cost depends only on the quadratic weight.
Input: arbitrary weights of total one. The inverse pair has equal conductors; expand and
combine the pair. This gives the exact cost without assuming equal conjugate weights. -/
theorem cyclic_four_arbitrary_cost {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) (w : DirichletCharacter ℂ q → ℝ)
    (hw : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple χ (χ ^ 2)) w = 1) :
    NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple χ (χ ^ 2)) w =
      (1 - w (χ ^ 2)) * Real.log χ.conductor + w (χ ^ 2) * Real.log (χ ^ 2).conductor := by
  have hc :=
    NumberTheory.conductor_pow_coprime χ
      (ho.symm ▸ (show Nat.Coprime 3 4 from of_decide_eq_true rfl))
  rw [NumberTheory.weightedConductorLogSum, sum_four_family χ ho, hc]
  nlinarith only [congrArg (fun v : ℝ ↦ v * Real.log χ.conductor) (four_pair_total χ ho w hw)]

/-- An arbitrary normalized cyclic-four trace certificate forces both affine constraints.
Input: actual total one and a global actual trace lower bound. Its grouped expression
coincides with the symmetric profile, whose extremal unit values were proved to occur. -/
theorem cyclic_four_arbitrary_penalty {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) (w : DirichletCharacter ℂ q → ℝ)
    (hW : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple χ (χ ^ 2)) w = 1) {m : ℝ}
    (htrace :
      ∀ z : ZMod q,
        -m ≤ NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple χ (χ ^ 2)) w z) :
    w (χ ^ 2) ≤ m ∧ 1 - 2 * w (χ ^ 2) ≤ m :=
  cyclic_four_penalty_necessary χ ho fun z ↦
    (htrace z).trans_eq
      ((cyclic_four_arbitrary_trace χ ho w hW z).trans
        (cyclic_four_trace_eq χ ho (w (χ ^ 2)) z).symm)

/-- A nonnegative normalized cyclic-four family has quadratic weight between zero and one.
Input: actual family nonnegativity and total one. Apply nonnegativity at its three members
and use the exact sum. This supplies the scalar interpolation parameter range. -/
private theorem four_weight_range {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) (w : DirichletCharacter ℂ q → ℝ)
    (hw : ∀ ψ ∈ NumberTheory.quadraticTriple χ (χ ^ 2), 0 ≤ w ψ)
    (hW : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple χ (χ ^ 2)) w = 1) :
    0 ≤ w (χ ^ 2) ∧ w (χ ^ 2) ≤ 1 := by
  classical
  have ha := hw χ (Finset.mem_insert_self _ _)
  have hb := hw (χ ^ 2) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hc :=
    hw (χ * χ ^ 2)
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  rw [show χ * χ ^ 2 = χ ^ 3 from (pow_succ' χ 2).symm] at hc
  have hn := (cyclic_four_arbitrary_total χ ho w).symm.trans hW
  exact ⟨hb, by linarith only [ha, hc, hn]⟩

/-- Both affine constraints give a trace lower bound for arbitrary normalized weights.
Input: actual nonnegative weights, total one and the two affine bounds. Use the identical
symmetric grouped expression. This supplies the exact converse to the necessary constraints. -/
theorem cyclic_four_arbitrary_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) (w : DirichletCharacter ℂ q → ℝ)
    (hw : ∀ ψ ∈ NumberTheory.quadraticTriple χ (χ ^ 2), 0 ≤ w ψ)
    (hW : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple χ (χ ^ 2)) w = 1) {m : ℝ}
    (hm1 : w (χ ^ 2) ≤ m) (hm2 : 1 - 2 * w (χ ^ 2) ≤ m) (z : ZMod q) :
    -m ≤ NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple χ (χ ^ 2)) w z :=
  (cyclic_four_trace_lower χ ho (four_weight_range χ ho w hw hW).1 hm1 hm2 z).trans_eq
    ((cyclic_four_trace_eq χ ho (w (χ ^ 2)) z).trans (cyclic_four_arbitrary_trace χ ho w hW z).symm)

/-- The two affine constraints characterize the actual trace bound for arbitrary weights.
Input: a nonnegative actual cyclic-four family of total one. Combine realized unit-value
necessity with the finite-root sufficiency. Unequal conjugate weights are fully included. -/
theorem cyclic_four_arbitrary_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) (w : DirichletCharacter ℂ q → ℝ)
    (hw : ∀ ψ ∈ NumberTheory.quadraticTriple χ (χ ^ 2), 0 ≤ w ψ)
    (hW : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple χ (χ ^ 2)) w = 1)
    {m : ℝ} :
    (∀ z : ZMod q,
        -m ≤ NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple χ (χ ^ 2)) w z) ↔
      w (χ ^ 2) ≤ m ∧ 1 - 2 * w (χ ^ 2) ≤ m :=
  ⟨cyclic_four_arbitrary_penalty χ ho w hW, fun hm z ↦
    cyclic_four_arbitrary_lower χ ho w hw hW hm.1 hm.2 z⟩

/-- The cyclic-four endpoints dominate every actual normalized weighted prefix deficit.
Input: arbitrary nonnegative family weights, total one and an actual trace certificate.
Derive both affine constraints from realized unit values and use the exact grouped cost.
The actual principal prefix and full tail are retained, without extra scalar hypotheses. -/
theorem cyclic_four_actual_endpoint (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 4) (w : DirichletCharacter ℂ q → ℝ)
    (hw : ∀ ψ ∈ NumberTheory.quadraticTriple χ (χ ^ 2), 0 ≤ w ψ)
    (hW : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple χ (χ ^ 2)) w = 1)
    {m x : ℝ}
    (htrace :
      ∀ z : ZMod q,
        -m ≤ NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple χ (χ ^ 2)) w z)
    (hx : 0 < x) (E : ℝ) (T : Finset ℕ) :
    let P := ∑ n ∈ T, (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
    let F := (∑' n : ℕ, MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
    let c₂ := K.mass * Real.log (χ ^ 2).conductor + E
    let c₄ := K.mass * Real.log χ.conductor + E
    min (c₂ - P + (F - P)) ((2 * c₄ + c₂) / 3 - P + (F - P) / 3) ≤
      K.mass * NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple χ (χ ^ 2)) w + E -
          P +
        m * (F - P) :=
  let hr := four_weight_range χ ho w hw hW
  let hm := cyclic_four_arbitrary_penalty χ ho w hW htrace
  ((cyclic_four_weight_cost χ ho (w (χ ^ 2))).trans (cyclic_four_arbitrary_cost χ ho w hW).symm) ▸
    cyclic_four_prefix_endpoint K χ ho hr.1 hr.2 hm.1 hm.2 hx E T

/-- The selected order-four character family contains only nonprincipal characters.
Input: exact order four and actual family membership. Powers one, two and three lie below
the order, hence cannot be one. This supplies the analytic criterion's nonprincipality. -/
private theorem four_family_nonprincipal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) : ∀ ψ ∈ NumberTheory.quadraticTriple χ (χ ^ 2), ψ ≠ 1 :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  let hp (k : ℕ) (hk0 : k ≠ 0) (hk4 : k < 4) : χ ^ k ≠ 1 :=
    pow_ne_one_of_lt_orderOf hk0 (ho.symm ▸ hk4)
  let h1 : χ ≠ 1 :=
    Eq.mp (congrArg (fun ψ ↦ ψ ≠ 1) (pow_one χ))
      (hp 1 (of_decide_eq_true rfl) (of_decide_eq_true rfl))
  let h2 := hp 2 (of_decide_eq_true rfl) (of_decide_eq_true rfl)
  let h3 := hp 3 (of_decide_eq_true rfl) (of_decide_eq_true rfl)
  fun _ hψ ↦
  Or.elim (Finset.mem_insert.mp hψ) (fun h ↦ h.symm ▸ h1)
    (fun h ↦
      Or.elim (Finset.mem_insert.mp h) (fun h ↦ h.symm ▸ h2)
        (fun h ↦ ((Finset.mem_singleton.mp h).trans (pow_succ' χ 2).symm).symm ▸ h3))

/-- All selected order-four characters annihilate the generator's unit kernel.
Input: an actual family member. The generator lies in its kernel annihilator and that
annihilator is closed under powers and products. This supplies the subgroup comparison. -/
private theorem four_family_annihilates {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∀ ψ ∈ NumberTheory.quadraticTriple χ (χ ^ 2),
      ψ ∈ NumberTheory.subgroupAnnihilator χ.toUnitHom.ker :=
  let hc : χ ∈ NumberTheory.subgroupAnnihilator χ.toUnitHom.ker :=
    (NumberTheory.kernel_annihilator_zpowers χ).symm ▸ Subgroup.mem_zpowers χ
  NumberTheory.quadraticTriple_annihilates _ χ (χ ^ 2) hc
    ((NumberTheory.subgroupAnnihilator χ.toUnitHom.ker).pow_mem hc 2)

/-- A negative actual cyclic-four deficit gives an actual least outside prime under GRH.
Input: arbitrary nonnegative normalized family weights and a supported principal prefix.
Use the proved exact canonical trace penalty and actual family admissibility in the common
weighted criterion. Constants and thresholds remain uniform. The strict gap is an explicit
input and is distinguished from the independently closed conductor-radius bounds. -/
theorem cyclic_four_least_criterion (K : MellinKernel)
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
                      orderOf χ = 4 →
                        ∀ w : DirichletCharacter ℂ q → ℝ,
                          (∀ ψ ∈ NumberTheory.quadraticTriple χ (χ ^ 2), 0 ≤ w ψ) →
                            NumberTheory.characterWeightTotal
                                  (NumberTheory.quadraticTriple χ (χ ^ 2)) w =
                                1 →
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
                                      let m := max (w (χ ^ 2)) (1 - 2 * w (χ ^ 2))
                                      K.mass *
                                                  NumberTheory.weightedConductorLogSum
                                                    (NumberTheory.quadraticTriple χ (χ ^ 2)) w +
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
  have htrace :
    ∀ z : ZMod q,
      -m ≤ NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple χ (χ ^ 2)) w z :=
    cyclic_four_arbitrary_lower χ ho w hw hW (le_max_left _ _) (le_max_right _ _)
  apply
    hb q hq χ.toUnitHom.ker (NumberTheory.quadraticTriple χ (χ ^ 2)) w hw
      (four_family_nonprincipal χ ho) (four_family_annihilates χ) m X x hx htrace T hT
  rw [hW, mul_one]
  change
    K.mass * NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple χ (χ ^ 2)) w + E <
      (1 + m) * P - m * F
  nlinarith only [hgap]

end PseudoPrime.LLS.PaperStatements
