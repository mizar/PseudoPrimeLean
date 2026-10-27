/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveCharacterLabels
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.BoundedPrimitiveLabels
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison

/-! # Half-scale arithmetic errors transferred to an injectively labelled primitive family -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For nonzero level and positive scale, the logarithmic character sum differs
from its primitive source by at most `omega(q) log(x)^2/2`. Majorize the level-quotient
prime factors by those of the level. This gives one correction uniform in the character. -/
theorem norm_characterLogWeightedSum_sub_primitive_le_level {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    ‖characterLogWeightedSum x χ - characterLogWeightedSum x χ.primitiveCharacter‖ ≤
      (1 / 2 : ℝ) * q.primeFactors.card * (Real.log x) ^ 2 := by
  have hb := norm_characterLogWeightedSum_sub_primitive_le x χ hx
  have hc : ((q / χ.conductor).primeFactors.card : ℝ) ≤ q.primeFactors.card := by
    exact_mod_cast
      Finset.card_le_card
        (Nat.primeFactors_mono (Nat.div_dvd_of_dvd χ.conductor_dvd_level) (NeZero.ne q))
  have hm :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num only : (0 : ℝ) ≤ 1 / 2))
      (sq_nonneg (Real.log x))
  exact hb.trans hm

/-- At scale at least two and nonzero level, the character half-scale norm is
bounded by its primitive half-scale norm plus `omega(q) log(x)^2`. Apply the two
endpoint level-change bounds, compare their nonnegative logarithms, and use the
triangle inequality. This transfers the exact half-scale error to primitive characters. -/
theorem norm_characterLogWeightedSum_half_le_primitive_add_level_error {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 2 ≤ x) :
    ‖characterLogWeightedSum x χ - characterLogWeightedSum (x / 2) χ‖ ≤
      ‖characterLogWeightedSum x χ.primitiveCharacter -
            characterLogWeightedSum (x / 2) χ.primitiveCharacter‖ +
        (q.primeFactors.card : ℝ) * (Real.log x) ^ 2 := by
  have hxpos : 0 < x := by linarith only [hx]
  have hypos : 0 < x / 2 := div_pos hxpos (by norm_num only)
  have hlogy : 0 ≤ Real.log (x / 2) := Real.log_nonneg (by linarith only [hx])
  have hlog := Real.log_le_log hypos (by linarith only [hx] : x / 2 ≤ x)
  have hlogsq : (Real.log (x / 2)) ^ 2 ≤ (Real.log x) ^ 2 := by nlinarith only [hlogy, hlog]
  have hb := norm_characterLogWeightedSum_sub_primitive_le_level χ hxpos
  have hc := norm_characterLogWeightedSum_sub_primitive_le_level χ hypos
  have hm :=
    mul_le_mul_of_nonneg_left hlogsq
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) (Nat.cast_nonneg q.primeFactors.card))
  have he :
    characterLogWeightedSum x χ - characterLogWeightedSum (x / 2) χ =
      (characterLogWeightedSum x χ.primitiveCharacter -
            characterLogWeightedSum (x / 2) χ.primitiveCharacter) +
          (characterLogWeightedSum x χ - characterLogWeightedSum x χ.primitiveCharacter) -
        (characterLogWeightedSum (x / 2) χ -
          characterLogWeightedSum (x / 2) χ.primitiveCharacter) := by
    ring
  rw [he]
  have ht :=
    (norm_sub_le
          ((characterLogWeightedSum x χ.primitiveCharacter -
              characterLogWeightedSum (x / 2) χ.primitiveCharacter) +
            (characterLogWeightedSum x χ - characterLogWeightedSum x χ.primitiveCharacter))
          (characterLogWeightedSum (x / 2) χ -
            characterLogWeightedSum (x / 2) χ.primitiveCharacter)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  linarith only [ht, hb, hc, hm]

open Classical in
/-- For a finite character family at nonzero level and scale at least two, the
sum of half-scale norms is bounded by the primitive-label norm sum plus the family
cardinality times `omega(q) log(x)^2`. Sum the pointwise transfer and use injectivity
of conductor-character labels. The primitive error sum has no extra family factor. -/
theorem sum_norm_characterLogWeightedSum_half_le_primitive_labels {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) {x : ℝ} (hx : 2 ≤ x) :
    ∑ χ ∈ S, ‖characterLogWeightedSum x χ - characterLogWeightedSum (x / 2) χ‖ ≤
      (∑ p ∈ S.image primitiveCharacterLabel,
          ‖characterLogWeightedSum x p.2 - characterLogWeightedSum (x / 2) p.2‖) +
        (S.card : ℝ) * ((q.primeFactors.card : ℝ) * (Real.log x) ^ 2) := by
  classical
  have hb :=
    Finset.sum_le_sum (s := S)
      (fun χ _ ↦ norm_characterLogWeightedSum_half_le_primitive_add_level_error χ hx)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hb
  rw [Finset.sum_image (fun χ _ ψ _ h ↦ primitiveCharacterLabel_injective q h)]
  exact hb

open Classical in
/-- For a finite family at nonzero level below a conductor cutoff, its half-scale
norm sum is bounded by the sum over bounded primitive labels plus the explicit
level-change correction. Use the exact reindexing identity after primitive transfer.
This supplies the family type consumed by the occurrence-ledger density estimates. -/
theorem sum_norm_characterLogWeightedSum_half_le_bounded_primitive_labels {q Q : ℕ} [NeZero q]
    (hq : q ≤ Q) (S : Finset (DirichletCharacter ℂ q)) {x : ℝ} (hx : 2 ≤ x) :
    ∑ χ ∈ S, ‖characterLogWeightedSum x χ - characterLogWeightedSum (x / 2) χ‖ ≤
      (∑ p ∈ S.image (boundedPrimitiveCharacterLabel hq),
          ‖characterLogWeightedSum x p.2 - characterLogWeightedSum (x / 2) p.2‖) +
        (S.card : ℝ) * ((q.primeFactors.card : ℝ) * (Real.log x) ^ 2) := by
  have hb := sum_norm_characterLogWeightedSum_half_le_primitive_labels S hx
  rw [sum_primitiveCharacterLabel_eq_bounded hq S
      (fun p ↦ ‖characterLogWeightedSum x p.2 - characterLogWeightedSum (x / 2) p.2‖)] at hb
  exact hb

end PseudoPrime.AnalyticNumberTheory.Arithmetic
