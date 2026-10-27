/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnramifiedCharacterReduction
public import PseudoPrime.LLS.MellinKernelPrimitiveSupport

/-! # Signed primitive comparison for character-subgroup Mellin averages

Primitive local orthogonality gives a nonnegative aggregate at every index.
Absolute convergence extends the sign to the complete smoothed series.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- At positive scale and a positive prime-power index, the real primitive
Mellin summand aggregate over a character subgroup is nonnegative.
Factor out the nonnegative real transform and Mangoldt weight, then apply
primitive local orthogonality. This supplies the prime-power sign. -/
private theorem primitive_primePow_summand_sum_re_nonneg (K : MellinKernel) {q p : ℕ} [NeZero q]
    (hp : p.Prime) {k : ℕ} (hk : 0 < k) (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] {x : ℝ}
    (hx : 0 < x) : 0 ≤ (∑ χ : S, K.summand χ.val.primitiveCharacter x (p ^ k)).re := by
  have hn : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  have hnpos : (0 : ℝ) < (p ^ k : ℕ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hu := div_pos hnpos hx
  have hi : (K.transform ((p ^ k : ℕ) / x)).im = 0 := K.mellin_real _ hu
  have hr : 0 ≤ (K.transform ((p ^ k : ℕ) / x)).re := K.mellin_nonneg _ hu
  have he :
    (∑ χ : S, K.summand χ.val.primitiveCharacter x (p ^ k)) =
      ((ArithmeticFunction.vonMangoldt (p ^ k) / Real.sqrt (p ^ k : ℕ) : ℝ) : ℂ) *
        (∑ χ : S, χ.val.primitiveCharacter (p ^ k)) *
        K.transform ((p ^ k : ℕ) / x) := by
    simp only [summand, ite_eq_right hn, Finset.sum_mul, Finset.mul_sum, Nat.cast_pow]
  rw [he, Complex.mul_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    hi, mul_zero, sub_zero]
  exact
    mul_nonneg
      (mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
        (NumberTheory.sum_primitive_prime_pow_re_nonneg hp S hk))
      hr

/-- At every natural index and positive scale, the real aggregate of primitive
Mellin summands over a finite character subgroup is nonnegative.
Prime powers use local orthogonality; all other indices have zero Mangoldt weight.
This controls every term of the signed primitive-level correction. -/
theorem primitive_summand_sum_re_nonneg (K : MellinKernel) {q n : ℕ} [NeZero q]
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] {x : ℝ} (hx : 0 < x) :
    0 ≤ (∑ χ : S, K.summand χ.val.primitiveCharacter x n).re := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    exact primitive_primePow_summand_sum_re_nonneg K hp hk S hx
  · have he : (∑ χ : S, K.summand χ.val.primitiveCharacter x n) = 0 :=
      Finset.sum_eq_zero (fun χ _ ↦ summand_eq_zero_of_not_primePow K χ.val.primitiveCharacter x hn)
    rw [he, Complex.zero_re]

/-- The real primitive-minus-original correction summed over a finite character
subgroup is nonnegative at every index and positive scale.
It vanishes on units of the original level; on nonunits it equals the primitive
aggregate. This is the local sign needed before summing the correction series. -/
theorem primitive_difference_sum_re_nonneg (K : MellinKernel) {q n : ℕ} [NeZero q]
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] {x : ℝ} (hx : 0 < x) :
    0 ≤ (∑ χ : S, (K.summand χ.val.primitiveCharacter x n - K.summand χ.val x n)).re := by
  by_cases hc : Nat.Coprime n q
  · simp only [primitive_summand_sub_eq_on_nonunits, ite_eq_left hc, Finset.sum_const_zero,
      Complex.zero_re, le_refl]
  · simp only [primitive_summand_sub_eq_on_nonunits, ite_eq_right hc]
    exact primitive_summand_sum_re_nonneg K S hx

/-- The full primitive-minus-original correction has nonnegative real part
after summing over a finite character subgroup. Absolute convergence permits
interchanging the finite and infinite sums, and every aggregate term is nonnegative.
This transfers the local sign to the complete smoothed series. -/
private theorem primitive_difference_tsum_sum_re_nonneg (K : MellinKernel) {q : ℕ} [NeZero q]
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] {x : ℝ} (hx : 0 < x) :
    0 ≤ (∑ χ : S, ∑' n : ℕ, (K.summand χ.val.primitiveCharacter x n - K.summand χ.val x n)).re := by
  have hs (χ : S) :
    Summable (fun n : ℕ ↦ K.summand χ.val.primitiveCharacter x n - K.summand χ.val x n) := by
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact (summable_summand K χ.val.primitiveCharacter hx).sub (summable_summand K χ.val hx)
  have he := Summable.tsum_finsetSum (fun χ (_ : χ ∈ Finset.univ) ↦ hs χ)
  rw [← he]
  have hi := (hasSum_sum (fun χ (_ : χ ∈ Finset.univ) ↦ (hs χ).hasSum)).summable
  change
    0 ≤
      Complex.reCLM
        (∑' n : ℕ, ∑ χ : S, (K.summand χ.val.primitiveCharacter x n - K.summand χ.val x n))
  rw [Complex.reCLM.map_tsum hi]
  exact tsum_nonneg (fun n ↦ primitive_difference_sum_re_nonneg K S hx)

/-- At positive scale, the real original-level Mellin aggregate over a finite
character subgroup is at most its primitive aggregate. Subtract the absolutely
convergent series and apply the nonnegative correction result.
This removes an absolute primitivization error from the subgroup comparison. -/
theorem sum_tsum_re_le_primitive (K : MellinKernel) {q : ℕ} [NeZero q]
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] {x : ℝ} (hx : 0 < x) :
    (∑ χ : S, ∑' n : ℕ, K.summand χ.val x n).re ≤
      (∑ χ : S, ∑' n : ℕ, K.summand χ.val.primitiveCharacter x n).re := by
  have h := primitive_difference_tsum_sum_re_nonneg K S hx
  have he :
    (∑ χ : S, ∑' n : ℕ, (K.summand χ.val.primitiveCharacter x n - K.summand χ.val x n)) =
      (∑ χ : S, ∑' n : ℕ, K.summand χ.val.primitiveCharacter x n) -
        (∑ χ : S, ∑' n : ℕ, K.summand χ.val x n) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro χ _
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact (summable_summand K χ.val.primitiveCharacter hx).tsum_sub (summable_summand K χ.val hx)
  rw [he, Complex.sub_re] at h
  linarith only [h]

/-- If every eligible prime below X lies in H, the subgroup index times the
finite principal sum is at most the real primitive-character average.
Combine the arithmetic no-small-prime lower bound with the signed aggregate
primitive comparison. This supplies the primitive analytic side directly,
without an absolute level-change error. -/
theorem principal_sum_le_primitive_average_of_noSmallPrimes (K : MellinKernel) {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) {x X : ℝ} (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re ≤
      ∑ χ : NumberTheory.subgroupAnnihilator H,
        (∑' n : ℕ, K.summand χ.val.primitiveCharacter x n).re := by
  have hc := sum_tsum_re_le_primitive K (NumberTheory.subgroupAnnihilator H) hx
  change
    Complex.reCLM (∑ χ : NumberTheory.subgroupAnnihilator H, ∑' n : ℕ, K.summand χ.val x n) ≤
      Complex.reCLM
        (∑ χ : NumberTheory.subgroupAnnihilator H,
          ∑' n : ℕ, K.summand χ.val.primitiveCharacter x n) at hc
  rw [map_sum, map_sum] at hc
  exact (principal_sum_le_average_of_noSmallPrimes K H hx hsmall).trans hc

end PseudoPrime.LLS.PaperStatements.MellinKernel
