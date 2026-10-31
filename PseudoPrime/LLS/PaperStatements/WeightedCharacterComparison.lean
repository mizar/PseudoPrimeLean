/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.PaperStatements.SubgroupKernelComparison
public import PseudoPrime.NumberTheory.CharacterWeights

/-! # Weighted character traces and the actual Mellin comparison -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At positive scale and nonzero index, the weighted real Mellin summands
factor into the nonnegative Mangoldt-transform weight and the weighted trace.
Use the real-valued transform to remove imaginary cross terms. -/
theorem weighted_summand_re_eq {q : ℕ} [NeZero q] (K : MellinKernel)
    (S : Finset (DirichletCharacter ℂ q)) (w : DirichletCharacter ℂ q → ℝ) {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : n ≠ 0) :
    (∑ χ ∈ S, w χ * ((MellinKernel.summand K) χ x n).re) =
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * (K.transform (n / x)).re *
        NumberTheory.weightedCharacterTrace S w n := by
  have hu : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx
  have hi : (K.transform (n / x)).im = 0 := K.mellin_real _ hu
  rw [NumberTheory.weightedCharacterTrace, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  rw [MellinKernel.summand, ite_eq_right hn, Complex.mul_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hi, mul_zero, sub_zero]
  ring

/-- A uniform trace lower bound minus m controls each weighted Mellin term
by minus m times its principal term. Treat nonunits separately so primes
dividing the ambient modulus remain excluded; use positivity at units. -/
theorem weighted_summand_lower {q : ℕ} [NeZero q] (K : MellinKernel)
    (S : Finset (DirichletCharacter ℂ q)) (w : DirichletCharacter ℂ q → ℝ) {m x : ℝ} (hx : 0 < x)
    (htrace : ∀ z : ZMod q, -m ≤ NumberTheory.weightedCharacterTrace S w z) (n : ℕ) :
    -m * ((MellinKernel.summand K) (1 : DirichletCharacter ℂ q) x n).re ≤
      ∑ χ ∈ S, w χ * ((MellinKernel.summand K) χ x n).re := by
  by_cases hn : n = 0
  · subst n
    simp only [MellinKernel.summand, ite_true, Complex.zero_re, mul_zero, Finset.sum_const_zero,
      le_refl]
  · by_cases hu : IsUnit (n : ZMod q)
    · let R := (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * (K.transform (n / x)).re
      have hR : 0 ≤ R :=
        mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
          (K.mellin_nonneg _ (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx))
      have he : ((MellinKernel.summand K) (1 : DirichletCharacter ℂ q) x n).re = R := by
        simp only [MellinKernel.summand, ite_eq_right hn, MulChar.one_apply hu, mul_one,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, R]
      rw [he, weighted_summand_re_eq K S w hx hn]
      have hm := mul_le_mul_of_nonneg_left (htrace n) hR
      dsimp only [R] at hm ⊢
      nlinarith only [hm]
    · have hz (χ : DirichletCharacter ℂ q) : (MellinKernel.summand K) χ x n = 0 := by
        simp only [MellinKernel.summand, ite_eq_right hn, MulChar.map_nonunit χ hu, mul_zero,
          zero_mul]
      simp only [hz, Complex.zero_re, mul_zero, Finset.sum_const_zero, le_refl]

/-- If no eligible prime through X lies outside H, the weighted Mellin
aggregate at each index through X equals total weight times the principal term.
Only unit prime powers contribute, and their prime bases already lie in H. -/
theorem weighted_summand_prefix_eq {q : ℕ} [NeZero q] (K : MellinKernel) (H : Subgroup (ZMod q)ˣ)
    (S : Finset (DirichletCharacter ℂ q)) (w : DirichletCharacter ℂ q → ℝ)
    (hS : ∀ χ ∈ S, χ ∈ NumberTheory.subgroupAnnihilator H) {X x : ℝ}
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p)
    {n : ℕ} (hbound : (n : ℝ) ≤ X) :
    (∑ χ ∈ S, w χ * ((MellinKernel.summand K) χ x n).re) =
      NumberTheory.characterWeightTotal S w *
        ((MellinKernel.summand K) (1 : DirichletCharacter ℂ q) x n).re := by
  by_cases hp : IsPrimePow n
  · by_cases hu : IsUnit (n : ZMod q)
    · have hres :=
        NumberTheory.residueInSubgroup_of_primePow_of_noSmallPrimes H hsmall hp
          ((ZMod.isUnit_iff_coprime n q).mp hu) hbound
      obtain ⟨u, huH, he⟩ := hres
      have hχ (χ : DirichletCharacter ℂ q) (hχ : χ ∈ S) : χ n = 1 :=
        he ▸ (NumberTheory.mem_subgroupAnnihilator_iff H χ).mp (hS χ hχ) u huH
      have h1 : (1 : DirichletCharacter ℂ q) n = 1 := MulChar.one_apply hu
      rw [NumberTheory.characterWeightTotal, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ hχS
      simp only [MellinKernel.summand, hχ χ hχS, h1]
    · have hz (χ : DirichletCharacter ℂ q) : (MellinKernel.summand K) χ x n = 0 := by
        simp only [MellinKernel.summand, MulChar.map_nonunit χ hu, mul_zero, zero_mul, ite_self]
      simp only [hz, Complex.zero_re, mul_zero, Finset.sum_const_zero]
  · have hz (χ : DirichletCharacter ℂ q) : (MellinKernel.summand K) χ x n = 0 :=
      MellinKernel.summand_eq_zero_of_not_primePow K χ x hp
    simp only [hz, Complex.zero_re, mul_zero, Finset.sum_const_zero]

/-- Under witness absence through X, any finite principal prefix supported
through X is controlled by the actual full weighted character series and
m times the full principal series, with coefficient total weight plus m.
Sum the nonnegative shifted terms using absolute convergence. -/
theorem weighted_noSmall_comparison {q : ℕ} [NeZero q] (K : MellinKernel) (H : Subgroup (ZMod q)ˣ)
    (S : Finset (DirichletCharacter ℂ q)) (w : DirichletCharacter ℂ q → ℝ)
    (hS : ∀ χ ∈ S, χ ∈ NumberTheory.subgroupAnnihilator H) {m X x : ℝ} (hx : 0 < x)
    (htrace : ∀ z : ZMod q, -m ≤ NumberTheory.weightedCharacterTrace S w z)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p)
    (T : Finset ℕ) (hT : ∀ n ∈ T, (n : ℝ) ≤ X) :
    (NumberTheory.characterWeightTotal S w + m) *
          (∑ n ∈ T, ((MellinKernel.summand K) (1 : DirichletCharacter ℂ q) x n).re) -
        m * (∑' n : ℕ, (MellinKernel.summand K) (1 : DirichletCharacter ℂ q) x n).re ≤
      ∑ χ ∈ S, w χ * (∑' n : ℕ, (MellinKernel.summand K) χ x n).re := by
  have hC :=
    hasSum_sum (s := S)
      (fun χ _ ↦
        HasSum.mul_left (w χ) (Complex.hasSum_re (MellinKernel.summable_summand K χ hx).hasSum))
  have hP :=
    HasSum.mul_left m
      (Complex.hasSum_re (MellinKernel.summable_summand K (1 : DirichletCharacter ℂ q) hx).hasSum)
  have hsum := hC.add hP
  have hnonneg (n : ℕ) :
    0 ≤
      (∑ χ ∈ S, w χ * ((MellinKernel.summand K) χ x n).re) +
        m * ((MellinKernel.summand K) (1 : DirichletCharacter ℂ q) x n).re := by
    have he := weighted_summand_lower K S w hx htrace n
    linarith only [he]
  have hs := hsum.summable.sum_le_tsum T (fun n _ ↦ hnonneg n)
  rw [hsum.tsum_eq] at hs
  have hpre :
    (∑ n ∈ T,
        ((∑ χ ∈ S, w χ * ((MellinKernel.summand K) χ x n).re) +
          m * ((MellinKernel.summand K) (1 : DirichletCharacter ℂ q) x n).re)) =
      (NumberTheory.characterWeightTotal S w + m) *
        (∑ n ∈ T, ((MellinKernel.summand K) (1 : DirichletCharacter ℂ q) x n).re) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [weighted_summand_prefix_eq K H S w hS hsmall (hT n hn)]
    ring
  rw [hpre] at hs
  linarith only [hs]

/-- A strict gap between the actual weighted character series and the
principal prefix-tail comparison yields an actual least eligible outside
prime at most X. Contradict witness absence and take the natural least element.
No analytic estimate or trace certificate is hidden in a new proposition. -/
theorem least_weighted_prime_of_gap {q : ℕ} [NeZero q] (K : MellinKernel) (H : Subgroup (ZMod q)ˣ)
    (S : Finset (DirichletCharacter ℂ q)) (w : DirichletCharacter ℂ q → ℝ)
    (hS : ∀ χ ∈ S, χ ∈ NumberTheory.subgroupAnnihilator H) {m X x : ℝ} (hx : 0 < x)
    (htrace : ∀ z : ZMod q, -m ≤ NumberTheory.weightedCharacterTrace S w z) (T : Finset ℕ)
    (hT : ∀ n ∈ T, (n : ℝ) ≤ X)
    (hgap :
      (∑ χ ∈ S, w χ * (∑' n : ℕ, (MellinKernel.summand K) χ x n).re) <
        (NumberTheory.characterWeightTotal S w + m) *
            (∑ n ∈ T, ((MellinKernel.summand K) (1 : DirichletCharacter ℂ q) x n).re) -
          m * (∑' n : ℕ, (MellinKernel.summand K) (1 : DirichletCharacter ℂ q) x n).re) :
    ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤ X := by
  classical
  have hex : ∃ p : ℕ, p ∈ NumberTheory.primesOutside q H ∧ (p : ℝ) ≤ X := by
    by_contra hn
    have hs : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p := by
      intro p hp hq hx
      by_contra hout
      exact hn ⟨p, ⟨hp, hq, hout⟩, hx⟩
    exact (not_lt_of_ge (weighted_noSmall_comparison K H S w hS hx htrace hs T hT)) hgap
  have hnon : ∃ p : ℕ, p ∈ NumberTheory.primesOutside q H := by
    obtain ⟨p, hp, _⟩ := hex
    exact ⟨p, hp⟩
  obtain ⟨p, hp, hpx⟩ := hex
  refine ⟨Nat.find hnon, ⟨Nat.find_spec hnon, fun _ hr ↦ Nat.find_min' hnon hr⟩, ?_⟩
  exact (Nat.cast_le.mpr (Nat.find_min' hnon hp)).trans hpx

end PseudoPrime.LLS.PaperStatements
