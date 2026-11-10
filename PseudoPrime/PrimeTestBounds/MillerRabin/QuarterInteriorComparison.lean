/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInteriorAverage
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterHighSupport

/-! # Interior subgroup arithmetic comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If no prime through the cutoff rejects the input, the finite scale-one
principal sum supplies a signed arithmetic credit. Apply the subgroup
scale-one inequality to the prime support conditions. -/
theorem quarter_interior_credit {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {X : ℝ} (hX : 0 ≤ X)
    (hnone : ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n))
    (K : LLS.PaperStatements.MellinKernel) :
    letI := Classical.propDecidable
    (2 : ℝ) * (((PrimeTest.fermatSubgroup n).index : ℝ)) *
          (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 m).re) -
        2 * (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 m).re ≤
      ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator (PrimeTest.fermatSubgroup n)),
        ((∑' m : ℕ, K.summand χ.val.primitiveCharacter 1 m).re +
          (∑' m : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 m).re) := by
  classical
  have hs := prime_support_of_no_reject hn ho hnone
  have hlarge : ∀ p : ℕ, p.Prime → p ∣ n → X < (p : ℝ) := by
    intro p hp hd
    by_contra h
    exact (hs p hp (le_of_not_gt h)).1 hd
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup n (PrimeTest.fermatSubgroup n) p := by
    intro p hp _ hpX
    exact (hs p hp hpX).2
  exact K.scaleOne_pair_lower (PrimeTest.fermatSubgroup n) hX hlarge hsmall

/-- If no prime through the cutoff rejects the input, the finite principal
sum at any positive scale is bounded by the full principal sum and the
primitive-character average. Use subgroup orthogonality and prime support. -/
theorem quarter_interior_forward {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {X y : ℝ} (hX : 0 ≤ X)
    (hy : 0 < y)
    (hnone : ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n))
    (K : LLS.PaperStatements.MellinKernel) :
    letI := Classical.propDecidable
    ((PrimeTest.fermatSubgroup n).index : ℝ) *
        (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) y m).re) ≤
      (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) y m).re +
        ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator (PrimeTest.fermatSubgroup n)),
          (∑' m : ℕ, K.summand χ.val.primitiveCharacter y m).re := by
  classical
  let _ := Classical.propDecidable
  let H := PrimeTest.fermatSubgroup n
  let A := NumberTheory.subgroupAnnihilator H
  let F := fun χ : A ↦ (∑' m : ℕ, K.summand χ.val.primitiveCharacter y m).re
  have hs := prime_support_of_no_reject hn ho hnone
  have hlarge : ∀ p : ℕ, p.Prime → p ∣ n → ⌊X⌋₊ < p := by
    intro p hp hd
    apply (Nat.floor_lt hX).mpr
    by_contra h
    exact (hs p hp (le_of_not_gt h)).1 hd
  have hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ n → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup n H p := by
    intro p hp _ hpX
    exact (hs p hp hpX).2
  have hfinite :=
    LLS.PaperStatements.MellinKernel.principal_sum_level_one_of_no_divisor K (q := n) y hlarge
  have hI : Finset.Ioc 0 ⌊X⌋₊ = Finset.Icc 1 ⌊X⌋₊ := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Icc, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  have heq := congrArg Complex.re hfinite
  simp only [hI, Complex.re_sum] at heq
  have hc := K.principal_sum_le_primitive_of_noSmall H hy hsmall
  rw [heq] at hc
  have he := Finset.sum_erase_add (s := Finset.univ) F (Finset.mem_univ (1 : A))
  have hp : F (1 : A) = (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) y m).re :=
    congrArg Complex.re
      (tsum_congr (LLS.PaperStatements.MellinKernel.principal_primitive_summand_eq_level_one K y))
  rw [hp] at he
  change (H.index : ℝ) * _ ≤ ∑ χ : A, F χ at hc
  change (H.index : ℝ) * _ ≤ _ + ∑ χ ∈ Finset.univ.erase (1 : A), F χ
  linarith only [hc, he]

/-- Under GRH and absence of rejecting primes through an interior scale,
bound the joint finite principal sum by full principal sums, the conductor
sum and an explicit Gamma allowance. Combine the three arithmetic credits
with the annihilator character bound. -/
theorem quarter_interior_comparison {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {a X : ℝ}
    (ha : 0 < a) (hX : 1 ≤ X) (hbound : Real.log X ≤ 2 * a)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hnone : ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    let H := PrimeTest.fermatSubgroup n
    (H.index : ℝ) *
        ((∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) X m).re) +
          2 * (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 m).re)) ≤
      (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X m).re +
        (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X⁻¹ m).re +
        2 * (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 m).re +
        (4 * a - Real.log X) * LLS.PaperStatements.subgroupConductorLogSum H +
        (-6 * a + (3 / 2 : ℝ) * Real.log X + 18) * ((H.index : ℝ) - 1) := by
  classical
  let _ := Classical.propDecidable
  let K := LLS.PaperStatements.triangularMellinKernel ha
  let H := PrimeTest.fermatSubgroup n
  let A := NumberTheory.subgroupAnnihilator H
  let S := Finset.univ.erase (1 : A)
  have hx0 : 0 < X := zero_lt_one.trans_le hX
  have hf := quarter_interior_forward hn ho (zero_le_one.trans hX) hx0 hnone K
  have hr := quarter_interior_forward hn ho (zero_le_one.trans hX) (inv_pos.mpr hx0) hnone K
  have hc := quarter_interior_credit hn ho (zero_le_one.trans hX) hnone K
  have hu := quarter_interior_annihilator ha H hGRH hX hbound
  have hpos :
    0 ≤
      (H.index : ℝ) *
        (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) X⁻¹ m).re) :=
    mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun m _ ↦
        LLS.PaperStatements.MellinKernel.principal_summand_re_nonneg K (inv_pos.mpr hx0) m)
  have hinv (χ : A) :
    (∑' m : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ X⁻¹ m).re =
      (∑' m : ℕ, K.summand χ.val.primitiveCharacter X⁻¹ m).re := by
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact
      LLS.PaperStatements.MellinKernel.tsum_summand_inv_re_eq K χ.val.primitiveCharacter
        (inv_pos.mpr hx0)
  have heq := Finset.sum_congr (s₁ := S) rfl (fun χ _ ↦ hinv χ)
  have hone (χ : A) :
    (∑' m : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 m).re =
      (∑' m : ℕ, K.summand χ.val.primitiveCharacter 1 m).re := by
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact
      LLS.PaperStatements.MellinKernel.tsum_summand_inv_re_eq K χ.val.primitiveCharacter
        (by norm_num only)
  have heq1 := Finset.sum_congr (s₁ := S) rfl (fun χ _ ↦ hone χ)
  dsimp only at hf hr hc hu ⊢
  simp only [Finset.sum_add_distrib] at hc
  rw [heq1] at hc
  rw [heq] at hu
  linarith only [hf, hr, hc, hu, hpos]

end PseudoPrime.PrimeTestBounds.MillerRabin
