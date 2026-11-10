/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularDualScaleGeneral
public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroup
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangularSupport

/-! # Prime support in the quarter-bound high-index argument -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If an odd input above one has no rejecting prime up to `X`, each prime
up to `X` is coprime to the input and its residue belongs to the Fermat
subgroup. A prime divisor cannot pass strong Miller--Rabin, and every passing
residue lies in the Fermat subgroup. This supplies the support conditions for
the variable-width triangular comparison. -/
theorem prime_support_of_no_reject {n : ℕ} (hn : 1 < n) (ho : Odd n) {X : ℝ}
    (hnone : ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ∀ p : ℕ,
      p.Prime →
        (p : ℝ) ≤ X → ¬p ∣ n ∧ NumberTheory.residueInSubgroup n (PrimeTest.fermatSubgroup n) p := by
  intro p hp hpX
  have hpass : PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    by_contra hbad
    exact hnone ⟨p, hp, hpX, hbad⟩
  have hnot : ¬p ∣ n := fun hd ↦ PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hd hpass
  exact ⟨hnot, PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass⟩

/-- If a strict comparison reverses the scale-one arithmetic credit for a
Mellin kernel at cutoff `X ≥ 0`, an odd input above one has a rejecting prime
at most `X`. Assuming otherwise supplies the support conditions for the
general scale-one inequality, yielding a contradiction. -/
theorem exists_reject_of_scale_one_gap {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (K : LLS.PaperStatements.MellinKernel) {X : ℝ} (hX : 0 ≤ X)
    (hgap :
      letI := Classical.propDecidable
      (∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator (PrimeTest.fermatSubgroup n)),
          ((∑' m : ℕ, K.summand χ.val.primitiveCharacter 1 m).re +
            (∑' m : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 m).re)) <
        (2 : ℝ) * ((PrimeTest.fermatSubgroup n).index : ℝ) *
            (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 m).re) -
          2 * (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 m).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  classical
  by_contra hnone
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
  have hcredit := K.scaleOne_pair_lower (PrimeTest.fermatSubgroup n) hX hlarge hsmall
  exact (not_lt_of_ge hcredit) hgap

/-- If an odd input has no rejecting prime through the endpoint of a
positive-width triangular kernel, the nonprincipal scale-one pair sum is at
least twice the number of nonprincipal annihilator characters times the full
level-one principal sum. Support vanishing identifies the finite arithmetic
credit with the full sum; this is the scale-one input to the high-index gap. -/
theorem quarter_scale_one_pair_lower {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {a X : ℝ}
    (ha : 0 < a) (hX : 1 ≤ X) (hbound : 2 * a ≤ Real.log X)
    (hnone : ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    letI := Classical.propDecidable
    let K := LLS.PaperStatements.triangularMellinKernel ha
    (2 : ℝ) * (((PrimeTest.fermatSubgroup n).index : ℝ) - 1) *
        (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 m).re ≤
      ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator (PrimeTest.fermatSubgroup n)),
        ((∑' m : ℕ, K.summand χ.val.primitiveCharacter 1 m).re +
          (∑' m : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 m).re) := by
  classical
  let K := LLS.PaperStatements.triangularMellinKernel ha
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
  have hcredit :=
    K.scaleOne_pair_lower (PrimeTest.fermatSubgroup n) (zero_le_one.trans hX) hlarge hsmall
  have heq :=
    congrArg Complex.re (quarter_triangular_scale_one_sum ha hX hbound (1 : DirichletCharacter ℂ 1))
  simp only [Complex.re_sum] at heq
  change (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 m).re = _ at heq
  rw [← heq] at hcredit
  dsimp only at hcredit ⊢
  linarith only [hcredit]

/-- If an odd input has no rejecting prime through `X ≥ 1`, the Fermat index
times the finite level-one triangular sum at scale `X` is at most the full
level-one sum plus the nonprincipal primitive-character average. Subgroup
orthogonality and the absence of small prime divisors provide the two steps
needed to isolate the principal term in the high-index comparison. -/
theorem quarter_forward_principal_le {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {a X : ℝ}
    (ha : 0 < a) (hX : 1 ≤ X)
    (hnone : ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    letI := Classical.propDecidable
    let K := LLS.PaperStatements.triangularMellinKernel ha
    ((PrimeTest.fermatSubgroup n).index : ℝ) *
        (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) X m).re) ≤
      (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X m).re +
        ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator (PrimeTest.fermatSubgroup n)),
          (∑' m : ℕ, K.summand χ.val.primitiveCharacter X m).re := by
  classical
  let _ := Classical.propDecidable
  let H := PrimeTest.fermatSubgroup n
  let A := NumberTheory.subgroupAnnihilator H
  let K := LLS.PaperStatements.triangularMellinKernel ha
  let F := fun χ : A ↦ (∑' m : ℕ, K.summand χ.val.primitiveCharacter X m).re
  have hs := prime_support_of_no_reject hn ho hnone
  have hlarge : ∀ p : ℕ, p.Prime → p ∣ n → ⌊X⌋₊ < p := by
    intro p hp hd
    apply (Nat.floor_lt (zero_le_one.trans hX)).mpr
    by_contra h
    exact (hs p hp (le_of_not_gt h)).1 hd
  have hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ n → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup n H p := by
    intro p hp _ hpX
    exact (hs p hp hpX).2
  have hfinite :=
    LLS.PaperStatements.MellinKernel.principal_sum_level_one_of_no_divisor K (q := n) X hlarge
  have hI : Finset.Ioc 0 ⌊X⌋₊ = Finset.Icc 1 ⌊X⌋₊ := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Icc, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  have heq := congrArg Complex.re hfinite
  simp only [hI, Complex.re_sum] at heq
  have hc := K.principal_sum_le_primitive_of_noSmall H (zero_lt_one.trans_le hX) hsmall
  rw [heq] at hc
  have he := Finset.sum_erase_add (s := Finset.univ) F (Finset.mem_univ (1 : A))
  have hp : F (1 : A) = (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X m).re :=
    congrArg Complex.re
      (tsum_congr (LLS.PaperStatements.MellinKernel.principal_primitive_summand_eq_level_one K X))
  rw [hp] at he
  change (H.index : ℝ) * _ ≤ ∑ χ : A, F χ at hc
  change (H.index : ℝ) * _ ≤ _ + ∑ χ ∈ Finset.univ.erase (1 : A), F χ
  linarith only [hc, he]

/-- For `r ≥ 100`, a natural index above `floor r²` absorbs principal sums
bounded by `12r²` and `12r`: their quotient by the index is below 13. The
floor inequality and a polynomial comparison yield the scalar estimate for
the high-index triangular argument. -/
theorem quarter_high_index_cost {r S P : ℝ} {h : ℕ} (hr : 100 ≤ r) (hh : ⌊r ^ 2⌋₊ < h)
    (hS : S ≤ 12 * r ^ 2) (hP : P ≤ 12 * r) : (S + 2 * P) / h < 13 := by
  have hhR : (⌊r ^ 2⌋₊ : ℝ) + 1 ≤ h := by exact_mod_cast hh
  have hh' : r ^ 2 < (h : ℝ) := (Nat.lt_floor_add_one (r ^ 2)).trans_le hhR
  have hr0 : 0 < r := by linarith only [hr]
  have hh0 : (0 : ℝ) < h := lt_of_le_of_lt (sq_nonneg r) hh'
  apply (div_lt_iff₀ hh0).2
  have hr2 : 100 * r ≤ r ^ 2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hr) hr0.le]
  nlinarith only [hS, hP, hh', hr2]

end PseudoPrime.PrimeTestBounds.MillerRabin
