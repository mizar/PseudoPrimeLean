/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LargeSieve

/-! # Pre-sifted large-sieve bounds

This module connects the squarefree Ramanujan lower bound to the factor-free additive
large-sieve estimate. The range-supported bound is the input for interval and hybrid versions.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: a modulus cutoff `Z`, a finite coefficient support, and coefficients whose supported
indices have no prime factor at most `Z`.

Claim: the primitive-character mean squares for `1 < q ≤ Z`, weighted by `log (Z / q)`, are
bounded by twice the rational additive mean square over reduced frequencies up to `Z`.

Proof: sum the squarefree Ramanujan lower bound over moduli, reindex the resulting pair family,
and compare it to the common rational-frequency mean square.

Role: separates the support-independent pre-sifted comparison from finite interval large-sieve
bounds.
-/
theorem primitiveCharacterFamilyMeanSquare_preSifted_le_rationalMeanSquare (Z : ℕ) (S : Finset ℕ)
    (a : ℕ → ℂ) (hprime : ∀ n ∈ S, ∀ p, Nat.Prime p → p ∣ n → Z < p) :
    (∑ q ∈ (Finset.Ioc 1 Z).attach,
        Real.log ((Z : ℝ) / (q.val : ℝ)) *
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) S a) ≤
      2 * rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Z) S a := by
  classical
  let Q : Finset ℕ := Finset.Ioc 1 Z
  let R : ℕ → Finset ℕ := fun q =>
    (Finset.range (Z / q + 1)).filter (fun r => 0 < r ∧ Squarefree r ∧ Nat.Coprime r q)
  let P : Finset (ℕ × ℕ) := Q.biUnion fun q => (R q).image fun r => (q, r)
  let w : ℕ → ℕ → ℝ := fun q r =>
    if hq : 1 < q then
      if hr : 0 < r then
        (q : ℝ) / (Nat.totient (q * r) : ℝ) *
          primitiveCharacterPolynomialMeanSquare q hq S
            (fun n => a n * @ramanujanSum r n ⟨Nat.ne_of_gt hr⟩)
      else 0
    else 0
  have hPq : ∀ p, p ∈ P → 1 < p.1 := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨q, hqQ, hpq⟩
    rcases Finset.mem_image.mp hpq with ⟨r, hr, rfl⟩
    exact (Finset.mem_Ioc.mp hqQ).1
  have hPr : ∀ p, p ∈ P → 0 < p.2 := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨q, hqQ, hpq⟩
    rcases Finset.mem_image.mp hpq with ⟨r, hr, rfl⟩
    exact (Finset.mem_filter.mp hr).2.1
  have hPcop : ∀ p, p ∈ P → Nat.Coprime p.1 p.2 := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨q, hqQ, hpq⟩
    rcases Finset.mem_image.mp hpq with ⟨r, hr, rfl⟩
    exact (Finset.mem_filter.mp hr).2.2.2.symm
  have hPmax : ∀ p, p ∈ P → p.1 * p.2 ≤ Z := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨q, hqQ, hpq⟩
    rcases Finset.mem_image.mp hpq with ⟨r, hr, rfl⟩
    have hle : r ≤ Z / q := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
    calc
      q * r ≤ q * (Z / q) := Nat.mul_le_mul_left q hle
      _ ≤ Z := Nat.mul_div_le Z q
  have hdisj : Set.PairwiseDisjoint (↑Q : Set ℕ) (fun q => (R q).image fun r => (q, r)) := by
    intro q hq q' hq' hne
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    rcases Finset.mem_image.mp hp with ⟨r, hr, rfl⟩
    rcases Finset.mem_image.mp hp' with ⟨r', hr', heq⟩
    exact hne (Prod.mk.inj heq).1.symm
  have hsum :
    (∑ q ∈ Q.attach, ∑ r ∈ (R q.val).attach, w q.val r.val) =
      ∑ p ∈ P.attach, w p.val.1 p.val.2 := by
    calc
      _ = ∑ q ∈ Q.attach, ∑ r ∈ R q.val, w q.val r := by
        apply Finset.sum_congr rfl
        intro q hq
        exact Finset.sum_attach (R q.val) (fun r => w q.val r)
      _ = ∑ q ∈ Q, ∑ r ∈ R q, w q r := by exact Finset.sum_attach Q (fun q => ∑ r ∈ R q, w q r)
      _ = ∑ q ∈ Q, ∑ p ∈ (R q).image (fun r => (q, r)), w p.1 p.2 := by
        apply Finset.sum_congr rfl
        intro q hq
        symm
        rw [Finset.sum_image]
        intro r hr r' hr' heq
        exact (Prod.mk.inj heq).2
      _ = ∑ p ∈ P, w p.1 p.2 := (Finset.sum_biUnion hdisj).symm
      _ = _ := (Finset.sum_attach P (fun p => w p.1 p.2)).symm
  have hhalf :
    (∑ q ∈ Q.attach,
        Real.log ((Z : ℝ) / (q.val : ℝ)) / 2 *
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) S a) ≤
      ∑ p ∈ P.attach, w p.val.1 p.val.2 := by
    rw [← hsum]
    apply Finset.sum_le_sum
    intro q hq
    have hq1 : 1 < q.val := (Finset.mem_Ioc.mp q.property).1
    have hqpos : 0 < q.val := lt_trans Nat.zero_lt_one hq1
    have hqZ : q.val ≤ Z := (Finset.mem_Ioc.mp q.property).2
    have hlower :=
      primitiveCharacterPolynomialMeanSquare_preSifted_weighted_lower q.val Z hqpos hqZ hq1 S a
        hprime
    calc
      Real.log ((Z : ℝ) / (q.val : ℝ)) / 2 * primitiveCharacterPolynomialMeanSquare q.val hq1 S a ≤
          ∑ r ∈ (R q.val).attach, w q.val r.val :=
        by
        convert hlower using 1
        apply Finset.sum_congr rfl
        intro r hrR
        have hrpos : 0 < r.val := (Finset.mem_filter.mp r.property).2.1
        simp only [w, dite_eq_left hq1, dite_eq_left hrpos]
      _ = ∑ r ∈ (R q.val).attach, w q.val r.val := rfl
  have hupper :=
    primitive_ramanujan_weighted_pair_family_le_rationalMeanSquare P hPq hPr hPcop Z hPmax S a
  have hupper' :
    (∑ p ∈ P.attach, w p.val.1 p.val.2) ≤
      rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Z) S a := by
    apply le_trans ?_ hupper
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro p hp
    simp only [w, dite_eq_left (hPq p.val p.property), dite_eq_left (hPr p.val p.property)]
  have hhalfBound := hhalf.trans hupper'
  calc
    _ =
        ∑ q ∈ Q.attach,
          2 *
            (Real.log ((Z : ℝ) / (q.val : ℝ)) / 2 *
              primitiveCharacterPolynomialMeanSquare q.val
                (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) S a) :=
      by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ =
        2 *
          (∑ q ∈ Q.attach,
            Real.log ((Z : ℝ) / (q.val : ℝ)) / 2 *
              primitiveCharacterPolynomialMeanSquare q.val
                (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) S a) :=
      by rw [Finset.mul_sum]
    _ ≤ 2 * rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Z) S a :=
      mul_le_mul_of_nonneg_left hhalfBound (Nat.cast_nonneg 2)

/--
Inputs: a modulus cutoff `Z ≥ 2`, a coefficient set supported in `[0, N)`, and coefficients
whose supported indices have no prime factor at most `Z`.

Claim: the primitive-character mean squares for `1 < q ≤ Z`, weighted by `log (Z / q)`, are
bounded by `(4N + 6Z²)` times the coefficient energy.

Proof: sum the squarefree Ramanujan lower bound over moduli, reindex the resulting pair family,
and apply the factor-free additive large sieve once.

Role: provides the range-supported pre-sifted estimate used to construct its interval and hybrid
versions.
-/
theorem primitiveCharacterFamilyMeanSquare_preSifted_le_of_range (Z : ℕ) (hZ : 2 ≤ Z) (N : ℕ)
    (S : Finset ℕ) (hSN : S ⊆ Finset.range N) (a : ℕ → ℂ)
    (hprime : ∀ n ∈ S, ∀ p, Nat.Prime p → p ∣ n → Z < p) :
    (∑ q ∈ (Finset.Ioc 1 Z).attach,
        Real.log ((Z : ℝ) / (q.val : ℝ)) *
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) S a) ≤
      (4 * (N : ℝ) + 6 * (Z : ℝ) ^ 2) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  calc
    _ ≤ 2 * rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Z) S a :=
      primitiveCharacterFamilyMeanSquare_preSifted_le_rationalMeanSquare Z S a hprime
    _ ≤ 2 * ((2 * (N : ℝ) + 3 * ((Z * Z : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (reducedUnitFrequencyRationalSet_mean_square_le_window_row_of_range
          (lt_of_lt_of_le Nat.zero_lt_two hZ) N S hSN a)
        (Nat.cast_nonneg 2)
    _ = _ := by
      rw [Nat.cast_mul]
      ring

/--
Inputs: a modulus cutoff `Z ≥ 2`, a finite coefficient support in `[M, M + N)`, and coefficients
whose supported indices have no prime factor at most `Z`.

Claim: the weighted primitive-character mean squares for `1 < q ≤ Z` are bounded by
`(4N + 6Z²)` times the coefficient energy, independently of the interval's starting point.

Proof: apply the support-independent Ramanujan comparison, then the additive mean-square estimate
for interval support.

Role: supplies the short-interval pre-sifted estimate for the finite-support hybrid argument.
-/
theorem primitiveCharacterFamilyMeanSquare_preSifted_le_of_support_Ico (Z : ℕ) (hZ : 2 ≤ Z)
    (M N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Ico M (M + N)) (a : ℕ → ℂ)
    (hprime : ∀ n ∈ S, ∀ p, Nat.Prime p → p ∣ n → Z < p) :
    (∑ q ∈ (Finset.Ioc 1 Z).attach,
        Real.log ((Z : ℝ) / (q.val : ℝ)) *
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) S a) ≤
      (4 * (N : ℝ) + 6 * (Z : ℝ) ^ 2) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  calc
    _ ≤ 2 * rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Z) S a :=
      primitiveCharacterFamilyMeanSquare_preSifted_le_rationalMeanSquare Z S a hprime
    _ ≤ 2 * ((2 * (N : ℝ) + 3 * ((Z * Z : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (reducedUnitFrequencyRationalSet_mean_square_le_of_support_Ico
          (lt_of_lt_of_le Nat.zero_lt_two hZ) M N S hS a)
        (Nat.cast_nonneg 2)
    _ = _ := by
      rw [Nat.cast_mul]
      ring

/--
Inputs: the hypotheses of the range-supported pre-sifted estimate.

Claim: that estimate follows from the interval-supported theorem by taking `M = 0`.

Proof: rewrite `[0, N)` as `Finset.range N` and apply the interval-supported estimate.

Role: checks that the interval formulation specializes to the existing range formulation.
-/
theorem primitiveCharacterFamilyMeanSquare_preSifted_le_of_range_via_support_Ico (Z : ℕ)
    (hZ : 2 ≤ Z) (N : ℕ) (S : Finset ℕ) (hSN : S ⊆ Finset.range N) (a : ℕ → ℂ)
    (hprime : ∀ n ∈ S, ∀ p, Nat.Prime p → p ∣ n → Z < p) :
    (∑ q ∈ (Finset.Ioc 1 Z).attach,
        Real.log ((Z : ℝ) / (q.val : ℝ)) *
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) S a) ≤
      (4 * (N : ℝ) + 6 * (Z : ℝ) ^ 2) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  apply primitiveCharacterFamilyMeanSquare_preSifted_le_of_support_Ico Z hZ 0 N S ?_ a hprime
  intro n hn
  have hnN := Finset.mem_range.mp (hSN hn)
  simp only [Finset.mem_Ico, Nat.zero_add]
  exact ⟨Nat.zero_le n, hnN⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
