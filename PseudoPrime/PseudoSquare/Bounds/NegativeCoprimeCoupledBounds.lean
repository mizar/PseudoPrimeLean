/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.EvenCoprimeCoupledComparison
public import PseudoPrime.NumberTheory.PrimitiveJacobiCharacter
public import PseudoPrime.PseudoSquare.Bounds.WitnessMaximum

/-! # Negative Jacobi witnesses from the coupled signed support comparison -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The explicit coupled coprime envelope for the level-4n quadratic
character, at arbitrary root y and reciprocal main error -179/200.
It retains both finite common-factor sums and signed conductor-quotient
corrections. A strict gap against the unsigned logarithmic sum yields
a negative Jacobi witness, rather than allowing a zero character value. -/
noncomputable def negativeCoprimeEnvelope (n : ℕ) (hn : Odd n) (y : ℝ) : ℝ :=
  LLS.Extensions.evenCoprimeUpper (NumberTheory.complexQuadraticCharacter n hn) y (-(179 / 200))

/-- For a positive odd nonsquare n under GRH, a root at least eight and
the displayed explicit coupled-envelope gap give an odd prime negative
Jacobi witness through y squared. Apply the coprime character-witness theorem
and use quadraticity to turn its non-one value into -1.
The quantitative gap remains an explicit hypothesis. -/
theorem exists_prime_neg_one_witness_of_coupledCoprimeGap {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hgap :
      negativeCoprimeEnvelope n hn y <
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ y ^ 2 ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨NumberTheory.complexQuadraticCharacter_conductor_ne_zero n hn⟩
  obtain ⟨p, hp, hd, hv, hb⟩ :=
    LLS.Extensions.exists_prime_coprime_ne_one_of_retainedEvenCoprimeGap
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns)
      (NumberTheory.primitiveQuadraticCharacter_isEven n hn) hGRH hy hgap
  have hm := NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd hv
  exact ⟨p, hm.1, hm.2.1, hb, hm.2.2⟩

/-- Under the same odd-nonsquare, GRH, root and explicit-gap assumptions,
the least odd-prime negative Jacobi witness is at most y squared.
Compare it with the actual witness from the coupled coprime comparison.
This supplies the common-endpoint input for finite maxima. -/
theorem primeNegOneWitness_cast_le_of_coupledCoprimeGap {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hgap :
      negativeCoprimeEnvelope n hn y <
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2))
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ y ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_neg_one_witness_of_coupledCoprimeGap hn hns hGRH hy hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH at root y at least eight, if the explicit coupled gap holds
for every admissible n through B, then QNegOne B is at most y squared.
Lift the common-endpoint least-witness bound through the full admissible set.
The gap premise covers small inputs as well; no finite check is inferred. -/
theorem QNegOne_le_of_coupledCoprimeGap {B : ℕ} {y : ℝ} (hy : 8 ≤ y)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hgap :
      ∀ n : ℕ,
        (hn : Odd n) →
          ¬IsSquare n →
            n ≤ B →
            negativeCoprimeEnvelope n hn y <
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2)) :
    (QNegOne B : ℝ) ≤ y ^ 2 := by
  apply QNegOne_cast_le_of_forall (sq_nonneg y)
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_of_coupledCoprimeGap ha.odd ha.not_isSquare hGRH hy
      (hgap n ha.odd ha.not_isSquare ha.le)
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- For a positive odd nonsquare n under GRH, log n at least 8001/1000 and
the explicit gap at root log n-1/1000 yield a negative Jacobi witness at most
the shifted square and strictly below log(n) squared.
Combine the root-independent witness theorem with the scalar comparison.
The gap is not asserted on an entire input half-line. -/
theorem exists_prime_neg_one_witness_le_shift_of_coupledCoprimeGap {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8001 / 1000 : ℝ) ≤ Real.log n)
    (hgap :
      negativeCoprimeEnvelope n hn (Real.log n - 1 / 1000) <
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum ((Real.log n - 1 / 1000) ^ 2)) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (Real.log n - 1 / 1000) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p = -1 := by
  have hy : (8 : ℝ) ≤ Real.log n - 1 / 1000 := by linarith only [hL]
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_neg_one_witness_of_coupledCoprimeGap hn hns hGRH hy hgap
  have hs : (Real.log n - 1 / 1000) ^ 2 < (Real.log n) ^ 2 := by nlinarith only [hL]
  exact ⟨p, hp, ho, hb, hb.trans_lt hs, hv⟩

end PseudoPrime.PseudoSquare
