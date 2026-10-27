/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.AdaptiveReciprocalConductorBounds
public import PseudoPrime.PseudoSquare.Bounds.DirectHadamardJacobiBounds

/-! # Quadratic witnesses with an explicit adaptive reciprocal cutoff -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH for an odd nonsquare n, an odd coprime negative prime lies below
the explicit adaptive root in the actual quadratic conductor and the cost of 2n.
Exclude input primes and two, then transfer the primitive non-one value to Jacobi -1. -/
theorem exists_prime_neg_one_le_adaptive_reciprocal_conductor_root {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          LLS.PaperStatements.adaptiveReciprocalWitnessBound
            (NumberTheory.complexQuadraticCharacter n hn).conductor (2 * n) := by
  let χ := NumberTheory.complexQuadraticCharacter n hn
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ : χ ≠ 1 := by
    intro he
    have hc := DirichletCharacter.eq_one_iff_conductor_eq_one.mp he
    have hh : NumberTheory.primitiveQuadraticCharacter n hn = 1 :=
      DirichletCharacter.level_one' _ hc
    exact NumberTheory.primitiveQuadraticCharacter_ne_one_of_not_square n hn hns hh
  have hf := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    LLS.PaperStatements.exists_prime_ne_one_le_adaptive_reciprocal_root χ.primitiveCharacter hf
      χ.primitiveCharacter_isPrimitive hGRH
      (mul_ne_zero (by norm_num only : (2 : ℕ) ≠ 0) hn.pos.ne')
  have hpn : ¬p ∣ n := fun h ↦ hd (h.trans (dvd_mul_left n 2))
  have hp2 : p ≠ 2 := by
    intro he
    apply hd
    rw [he]
    exact dvd_mul_right 2 n
  have ho := hp.odd_of_ne_two hp2
  have hcop := hp.coprime_iff_not_dvd.mpr hpn
  have he := NumberTheory.primitiveQuadraticCharacter_apply_odd_prime hn hp ho hpn
  simp only [Int.cast_natCast] at he
  have hne : jacobiSym n p ≠ 1 := by
    intro h
    apply hv
    change NumberTheory.primitiveQuadraticCharacter n hn p = 1
    rw [he, h, Int.cast_one]
  have hj :=
    jacobiSym.eq_one_or_neg_one
      (show (n : ℤ).gcd p = 1 by
        rw [Int.gcd_natCast_natCast]
        exact hcop.symm.gcd_eq_one)
  exact ⟨p, hp, ho, hcop, hj.resolve_left hne, hb⟩

/-- Under GRH for odd nonsquare n, bound the least negative odd-prime witness
by the explicit adaptive conductor root. Apply leastness to the actual prime.
This exposes the analytic bound at the least-witness interface. -/
theorem primeNegOneWitness_le_adaptive_reciprocal_conductor_root {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      LLS.PaperStatements.adaptiveReciprocalWitnessBound
        (NumberTheory.complexQuadraticCharacter n hn).conductor (2 * n) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_adaptive_reciprocal_conductor_root (hn := hn) (hns := hns) hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under GRH for odd nonsquare n, bound the least non-one odd-prime witness
by the explicit adaptive conductor root. A negative Jacobi value is non-one,
so the actual negative prime also supplies this least-witness bound. -/
theorem primeNeOneWitness_le_adaptive_reciprocal_conductor_root {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      LLS.PaperStatements.adaptiveReciprocalWitnessBound
        (NumberTheory.complexQuadraticCharacter n hn).conductor (2 * n) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_adaptive_reciprocal_conductor_root (hn := hn) (hns := hns) hGRH
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

/-- Under GRH and the canonical n=s²d decomposition, an odd coprime negative
prime is at most 4(A(log(4d))+1)²+(28/5)E(s), with adaptive radius A.
Compare conductors, bound the positive root polynomially, and absorb the d and two costs. -/
theorem exists_prime_neg_one_le_adaptive_reciprocal_squarefree_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          4 *
              (LLS.PaperStatements.adaptiveReciprocalRadius
                    (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) +
                  1) ^
                2 +
            (28 / 5 : ℝ) * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  obtain ⟨p, hp, ho, hcop, hj, hb⟩ :=
    exists_prime_neg_one_le_adaptive_reciprocal_conductor_root (hn := hn) (hns := hns) hGRH
  have hd := bridge.squarefreePart_pos.ne'
  have hs : bridge.squareFactor ≠ 0 := by
    intro hz
    have he := bridge.squarefreePart_sq_mul
    rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at he
    exact hn.pos.ne' he.symm
  have hdiv : bridge.squarefreePart ∣ n :=
    ⟨bridge.squareFactor ^ 2, by simpa only [mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  have hf :
    (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ 4 * bridge.squarefreePart := by
    rw [NumberTheory.complexQuadraticCharacter_conductor_eq_discriminant bridge hdiv]
    exact bridge.discriminant_le_four_mul_squarefreePart
  have hflog :=
    Real.log_le_log
      (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero))
      (Nat.cast_le.mpr hf)
  have he2 :=
    AnalyticNumberTheory.Arithmetic.prime_factor_log_sum_mul_le (by decide : 2 ≠ 0) hn.pos.ne'
  rw [Nat.prime_two.primeFactors, Finset.sum_singleton] at he2
  norm_num only [Nat.cast_ofNat] at he2
  have hen := AnalyticNumberTheory.Arithmetic.prime_factor_log_sum_mul_le (pow_ne_zero 2 hs) hd
  rw [bridge.squarefreePart_sq_mul, Nat.primeFactors_pow _ (by decide : 2 ≠ 0)] at hen
  have hEd := AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log hd
  have hG : 0 ≤ Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hd4 : bridge.squarefreePart ≤ 4 * bridge.squarefreePart :=
    Nat.le_mul_of_pos_left _ (by decide : 0 < 4)
  have hdlog := Real.log_le_log (Nat.cast_pos.mpr bridge.squarefreePart_pos) (Nat.cast_le.mpr hd4)
  have hcoef0 :=
    LLS.PaperStatements.adaptiveReciprocalRadius_nonneg
      (Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor)
  have hsq :=
    pow_le_pow_left₀ hcoef0
      (LLS.PaperStatements.adaptiveReciprocalRadius_mono
        (Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor) hflog)
      2
  have hA := LLS.PaperStatements.adaptiveReciprocalRadius_lower_bound hG
  have hb' :=
    hb.trans
      (LLS.PaperStatements.root_radius_sq_le_polynomial
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 14 / 5)
          (Finset.sum_nonneg (fun r _ ↦ Real.log_natCast_nonneg r))))
  refine ⟨p, hp, ho, hcop, hj, hb'.trans ?_⟩
  nlinarith only [hsq, hA, he2, hen, hEd, hdlog, hG, Real.log_two_lt_d9]

/-- Under GRH and n=s²d, bound the least negative odd-prime witness by the
adaptive squarefree radius and square-factor prime cost. Apply leastness to
the actual prime theorem. This improves the large-squarefree-part structural bound. -/
theorem primeNegOneWitness_le_adaptive_reciprocal_squarefree_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      4 *
          (LLS.PaperStatements.adaptiveReciprocalRadius
                (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) +
              1) ^
            2 +
        (28 / 5 : ℝ) * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_adaptive_reciprocal_squarefree_budget bridge hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under GRH and n=s²d, bound the least non-one odd-prime witness by the
adaptive squarefree radius and square-factor prime cost. Transfer the actual
negative prime to non-one membership, then use leastness. -/
theorem primeNeOneWitness_le_adaptive_reciprocal_squarefree_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      4 *
          (LLS.PaperStatements.adaptiveReciprocalRadius
                (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) +
              1) ^
            2 +
        (28 / 5 : ℝ) * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_adaptive_reciprocal_squarefree_budget bridge hGRH
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

/-- Under GRH and n=s²d, replace the square-factor prime cost in the least
negative witness bound by log(n)/2. This gives a logarithm-linear envelope
for fixed d, using the already proved square-factor cost estimate. -/
theorem primeNegOneWitness_le_adaptive_reciprocal_squarefree_log_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      4 *
          (LLS.PaperStatements.adaptiveReciprocalRadius
                (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) +
              1) ^
            2 +
        (14 / 5 : ℝ) * Real.log n := by
  apply (primeNegOneWitness_le_adaptive_reciprocal_squarefree_budget bridge hGRH hw).trans
  linarith only [squareFactor_prime_log_sum_le_half_log bridge]

/-- For G ≥ 100 and any real prime cost E, the adaptive squarefree polynomial
bound is at most the preceding direct even Hadamard polynomial bound.
Compare the positive radii, add the common unit saving and square. -/
theorem adaptive_reciprocal_squarefree_budget_le_previous {G E : ℝ} (hG : 100 ≤ G) :
    4 * (LLS.PaperStatements.adaptiveReciprocalRadius G + 1) ^ 2 + (28 / 5 : ℝ) * E ≤
      4 * ((2429 / 720 : ℝ) * G + 18339 / 400) ^ 2 + (28 / 5 : ℝ) * E := by
  have h := LLS.PaperStatements.adaptiveReciprocalRadius_le_even_fixed_of_ge_hundred hG
  have h0 := LLS.PaperStatements.adaptiveReciprocalRadius_nonneg (show 0 ≤ G by linarith only [hG])
  have hs :=
    pow_le_pow_left₀
      (show 0 ≤ LLS.PaperStatements.adaptiveReciprocalRadius G + 1 by linarith only [h0])
      (show LLS.PaperStatements.adaptiveReciprocalRadius G + 1 ≤ (2429 / 720 : ℝ) * G + 18339 / 400
        by linarith only [h])
      2
  linarith only [hs]

end PseudoPrime.PseudoSquare
