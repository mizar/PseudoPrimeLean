/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ConductorPrimeExclusionBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.BoundedPrimeExclusion
public import PseudoPrime.NumberTheory.DirichletCharacterSmallLevels
public import PseudoPrime.PseudoSquare.Bounds.ConductorSquareFactorJacobi

/-! # Quadratic witnesses with separate conductor and square-factor radical costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH, an odd nonsquare n has an odd coprime prime Jacobi-minus-one
witness bounded by the primitive conductor square and the prime logarithm sum
of 2n. Exclude two and all input prime factors before transferring the primitive
character value; its nontrivial unit value must be minus one. -/
theorem exists_prime_neg_one_le_conductor_prime_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          8 * (12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 200) ^ 2 +
            16 * (∑ r ∈ (2 * n).primeFactors, Real.log r) := by
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
    LLS.PaperStatements.exists_prime_ne_one_le_conductor_exclusion χ.primitiveCharacter hf
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

/-- For an odd nonsquare input with squarefree decomposition n=s^2*d,
GRH gives a negative odd-prime witness bounded by 8(12log(4d)+201)^2 plus
16 times the distinct prime logarithm sum of s. Enlarge the conductor to 4d,
split the excluded prime support, and absorb the d and two costs into the square.
This retains a linear radical cost for the square factor. -/
theorem exists_prime_neg_one_le_squarefree_square_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          8 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 201) ^ 2 +
            16 * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  obtain ⟨p, hp, ho, hcop, hj, hb⟩ :=
    exists_prime_neg_one_le_conductor_prime_budget (hn := hn) (hns := hns) hGRH
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
  have hcoef0 :
    0 ≤ 12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 200 := by
    linarith only [Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor]
  have hsq :=
    pow_le_pow_left₀ hcoef0
      (show
        12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 200 ≤
          12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 200
        by linarith only [hflog])
      2
  refine ⟨p, hp, ho, hcop, hj, hb.trans ?_⟩
  nlinarith only [hsq, he2, hen, hEd, hdlog, hG, Real.log_two_lt_d9]

/-- Under the squarefree decomposition and GRH, the least negative odd
prime witness obeys the conductor-square plus square-factor-radical bound.
Apply leastness to the actual coprime negative prime constructed above. -/
theorem primeNegOneWitness_le_squarefree_square_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      8 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 201) ^ 2 +
        16 * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_squarefree_square_budget bridge hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under the same decomposition and GRH, the least non-one odd-prime
witness also obeys the negative-witness bound. A value of minus one is non-one.
This transfer does not identify the two least witness definitions. -/
theorem primeNeOneWitness_le_squarefree_square_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      8 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 201) ^ 2 +
        16 * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_squarefree_square_budget bridge hGRH
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

/-- Under GRH, upper bounds on the squarefree logarithmic radius and the
square-factor prime logarithm budget produce a negative odd-prime witness at
most log(n)^(2-epsilon). Square the radius condition and add the radical cost.
This is a structured-input exponent improvement, not a uniform one. -/
theorem exists_prime_neg_one_le_log_power_of_squarefree_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {epsilon : ℝ}
    (hA :
      12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 201 ≤
        (Real.log n) ^ (1 - epsilon / 2) / 4)
    (hE :
      (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) ≤ (Real.log n) ^ (2 - epsilon) / 32) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 ∧ (p : ℝ) ≤ (Real.log n) ^ (2 - epsilon) := by
  obtain ⟨p, hp, ho, hc, hj, hb⟩ := exists_prime_neg_one_le_squarefree_square_budget bridge hGRH
  have hA0 : 0 ≤ 12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 201 := by
    linarith only [Real.log_natCast_nonneg (4 * bridge.squarefreePart)]
  have hs := pow_le_pow_left₀ hA0 hA 2
  have he : ((Real.log n) ^ (1 - epsilon / 2)) ^ (2 : ℕ) = (Real.log n) ^ (2 - epsilon) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (Real.log_natCast_nonneg n)]
    congr 1
    ring
  rw [div_pow, he] at hs
  norm_num only at hs
  refine ⟨p, hp, ho, hc, hj, hb.trans ?_⟩
  nlinarith only [hs, hE]

end PseudoPrime.PseudoSquare
