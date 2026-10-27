/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointConductorBounds
public import PseudoPrime.PseudoSquare.Bounds.RefinedConductorRadicalWitnessBounds

/-! # Quadratic witnesses from independent endpoint and zero-mass caps -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH for an odd nonsquare n, a coprime negative odd-prime witness
lies below the endpoint-refined root bound in the actual conductor and E(2n).
Exclude two and input primes, then transfer the primitive value. -/
theorem exists_prime_neg_one_le_endpoint_conductor_root {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          (((287 / 80 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
              4327 / 80 +
              Real.sqrt
                (((287 / 80 : ℝ) *
                        Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
                      4327 / 80) ^
                    2 +
                  (14 / 5 : ℝ) * (∑ r ∈ (2 * n).primeFactors, Real.log r))) ^
            2) := by
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
    LLS.PaperStatements.exists_prime_ne_one_le_endpoint_conductor_root χ.primitiveCharacter hf
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

/-- Under GRH and the canonical n=s²d decomposition, an odd coprime negative
prime lies below 4((287/80)log(4d)+4407/80)²+(28/5)E(s).
Bound the conductor and root radius and absorb the d and two exclusion costs. -/
theorem exists_prime_neg_one_le_endpoint_squarefree_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          (4 * ((287 / 80 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 4407 / 80) ^ 2 +
            (28 / 5 : ℝ) * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  obtain ⟨p, hp, ho, hcop, hj, hb⟩ :=
    exists_prime_neg_one_le_endpoint_conductor_root (hn := hn) (hns := hns) hGRH
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
    0 ≤
      (287 / 80 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        4327 / 80 := by
    linarith only [Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor]
  have hsq :=
    pow_le_pow_left₀ hcoef0
      (show
        (287 / 80 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
            4327 / 80 ≤
          (287 / 80 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 4327 / 80
        by linarith only [hflog])
      2
  have hb' :=
    hb.trans
      (LLS.PaperStatements.root_radius_sq_le_polynomial
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 14 / 5)
          (Finset.sum_nonneg (fun r _ ↦ Real.log_natCast_nonneg r))))
  refine ⟨p, hp, ho, hcop, hj, hb'.trans ?_⟩
  nlinarith only [hsq, he2, hen, hEd, hdlog, hG, Real.log_two_lt_d9]

/-- Under GRH and the canonical decomposition, the least negative odd-prime
witness obeys the endpoint-refined conductor-square and radical bound.
Apply leastness to the constructed coprime negative prime. -/
theorem primeNegOneWitness_le_endpoint_squarefree_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (4 * ((287 / 80 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 4407 / 80) ^ 2 +
        (28 / 5 : ℝ) * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_endpoint_squarefree_budget bridge hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under GRH and the canonical decomposition, the least non-one odd-prime
witness obeys the endpoint-refined negative bound. Transfer the minus-one value
to non-one and apply leastness. -/
theorem primeNeOneWitness_le_endpoint_squarefree_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (4 * ((287 / 80 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 4407 / 80) ^ 2 +
        (28 / 5 : ℝ) * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_endpoint_squarefree_budget bridge hGRH
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

/-- Under GRH and n=s²d, the least negative odd-prime witness is at most
4((287/80)log(4d)+4407/80)²+(14/5)log(n). Use E(s) ≤ log(n)/2.
This improves the explicit logarithm-linear envelope for fixed d. -/
theorem primeNegOneWitness_le_endpoint_squarefree_log_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (4 * ((287 / 80 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 4407 / 80) ^ 2 +
        (14 / 5 : ℝ) * Real.log n) := by
  apply (primeNegOneWitness_le_endpoint_squarefree_budget bridge hGRH hw).trans
  linarith only [squareFactor_prime_log_sum_le_half_log bridge]

/-- Under GRH and the canonical decomposition, an actual negative odd-prime
witness lies below the endpoint-refined logarithm-linear bound.
Take the least witness and its membership proof. -/
theorem exists_prime_neg_one_le_endpoint_squarefree_log_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          (4 * ((287 / 80 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 4407 / 80) ^ 2 +
            (14 / 5 : ℝ) * Real.log n) := by
  have hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hm := NumberTheory.primeNegOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNegOneWitness n hw, hm.1, hm.2.1, hm.2.2,
      primeNegOneWitness_le_endpoint_squarefree_log_budget bridge hGRH hw⟩

/-- Under GRH for an odd nonsquare n, the least negative odd-prime witness
obeys the endpoint-refined root bound in the actual conductor and E(2n).
Apply leastness to the constructed coprime prime. -/
theorem primeNegOneWitness_le_endpoint_conductor_root {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (((287 / 80 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
          4327 / 80 +
          Real.sqrt
            (((287 / 80 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
                  4327 / 80) ^
                2 +
              (14 / 5 : ℝ) * (∑ r ∈ (2 * n).primeFactors, Real.log r))) ^
        2) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_endpoint_conductor_root (hn := hn) (hns := hns) hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under GRH and the endpoint-refined radius and radical conditions, an odd
coprime negative prime lies below log(n)^(2-epsilon). Square the radius and
combine the budget with the nonnegative target power. This weakens the previous radius condition. -/
theorem exists_prime_neg_one_le_log_power_of_endpoint_squarefree_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {epsilon : ℝ}
    (hA :
      (287 / 80 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 4407 / 80 ≤
        (Real.log n) ^ (1 - epsilon / 2) / 4)
    (hE : (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) ≤ (Real.log n) ^ (2 - epsilon) / 8) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 ∧ (p : ℝ) ≤ (Real.log n) ^ (2 - epsilon) := by
  obtain ⟨p, hp, ho, hc, hj, hb⟩ := exists_prime_neg_one_le_endpoint_squarefree_budget bridge hGRH
  have hA0 : 0 ≤ (287 / 80 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 4407 / 80 := by
    linarith only [Real.log_natCast_nonneg (4 * bridge.squarefreePart)]
  have hs := pow_le_pow_left₀ hA0 hA 2
  have he : ((Real.log n) ^ (1 - epsilon / 2)) ^ (2 : ℕ) = (Real.log n) ^ (2 - epsilon) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (Real.log_natCast_nonneg n)]
    congr 1
    ring
  rw [div_pow, he] at hs
  norm_num only at hs
  refine ⟨p, hp, ho, hc, hj, hb.trans ?_⟩
  nlinarith only [hs, hE, Real.rpow_nonneg (Real.log_natCast_nonneg n) (2 - epsilon)]

/-- Under GRH and the endpoint-refined structural conditions, the least
negative odd-prime witness is at most log(n)^(2-epsilon).
Apply leastness to the actual exponent-bounded prime. -/
theorem primeNegOneWitness_le_log_power_of_endpoint_squarefree_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) {epsilon : ℝ}
    (hA :
      (287 / 80 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 4407 / 80 ≤
        (Real.log n) ^ (1 - epsilon / 2) / 4)
    (hE : (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) ≤ (Real.log n) ^ (2 - epsilon) / 8) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (Real.log n) ^ (2 - epsilon) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_log_power_of_endpoint_squarefree_budget bridge hGRH hA hE
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- For G ≥ 0 and real E, the endpoint-refined squarefree budget is no larger
than the preceding affine budget. Compare nonnegative squared radii while
retaining the same radical coefficient. This proves improvement on the complete domain. -/
theorem endpoint_squarefree_budget_le_previous {G E : ℝ} (hG : 0 ≤ G) :
    4 * ((287 / 80 : ℝ) * G + 4407 / 80) ^ 2 + (28 / 5 : ℝ) * E ≤
      4 * ((21 / 4 : ℝ) * G + 627 / 10) ^ 2 + (28 / 5 : ℝ) * E := by
  have h0 : 0 ≤ (287 / 80 : ℝ) * G + 4407 / 80 := by linarith only [hG]
  have hle : (287 / 80 : ℝ) * G + 4407 / 80 ≤ (21 / 4 : ℝ) * G + 627 / 10 := by linarith only [hG]
  linarith only [pow_le_pow_left₀ h0 hle 2]

end PseudoPrime.PseudoSquare
