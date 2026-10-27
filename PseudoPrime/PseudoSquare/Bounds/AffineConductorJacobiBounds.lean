/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.AffineConductorWitnessBounds
public import PseudoPrime.PseudoSquare.Bounds.RefinedConductorRadicalWitnessBounds

/-! # Quadratic witnesses with smaller affine conductor and exclusion costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH for an odd nonsquare n, an odd coprime negative Jacobi prime lies
below the root bound in the actual conductor and E(2n), with improved affine constants.
Exclude two and input primes before transferring primitive values. -/
theorem exists_prime_neg_one_le_affine_conductor_root {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          (((21 / 4 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
              617 / 10 +
              Real.sqrt
                (((21 / 4 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
                      617 / 10) ^
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
    LLS.PaperStatements.exists_prime_ne_one_le_affine_conductor_root χ.primitiveCharacter hf
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

/-- For the canonical n=s²d under GRH, a coprime negative odd prime lies below
4((21/4)log(4d)+627/10)²+(28/5)E(s). Bound the root by its polynomial envelope
and absorb two and d into the radius. Both conductor and radical costs are improved. -/
theorem exists_prime_neg_one_le_affine_squarefree_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          (4 * ((21 / 4 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 627 / 10) ^ 2 +
            (28 / 5 : ℝ) * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  obtain ⟨p, hp, ho, hcop, hj, hb⟩ :=
    exists_prime_neg_one_le_affine_conductor_root (hn := hn) (hns := hns) hGRH
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
      (21 / 4 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        617 / 10 := by
    linarith only [Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor]
  have hsq :=
    pow_le_pow_left₀ hcoef0
      (show
        (21 / 4 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 617 / 10 ≤
          (21 / 4 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 617 / 10
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
witness obeys the improved affine conductor-square and radical bound.
Apply leastness to the constructed coprime negative prime. -/
theorem primeNegOneWitness_le_affine_squarefree_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (4 * ((21 / 4 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 627 / 10) ^ 2 +
        (28 / 5 : ℝ) * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_affine_squarefree_budget bridge hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under GRH and the canonical decomposition, the least non-one odd-prime
witness also obeys the improved negative bound. Transfer the value minus one to
non-one and apply leastness, retaining their distinct definitions. -/
theorem primeNeOneWitness_le_affine_squarefree_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (4 * ((21 / 4 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 627 / 10) ^ 2 +
        (28 / 5 : ℝ) * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_affine_squarefree_budget bridge hGRH
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

/-- Under GRH and n=s²d, the least negative odd-prime witness is at most
4((21/4)log(4d)+627/10)²+(14/5)log(n). Use E(s) ≤ log(n)/2.
For fixed d this gives a smaller explicit logarithm-linear envelope. -/
theorem primeNegOneWitness_le_affine_squarefree_log_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (4 * ((21 / 4 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 627 / 10) ^ 2 +
        (14 / 5 : ℝ) * Real.log n) := by
  apply (primeNegOneWitness_le_affine_squarefree_budget bridge hGRH hw).trans
  linarith only [squareFactor_prime_log_sum_le_half_log bridge]

/-- Under GRH and the canonical decomposition, an actual negative odd-prime
witness lies below the improved logarithm-linear envelope. Take the least witness
and its membership proof, without any new finite input verification. -/
theorem exists_prime_neg_one_le_affine_squarefree_log_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          (4 * ((21 / 4 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 627 / 10) ^ 2 +
            (14 / 5 : ℝ) * Real.log n) := by
  have hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hm := NumberTheory.primeNegOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNegOneWitness n hw, hm.1, hm.2.1, hm.2.2,
      primeNegOneWitness_le_affine_squarefree_log_budget bridge hGRH hw⟩

/-- Under GRH for an odd nonsquare n, its least negative odd-prime witness is
bounded by the improved root expression in the actual conductor and E(2n).
Apply leastness to the constructed coprime prime. -/
theorem primeNegOneWitness_le_affine_conductor_root {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (((21 / 4 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 617 / 10 +
          Real.sqrt
            (((21 / 4 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
                  617 / 10) ^
                2 +
              (14 / 5 : ℝ) * (∑ r ∈ (2 * n).primeFactors, Real.log r))) ^
        2) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_affine_conductor_root (hn := hn) (hns := hns) hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under GRH and the displayed squarefree radius and radical conditions, an
odd coprime negative prime lies below log(n)^(2-epsilon). Square the radius and
combine the improved coefficients. The allowed radical cost is log(n)^(2-epsilon)/8. -/
theorem exists_prime_neg_one_le_log_power_of_affine_squarefree_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {epsilon : ℝ}
    (hA :
      (21 / 4 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 627 / 10 ≤
        (Real.log n) ^ (1 - epsilon / 2) / 4)
    (hE : (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) ≤ (Real.log n) ^ (2 - epsilon) / 8) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 ∧ (p : ℝ) ≤ (Real.log n) ^ (2 - epsilon) := by
  obtain ⟨p, hp, ho, hc, hj, hb⟩ := exists_prime_neg_one_le_affine_squarefree_budget bridge hGRH
  have hA0 : 0 ≤ (21 / 4 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 627 / 10 := by
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

/-- Under GRH and the improved structural radius and radical conditions, the
least negative odd-prime witness is at most log(n)^(2-epsilon).
Apply leastness to the actual exponent-bounded prime. This completes the minimum interface. -/
theorem primeNegOneWitness_le_log_power_of_affine_squarefree_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) {epsilon : ℝ}
    (hA :
      (21 / 4 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 627 / 10 ≤
        (Real.log n) ^ (1 - epsilon / 2) / 4)
    (hE : (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) ≤ (Real.log n) ^ (2 - epsilon) / 8) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (Real.log n) ^ (2 - epsilon) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_log_power_of_affine_squarefree_budget bridge hGRH hA hE
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- For G,E ≥ 0, the improved squarefree conductor and radical budget is no
larger than 4(12G+114)²+8E. Compare nonnegative squared radii and the radical
coefficients. This verifies the structured bound improvement for every decomposition. -/
theorem affine_squarefree_budget_le_previous {G E : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E) :
    4 * ((21 / 4 : ℝ) * G + 627 / 10) ^ 2 + (28 / 5 : ℝ) * E ≤ 4 * (12 * G + 114) ^ 2 + 8 * E := by
  have h0 : 0 ≤ (21 / 4 : ℝ) * G + 627 / 10 := by linarith only [hG]
  have hle : (21 / 4 : ℝ) * G + 627 / 10 ≤ 12 * G + 114 := by linarith only [hG]
  nlinarith only [pow_le_pow_left₀ h0 hle 2, hE]

end PseudoPrime.PseudoSquare
