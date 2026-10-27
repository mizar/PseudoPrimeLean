/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RefinedConductorPrimeExclusionBounds
public import PseudoPrime.PseudoSquare.Bounds.ConductorRadicalWitnessBounds

/-! # Quadratic witnesses with refined conductor and radical costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH for an odd nonsquare n, an odd coprime negative Jacobi prime lies
below the root bound in the actual conductor and E(2n). Exclude two and input
prime factors before transferring primitive values. This retains the sharper
arbitrary-exclusion estimate for negative witnesses. -/
theorem exists_prime_neg_one_le_conductor_root_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          max 131072
            ((12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 113 +
                Real.sqrt
                  ((12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 113) ^
                      2 +
                    4 * (∑ r ∈ (2 * n).primeFactors, Real.log r))) ^
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
    LLS.PaperStatements.exists_prime_ne_one_le_root_conductor_exclusion χ.primitiveCharacter hf
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

/-- For n=s²d with its canonical odd nonsquare decomposition, GRH gives a
negative odd-prime witness bounded by max(131072,4(12log(4d)+114)²+8E(s)).
Bound the conductor by 4d and absorb the d and two exclusion terms into the square.
This halves the previous leading and radical coefficients. -/
theorem exists_prime_neg_one_le_refined_squarefree_square_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          max 131072
            (4 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114) ^ 2 +
              8 * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  obtain ⟨p, hp, ho, hcop, hj, hb⟩ :=
    exists_prime_neg_one_le_conductor_root_budget (hn := hn) (hns := hns) hGRH
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
    0 ≤ 12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 113 := by
    linarith only [Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor]
  have hsq :=
    pow_le_pow_left₀ hcoef0
      (show
        12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 113 ≤
          12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 113
        by linarith only [hflog])
      2
  have hb' :=
    hb.trans
      (LLS.PaperStatements.root_conductor_budget_le_linear
        (Finset.sum_nonneg (fun r _ ↦ Real.log_natCast_nonneg r)))
  refine ⟨p, hp, ho, hcop, hj, hb'.trans (max_le_max (le_refl _) ?_)⟩
  nlinarith only [hsq, he2, hen, hEd, hdlog, hG, Real.log_two_lt_d9]

/-- Under the canonical decomposition and GRH, the least negative odd-prime
witness satisfies the refined conductor-square and square-factor-radical bound.
Apply leastness to the coprime negative prime constructed above. -/
theorem primeNegOneWitness_le_refined_squarefree_square_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      max 131072
        (4 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114) ^ 2 +
          8 * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_refined_squarefree_square_budget bridge hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under the canonical decomposition and GRH, the least non-one odd-prime
witness also obeys the refined negative bound. Transfer the value minus one
to non-one and apply leastness, keeping the two witness definitions distinct. -/
theorem primeNeOneWitness_le_refined_squarefree_square_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      max 131072
        (4 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114) ^ 2 +
          8 * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_refined_squarefree_square_budget bridge hGRH
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

/-- Under GRH and the displayed squarefree radius and square-factor radical
conditions, an odd coprime negative prime lies below log(n)^(2-epsilon).
Square the radius, verify the common analytic cutoff and combine the costs.
The radical allowance is twice the previous structured-input allowance. -/
theorem exists_prime_neg_one_le_log_power_of_refined_squarefree_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {epsilon : ℝ}
    (hA :
      12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114 ≤
        (Real.log n) ^ (1 - epsilon / 2) / 4)
    (hE :
      (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) ≤ (Real.log n) ^ (2 - epsilon) / 16) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 ∧ (p : ℝ) ≤ (Real.log n) ^ (2 - epsilon) := by
  obtain ⟨p, hp, ho, hc, hj, hb⟩ :=
    exists_prime_neg_one_le_refined_squarefree_square_budget bridge hGRH
  have hA0 : 0 ≤ 12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114 := by
    linarith only [Real.log_natCast_nonneg (4 * bridge.squarefreePart)]
  have hs := pow_le_pow_left₀ hA0 hA 2
  have he : ((Real.log n) ^ (1 - epsilon / 2)) ^ (2 : ℕ) = (Real.log n) ^ (2 - epsilon) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (Real.log_natCast_nonneg n)]
    congr 1
    ring
  rw [div_pow, he] at hs
  norm_num only at hs
  have hA114 : 114 ≤ 12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114 := by
    linarith only [Real.log_natCast_nonneg (4 * bridge.squarefreePart)]
  have ht : (131072 : ℝ) ≤ (Real.log n) ^ (2 - epsilon) := by nlinarith only [hs, hA114]
  refine ⟨p, hp, ho, hc, hj, hb.trans (max_le ht ?_)⟩
  nlinarith only [hs, hE, ht]

/-- For nonnegative G and E, the refined squarefree budget is at most the
previous 8(12G+201)²+16E. Check both maximum branches by polynomial inequalities.
This certifies improvement for every admissible decomposition. -/
theorem refined_squarefree_budget_le_previous {G E : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E) :
    max (131072 : ℝ) (4 * (12 * G + 114) ^ 2 + 8 * E) ≤ 8 * (12 * G + 201) ^ 2 + 16 * E := by
  apply max_le
  · nlinarith only [hG, hE, sq_nonneg G]
  · nlinarith only [hG, hE, sq_nonneg G]

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Under GRH for an odd nonsquare n, its least negative odd-prime witness
obeys the root bound in the actual conductor and E(2n). Apply leastness to the
constructed coprime negative prime. This exposes the sharper formula for minimum consumers. -/
theorem primeNegOneWitness_le_conductor_root_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      max 131072
        ((12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 113 +
            Real.sqrt
              ((12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 113) ^ 2 +
                4 * (∑ r ∈ (2 * n).primeFactors, Real.log r))) ^
          2) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_conductor_root_budget (hn := hn) (hns := hns) hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- For the canonical decomposition n=s²d of an odd nonsquare input, the sum
of distinct prime logarithms of s is at most log(n)/2. Use s² dividing n and the
prime-factor logarithm bound. This removes factorization-dependent data from a coarse envelope. -/
theorem squareFactor_prime_log_sum_le_half_log {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) ≤ Real.log n / 2 := by
  have hs : bridge.squareFactor ≠ 0 := by
    intro hz
    have he := bridge.squarefreePart_sq_mul
    rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at he
    exact hn.pos.ne' he.symm
  have hdiv : bridge.squareFactor ^ 2 ∣ n :=
    ⟨bridge.squarefreePart, bridge.squarefreePart_sq_mul.symm⟩
  have hle := Nat.le_of_dvd hn.pos hdiv
  have hlog :=
    Real.log_le_log (pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)) 2)
      (show (bridge.squareFactor : ℝ) ^ 2 ≤ n by exact_mod_cast hle)
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hE := AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log hs
  linarith only [hE, hlog]

/-- Under GRH and the canonical decomposition, the least negative odd-prime
witness is at most max(131072,4(12log(4d)+114)²+4log(n)). Bound the square-factor
radical cost by half log(n). For fixed d this is an explicit logarithm-linear envelope. -/
theorem primeNegOneWitness_le_refined_squarefree_log_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      max 131072
        (4 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114) ^ 2 + 4 * Real.log n) := by
  apply (primeNegOneWitness_le_refined_squarefree_square_budget bridge hGRH hw).trans
  apply max_le_max (le_refl _)
  linarith only [squareFactor_prime_log_sum_le_half_log bridge]

/-- Under GRH and the canonical decomposition, an actual negative odd-prime
witness lies below the logarithm-linear envelope with its squarefree part retained.
Use unconditional nonemptiness and the least-witness theorem, with no new finite verification. -/
theorem exists_prime_neg_one_le_refined_squarefree_log_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          max 131072
            (4 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114) ^ 2 +
              4 * Real.log n) := by
  have hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hm := NumberTheory.primeNegOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNegOneWitness n hw, hm.1, hm.2.1, hm.2.2,
      primeNegOneWitness_le_refined_squarefree_log_budget bridge hGRH hw⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Under GRH for an odd nonsquare n, a coprime negative odd-prime witness lies
below the displayed conductor root radius without a constant branch. Exclude two
and input primes in the smaller-scale character theorem, then transfer values. -/
theorem exists_prime_neg_one_le_unclipped_conductor_root {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          ((12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 113 +
              Real.sqrt
                ((12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 113) ^ 2 +
                  4 * (∑ r ∈ (2 * n).primeFactors, Real.log r))) ^
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
    LLS.PaperStatements.exists_prime_ne_one_le_unclipped_conductor_root χ.primitiveCharacter hf
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

/-- For the canonical decomposition n=s²d under GRH, a coprime negative odd prime
lies below 4(12log(4d)+114)²+8E(s), with no maximum with an analytic floor.
Bound the root by its polynomial envelope and absorb two and d into the radius. -/
theorem exists_prime_neg_one_le_unclipped_squarefree_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          (4 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114) ^ 2 +
            8 * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  obtain ⟨p, hp, ho, hcop, hj, hb⟩ :=
    exists_prime_neg_one_le_unclipped_conductor_root (hn := hn) (hns := hns) hGRH
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
    0 ≤ 12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 113 := by
    linarith only [Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor]
  have hsq :=
    pow_le_pow_left₀ hcoef0
      (show
        12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 113 ≤
          12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 113
        by linarith only [hflog])
      2
  have hb' :=
    hb.trans
      (LLS.PaperStatements.conductor_root_le_polynomial
        (Finset.sum_nonneg (fun r _ ↦ Real.log_natCast_nonneg r)))
  refine ⟨p, hp, ho, hcop, hj, hb'.trans ?_⟩
  nlinarith only [hsq, he2, hen, hEd, hdlog, hG, Real.log_two_lt_d9]

/-- Under GRH and the canonical decomposition, the least negative odd-prime
witness satisfies the untruncated conductor-square and square-factor-radical bound.
Apply leastness to the coprime prime constructed above. -/
theorem primeNegOneWitness_le_unclipped_squarefree_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (4 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114) ^ 2 +
        8 * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_unclipped_squarefree_budget bridge hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under GRH and the canonical decomposition, the least non-one odd-prime
witness also obeys the untruncated negative bound. Transfer the minus-one value
to non-one and apply leastness. -/
theorem primeNeOneWitness_le_unclipped_squarefree_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (4 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114) ^ 2 +
        8 * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_unclipped_squarefree_budget bridge hGRH
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

/-- Under GRH and n=s²d, the least negative odd-prime witness is at most
4(12log(4d)+114)²+4log(n). Bound E(s) by log(n)/2.
For fixed d this gives a logarithm-linear envelope without a constant maximum branch. -/
theorem primeNegOneWitness_le_unclipped_squarefree_log_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (4 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114) ^ 2 + 4 * Real.log n) := by
  apply (primeNegOneWitness_le_unclipped_squarefree_budget bridge hGRH hw).trans
  linarith only [squareFactor_prime_log_sum_le_half_log bridge]

/-- Under GRH and the canonical decomposition, an actual negative odd-prime
witness satisfies the logarithm-linear bound without a constant branch.
Take the least witness and its membership proof. -/
theorem exists_prime_neg_one_le_unclipped_squarefree_log_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          (4 * (12 * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 114) ^ 2 +
            4 * Real.log n) := by
  have hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hm := NumberTheory.primeNegOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNegOneWitness n hw, hm.1, hm.2.1, hm.2.2,
      primeNegOneWitness_le_unclipped_squarefree_log_budget bridge hGRH hw⟩

/-- Under GRH for an odd nonsquare n, its least negative odd-prime witness is
bounded by the root expression in the actual conductor and E(2n), without a floor.
Apply leastness to the constructed coprime prime. -/
theorem primeNegOneWitness_le_unclipped_conductor_root {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      ((12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 113 +
          Real.sqrt
            ((12 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 113) ^ 2 +
              4 * (∑ r ∈ (2 * n).primeFactors, Real.log r))) ^
        2) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_unclipped_conductor_root (hn := hn) (hns := hns) hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

end PseudoPrime.PseudoSquare
