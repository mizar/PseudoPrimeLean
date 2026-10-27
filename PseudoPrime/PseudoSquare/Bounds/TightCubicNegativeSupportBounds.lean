/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TightCubicConductorBounds
public import PseudoPrime.PseudoSquare.Bounds.CubicNegativeSupportBounds

/-! # Negative Jacobi witnesses with tight cubic conductor radii -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Conductor and sensitive-cost envelopes under GRH give an odd coprime
negative Jacobi witness at the tight cubic radius. Transfer the primitive
quadratic character value and exclude two through the excluded integer 2n. -/
theorem exists_prime_neg_one_le_tight_cubic_sensitive_radius {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G E : ℝ}
    (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G)
    (hcost :
      AnalyticNumberTheory.Arithmetic.characterExclusionCost
          (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) ≤
        E) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧ (p : ℝ) ≤ (LLS.PaperStatements.tightCubicExclusionRadius G E) ^ 2 := by
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
  have hprim := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    LLS.PaperStatements.exists_prime_outside_le_tight_cubic_exclusion_radius χ.primitiveCharacter
      (le_trans (by decide : 2 ≤ 3) hf) (mul_ne_zero (by norm_num only : (2 : ℕ) ≠ 0) hn.pos.ne')
      hGRH χ.primitiveCharacter_isPrimitive hprim hlog hcost
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

/-- If the cost at 2n is at most G+2E, the tight square-factor radius bounds
an odd coprime negative prime. Apply sensitive extraction and the proved
ramification absorption, with nonnegative conductor and square-factor envelopes. -/
theorem exists_prime_neg_one_le_tight_cubic_square_factor_of_envelopes {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G E : ℝ}
    (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G) (hE : 0 ≤ E)
    (hcost :
      AnalyticNumberTheory.Arithmetic.characterExclusionCost
          (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) ≤
        G + 2 * E) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤ (LLS.PaperStatements.tightCubicSquareFactorRadius G E) ^ 2 := by
  have hG :=
    (Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor).trans hlog
  obtain ⟨p, hp, ho, hc, hj, hb⟩ :=
    exists_prime_neg_one_le_tight_cubic_sensitive_radius (hns := hns) hGRH hlog hcost
  have hr := LLS.PaperStatements.tightCubicExclusionRadius_le_square_factor hG hE
  have hcost0 : 0 ≤ G + 2 * E := by linarith only [hG, hE]
  have hn := (LLS.PaperStatements.tightCubicExclusionRadius_data hG hcost0).1
  have hs := pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 63 / 2).trans hn) hr 2
  exact ⟨p, hp, ho, hc, hj, hb.trans hs⟩

/-- For the canonical decomposition n=d*s², GRH supplies an odd negative
prime below the tight square-factor radius. Its only square-factor cost is
the logarithm sum over primes where (d/p)=-1. Conductor and cost estimates
are discharged from the existing arithmetic decomposition. -/
theorem exists_prime_neg_one_le_tight_cubic_negative_support {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          (LLS.PaperStatements.tightCubicSquareFactorRadius
              (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
              (negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
            2 := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hdvd : bridge.squarefreePart ∣ n :=
    ⟨bridge.squareFactor ^ 2, by simpa only [mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  have hf :=
    Nat.le_of_dvd (Nat.mul_pos (by decide : 0 < 4) bridge.squarefreePart_pos)
      (NumberTheory.complexQuadraticCharacter_conductor_dvd_four_mul_squarefreePart bridge hdvd)
  have hlog :=
    Real.log_le_log
      (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero))
      (Nat.cast_le.mpr hf)
  exact
    exists_prime_neg_one_le_tight_cubic_square_factor_of_envelopes (hns := hns) hGRH hlog
      (negativeSquareFactorCost_nonneg _ _)
      (primitiveQuadraticExclusionCost_le_negative_square_factor bridge)

/-- Under GRH, leastness transfers the negative-support cubic radius to the
least negative odd-prime witness of n=s²d. The support cost is the explicit
Jacobi filter on the square factor, with no remaining analytic cost hypothesis. -/
theorem primeNegOneWitness_le_tight_cubic_negative_support {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (LLS.PaperStatements.tightCubicSquareFactorRadius
          (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
          (negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
        2 := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_tight_cubic_negative_support bridge hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- The same negative-support radius bounds the least non-one odd-prime
witness under GRH. Use the constructed negative value as a non-one value;
this does not identify the two least witnesses. -/
theorem primeNeOneWitness_le_tight_cubic_negative_support {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (LLS.PaperStatements.tightCubicSquareFactorRadius
          (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
          (negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
        2 := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_tight_cubic_negative_support bridge hGRH
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

end PseudoPrime.PseudoSquare
