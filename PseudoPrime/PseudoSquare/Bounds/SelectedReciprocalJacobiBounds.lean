/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SelectedReciprocalConductorBounds
public import PseudoPrime.PseudoSquare.Bounds.AdaptiveReciprocalJacobiBounds
public import PseudoPrime.PseudoSquare.Bounds.VariableReciprocalJacobiBounds

/-! # Quadratic witness bounds using the selected reciprocal cutoff -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH for odd nonsquare n, G≥16 and log(actual conductor)≤G, an odd
coprime negative prime lies below the selected-envelope root with exclusion 2n.
Apply the primitive envelope theorem and transfer the non-one value to Jacobi -1. -/
theorem exists_prime_neg_one_le_selected_reciprocal_conductor_root {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ}
    (hG : 16 ≤ G) (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤ LLS.PaperStatements.selectedReciprocalWitnessBound G (2 * n) := by
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
    LLS.PaperStatements.exists_prime_ne_one_le_selected_envelope_root χ.primitiveCharacter hf
      χ.primitiveCharacter_isPrimitive hGRH
      (mul_ne_zero (by norm_num only : (2 : ℕ) ≠ 0) hn.pos.ne') hG hlog
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

/-- Under GRH and the stated conductor envelope, the least negative odd-prime
witness lies below the selected root. Apply leastness to the actual prime.
This connects the explicit analytic estimate to the least-witness interface. -/
theorem primeNegOneWitness_le_selected_reciprocal_conductor_root {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ}
    (hG : 16 ≤ G) (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      LLS.PaperStatements.selectedReciprocalWitnessBound G (2 * n) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_selected_reciprocal_conductor_root (hn := hn) (hns := hns) hGRH hG hlog
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under GRH and the stated conductor envelope, the least non-one odd-prime
witness lies below the selected root. A negative Jacobi value supplies non-one
membership, so the actual negative prime bounds this least witness. -/
theorem primeNeOneWitness_le_selected_reciprocal_conductor_root {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ}
    (hG : 16 ≤ G) (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      LLS.PaperStatements.selectedReciprocalWitnessBound G (2 * n) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_selected_reciprocal_conductor_root (hn := hn) (hns := hns) hGRH hG hlog
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

/-- Under GRH, canonical n=s²d and log(4d)≥16, an odd coprime negative prime is
at most 4(A(log(4d))+1)²+(28/5)E(s), using the selected radius A.
Bound the actual conductor first, then absorb squarefree-part exclusion costs.
Small actual conductors are covered by the primitive envelope theorem. -/
theorem exists_prime_neg_one_le_selected_reciprocal_squarefree_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hG : 16 ≤ Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          4 *
              (LLS.PaperStatements.selectedReciprocalRadius
                    (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) +
                  1) ^
                2 +
            (28 / 5 : ℝ) * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
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
  obtain ⟨p, hp, ho, hcop, hj, hb⟩ :=
    exists_prime_neg_one_le_selected_reciprocal_conductor_root (hn := hn) (hns := hns) hGRH hG hflog
  have he2 :=
    AnalyticNumberTheory.Arithmetic.prime_factor_log_sum_mul_le (by decide : 2 ≠ 0) hn.pos.ne'
  rw [Nat.prime_two.primeFactors, Finset.sum_singleton] at he2
  norm_num only [Nat.cast_ofNat] at he2
  have hen := AnalyticNumberTheory.Arithmetic.prime_factor_log_sum_mul_le (pow_ne_zero 2 hs) hd
  rw [bridge.squarefreePart_sq_mul, Nat.primeFactors_pow _ (by decide : 2 ≠ 0)] at hen
  have hEd := AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log hd
  have hG0 : 0 ≤ Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hd4 : bridge.squarefreePart ≤ 4 * bridge.squarefreePart :=
    Nat.le_mul_of_pos_left _ (by decide : 0 < 4)
  have hdlog := Real.log_le_log (Nat.cast_pos.mpr bridge.squarefreePart_pos) (Nat.cast_le.mpr hd4)
  have hA :=
    LLS.PaperStatements.selectedReciprocalRadius_lower_bound
      (show 1 ≤ Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) by linarith only [hG])
  have hb' :=
    hb.trans
      (LLS.PaperStatements.root_radius_sq_le_polynomial
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 14 / 5)
          (Finset.sum_nonneg (fun r _ ↦ Real.log_natCast_nonneg r))))
  refine ⟨p, hp, ho, hcop, hj, hb'.trans ?_⟩
  nlinarith only [hA, he2, hen, hEd, hdlog, hG0, Real.log_two_lt_d9]

/-- Under GRH, n=s²d and log(4d)≥16, the least negative odd-prime witness obeys
the selected squarefree-radius and square-factor cost bound. Apply leastness
to the actual prime. No input-integer finite certificate is used. -/
theorem primeNegOneWitness_le_selected_reciprocal_squarefree_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hG : 16 ≤ Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      4 *
          (LLS.PaperStatements.selectedReciprocalRadius
                (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) +
              1) ^
            2 +
        (28 / 5 : ℝ) * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_selected_reciprocal_squarefree_budget bridge hGRH hG
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under GRH, n=s²d and log(4d)≥16, the least non-one odd-prime witness obeys
the selected squarefree-radius and square-factor cost bound. Transfer the actual
negative prime to non-one membership and apply leastness. -/
theorem primeNeOneWitness_le_selected_reciprocal_squarefree_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hG : 16 ≤ Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      4 *
          (LLS.PaperStatements.selectedReciprocalRadius
                (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) +
              1) ^
            2 +
        (28 / 5 : ℝ) * (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_selected_reciprocal_squarefree_budget bridge hGRH hG
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

/-- Under GRH, n=s²d and log(4d)≥16, replace the square-factor cost by log(n)/2.
This gives a logarithm-linear envelope for fixed d using the improved selected
radius. Apply the proved bound and the square-factor prime-log estimate. -/
theorem primeNegOneWitness_le_selected_reciprocal_squarefree_log_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hG : 16 ≤ Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      4 *
          (LLS.PaperStatements.selectedReciprocalRadius
                (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) +
              1) ^
            2 +
        (14 / 5 : ℝ) * Real.log n := by
  apply (primeNegOneWitness_le_selected_reciprocal_squarefree_budget bridge hGRH hG hw).trans
  linarith only [squareFactor_prime_log_sum_le_half_log bridge]

/-- For G≥16 and any real exclusion cost E, the selected squarefree polynomial
bound is at most the previous adaptive polynomial with the same cost.
Compare nonnegative radii and square. This certifies improvement on the full explicit domain. -/
theorem selected_reciprocal_squarefree_budget_le_previous {G E : ℝ} (hG : 16 ≤ G) :
    4 * (LLS.PaperStatements.selectedReciprocalRadius G + 1) ^ 2 + (28 / 5 : ℝ) * E ≤
      4 * (LLS.PaperStatements.adaptiveReciprocalRadius G + 1) ^ 2 + (28 / 5 : ℝ) * E := by
  have h := LLS.PaperStatements.selectedReciprocalRadius_le_previous hG
  have h0 := LLS.PaperStatements.selectedReciprocalRadius_nonneg (show 1 ≤ G by linarith only [hG])
  have hs :=
    pow_le_pow_left₀
      (show 0 ≤ LLS.PaperStatements.selectedReciprocalRadius G + 1 by linarith only [h0])
      (show
        LLS.PaperStatements.selectedReciprocalRadius G + 1 ≤
          LLS.PaperStatements.adaptiveReciprocalRadius G + 1
        by linarith only [h])
      2
  linarith only [hs]

/-- Under GRH for odd nonsquare n, the least negative odd-prime witness is
bounded by the variable even root at max(8,log(conductor)/2)². Instantiate the
existing variable theorem, retaining its minimum with the fixed even Hadamard cap. -/
theorem primeNegOneWitness_le_selected_cutoff_root {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      LLS.PaperStatements.variableReciprocalWitnessBound
        (NumberTheory.complexQuadraticCharacter n hn).conductor (2 * n)
        (LLS.PaperStatements.halfConductorReciprocalCutoff
          (NumberTheory.complexQuadraticCharacter n hn).conductor)
        (179 / 200) (21 / 10) := by
  exact
    primeNegOneWitness_le_variable_reciprocal_conductor_root (hn := hn) (hns := hns) hGRH hw
      (LLS.PaperStatements.halfConductorReciprocalCutoff_ge_sixtyFour _)

/-- Under GRH for odd nonsquare n, the least non-one odd-prime witness is
bounded by the variable even root at the selected cutoff. Instantiate the existing
variable theorem, preserving the fixed even cap as a competing analytic bound. -/
theorem primeNeOneWitness_le_selected_cutoff_root {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      LLS.PaperStatements.variableReciprocalWitnessBound
        (NumberTheory.complexQuadraticCharacter n hn).conductor (2 * n)
        (LLS.PaperStatements.halfConductorReciprocalCutoff
          (NumberTheory.complexQuadraticCharacter n hn).conductor)
        (179 / 200) (21 / 10) := by
  exact
    primeNeOneWitness_le_variable_reciprocal_conductor_root (hn := hn) (hns := hns) hGRH hw
      (LLS.PaperStatements.halfConductorReciprocalCutoff_ge_sixtyFour _)

/-- For G≥57 and any real exclusion cost E, the selected squarefree polynomial
bound is at most the preceding direct even Hadamard polynomial. Use the certified
radius comparison and nonnegative square monotonicity. The threshold is sufficient. -/
theorem selected_reciprocal_squarefree_budget_le_even_fixed {G E : ℝ} (hG : 57 ≤ G) :
    4 * (LLS.PaperStatements.selectedReciprocalRadius G + 1) ^ 2 + (28 / 5 : ℝ) * E ≤
      4 * ((2429 / 720 : ℝ) * G + 18339 / 400) ^ 2 + (28 / 5 : ℝ) * E := by
  have h := LLS.PaperStatements.selectedReciprocalRadius_le_even_fixed hG
  have h0 := LLS.PaperStatements.selectedReciprocalRadius_nonneg (show 1 ≤ G by linarith only [hG])
  have hs :=
    pow_le_pow_left₀
      (show 0 ≤ LLS.PaperStatements.selectedReciprocalRadius G + 1 by linarith only [h0])
      (show LLS.PaperStatements.selectedReciprocalRadius G + 1 ≤ (2429 / 720 : ℝ) * G + 18339 / 400
        by linarith only [h])
      2
  linarith only [hs]

end PseudoPrime.PseudoSquare
