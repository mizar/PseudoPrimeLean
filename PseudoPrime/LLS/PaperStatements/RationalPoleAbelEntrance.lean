/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleAbelBudget

/-!
# Three certified entrances from the actual fourth-pole double Abel gap

The rational rows certify the unchanged character and ambient local costs together with
the improved principal error. Actual Jacobi witnesses and least witnesses are produced
at every larger common logarithmic scale. These entrances are finite-scale analytic
improvements; they do not assert practical-bit-width guarantees.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The coefficient 777 / 1000 row is certified at logarithmic entrance 1600000000.
The rational square-root and fourth-root comparisons, power-of-two cap and strict
budget margin are all checked exactly. This supplies an actual-witness entrance
through the generic half-line certificate, without an additional analytic premise. -/
noncomputable def fourPoleAbel777 : FourPoleAbelRow :=
  { coefficient := 777 / 1000
    sqrtLower := 88147 / 100000
    quarterUpper := 47 / 50
    rootEntrance := 40000
    logPower := 31
    coefficient_lower := by norm_num only
    coefficient_upper := by norm_num only
    sqrtLower_lower := by norm_num only
    quarterUpper_nonneg := by norm_num only
    sqrtLower_sq := by norm_num only
    quarterUpper_pow := by norm_num only
    rootEntrance_pos := by norm_num only
    scale_lower := by norm_num only
    logPower_upper := by norm_num only
    margin := by norm_num only }

/-- The coefficient 39 / 50 row is certified at logarithmic entrance 25000000.
The rational square-root and fourth-root comparisons, power-of-two cap and strict
budget margin are all checked exactly. This supplies an actual-witness entrance
through the generic half-line certificate, without an additional analytic premise. -/
noncomputable def fourPoleAbel78 : FourPoleAbelRow :=
  { coefficient := 39 / 50
    sqrtLower := 88317 / 100000
    quarterUpper := 47 / 50
    rootEntrance := 5000
    logPower := 25
    coefficient_lower := by norm_num only
    coefficient_upper := by norm_num only
    sqrtLower_lower := by norm_num only
    quarterUpper_nonneg := by norm_num only
    sqrtLower_sq := by norm_num only
    quarterUpper_pow := by norm_num only
    rootEntrance_pos := by norm_num only
    scale_lower := by norm_num only
    logPower_upper := by norm_num only
    margin := by norm_num only }

/-- The coefficient 79 / 100 row is certified at logarithmic entrance 4000000.
The rational square-root and fourth-root comparisons, power-of-two cap and strict
budget margin are all checked exactly. This supplies an actual-witness entrance
through the generic half-line certificate, without an additional analytic premise. -/
noncomputable def fourPoleAbel79 : FourPoleAbelRow :=
  { coefficient := 79 / 100
    sqrtLower := 88881 / 100000
    quarterUpper := 19 / 20
    rootEntrance := 2000
    logPower := 22
    coefficient_lower := by norm_num only
    coefficient_upper := by norm_num only
    sqrtLower_lower := by norm_num only
    quarterUpper_nonneg := by norm_num only
    sqrtLower_sq := by norm_num only
    quarterUpper_pow := by norm_num only
    rootEntrance_pos := by norm_num only
    scale_lower := by norm_num only
    logPower_upper := by norm_num only
    margin := by norm_num only }

/-- A common upper logarithmic scale bounds the original level 4*n by L+2.
Split the logarithm and bound log(4) by two.
This pays the ambient local cost in each actual common-scale witness theorem. -/
private theorem fourPole_abel_level_bound {n : ℕ} (hn : 0 < n) {L : ℝ} (hlog : Real.log n ≤ L) :
    Real.log (4 * n : ℕ) ≤ L + 2 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) hnR.ne',
    add_comm (Real.log (4 : ℝ))]
  apply add_le_add hlog
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num only, Real.log_pow]
  norm_num only
  linarith only [Real.log_two_lt_d9]

/-- The primitive quadratic conductor's logarithm is at most the common scale plus two.
Its conductor divides the original level 4*n, whose logarithm has the stated bound.
This pays the character-side cost internally while retaining the separate ambient level. -/
private theorem fourPole_abel_conductor_bound {n : ℕ} (hn : Odd n) {L : ℝ} (hlog : Real.log n ≤ L) :
    Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ L + 2 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hd := DirichletCharacter.conductor_dvd_level (NumberTheory.complexQuadraticCharacter n hn)
  have hcon := Nat.le_of_dvd (Nat.mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos) hd
  have hp : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero
  exact
    (Real.log_le_log (Nat.cast_pos.mpr hp) (Nat.cast_le.mpr hcon)).trans
      (fourPole_abel_level_bound hn.pos hlog)

/-- A certified row under GRH gives an actual negative Jacobi odd prime at every
common scale above its squared entrance and above the input logarithm.
Pay the conductor and ambient logarithms, then apply the closed scalar gap and
actual Jacobi criterion. No former finite entrance or unproved scalar hypothesis remains. -/
theorem fourPole_abel_jacobi_scale (f : FourPoleAbelRow) {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : f.rootEntrance ^ 2 ≤ L) (hlog : Real.log n ≤ L) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ f.coefficient * L ^ 2 ∧ jacobiSym n p = -1 := by
  have hLb := f.scale_lower.trans hL
  have hxl := (fourPole_abel_scale_bounds f hL).1
  apply
    fourPole_abel_jacobi_scalar bridge hGRH
      ((by norm_num only : (2 : ℝ) ≤ 1682).trans (hLb.trans hxl))
  exact
    fourPole_abel_scale_gap f hL (fourPole_abel_conductor_bound hn hlog)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using fourPole_abel_level_bound hn.pos hlog)

/-- Every certified common scale under GRH yields an actual negative-witness-set member.
Construct the canonical arithmetic bridge and use the actual odd-prime theorem.
This removes the external bridge from the finite entrance interface. -/
theorem fourPole_abel_scale_witness (f : FourPoleAbelRow) {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : f.rootEntrance ^ 2 ≤ L) (hlog : Real.log n ≤ L) :
    ∃ p : ℕ, p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ f.coefficient * L ^ 2 := by
  exact
    Nonempty.elim (NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns) fun bridge ↦
      Exists.elim (fourPole_abel_jacobi_scale f bridge hGRH hL hlog) fun p hp ↦
        ⟨p, ⟨hp.1, hp.2.1, hp.2.2.2⟩, hp.2.2.1⟩

/-- The actual least negative witness obeys any certified common-scale cutoff under GRH.
Minimize the constructed actual witness using the canonical least-witness definition.
This supplies the hypothesis used for cumulative endpoint lifting. -/
theorem fourPole_abel_scale_least (f : FourPoleAbelRow) {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : f.rootEntrance ^ 2 ≤ L) (hlog : Real.log n ≤ L)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ f.coefficient * L ^ 2 := by
  exact
    Exists.elim (fourPole_abel_scale_witness f hn hns hGRH hL hlog) fun _p hp ↦
      (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw hp.1)).trans hp.2

/-- A certified common scale under GRH yields a bounded least element of the actual
negative Jacobi witness set. Construct nonemptiness from the actual bounded witness
and minimize it. This exposes leastness without an external nonemptiness premise. -/
theorem fourPole_abel_scale_isLeast (f : FourPoleAbelRow) {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : f.rootEntrance ^ 2 ≤ L) (hlog : Real.log n ≤ L) :
    ∃ p : ℕ,
      IsLeast (NumberTheory.primeNegOneWitnessSet n) p ∧ (p : ℝ) ≤ f.coefficient * L ^ 2 := by
  exact
    Exists.elim (fourPole_abel_scale_witness f hn hns hGRH hL hlog) fun p hp ↦
      let hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty := ⟨p, hp.1⟩
      ⟨NumberTheory.primeNegOneWitness n hw,
        ⟨NumberTheory.primeNegOneWitness_mem n hw, fun _q hq ↦
          NumberTheory.primeNegOneWitness_le n hw hq⟩,
        (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw hp.1)).trans hp.2⟩

/-- Under GRH, logarithmic scale at least 1600000000 and above the input logarithm
produces an actual negative Jacobi prime below (777 / 1000)*L^2.
Instantiate the exact rational row and the closed common-scale witness theorem.
This makes the selected finite entrance explicit in the public witness contract. -/
theorem fourPoleAbel777_witness {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : (1600000000 : ℝ) ≤ L) (hlog : Real.log n ≤ L) :
    ∃ p : ℕ, p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ (777 / 1000 : ℝ) * L ^ 2 := by
  apply fourPole_abel_scale_witness fourPoleAbel777 hn hns hGRH ?_ hlog
  norm_num only [fourPoleAbel777]
  exact hL

/-- Under GRH, logarithmic scale at least 25000000 and above the input logarithm
produces an actual negative Jacobi prime below (39 / 50)*L^2.
Instantiate the exact rational row and the closed common-scale witness theorem.
This makes the selected finite entrance explicit in the public witness contract. -/
theorem fourPoleAbel78_witness {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : (25000000 : ℝ) ≤ L)
    (hlog : Real.log n ≤ L) :
    ∃ p : ℕ, p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ (39 / 50 : ℝ) * L ^ 2 := by
  apply fourPole_abel_scale_witness fourPoleAbel78 hn hns hGRH ?_ hlog
  norm_num only [fourPoleAbel78]
  exact hL

/-- Under GRH, logarithmic scale at least 4000000 and above the input logarithm
produces an actual negative Jacobi prime below (79 / 100)*L^2.
Instantiate the exact rational row and the closed common-scale witness theorem.
This makes the selected finite entrance explicit in the public witness contract. -/
theorem fourPoleAbel79_witness {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : (4000000 : ℝ) ≤ L)
    (hlog : Real.log n ≤ L) :
    ∃ p : ℕ, p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ (79 / 100 : ℝ) * L ^ 2 := by
  apply fourPole_abel_scale_witness fourPoleAbel79 hn hns hGRH ?_ hlog
  norm_num only [fourPoleAbel79]
  exact hL

end PseudoPrime.LLS.PaperStatements
