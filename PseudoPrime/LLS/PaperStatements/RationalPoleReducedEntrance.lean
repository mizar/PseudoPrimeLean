/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleScaleBudget

/-! # Three certified reduced fourth-pole entrances

The numerical rows certify the existing selected-kernel scalar inequality. Keeping them
outside the stable scalar-budget module confines later coefficient and entrance changes
to this application layer. Arithmetic bridges and GRH are supplied before exposing actual
Jacobi witnesses; no new input enumeration or primitive-conductor assumption is introduced.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A finite scalar certificate for the selected fourth-pole kernel.
The coefficient determines the squared-scale cutoff; the two root bounds control its
square root and fourth root, and the root entrance determines the minimum common scale.
The proof fields require the coefficient range, nonnegative roots, the root comparisons,
the lower entrance and a strict principal margin. These invariants supply a closed
actual-witness theorem and its cumulative consumers for each of the three numerical rows. -/
structure FourPoleEntry where
  /-- The coefficient of the squared logarithmic cutoff. -/
  coefficient : ℝ
  /-- A rational lower bound for its square root. -/
  sqrtLower : ℝ
  /-- A rational upper bound for its fourth root. -/
  quarterUpper : ℝ
  /-- The square root of the minimum common logarithmic scale. -/
  rootEntrance : ℝ
  /-- The coefficient is within the existing kernel's certified range. -/
  coefficient_lower : (777 / 1000 : ℝ) ≤ coefficient
  /-- The cutoff does not exceed the squared common scale. -/
  coefficient_upper : coefficient ≤ 1
  /-- The square-root comparison uses a nonnegative lower root. -/
  sqrtLower_nonneg : 0 ≤ sqrtLower
  /-- The fourth-root comparison uses a nonnegative upper root. -/
  quarterUpper_nonneg : 0 ≤ quarterUpper
  /-- The lower root squares below the coefficient. -/
  sqrtLower_sq : sqrtLower ^ 2 ≤ coefficient
  /-- The upper root's fourth power covers the coefficient. -/
  quarterUpper_pow : coefficient ≤ quarterUpper ^ 4
  /-- The entrance lies in the stable scalar budget's domain. -/
  rootEntrance_lower : 10000 ≤ rootEntrance
  /-- The entrance leaves a strict margin above the complete square-root error. -/
  margin : 65 * quarterUpper + 1 < ((28379 / 100000 : ℝ) * sqrtLower - 2501 / 10000) * rootEntrance

/-- The coefficient-777/1000 row has common logarithmic entrance 1440000000000.
Input: none. Output: the four rational parameters with all scalar guards certified.
Proof: exact rational arithmetic. Role: retain the best coefficient at a reduced entrance. -/
noncomputable def fourPole777Entrance : FourPoleEntry :=
  { coefficient := 777 / 1000
    sqrtLower := 88147 / 100000
    quarterUpper := 47 / 50
    rootEntrance := 1200000
    coefficient_lower := by norm_num only
    coefficient_upper := by norm_num only
    sqrtLower_nonneg := by norm_num only
    quarterUpper_nonneg := by norm_num only
    sqrtLower_sq := by norm_num only
    quarterUpper_pow := by norm_num only
    rootEntrance_lower := by norm_num only
    margin := by norm_num only }

/-- The coefficient-39/50 row has common logarithmic entrance 14400000000.
Input: none. Output: the four rational parameters and their scalar certificate.
Proof: exact rational arithmetic. Role: improve the transition before the 777/1000 row. -/
noncomputable def fourPole78Entrance : FourPoleEntry :=
  { coefficient := 39 / 50
    sqrtLower := 88317 / 100000
    quarterUpper := 47 / 50
    rootEntrance := 120000
    coefficient_lower := by norm_num only
    coefficient_upper := by norm_num only
    sqrtLower_nonneg := by norm_num only
    quarterUpper_nonneg := by norm_num only
    sqrtLower_sq := by norm_num only
    quarterUpper_pow := by norm_num only
    rootEntrance_lower := by norm_num only
    margin := by norm_num only }

/-- The coefficient-79/100 row has common logarithmic entrance 900000000.
Input: none. Output: the four rational parameters and their scalar certificate.
Proof: exact rational arithmetic. Role: expose the earliest of the three reduced entrances. -/
noncomputable def fourPole79Entrance : FourPoleEntry :=
  { coefficient := 79 / 100
    sqrtLower := 88881 / 100000
    quarterUpper := 19 / 20
    rootEntrance := 30000
    coefficient_lower := by norm_num only
    coefficient_upper := by norm_num only
    sqrtLower_nonneg := by norm_num only
    quarterUpper_nonneg := by norm_num only
    sqrtLower_sq := by norm_num only
    quarterUpper_pow := by norm_num only
    rootEntrance_lower := by norm_num only
    margin := by norm_num only }

/-- Every certified entrance scale lies in the stable scalar budget's domain.
Input: certified entrance data. Claim: its squared entrance is at least one hundred million.
Proof: square the nonnegative root-entrance lower bound.
Role: supply the common scalar domain before applying the selected numerical row. -/
theorem fourPole_data_scale_lower (f : FourPoleEntry) : (100000000 : ℝ) ≤ f.rootEntrance ^ 2 := by
  have ht : 0 ≤ f.rootEntrance := (by norm_num only : (0 : ℝ) ≤ 10000).trans f.rootEntrance_lower
  have h := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 10000) ht).mpr f.rootEntrance_lower
  norm_num only at h
  exact h

/-- A common logarithmic scale bounds the original quadratic level's logarithm.
Input: a positive input and a common upper scale. Claim: the level logarithm is at most L+2.
Proof: split the logarithm of four times the input.
Role: supply the arithmetic local-cost input to each reduced fourth-pole entrance. -/
private theorem fourPole_data_level_bound {n : ℕ} (hn : 0 < n) {L : ℝ} (hlog : Real.log n ≤ L) :
    Real.log (4 * n : ℕ) ≤ L + 2 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) hnR.ne',
    add_comm (Real.log (4 : ℝ))]
  apply add_le_add hlog
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num only, Real.log_pow]
  norm_num only
  linarith only [Real.log_two_lt_d9]

/-- The primitive quadratic conductor also fits the same upper scale.
Input: an odd input and its logarithmic upper scale. Claim: conductor logarithm is at most L+2.
Proof: the primitive conductor divides the original level.
Role: close the conductor-cost hypothesis internally rather than expose it to users. -/
private theorem fourPole_data_conductor_bound {n : ℕ} (hn : Odd n) {L : ℝ} (hlog : Real.log n ≤ L) :
    Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ L + 2 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hd := DirichletCharacter.conductor_dvd_level (NumberTheory.complexQuadraticCharacter n hn)
  have hcon := Nat.le_of_dvd (Nat.mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos) hd
  have hp : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero
  exact
    (Real.log_le_log (Nat.cast_pos.mpr hp) (Nat.cast_le.mpr hcon)).trans
      (fourPole_data_level_bound hn.pos hlog)

/-- Certified reduced entrance data yield an actual Jacobi prime at every common scale.
Input: a certified row, arithmetic bridge, GRH and a common scale above its squared entrance.
Claim: an odd prime with negative Jacobi value lies below the coefficient times that scale squared.
Proof: supply conductor and original-level costs, then apply the complete certified scalar gap.
Role: expose all three finite entrances with the same arithmetic and analytic contract. -/
theorem fourPole_reduced_jacobi_scale (f : FourPoleEntry) {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : f.rootEntrance ^ 2 ≤ L) (hlog : Real.log n ≤ L) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ f.coefficient * L ^ 2 ∧ jacobiSym n p = -1 := by
  have hLbase := (fourPole_data_scale_lower f).trans hL
  obtain ⟨hxl, _⟩ :=
    fourPole_scaled_bounds hLbase f.coefficient_lower f.coefficient_upper f.quarterUpper_nonneg
      f.quarterUpper_pow
  apply
    fourPole_exists_jacobi_scalar bridge hGRH
      ((by norm_num only : (2 : ℝ) ≤ 100000000).trans (hLbase.trans hxl))
  exact
    fourPole_scale_gap hLbase f.coefficient_lower f.coefficient_upper f.sqrtLower_nonneg
      f.quarterUpper_nonneg f.sqrtLower_sq f.quarterUpper_pow
      ((by norm_num only : (0 : ℝ) ≤ 10000).trans f.rootEntrance_lower) hL f.margin
      (fourPole_data_conductor_bound hn hlog)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using fourPole_data_level_bound hn.pos hlog)

/-- Reduced entrances supply an actual witness without an external arithmetic bridge.
Input: a certified row, an odd nonsquare input, GRH and the common-scale conditions.
Claim: an actual member of the negative witness set meets the certified bound.
Proof: construct the arithmetic data before applying the scalar-backed prime theorem.
Role: a closed public witness interface for all three numerical certificates. -/
theorem fourPole_reduced_scale_witness (f : FourPoleEntry) {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : f.rootEntrance ^ 2 ≤ L) (hlog : Real.log n ≤ L) :
    ∃ p : ℕ, p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ f.coefficient * L ^ 2 :=
  Nonempty.elim (NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns) fun bridge ↦
    Exists.elim (fourPole_reduced_jacobi_scale f bridge hGRH hL hlog) fun p hp ↦
      ⟨p, ⟨hp.1, hp.2.1, hp.2.2.2⟩, hp.2.2.1⟩

/-- The least actual negative witness obeys each certified reduced common-scale bound.
Input: a certified row, an odd nonsquare input, GRH, a valid scale and witness nonemptiness.
Claim: the least witness meets the selected squared-scale cutoff.
Proof: minimize the actual witness. Role: cumulative lifting without an unproved gap hypothesis. -/
theorem fourPole_reduced_scale_least (f : FourPoleEntry) {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : f.rootEntrance ^ 2 ≤ L) (hlog : Real.log n ≤ L)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ f.coefficient * L ^ 2 :=
  Exists.elim (fourPole_reduced_scale_witness f hn hns hGRH hL hlog) fun _p hp ↦
    (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw hp.1)).trans hp.2

end PseudoPrime.LLS.PaperStatements
