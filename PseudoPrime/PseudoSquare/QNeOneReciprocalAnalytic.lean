/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.QNeOneSharpAnalytic
public import PseudoPrime.PseudoSquare.Bounds.QNeOneLogSq
public import PseudoPrime.PseudoSquare.Bounds.PointwiseWitness
public import PseudoPrime.LLS.Extensions.QNeOneReciprocalSeparation

/-! # Shifted odd-Jacobi witnesses from the reciprocal three-branch comparison -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For an odd nonsquare arithmetic bridge under GRH with log squarefree
part at least 8501/1000, absence of witnesses through the shifted square is
impossible. Pass the shifted root and the original conductor level separately
to the three-branch comparison. This is the new analytic contradiction. -/
theorem qNeOneAnalyticFalse_of_reciprocal_shift {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hy : (8501 / 1000 : ℝ) ≤ bridge.y)
    (hno :
      ∀ p,
        p.Prime →
          Odd p → p ≤ ⌊(bridge.y - 1 / 1000) ^ 2⌋₊ → p ∉ NumberTheory.primeNeOneWitnessSet n) :
    False := by
  let _ : NeZero bridge.character.conductor :=
    ⟨by
      intro hc
      exact
        (inferInstance : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor).out
          ((DirichletCharacter.isPrimitive_def bridge.character).mp bridge.character_primitive ▸
            hc)⟩
  have hroot : (17 / 2 : ℝ) ≤ bridge.y - 1 / 1000 := by linarith only [hy]
  have hodd : LLS.Extensions.OddPrimeTrivial bridge.character ((bridge.y - 1 / 1000) ^ 2) :=
    bridge.primitiveCharacter_eq_one_in_log_square_range
      (show 1 ≤ bridge.y - 1 / 1000 by linarith only [hroot]) hno
  have hcases :=
    NumberTheory.isQuadratic_primitiveCharacter bridge.character bridge.character_quadratic
      (2 : ZMod bridge.character.conductor)
  exact
    LLS.Extensions.not_oddPrimeTrivial_of_reciprocal_entrance bridge.character
      bridge.character_ne_one bridge.primitiveCharacter_even hGRH hroot
      (by linarith only : bridge.y ≤ bridge.y - 1 / 1000 + 1 / 1000)
      bridge.log_character_conductor_le_y_add_log_four
      (qNeOne_log_conductor_le_y_of_two_ne_zero bridge) hcases hodd

/-- Under the analytic bridge assumptions, an actual odd prime with Jacobi
value not one lies through (log squarefree part-1/1000)^2. Negate witness
existence and apply the shifted contradiction. Zero values are allowed. -/
theorem exists_prime_ne_one_witness_le_reciprocal_shift {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hy : (8501 / 1000 : ℝ) ≤ bridge.y) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (bridge.y - 1 / 1000) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  by_contra h
  apply qNeOneAnalyticFalse_of_reciprocal_shift bridge hGRH hy
  intro p hp ho hb hmem
  apply h
  exact
    ⟨p, hp, ho, (Nat.floor_le (sq_nonneg (bridge.y - 1 / 1000))).trans' (Nat.cast_le.mpr hb),
      hmem.2.2⟩

/-- Every natural input at least 4920 has logarithm at least 8501/1000.
A short rational Taylor certificate proves the endpoint, and monotonicity
covers the half-line. This converts the real analytic entrance to integers. -/
theorem log_ge_reciprocal_shift_entrance {d : ℕ} (hd : 4920 ≤ d) :
    (8501 / 1000 : ℝ) ≤ Real.log d := by
  have hc : Analysis.rationalLogIntervalCheck 4920 12 14 (8501 / 1000) (851 / 100) = true := by
    decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  exact h.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hd))

/-- Under GRH, an odd nonsquare bridge with squarefree part at least 4920
has an odd-prime non-one witness below the shifted squarefree logarithmic square.
Apply the certified log entrance to the analytic existence theorem. -/
theorem exists_prime_ne_one_witness_le_reciprocal_shift_of_ge_4920 {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hd : 4920 ≤ bridge.squarefreePart) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (bridge.y - 1 / 1000) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  exact
    exists_prime_ne_one_witness_le_reciprocal_shift bridge hGRH
      (log_ge_reciprocal_shift_entrance hd)

/-- For an odd nonsquare bridge with squarefree part at least 4920, the
shifted squarefree logarithmic square is strictly below log(n)^2.
The squarefree part does not exceed n and the shift is strictly negative.
The conclusion includes squarefree inputs, with no strict part inequality. -/
theorem reciprocal_shift_sq_lt_input_log_sq {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hd : 4920 ≤ bridge.squarefreePart) : (bridge.y - 1 / 1000) ^ 2 < (Real.log n) ^ 2 := by
  have hs : 1 ≤ bridge.squareFactor ^ 2 :=
    Nat.succ_le_iff.mpr (pow_pos (Odd.pos bridge.squareFactor_odd) 2)
  have hm := Nat.mul_le_mul_right bridge.squarefreePart hs
  rw [one_mul, bridge.squarefreePart_sq_mul] at hm
  have hlog : bridge.y ≤ Real.log n :=
    Real.log_le_log (Nat.cast_pos.mpr bridge.squarefreePart_pos) (Nat.cast_le.mpr hm)
  have hy := log_ge_reciprocal_shift_entrance hd
  have hroot : 0 ≤ bridge.y - 1 / 1000 := by
    change _ ≤ Real.log bridge.squarefreePart - _
    linarith only [hy]
  have hlt : bridge.y - 1 / 1000 < Real.log n := by linarith only [hlog]
  exact (sq_lt_sq₀ hroot (hroot.trans hlt.le)).mpr hlt

/-- Under GRH and the squarefree-part entrance, the same odd-prime Jacobi
non-one witness satisfies both the shifted upper bound and the strict input
logarithmic-square bound. Combine existence with the analytic root comparison. -/
theorem exists_prime_ne_one_witness_le_reciprocal_shift_and_lt_log_sq {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hd : 4920 ≤ bridge.squarefreePart) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (bridge.y - 1 / 1000) ^ 2 ∧ (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_ne_one_witness_le_reciprocal_shift_of_ge_4920 bridge hGRH hd
  exact ⟨p, hp, ho, hb, hb.trans_lt (reciprocal_shift_sq_lt_input_log_sq bridge hd), hv⟩

/-- Under the analytic bridge assumptions and squarefree part at least 4920,
the least odd-prime non-one witness obeys the shifted bound.
Compare it with the constructed witness, keeping nonemptiness explicit. -/
theorem primeNeOneWitness_cast_le_reciprocal_shift {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hd : 4920 ≤ bridge.squarefreePart) (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (bridge.y - 1 / 1000) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_ne_one_witness_le_reciprocal_shift_of_ge_4920 bridge hGRH hd
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- A squarefree natural number greater than one is not a square.
A square representation would force its root to be a unit and the number
to equal one. This supplies the small-squarefree-part transfer condition. -/
theorem squarefree_not_isSquare_of_one_lt {n : ℕ} (hsf : Squarefree n) (hn : 1 < n) :
    ¬IsSquare n := by
  rintro ⟨a, ha⟩
  have hd : a * a ∣ n := ⟨1, by simpa only [mul_one] using ha⟩
  have hu := Nat.isUnit_iff.mp (hsf a hd)
  rw [hu, one_mul] at ha
  nlinarith only [hn, ha]

/-- The squarefree-part logarithm of an odd nonsquare bridge does not exceed
log n. Use the positive square factor in its exact decomposition and log
monotonicity. This transports shifted radii to a common endpoint. -/
theorem qNeOne_bridge_y_le_log_input {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) : bridge.y ≤ Real.log n := by
  have hs : 1 ≤ bridge.squareFactor ^ 2 :=
    Nat.succ_le_iff.mpr (pow_pos (Odd.pos bridge.squareFactor_odd) 2)
  have hm := Nat.mul_le_mul_right bridge.squarefreePart hs
  rw [one_mul, bridge.squarefreePart_sq_mul] at hm
  exact Real.log_le_log (Nat.cast_pos.mpr bridge.squarefreePart_pos) (Nat.cast_le.mpr hm)

/-- A natural input at most 4919 has logarithm at most 8501/1000.
Treat zero separately, then use a rational Taylor certificate and monotonicity.
This is a numerical bound, without enumerating Jacobi witnesses. -/
theorem log_le_small_reciprocal_entrance {d : ℕ} (hd : d ≤ 4919) :
    Real.log d ≤ (8501 / 1000 : ℝ) := by
  by_cases h0 : d = 0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    norm_num only
  · have hc : Analysis.rationalLogIntervalCheck 4919 12 14 (17 / 2) (8501 / 1000) = true := by
      decide +kernel
    have h := (Analysis.rationalLogIntervalCheck_sound hc).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact (Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)) (Nat.cast_le.mpr hd)).trans h

/-- Under GRH, every odd nonsquare n with log n at most L and L at least
8501/1000 has an odd-prime non-one witness at most (L-1/1000)^2.
Use the new analytic theorem for large squarefree parts. For smaller parts,
reuse the existing pointwise GRH theorem and integer rounding, then transfer
its witness. No new finite modulus certificate is generated. -/
theorem exists_prime_ne_one_witness_le_reciprocal_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    {L : ℝ} (hL : (8501 / 1000 : ℝ) ≤ L) (hlogn : Real.log n ≤ L)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (L - 1 / 1000) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  let : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨NumberTheory.complexQuadraticCharacter_conductor_ne_zero n hn⟩
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData (Odd.pos hn) hn hns
  by_cases hd : 4920 ≤ bridge.squarefreePart
  · obtain ⟨p, hp, ho, hb, hv⟩ :=
      exists_prime_ne_one_witness_le_reciprocal_shift_of_ge_4920 bridge hGRH hd
    have hy := log_ge_reciprocal_shift_entrance hd
    have hlev := (qNeOne_bridge_y_le_log_input bridge).trans hlogn
    have hroot : 0 ≤ bridge.y - 1 / 1000 := by
      change _ ≤ Real.log bridge.squarefreePart - _
      linarith only [hy]
    have hsq : (bridge.y - 1 / 1000) ^ 2 ≤ (L - 1 / 1000) ^ 2 :=
      (sq_le_sq₀ hroot (by linarith only [hL])).mpr (by linarith only [hlev])
    exact ⟨p, hp, ho, hb.trans hsq, hv⟩
  · have hdsmall : bridge.squarefreePart ≤ 4919 := Nat.le_of_lt_succ (lt_of_not_ge hd)
    have hdns :=
      squarefree_not_isSquare_of_one_lt bridge.squarefreePart_squarefree
        bridge.squarefreePart_gt_one
    obtain ⟨p, hp, ho, hb, hv⟩ :=
      exists_prime_ne_one_witness_of_grh hGRH bridge.squarefreePart_pos bridge.squarefreePart_odd
        hdns
    have hpn := NumberTheory.primeNeOneWitness_mem_of_squarefreePart_mem bridge ⟨hp, ho, hv⟩
    have hlog0 : 0 ≤ Real.log bridge.squarefreePart :=
      Real.log_nonneg (by exact_mod_cast bridge.squarefreePart_gt_one.le)
    have hlog := log_le_small_reciprocal_entrance hdsmall
    have hs : (Real.log bridge.squarefreePart) ^ 2 ≤ (8501 / 1000 : ℝ) ^ 2 :=
      (sq_le_sq₀ hlog0 (by norm_num only)).mpr hlog
    have hbudget : max (5 : ℝ) ((Real.log bridge.squarefreePart) ^ 2) < 73 :=
      max_lt (by norm_num only) (hs.trans_lt (by norm_num only))
    have hpN : p < 73 := by exact_mod_cast (hb.trans_lt hbudget)
    have hp72 : (p : ℝ) ≤ 72 := Nat.cast_le.mpr (Nat.le_of_lt_succ hpN)
    have hcap : (72 : ℝ) ≤ (L - 1 / 1000) ^ 2 := by nlinarith only [hL]
    exact ⟨p, hpn.1, hpn.2.1, hp72.trans hcap, hpn.2.2⟩

/-- Under the common-endpoint assumptions, the least odd-prime Jacobi
non-one witness is at most (L-1/1000)^2. Compare it with the endpoint witness.
This supplies the input used by full finite-maximum bounds. -/
theorem primeNeOneWitness_cast_le_reciprocal_endpoint
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L : ℝ} (hL : (8501 / 1000 : ℝ) ≤ L) (hlogn : Real.log n ≤ L)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (L - 1 / 1000) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_ne_one_witness_le_reciprocal_endpoint hn hns hL hlogn hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH, every odd nonsquare n at least 4920 has an odd-prime Jacobi
non-one witness through (log n-1/1000)^2 and strictly below log(n)^2.
Use the common endpoint at log n. Small squarefree parts reuse the earlier
pointwise theorem, while large parts use the new analytic comparison. -/
theorem exists_prime_ne_one_witness_le_reciprocal_shift_and_lt_log_sq_of_ge_4920
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlarge : 4920 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (Real.log n - 1 / 1000) ^ 2 ∧ (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  have hL := log_ge_reciprocal_shift_entrance hlarge
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_ne_one_witness_le_reciprocal_endpoint hn hns hL (le_refl _) hGRH
  have hs : (Real.log n - 1 / 1000) ^ 2 < (Real.log n) ^ 2 := by nlinarith only [hL]
  exact ⟨p, hp, ho, hb, hb.trans_lt hs, hv⟩

/-- Under GRH for every B at least 4920, the finite maximum of least
non-one witnesses through B is at most (log B-1/1000)^2.
Apply the same endpoint theorem to every admissible input, including small
inputs and small squarefree parts. This is a full-domain finite maximum. -/
theorem QNeOne_le_reciprocal_shift_of_ge_4920 {B : ℕ} (hB : 4920 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ (Real.log B - 1 / 1000) ^ 2 := by
  apply QNeOne_cast_le_of_forall (sq_nonneg _)
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Odd.pos ha.odd
  have hnB : (n : ℝ) ≤ B := by exact_mod_cast ha.le
  exact
    primeNeOneWitness_cast_le_reciprocal_endpoint hGRH ha.odd ha.not_isSquare
      (log_ge_reciprocal_shift_entrance hB) (Real.log_le_log hn0 hnB)
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

end PseudoPrime.PseudoSquare
