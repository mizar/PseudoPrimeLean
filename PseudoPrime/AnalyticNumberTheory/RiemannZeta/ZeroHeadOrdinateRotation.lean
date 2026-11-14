/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPhaseRotation
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinateRational

/-! # Sequential rational checks for an ordinate phase -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Decide whether a rational phase state places the ordinate term between
rational endpoints after its explicit error allowance. -/
def rotationOrdinateStateCheck (q : ℚ) (z : ℚ × ℚ) (lo hi : ℚ) : Bool :=
  let v := rationalOrdinateSample q z
  let e := 2 / (100000000 * q)
  decide (lo ≤ v - e ∧ v + e ≤ hi)

/-- Check one logarithmic grid node using the iterated rounded rotation state. -/
def rotationOrdinateNodeCheck (A q lo hi : ℚ) (j : ℕ) : Bool :=
  rotationOrdinateStateCheck q (Analysis.rationalPhaseRotation (10 ^ 20) q A 24 12 j) lo hi

/-- A successful node check bounds the real ordinate term at the
corresponding logarithmic grid node. -/
theorem rotationOrdinateNodeCheck_sound (A q lo hi : ℚ) {j : ℕ} (hq : (0 : ℝ) < q)
    (hqu : (q : ℝ) ≤ 100) (hA : |(A : ℝ)| ≤ 21) (hj : j ≤ 1600)
    (hc : rotationOrdinateNodeCheck A q lo hi j = true) :
    (lo : ℝ) ≤ ordinateTerm ((A : ℝ) + (j : ℝ) / 250) (q : ℝ) ∧
      ordinateTerm ((A : ℝ) + (j : ℝ) / 250) (q : ℝ) ≤ (hi : ℝ) := by
  have hqabs : |(q : ℝ)| ≤ 100 := by
    rw [abs_of_pos hq]; exact hqu
  have hphase := Analysis.norm_rationalPhaseRotation20_error q A hqabs hA hj
  rw [norm_sub_rev] at hphase
  have he :
    ‖Complex.exp (Complex.I * (((A : ℝ) + (j : ℝ) / 250 : ℝ) : ℂ) * (q : ℂ)) -
          Analysis.rationalComplexCast (Analysis.rationalPhaseRotation (10 ^ 20) q A 24 12 j)‖ ≤
      (1 / 100000000 : ℝ) := by
    convert hphase using 1
    simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ratCast,
      Complex.ofReal_natCast, Complex.ofReal_ofNat]
  have herr :=
    ordinateTerm_rational_error ((A : ℝ) + (j : ℝ) / 250) q
      (Analysis.rationalPhaseRotation (10 ^ 20) q A 24 12 j) (1 / 100000000 : ℝ) hq he
  have h := of_decide_eq_true hc
  change
    lo ≤
        rationalOrdinateSample q (Analysis.rationalPhaseRotation (10 ^ 20) q A 24 12 j) -
          2 / (100000000 * q) ∧
      rationalOrdinateSample q (Analysis.rationalPhaseRotation (10 ^ 20) q A 24 12 j) +
          2 / (100000000 * q) ≤
        hi at h
  have h1 := (Rat.cast_le (K := ℝ)).mpr h.1
  have h2 := (Rat.cast_le (K := ℝ)).mpr h.2
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat] at h1 h2
  have hh := abs_le.mp herr
  simp only [div_eq_mul_inv, mul_inv_rev] at h1 h2 hh ⊢
  constructor <;> nlinarith only [h1, h2, hh.1, hh.2]

/-- Iterating once more equals starting from the first rotated state
and iterating the remaining times. -/
theorem rationalRotationIter_step_comm (G : ℕ) (rot z : ℚ × ℚ) (k : ℕ) :
    Analysis.rationalRotationIter G rot z (k + 1) =
      Analysis.rationalRotationIter G rot (Analysis.rationalRotationStep G rot z) k := by
  induction k generalizing z with
  | zero => rfl
  | succ k
    ih =>
    change
      Analysis.rationalRotationStep G rot (Analysis.rationalRotationIter G rot z (k + 1)) =
        Analysis.rationalRotationStep G rot
          (Analysis.rationalRotationIter G rot (Analysis.rationalRotationStep G rot z) k)
    rw [ih]

/-- Check a sequence of rational ordinate bounds while updating one rounded phase state per node. -/
def rotationOrdinateWalk (G : ℕ) (rot : ℚ × ℚ) (q : ℚ) (lo hi : ℕ → ℚ) : ℕ → ℕ → (ℚ × ℚ) → Bool
  | 0, _, _ => true
  | m + 1, j, z =>
    rotationOrdinateStateCheck q z (lo j) (hi j) &&
      rotationOrdinateWalk G rot q lo hi m (j + 1) (Analysis.rationalRotationStep G rot z)

/-- Every entry of a successful sequential walk satisfies its corresponding rational state check. -/
theorem rotationOrdinateWalk_get {G : ℕ} (rot z : ℚ × ℚ) (q : ℚ) (lo hi : ℕ → ℚ) {m j k : ℕ}
    (hk : k < m) (hc : rotationOrdinateWalk G rot q lo hi m j z = true) :
    rotationOrdinateStateCheck q (Analysis.rationalRotationIter G rot z k) (lo (j + k))
        (hi (j + k)) =
      true := by
  induction m generalizing j z k with
  | zero => exact (Nat.not_lt_zero k hk).elim
  | succ m ih =>
    simp only [rotationOrdinateWalk, Bool.and_eq_true] at hc
    cases k with
    | zero => simpa only [Analysis.rationalRotationIter, Nat.add_zero] using hc.1
    | succ k =>
      have hk' : k < m := Nat.lt_of_succ_lt_succ hk
      have h := ih (Analysis.rationalRotationStep G rot z) hk' hc.2
      rw [rationalRotationIter_step_comm]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Check every node from zero through N using a single rounded phase walk. -/
def rotationOrdinateGridCheck (A q : ℚ) (lo hi : ℕ → ℚ) (N : ℕ) : Bool :=
  rotationOrdinateWalk (10 ^ 20) (Analysis.rationalScaledPhase (10 ^ 20) (q / 250) 24 12) q lo hi
    (N + 1) 0 (Analysis.rationalScaledPhase (10 ^ 20) (A * q) 24 12)

/-- A successful grid check supplies real ordinate-term bounds
at every node through N. -/
theorem rotationOrdinateGridCheck_sound (A q : ℚ) (lo hi : ℕ → ℚ) {N : ℕ} (hq : (0 : ℝ) < q)
    (hqu : (q : ℝ) ≤ 100) (hA : |(A : ℝ)| ≤ 21) (hN : N ≤ 1600)
    (hc : rotationOrdinateGridCheck A q lo hi N = true) :
    ∀ j : ℕ,
      j ≤ N →
        (lo j : ℝ) ≤ ordinateTerm ((A : ℝ) + (j : ℝ) / 250) (q : ℝ) ∧
          ordinateTerm ((A : ℝ) + (j : ℝ) / 250) (q : ℝ) ≤ (hi j : ℝ) := by
  intro j hj
  have hw :=
    rotationOrdinateWalk_get (Analysis.rationalScaledPhase (10 ^ 20) (q / 250) 24 12)
      (Analysis.rationalScaledPhase (10 ^ 20) (A * q) 24 12) q lo hi (m := N + 1) (j := 0) (k := j)
      (Nat.lt_succ_of_le hj) hc
  have hn : rotationOrdinateNodeCheck A q (lo j) (hi j) j = true := by
    simpa only [rotationOrdinateNodeCheck, Analysis.rationalPhaseRotation, Nat.zero_add] using hw
  exact rotationOrdinateNodeCheck_sound A q (lo j) (hi j) hq hqu hA (hj.trans hN) hn

/-- The first ordinate sample passes the sequential rational checker
at the first eight log nodes. -/
theorem rotation_first_eight_checks :
    rotationOrdinateGridCheck (1381 / 100) (14473 / 1024) (fun _ ↦ 3 / 50) (fun _ ↦ 11 / 100) 7 =
      true := by
  decide +kernel

/-- The first ordinate sample lies in the certified interval at each
of the first eight log nodes. -/
theorem rotation_first_eight_bounds :
    ∀ j : ℕ,
      j ≤ 7 →
        (3 / 50 : ℝ) ≤ ordinateTerm (1381 / 100 + (j : ℝ) / 250) (14473 / 1024) ∧
          ordinateTerm (1381 / 100 + (j : ℝ) / 250) (14473 / 1024) ≤ (11 / 100 : ℝ) := by
  have h :=
    rotationOrdinateGridCheck_sound (1381 / 100) (14473 / 1024) (fun _ ↦ 3 / 50) (fun _ ↦ 11 / 100)
      (N := 7) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      rotation_first_eight_checks
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
