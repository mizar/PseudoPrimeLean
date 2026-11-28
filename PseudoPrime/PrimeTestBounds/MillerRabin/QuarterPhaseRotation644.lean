/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseArithmetic644
public import PseudoPrime.Analysis.QuarterPhaseHorner

/-! # Checked quarter-turn phase rectangles for the section 122 endpoints -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The center of the reduced phase rectangle, rounded down at scale G. -/
def phaseCenter644 (G k : ℤ) (A P : Analysis.IntegerInterval) : ℤ :=
  let R := Analysis.quarterRemainder G k A P
  (R.lower + R.upper) / 2

/-- The chosen center and both endpoints determine the perturbation radius.
Its integer value counts the wider of the two distances to the center. -/
def phaseError644 (G k : ℤ) (A P : Analysis.IntegerInterval) : ℤ :=
  let R := Analysis.quarterRemainder G k A P
  let c := phaseCenter644 G k A P
  max (c - R.lower) (R.upper - c)

/-- The integer quarter turn reduced to one of four rotations. -/
def phaseTurn644 (k : ℤ) : Fin 4 :=
  ⟨(k % 4).toNat,
    (Int.toNat_lt (Int.emod_nonneg k (by decide : (4 : ℤ) ≠ 0))).mpr
      (Int.emod_lt_of_pos k (by decide : 0 < (4 : ℤ)))⟩

/-- Compute a rectangle for the phase by quarter-turn reduction, a rounded
Taylor argument, and two outward squarings. The integer residue determines
the final exact rotation. -/
def phaseRotationBox644 (G k : ℤ) (A P : Analysis.IntegerInterval) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  Analysis.quarterComputedResult (Analysis.roundedConstant G (phaseCenter644 G k A P) (4 * G)) G 1
    (phaseError644 G k A P) (phaseTurn644 k)

private theorem phase_center_small {G c : ℤ} (hG : 0 < G) (hl : -G ≤ c) (hu : c ≤ G) :
    |((c : ℝ) / (4 * (G : ℝ)))| ≤ 1 / 4 := by
  have hg : 0 < (G : ℝ) := Int.cast_pos.mpr hG
  have hlo : -(G : ℝ) ≤ (c : ℝ) := by exact_mod_cast hl
  have hhi : (c : ℝ) ≤ (G : ℝ) := by exact_mod_cast hu
  rw [abs_div, abs_of_nonneg (mul_nonneg (by norm_num only) hg.le)]
  apply (div_le_iff₀ (mul_pos (by norm_num only) hg)).mpr
  have h := abs_le.mpr ⟨hlo, hhi⟩
  linarith only [h]

/-- An interval for the angle and one for π determine a certified phase
rectangle if the computed center is inside the Taylor domain. No squaring
or polynomial product witnesses are required from the caller. -/
theorem phase_rotation_box_sound {G k : ℤ} (hG : 0 < G) {A P : Analysis.IntegerInterval} {x : ℝ}
    (hx : A.Contains G x) (hpi : P.Contains G Real.pi) (hl : -G ≤ phaseCenter644 G k A P)
    (hu : phaseCenter644 G k A P ≤ G) (he : (1 / 2 ^ 120 : ℝ) ≤ 1 / (G : ℝ)) :
    Analysis.complexIntervalContains (phaseRotationBox644 G k A P).1 (phaseRotationBox644 G k A P).2
      G (Complex.exp (Complex.I * (x : ℂ))) := by
  let c := phaseCenter644 G k A P
  let d := phaseError644 G k A P
  let q : ℚ := (c : ℚ) / (4 * (G : ℚ))
  let j : Fin 4 := (phaseTurn644 k)
  have hq : (q : ℝ) = (c : ℝ) / (4 * (G : ℝ)) := by
    norm_num only [q, Rat.cast_div, Rat.cast_mul, Rat.cast_intCast, Rat.cast_ofNat]
  have hX : (Analysis.roundedConstant G c (4 * G)).Contains G (q : ℝ) := by
    rw [hq]
    have h :=
      Analysis.roundedConstant_contains (p := c) hG (mul_pos (by norm_num only : (0 : ℤ) < 4) hG)
    norm_num only [Int.cast_mul, Int.cast_ofNat, Int.reduceMul] at h
    exact h
  have hsmall : |(q : ℝ)| ≤ 1 / 4 := hq ▸ phase_center_small hG hl hu
  have hcenter : 4 * (q : ℝ) = (c : ℝ) / G := by
    rw [hq]
    ring
  have hj : k % 4 = j.val := by
    dsimp only [j, phaseTurn644]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide : (4 : ℤ) ≠ 0))]
  have hleft : c - d ≤ (Analysis.quarterRemainder G k A P).lower := by
    have h : c - (Analysis.quarterRemainder G k A P).lower ≤ d := le_max_left _ _
    exact sub_le_comm.mp h
  have hright : (Analysis.quarterRemainder G k A P).upper ≤ c + d := by
    have h : (Analysis.quarterRemainder G k A P).upper - c ≤ d := le_max_right _ _
    exact (sub_le_iff_le_add.mp h).trans_eq (add_comm _ _)
  rw [mul_comm Complex.I]
  exact
    Analysis.quarter_computed_checked _ A P G 1 d c q x k j hG hX hsmall
      (by simpa only [Int.cast_one] using he) hj hx hpi hcenter hleft hright

/-- At the common positive scale, an ordinate interval and an interval
for twice the radius logarithm determine both required angle intervals.
The shifted angle uses the exact rational displacement of the Mellin term. -/
theorem phase_angle_boxes_644 {G : ℤ} (hG : 0 < G) {A T : Analysis.IntegerInterval} {x t : ℝ}
    (hx : A.Contains G x) (ht : T.Contains G t) :
    (Analysis.roundedProduct G A T).Contains G (x * t) ∧
      (Analysis.roundedProduct G (A.add (Analysis.roundedConstant G 2687 1000)) T).Contains G
        ((x + 2687 / 1000) * t) := by
  have hs : (Analysis.roundedConstant G 2687 1000).Contains G (2687 / 1000 : ℝ) := by
    simpa only [Int.cast_ofNat] using
      Analysis.roundedConstant_contains (p := 2687) hG (by decide : (0 : ℤ) < 1000)
  exact
    ⟨Analysis.roundedProduct_contains hG hx ht,
      Analysis.roundedProduct_contains hG (Analysis.IntegerInterval.add_contains hx hs) ht⟩

/-- Compute the angle box from a logarithm box and an ordinate box.
The Boolean selects the exact Mellin shift when it is true. -/
def phaseAngle644 (G : ℤ) (A T : Analysis.IntegerInterval) (shifted : Bool) :
    Analysis.IntegerInterval :=
  Analysis.roundedProduct G (if shifted then A.add (Analysis.roundedConstant G 2687 1000) else A) T

/-- Combine the computed rotations and the two coefficient rectangles at
each of the 29 ordinate brackets. The only angle witnesses are the integer
quarter turns and the checks that their centers lie in the Taylor domain. -/
theorem phase_endpoint_rotations_lower_644 {G : ℤ} (hG : 0 < G) {A P : Analysis.IntegerInterval}
    {x : ℝ} (hx : A.Contains G x) (hpi : P.Contains G Real.pi)
    (he : (1 / 2 ^ 120 : ℝ) ≤ 1 / (G : ℝ)) (g : Fin 29 → ℝ) (T : Fin 29 → Analysis.IntegerInterval)
    (ht : ∀ i, (T i).Contains G (g i)) (k : Fin 29 → Bool → ℤ)
    (hc : ∀ i f, |phaseCenter644 G (k i f) (phaseAngle644 G A (T i) f) P| ≤ G)
    (R S : Fin 29 → Analysis.IntegerInterval × Analysis.IntegerInterval)
    (hR : ∀ i, Analysis.complexIntervalContains (R i).1 (R i).2 G (quarterPhaseRational644 (g i)))
    (hS : ∀ i, Analysis.complexIntervalContains (S i).1 (S i).2 G (quarterPhasePole644 (g i))) :
    let E := fun i f ↦ phaseRotationBox644 G (k i f) (phaseAngle644 G A (T i) f) P
    let W :=
      Analysis.intervalFinsetSum Finset.univ
        (fun i ↦ phaseTermBox G (R i) (S i) (E i false) (E i true))
    2 * ((W.lower : ℝ) / G) ≤ pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) x := by
  intro E W
  have h (i : Fin 29) (f : Bool) :
    Analysis.complexIntervalContains (E i f).1 (E i f).2 G
      (Complex.exp (Complex.I * ((((if f then x + 2687 / 1000 else x) * g i : ℝ)) : ℂ))) := by
    have hA :
      (phaseAngle644 G A (T i) f).Contains G ((if f then x + 2687 / 1000 else x) * g i) := by
      cases f
      · exact (phase_angle_boxes_644 hG hx (ht i)).1
      · exact (phase_angle_boxes_644 hG hx (ht i)).2
    exact phase_rotation_box_sound hG hA hpi (abs_le.mp (hc i f)).1 (abs_le.mp (hc i f)).2 he
  exact
    phase_endpoint_boxes_lower_644 hG g x R S (fun i ↦ E i false) (fun i ↦ E i true) hR hS
      (fun i ↦ h i false) (fun i ↦ h i true)

end PseudoPrime.PrimeTestBounds.MillerRabin
