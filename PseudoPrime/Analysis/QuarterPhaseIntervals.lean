/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.QuarterPhase
public import PseudoPrime.Analysis.IntegerIntervalPhase
public import PseudoPrime.Analysis.IntegerIntervalComputed

/-! # Quarter-turn rotations of complex integer intervals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Compute an outward-rounded interval for `x - k * π / 2` from input intervals for `x` and
`π`, an integer quarter-turn count, and a common integer scale. The product uses four endpoint
products and works for either sign of `k`. The result supplies the phase-reduction checker. -/
def quarterRemainder (G k : ℤ) (X P : IntegerInterval) : IntegerInterval :=
  X.add (roundedProduct G (roundedConstant G k 2) P).neg

/-- At positive scale, the computed remainder interval contains the exact phase remainder when
the input intervals contain `x` and the true value of `π`. Outward-rounded multiplication and
interval negation handle negative quarter turns without assuming a particular rounding choice. -/
theorem quarterRemainder_contains {G k : ℤ} {X P : IntegerInterval} {x : ℝ} (hG : 0 < G)
    (hx : X.Contains G x) (hpi : P.Contains G Real.pi) :
    (quarterRemainder G k X P).Contains G (x - (k : ℝ) * (Real.pi / 2)) := by
  have hc := roundedConstant_contains (p := k) (d := 2) hG (by decide)
  have hp := roundedProduct_contains hG hc hpi
  have hr := IntegerInterval.add_contains hx (IntegerInterval.neg_contains hp)
  have he : x - (k : ℝ) * (Real.pi / 2) = x + -(((k : ℝ) / 2) * Real.pi) := by ring
  rw [he]
  exact hr

/-- An integer interval contained in `[-1,1]` bounds one quarter of every real point in it by
`1/4` in absolute value. Integer endpoint comparisons and a positive scale provide the required
Taylor-domain condition for the compact phase checker. -/
theorem quarter_remainder_small {G : ℤ} {B : IntegerInterval} {r : ℝ} (hG : 0 < G)
    (hr : B.Contains G r) (hl : -G ≤ B.lower) (hu : B.upper ≤ G) : |r / (2 : ℝ) ^ 2| ≤ 1 / 4 := by
  have hg : (0 : ℝ) < G := Int.cast_pos.mpr hG
  have hlo : (-1 : ℝ) ≤ r := by
    have hcast : (-(G : ℝ)) ≤ (B.lower : ℝ) := by exact_mod_cast hl
    have hdiv := div_le_div_of_nonneg_right hcast hg.le
    have hone : (-(G : ℝ)) / G = -1 := by rw [neg_div, div_self (ne_of_gt hg)]
    exact (hone ▸ hdiv).trans hr.1
  have hhi : r ≤ 1 := by
    have hcast : (B.upper : ℝ) ≤ G := by exact_mod_cast hu
    have hdiv := div_le_div_of_nonneg_right hcast hg.le
    have hone : (G : ℝ) / G = 1 := div_self (ne_of_gt hg)
    exact hr.2.trans (hone ▸ hdiv)
  have habs : |r| ≤ 1 := abs_le.mpr ⟨hlo, hhi⟩
  have htwo : (0 : ℝ) < 2 ^ 2 := pow_pos (by norm_num only) 2
  rw [abs_div, abs_of_pos htwo]
  have h := div_le_div_of_nonneg_right habs htwo.le
  norm_num only [OfNat.ofNat_ne_zero, Nat.ofNat_pos, pow_two, mul_one] at h ⊢
  exact h

/-- If both integer endpoints lie within `d` ticks of `c`, every real point in the interval lies
within `d / G` of `c / G` at positive scale. The two integer comparisons provide the perturbation
bound needed when a rational Taylor center approximates the exact reduced phase. -/
theorem interval_center_distance {G c d : ℤ} {B : IntegerInterval} {r : ℝ} (hG : 0 < G)
    (hr : B.Contains G r) (hl : c - d ≤ B.lower) (hu : B.upper ≤ c + d) :
    |r - (c : ℝ) / G| ≤ (d : ℝ) / G := by
  have hg : (0 : ℝ) < G := Int.cast_pos.mpr hG
  have hlo : ((c : ℝ) - d) / G ≤ r := by
    have hc : (c : ℝ) - d ≤ B.lower := by exact_mod_cast hl
    exact (div_le_div_of_nonneg_right hc hg.le).trans hr.1
  have hhi : r ≤ ((c : ℝ) + d) / G := by
    have hc : (B.upper : ℝ) ≤ (c : ℝ) + d := by exact_mod_cast hu
    exact hr.2.trans (div_le_div_of_nonneg_right hc hg.le)
  rw [abs_le]
  constructor
  · rw [sub_div] at hlo
    linarith only [hlo]
  · rw [add_div] at hhi
    linarith only [hhi]

/-- Rotate a complex rectangle by one of four exact quarter turns. The input intervals enclose
the real and imaginary coordinates at a common scale; the output swaps or negates them as needed.
No multiplication, rounding, or indexed certificate list is needed for this rotation. -/
def quarterRotate (R I : IntegerInterval) : Fin 4 → IntegerInterval × IntegerInterval
  | 0 => (R, I)
  | 1 => (I.neg, R)
  | 2 => (R.neg, I.neg)
  | 3 => (I, R.neg)

/-- A checked residue modulo four transports complex interval containment through an integer
power of `I`. The four cases use exact coordinate swaps and negation. This supplies the rotation
step of the reduced-phase checker for positive or negative integer quarter turns. -/
theorem quarterRotate_contains (R I : IntegerInterval) (G : ℤ) (z : ℂ) (k : ℤ) (j : Fin 4)
    (hj : k % 4 = j.val) (hz : complexIntervalContains R I G z) :
    complexIntervalContains (quarterRotate R I j).1 (quarterRotate R I j).2 G
      (z * Complex.I ^ k) := by
  rw [I_zpow_mod_four, hj]
  fin_cases j
  · simpa only [Fin.val_zero, Nat.cast_zero, zpow_zero, mul_one, quarterRotate] using hz
  · simpa only [Fin.val_one, Nat.cast_one, zpow_one, quarterRotate, complexIntervalContains,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      zero_add, sub_eq_add_neg, add_zero] using
      (show (I.neg.Contains G (-z.im) ∧ R.Contains G z.re) from
        ⟨IntegerInterval.neg_contains hz.2, hz.1⟩)
  · simpa only [Fin.val_fin_le, Nat.cast_ofNat, zpow_ofNat, Complex.I_sq, mul_neg, mul_one,
      quarterRotate, complexIntervalContains, Complex.neg_re, Complex.neg_im] using
      (show (R.neg.Contains G (-z.re) ∧ I.neg.Contains G (-z.im)) from
        ⟨IntegerInterval.neg_contains hz.1, IntegerInterval.neg_contains hz.2⟩)
  · have hi : Complex.I ^ 3 = -Complex.I := by
      rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, Complex.I_sq, neg_one_mul]
    simpa only [Fin.val_fin_le, Nat.cast_ofNat, zpow_ofNat, hi, mul_neg, quarterRotate,
      complexIntervalContains, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, sub_eq_add_neg, add_zero,
      neg_neg] using
      (show (I.Contains G z.im ∧ R.neg.Contains G (-z.re)) from
        ⟨hz.2, IntegerInterval.neg_contains hz.1⟩)

/-- A Taylor enclosure at one quarter of the exact reduced phase, two checked squarings, and
the checked quarter-turn residue enclose the original complex exponential. The remainder uses
the true value of `π`; callers must separately certify its interval and the small-angle bound.
The result connects the existing phase checker to compact quarter-turn reduction. -/
theorem quarter_phase_contains (chain : List PhaseSquareWitness) (R I : IntegerInterval) (G e : ℤ)
    (x r : ℝ) (k : ℤ) (j : Fin 4) (hlen : chain.length = 2) (hr : r = x - k * (Real.pi / 2))
    (hj : k % 4 = j.val) (hs : |r / (2 : ℝ) ^ 2| ≤ 1 / 4)
    (hp :
      complexIntervalContains R I G
        (∑ m ∈ Finset.range 25, (((r / (2 : ℝ) ^ 2 : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)))
    (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G)
    (hc : phaseSquareCheck G (R.widen e) (I.widen e) chain = true) :
    complexIntervalContains
      (quarterRotate (phaseSquareResult (R.widen e) (I.widen e) chain).1
          (phaseSquareResult (R.widen e) (I.widen e) chain).2 j).1
      (quarterRotate (phaseSquareResult (R.widen e) (I.widen e) chain).1
          (phaseSquareResult (R.widen e) (I.widen e) chain).2 j).2
      G (Complex.exp ((x : ℂ) * Complex.I)) := by
  have h := phase_reduced_contains chain 2 R I G e r hlen hs hp he hc
  have hz := quarterRotate_contains _ _ G _ k j hj h
  have hx : x = r + k * (Real.pi / 2) := by rw [hr, sub_add_cancel]
  rw [hx, exp_quarter_turn]
  exact hz

/-- Integer bounds on the computed quarter-turn remainder discharge the small-angle hypothesis
of the compact phase checker. Given certified input and π intervals, a Taylor enclosure, two
checked squarings, and a residue modulo four, the output encloses the original phase. The Taylor
enclosure itself is an explicit input and must be supplied by a separate soundness theorem. -/
theorem quarter_phase_checked (chain : List PhaseSquareWitness) (R I X P : IntegerInterval)
    (G e k : ℤ) (x : ℝ) (j : Fin 4) (hG : 0 < G) (hx : X.Contains G x) (hpi : P.Contains G Real.pi)
    (hl : -G ≤ (quarterRemainder G k X P).lower) (hu : (quarterRemainder G k X P).upper ≤ G)
    (hlen : chain.length = 2) (hj : k % 4 = j.val)
    (hp :
      complexIntervalContains R I G
        (∑ m ∈ Finset.range 25,
          ((((x - k * (Real.pi / 2)) / (2 : ℝ) ^ 2 : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)))
    (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G)
    (hc : phaseSquareCheck G (R.widen e) (I.widen e) chain = true) :
    complexIntervalContains
      (quarterRotate (phaseSquareResult (R.widen e) (I.widen e) chain).1
          (phaseSquareResult (R.widen e) (I.widen e) chain).2 j).1
      (quarterRotate (phaseSquareResult (R.widen e) (I.widen e) chain).1
          (phaseSquareResult (R.widen e) (I.widen e) chain).2 j).2
      G (Complex.exp ((x : ℂ) * Complex.I)) := by
  have hr := quarterRemainder_contains (k := k) hG hx hpi
  have hs := quarter_remainder_small hG hr hl hu
  exact quarter_phase_contains chain R I G e x _ k j hlen rfl hj hs hp he hc

end PseudoPrime.Analysis
