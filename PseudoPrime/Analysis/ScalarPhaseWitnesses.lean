/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ComputedScalarPhase

/-! # Cached arithmetic witnesses for continuous scalar phases -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Proposed arithmetic intervals for one continuous scalar phase enclosure.
Each field stores an intermediate bound rather than assuming it is correct.
The invariant is a successful check at a common positive scale, together with
real input and center containments. Soundness supplies the scalar quotient
for repeated cells without reevaluating the nested rounding algorithm. -/
structure ScalarPhaseWitness where
  /-- Product of the ordinate and continuous phase argument. -/
  argProduct : IntegerInterval
  /-- Center sine times the argument displacement. -/
  sinDisplacement : IntegerInterval
  /-- Center cosine times the argument displacement. -/
  cosDisplacement : IntegerInterval
  /-- Square of the ordinate input. -/
  square : IntegerInterval
  /-- Ordinate times the perturbed sine interval. -/
  weightedSin : IntegerInterval
  /-- Interval containing the exact constant one quarter. -/
  quarter : IntegerInterval
  /-- Positive reciprocal of the quarter-plus-square denominator. -/
  inverse : IntegerInterval
  /-- Final critical-line scalar quotient interval. -/
  out : IntegerInterval
  /-- Integer upper bound for the quadratic phase remainder. -/
  error : ℤ

/-- Subtract the certified center argument W from the stored argument product.
The result contains g*v-c once the product and input containments are proved. -/
def ScalarPhaseWitness.displacement (w : ScalarPhaseWitness) (W : IntegerInterval) :
    IntegerInterval :=
  w.argProduct.add W.neg

/-- Perturbed cosine interval from center C and the checked sine-displacement
product. The stored quadratic error widens both endpoints. -/
def ScalarPhaseWitness.cosine (w : ScalarPhaseWitness) (C : IntegerInterval) : IntegerInterval :=
  (C.add w.sinDisplacement.neg).widen w.error

/-- Perturbed sine interval from center S and the checked cosine-displacement
product, widened by the stored quadratic error. -/
def ScalarPhaseWitness.sine (w : ScalarPhaseWitness) (S : IntegerInterval) : IntegerInterval :=
  (S.add w.cosDisplacement).widen w.error

/-- Check every proposed arithmetic witness at scale G for ordinate A,
argument V, center argument W, and center coordinates C,S. Products, the
quadratic remainder, one quarter, and the positive reciprocal are all checked;
no table entry is trusted merely because it has been stored. -/
def ScalarPhaseWitness.check (w : ScalarPhaseWitness) (G : ℤ) (A V W C S : IntegerInterval) :
    Bool :=
  let D := w.displacement W
  let PC := w.cosine C
  let PS := w.sine S
  let den := w.quarter.add w.square
  let num := PC.add (w.weightedSin.scale 2)
  integerProductCheck G A.lower A.upper V.lower V.upper w.argProduct.lower w.argProduct.upper &&
    integerProductCheck G S.lower S.upper D.lower D.upper w.sinDisplacement.lower
      w.sinDisplacement.upper &&
    integerProductCheck G C.lower C.upper D.lower D.upper w.cosDisplacement.lower
      w.cosDisplacement.upper &&
    phaseRadiusCheck G (max |D.lower| |D.upper|) w.error &&
    integerConstantCheck G 1 4 w.quarter.lower w.quarter.upper &&
    integerProductCheck G A.lower A.upper A.lower A.upper w.square.lower w.square.upper &&
    integerProductCheck G A.lower A.upper PS.lower PS.upper w.weightedSin.lower
      w.weightedSin.upper &&
    integerReciprocalCheck G den.lower den.upper w.inverse.lower w.inverse.upper &&
    integerProductCheck G num.lower num.upper w.inverse.lower w.inverse.upper w.out.lower
      w.out.upper

/-- Checked witnesses and containments of the real ordinate, argument and
phase center imply the scalar quotient enclosure. The proof composes existing
primitive soundness and the sharp quadratic phase estimate; no zero-existence
assumption or external numerical table is needed for this arithmetic step. -/
theorem ScalarPhaseWitness.check_sound (w : ScalarPhaseWitness) {G : ℤ}
    {A V W C S : IntegerInterval} {g v c : ℝ} (hg : A.Contains G g) (hv : V.Contains G v)
    (hw : W.Contains G c) (hp : complexIntervalContains C S G (Complex.exp ((c : ℂ) * Complex.I)))
    (hc : w.check G A V W C S = true) :
    w.out.Contains G ((Real.cos (g * v) + 2 * g * Real.sin (g * v)) / ((1 / 4 : ℝ) + g ^ 2)) := by
  simp only [ScalarPhaseWitness.check, Bool.and_eq_true_iff] at hc
  rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨hArg, hSD⟩, hCD⟩, hRad⟩, hQ⟩, hAA⟩, hAS⟩, hInv⟩, hOut⟩
  have hG : 0 < G := (of_decide_eq_true hRad).1
  have hd : (w.displacement W).Contains G (g * v - c) := by
    simpa only [ScalarPhaseWitness.displacement, sub_eq_add_neg] using
      IntegerInterval.add_contains (IntegerInterval.product_contains hArg hg hv)
        (IntegerInterval.neg_contains hw)
  have hphase := phase_cell_radius_contains hp hd hSD hCD hRad (interval_abs_le hG hd)
  have hquarter := integerConstantCheck_sound hQ
  norm_num only [Int.cast_one, Int.cast_ofNat] at hquarter
  exact scalar_phase_contains hg hphase hquarter hAA hAS hInv hOut

end PseudoPrime.Analysis
