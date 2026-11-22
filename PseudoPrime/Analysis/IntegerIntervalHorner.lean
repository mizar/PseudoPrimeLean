/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalComputed
public import PseudoPrime.Analysis.RationalHorner25
public import PseudoPrime.Analysis.IntegerIntervalPhase

/-! # Computed integer interval Horner phase enclosures -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Evaluate the phase Taylor polynomial by a real Horner recurrence.
The depth and denominator offset match the rational exponential recurrence. -/
noncomputable def realPhaseHorner (x : ℝ) : ℕ → ℕ → ℝ × ℝ
  | 0, _ => (1, 0)
  | n + 1, j =>
    let w := realPhaseHorner x n (j + 1)
    (1 - x / (j + 1) * w.2, x / (j + 1) * w.1)

/-- Compute integer interval bounds for the real phase Horner recurrence.
Every multiplication rounds outwards; no intermediate table or list indexing is used. -/
def intervalPhaseHorner (G : ℤ) (X : IntegerInterval) : ℕ → ℕ → IntegerInterval × IntegerInterval
  | 0, _ => (⟨G, G⟩, ⟨0, 0⟩)
  | n + 1, j =>
    let w := intervalPhaseHorner G X n (j + 1)
    let a := roundedProduct G X (roundedConstant G 1 (j + 1))
    ((IntegerInterval.mk G G).add (roundedProduct G a w.2).neg, roundedProduct G a w.1)

/-- At positive scale, Horner interval evaluation encloses both real coordinates.
Induction composes computed constant and product containment at every depth. -/
theorem intervalPhaseHorner_contains {G : ℤ} {X : IntegerInterval} {x : ℝ} (hg : 0 < G)
    (hx : X.Contains G x) (n j : ℕ) :
    (intervalPhaseHorner G X n j).1.Contains G (realPhaseHorner x n j).1 ∧
      (intervalPhaseHorner G X n j).2.Contains G (realPhaseHorner x n j).2 := by
  have hr : (0 : ℝ) < G := (Int.cast_pos (R := ℝ)).mpr hg
  have hone : (IntegerInterval.mk G G).Contains G 1 := by
    constructor <;> simp only [div_self (ne_of_gt hr), le_refl]
  have hzero : (IntegerInterval.mk 0 0).Contains G 0 := by
    constructor <;> simp only [Int.cast_zero, zero_div, le_refl]
  induction n generalizing j with
  | zero => exact ⟨hone, hzero⟩
  | succ n
    ih =>
    have hd : (0 : ℤ) < (j : ℤ) + 1 :=
      Int.add_pos_of_nonneg_of_pos (Int.natCast_nonneg j) Int.zero_lt_one
    have hc := roundedConstant_contains (p := 1) hg hd
    have ha := roundedProduct_contains hg hx hc
    have hw := ih (j + 1)
    have hl :=
      IntegerInterval.add_contains hone
        (IntegerInterval.neg_contains (roundedProduct_contains hg ha hw.2))
    have hu := roundedProduct_contains hg ha hw.1
    simpa only [intervalPhaseHorner, realPhaseHorner, Int.cast_one, Int.cast_add, Int.cast_natCast,
      one_div, div_eq_mul_inv, one_mul, sub_eq_add_neg] using And.intro hl hu

/-- Casting rational phase Horner coordinates agrees with the real recurrence.
Induction and ring identities avoid evaluating large rational polynomials at concrete phases. -/
theorem realPhaseHorner_cast (x : ℚ) (n j : ℕ) :
    realPhaseHorner (x : ℝ) n j =
      (((rationalExpHorner (0, x) n j).1 : ℝ), ((rationalExpHorner (0, x) n j).2 : ℝ)) := by
  induction n generalizing j with
  | zero => simp only [realPhaseHorner, rationalExpHorner, Rat.cast_one, Rat.cast_zero]
  | succ n
    ih =>
    simp only [realPhaseHorner, rationalExpHorner, rationalComplexAdd, rationalComplexScale,
      rationalComplexMul, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
      zero_mul, zero_add, zero_sub, Rat.cast_neg, ih]
    congr 1 <;> ring

/-- At positive scale, computed depth-24 intervals enclose the existing 25-term polynomial.
Use the generic cast identity and the fixed rational polynomial identity. -/
theorem intervalHorner25_contains {G : ℤ} {X : IntegerInterval} (x : ℚ) (hg : 0 < G)
    (hx : X.Contains G (x : ℝ)) :
    (intervalPhaseHorner G X 24 0).1.Contains G ((rationalPhaseTaylor x 25).1 : ℝ) ∧
      (intervalPhaseHorner G X 24 0).2.Contains G ((rationalPhaseTaylor x 25).2 : ℝ) := by
  have h := intervalPhaseHorner_contains hg hx 24 0
  rw [realPhaseHorner_cast, rational_horner25_poly] at h
  exact h

/-- For a small rational phase, widen the computed polynomial enclosure by the analytic error.
This contains the true complex exponential and feeds the existing squaring-chain interface. -/
theorem intervalHorner25_phase {G r : ℤ} {X : IntegerInterval} (q : ℚ) (hg : 0 < G)
    (hx : X.Contains G (q : ℝ)) (hd : |(q : ℝ)| ≤ 1 / 4) (hr : (1 / 2 ^ 120 : ℝ) ≤ (r : ℝ) / G) :
    complexIntervalContains ((intervalPhaseHorner G X 24 0).1.widen r)
      ((intervalPhaseHorner G X 24 0).2.widen r) G (Complex.exp ((q : ℂ) * Complex.I)) := by
  have hc := intervalHorner25_contains q hg hx
  have hp :
    complexIntervalContains (intervalPhaseHorner G X 24 0).1 (intervalPhaseHorner G X 24 0).2 G
      (∑ m ∈ Finset.range 25, (Complex.I * (q : ℂ)) ^ m / (m.factorial : ℂ)) := by
    rw [← rationalPhaseTaylor_cast]
    exact hc
  have ht :
    complexIntervalContains (intervalPhaseHorner G X 24 0).1 (intervalPhaseHorner G X 24 0).2 G
      (∑ m ∈ Finset.range 25, (((q : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) := by
    simpa only [Complex.ofReal_ratCast, mul_comm] using hp
  simpa only [Complex.ofReal_ratCast] using phase_taylor24_contains hd ht hr

/-- Evaluate one Horner coordinate by alternating real and imaginary dependencies.
Each branch has one recursive call, avoiding duplicated reduction of pairs. -/
def intervalHornerCoord (G : ℤ) (X : IntegerInterval) : ℕ → ℕ → Bool → IntegerInterval
  | 0, _, b => if b then ⟨0, 0⟩ else ⟨G, G⟩
  | n + 1, j, b =>
    let a := roundedProduct G X (roundedConstant G 1 (j + 1))
    let w := roundedProduct G a (intervalHornerCoord G X n (j + 1) (!b))
    if b then w else (IntegerInterval.mk G G).add w.neg

/-- The alternating coordinate computation equals the compositional pair recurrence.
Induction supplies a linear evaluation interface with the same certified polynomial. -/
theorem intervalHornerCoord_eq (G : ℤ) (X : IntegerInterval) (n j : ℕ) :
    intervalHornerCoord G X n j false = (intervalPhaseHorner G X n j).1 ∧
      intervalHornerCoord G X n j true = (intervalPhaseHorner G X n j).2 := by
  induction n generalizing j with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h := ih (j + 1)
    simp only [intervalHornerCoord, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      h.1, h.2, intervalPhaseHorner]
    exact ⟨True.intro, True.intro⟩

/-- Checked Horner output products contain one step of the real and imaginary update.
The real coordinate uses the reflected product interval around one. -/
theorem hornerStep_contains {G : ℤ} {A R I S T : IntegerInterval} {a u v : ℝ} (ha : A.Contains G a)
    (hr : R.Contains G u) (hi : I.Contains G v)
    (hs : integerProductCheck G A.lower A.upper I.lower I.upper (G - S.upper) (G - S.lower) = true)
    (ht : integerProductCheck G A.lower A.upper R.lower R.upper T.lower T.upper = true)
    (hg : 0 < G) : S.Contains G (1 - a * v) ∧ T.Contains G (a * u) := by
  have h := integerProductCheck_sound hs ha hi
  have g : (0 : ℝ) < G := (Int.cast_pos (R := ℝ)).mpr hg
  have hh : S.Contains G (1 - a * v) := by
    constructor
    · have he := h.2
      simp only [Int.cast_sub, sub_div, div_self (ne_of_gt g)] at he
      linarith only [he]
    · have he := h.1
      simp only [Int.cast_sub, sub_div, div_self (ne_of_gt g)] at he
      linarith only [he]
  exact ⟨hh, integerProductCheck_sound ht ha hr⟩

/-- Three finite integer checks certify one real Horner recurrence step.
The previous coordinate enclosure and rational factor checks compose without nested evaluation. -/
theorem hornerStep_real {G p d : ℤ} {A R I S T : IntegerInterval} (n j : ℕ) (hg : 0 < G)
    (ha : integerConstantCheck G p (d * ((j : ℤ) + 1)) A.lower A.upper = true)
    (hw :
      R.Contains G (realPhaseHorner ((p : ℝ) / d) n (j + 1)).1 ∧
        I.Contains G (realPhaseHorner ((p : ℝ) / d) n (j + 1)).2)
    (hs : integerProductCheck G A.lower A.upper I.lower I.upper (G - S.upper) (G - S.lower) = true)
    (ht : integerProductCheck G A.lower A.upper R.lower R.upper T.lower T.upper = true) :
    S.Contains G (realPhaseHorner ((p : ℝ) / d) (n + 1) j).1 ∧
      T.Contains G (realPhaseHorner ((p : ℝ) / d) (n + 1) j).2 := by
  have hh : A.Contains G (((p : ℝ) / d) / (j + 1)) := by
    simpa only [IntegerInterval.Contains, Int.cast_mul, Int.cast_add, Int.cast_natCast,
      Int.cast_one, div_div] using integerConstantCheck_sound ha
  exact hornerStep_contains hh hw.1 hw.2 hs ht hg

/-- Any certified depth-24 real Horner enclosure contains the existing complex Taylor sum.
The cast and fixed polynomial identities avoid concrete rational evaluation. -/
theorem horner25_poly_contains {G : ℤ} {R I : IntegerInterval} (q : ℚ)
    (h :
      R.Contains G (realPhaseHorner (q : ℝ) 24 0).1 ∧
        I.Contains G (realPhaseHorner (q : ℝ) 24 0).2) :
    complexIntervalContains R I G
      (∑ m ∈ Finset.range 25, (Complex.I * (q : ℂ)) ^ m / (m.factorial : ℂ)) := by
  rw [realPhaseHorner_cast, rational_horner25_poly] at h
  rw [← rationalPhaseTaylor_cast]
  exact h

/-- A certified small-angle Horner enclosure, widened by analytic error, contains the phase.
This applies to both computed intervals and independently checked stage witnesses. -/
theorem horner25_phase_contains {G r : ℤ} {R I : IntegerInterval} (q : ℚ)
    (h :
      R.Contains G (realPhaseHorner (q : ℝ) 24 0).1 ∧ I.Contains G (realPhaseHorner (q : ℝ) 24 0).2)
    (hd : |(q : ℝ)| ≤ 1 / 4) (hr : (1 / 2 ^ 120 : ℝ) ≤ (r : ℝ) / G) :
    complexIntervalContains (R.widen r) (I.widen r) G (Complex.exp ((q : ℂ) * Complex.I)) := by
  have hp := horner25_poly_contains q h
  have ht :
    complexIntervalContains R I G
      (∑ m ∈ Finset.range 25, (((q : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) := by
    simpa only [Complex.ofReal_ratCast, mul_comm] using hp
  simpa only [Complex.ofReal_ratCast] using phase_taylor24_contains hd ht hr

end PseudoPrime.Analysis
