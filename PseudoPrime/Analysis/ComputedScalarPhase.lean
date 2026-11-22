/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalComputed
public import PseudoPrime.Analysis.IntegerIntervalPhaseCells
public import PseudoPrime.Analysis.IntegerIntervalScalarPhase
import Mathlib.Tactic.Linarith

/-! # Computed scalar phase cells without intermediate witness tables -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Computed intervals for the cosine, sine and critical-line phase quotient.
Fields real and imag enclose the trigonometric coordinates; quotient encloses
(cos(g*v)+2*g*sin(g*v))/(1/4+g^2). Field valid checks the radius and reciprocal
conditions. Soundness is conditional on valid=true and certified inputs,
rather than stored as an invariant in this computational record. -/
structure ScalarPhaseBounds where
  real : IntegerInterval
  imag : IntegerInterval
  quotient : IntegerInterval
  valid : Bool

/-- Propose outward integer endpoints for the reciprocal of an interval at
scale G. The candidate uses floor and ceiling integer divisions and is
accepted only through the existing reciprocal checker in the scalar cell. -/
def reciprocalCandidate (G : ℤ) (I : IntegerInterval) : IntegerInterval :=
  ⟨G ^ 2 / I.upper, -((-(G ^ 2)) / I.lower)⟩

/-- Check the displacement radius and reciprocal domain from A,V,W at scale G.
The center coordinates are certified analytically and do not enter these checks;
separating the guard avoids evaluating unused coordinate tables during validation. -/
def scalarPhaseDomainCheck (G : ℤ) (A V W : IntegerInterval) : Bool :=
  let D := (roundedProduct G A V).add W.neg
  let radius := max |D.lower| |D.upper|
  let error := -((-(radius ^ 2)) / (2 * G))
  let den := (roundedConstant G 1 4).add (roundedProduct G A A)
  let inv := reciprocalCandidate G den
  phaseRadiusCheck G radius error &&
    integerReciprocalCheck G den.lower den.upper inv.lower inv.upper

/-- Compute a continuous scalar phase cell from ordinate A, argument V,
center argument W and certified center coordinates C,S at scale G.
Rounded products, a quadratic phase remainder and a checked reciprocal
produce every intermediate interval internally, without a witness table.
The valid flag records the remaining executable domain and radius checks. -/
def computedScalarPhase (G : ℤ) (A V W C S : IntegerInterval) : ScalarPhaseBounds :=
  let D := (roundedProduct G A V).add W.neg
  let radius := max |D.lower| |D.upper|
  let error := -((-(radius ^ 2)) / (2 * G))
  let SD := roundedProduct G S D
  let CD := roundedProduct G C D
  let PC := (C.add SD.neg).widen error
  let PS := (S.add CD).widen error
  let Q := roundedConstant G 1 4
  let AA := roundedProduct G A A
  let AS := roundedProduct G A PS
  let den := Q.add AA
  let inv := reciprocalCandidate G den
  ⟨PC, PS, roundedProduct G (PC.add (AS.scale 2)) inv, scalarPhaseDomainCheck G A V W⟩

/-- The executable guard is independent of the certified center coordinates.
This equality lets finite validation reduce only the relevant domain arithmetic. -/
theorem computedScalarPhase_valid (G : ℤ) (A V W C S : IntegerInterval) :
    (computedScalarPhase G A V W C S).valid = scalarPhaseDomainCheck G A V W := by rfl

/-- An interval containing x at positive scale bounds its absolute value by
the larger absolute integer endpoint divided by the scale. This supplies
the uniform displacement radius for computed continuous phase cells. -/
theorem interval_abs_le {I : IntegerInterval} {G : ℤ} {x : ℝ} (hg : 0 < G) (hx : I.Contains G x) :
    |x| ≤ ((max |I.lower| |I.upper| : ℤ) : ℝ) / G := by
  have hg' : (0 : ℝ) < G := (Int.cast_pos (R := ℝ)).mpr hg
  have hl : -(max |I.lower| |I.upper|) ≤ I.lower :=
    (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
  have hu : I.upper ≤ max |I.lower| |I.upper| := (le_abs_self _).trans (le_max_right _ _)
  have hl' := div_le_div_of_nonneg_right ((Int.cast_le (R := ℝ)).mpr hl) hg'.le
  have hu' := div_le_div_of_nonneg_right ((Int.cast_le (R := ℝ)).mpr hu) hg'.le
  simp only [Int.cast_neg, neg_div] at hl'
  exact abs_le.mpr ⟨hl'.trans hx.1, hx.2.trans hu'⟩

/-- Successful computed-cell checks and real input containments certify the
cosine, sine and critical-line quotient at every g,v in the input boxes.
The proof composes rounded-product soundness, the sharp phase-cell error
and the existing scalar quotient theorem; no intermediate table is assumed. -/
theorem computedScalarPhase_sound {G : ℤ} {A V W C S : IntegerInterval} {g v c : ℝ}
    (hg : A.Contains G g) (hv : V.Contains G v) (hw : W.Contains G c)
    (hp : complexIntervalContains C S G (Complex.exp ((c : ℂ) * Complex.I)))
    (hc : (computedScalarPhase G A V W C S).valid = true) :
    (computedScalarPhase G A V W C S).real.Contains G (Real.cos (g * v)) ∧
      (computedScalarPhase G A V W C S).imag.Contains G (Real.sin (g * v)) ∧
      (computedScalarPhase G A V W C S).quotient.Contains G
        ((Real.cos (g * v) + 2 * g * Real.sin (g * v)) / ((1 / 4 : ℝ) + g ^ 2)) := by
  let D := (roundedProduct G A V).add W.neg
  let radius := max |D.lower| |D.upper|
  let error := -((-(radius ^ 2)) / (2 * G))
  let PC := (C.add (roundedProduct G S D).neg).widen error
  let PS := (S.add (roundedProduct G C D)).widen error
  let Q := roundedConstant G 1 4
  let AA := roundedProduct G A A
  let AS := roundedProduct G A PS
  let den := Q.add AA
  let inv := reciprocalCandidate G den
  let out := roundedProduct G (PC.add (AS.scale 2)) inv
  change
    PC.Contains G (Real.cos (g * v)) ∧
      PS.Contains G (Real.sin (g * v)) ∧
      out.Contains G ((Real.cos (g * v) + 2 * g * Real.sin (g * v)) / ((1 / 4 : ℝ) + g ^ 2))
  change
    (phaseRadiusCheck G radius error &&
        integerReciprocalCheck G den.lower den.upper inv.lower inv.upper) =
      true at hc
  have hchecks := Bool.and_eq_true_iff.mp hc
  have hG : 0 < G := (of_decide_eq_true hchecks.1).1
  have hd : D.Contains G (g * v - c) := by
    simpa only [sub_eq_add_neg] using
      IntegerInterval.add_contains (roundedProduct_contains hG hg hv)
        (IntegerInterval.neg_contains hw)
  have hphase :=
    phase_cell_radius_contains hp hd (roundedProduct_check G S D hG) (roundedProduct_check G C D hG)
      hchecks.1 (interval_abs_le hG hd)
  have hq := roundedConstant_contains (G := G) (p := 1) (d := 4) hG (by norm_num only)
  norm_num only [Int.cast_one, Int.cast_ofNat] at hq
  have hvalue :=
    scalar_phase_contains (AA := AA) (AS := AS) (Q := Q) (D := inv) (O := out) hg hphase hq
      (roundedProduct_check G A A hG) (roundedProduct_check G A PS hG) hchecks.2
      (roundedProduct_check G (PC.add (AS.scale 2)) inv hG)
  refine ⟨?_, ?_, hvalue⟩
  · simpa only [Complex.exp_ofReal_mul_I_re] using hphase.1
  · simpa only [Complex.exp_ofReal_mul_I_im] using hphase.2

/-- The rounded quadratic error satisfies the phase radius check for every positive scale. -/
private theorem phaseRadiusCandidate_check {G r : ℤ} (hg : 0 < G) (hr : 0 ≤ r) :
    phaseRadiusCheck G r (-((-(r ^ 2)) / (2 * G))) = true := by
  let e := -((-(r ^ 2)) / (2 * G))
  have ht :=
    round_corner (G := 2 * G) (l := r ^ 2) (u := r ^ 2) (x := r ^ 2) (mul_pos (by decide) hg) le_rfl
      le_rfl
  have hu : r ^ 2 ≤ e * (2 * G) := ht.2
  have he : 0 ≤ e := nonneg_of_mul_nonneg_left ((sq_nonneg r).trans hu) (mul_pos (by decide) hg)
  apply decide_eq_true
  refine ⟨hg, hr, he, ?_⟩
  nlinarith only [hu]

/-- For an ordered positive interval and positive scale, the computed reciprocal
passes its check. -/
theorem reciprocalCandidate_check {G : ℤ} {I : IntegerInterval} (hg : 0 < G) (ha : 0 < I.lower)
    (hab : I.lower ≤ I.upper) :
    integerReciprocalCheck G I.lower I.upper (reciprocalCandidate G I).lower
        (reciprocalCandidate G I).upper =
      true := by
  let l := G ^ 2 / I.upper
  let u := -((-(G ^ 2)) / I.lower)
  have hb : 0 < I.upper := ha.trans_le hab
  have hl : l * I.upper ≤ G ^ 2 := Int.ediv_mul_le _ hb.ne'
  have hu : G ^ 2 ≤ u * I.lower := by
    simpa only [u, neg_mul, neg_neg] using neg_le_neg (Int.ediv_mul_le (-(G ^ 2)) ha.ne')
  have hu0 : 0 ≤ u := nonneg_of_mul_nonneg_left ((sq_nonneg G).trans hu) ha
  have hlu : l ≤ u :=
    Int.le_of_mul_le_mul_right (hl.trans (hu.trans (mul_le_mul_of_nonneg_left hab hu0))) hb
  apply decide_eq_true
  refine ⟨hg, ha, hab, hlu, ?_, ?_⟩
  · simpa only [reciprocalCandidate, l, pow_two] using hl
  · simpa only [reciprocalCandidate, u, pow_two] using hu

/-- Rounded multiplication has ordered endpoints at every positive scale. -/
private theorem roundedProduct_order {G : ℤ} (hg : 0 < G) (I J : IntegerInterval) :
    (roundedProduct G I J).lower ≤ (roundedProduct G I J).upper := by
  have hc := of_decide_eq_true (roundedProduct_check G I J hg)
  exact Int.le_of_mul_le_mul_right (hc.2.1.1.trans hc.2.1.2) hg

/-- Rounding a rational constant with positive denominator gives ordered endpoints. -/
private theorem roundedConstant_order (G p d : ℤ) (hd : 0 < d) :
    (roundedConstant G p d).lower ≤ (roundedConstant G p d).upper := by
  have hc := round_corner (G := d) (l := p * G) (u := p * G) (x := p * G) hd le_rfl le_rfl
  exact Int.le_of_mul_le_mul_right (hc.1.trans hc.2) hd

/-- An ordered interval above the scale has a rounded square above the scale. -/
private theorem roundedSquare_lower_ge {G : ℤ} {A : IntegerInterval} (hg : 0 < G) (ha : G ≤ A.lower)
    (hab : A.lower ≤ A.upper) : G ≤ (roundedProduct G A A).lower := by
  have hb := ha.trans hab
  have hp (x y : ℤ) (hx : G ≤ x) (hy : G ≤ y) : G * G ≤ x * y :=
    mul_le_mul hx hy hg.le (hg.le.trans hx)
  change
    G ≤
      (min (min (A.lower * A.lower) (A.lower * A.upper))
          (min (A.upper * A.lower) (A.upper * A.upper))) /
        G
  exact
    (Int.le_ediv_iff_mul_le hg).mpr
      (le_min (le_min (hp _ _ ha ha) (hp _ _ ha hb)) (le_min (hp _ _ hb ha) (hp _ _ hb hb)))

/-- If an ordered ordinate interval lies above a positive scale, every argument
and center pass the scalar domain check. The proof discharges rounding and
reciprocal guards without expanding concrete phase tables. -/
theorem scalarPhaseDomainCheck_true {G : ℤ} {A V W : IntegerInterval} (hg : 0 < G)
    (ha : G ≤ A.lower) (hab : A.lower ≤ A.upper) : scalarPhaseDomainCheck G A V W = true := by
  let D := (roundedProduct G A V).add W.neg
  let radius := max |D.lower| |D.upper|
  let error := -((-(radius ^ 2)) / (2 * G))
  let Q := roundedConstant G 1 4
  let AA := roundedProduct G A A
  let den := Q.add AA
  let inv := reciprocalCandidate G den
  have hQ0 : 0 ≤ Q.lower := by
    change 0 ≤ (1 * G) / 4
    exact Int.ediv_nonneg (mul_nonneg (by decide) hg.le) (by decide)
  have hA0 : G ≤ AA.lower := roundedSquare_lower_ge hg ha hab
  have hpos : 0 < den.lower := by
    change 0 < Q.lower + AA.lower
    linarith only [hg, hQ0, hA0]
  have hord : den.lower ≤ den.upper :=
    add_le_add (roundedConstant_order G 1 4 (by decide)) (roundedProduct_order hg A A)
  change
    (phaseRadiusCheck G radius error &&
        integerReciprocalCheck G den.lower den.upper inv.lower inv.upper) =
      true
  exact
    Bool.and_eq_true_iff.mpr
      ⟨phaseRadiusCandidate_check hg ((abs_nonneg D.lower).trans (le_max_left _ _)),
        reciprocalCandidate_check hg hpos hord⟩

end PseudoPrime.Analysis
