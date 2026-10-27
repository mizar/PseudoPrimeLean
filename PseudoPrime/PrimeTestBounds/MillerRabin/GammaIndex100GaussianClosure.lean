/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaKernel
public import PseudoPrime.LLS.RelativeGaussianSubgroupComparison
public import PseudoPrime.LLS.GammaNonOneRefinedNumerics
public import PseudoPrime.PrimeTest.MillerRabin.SignSubgroupIndex

/-! # Gamma index-100 cutoff and its index-four Gaussian closure -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The positive root for the index-100 Gamma branch. It solves
`(91/100) r - μ L - 1057/2500 - ((7/6)L+61)/r = 0`, where
`μ = 11783423/25000000`. The root supplies the analytic radius for the
50000-term signed-prefix witness bound on `L ≥ 330`. -/
noncomputable def gammaIndex100Radius (L : ℝ) : ℝ :=
  ((11783423 / 25000000 : ℝ) * L + 1057 / 2500 +
      Real.sqrt
        (((11783423 / 25000000 : ℝ) * L + 1057 / 2500) ^ 2 +
          4 * (91 / 100 : ℝ) * ((7 / 6 : ℝ) * L + 61))) /
    (2 * (91 / 100 : ℝ))

/-- The public index-100 Gamma witness bound associated with `gammaIndex100Radius`. -/
noncomputable def gammaIndex100Bound (L : ℝ) : ℝ :=
  (99 / 40 : ℝ) * (gammaIndex100Radius L) ^ 2

/-- The radius attached to a retained Gamma prefix of lower mass `C`. Its
positive root solves the signed index-100 budget with both the prefix credit
and the pole term retained. -/
noncomputable def gammaPrefix100Radius (L C : ℝ) : ℝ :=
  ((11783423 / 25000000 : ℝ) * L + (591 / 50 - 2 * C) +
      Real.sqrt
        (((11783423 / 25000000 : ℝ) * L + (591 / 50 - 2 * C)) ^ 2 +
          4 * (91 / 100 : ℝ) * ((7 / 6 : ℝ) * L + 61))) /
    (2 * (91 / 100 : ℝ))

/-- The two prefix choices for the improved index-100 Gamma envelope. The
maximum preserves each prefix's own applicability threshold. -/
noncomputable def gammaIndex100PrefixUpper (L : ℝ) : ℝ :=
  min (max 1000 ((99 / 40 : ℝ) * gammaPrefix100Radius L (203 / 50) ^ 2))
    (max 50000 ((99 / 40 : ℝ) * gammaPrefix100Radius L (28493 / 5000) ^ 2))

/-- For nonnegative prefix loss and `L ≥ 240`, the retained-prefix radius is
positive and satisfies its defining quadratic equation. -/
theorem gammaPrefix100Radius_properties {L C : ℝ} (hL : 240 ≤ L) (hD : 0 ≤ 591 / 50 - 2 * C) :
    0 < gammaPrefix100Radius L C ∧
      (91 / 100 : ℝ) * (gammaPrefix100Radius L C) ^ 2 -
          ((11783423 / 25000000 : ℝ) * L + (591 / 50 - 2 * C)) * gammaPrefix100Radius L C -
          ((7 / 6 : ℝ) * L + 61) =
        0 := by
  let A : ℝ := (11783423 / 25000000 : ℝ) * L + (591 / 50 - 2 * C)
  let S : ℝ := (7 / 6 : ℝ) * L + 61
  let a : ℝ := 91 / 100
  have hLpos : 0 < L := by linarith only [hL]
  have hA : 0 < A := by
    dsimp only [A]
    exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num only) hLpos) hD
  have hS : 0 < S := by
    dsimp only [S]
    exact add_pos (mul_pos (by norm_num only) hLpos) (by norm_num only)
  have ha : 0 < a := by norm_num only [a]
  have hrad : 0 ≤ A ^ 2 + 4 * a * S :=
    add_nonneg (sq_nonneg A) (mul_nonneg (by norm_num only [a]) hS.le)
  have hs := Real.sq_sqrt hrad
  have hden : (2 * a : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num only) ha)
  have hnum : 2 * a * gammaPrefix100Radius L C = A + Real.sqrt (A ^ 2 + 4 * a * S) := by
    dsimp only [gammaPrefix100Radius, A, S, a]
    field_simp [hden]
  have hroot : (2 * a * gammaPrefix100Radius L C - A) ^ 2 = A ^ 2 + 4 * a * S := by
    rw [hnum]
    nlinarith only [hs]
  have hpoly :
    4 * a * (a * (gammaPrefix100Radius L C) ^ 2 - A * gammaPrefix100Radius L C - S) =
      (2 * a * gammaPrefix100Radius L C - A) ^ 2 - (A ^ 2 + 4 * a * S) := by
    ring
  have hzero :
    4 * a * (a * (gammaPrefix100Radius L C) ^ 2 - A * gammaPrefix100Radius L C - S) = 0 := by
    rw [hroot] at hpoly
    simpa only [sub_self] using hpoly
  have hquad : a * (gammaPrefix100Radius L C) ^ 2 - A * gammaPrefix100Radius L C - S = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (mul_pos (by norm_num only) ha))
  have hpos : 0 < gammaPrefix100Radius L C := by
    change 0 < (A + Real.sqrt (A ^ 2 + 4 * a * S)) / (2 * a)
    exact div_pos (add_pos_of_pos_of_nonneg hA (Real.sqrt_nonneg _)) (mul_pos (by norm_num only) ha)
  constructor
  · exact hpos
  · simpa only [A, S, a] using hquad

/-- The retained-prefix root makes the normalized index-100 Gamma margin
exactly zero. -/
theorem gammaPrefix100Radius_budget_eq {L C : ℝ} (hL : 240 ≤ L) (hD : 0 ≤ 591 / 50 - 2 * C) :
    (91 / 100 : ℝ) * gammaPrefix100Radius L C - (11783423 / 25000000 : ℝ) * L - (591 / 50 - 2 * C) -
        ((7 / 6 : ℝ) * L + 61) / gammaPrefix100Radius L C =
      0 := by
  have hp := gammaPrefix100Radius_properties hL hD
  have hr := hp.1
  have hq := hp.2
  field_simp [hr.ne']
  nlinarith only [hq]

/-- The retained-prefix radius grows at least as fast as `L / 2`. The
linear part of the quadratic formula already gives this lower bound. -/
theorem gammaPrefix100Radius_lower_half {L C : ℝ} (hL : 240 ≤ L) (hD : 0 ≤ 591 / 50 - 2 * C) :
    L / 2 ≤ gammaPrefix100Radius L C := by
  let A : ℝ := (11783423 / 25000000 : ℝ) * L + (591 / 50 - 2 * C)
  let S : ℝ := (7 / 6 : ℝ) * L + 61
  let a : ℝ := 91 / 100
  have hLpos : 0 < L := by linarith only [hL]
  have hA : 0 < A := by
    dsimp only [A]
    exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num only) hLpos) hD
  have hS : 0 < S := by
    dsimp only [S]
    exact add_pos (mul_pos (by norm_num only) hLpos) (by norm_num only)
  have ha : 0 < a := by norm_num only [a]
  have hsqrt : A ≤ Real.sqrt (A ^ 2 + 4 * a * S) := by
    have hterm : 0 ≤ 4 * a * S := mul_nonneg (mul_nonneg (by norm_num only) ha.le) hS.le
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hterm]
  have hAlinear : a * (L / 2) ≤ A := by
    dsimp only [A, a]
    nlinarith only [hL, hD]
  have hden : 0 < 2 * a := mul_pos (by norm_num only) ha
  unfold gammaPrefix100Radius
  apply (le_div_iff₀ hden).2
  dsimp only [A, S, a] at hsqrt hAlinear
  nlinarith only [hsqrt, hAlinear]

/-- For `L ≥ 330`, the Gamma radius is positive and satisfies its defining
quadratic equation. This records the positive-root choice used by the budget. -/
theorem gammaIndex100Radius_properties {L : ℝ} (hL : 330 ≤ L) :
    0 < gammaIndex100Radius L ∧
      (91 / 100 : ℝ) * (gammaIndex100Radius L) ^ 2 -
          ((11783423 / 25000000 : ℝ) * L + 1057 / 2500) * gammaIndex100Radius L -
          ((7 / 6 : ℝ) * L + 61) =
        0 := by
  let A : ℝ := (11783423 / 25000000 : ℝ) * L + 1057 / 2500
  let S : ℝ := (7 / 6 : ℝ) * L + 61
  let a : ℝ := 91 / 100
  have hLpos : 0 < L := by linarith only [hL]
  have hmu : 0 < (11783423 / 25000000 : ℝ) := by norm_num only
  have hA : 0 < A := by
    dsimp only [A]
    exact add_pos (mul_pos hmu hLpos) (by norm_num only)
  have hS : 0 < S := by
    dsimp only [S]
    exact add_pos (mul_pos (by norm_num only) hLpos) (by norm_num only)
  have ha : 0 < a := by norm_num only [a]
  have hrad : 0 ≤ A ^ 2 + 4 * a * S :=
    add_nonneg (sq_nonneg A) (mul_nonneg (by norm_num only [a]) hS.le)
  have hs := Real.sq_sqrt hrad
  have hden : (2 * a : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num only) ha)
  have hfac : (4 * a : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num only) ha)
  have hnum : 2 * a * gammaIndex100Radius L = A + Real.sqrt (A ^ 2 + 4 * a * S) := by
    dsimp only [gammaIndex100Radius, A, S, a]
    field_simp [hden]
  have hroot : (2 * a * gammaIndex100Radius L - A) ^ 2 = A ^ 2 + 4 * a * S := by
    rw [hnum]
    nlinarith only [hs]
  have hpoly :
    4 * a * (a * (gammaIndex100Radius L) ^ 2 - A * gammaIndex100Radius L - S) =
      (2 * a * gammaIndex100Radius L - A) ^ 2 - (A ^ 2 + 4 * a * S) := by
    ring
  have hzero : 4 * a * (a * (gammaIndex100Radius L) ^ 2 - A * gammaIndex100Radius L - S) = 0 := by
    rw [hroot] at hpoly
    simpa only [sub_self] using hpoly
  have hquad : a * (gammaIndex100Radius L) ^ 2 - A * gammaIndex100Radius L - S = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hfac
  have hpos : 0 < gammaIndex100Radius L := by
    change 0 < (A + Real.sqrt (A ^ 2 + 4 * a * S)) / (2 * a)
    exact div_pos (add_pos_of_pos_of_nonneg hA (Real.sqrt_nonneg _)) (mul_pos (by norm_num only) ha)
  constructor
  · exact hpos
  · simpa only [A, S, a] using hquad

/-- The chosen root makes the normalized index-100 Gamma budget margin zero. -/
theorem gammaIndex100Radius_budget_eq {L : ℝ} (hL : 330 ≤ L) :
    (91 / 100 : ℝ) * gammaIndex100Radius L - (11783423 / 25000000 : ℝ) * L - 1057 / 2500 -
        ((7 / 6 : ℝ) * L + 61) / gammaIndex100Radius L =
      0 := by
  have hp := gammaIndex100Radius_properties hL
  have hr := hp.1
  have hq := hp.2
  field_simp [hr.ne']
  nlinarith only [hq]

/-- For `L ≥ 330`, the index-100 radius lies between `517L/1000` and
`11L/20`. These rational slopes leave room for the scaled `21/10` Gaussian
radius used in the uniform Korselt triple branch. -/
theorem gammaIndex100Radius_linear_bounds {L : ℝ} (hL : 330 ≤ L) :
    (517 / 1000 : ℝ) * L ≤ gammaIndex100Radius L ∧ gammaIndex100Radius L ≤ (11 / 20 : ℝ) * L := by
  have hS : 0 ≤ (7 / 6 : ℝ) * L + 61 := by nlinarith only [hL]
  have hrootlo :
    (11783423 / 25000000 : ℝ) * L + 1057 / 2500 ≤
      Real.sqrt
        (((11783423 / 25000000 : ℝ) * L + 1057 / 2500) ^ 2 +
          4 * (91 / 100 : ℝ) * ((7 / 6 : ℝ) * L + 61)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hS]
  have hlo : (517 / 1000 : ℝ) * L ≤ gammaIndex100Radius L := by
    unfold gammaIndex100Radius
    have hden : 0 < 2 * (91 / 100 : ℝ) := by norm_num only
    apply (le_div_iff₀ hden).2
    nlinarith only [hrootlo, hL]
  have hA' :
    0 ≤
      2 * (91 / 100 : ℝ) * ((11 / 20 : ℝ) * L) - ((11783423 / 25000000 : ℝ) * L + 1057 / 2500) := by
    nlinarith only [hL]
  have hrootup :
    Real.sqrt
        (((11783423 / 25000000 : ℝ) * L + 1057 / 2500) ^ 2 +
          4 * (91 / 100 : ℝ) * ((7 / 6 : ℝ) * L + 61)) ≤
      2 * (91 / 100 : ℝ) * ((11 / 20 : ℝ) * L) - ((11783423 / 25000000 : ℝ) * L + 1057 / 2500) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact hA'
    · nlinarith only [hL, sq_nonneg (L - 330)]
  have hup : gammaIndex100Radius L ≤ (11 / 20 : ℝ) * L := by
    unfold gammaIndex100Radius
    have hden : 0 < 2 * (91 / 100 : ℝ) := by norm_num only
    apply (div_le_iff₀ hden).2
    nlinarith only [hrootup]
  exact ⟨hlo, hup⟩

/-- Gaussian radius whose `21/10` cutoff equals the Gamma index-100 bound. -/
noncomputable def gammaIndex100GaussianRadius (L : ℝ) : ℝ :=
  Real.sqrt (33 / 28 : ℝ) * gammaIndex100Radius L

/-- The positive square-root radius for the index-four Gaussian branch with
the 1000-prefix residual budget 29. Its square solves the analysis13 §4.2
equation with the existing cutoff `21/10`. -/
noncomputable def gammaIndex100GaussianTripleRadius29 (L : ℝ) : ℝ :=
  (((4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10) +
        Real.sqrt
          (((4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10)) ^ 2 +
            4 * ((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) *
              ((161 / 600 : ℝ) * L + 29))) /
      (2 * ((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3))) ^
    2

/-- The internal cutoff from the residual-29 Gaussian radius. -/
noncomputable def gammaIndex100GaussianTripleBound29 (L : ℝ) : ℝ :=
  (21 / 10 : ℝ) * (gammaIndex100GaussianTripleRadius29 L) ^ 2

/-- The scaled `21/10` Gaussian radius lies between `14L/25` and `3L/5`
throughout the index-100 Gamma domain. -/
theorem gammaIndex100GaussianRadius_linear_bounds {L : ℝ} (hL : 330 ≤ L) :
    (14 / 25 : ℝ) * L ≤ gammaIndex100GaussianRadius L ∧
      gammaIndex100GaussianRadius L ≤ (3 / 5 : ℝ) * L := by
  let q : ℝ := Real.sqrt (33 / 28)
  have hqlo : (1085 / 1000 : ℝ) ≤ q := by
    dsimp only [q]
    apply Real.le_sqrt_of_sq_le
    norm_num only
  have hqhi : q ≤ (109 / 100 : ℝ) := by
    dsimp only [q]
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num only
    · norm_num only
  have hLpos : 0 < L := by linarith only [hL]
  have hrange := gammaIndex100Radius_linear_bounds hL
  have hqpos : 0 ≤ q := Real.sqrt_nonneg _
  have hrpos : 0 < gammaIndex100Radius L := (gammaIndex100Radius_properties hL).1
  have hlow1 := mul_le_mul_of_nonneg_left hrange.1 hqpos
  have hlow2 :=
    mul_le_mul_of_nonneg_right hqlo (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 517 / 1000) hLpos.le)
  have hupper1 := mul_le_mul_of_nonneg_left hrange.2 hqpos
  have hupper2 := mul_le_mul_of_nonneg_right hqhi hrpos.le
  dsimp only [gammaIndex100GaussianRadius, q]
  constructor
  · nlinarith only [hlow1, hlow2, hL]
  · nlinarith only [hupper1, hupper2, hL]

/-- For `L ≥ 200`, the positive root defining the index-four residual-29
radius is positive and satisfies its quadratic budget equation. -/
theorem gammaIndex100GaussianTripleRadius29_properties {L : ℝ} (hL : 200 ≤ L) :
    0 < gammaIndex100GaussianTripleRadius29 L ∧
      ((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) * gammaIndex100GaussianTripleRadius29 L -
          (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10) *
            Real.sqrt (gammaIndex100GaussianTripleRadius29 L) -
          (161 / 600 : ℝ) * L -
          29 =
        0 := by
  let d : ℝ := (4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3
  let b : ℝ := (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10)
  let A : ℝ := (161 / 600 : ℝ) * L + 29
  let s : ℝ := (b + Real.sqrt (b ^ 2 + 4 * d * A)) / (2 * d)
  let R : ℝ := gammaIndex100GaussianTripleRadius29 L
  have hd : 0 < d := by norm_num only [d]
  have hb : 0 < b := by norm_num only [b]
  have hA : 0 < A := by
    dsimp only [A]
    nlinarith only [hL]
  have hrad : 0 ≤ b ^ 2 + 4 * d * A :=
    add_nonneg (sq_nonneg b) (mul_nonneg (mul_nonneg (by norm_num only) hd.le) hA.le)
  have hsqrt := Real.sq_sqrt hrad
  have hden : 2 * d ≠ 0 := ne_of_gt (mul_pos (by norm_num only) hd)
  have hnum : 2 * d * s = b + Real.sqrt (b ^ 2 + 4 * d * A) := by
    dsimp only [s]
    field_simp [hden]
  have hroot : (2 * d * s - b) ^ 2 = b ^ 2 + 4 * d * A := by
    rw [hnum]
    nlinarith only [hsqrt]
  have hpoly : 4 * d * (d * s ^ 2 - b * s - A) = (2 * d * s - b) ^ 2 - (b ^ 2 + 4 * d * A) := by
    ring
  have hzero : 4 * d * (d * s ^ 2 - b * s - A) = 0 := by
    rw [hroot] at hpoly
    simpa only [sub_self] using hpoly
  have hquad : d * s ^ 2 - b * s - A = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (mul_pos (by norm_num only) hd))
  have hspos : 0 < s := by
    dsimp only [s]
    exact div_pos (add_pos_of_pos_of_nonneg hb (Real.sqrt_nonneg _)) (mul_pos (by norm_num only) hd)
  have hR : R = s ^ 2 := by rfl
  have hRsqrt : Real.sqrt R = s := by rw [hR, Real.sqrt_sq hspos.le]
  constructor
  · change 0 < R
    rw [hR]
    positivity
  · change d * R - b * Real.sqrt R - (161 / 600 : ℝ) * L - 29 = 0
    rw [hR, Real.sqrt_sq hspos.le]
    dsimp only [d, b, A] at hquad ⊢
    nlinarith only [hquad]

/-- The residual-29 radius is at least `9L/25+50` from `L ≥ 200` onward.
Use the root equation and monotonicity of its quadratic in the square root. -/
theorem gammaIndex100GaussianTripleRadius29_lower {L : ℝ} (hL : 200 ≤ L) :
    (9 / 25 : ℝ) * L + 50 ≤ gammaIndex100GaussianTripleRadius29 L := by
  let R := gammaIndex100GaussianTripleRadius29 L
  let s := Real.sqrt R
  let d : ℝ := (4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3
  let b : ℝ := (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10)
  let T : ℝ := (9 / 25 : ℝ) * L + 50
  have hprops := gammaIndex100GaussianTripleRadius29_properties hL
  have hRpos : 0 < R := hprops.1
  have hspos : 0 < s := by
    dsimp only [s]; exact Real.sqrt_pos.2 hRpos
  have hsR : s ^ 2 = R := by
    dsimp only [s]; exact Real.sq_sqrt hRpos.le
  have hRsqrt : Real.sqrt R = s := by rfl
  have hroot : d * R - b * Real.sqrt R - (161 / 600 : ℝ) * L - 29 = 0 := by
    dsimp only [d, b, R]
    exact hprops.2
  have hsquad : d * s ^ 2 - b * s - (161 / 600 : ℝ) * L - 29 = 0 := by
    rw [← hsR] at hroot
    rw [Real.sqrt_sq hspos.le] at hroot
    exact hroot
  have hT : 121 ≤ T := by
    dsimp only [T]; nlinarith only [hL]
  have hTroot : 11 ≤ Real.sqrt T := Real.le_sqrt_of_sq_le (by nlinarith only [hT])
  have hsroot : 11 ≤ s := by
    by_contra hnot
    have hslt : s < 11 := lt_of_not_ge hnot
    have hzero := hsquad
    have htest : d * (11 : ℝ) ^ 2 - b * 11 - (161 / 600 : ℝ) * L - 29 < 0 := by
      norm_num only [d, b]
      nlinarith only [hL]
    have hfac : 0 < d * (11 + s) - b := by
      norm_num only [d, b]
      nlinarith only [hspos, hslt]
    have hfactor :
      (d * 11 ^ 2 - b * 11 - (161 / 600 : ℝ) * L - 29) -
          (d * s ^ 2 - b * s - (161 / 600 : ℝ) * L - 29) =
        (11 - s) * (d * (11 + s) - b) := by
      ring
    rw [hzero] at hfactor
    have h11s : 0 < 11 - s := by linarith only [hslt]
    have hpositive := mul_pos h11s hfac
    have hfactor' :
      d * 11 ^ 2 - b * 11 - (161 / 600 : ℝ) * L - 29 = (11 - s) * (d * (11 + s) - b) := by
      simpa only [sub_zero] using hfactor
    have htestpos : 0 < d * 11 ^ 2 - b * 11 - (161 / 600 : ℝ) * L - 29 := by
      rw [hfactor']
      exact hpositive
    exact lt_asymm htestpos htest
  have hTineq : d * T - b * Real.sqrt T - (161 / 600 : ℝ) * L - 29 ≤ 0 := by
    dsimp only [d, b, T]
    norm_num only
    nlinarith only [hL, hTroot]
  by_contra hnot
  have hRT : R < T := lt_of_not_ge hnot
  have hrootlt : s < Real.sqrt T := by
    apply Real.sqrt_lt_sqrt
    · exact hRpos.le
    · dsimp only [R, T] at hRT ⊢
      exact hRT
  have hfactor : 0 < d * (Real.sqrt T + s) - b := by
    norm_num only [d, b]
    nlinarith only [hTroot, hsroot]
  have hdifference :
    (d * T - b * Real.sqrt T - (161 / 600 : ℝ) * L - 29) -
        (d * R - b * s - (161 / 600 : ℝ) * L - 29) =
      (Real.sqrt T - s) * (d * (Real.sqrt T + s) - b) := by
    have hR : R = s ^ 2 := by
      dsimp only [s]; exact (Real.sq_sqrt hRpos.le).symm
    rw [hR]
    have hT' : T = (Real.sqrt T) ^ 2 := (Real.sq_sqrt (by linarith only [hT] : 0 ≤ T)).symm
    rw [hT']
    rw [Real.sqrt_sq (Real.sqrt_nonneg T)]
    ring
  have hsqrtgap : 0 < Real.sqrt T - s := sub_pos.mpr hrootlt
  have hpositive := mul_pos hsqrtgap hfactor
  have hzero : d * R - b * s - (161 / 600 : ℝ) * L - 29 = 0 := by
    rw [hRsqrt] at hroot
    exact hroot
  have hdiffpos :
    0 <
      (d * T - b * Real.sqrt T - (161 / 600 : ℝ) * L - 29) -
        (d * R - b * s - (161 / 600 : ℝ) * L - 29) := by
    rw [hdifference]
    exact hpositive
  have hTpositive : 0 < d * T - b * Real.sqrt T - (161 / 600 : ℝ) * L - 29 := by
    rw [hzero, sub_zero] at hdiffpos
    exact hdiffpos
  exact (not_lt_of_ge hTineq) hTpositive

/-- On the overlap `240 ≤ L ≤ 270`, the residual-29 Gaussian radius is at
most 153. This keeps its cutoff below the applicability threshold of the
50000-prefix Gamma branch. -/
theorem gammaIndex100GaussianTripleRadius29_le_153 {L : ℝ} (hL : 240 ≤ L) (hU : L ≤ 270) :
    gammaIndex100GaussianTripleRadius29 L ≤ 153 := by
  let R := gammaIndex100GaussianTripleRadius29 L
  let s := Real.sqrt R
  let d : ℝ := (4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3
  let b : ℝ := (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10)
  let c : ℝ := 161 / 600
  have hprops := gammaIndex100GaussianTripleRadius29_properties (by linarith only [hL])
  have hRpos : 0 < R := by
    dsimp only [R]; exact hprops.1
  have hspos : 0 < s := by
    dsimp only [s]; exact Real.sqrt_pos.2 hRpos
  have hsR : s ^ 2 = R := by
    dsimp only [s]; exact Real.sq_sqrt hRpos.le
  have hroot : d * R - b * s - c * L - 29 = 0 := by
    have h := hprops.2
    change d * R - b * Real.sqrt R - c * L - 29 = 0 at h
    rw [show Real.sqrt R = s by rfl] at h
    exact h
  have htlo : 12 ≤ Real.sqrt (153 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num only)
  have hthi : Real.sqrt (153 : ℝ) ≤ 25 / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num only
    · norm_num only
  have htarget : c * L + 29 < d * 153 - b * Real.sqrt (153 : ℝ) := by
    dsimp only [c, d, b]
    have hanchor :
      (161 / 600 : ℝ) * 270 + 29 <
        ((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) * 153 -
          (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10) * (25 / 2) := by
      norm_num only
    nlinarith only [hU, hthi, hanchor]
  by_contra hnot
  have hbad : 153 < R := by
    dsimp only [R] at hnot ⊢; exact lt_of_not_ge hnot
  have hrootlt : Real.sqrt (153 : ℝ) < s := by
    apply Real.sqrt_lt_sqrt (by norm_num only)
    dsimp only [s, R] at hbad ⊢
    exact hbad
  have hfactor : 0 < d * (s + Real.sqrt (153 : ℝ)) - b := by
    dsimp only [d, b]
    nlinarith only [htlo, hrootlt]
  have hdiff :
    (d * R - b * s) - (d * 153 - b * Real.sqrt (153 : ℝ)) =
      (s - Real.sqrt (153 : ℝ)) * (d * (s + Real.sqrt (153 : ℝ)) - b) := by
    have hsq : (153 : ℝ) = Real.sqrt (153 : ℝ) ^ 2 := (Real.sq_sqrt (by norm_num only)).symm
    have hdT : d * 153 = d * Real.sqrt (153 : ℝ) ^ 2 := congrArg (fun x : ℝ => d * x) hsq
    rw [← hsR]
    calc
      _ = d * s ^ 2 - b * s - d * 153 + b * Real.sqrt (153 : ℝ) := by ring
      _ = d * (s ^ 2 - Real.sqrt (153 : ℝ) ^ 2) - b * (s - Real.sqrt (153 : ℝ)) := by
        rw [hdT]; ring
      _ = (s - Real.sqrt (153 : ℝ)) * (d * (s + Real.sqrt (153 : ℝ)) - b) := by ring
  have hstrict : d * R - b * s > d * 153 - b * Real.sqrt (153 : ℝ) := by
    have hdiffpos : 0 < (d * R - b * s) - (d * 153 - b * Real.sqrt (153 : ℝ)) := by
      rw [hdiff]
      exact mul_pos (sub_pos.mpr hrootlt) hfactor
    linarith only [hdiffpos]
  have hLt : d * R - b * s < d * 153 - b * Real.sqrt (153 : ℝ) := by
    have hroot' : d * R - b * s = c * L + 29 := by linarith only [hroot]
    rw [hroot']
    exact htarget
  exact lt_asymm hLt hstrict

/-- The 1000-prefix Gamma radius is at least `(μ/a)L+6` from its own
starting scale onward. The affine candidate lies below the positive quadratic
root by an exact rational budget check. -/
theorem gammaPrefix100Radius_lower_mu_six {L : ℝ} (hL : 240 ≤ L) :
    ((11783423 / 25000000 : ℝ) / (91 / 100)) * L + 6 ≤ gammaPrefix100Radius L (203 / 50) := by
  let μ : ℝ := 11783423 / 25000000
  let a : ℝ := 91 / 100
  let D : ℝ := 591 / 50 - 2 * (203 / 50)
  let S : ℝ := (7 / 6 : ℝ) * L + 61
  let r := gammaPrefix100Radius L (203 / 50)
  let T := (μ / a) * L + 6
  have hD : 0 ≤ (591 / 50 : ℝ) - 2 * (203 / 50) := by norm_num only
  have hprop := gammaPrefix100Radius_properties hL hD
  have hrpos : 0 < r := by
    dsimp only [r]; exact hprop.1
  have hquad : a * r ^ 2 - (μ * L + D) * r - S = 0 := by
    have h := hprop.2
    change a * r ^ 2 - (μ * L + D) * r - S = 0
    dsimp only [r, a, μ, D, S]
    exact h
  have hqT : a * T ^ 2 - (μ * L + D) * T - S ≤ 0 := by
    have hidentity :
      a * T ^ 2 - (μ * L + D) * T - S = -(108803291 / 426562500 : ℝ) * L - 1261 / 25 := by
      dsimp only [T, μ, a, D, S]
      ring
    rw [hidentity]
    nlinarith only [hL]
  by_contra hnot
  have hbad : r < T := lt_of_not_ge hnot
  have hfactor : 0 < a * (T + r) - (μ * L + D) := by
    have hbase : 0 < a * T - (μ * L + D) := by
      have heq : a * T - (μ * L + D) = 6 * a - D := by
        dsimp only [T]
        ring
      rw [heq]
      norm_num only [a, D]
    calc
      0 < (a * T - (μ * L + D)) + a * r := add_pos hbase (mul_pos (by norm_num only [a]) hrpos)
      _ = a * (T + r) - (μ * L + D) := by ring
  have hdiff :
    (a * T ^ 2 - (μ * L + D) * T - S) - (a * r ^ 2 - (μ * L + D) * r - S) =
      (T - r) * (a * (T + r) - (μ * L + D)) := by
    ring
  have hdiffpos : 0 < (a * T ^ 2 - (μ * L + D) * T - S) - (a * r ^ 2 - (μ * L + D) * r - S) := by
    rw [hdiff]
    exact mul_pos (sub_pos.mpr hbad) hfactor
  linarith only [hqT, hquad, hdiffpos]

/-- The 50000-prefix Gamma radius is at least `(μ/a)L+14/5` from scale
270 onward. -/
theorem gammaPrefix100Radius_lower_mu_fourteen_fifths {L : ℝ} (hL : 270 ≤ L) :
    ((11783423 / 25000000 : ℝ) / (91 / 100)) * L + 14 / 5 ≤
      gammaPrefix100Radius L (28493 / 5000) := by
  let μ : ℝ := 11783423 / 25000000
  let a : ℝ := 91 / 100
  let D : ℝ := 591 / 50 - 2 * (28493 / 5000)
  let S : ℝ := (7 / 6 : ℝ) * L + 61
  let r := gammaPrefix100Radius L (28493 / 5000)
  let T := (μ / a) * L + 14 / 5
  have hD : 0 ≤ (591 / 50 : ℝ) - 2 * (28493 / 5000) := by norm_num only
  have hprop :=
    gammaPrefix100Radius_properties (C := (28493 / 5000 : ℝ)) (by linarith only [hL] : 240 ≤ L) hD
  have hrpos : 0 < r := by
    dsimp only [r]; exact hprop.1
  have hquad : a * r ^ 2 - (μ * L + D) * r - S = 0 := by
    have h := hprop.2
    change a * r ^ 2 - (μ * L + D) * r - S = 0
    dsimp only [r, a, μ, D, S]
    exact h
  have hqT : a * T ^ 2 - (μ * L + D) * T - S ≤ 0 := by
    have hidentity :
      a * T ^ 2 - (μ * L + D) * T - S = -(1606645829 / 24375000000 : ℝ) * L - 344059 / 6250 := by
      dsimp only [T, μ, a, D, S]
      ring
    rw [hidentity]
    nlinarith only [hL]
  by_contra hnot
  have hbad : r < T := lt_of_not_ge hnot
  have hfactor : 0 < a * (T + r) - (μ * L + D) := by
    have hbase : 0 < a * T - (μ * L + D) := by
      have heq : a * T - (μ * L + D) = (14 / 5 : ℝ) * a - D := by
        dsimp only [T]
        ring
      rw [heq]
      norm_num only [a, D]
    calc
      0 < (a * T - (μ * L + D)) + a * r := add_pos hbase (mul_pos (by norm_num only [a]) hrpos)
      _ = a * (T + r) - (μ * L + D) := by ring
  have hdiff :
    (a * T ^ 2 - (μ * L + D) * T - S) - (a * r ^ 2 - (μ * L + D) * r - S) =
      (T - r) * (a * (T + r) - (μ * L + D)) := by
    ring
  have hdiffpos : 0 < (a * T ^ 2 - (μ * L + D) * T - S) - (a * r ^ 2 - (μ * L + D) * r - S) := by
    rw [hdiff]
    exact mul_pos (sub_pos.mpr hbad) hfactor
  linarith only [hqT, hquad, hdiffpos]

/-- A linear upper estimate for the residual-29 Gaussian radius. It is used
to compare the new three-prime cutoff with the 1000-prefix Gamma curve. -/
theorem gammaIndex100GaussianTripleRadius29_le_half_add_213_tenths {L : ℝ} (hL : 240 ≤ L) :
    gammaIndex100GaussianTripleRadius29 L ≤ L / 2 + 213 / 10 := by
  let R := gammaIndex100GaussianTripleRadius29 L
  let s := Real.sqrt R
  let d : ℝ := (4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3
  let b : ℝ := (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10)
  let c : ℝ := 161 / 600
  let T := L / 2 + 213 / 10
  have hprops := gammaIndex100GaussianTripleRadius29_properties (by linarith only [hL])
  have hRpos : 0 < R := by
    dsimp only [R]; exact hprops.1
  have hspos : 0 < s := by
    dsimp only [s]; exact Real.sqrt_pos.2 hRpos
  have hsR : s ^ 2 = R := by
    dsimp only [s]; exact Real.sq_sqrt hRpos.le
  have hroot : d * R - b * s - c * L - 29 = 0 := by
    have h := hprops.2
    change d * R - b * Real.sqrt R - c * L - 29 = 0 at h
    rw [show Real.sqrt R = s by rfl] at h
    exact h
  have hTlower : 121 ≤ T := by
    dsimp only [T]; nlinarith only [hL]
  have hTnonneg : 0 ≤ T := by linarith only [hTlower]
  have hTroot : Real.sqrt T ≤ L / 20 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith only [hL]
    · dsimp only [T]
      nlinarith only [hL, sq_nonneg (L - 240)]
  have hT121 : (11 : ℝ) ^ 2 ≤ T := by nlinarith only [hTlower]
  have hTrootlow : 11 ≤ Real.sqrt T := Real.le_sqrt_of_sq_le hT121
  have hsLower : 11 ≤ s := by
    have hRlower := gammaIndex100GaussianTripleRadius29_lower (by linarith only [hL])
    have hR121 : 121 ≤ R := by
      dsimp only [R] at hRlower ⊢; nlinarith only [hL, hRlower]
    have hs2 : (11 : ℝ) ^ 2 ≤ s ^ 2 := by
      rw [hsR]
      nlinarith only [hR121]
    nlinarith only [hspos, hs2]
  have hslope : 0 < d / 2 - b / 20 - c := by norm_num only [d, b, c]
  have hmargin0 : 0 < (d / 2 - b / 20 - c) * 240 + d * (213 / 10) - 29 := by norm_num only [d, b, c]
  have hmargin : 0 < (d / 2 - b / 20 - c) * L + d * (213 / 10) - 29 := by
    have hdelta : 0 ≤ L - 240 := by linarith only [hL]
    have hlinear :
      (d / 2 - b / 20 - c) * L + d * (213 / 10) - 29 =
        ((d / 2 - b / 20 - c) * 240 + d * (213 / 10) - 29) + (d / 2 - b / 20 - c) * (L - 240) := by
      ring
    rw [hlinear]
    exact add_pos_of_pos_of_nonneg hmargin0 (mul_nonneg hslope.le hdelta)
  have hTineq : c * L + 29 < d * T - b * Real.sqrt T := by
    have hb : 0 ≤ b := by norm_num only [b]
    calc
      c * L + 29 < d * T - b * (L / 20) := by
        dsimp only [T]
        nlinarith only [hmargin]
      _ ≤ d * T - b * Real.sqrt T := by
        have hscaled := mul_le_mul_of_nonneg_left hTroot hb
        linarith only [hscaled]
  by_contra hnot
  have hbad : T < R := by
    dsimp only [T, R] at hnot ⊢; exact lt_of_not_ge hnot
  have hrootlt : Real.sqrt T < s := by
    apply Real.sqrt_lt_sqrt hTnonneg
    dsimp only [R] at hbad ⊢
    exact hbad
  have hfactor : 0 < d * (Real.sqrt T + s) - b := by
    dsimp only [d, b]
    nlinarith only [hTrootlow, hsLower]
  have hdiff :
    (d * T - b * Real.sqrt T - c * L - 29) - (d * R - b * s - c * L - 29) =
      (Real.sqrt T - s) * (d * (Real.sqrt T + s) - b) := by
    have hTsq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTnonneg
    have hdT : d * T = d * (Real.sqrt T) ^ 2 := congrArg (fun x : ℝ => d * x) hTsq.symm
    have hdR : d * R = d * s ^ 2 := congrArg (fun x : ℝ => d * x) hsR.symm
    calc
      _ = d * T - b * Real.sqrt T - c * L - 29 - d * R + b * s + c * L + 29 := by ring
      _ = d * (Real.sqrt T) ^ 2 - b * Real.sqrt T - c * L - 29 - d * s ^ 2 + b * s + c * L + 29 :=
        by rw [hdT, hdR]
      _ = (Real.sqrt T - s) * (d * (Real.sqrt T + s) - b) := by ring
  have hzero : d * R - b * s - c * L - 29 = 0 := hroot
  have hdiffpos : 0 < (d * T - b * Real.sqrt T - c * L - 29) - (d * R - b * s - c * L - 29) := by
    rw [hzero, sub_zero]
    linarith only [hTineq]
  have hdiffneg : (d * T - b * Real.sqrt T - c * L - 29) - (d * R - b * s - c * L - 29) < 0 := by
    rw [hdiff]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hrootlt) hfactor
  exact lt_asymm hdiffneg hdiffpos

/-- From `L ≥ 270`, a sharper affine upper estimate for the residual-29
radius supplies the comparison with the 50000-prefix Gamma branch. -/
theorem gammaIndex100GaussianTripleRadius29_le_49_hundredths_add_22 {L : ℝ} (hL : 270 ≤ L) :
    gammaIndex100GaussianTripleRadius29 L ≤ (49 / 100 : ℝ) * L + 22 := by
  let R := gammaIndex100GaussianTripleRadius29 L
  let s := Real.sqrt R
  let d : ℝ := (4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3
  let b : ℝ := (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10)
  let c : ℝ := 161 / 600
  let T := (49 / 100 : ℝ) * L + 22
  have hprops := gammaIndex100GaussianTripleRadius29_properties (by linarith only [hL])
  have hRpos : 0 < R := by
    dsimp only [R]; exact hprops.1
  have hspos : 0 < s := by
    dsimp only [s]; exact Real.sqrt_pos.2 hRpos
  have hsR : s ^ 2 = R := by
    dsimp only [s]; exact Real.sq_sqrt hRpos.le
  have hroot : d * R - b * s - c * L - 29 = 0 := by
    have h := hprops.2
    change d * R - b * Real.sqrt R - c * L - 29 = 0 at h
    rw [show Real.sqrt R = s by rfl] at h
    exact h
  have hTlower : 121 ≤ T := by
    dsimp only [T]; nlinarith only [hL]
  have hTnonneg : 0 ≤ T := by linarith only [hTlower]
  have hTroot : Real.sqrt T ≤ L / 20 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith only [hL]
    · dsimp only [T]
      nlinarith only [hL, sq_nonneg (L - 270)]
  have hT121 : (11 : ℝ) ^ 2 ≤ T := by nlinarith only [hTlower]
  have hTrootlow : 11 ≤ Real.sqrt T := Real.le_sqrt_of_sq_le hT121
  have hsLower : 11 ≤ s := by
    have hRlower := gammaIndex100GaussianTripleRadius29_lower (by linarith only [hL])
    have hR121 : 121 ≤ R := by
      dsimp only [R] at hRlower ⊢; nlinarith only [hL, hRlower]
    have hs2 : (11 : ℝ) ^ 2 ≤ s ^ 2 := by
      rw [hsR]
      nlinarith only [hR121]
    nlinarith only [hspos, hs2]
  have hslope : 0 < d * (49 / 100 : ℝ) - b / 20 - c := by norm_num only [d, b, c]
  have hmargin0 : 0 < (d * (49 / 100 : ℝ) - b / 20 - c) * 270 + d * 22 - 29 := by
    norm_num only [d, b, c]
  have hmargin : 0 < (d * (49 / 100 : ℝ) - b / 20 - c) * L + d * 22 - 29 := by
    have hdelta : 0 ≤ L - 270 := by linarith only [hL]
    have hlinear :
      (d * (49 / 100 : ℝ) - b / 20 - c) * L + d * 22 - 29 =
        ((d * (49 / 100 : ℝ) - b / 20 - c) * 270 + d * 22 - 29) +
          (d * (49 / 100 : ℝ) - b / 20 - c) * (L - 270) := by
      ring
    rw [hlinear]
    exact add_pos_of_pos_of_nonneg hmargin0 (mul_nonneg hslope.le hdelta)
  have hTineq : c * L + 29 < d * T - b * Real.sqrt T := by
    have hb : 0 ≤ b := by norm_num only [b]
    calc
      c * L + 29 < d * T - b * (L / 20) := by
        dsimp only [T]
        nlinarith only [hmargin]
      _ ≤ d * T - b * Real.sqrt T := by
        have hscaled := mul_le_mul_of_nonneg_left hTroot hb
        linarith only [hscaled]
  by_contra hnot
  have hbad : T < R := by
    dsimp only [T, R] at hnot ⊢; exact lt_of_not_ge hnot
  have hrootlt : Real.sqrt T < s := by
    apply Real.sqrt_lt_sqrt hTnonneg
    dsimp only [R] at hbad ⊢
    exact hbad
  have hfactor : 0 < d * (Real.sqrt T + s) - b := by
    dsimp only [d, b]
    nlinarith only [hTrootlow, hsLower]
  have hdiff :
    (d * T - b * Real.sqrt T - c * L - 29) - (d * R - b * s - c * L - 29) =
      (Real.sqrt T - s) * (d * (Real.sqrt T + s) - b) := by
    have hTsq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTnonneg
    have hdT : d * T = d * (Real.sqrt T) ^ 2 := congrArg (fun x : ℝ => d * x) hTsq.symm
    have hdR : d * R = d * s ^ 2 := congrArg (fun x : ℝ => d * x) hsR.symm
    calc
      _ = d * T - b * Real.sqrt T - c * L - 29 - d * R + b * s + c * L + 29 := by ring
      _ = d * (Real.sqrt T) ^ 2 - b * Real.sqrt T - c * L - 29 - d * s ^ 2 + b * s + c * L + 29 :=
        by rw [hdT, hdR]
      _ = (Real.sqrt T - s) * (d * (Real.sqrt T + s) - b) := by ring
  have hdiffpos : 0 < (d * T - b * Real.sqrt T - c * L - 29) - (d * R - b * s - c * L - 29) := by
    rw [hroot, sub_zero]
    linarith only [hTineq]
  have hdiffneg : (d * T - b * Real.sqrt T - c * L - 29) - (d * R - b * s - c * L - 29) < 0 := by
    rw [hdiff]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hrootlt) hfactor
  exact lt_asymm hdiffneg hdiffpos

/-- The new index-four cutoff is below the uncapped 1000-prefix Gamma curve
for every `L ≥ 240`. The two affine radius bounds give a uniform comparison. -/
theorem gammaIndex100GaussianTripleBound29_le_gammaPrefix1000 {L : ℝ} (hL : 240 ≤ L) :
    (21 / 10 : ℝ) * (gammaIndex100GaussianTripleRadius29 L) ^ 2 ≤
      (99 / 40 : ℝ) * (gammaPrefix100Radius L (203 / 50)) ^ 2 := by
  let R := gammaIndex100GaussianTripleRadius29 L
  let ρ := gammaPrefix100Radius L (203 / 50)
  let μ : ℝ := 11783423 / 25000000
  let a : ℝ := 91 / 100
  let T := L / 2 + 213 / 10
  have hRpos := (gammaIndex100GaussianTripleRadius29_properties (by linarith only [hL] : 200 ≤ L)).1
  have hρprop := gammaPrefix100Radius_properties (C := (203 / 50 : ℝ)) hL (by norm_num only)
  have hρpos : 0 < ρ := by
    dsimp only [ρ]; exact hρprop.1
  have hρlower : (μ / a) * L + 6 ≤ ρ := by
    dsimp only [ρ, μ, a]
    exact gammaPrefix100Radius_lower_mu_six hL
  have hRupper : R ≤ T := by
    dsimp only [R, T]
    exact gammaIndex100GaussianTripleRadius29_le_half_add_213_tenths hL
  have hfactor : (217 / 200 : ℝ) ≤ Real.sqrt (33 / 28 : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num only
  have hlinear : T ≤ (217 / 200 : ℝ) * ((μ / a) * L + 6) := by
    have hdiff :
      (217 / 200 : ℝ) * ((μ / a) * L + 6) - T =
        (40286113 / 650000000 : ℝ) * (L - 240) + 689589 / 8125000 := by
      dsimp only [T, μ, a]
      ring
    rw [← sub_nonneg]
    rw [hdiff]
    have hdelta : 0 ≤ L - 240 := by linarith only [hL]
    nlinarith only [hdelta]
  have hscaled : R ≤ Real.sqrt (33 / 28 : ℝ) * ρ := by
    have hbound := hRupper.trans hlinear
    have hmul := mul_le_mul_of_nonneg_left hρlower (by norm_num only : (0 : ℝ) ≤ 217 / 200)
    have hfactorρ := mul_le_mul_of_nonneg_right hfactor hρpos.le
    dsimp only [μ, a] at hρlower hmul hfactorρ ⊢
    nlinarith only [hbound, hmul, hfactorρ]
  have hRnonneg : 0 ≤ R := by
    dsimp only [R]; exact hRpos.le
  have hRsq : R ^ 2 ≤ (Real.sqrt (33 / 28 : ℝ) * ρ) ^ 2 := by nlinarith only [hscaled, hRnonneg]
  have hcoef : (21 / 10 : ℝ) * (Real.sqrt (33 / 28 : ℝ)) ^ 2 ≤ 99 / 40 := by
    rw [Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 33 / 28)]
    norm_num only
  calc
    (21 / 10 : ℝ) * R ^ 2 ≤ (21 / 10 : ℝ) * (Real.sqrt (33 / 28 : ℝ) * ρ) ^ 2 :=
      mul_le_mul_of_nonneg_left hRsq (by norm_num only)
    _ ≤ (99 / 40 : ℝ) * ρ ^ 2 := by
      dsimp only [ρ]
      nlinarith only [hcoef, sq_nonneg (gammaPrefix100Radius L (203 / 50))]

/-- On the 240-to-270 overlap, the residual-29 cutoff is below 50000, so it
is covered by the clipped 50000-prefix branch. -/
theorem gammaIndex100GaussianTripleBound29_le_50000 {L : ℝ} (hL : 240 ≤ L) (hU : L ≤ 270) :
    gammaIndex100GaussianTripleBound29 L ≤ 50000 := by
  have hRle := gammaIndex100GaussianTripleRadius29_le_153 hL hU
  have hRpos := (gammaIndex100GaussianTripleRadius29_properties (by linarith only [hL] : 200 ≤ L)).1
  have hRsq : (gammaIndex100GaussianTripleRadius29 L) ^ 2 ≤ (153 : ℝ) ^ 2 := by
    nlinarith only [hRle, hRpos]
  dsimp only [gammaIndex100GaussianTripleBound29]
  nlinarith only [hRsq]

/-- The residual-29 cutoff is covered by the clipped 1000-prefix Gamma
branch throughout its range of validity. -/
theorem gammaIndex100GaussianTripleBound29_le_gammaIndex100Prefix1000 {L : ℝ} (hL : 240 ≤ L) :
    gammaIndex100GaussianTripleBound29 L ≤
      max 1000 ((99 / 40 : ℝ) * gammaPrefix100Radius L (203 / 50) ^ 2) := by
  exact (gammaIndex100GaussianTripleBound29_le_gammaPrefix1000 hL).trans (le_max_right _ _)

/-- From scale 270, the residual-29 cutoff is below the uncapped 50000-prefix
Gamma curve. -/
theorem gammaIndex100GaussianTripleBound29_le_gammaPrefix50000 {L : ℝ} (hL : 270 ≤ L) :
    gammaIndex100GaussianTripleBound29 L ≤
      (99 / 40 : ℝ) * (gammaPrefix100Radius L (28493 / 5000)) ^ 2 := by
  let R := gammaIndex100GaussianTripleRadius29 L
  let ρ := gammaPrefix100Radius L (28493 / 5000)
  let μ : ℝ := 11783423 / 25000000
  let a : ℝ := 91 / 100
  let T := (49 / 100 : ℝ) * L + 22
  have hRpos := (gammaIndex100GaussianTripleRadius29_properties (by linarith only [hL] : 200 ≤ L)).1
  have hρprop :=
    gammaPrefix100Radius_properties (C := (28493 / 5000 : ℝ)) (by linarith only [hL] : 240 ≤ L)
      (by norm_num only)
  have hρpos : 0 < ρ := by
    dsimp only [ρ]; exact hρprop.1
  have hρlower : (μ / a) * L + 14 / 5 ≤ ρ := by
    dsimp only [ρ, μ, a]
    exact gammaPrefix100Radius_lower_mu_fourteen_fifths hL
  have hRupper : R ≤ T := by
    dsimp only [R, T]
    exact gammaIndex100GaussianTripleRadius29_le_49_hundredths_add_22 hL
  have hfactor : (217 / 200 : ℝ) ≤ Real.sqrt (33 / 28 : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num only
  have hlinear : T ≤ (217 / 200 : ℝ) * ((μ / a) * L + 14 / 5) := by
    have hdiff :
      (217 / 200 : ℝ) * ((μ / a) * L + 14 / 5) - T =
        (46786113 / 650000000 : ℝ) * (L - 270) + 30695051 / 65000000 := by
      dsimp only [T, μ, a]
      ring
    rw [← sub_nonneg]
    rw [hdiff]
    have hdelta : 0 ≤ L - 270 := by linarith only [hL]
    nlinarith only [hdelta]
  have hscaled : R ≤ Real.sqrt (33 / 28 : ℝ) * ρ := by
    have hbound := hRupper.trans hlinear
    have hmul := mul_le_mul_of_nonneg_left hρlower (by norm_num only : (0 : ℝ) ≤ 217 / 200)
    have hfactorρ := mul_le_mul_of_nonneg_right hfactor hρpos.le
    dsimp only [μ, a] at hρlower hmul hfactorρ ⊢
    nlinarith only [hbound, hmul, hfactorρ]
  have hRnonneg : 0 ≤ R := by
    dsimp only [R]; exact hRpos.le
  have hRsq : R ^ 2 ≤ (Real.sqrt (33 / 28 : ℝ) * ρ) ^ 2 := by nlinarith only [hscaled, hRnonneg]
  have hcoef : (21 / 10 : ℝ) * (Real.sqrt (33 / 28 : ℝ)) ^ 2 ≤ 99 / 40 := by
    rw [Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 33 / 28)]
    norm_num only
  calc
    gammaIndex100GaussianTripleBound29 L = (21 / 10 : ℝ) * R ^ 2 := by rfl
    _ ≤ (21 / 10 : ℝ) * (Real.sqrt (33 / 28 : ℝ) * ρ) ^ 2 :=
      mul_le_mul_of_nonneg_left hRsq (by norm_num only)
    _ ≤ (99 / 40 : ℝ) * ρ ^ 2 := by
      dsimp only [ρ]
      nlinarith only [hcoef, sq_nonneg (gammaPrefix100Radius L (28493 / 5000))]

/-- The residual-29 index-four cutoff lies below both clipped prefix curves,
and hence below their minimum `U₁₀₀`, from logarithmic scale 240 onward. -/
theorem gammaIndex100GaussianTripleBound29_le_prefix_upper {L : ℝ} (hL : 240 ≤ L) :
    gammaIndex100GaussianTripleBound29 L ≤ gammaIndex100PrefixUpper L := by
  apply le_min
  · exact gammaIndex100GaussianTripleBound29_le_gammaIndex100Prefix1000 hL
  · by_cases hU : L ≤ 270
    · exact (gammaIndex100GaussianTripleBound29_le_50000 hL hU).trans (le_max_left _ _)
    · have h270 : 270 ≤ L := le_of_not_ge hU
      exact (gammaIndex100GaussianTripleBound29_le_gammaPrefix50000 h270).trans (le_max_right _ _)

/-- The old `21/10` Gaussian ambient error is below 29 at the scaled
Gamma index-100 radius for every `L ≥ 330`. Use the `9/5` negative-power
anchor together with the lower and upper radius bounds. -/
theorem gammaIndex100GaussianAmbientError_lt {n : ℕ} {L : ℝ} (hL : 330 ≤ L)
    (hlog : Real.log n = L) :
    LLS.PaperStatements.gaussianAmbientError n (gammaIndex100GaussianRadius L ^ 2) < 29 := by
  let R := gammaIndex100GaussianRadius L
  have hRbounds := gammaIndex100GaussianRadius_linear_bounds (by linarith only [hL])
  have hR184 : 184 ≤ R := by
    dsimp only [R] at hRbounds ⊢
    nlinarith only [hL, hRbounds.1]
  have hRpos : 0 < R := by linarith only [hR184]
  have hx : (9 / 5 : ℝ) ^ (16 : ℕ) ≤ R ^ 2 := by
    have hsquare : (184 : ℝ) ^ 2 ≤ R ^ 2 := by nlinarith only [hR184, sq_nonneg (R - 184)]
    norm_num only at hsquare ⊢
    nlinarith only [hsquare]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 9 / 5) (by norm_num only)
      hx
  have hsqrt : Real.sqrt (R ^ 2) = R := Real.sqrt_sq hRpos.le
  have hcoeff : 0 ≤ (16 / 5 : ℝ) * (L + 283) + 5 / 3 := by nlinarith only [hL]
  have hpole : (2129 / 2000 : ℝ) * (((7 / 6) * L + 4) / R) ≤ 9 / 4 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hRpos).2
    nlinarith only [hRbounds.1, hL]
  have htail :
    (11 / 10 : ℝ) * (R ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * (L + 283) + 5 / 3) ≤ 13 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hdec hcoeff
    rw [hsqrt] at hmul
    have hbound :
      (11 / 10 : ℝ) * ((16 / 5 : ℝ) * (L + 283) + 5 / 3) / ((9 / 5 : ℝ) * R) ≤ 13 / 2 := by
      apply (div_le_iff₀ (mul_pos (by norm_num only) hRpos)).2
      nlinarith only [hRbounds.1, hL]
    simp only [div_eq_mul_inv] at hmul hbound ⊢
    nlinarith only [hmul, hbound]
  change
    (12871 / 1000 : ℝ) + 64 / 9 +
        (2129 / 2000 : ℝ) * (((7 / 6) * Real.log n + 4) / Real.sqrt (R ^ 2)) +
        (11 / 10 : ℝ) * (R ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * (Real.log n + 283) + 5 / 3) <
      29
  rw [hlog, hsqrt]
  have htotal : (12871 / 1000 : ℝ) + 64 / 9 + 9 / 4 + 13 / 2 < 29 := by norm_num only
  linarith only [hpole, htail, htotal]

/-- At the existing index-100 Gaussian radius, the transferred 1000-prefix
ambient error is below 22 for every `L ≥ 330`. -/
theorem gammaIndex100GaussianAmbientErrorPrefix1000_lt {n : ℕ} {L : ℝ} (hL : 330 ≤ L)
    (hlog : Real.log n = L) :
    LLS.PaperStatements.gaussianAmbientErrorPrefix1000 n (gammaIndex100GaussianRadius L ^ 2) <
      22 := by
  let R := gammaIndex100GaussianRadius L
  have hRbounds := gammaIndex100GaussianRadius_linear_bounds hL
  have hR184 : 184 ≤ R := by
    dsimp only [R] at hRbounds ⊢
    nlinarith only [hL, hRbounds.1]
  have hRpos : 0 < R := by linarith only [hR184]
  have hx : (9 / 5 : ℝ) ^ (16 : ℕ) ≤ R ^ 2 := by
    have hsquare : (184 : ℝ) ^ 2 ≤ R ^ 2 := by nlinarith only [hR184, sq_nonneg (R - 184)]
    norm_num only at hsquare ⊢
    nlinarith only [hsquare]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 9 / 5) (by norm_num only)
      hx
  have hsqrt : Real.sqrt (R ^ 2) = R := Real.sqrt_sq hRpos.le
  have hcoeff : 0 ≤ (16 / 5 : ℝ) * (L + 283) + 5 / 3 := by nlinarith only [hL]
  have hpole : (2129 / 2000 : ℝ) * (((7 / 6) * L + 4) / R) ≤ 9 / 4 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hRpos).2
    nlinarith only [hRbounds.1, hL]
  have htail :
    (11 / 10 : ℝ) * (R ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * (L + 283) + 5 / 3) ≤ 13 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hdec hcoeff
    rw [hsqrt] at hmul
    have hbound :
      (11 / 10 : ℝ) * ((16 / 5 : ℝ) * (L + 283) + 5 / 3) / ((9 / 5 : ℝ) * R) ≤ 13 / 2 := by
      apply (div_le_iff₀ (mul_pos (by norm_num only) hRpos)).2
      nlinarith only [hRbounds.1, hL]
    simp only [div_eq_mul_inv] at hmul hbound ⊢
    nlinarith only [hmul, hbound]
  change
    (5969 / 1000 : ℝ) + 64 / 9 +
        (2129 / 2000 : ℝ) * (((7 / 6) * Real.log n + 4) / Real.sqrt (R ^ 2)) +
        (11 / 10 : ℝ) * (R ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * (Real.log n + 283) + 5 / 3) <
      22
  rw [hlog, hsqrt]
  have htotal : (5969 / 1000 : ℝ) + 64 / 9 + 9 / 4 + 13 / 2 < 22 := by norm_num only
  linarith only [hpole, htail, htotal]

/-- At the residual-29 radius, the transferred 1000-prefix ambient error is
below 23 for every `L ≥ 200`. -/
theorem gammaIndex100GaussianTripleAmbientErrorPrefix1000_lt {n : ℕ} {L : ℝ} (hL : 200 ≤ L)
    (hlog : Real.log n = L) :
    LLS.PaperStatements.gaussianAmbientErrorPrefix1000 n
        (gammaIndex100GaussianTripleRadius29 L ^ 2) <
      23 := by
  let R := gammaIndex100GaussianTripleRadius29 L
  let P : ℝ := (2129 / 2000) * ((7 / 6) * L + 4)
  let Q : ℝ := (11 / 10) * ((16 / 5 : ℝ) * (L + 283) + 5 / 3)
  have hRlower : (9 / 25 : ℝ) * L + 50 ≤ R := gammaIndex100GaussianTripleRadius29_lower hL
  have hR122 : 122 ≤ R := by nlinarith only [hL, hRlower]
  have hRpos : 0 < R := by linarith only [hR122]
  have hx : (9 / 5 : ℝ) ^ (16 : ℕ) ≤ R ^ 2 := by
    have hsquare : (122 : ℝ) ^ 2 ≤ R ^ 2 := by nlinarith only [hR122, sq_nonneg (R - 122)]
    norm_num only at hsquare ⊢
    nlinarith only [hsquare]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 9 / 5) (by norm_num only)
      hx
  have hsqrt : Real.sqrt (R ^ 2) = R := Real.sqrt_sq hRpos.le
  have hcoeff : 0 ≤ (16 / 5 : ℝ) * (L + 283) + 5 / 3 := by nlinarith only [hL]
  have htailBound :
    (11 / 10 : ℝ) * (R ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * (L + 283) + 5 / 3) ≤
      Q / ((9 / 5 : ℝ) * R) := by
    have hmul := mul_le_mul_of_nonneg_right hdec hcoeff
    rw [hsqrt] at hmul
    have hscaled := mul_le_mul_of_nonneg_left hmul (by norm_num only : (0 : ℝ) ≤ 11 / 10)
    dsimp only [Q]
    simp only [div_eq_mul_inv] at hscaled ⊢
    nlinarith only [hscaled]
  have hcostNum : P + Q / (9 / 5 : ℝ) ≤ (99 / 10 : ℝ) * R := by
    dsimp only [P, Q]
    nlinarith only [hRlower, hL]
  have hcost : P / R + Q / ((9 / 5 : ℝ) * R) ≤ 99 / 10 := by
    have hdiv := (div_le_iff₀ hRpos).2 hcostNum
    have heq : (P + Q / (9 / 5 : ℝ)) / R = P / R + Q / ((9 / 5 : ℝ) * R) := by rw [add_div, div_div]
    rw [← heq]
    exact hdiv
  have hcombined :
    (2129 / 2000 : ℝ) * (((7 / 6) * L + 4) / R) +
        (11 / 10 : ℝ) * (R ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * (L + 283) + 5 / 3) ≤
      99 / 10 := by
    have hP : (2129 / 2000 : ℝ) * (((7 / 6) * L + 4) / R) = P / R := by
      dsimp only [P]
      rw [← mul_div_assoc]
    rw [hP]
    exact (add_le_add (le_refl (P / R)) htailBound).trans hcost
  change
    (5969 / 1000 : ℝ) + 64 / 9 +
        (2129 / 2000 : ℝ) * (((7 / 6) * Real.log n + 4) / Real.sqrt (R ^ 2)) +
        (11 / 10 : ℝ) * (R ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * (Real.log n + 283) + 5 / 3) <
      23
  rw [hlog, hsqrt]
  have htotal : (5969 / 1000 : ℝ) + 64 / 9 + 99 / 10 < 23 := by norm_num only
  linarith only [hcombined, htotal]

/-- At `L ≥ 330`, the index-four inverse-radius and ambient costs at the
scaled `21/10` radius total less than 35. -/
theorem gammaIndex100GaussianTripleScalarError_lt {L s R A : ℝ} (hL : 330 ≤ L)
    (hRlo : (14 / 25 : ℝ) * L ≤ R) (hs0 : 0 ≤ s) (hssq : s ^ 2 = R) (hA : A ≤ 29) :
    (4 / 3 : ℝ) * (63 * (2129 / 2000 : ℝ) / (10 * s) + 1839 * (2129 / 2000 : ℝ) / (1000 * R)) +
        13 / 3 +
        A <
      35 := by
  have hR184 : 184 ≤ R := by nlinarith only [hL, hRlo]
  have hsLower : 27 / 2 ≤ s := by
    by_contra hs
    have hslt : s < 27 / 2 := lt_of_not_ge hs
    nlinarith only [hs0, hssq, hR184, hslt]
  have hspos : 0 < s := by linarith only [hsLower]
  have hRpos : 0 < R := by linarith only [hR184]
  have hnum1 : 0 ≤ 63 * (2129 / 2000 : ℝ) := by norm_num only
  have hden1 : 0 < 10 * (27 / 2 : ℝ) := by norm_num only
  have hterm1 : 63 * (2129 / 2000 : ℝ) / (10 * s) ≤ 63 * (2129 / 2000 : ℝ) / (10 * (27 / 2 : ℝ)) :=
    div_le_div_of_nonneg_left hnum1 hden1 (by nlinarith only [hsLower])
  have hnum2 : 0 ≤ 1839 * (2129 / 2000 : ℝ) := by norm_num only
  have hden2 : 0 < 1000 * (184 : ℝ) := by norm_num only
  have hterm2 : 1839 * (2129 / 2000 : ℝ) / (1000 * R) ≤ 1839 * (2129 / 2000 : ℝ) / (1000 * 184) :=
    div_le_div_of_nonneg_left hnum2 hden2 (by nlinarith only [hR184])
  have hconst :
    (4 / 3 : ℝ) *
          (63 * (2129 / 2000 : ℝ) / (10 * (27 / 2 : ℝ)) + 1839 * (2129 / 2000 : ℝ) / (1000 * 184)) +
        13 / 3 +
        29 <
      35 := by
    norm_num only
  have htail := add_le_add hterm1 hterm2
  nlinarith only [htail, hA, hconst]

/-- From `L ≥ 200`, the inverse-radius terms and the 1000-prefix ambient
error total less than the residual budget 29. -/
theorem gammaIndex100GaussianTripleScalarErrorPrefix1000_lt {L s R A : ℝ} (hL : 200 ≤ L)
    (hRlo : (9 / 25 : ℝ) * L + 50 ≤ R) (hs0 : 0 ≤ s) (hssq : s ^ 2 = R) (hA : A ≤ 23) :
    (4 / 3 : ℝ) * (63 * (2129 / 2000 : ℝ) / (10 * s) + 1839 * (2129 / 2000 : ℝ) / (1000 * R)) +
        13 / 3 +
        A <
      29 := by
  have hR122 : 122 ≤ R := by nlinarith only [hL, hRlo]
  have hsLower : 11 ≤ s := by
    by_contra hs
    have hslt : s < 11 := lt_of_not_ge hs
    nlinarith only [hs0, hssq, hR122, hslt]
  have hspos : 0 < s := by linarith only [hsLower]
  have hRpos : 0 < R := by linarith only [hR122]
  have hnum1 : 0 ≤ 63 * (2129 / 2000 : ℝ) := by norm_num only
  have hden1 : 0 < 10 * (11 : ℝ) := by norm_num only
  have hterm1 : 63 * (2129 / 2000 : ℝ) / (10 * s) ≤ 63 * (2129 / 2000 : ℝ) / (10 * (11 : ℝ)) :=
    div_le_div_of_nonneg_left hnum1 hden1 (by nlinarith only [hsLower])
  have hnum2 : 0 ≤ 1839 * (2129 / 2000 : ℝ) := by norm_num only
  have hden2 : 0 < 1000 * (122 : ℝ) := by norm_num only
  have hterm2 : 1839 * (2129 / 2000 : ℝ) / (1000 * R) ≤ 1839 * (2129 / 2000 : ℝ) / (1000 * 122) :=
    div_le_div_of_nonneg_left hnum2 hden2 (by nlinarith only [hR122])
  have hconst :
    (4 / 3 : ℝ) *
          (63 * (2129 / 2000 : ℝ) / (10 * (11 : ℝ)) + 1839 * (2129 / 2000 : ℝ) / (1000 * 122)) +
        13 / 3 +
        23 <
      29 := by
    norm_num only
  have htail := add_le_add hterm1 hterm2
  nlinarith only [htail, hA, hconst]

/-- The index-four Gaussian main term at the scaled radius beats the conductor,
width, and residual costs. This is the exact positive margin from analysis12
§4.3 after using `R ≥ 14L/25`, `R ≤ 3L/5`, and `L ≥ 330`. -/
theorem gammaIndex100GaussianTripleBudget {L R s : ℝ} (hL : 330 ≤ L) (hRlo : (14 / 25 : ℝ) * L ≤ R)
    (hRhi : R ≤ (3 / 5 : ℝ) * L) (hs0 : 0 ≤ s) (hssq : s ^ 2 = R) :
    ((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) * R >
      (161 / 600 : ℝ) * L + (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10) * s + 35 := by
  let d4 : ℝ := (4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3
  let beta4 : ℝ := (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10)
  have hLpos : 0 < L := by linarith only [hL]
  have hsUpper : s ≤ (31 / 720 : ℝ) * L := by
    by_contra hnot
    have hdiff : 0 < s - (31 / 720 : ℝ) * L := by linarith only [hnot]
    have hsum : 0 < s + (31 / 720 : ℝ) * L := by positivity
    have hsq : ((31 / 720 : ℝ) * L) ^ 2 < s ^ 2 := by nlinarith only [hdiff, hsum]
    have hLsq : (3 / 5 : ℝ) * L ≤ ((31 / 720 : ℝ) * L) ^ 2 := by
      nlinarith only [hL, sq_nonneg (L - 330)]
    rw [hssq] at hsq
    linarith only [hsq, hRhi, hLsq]
  have hmargin :
    d4 * (14 / 25 : ℝ) - (161 / 600 : ℝ) - beta4 * (31 / 720 : ℝ) - 35 / 330 =
      4277877353 / 1782000000000 := by
    norm_num [d4, beta4]
  have hmarginpos : 0 < (4277877353 / 1782000000000 : ℝ) := by norm_num only
  have h350 : (35 : ℝ) ≤ (35 / 330) * L := by nlinarith only [hL]
  have hlinear :
    (161 / 600 : ℝ) * L + beta4 * ((31 / 720 : ℝ) * L) + 35 < d4 * ((14 / 25 : ℝ) * L) := by
    have hmarginL := mul_le_mul_of_nonneg_right (le_of_lt hmarginpos) hLpos.le
    rw [← hmargin] at hmarginL
    nlinarith only [hmarginL, h350, hL]
  have hd4pos : 0 < d4 := by norm_num [d4]
  have hbetapos : 0 ≤ beta4 := by norm_num [beta4]
  have hRlo' := mul_le_mul_of_nonneg_left hRlo (le_of_lt hd4pos)
  have hsUpper' := mul_le_mul_of_nonneg_left hsUpper hbetapos
  nlinarith only [hlinear, hRlo', hsUpper']

/-- The actual relative Gaussian comparison is impossible at the scaled
Gamma radius for an index-four subgroup whose conductor cost is at most `2L`.
Normalize the comparison by three, use the certified mass and endpoint bounds,
then apply the explicit inverse-radius and ambient budget. -/
theorem gammaIndex100GaussianTripleComparisonImpossible {L R s A I E C h : ℝ} (hL : 330 ≤ L)
    (hRlo : (14 / 25 : ℝ) * L ≤ R) (hRhi : R ≤ (3 / 5 : ℝ) * L) (hs0 : 0 ≤ s) (hssq : s ^ 2 = R)
    (hA : A ≤ 29) (hC : C ≤ 2 * L) (hI : 81470555 / 100000000 ≤ I) (hE : E ≤ 2129 / 2000)
    (hh : h = 1 / (3 * s)) (hh1 : h ≤ 1 / 2)
    (hcmp :
      (4 * (1 - h) * I - E) * R ≤
        (161 / 400 : ℝ) * C + 4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / R) * E) + 13 +
          3 * A) :
    False := by
  have hR184 : 184 ≤ R := by nlinarith only [hL, hRlo]
  have hRpos : 0 < R := by linarith only [hR184]
  have hspos : 0 < s := by
    by_contra hnot
    have hsnonpos : s ≤ 0 := le_of_not_gt hnot
    have hszero : s = 0 := le_antisymm hsnonpos hs0
    rw [hszero] at hssq
    linarith only [hssq, hRpos]
  have hdiv := div_le_div_of_nonneg_right hcmp (by norm_num only : (0 : ℝ) ≤ 3)
  have hleftEq : ((4 * (1 - h) * I - E) * R) / 3 = ((4 / 3 : ℝ) * (1 - h) * I - E / 3) * R := by
    ring
  have hrightEq :
    ((161 / 400 : ℝ) * C + 4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / R) * E) + 13 +
          3 * A) /
        3 =
      (161 / 1200 : ℝ) * C + (4 / 3) * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / R) * E) +
        13 / 3 +
        A := by
    ring
  rw [hleftEq, hrightEq] at hdiv
  have hW :
    1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / R) * E =
      3 * s / 10 + 63 * E / (10 * s) + 1839 * E / (1000 * R) := by
    rw [hh, ← hssq]
    field_simp [hspos.ne']
    ring
  rw [hW] at hdiv
  have hC' : (161 / 1200 : ℝ) * C ≤ (161 / 600 : ℝ) * L := by
    have hscaled := mul_le_mul_of_nonneg_left hC (by norm_num only : (0 : ℝ) ≤ 161 / 1200)
    nlinarith only [hscaled]
  have herror := gammaIndex100GaussianTripleScalarError_lt hL hRlo hs0 hssq hA
  have hmain :
    (((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) -
          (4 * (81470555 / 100000000 : ℝ)) / (9 * s)) *
        R ≤
      ((4 / 3 : ℝ) * (1 - h) * I - E / 3) * R := by
    have hfactor : 0 ≤ 1 - h := by linarith only [hh1]
    have hI' :=
      mul_le_mul_of_nonneg_left hI (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4 / 3) hfactor)
    have hE' := neg_le_neg hE
    have hbase :
      ((4 / 3 : ℝ) * (1 - h) * (81470555 / 100000000) - (2129 / 2000) / 3) ≤
        (4 / 3) * (1 - h) * I - E / 3 := by
      nlinarith only [hI', hE']
    have hscaled := mul_le_mul_of_nonneg_right hbase hRpos.le
    have hleft :
      (((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) -
            (4 * (81470555 / 100000000 : ℝ)) / (9 * s)) *
          R =
        ((4 / 3 : ℝ) * (1 - h) * (81470555 / 100000000) - (2129 / 2000) / 3) * R := by
      rw [hh]
      field_simp [hspos.ne']
      ring
    rw [hleft]
    exact hscaled
  have hbudget := gammaIndex100GaussianTripleBudget hL hRlo hRhi hs0 hssq
  have hupper :
    ((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) * R ≤
      (161 / 600 : ℝ) * L + (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10) * s + 35 := by
    have hE1 : 63 * E / (10 * s) ≤ 63 * (2129 / 2000 : ℝ) / (10 * s) := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hE (by norm_num only)
      · positivity
    have hE2 : 1839 * E / (1000 * R) ≤ 1839 * (2129 / 2000 : ℝ) / (1000 * R) := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hE (by norm_num only)
      · positivity
    have hcmp' := hmain.trans hdiv
    have herror' :
      (4 / 3 : ℝ) * (63 * (2129 / 2000 : ℝ) / (10 * s) + 1839 * (2129 / 2000 : ℝ) / (1000 * R)) +
          13 / 3 +
          A <
        35 := by
      exact gammaIndex100GaussianTripleScalarError_lt hL hRlo hs0 hssq hA
    have hcombine := hcmp'
    have hrootTerm :
      (4 * (81470555 / 100000000 : ℝ)) / (9 * s) * R =
        (4 * (81470555 / 100000000 : ℝ) / 9) * s := by
      rw [← hssq]
      field_simp [hspos.ne']
    have hbeta :
      (4 * (81470555 / 100000000 : ℝ) / 9) * s + (2 / 5 : ℝ) * s =
        (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10) * s := by
      ring
    nlinarith only [hcombine, hC', hE1, hE2, herror', hrootTerm, hbeta]
  exact (not_le_of_gt hbudget) hupper

/-- The relative Gaussian comparison contradicts the residual-29 root equation
for the 1000-prefix radius when the conductor cost is at most `2L`. -/
theorem gammaIndex100GaussianTripleComparisonImpossiblePrefix1000 {L R s A I E C h : ℝ}
    (hL : 200 ≤ L) (hRlo : (9 / 25 : ℝ) * L + 50 ≤ R) (hs0 : 0 ≤ s) (hssq : s ^ 2 = R) (hA : A ≤ 23)
    (hC : C ≤ 2 * L) (hI : 81470555 / 100000000 ≤ I) (hE : E ≤ 2129 / 2000) (hh : h = 1 / (3 * s))
    (hh1 : h ≤ 1 / 2)
    (hroot :
      ((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) * R -
          (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10) * s -
          (161 / 600 : ℝ) * L -
          29 =
        0)
    (hcmp :
      (4 * (1 - h) * I - E) * R ≤
        (161 / 400 : ℝ) * C + 4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / R) * E) + 13 +
          3 * A) :
    False := by
  have hR122 : 122 ≤ R := by nlinarith only [hL, hRlo]
  have hRpos : 0 < R := by linarith only [hR122]
  have hspos : 0 < s := by
    by_contra hnot
    have hsnonpos : s ≤ 0 := le_of_not_gt hnot
    have hszero : s = 0 := le_antisymm hsnonpos hs0
    rw [hszero] at hssq
    linarith only [hssq, hRpos]
  have hdiv := div_le_div_of_nonneg_right hcmp (by norm_num only : (0 : ℝ) ≤ 3)
  have hleftEq : ((4 * (1 - h) * I - E) * R) / 3 = ((4 / 3 : ℝ) * (1 - h) * I - E / 3) * R := by
    ring
  have hrightEq :
    ((161 / 400 : ℝ) * C + 4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / R) * E) + 13 +
          3 * A) /
        3 =
      (161 / 1200 : ℝ) * C + (4 / 3) * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / R) * E) +
        13 / 3 +
        A := by
    ring
  rw [hleftEq, hrightEq] at hdiv
  have hW :
    1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / R) * E =
      3 * s / 10 + 63 * E / (10 * s) + 1839 * E / (1000 * R) := by
    rw [hh, ← hssq]
    field_simp [hspos.ne']
    ring
  rw [hW] at hdiv
  have hC' : (161 / 1200 : ℝ) * C ≤ (161 / 600 : ℝ) * L := by
    have hscaled := mul_le_mul_of_nonneg_left hC (by norm_num only : (0 : ℝ) ≤ 161 / 1200)
    nlinarith only [hscaled]
  have herror := gammaIndex100GaussianTripleScalarErrorPrefix1000_lt hL hRlo hs0 hssq hA
  have hmain :
    (((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) -
          (4 * (81470555 / 100000000 : ℝ)) / (9 * s)) *
        R ≤
      ((4 / 3 : ℝ) * (1 - h) * I - E / 3) * R := by
    have hfactor : 0 ≤ 1 - h := by linarith only [hh1]
    have hI' :=
      mul_le_mul_of_nonneg_left hI (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4 / 3) hfactor)
    have hE' := neg_le_neg hE
    have hbase :
      ((4 / 3 : ℝ) * (1 - h) * (81470555 / 100000000) - (2129 / 2000) / 3) ≤
        (4 / 3) * (1 - h) * I - E / 3 := by
      nlinarith only [hI', hE']
    have hscaled := mul_le_mul_of_nonneg_right hbase hRpos.le
    have hleft :
      (((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) -
            (4 * (81470555 / 100000000 : ℝ)) / (9 * s)) *
          R =
        ((4 / 3 : ℝ) * (1 - h) * (81470555 / 100000000) - (2129 / 2000) / 3) * R := by
      rw [hh]
      field_simp [hspos.ne']
      ring
    rw [hleft]
    exact hscaled
  have hE1 : 63 * E / (10 * s) ≤ 63 * (2129 / 2000 : ℝ) / (10 * s) := by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hE (by norm_num only)
    · positivity
  have hE2 : 1839 * E / (1000 * R) ≤ 1839 * (2129 / 2000 : ℝ) / (1000 * R) := by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hE (by norm_num only)
    · positivity
  have hcombine := hmain.trans hdiv
  have hrootTerm :
    (4 * (81470555 / 100000000 : ℝ)) / (9 * s) * R = (4 * (81470555 / 100000000 : ℝ) / 9) * s := by
    rw [← hssq]
    field_simp [hspos.ne']
  have hbeta :
    (4 * (81470555 / 100000000 : ℝ) / 9) * s + (2 / 5 : ℝ) * s =
      (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10) * s := by
    ring
  have hstrict :
    ((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) * R <
      (161 / 600 : ℝ) * L + (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10) * s + 29 := by
    nlinarith only [hcombine, hC', hE1, hE2, herror, hrootTerm, hbeta]
  nlinarith only [hroot, hstrict]

/-- A pass-containing subgroup of index four and conductor cost at most `2L`
forces a rejecting prime below the Gamma index-100 cutoff from `L ≥ 330`.
Use the scaled `21/10` Gaussian comparison at exactly the same final cutoff. -/
theorem exists_prime_witness_le_gammaIndex100_of_index_four_conductor {n : ℕ} [NeZero n]
    (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 330 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let R := gammaIndex100GaussianRadius L
  let s := Real.sqrt R
  let x := R ^ 2
  let h := 1 / (3 * s)
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(21 / 10 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  let A := LLS.PaperStatements.gaussianAmbientErrorPrefix1000 n x
  have hcut : (21 / 10 : ℝ) * x = gammaIndex100Bound (Real.log n) := by
    dsimp only [x, R, gammaIndex100GaussianRadius, gammaIndex100Bound, L]
    rw [mul_pow, Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 33 / 28)]
    ring
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (21 / 10 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hpbound
    rw [hcut] at hpbound
    by_contra hfail
    exact hnone ⟨p, hp, hpbound, hfail⟩
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ n → ⌊(21 / 10 : ℝ) * x⌋₊ < p := by
    intro p hp hpdvd
    apply lt_of_not_ge
    intro hfloor
    have hpbound : (p : ℝ) ≤ (21 / 10 : ℝ) * x := (Nat.le_floor_iff' hp.ne_zero).mp hfloor
    exact
      PrimeTest.strongMillerRabinPass_not_of_prime_dvd
        (lt_of_lt_of_le (by decide : 1 < 20000) hnlarge) hnOdd hp hpdvd (hpass p hp hpbound)
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ (21 / 10 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hRbounds := gammaIndex100GaussianRadius_linear_bounds hL
  have hR184 : 184 ≤ R := by
    dsimp only [R, L] at hRbounds ⊢
    nlinarith only [hL, hRbounds.1]
  have hRpos : 0 < R := by linarith only [hR184]
  have hspos : 0 < s := by
    dsimp only [s]
    exact Real.sqrt_pos.2 hRpos
  have hssq : s ^ 2 = R := by
    dsimp only [s]
    exact Real.sq_sqrt hRpos.le
  have hsLower : 27 / 2 ≤ s := by nlinarith only [hssq, hR184, hspos]
  have hh : h = 1 / (3 * s) := by rfl
  have hhpos : 0 < h := by
    rw [hh]; positivity
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsLower]
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hR184]
  have hX : 1000 ≤ (21 / 10 : ℝ) * x := by
    dsimp only [x]
    nlinarith only [hR184]
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative_prefix1000_gain hnlarge H hGRH
      hhpos hh1 hx (by norm_num only : (0 : ℝ) ≤ 21 / 10) hX hdiv hsmall
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  have hcmp' :
    (4 * (1 - h) * I - E) * R ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / R) * E) +
        13 +
        3 * A := by
    dsimp only [I, E, A, x] at hcmp
    simpa only [hindex, hi, Nat.cast_ofNat, Nat.reduceSub, Real.sqrt_sq hRpos.le] using hcmp
  have hI : 81470555 / 100000000 ≤ I := by
    dsimp only [I]
    exact LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le
  have hE : E ≤ 2129 / 2000 := by
    dsimp only [E]
    exact Analysis.gaussian_endpoint_exp_le
  have hA : A ≤ 29 := by
    dsimp only [A, x, R, L]
    exact
      (gammaIndex100GaussianAmbientErrorPrefix1000_lt hL rfl).le.trans
        (by norm_num only : (22 : ℝ) ≤ 29)
  have hC' : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * L := by
    dsimp only [L]
    exact hC
  have hRlo : (14 / 25 : ℝ) * L ≤ R := by exact hRbounds.1
  have hRhi : R ≤ (3 / 5 : ℝ) * L := by exact hRbounds.2
  exact
    gammaIndex100GaussianTripleComparisonImpossible hL hRlo hRhi (le_of_lt hspos) hssq hA hC' hI hE
      hh hh1 hcmp'

/-- For `L ≥ 200`, an index-four pass-containing subgroup with conductor cost
at most `2L` has a rejecting prime below the internal residual-29 cutoff. -/
theorem exists_prime_witness_le_gammaIndex100GaussianTripleBound29_of_index_four_conductor {n : ℕ}
    [NeZero n] (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 200 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * (gammaIndex100GaussianTripleRadius29 (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  have hExp10 : (11 : ℝ) ≤ Real.exp 10 := by
    have h := Real.add_one_le_exp (10 : ℝ)
    norm_num only at h
    exact h
  have hpow : (20000 : ℝ) < (11 : ℝ) ^ 20 := by norm_num only
  have hexp : Real.exp (200 : ℝ) = Real.exp 10 ^ 20 := by
    rw [show (200 : ℝ) = (20 : ℕ) * 10 by norm_num only]
    exact Real.exp_nat_mul 10 20
  have hExp200 : (20000 : ℝ) < Real.exp (200 : ℝ) := by
    rw [hexp]
    exact hpow.trans_le (pow_le_pow_left₀ (by norm_num only) hExp10 20)
  have hlog20000 : Real.log (20000 : ℝ) < 200 :=
    (Real.log_lt_iff_lt_exp (by norm_num only)).2 hExp200
  have hnlarge : 20000 ≤ n := by
    by_contra hnot
    have hnlt : n < 20000 := Nat.lt_of_not_ge hnot
    have hloglt : Real.log (n : ℝ) < Real.log (20000 : ℝ) :=
      Real.log_lt_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))) (Nat.cast_lt.mpr hnlt)
    exact (not_lt_of_ge hL) (hloglt.trans hlog20000)
  let L := Real.log n
  let R := gammaIndex100GaussianTripleRadius29 L
  let s := Real.sqrt R
  let x := R ^ 2
  let h := 1 / (3 * s)
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(21 / 10 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  let A := LLS.PaperStatements.gaussianAmbientErrorPrefix1000 n x
  have hcut : (21 / 10 : ℝ) * x = gammaIndex100GaussianTripleBound29 (Real.log n) := by
    dsimp only [x, R, gammaIndex100GaussianTripleBound29, L]
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (21 / 10 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hpbound
    rw [hcut] at hpbound
    by_contra hfail
    exact hnone ⟨p, hp, hpbound, hfail⟩
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ n → ⌊(21 / 10 : ℝ) * x⌋₊ < p := by
    intro p hp hpdvd
    apply lt_of_not_ge
    intro hfloor
    have hpbound : (p : ℝ) ≤ (21 / 10 : ℝ) * x := (Nat.le_floor_iff' hp.ne_zero).mp hfloor
    exact
      PrimeTest.strongMillerRabinPass_not_of_prime_dvd
        (lt_of_lt_of_le (by decide : 1 < 20000) hnlarge) hnOdd hp hpdvd (hpass p hp hpbound)
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ (21 / 10 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hRlower : (9 / 25 : ℝ) * L + 50 ≤ R :=
    gammaIndex100GaussianTripleRadius29_lower
      (by
        dsimp only [L]; exact hL)
  have hR122 : 122 ≤ R := by
    dsimp only [L, R] at hRlower ⊢
    nlinarith only [hL, hRlower]
  have hRpos : 0 < R := by linarith only [hR122]
  have hspos : 0 < s := by
    dsimp only [s]; exact Real.sqrt_pos.2 hRpos
  have hssq : s ^ 2 = R := by
    dsimp only [s]; exact Real.sq_sqrt hRpos.le
  have hh : h = 1 / (3 * s) := by rfl
  have hhpos : 0 < h := by
    rw [hh]; positivity
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hspos, hssq, hR122]
  have hx : 4 ≤ x := by
    dsimp only [x]; nlinarith only [hR122]
  have hX : 1000 ≤ (21 / 10 : ℝ) * x := by
    dsimp only [x]
    nlinarith only [hR122]
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative_prefix1000_gain hnlarge H hGRH
      hhpos hh1 hx (by norm_num only : (0 : ℝ) ≤ 21 / 10) hX hdiv hsmall
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  have hcmp' :
    (4 * (1 - h) * I - E) * R ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / R) * E) +
        13 +
        3 * A := by
    dsimp only [I, E, A, x] at hcmp
    simpa only [hindex, hi, Nat.cast_ofNat, Nat.reduceSub, Real.sqrt_sq hRpos.le] using hcmp
  have hI : 81470555 / 100000000 ≤ I := by
    dsimp only [I]
    exact LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le
  have hE : E ≤ 2129 / 2000 := by
    dsimp only [E]
    exact Analysis.gaussian_endpoint_exp_le
  have hA : A ≤ 23 := by
    dsimp only [A, x, R, L]
    exact (gammaIndex100GaussianTripleAmbientErrorPrefix1000_lt hL rfl).le
  have hC' : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * L := by
    dsimp only [L]
    exact hC
  have hrootProps := gammaIndex100GaussianTripleRadius29_properties hL
  have hRsqrt : Real.sqrt R = s := by dsimp only [s]
  have hroot :
    ((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) * R -
        (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10) * s -
        (161 / 600 : ℝ) * L -
        29 =
      0 := by
    have hrootEq := hrootProps.2
    change
      ((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) / 3) * R -
          (4 / 3 : ℝ) * ((81470555 / 100000000 : ℝ) / 3 + 3 / 10) * Real.sqrt R -
          (161 / 600 : ℝ) * L -
          29 =
        0 at hrootEq
    rw [hRsqrt] at hrootEq
    exact hrootEq
  exact
    gammaIndex100GaussianTripleComparisonImpossiblePrefix1000 hL hRlower (le_of_lt hspos) hssq hA
      hC' hI hE hh hh1 hroot hcmp'

end PseudoPrime.PrimeTestBounds.MillerRabin
