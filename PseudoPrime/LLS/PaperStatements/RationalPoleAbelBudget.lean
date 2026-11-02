/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleAbelWitness
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Stable half-line budget for the double-Abel fourth-pole bound

The scalar estimates use the improved principal error and retain the existing character
and ambient local costs. A rational certificate at its squared root entrance extends to
all larger logarithmic scales using monotonicity. The three selected certificate rows are
kept in a downstream module, so changing an entrance does not rebuild this scalar proof.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Rational-parameter entrance data for the selected K4 double-Abel witness bound.
The coefficient and root comparisons control x=c*L^2, the squared entrance lies in
the stable budget domain, and the power-of-two comparison bounds its logarithm.
The strict margin invariant pays all scalar errors at that entrance and therefore
on the whole upper half-line. Concrete rows supply closed actual-witness consumers. -/
structure FourPoleAbelRow where
  /-- The coefficient of the squared logarithmic cutoff. -/
  coefficient : ℝ
  /-- A lower bound for the coefficient's nonnegative square root. -/
  sqrtLower : ℝ
  /-- An upper bound for the coefficient's nonnegative fourth root. -/
  quarterUpper : ℝ
  /-- The positive square root of the minimum logarithmic scale. -/
  rootEntrance : ℝ
  /-- A natural exponent bounding the entrance by a power of two. -/
  logPower : ℕ
  /-- The coefficient stays in the selected K4 certificate range. -/
  coefficient_lower : (777 / 1000 : ℝ) ≤ coefficient
  /-- The cutoff does not exceed the squared logarithmic scale. -/
  coefficient_upper : coefficient ≤ 1
  /-- The lower square root is at least one half. -/
  sqrtLower_lower : (1 / 2 : ℝ) ≤ sqrtLower
  /-- The upper fourth root is nonnegative. -/
  quarterUpper_nonneg : 0 ≤ quarterUpper
  /-- The lower square root squares below the coefficient. -/
  sqrtLower_sq : sqrtLower ^ 2 ≤ coefficient
  /-- The upper fourth root's fourth power covers the coefficient. -/
  quarterUpper_pow : coefficient ≤ quarterUpper ^ 4
  /-- The root entrance is strictly positive. -/
  rootEntrance_pos : 0 < rootEntrance
  /-- The squared entrance is at least the stable scalar threshold. -/
  scale_lower : (1682 : ℝ) ≤ rootEntrance ^ 2
  /-- The squared entrance is bounded by the chosen power of two. -/
  logPower_upper : rootEntrance ^ 2 ≤ (2 : ℝ) ^ logPower
  /-- The entrance leaves a strict rational margin above all scalar errors. -/
  margin :
    2 * quarterUpper * rootEntrance + (5332501 / 5000 : ℝ) +
        (40 * logPower / sqrtLower) * (1 + 2 / rootEntrance ^ 2) <
      ((28379 / 100000 : ℝ) * sqrtLower - 2501 / 10000) * rootEntrance ^ 2

/-- The complete selected K4 scalar budget at x=c*L^2.
Inputs are the coefficient, logarithmic scale, primitive-conductor logarithm and
original-level logarithm. The improved principal error is 2*x^(1/4)+14; character
and ambient local coefficients are unchanged. This budget is paid before witness extraction. -/
noncomputable def fourPoleAbelBudget (c L F G : ℝ) : ℝ :=
  let x := c * L ^ 2
  (2501 / 10000 : ℝ) * F + 1003 + (24 * F + 793) * x ^ (-3 / 4 : ℝ) + (2 * x ^ (1 / 4 : ℝ) + 14) +
    (20 / Real.sqrt x) * (Real.log x / Real.log 2) * G

/-- Any certified scale has the explicit root, quarter-power, negative-power and
logarithmic comparisons displayed below. The certificate ensures L>=1682, so the
fixed K4 coefficient range and root guards imply every comparison.
These bounds isolate the scalar errors without using a former finite entrance. -/
theorem fourPole_abel_scale_bounds (f : FourPoleAbelRow) {L : ℝ} (hL : f.rootEntrance ^ 2 ≤ L) :
    let x := f.coefficient * L ^ 2
    L ≤ x ∧
      x ≤ L ^ 2 ∧
      f.sqrtLower * L ≤ Real.sqrt x ∧
      x ^ (1 / 4 : ℝ) ≤ f.quarterUpper * Real.sqrt L ∧
      x ^ (-3 / 4 : ℝ) ≤ 2 / L ∧ Real.log x ≤ 2 * Real.log L := by
  let x := f.coefficient * L ^ 2
  have hLb : (1682 : ℝ) ≤ L := f.scale_lower.trans hL
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 1682).trans_le hLb
  have hr0 : 0 < f.sqrtLower := (by norm_num only : (0 : ℝ) < 1 / 2).trans_le f.sqrtLower_lower
  have hxl : L ≤ x := by
    have hm := mul_le_mul_of_nonneg_right f.coefficient_lower (sq_nonneg L)
    dsimp only [x]
    nlinarith only [hm, hLb, sq_nonneg (L - 2)]
  have hxu : x ≤ L ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right f.coefficient_upper (sq_nonneg L)
  have hx0 : 0 < x := hL0.trans_le hxl
  have hsl : f.sqrtLower * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg hr0.le hL0.le) hx0.le).mpr
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right f.sqrtLower_sq (sq_nonneg L)
  have hquarter : x ^ (1 / 4 : ℝ) ≤ f.quarterUpper * Real.sqrt L := by
    have hsL4 : Real.sqrt L ^ 4 = L ^ 2 := by
      calc
        _ = (Real.sqrt L ^ 2) ^ 2 := by ring
        _ = _ := congrArg (fun z : ℝ ↦ z ^ 2) (Real.sq_sqrt hL0.le)
    have hbound : x ≤ (f.quarterUpper * Real.sqrt L) ^ 4 := by
      rw [mul_pow, hsL4]
      exact mul_le_mul_of_nonneg_right f.quarterUpper_pow (sq_nonneg L)
    have h := Real.rpow_le_rpow hx0.le hbound (by norm_num only : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast (f.quarterUpper * Real.sqrt L) 4, ←
      Real.rpow_mul (mul_nonneg f.quarterUpper_nonneg (Real.sqrt_nonneg L))] at h
    norm_num only [Real.rpow_one] at h
    exact h
  have hnegative : x ^ (-3 / 4 : ℝ) ≤ 2 / L := by
    have hx1 : 1 ≤ x := (by linarith only [hLb] : (1 : ℝ) ≤ L).trans hxl
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num only : (-3 / 4 : ℝ) ≤ -(1 / 2))
    rw [Real.rpow_neg hx0.le] at h
    have hn : x ^ (-3 / 4 : ℝ) ≤ 1 / Real.sqrt x := by
      simpa only [Real.sqrt_eq_rpow, one_div] using h
    have hhalf := mul_le_mul_of_nonneg_right f.sqrtLower_lower hL0.le
    have hd : 1 / Real.sqrt x ≤ 2 / L :=
      (div_le_div_iff₀ (Real.sqrt_pos.mpr hx0) hL0).mpr (by linarith only [hsl, hhalf])
    exact hn.trans hd
  have hlog : Real.log x ≤ 2 * Real.log L := by
    have h := Real.log_le_log hx0 hxu
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  exact ⟨hxl, hxu, hsl, hquarter, hnegative, hlog⟩

/-- Above a certified entrance, log(L)/log(2) is at most k*L/S^2.
Use the certificate's power-of-two bound at S^2 and antitonicity of log(L)/L.
This transports the local logarithmic budget to the entire upper half-line. -/
theorem fourPole_abel_log_ratio (f : FourPoleAbelRow) {L : ℝ} (hL : f.rootEntrance ^ 2 ≤ L) :
    Real.log L / Real.log 2 ≤ (f.logPower : ℝ) * L / f.rootEntrance ^ 2 := by
  have hE0 : 0 < f.rootEntrance ^ 2 := (by norm_num only : (0 : ℝ) < 1682).trans_le f.scale_lower
  have hL0 := hE0.trans_le hL
  have hlow : (1 : ℝ) ≤ Real.log (f.rootEntrance ^ 2) := by
    have h4 :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 4)
        (by linarith only [f.scale_lower] : (4 : ℝ) ≤ f.rootEntrance ^ 2)
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num only, Real.log_pow] at h4
    norm_num only [Nat.cast_ofNat] at h4
    linarith only [h4, Real.log_two_gt_d9]
  have he : Real.exp 1 ≤ f.rootEntrance ^ 2 := (Real.le_log_iff_exp_le hE0).mp hlow
  have ht := Real.log_div_self_antitoneOn he (he.trans hL) hL
  have hcap := Real.log_le_log hE0 f.logPower_upper
  rw [Real.log_pow (2 : ℝ) f.logPower] at hcap
  have hratio := ht.trans (div_le_div_of_nonneg_right hcap hE0.le)
  have hclear := (div_le_iff₀ hL0).mp hratio
  apply (div_le_iff₀ (Real.log_pos (by norm_num only : (1 : ℝ) < 2))).mpr
  exact hclear.trans_eq (by ring)

/-- For conductor and ambient logarithms at most L+2, the complete scalar budget
is bounded by its linear term and the displayed quarter-root, constant and local errors.
Use the scale comparisons, retain the original local coefficient, and bound the
negative-power term by 49. This is the stable scalar estimate shared by all entrance rows. -/
theorem fourPole_abel_budget_le (f : FourPoleAbelRow) {L F G : ℝ} (hL : f.rootEntrance ^ 2 ≤ L)
    (hF : F ≤ L + 2) (hG : G ≤ L + 2) :
    fourPoleAbelBudget f.coefficient L F G ≤
      (2501 / 10000 : ℝ) * L +
        (2 * f.quarterUpper * Real.sqrt L + (5332501 / 5000 : ℝ) +
          (40 / f.sqrtLower) * (Real.log L / Real.log 2) * (1 + 2 / L)) := by
  let x := f.coefficient * L ^ 2
  have hLb : (1682 : ℝ) ≤ L := f.scale_lower.trans hL
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 1682).trans_le hLb
  have hr0 : 0 < f.sqrtLower := (by norm_num only : (0 : ℝ) < 1 / 2).trans_le f.sqrtLower_lower
  obtain ⟨hxl, _hxu, hroot, hp, hn, hlog⟩ := fourPole_abel_scale_bounds f hL
  have hx0 : 0 < x := hL0.trans_le hxl
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg ((by linarith only [hLb] : (1 : ℝ) ≤ L).trans hxl)
  have hmain := mul_le_mul_of_nonneg_left hF (by norm_num only : (0 : ℝ) ≤ 2501 / 10000)
  have hneg : (24 * F + 793) * x ^ (-3 / 4 : ℝ) ≤ 49 := by
    calc
      _ ≤ (24 * L + 841) * x ^ (-3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hF]) (Real.rpow_nonneg hx0.le _)
      _ ≤ (24 * L + 841) * (2 / L) := mul_le_mul_of_nonneg_left hn (by linarith only [hLb])
      _ = (48 * L + 1682) / L := by ring
      _ ≤ 49 := (div_le_iff₀ hL0).mpr (by linarith only [hLb])
  have hquarter := mul_le_mul_of_nonneg_left hp (by norm_num only : (0 : ℝ) ≤ 2)
  have hden : 20 / Real.sqrt x ≤ 20 / (f.sqrtLower * L) :=
    (div_le_div_iff₀ hsx (mul_pos hr0 hL0)).mpr (by linarith only [hroot])
  have hlogcap : Real.log x / Real.log 2 ≤ (2 * Real.log L) / Real.log 2 :=
    div_le_div_of_nonneg_right hlog hl2.le
  have hlocal :
    (20 / Real.sqrt x) * (Real.log x / Real.log 2) * G ≤
      (40 / f.sqrtLower) * (Real.log L / Real.log 2) * (1 + 2 / L) := by
    have h1 :=
      mul_le_mul_of_nonneg_left hG
        (mul_nonneg (div_nonneg (by norm_num only : (0 : ℝ) ≤ 20) hsx.le) (div_nonneg hlogx hl2.le))
    have h2 :=
      mul_le_mul hden hlogcap (div_nonneg hlogx hl2.le)
        (div_nonneg (by norm_num only : (0 : ℝ) ≤ 20) (mul_nonneg hr0.le hL0.le))
    have h3 := mul_le_mul_of_nonneg_right h2 (by linarith only [hLb] : 0 ≤ L + 2)
    exact
      h1.trans
        (h3.trans_eq
          (by
            field_simp (disch :=
              first
              | exact hr0.ne'
              | exact hL0.ne'
              | exact hl2.ne'
              | norm_num only)
            ring))
  change
    (2501 / 10000 : ℝ) * F + 1003 + (24 * F + 793) * x ^ (-3 / 4 : ℝ) + (2 * x ^ (1 / 4 : ℝ) + 14) +
        (20 / Real.sqrt x) * (Real.log x / Real.log 2) * G ≤
      _
  nlinarith only [hmain, hneg, hquarter, hlocal]

/-- Every scale above a certified squared entrance retains the strict scalar margin.
The square-root term, constant term, log(L)/L and 1+2/L decrease after normalization;
rescale the certified entrance inequality to L.
This closes the whole upper half-line from one exact rational certificate. -/
theorem fourPole_abel_margin (f : FourPoleAbelRow) {L : ℝ} (hL : f.rootEntrance ^ 2 ≤ L) :
    2 * f.quarterUpper * Real.sqrt L + (5332501 / 5000 : ℝ) +
        (40 / f.sqrtLower) * (Real.log L / Real.log 2) * (1 + 2 / L) <
      ((28379 / 100000 : ℝ) * f.sqrtLower - 2501 / 10000) * L := by
  have hLb : (1682 : ℝ) ≤ L := f.scale_lower.trans hL
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 1682).trans_le hLb
  have hS0 := f.rootEntrance_pos
  have hE0 : 0 < f.rootEntrance ^ 2 := pow_pos hS0 2
  have hr0 : 0 < f.sqrtLower := (by norm_num only : (0 : ℝ) < 1 / 2).trans_le f.sqrtLower_lower
  have hroot : f.rootEntrance ≤ Real.sqrt L := (Real.le_sqrt hS0.le hL0.le).mpr hL
  have hrootcap : Real.sqrt L ≤ L / f.rootEntrance := by
    apply (le_div_iff₀ hS0).mpr
    have h := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg L)
    nlinarith only [h, Real.sq_sqrt hL0.le]
  have hquarter :
    2 * f.quarterUpper * Real.sqrt L ≤
      (2 * f.quarterUpper * f.rootEntrance) * (L / f.rootEntrance ^ 2) := by
    have h :=
      mul_le_mul_of_nonneg_left hrootcap
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) f.quarterUpper_nonneg)
    exact
      h.trans_eq
        (by
          field_simp (disch :=
            first
            | exact hS0.ne'
            | norm_num only))
  have hscale : 1 ≤ L / f.rootEntrance ^ 2 :=
    (le_div_iff₀ hE0).mpr (by simpa only [one_mul] using hL)
  have hconstant : (5332501 / 5000 : ℝ) ≤ (5332501 / 5000 : ℝ) * (L / f.rootEntrance ^ 2) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hscale (by norm_num only : (0 : ℝ) ≤ 5332501 / 5000)
  have hfactor : 1 + 2 / L ≤ 1 + 2 / f.rootEntrance ^ 2 := by
    exact add_le_add (le_refl (1 : ℝ)) ((div_le_div_iff₀ hL0 hE0).mpr (by linarith only [hL]))
  have hlog := fourPole_abel_log_ratio f hL
  have hprod :=
    mul_le_mul hlog hfactor (add_nonneg zero_le_one (div_nonneg (by norm_num only) hL0.le))
      (div_nonneg (mul_nonneg (Nat.cast_nonneg f.logPower) hL0.le) hE0.le)
  have hlocal :
    (40 / f.sqrtLower) * (Real.log L / Real.log 2) * (1 + 2 / L) ≤
      ((40 * f.logPower / f.sqrtLower) * (1 + 2 / f.rootEntrance ^ 2)) *
        (L / f.rootEntrance ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hprod (div_nonneg (by norm_num only : (0 : ℝ) ≤ 40) hr0.le)
    calc
      _ ≤
          (40 / f.sqrtLower) *
            (((f.logPower : ℝ) * L / f.rootEntrance ^ 2) * (1 + 2 / f.rootEntrance ^ 2)) :=
        by simpa only [mul_assoc] using h
      _ = _ := by ring
  have hmargin := mul_lt_mul_of_pos_right f.margin (div_pos hL0 hE0)
  have hmargin' :
    (2 * f.quarterUpper * f.rootEntrance + (5332501 / 5000 : ℝ) +
          (40 * f.logPower / f.sqrtLower) * (1 + 2 / f.rootEntrance ^ 2)) *
        (L / f.rootEntrance ^ 2) <
      ((28379 / 100000 : ℝ) * f.sqrtLower - 2501 / 10000) * L := by
    exact
      hmargin.trans_eq
        (by
          field_simp (disch :=
            first
            | exact hS0.ne'
            | norm_num only))
  nlinarith only [hquarter, hconstant, hlocal, hmargin']

/-- A certified row and conductor/ambient logarithms at most L+2 pay the complete
budget below the actual unchanged K4 principal main gap at x=c*L^2.
Combine the half-line margin with the existing unconditional main-coefficient certificate.
This supplies a strict scalar hypothesis for the actual double-Abel witness criterion. -/
theorem fourPole_abel_scale_gap (f : FourPoleAbelRow) {L F G : ℝ} (hL : f.rootEntrance ^ 2 ≤ L)
    (hF : F ≤ L + 2) (hG : G ≤ L + 2) :
    fourPoleAbelBudget f.coefficient L F G <
      Real.sqrt (f.coefficient * L ^ 2) *
        (2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
          (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4)) := by
  have hb := fourPole_abel_budget_le f hL hF hG
  have hm := fourPole_abel_margin f hL
  have hroot := (fourPole_abel_scale_bounds f hL).2.2.1
  have hmain := rationalPole_four_principal_gap
  have he :
    (rationalPoleFourKernel.function (1 / 2)).re =
      2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4 := by
    rw [rationalPoleFourKernel, rationalPole_half_value]
  rw [rationalPole_four_cutoff, he] at hmain
  calc
    _ < (28379 / 100000 : ℝ) * (f.sqrtLower * L) := by nlinarith only [hb, hm]
    _ ≤ (28379 / 100000 : ℝ) * Real.sqrt (f.coefficient * L ^ 2) :=
      mul_le_mul_of_nonneg_left hroot (by norm_num only)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hmain (Real.sqrt_nonneg (f.coefficient * L ^ 2))
      nlinarith only [h]

end PseudoPrime.LLS.PaperStatements
