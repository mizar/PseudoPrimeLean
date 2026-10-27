/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRRelativeNumerics
public import PseudoPrime.LLS.GammaNonOneRefinedNumerics

/-! # Variable-radius relative Gaussian MR budgets

The radius uses the logarithmic scale and its square root. Rational bounds on
the radius, the ambient error, and the normalized subgroup comparison prove
the half-line estimate from `analysis10.md`.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The variable Gaussian endpoint width converts the integral and endpoint
constants into a normalized main-term lower bound. -/
theorem gaussianMRVariable_normalized_main_lower {u v s I E h : ℝ} (huv : u = 1 + v) (hv0 : 0 ≤ v)
    (hv3 : v ≤ 1 / 3) (hs : 0 < s) (hh : h = 1 / (3 * s)) (hh1 : h ≤ 1 / 2) (hI : 8147 / 10000 ≤ I)
    (hE : E ≤ 2129 / 2000) :
    21943 / 30000 - (4 / 9 * (8147 / 10000)) / s ≤ u * (1 - h) * I - v * E := by
  have hfactor : 0 ≤ 1 - h := by linarith only [hh1]
  have hU : 0 ≤ u := by
    rw [huv]; linarith only [hv0]
  have hh0 : 0 ≤ h := by
    rw [hh]; positivity
  have hI0 : (8147 / 10000 : ℝ) ≤ 1 := by norm_num only
  have hE0' : (1 : ℝ) ≤ 2129 / 2000 := by norm_num only
  have hbaseUpper : (1 - h) * (8147 / 10000) ≤ 2129 / 2000 := by
    have hmul := mul_le_mul_of_nonneg_left hI0 hfactor
    nlinarith only [hmul, hh0, hE0']
  have hI' : u * (1 - h) * (8147 / 10000) ≤ u * (1 - h) * I := by
    calc
      _ = (u * (1 - h)) * (8147 / 10000) := by ring
      _ ≤ (u * (1 - h)) * I := mul_le_mul_of_nonneg_left hI (mul_nonneg hU hfactor)
      _ = _ := by ring
  have hE' := mul_le_mul_of_nonneg_left hE hv0
  have hgap := mul_le_mul_of_nonneg_right (sub_nonpos.mpr hbaseUpper) (sub_nonneg.mpr hv3)
  have hbase :
    u * ((1 - h) * (8147 / 10000)) - v * (2129 / 2000) =
      (1 - h) * (8147 / 10000) + v * ((1 - h) * (8147 / 10000) - 2129 / 2000) := by
    rw [huv]
    ring
  have hgap' :
    (1 - h) * (8147 / 10000) + (1 / 3) * ((1 - h) * (8147 / 10000) - 2129 / 2000) ≤
      (1 - h) * (8147 / 10000) + v * ((1 - h) * (8147 / 10000) - 2129 / 2000) := by
    nlinarith only [hgap]
  have hEq :
    (4 / 3) * (1 - h) * (8147 / 10000) - (1 / 3) * (2129 / 2000) =
      21943 / 30000 - (4 / 9 * (8147 / 10000)) / s := by
    rw [hh]
    field_simp
    ring
  have hI'' : u * ((1 - h) * (8147 / 10000)) ≤ u * (1 - h) * I := by
    calc
      _ = u * (1 - h) * (8147 / 10000) := by ring
      _ ≤ _ := hI'
  calc
    _ = (4 / 3) * (1 - h) * (8147 / 10000) - (1 / 3) * (2129 / 2000) := hEq.symm
    _ = (1 - h) * (8147 / 10000) + (1 / 3) * ((1 - h) * (8147 / 10000) - 2129 / 2000) := by ring
    _ ≤ _ := hgap'
    _ = u * ((1 - h) * (8147 / 10000)) - v * (2129 / 2000) := hbase.symm
    _ ≤ _ := sub_le_sub hI'' hE'

/-- For a real index `m ≥ 4`, retain its exact factor `m/(m-1)` in the
normalized Gaussian main term. -/
theorem gaussianMRStar_normalized_main_lower {m t s I E h : ℝ} (hm : 4 ≤ m) (ht : t = m - 1)
    (hs : 0 < s) (hh : h = 1 / (3 * s)) (hh1 : h ≤ 1 / 2) (hI : 81470555 / 100000000 ≤ I)
    (hE : E ≤ 2129 / 2000) :
    ((m * (81470555 / 100000000) - 2129 / 2000) / t - (m * (81470555 / 100000000)) / (3 * t * s)) ≤
      (m / t) * (1 - h) * I - E / t := by
  exact gaussianMR_normalized_main_lower_of_mass hm ht hs hh hh1 hI hE

/-- The variable Gaussian error bracket is bounded using the endpoint
exponential estimate and the exact width and scale substitutions. -/
theorem gaussianMRVariable_error_bracket_upper {s r h E : ℝ} (hs : 0 < s) (hr : r = s ^ 2)
    (hh : h = 1 / (3 * s)) (hE : E ≤ 2129 / 2000) :
    (4 / 3) * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) ≤
      (2 / 5) * s + 44709 / (5000 * s) + 1305077 / (500000 * r) := by
  have hrpos : 0 < r := by
    rw [hr]; positivity
  have hcoef : 0 ≤ (21 / (10 * h) + 1839 / 1000) / r := by
    rw [hh]
    positivity
  have hterm := mul_le_mul_of_nonneg_left hE hcoef
  rw [hh, hr] at hterm ⊢
  field_simp at hterm ⊢
  nlinarith only [hterm, hs]

/-- The proposed Gaussian radius at logarithmic scale `L`.
It combines a linear term, a square-root correction, and a fixed offset. -/
noncomputable def gaussianMRVariableRadius (L : ℝ) : ℝ :=
  (5503 / 10000 : ℝ) * L + (4 / 5 : ℝ) * Real.sqrt L + 46

/-- For `L ≥ 4000`, the variable radius is at least `L/2`.
The linear coefficient alone exceeds one half, and the other terms are
nonnegative. -/
theorem gaussianMRVariableRadius_half {L : ℝ} (hL : 4000 ≤ L) :
    L / 2 ≤ gaussianMRVariableRadius L := by
  dsimp only [gaussianMRVariableRadius]
  nlinarith only [hL, Real.sqrt_nonneg L]

/-- For `L ≥ 4000`, the variable radius is at most `361L/625`.
First use `sqrt L ≤ L/60` and then compare the rational linear coefficients. -/
theorem gaussianMRVariableRadius_upper {L : ℝ} (hL : 4000 ≤ L) :
    gaussianMRVariableRadius L ≤ (361 / 625 : ℝ) * L := by
  have hs : Real.sqrt L ≤ L / 60 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact div_nonneg (by linarith only [hL]) (by norm_num only)
    · nlinarith only [hL]
  dsimp only [gaussianMRVariableRadius]
  nlinarith only [hL, hs]

/-- For `L ≥ 4000`, the square root of the radius is at most
`(19/25) sqrt L`. Square the nonnegative sides and use the radius bound. -/
theorem gaussianMRVariableRadius_sqrt_upper {L : ℝ} (hL : 4000 ≤ L) :
    Real.sqrt (gaussianMRVariableRadius L) ≤ (19 / 25 : ℝ) * Real.sqrt L := by
  have hr := gaussianMRVariableRadius_upper hL
  have hL0 : 0 ≤ L := by linarith only [hL]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (by norm_num only) (Real.sqrt_nonneg L)
  · rw [mul_pow, Real.sq_sqrt hL0]
    nlinarith only [hr]

/-- For `L ≥ 4000`, the square root of the radius is at least `20`.
The radius is at least `2000`, so the squared comparison gives the claim. -/
theorem gaussianMRVariableRadius_sqrt_lower {L : ℝ} (hL : 4000 ≤ L) :
    20 ≤ Real.sqrt (gaussianMRVariableRadius L) := by
  have hr : 2000 ≤ gaussianMRVariableRadius L := by
    dsimp only [gaussianMRVariableRadius]
    nlinarith only [hL, Real.sqrt_nonneg L]
  apply (Real.le_sqrt (by norm_num only) (by linarith only [hr])).mpr
  nlinarith only [hr]

/-- For `L ≥ 4000`, the squared radius is large enough to use the
`5/2`-anchored decay estimate for the ambient error. -/
theorem gaussianMRVariableRadius_pow_anchor {L : ℝ} (hL : 4000 ≤ L) :
    (5 / 2 : ℝ) ^ 16 ≤ gaussianMRVariableRadius L ^ 2 := by
  have hr : 2000 ≤ gaussianMRVariableRadius L := by
    dsimp only [gaussianMRVariableRadius]
    nlinarith only [hL, Real.sqrt_nonneg L]
  have hpow : (5 / 2 : ℝ) ^ 16 ≤ 2000 ^ 2 := by norm_num only
  nlinarith only [hpow, hr, sq_nonneg (gaussianMRVariableRadius L - 2000)]

/-- If `log q ≤ L` and `L ≥ 4000`, the ambient Gaussian error at the
variable scale is at most `28`. Bound its pole contribution by `3` and its
left-moment contribution by `5`, using the `5/2` decay anchor. -/
theorem gaussianMRVariable_ambient_error_le {q : ℕ} {L : ℝ} (hL : 4000 ≤ L) (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientError q (gaussianMRVariableRadius L ^ 2) ≤ 28 := by
  let r := gaussianMRVariableRadius L
  have hrdef : r = gaussianMRVariableRadius L := rfl
  have hrL : L / 2 ≤ r := gaussianMRVariableRadius_half hL
  have hrpos : 0 < r := by
    have hLpos : 0 < L := by linarith only [hL]
    exact lt_of_lt_of_le (div_pos hLpos (by norm_num only)) hrL
  have hsqrt : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hrpos.le
  have hx := gaussianMRVariableRadius_pow_anchor hL
  have hP : (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / r) ≤ 3 := by
    rw [← mul_div_assoc, div_le_iff₀ hrpos]
    nlinarith only [hL, hq, hrL]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 5 / 2) (by norm_num only)
      hx
  have hC : 0 ≤ (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) := by
    have hlog := Real.log_natCast_nonneg q
    linarith only [hlog]
  have hb := mul_le_mul_of_nonneg_left hdec hC
  have hB : (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) / ((5 / 2 : ℝ) * r) ≤ 5 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) hrpos)).mpr
    nlinarith only [hL, hq, hrL]
  rw [hsqrt] at hb
  have hb' :
    (11 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) ≤
      (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) / ((5 / 2 : ℝ) * r) := by
    simp only [div_eq_mul_inv] at hb hB ⊢
    nlinarith only [hb, hB]
  have hdecay := hb'.trans hB
  rw [← hrdef]
  dsimp only [LLS.PaperStatements.gaussianAmbientError]
  rw [hsqrt]
  have hconstant : (12871 / 1000 : ℝ) + 64 / 9 + 3 + 5 ≤ 28 := by norm_num only
  linarith only [hP, hdecay, hconstant]

/-- The proposed radius makes the normalized index-four Gaussian comparison
impossible on `L ≥ 4000`. Bound inverse-radius terms by fixed rational values;
the three coefficient differences against the proposed radius are positive. -/
theorem gaussianMRVariable_comparison_impossible {L : ℝ} (hL : 4000 ≤ L) {A : ℝ} (hA : A ≤ 28) :
    ¬((21943 / 30000 : ℝ) * gaussianMRVariableRadius L ≤
        (161 / 400 : ℝ) * L + (17147 / 22500 : ℝ) * Real.sqrt (gaussianMRVariableRadius L) +
          44709 / (5000 * Real.sqrt (gaussianMRVariableRadius L)) +
          1305077 / (500000 * gaussianMRVariableRadius L) +
          13 / 3 +
          A) := by
  intro hcmp
  have hr : 2000 ≤ gaussianMRVariableRadius L := by
    dsimp only [gaussianMRVariableRadius]
    nlinarith only [hL, Real.sqrt_nonneg L]
  have hs : 20 ≤ Real.sqrt (gaussianMRVariableRadius L) := by
    apply (Real.le_sqrt (by norm_num only) (by linarith only [hr])).mpr
    nlinarith only [hr]
  have hrootUpper : Real.sqrt (gaussianMRVariableRadius L) ≤ (19 / 25 : ℝ) * Real.sqrt L := by
    have hru := gaussianMRVariableRadius_upper hL
    have hL0 : 0 ≤ L := by linarith only [hL]
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num only) (Real.sqrt_nonneg L)
    · rw [mul_pow, Real.sq_sqrt hL0]
      nlinarith only [hru]
  have hInvS : 1 / Real.sqrt (gaussianMRVariableRadius L) ≤ 1 / 20 :=
    one_div_le_one_div_of_le (by norm_num only) hs
  have hInvR : 1 / gaussianMRVariableRadius L ≤ 1 / 400 :=
    one_div_le_one_div_of_le (by norm_num only) (by linarith only [hr])
  have htail :
    44709 / (5000 * Real.sqrt (gaussianMRVariableRadius L)) +
        1305077 / (500000 * gaussianMRVariableRadius L) ≤
      44709 / (5000 * 20) + 1305077 / (500000 * 400) := by
    have hS := mul_le_mul_of_nonneg_left hInvS (by norm_num only : (0 : ℝ) ≤ 44709 / 5000)
    have hR := mul_le_mul_of_nonneg_left hInvR (by norm_num only : (0 : ℝ) ≤ 1305077 / 500000)
    have hS' : 44709 / (5000 * Real.sqrt (gaussianMRVariableRadius L)) ≤ 44709 / (5000 * 20) := by
      calc
        _ = (44709 / 5000 : ℝ) * (1 / Real.sqrt (gaussianMRVariableRadius L)) := by ring
        _ ≤ _ := hS
        _ = _ := by ring
    have hR' : 1305077 / (500000 * gaussianMRVariableRadius L) ≤ 1305077 / (500000 * 400) := by
      calc
        _ = (1305077 / 500000 : ℝ) * (1 / gaussianMRVariableRadius L) := by ring
        _ ≤ _ := hR
        _ = _ := by ring
    exact add_le_add hS' hR'
  have hconst : 13 / 3 + 28 + 44709 / (5000 * 20) + 1305077 / (500000 * 400) < 33 := by
    norm_num only
  have hsmall :
    (17147 / 22500 : ℝ) * Real.sqrt (gaussianMRVariableRadius L) +
        44709 / (5000 * Real.sqrt (gaussianMRVariableRadius L)) +
        1305077 / (500000 * gaussianMRVariableRadius L) +
        13 / 3 +
        A <
      (17147 / 22500 : ℝ) * ((19 / 25 : ℝ) * Real.sqrt L) + 33 := by
    nlinarith only [hrootUpper, htail, hA, hconst]
  have hcoefL : 0 < (21943 / 30000 : ℝ) * (5503 / 10000) - 161 / 400 := by norm_num only
  have hcoefS : 0 < (21943 / 30000 : ℝ) * (4 / 5) - (17147 / 22500) * (19 / 25) := by norm_num only
  have hcoefC : 0 < (21943 / 30000 : ℝ) * 46 - 33 := by norm_num only
  have hmain :
    (161 / 400 : ℝ) * L + (17147 / 22500) * (19 / 25) * Real.sqrt L + 33 <
      (21943 / 30000 : ℝ) * gaussianMRVariableRadius L := by
    dsimp only [gaussianMRVariableRadius]
    have hLgap := mul_pos hcoefL (by linarith only [hL])
    have hSgap := mul_nonneg hcoefS.le (Real.sqrt_nonneg L)
    nlinarith only [hLgap, hSgap, hcoefC]
  have hupper :
    (161 / 400 : ℝ) * L + (17147 / 22500 : ℝ) * Real.sqrt (gaussianMRVariableRadius L) +
        44709 / (5000 * Real.sqrt (gaussianMRVariableRadius L)) +
        1305077 / (500000 * gaussianMRVariableRadius L) +
        13 / 3 +
        A <
      (21943 / 30000 : ℝ) * gaussianMRVariableRadius L := by
    calc
      _ < (161 / 400 : ℝ) * L + (17147 / 22500 : ℝ) * (19 / 25) * Real.sqrt L + 33 := by
        linarith only [hsmall]
      _ < _ := hmain
  exact (not_lt_of_ge hcmp) hupper

/-- With `log q ≤ L`, the variable-radius Gaussian comparison is impossible
throughout `L ≥ 4000`. -/
theorem gaussianMRVariable_comparison_impossible_of_ambient {q : ℕ} {L : ℝ} (hL : 4000 ≤ L)
    (hq : Real.log q ≤ L) :
    ¬((21943 / 30000 : ℝ) * gaussianMRVariableRadius L ≤
        (161 / 400 : ℝ) * L + (17147 / 22500 : ℝ) * Real.sqrt (gaussianMRVariableRadius L) +
          44709 / (5000 * Real.sqrt (gaussianMRVariableRadius L)) +
          1305077 / (500000 * gaussianMRVariableRadius L) +
          13 / 3 +
          LLS.PaperStatements.gaussianAmbientError q (gaussianMRVariableRadius L ^ 2)) := by
  exact gaussianMRVariable_comparison_impossible hL (gaussianMRVariable_ambient_error_le hL hq)

/-- On the full half-line `L ≥ 4000`, the variable Gaussian cutoff is
strictly below `7/10 L^2`. -/
theorem gaussianMRVariable_cutoff_lt_seven_tenths {L : ℝ} (hL : 4000 ≤ L) :
    (21 / 10 : ℝ) * (gaussianMRVariableRadius L) ^ 2 < (7 / 10 : ℝ) * L ^ 2 := by
  have hsqrt : Real.sqrt L ≤ L / 60 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact div_nonneg (by linarith only [hL]) (by norm_num only)
    · nlinarith only [hL]
  have hradius : gaussianMRVariableRadius L ≤ (8627 / 15000 : ℝ) * L := by
    dsimp only [gaussianMRVariableRadius]
    nlinarith only [hL, hsqrt]
  have hratio : (21 / 10 : ℝ) * (8627 / 15000) ^ 2 < 7 / 10 := by norm_num only
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hr0 : 0 ≤ gaussianMRVariableRadius L := by
    dsimp only [gaussianMRVariableRadius]
    positivity
  have hsq : gaussianMRVariableRadius L ^ 2 ≤ ((8627 / 15000 : ℝ) * L) ^ 2 := by
    nlinarith only [hradius, hr0, mul_nonneg (by norm_num only : (0 : ℝ) ≤ 8627 / 15000) hL0]
  have hcoef := mul_le_mul_of_nonneg_left hsq (by norm_num only : (0 : ℝ) ≤ 21 / 10)
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hcoefStrict : (21 / 10 : ℝ) * ((8627 / 15000 : ℝ) * L) ^ 2 < (7 / 10 : ℝ) * L ^ 2 := by
    have hratioL := mul_lt_mul_of_pos_right hratio hLsq
    ring_nf at hratioL ⊢
    nlinarith only [hratioL]
  exact lt_of_le_of_lt hcoef hcoefStrict

/-- From logarithmic scale `350000` onward, the variable Gaussian cutoff
also improves the existing `16/25` log-squared cutoff. -/
theorem gaussianMRVariable_cutoff_lt_sixteen_twentyfifths {L : ℝ} (hL : 350000 ≤ L) :
    (21 / 10 : ℝ) * (gaussianMRVariableRadius L) ^ 2 < (16 / 25 : ℝ) * L ^ 2 := by
  have hsqrt : Real.sqrt L ≤ L / 590 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact div_nonneg (by linarith only [hL]) (by norm_num only)
    · nlinarith only [hL]
  have hradius :
    gaussianMRVariableRadius L ≤ ((5503 / 10000 : ℝ) + 4 / (5 * 590) + 46 / 350000) * L := by
    dsimp only [gaussianMRVariableRadius]
    nlinarith only [hL, hsqrt]
  have hratio :
    (21 / 10 : ℝ) * ((5503 / 10000 : ℝ) + 4 / (5 * 590) + 46 / 350000) ^ 2 < 16 / 25 := by
    norm_num only
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hr0 : 0 ≤ gaussianMRVariableRadius L := by
    dsimp only [gaussianMRVariableRadius]
    positivity
  have hcoef0 : 0 ≤ (5503 / 10000 : ℝ) + 4 / (5 * 590) + 46 / 350000 := by norm_num only
  have hsq :
    gaussianMRVariableRadius L ^ 2 ≤
      (((5503 / 10000 : ℝ) + 4 / (5 * 590) + 46 / 350000) * L) ^ 2 := by
    nlinarith only [hradius, hr0, mul_nonneg hcoef0 hL0]
  have hscaled := mul_le_mul_of_nonneg_left hsq (by norm_num only : (0 : ℝ) ≤ 21 / 10)
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hcoefStrict :
    (21 / 10 : ℝ) * (((5503 / 10000 : ℝ) + 4 / (5 * 590) + 46 / 350000) * L) ^ 2 <
      (16 / 25 : ℝ) * L ^ 2 := by
    have hratioL := mul_lt_mul_of_pos_right hratio hLsq
    ring_nf at hratioL ⊢
    nlinarith only [hratioL]
  exact lt_of_le_of_lt hscaled hcoefStrict

/-- The cutoff mass retained by the classified Gaussian bound. -/
noncomputable def gaussianMRStarMass : ℝ :=
  81470555 / 100000000

/-- The endpoint constant used by the classified Gaussian comparison. -/
noncomputable def gaussianMRStarEndpoint : ℝ :=
  2129 / 2000

/-- The finite-index split in the classified Gaussian argument. -/
noncomputable def gaussianMRStarIndex : ℝ :=
  1000000000

/-- The coefficient of the conductor budget in the normalized comparison. -/
noncomputable def gaussianMRStarConductor : ℝ :=
  161 / 400

/-- The leading coefficient in the positive-root equation. -/
noncomputable def gaussianMRStarD : ℝ :=
  (gaussianMRStarIndex * gaussianMRStarMass - gaussianMRStarEndpoint) / (gaussianMRStarIndex - 1)

/-- The square-root coefficient in the positive-root equation. -/
noncomputable def gaussianMRStarBeta : ℝ :=
  (gaussianMRStarIndex / (gaussianMRStarIndex - 1)) * (gaussianMRStarMass / 3 + 3 / 10)

/-- Positive root of the quadratic budget equation for the classified
Gaussian radius. -/
noncomputable def gaussianMRStarRoot (L : ℝ) : ℝ :=
  (gaussianMRStarBeta +
      Real.sqrt
        (gaussianMRStarBeta ^ 2 + 4 * gaussianMRStarD * (gaussianMRStarConductor * L + 29))) /
    (2 * gaussianMRStarD)

/-- The classified radius is the square of the positive quadratic root. -/
noncomputable def gaussianMRStarRadius (L : ℝ) : ℝ :=
  gaussianMRStarRoot L ^ 2

/-- The new explicit upper-bound candidate on the logarithmic scale. -/
noncomputable def gaussianMRStarBound (L : ℝ) : ℝ :=
  (21 / 10 : ℝ) * gaussianMRStarRadius L ^ 2

/-- The quadratic coefficient and linear root coefficient are positive. -/
theorem gaussianMRStar_coefficients_pos : 0 < gaussianMRStarD ∧ 0 < gaussianMRStarBeta := by
  constructor
  · norm_num [gaussianMRStarD, gaussianMRStarIndex, gaussianMRStarMass, gaussianMRStarEndpoint]
  · norm_num [gaussianMRStarBeta, gaussianMRStarIndex, gaussianMRStarMass]

/-- The discriminant is nonnegative on the target range. -/
theorem gaussianMRStar_discriminant_nonneg {L : ℝ} (hL : 600 ≤ L) :
    0 ≤ gaussianMRStarBeta ^ 2 + 4 * gaussianMRStarD * (gaussianMRStarConductor * L + 29) := by
  have hD : 0 < gaussianMRStarD := by
    norm_num [gaussianMRStarD, gaussianMRStarIndex, gaussianMRStarMass, gaussianMRStarEndpoint]
  have hC : 0 < gaussianMRStarConductor := by norm_num [gaussianMRStarConductor]
  have hB : 0 < gaussianMRStarBeta := by
    norm_num [gaussianMRStarBeta, gaussianMRStarIndex, gaussianMRStarMass]
  have harg : 0 < gaussianMRStarConductor * L + 29 := by nlinarith only [hL, hC]
  positivity

/-- The classified positive root is strictly positive on the target range. -/
theorem gaussianMRStarRoot_pos {L : ℝ} (_hL : 600 ≤ L) : 0 < gaussianMRStarRoot L := by
  obtain ⟨hD, hBeta⟩ := gaussianMRStar_coefficients_pos
  have hnum :
    0 <
      gaussianMRStarBeta +
        Real.sqrt
          (gaussianMRStarBeta ^ 2 + 4 * gaussianMRStarD * (gaussianMRStarConductor * L + 29)) :=
    add_pos_of_pos_of_nonneg hBeta (Real.sqrt_nonneg _)
  have hden : 0 < 2 * gaussianMRStarD := by positivity
  dsimp only [gaussianMRStarRoot]
  exact div_pos hnum hden

/-- The square root of the classified radius recovers its positive root. -/
theorem gaussianMRStarRadius_sqrt {L : ℝ} (hL : 600 ≤ L) :
    Real.sqrt (gaussianMRStarRadius L) = gaussianMRStarRoot L := by
  rw [gaussianMRStarRadius, Real.sqrt_sq_eq_abs, abs_of_pos (gaussianMRStarRoot_pos hL)]

/-- The radius definition satisfies the quadratic equation that determines
its least value closing the Gaussian error budget. -/
theorem gaussianMRStarRadius_equation {L : ℝ} (hL : 600 ≤ L) :
    gaussianMRStarD * gaussianMRStarRadius L =
      gaussianMRStarConductor * L + gaussianMRStarBeta * gaussianMRStarRoot L + 29 := by
  let z :=
    Real.sqrt (gaussianMRStarBeta ^ 2 + 4 * gaussianMRStarD * (gaussianMRStarConductor * L + 29))
  have hD : 0 < gaussianMRStarD := by
    norm_num [gaussianMRStarD, gaussianMRStarIndex, gaussianMRStarMass, gaussianMRStarEndpoint]
  have harg := gaussianMRStar_discriminant_nonneg hL
  have hz :
    z ^ 2 = gaussianMRStarBeta ^ 2 + 4 * gaussianMRStarD * (gaussianMRStarConductor * L + 29) := by
    dsimp only [z]
    rw [Real.sq_sqrt harg]
  have hD0 : gaussianMRStarD ≠ 0 := ne_of_gt hD
  have hlin : 2 * gaussianMRStarD * gaussianMRStarRoot L = gaussianMRStarBeta + z := by
    dsimp only [gaussianMRStarRoot, z]
    field_simp
  calc
    gaussianMRStarD * gaussianMRStarRadius L =
        (4 * gaussianMRStarD ^ 2 * gaussianMRStarRoot L ^ 2) / (4 * gaussianMRStarD) :=
      by
      dsimp only [gaussianMRStarRadius]
      field_simp
    _ = (gaussianMRStarBeta + z) ^ 2 / (4 * gaussianMRStarD) := by
      rw [← hlin]
      ring
    _ = (gaussianMRStarBeta ^ 2 + 2 * gaussianMRStarBeta * z + z ^ 2) / (4 * gaussianMRStarD) := by
      ring
    _ =
        (2 * gaussianMRStarBeta ^ 2 + 2 * gaussianMRStarBeta * z +
            4 * gaussianMRStarD * (gaussianMRStarConductor * L + 29)) /
          (4 * gaussianMRStarD) :=
      by
      rw [hz]; ring
    _ =
        (2 * gaussianMRStarBeta * (gaussianMRStarBeta + z) +
            4 * gaussianMRStarD * (gaussianMRStarConductor * L + 29)) /
          (4 * gaussianMRStarD) :=
      by ring
    _ =
        (2 * gaussianMRStarBeta * (2 * gaussianMRStarD * gaussianMRStarRoot L) +
            4 * gaussianMRStarD * (gaussianMRStarConductor * L + 29)) /
          (4 * gaussianMRStarD) :=
      by rw [hlin]
    _ = gaussianMRStarConductor * L + gaussianMRStarBeta * gaussianMRStarRoot L + 29 := by
      field_simp
      ring

/-- The explicit radius stays above the squared-log scale needed by all
classified Gaussian branches. -/
theorem gaussianMRStarRadius_lower {L : ℝ} (hL : 600 ≤ L) :
    (49 / 100 : ℝ) * L ≤ gaussianMRStarRadius L := by
  obtain ⟨hD, hBeta⟩ := gaussianMRStar_coefficients_pos
  have hRoot := gaussianMRStarRoot_pos hL
  have hEq := gaussianMRStarRadius_equation hL
  have hLpos : 0 < L := by linarith only [hL]
  have hstrict : gaussianMRStarConductor * L < gaussianMRStarD * gaussianMRStarRadius L := by
    rw [hEq]
    have hrem : 0 < gaussianMRStarBeta * gaussianMRStarRoot L + 29 := by positivity
    linarith only [hrem]
  have hcoeff : gaussianMRStarD * (49 / 100 : ℝ) < gaussianMRStarConductor := by
    norm_num [gaussianMRStarD, gaussianMRStarIndex, gaussianMRStarMass, gaussianMRStarEndpoint,
      gaussianMRStarConductor]
  have hscaled := mul_lt_mul_of_pos_right hcoeff hLpos
  by_contra hnot
  have hlt : gaussianMRStarRadius L < (49 / 100 : ℝ) * L := lt_of_not_ge hnot
  have hrad := mul_lt_mul_of_pos_left hlt hD
  nlinarith only [hstrict, hscaled, hrad]

/-- The explicit radius remains strictly below `72/125` times the log scale. -/
theorem gaussianMRStarRadius_upper {L : ℝ} (hL : 600 ≤ L) :
    gaussianMRStarRadius L < (72 / 125 : ℝ) * L := by
  obtain ⟨hD, hBeta⟩ := gaussianMRStar_coefficients_pos
  have hEq := gaussianMRStarRadius_equation hL
  have hDlo : 8147 / 10000 ≤ gaussianMRStarD := by
    norm_num [gaussianMRStarD, gaussianMRStarIndex, gaussianMRStarMass, gaussianMRStarEndpoint]
  have hBetaHi : gaussianMRStarBeta ≤ 143 / 250 := by
    norm_num [gaussianMRStarBeta, gaussianMRStarIndex, gaussianMRStarMass]
  have hBetaSq := mul_le_mul hBetaHi hBetaHi hBeta.le (by norm_num only)
  norm_num only at hBetaSq
  have hYoung :
    gaussianMRStarBeta * gaussianMRStarRoot L ≤
      (1 / 50 : ℝ) * gaussianMRStarRadius L + 41 / 10 := by
    dsimp only [gaussianMRStarRadius]
    have hsquare := sq_nonneg (gaussianMRStarBeta / (2 * (1 / 50 : ℝ)) - gaussianMRStarRoot L)
    ring_nf at hsquare
    nlinarith only [hsquare, hBetaSq]
  have hLpos : 0 < L := by linarith only [hL]
  have hDgap : 0 < gaussianMRStarD - 1 / 50 := by linarith only [hDlo]
  have hcoef : (8147 / 10000 - 1 / 50 : ℝ) * (72 / 125) - 161 / 400 = 69059 / 1250000 := by
    norm_num only
  have hcoefpos : 0 < (8147 / 10000 - 1 / 50 : ℝ) * (72 / 125) - 161 / 400 := by
    rw [hcoef]; norm_num only
  by_contra hnot
  have hlarge : (72 / 125 : ℝ) * L ≤ gaussianMRStarRadius L := le_of_not_gt hnot
  have hbound :
    (gaussianMRStarD - 1 / 50) * gaussianMRStarRadius L ≤
      gaussianMRStarConductor * L + 331 / 10 := by
    calc
      _ = gaussianMRStarD * gaussianMRStarRadius L - (1 / 50 : ℝ) * gaussianMRStarRadius L := by
        ring
      _ =
          gaussianMRStarConductor * L + gaussianMRStarBeta * gaussianMRStarRoot L + 29 -
            (1 / 50 : ℝ) * gaussianMRStarRadius L :=
        by rw [hEq]
      _ ≤ gaussianMRStarConductor * L + 331 / 10 := by nlinarith only [hYoung]
  have hscale := mul_le_mul_of_nonneg_left hlarge (le_of_lt hDgap)
  have hcoefscale :=
    mul_le_mul_of_nonneg_right (sub_le_sub_right hDlo (1 / 50 : ℝ))
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 72 / 125) (le_of_lt hLpos))
  have hmarginExact :
    (8147 / 10000 - 1 / 50 : ℝ) * (72 / 125) * L - (161 / 400) * L = (69059 / 1250000) * L := by
    ring
  have hcontradiction : (331 / 10 : ℝ) < (69059 / 1250000) * L := by
    have hconstant : (331 / 10 : ℝ) < (69059 / 1250000) * 600 := by norm_num only
    have hscaled := mul_le_mul_of_nonneg_left hL (by norm_num only : (0 : ℝ) ≤ 69059 / 1250000)
    linarith only [hconstant, hscaled]
  have hcombined := hcoefscale.trans (hscale.trans hbound)
  ring_nf at hcombined
  have hupper : (69059 / 1250000 : ℝ) * L ≤ 331 / 10 := by
    norm_num only [gaussianMRStarConductor] at hcombined ⊢
    nlinarith only [hcombined]
  linarith only [hupper, hcontradiction]

/-- The Young inequality absorbs the square-root term into a small linear
fraction of the radius, leaving a fixed numerical allowance. -/
theorem gaussianMRStarRadius_budget_upper {L : ℝ} (hL : 600 ≤ L) :
    (gaussianMRStarD - 1 / 50) * gaussianMRStarRadius L ≤
      gaussianMRStarConductor * L + 331 / 10 := by
  have hEq := gaussianMRStarRadius_equation hL
  obtain ⟨hD, hBeta⟩ := gaussianMRStar_coefficients_pos
  have hDlo : 8147 / 10000 ≤ gaussianMRStarD := by
    norm_num [gaussianMRStarD, gaussianMRStarIndex, gaussianMRStarMass, gaussianMRStarEndpoint]
  have hBetaHi : gaussianMRStarBeta ≤ 143 / 250 := by
    norm_num [gaussianMRStarBeta, gaussianMRStarIndex, gaussianMRStarMass]
  have hBetaSq := mul_le_mul hBetaHi hBetaHi hBeta.le (by norm_num only)
  norm_num only at hBetaSq
  have hYoung :
    gaussianMRStarBeta * gaussianMRStarRoot L ≤
      (1 / 50 : ℝ) * gaussianMRStarRadius L + 41 / 10 := by
    dsimp only [gaussianMRStarRadius]
    have hsquare := sq_nonneg (gaussianMRStarBeta / (2 * (1 / 50 : ℝ)) - gaussianMRStarRoot L)
    ring_nf at hsquare
    nlinarith only [hsquare, hBetaSq]
  calc
    _ = gaussianMRStarD * gaussianMRStarRadius L - (1 / 50 : ℝ) * gaussianMRStarRadius L := by ring
    _ =
        gaussianMRStarConductor * L + gaussianMRStarBeta * gaussianMRStarRoot L + 29 -
          (1 / 50 : ℝ) * gaussianMRStarRadius L :=
      by rw [hEq]
    _ ≤ gaussianMRStarConductor * L + 331 / 10 := by nlinarith only [hYoung]

/-- At scales from 4000, the classified radius is at most `13/25` of `L`. -/
theorem gaussianMRStarRadius_upper_fiftytwo {L : ℝ} (hL : 4000 ≤ L) :
    gaussianMRStarRadius L < (13 / 25 : ℝ) * L := by
  have hbudget := gaussianMRStarRadius_budget_upper (by linarith only [hL])
  have hDlo : 8147 / 10000 ≤ gaussianMRStarD := by
    norm_num [gaussianMRStarD, gaussianMRStarIndex, gaussianMRStarMass, gaussianMRStarEndpoint]
  have hDgap : 0 < gaussianMRStarD - 1 / 50 := by linarith only [hDlo]
  have hLpos : 0 < L := by linarith only [hL]
  by_contra hnot
  have hlarge : (13 / 25 : ℝ) * L ≤ gaussianMRStarRadius L := le_of_not_gt hnot
  have hscale := mul_le_mul_of_nonneg_left hlarge (le_of_lt hDgap)
  have hcoefscale :=
    mul_le_mul_of_nonneg_right (sub_le_sub_right hDlo (1 / 50 : ℝ))
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 13 / 25) (le_of_lt hLpos))
  have hcombined := hcoefscale.trans (hscale.trans hbudget)
  norm_num only [gaussianMRStarConductor] at hcombined
  have hgap : (1343 / 125000 : ℝ) * L ≤ 331 / 10 := by nlinarith only [hcombined]
  have hcontradiction : 331 / 10 < (1343 / 125000 : ℝ) * L := by
    have hc : (331 / 10 : ℝ) < (1343 / 125000) * 4000 := by norm_num only
    have hs := mul_le_mul_of_nonneg_left hL (by norm_num only : (0 : ℝ) ≤ 1343 / 125000)
    linarith only [hc, hs]
  linarith only [hgap, hcontradiction]

/-- The ambient Gaussian remainder at the classified radius is bounded by
the exact rational allowance specified for the range `L ≥ 600`. -/
theorem gaussianMRStar_ambient_error_le {q : ℕ} {L : ℝ} (hL : 600 ≤ L) (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientError q (gaussianMRStarRadius L ^ 2) ≤ 125191 / 4500 := by
  let r := gaussianMRStarRadius L
  have hrL : (49 / 100 : ℝ) * L ≤ r := gaussianMRStarRadius_lower hL
  have hLpos : 0 < L := by linarith only [hL]
  have hrpos : 0 < r := by
    have hscaled := mul_pos (by norm_num only : (0 : ℝ) < 49 / 100) hLpos
    exact lt_of_lt_of_le hscaled hrL
  have hsqrt : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hrpos.le
  have hx : (2 : ℝ) ^ 16 ≤ r ^ 2 := by
    have hr294 : 294 ≤ r := by nlinarith only [hL, hrL]
    norm_num only at hr294 ⊢
    nlinarith only [hr294]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 2) (by norm_num only) hx
  have hP : (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / r) ≤ 46838 / 18375 := by
    rw [div_eq_mul_inv]
    field_simp [hrpos.ne']
    nlinarith only [hL, hq, hrL]
  have hC : 0 ≤ (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) := by
    have hlog := Real.log_natCast_nonneg q
    positivity
  have hb := mul_le_mul_of_nonneg_left hdec hC
  have hB : (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) / (2 * r) ≤ 466499 / 88200 := by
    rw [div_le_iff₀ (mul_pos (by norm_num only) hrpos)]
    nlinarith only [hL, hq, hrL]
  rw [hsqrt] at hb
  have hb' :
    (11 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) ≤
      (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) / (2 * r) := by
    simp only [div_eq_mul_inv] at hb hB ⊢
    nlinarith only [hb, hB]
  have hb'' := hb'.trans hB
  change LLS.PaperStatements.gaussianAmbientError q (r ^ 2) ≤ 125191 / 4500
  dsimp only [LLS.PaperStatements.gaussianAmbientError]
  rw [hsqrt]
  have htotal : (12871 / 1000 : ℝ) + 64 / 9 + 46838 / 18375 + 466499 / 88200 ≤ 125191 / 4500 := by
    norm_num only
  calc
    _ =
        (12871 / 1000 : ℝ) + 64 / 9 +
          ((2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / r) +
            (11 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3)) :=
      by ring
    _ =
        ((12871 / 1000 : ℝ) + 64 / 9 + (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / r)) +
          (11 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) :=
      by ring
    _ ≤ ((12871 / 1000 : ℝ) + 64 / 9 + 46838 / 18375) + 466499 / 88200 := by
      exact add_le_add (add_le_add_right hP ((12871 / 1000 : ℝ) + 64 / 9)) hb''
    _ = (12871 / 1000 : ℝ) + 64 / 9 + 46838 / 18375 + 466499 / 88200 := by ring
    _ ≤ 125191 / 4500 := htotal

/-- The classified Gaussian candidate improves the coefficient `7/10` on
the entire half-line beginning at 600. -/
theorem gaussianMRStarBound_lt_seven_tenths {L : ℝ} (hL : 600 ≤ L) :
    gaussianMRStarBound L < (7 / 10 : ℝ) * L ^ 2 := by
  have hr := gaussianMRStarRadius_upper hL
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hr0 : 0 ≤ gaussianMRStarRadius L := by
    dsimp only [gaussianMRStarRadius]
    positivity
  have hcoef0 : (0 : ℝ) ≤ 72 / 125 := by norm_num only
  have hsq : gaussianMRStarRadius L ^ 2 ≤ ((72 / 125 : ℝ) * L) ^ 2 := by
    nlinarith only [hr, hr0, mul_nonneg hcoef0 hL0]
  have hscaled := mul_le_mul_of_nonneg_left hsq (by norm_num only : (0 : ℝ) ≤ 21 / 10)
  have hratio : (21 / 10 : ℝ) * (72 / 125) ^ 2 < 7 / 10 := by norm_num only
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hstrict : (21 / 10 : ℝ) * ((72 / 125 : ℝ) * L) ^ 2 < (7 / 10 : ℝ) * L ^ 2 := by
    have hratioL := mul_lt_mul_of_pos_right hratio hLsq
    ring_nf at hratioL ⊢
    nlinarith only [hratioL]
  dsimp only [gaussianMRStarBound]
  exact lt_of_le_of_lt hscaled hstrict

/-- Whenever the existing coefficient branch applies, its bound is below
the classified Gaussian candidate. -/
theorem gaussianMRStarBound_gt_triangular_coefficient {L : ℝ} (hL : 600 ≤ L) :
    (282924 / 1000000 : ℝ) * L ^ 2 < gaussianMRStarBound L := by
  have hr := gaussianMRStarRadius_lower hL
  have hLpos : 0 < L := by linarith only [hL]
  have hbase : 0 ≤ (49 / 100 : ℝ) * L := by positivity
  have hsq : ((49 / 100 : ℝ) * L) ^ 2 ≤ gaussianMRStarRadius L ^ 2 := by
    have hr0 : 0 ≤ gaussianMRStarRadius L := by
      dsimp only [gaussianMRStarRadius]
      positivity
    nlinarith only [hr, hr0, hbase, sq_nonneg (gaussianMRStarRadius L - (49 / 100 : ℝ) * L)]
  have hcoef : (282924 / 1000000 : ℝ) < (21 / 10 : ℝ) * (49 / 100) ^ 2 := by norm_num only
  have hstrict := mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hLpos)
  have hscaled := mul_le_mul_of_nonneg_left hsq (by norm_num only : (0 : ℝ) ≤ 21 / 10)
  dsimp only [gaussianMRStarBound]
  calc
    (282924 / 1000000 : ℝ) * L ^ 2 < (21 / 10 : ℝ) * ((49 / 100 : ℝ) * L) ^ 2 := by
      nlinarith only [hstrict]
    _ ≤ (21 / 10 : ℝ) * gaussianMRStarRadius L ^ 2 := hscaled

/-- From scale 4000 onward, the classified radius improves the previously
available variable-width Gaussian cutoff. -/
theorem gaussianMRStarBound_lt_variable_gaussian {L : ℝ} (hL : 4000 ≤ L) :
    gaussianMRStarBound L < (21 / 10 : ℝ) * (gaussianMRVariableRadius L) ^ 2 := by
  have hLpos : 0 < L := by linarith only [hL]
  have hs := gaussianMRStarRadius_upper_fiftytwo hL
  have hs0 : 0 ≤ gaussianMRStarRadius L := by
    dsimp only [gaussianMRStarRadius]
    positivity
  have hg : (5503 / 10000 : ℝ) * L ≤ gaussianMRVariableRadius L := by
    dsimp only [gaussianMRVariableRadius]
    nlinarith only [Real.sqrt_nonneg L]
  have hg0 : 0 ≤ (5503 / 10000 : ℝ) * L := by positivity
  have hstarMul :
    gaussianMRStarRadius L * gaussianMRStarRadius L < ((13 / 25 : ℝ) * L) * ((13 / 25 : ℝ) * L) :=
    mul_self_lt_mul_self hs0 hs
  have hstarSq : gaussianMRStarRadius L ^ 2 < ((13 / 25 : ℝ) * L) ^ 2 := by
    simpa only [pow_two] using hstarMul
  have holdMul :
    ((5503 / 10000 : ℝ) * L) * ((5503 / 10000 : ℝ) * L) ≤
      gaussianMRVariableRadius L * gaussianMRVariableRadius L :=
    mul_self_le_mul_self hg0 hg
  have holdSq : ((5503 / 10000 : ℝ) * L) ^ 2 ≤ (gaussianMRVariableRadius L) ^ 2 := by
    simpa only [pow_two] using holdMul
  have hcoef : (13 / 25 : ℝ) ^ 2 < (5503 / 10000 : ℝ) ^ 2 := by norm_num only
  have hscale := mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hLpos)
  have hscaledStar := mul_lt_mul_of_pos_left hstarSq (by norm_num only : (0 : ℝ) < 21 / 10)
  have hscaledOld := mul_le_mul_of_nonneg_left holdSq (by norm_num only : (0 : ℝ) ≤ 21 / 10)
  have hcoeffCompare :
    (21 / 10 : ℝ) * ((13 / 25 : ℝ) * L) ^ 2 < (21 / 10 : ℝ) * ((5503 / 10000 : ℝ) * L) ^ 2 := by
    ring_nf at hscale ⊢
    nlinarith only [hscale]
  dsimp only [gaussianMRStarBound]
  exact lt_of_lt_of_le (hscaledStar.trans hcoeffCompare) hscaledOld

/-- For a Fermat index at least `10^9`, the inverse-radius and ambient
contributions in the normalized relative comparison have total strictly below
the radius equation's constant `29`. -/
theorem gaussianMRStar_scalar_error_lt {m s r A : ℝ} (hm : gaussianMRStarIndex ≤ m) (hs : 17 ≤ s)
    (hr : 294 ≤ r) (hgamma : m / (m - 1) ≤ gaussianMRStarIndex / (gaussianMRStarIndex - 1))
    (hA : A ≤ 125191 / 4500) :
    (m / (m - 1)) *
          (63 * gaussianMRStarEndpoint / (10 * s) + 1839 * gaussianMRStarEndpoint / (1000 * r)) +
        13 / (m - 1) +
        A <
      29 := by
  have hK : (1 : ℝ) < gaussianMRStarIndex := by norm_num only [gaussianMRStarIndex]
  have hK0 : 0 ≤ gaussianMRStarIndex := le_of_lt (by norm_num only [gaussianMRStarIndex])
  have hmden : 0 < m - 1 := by linarith only [hm, hK]
  have hKden : 0 < gaussianMRStarIndex - 1 := by norm_num only [gaussianMRStarIndex]
  have hspos : 0 < s := by linarith only [hs]
  have hrpos : 0 < r := by linarith only [hr]
  have hnum1 : 0 ≤ 63 * gaussianMRStarEndpoint / 10 := by norm_num only [gaussianMRStarEndpoint]
  have hterm1 : (63 * gaussianMRStarEndpoint / 10) / s ≤ (63 * gaussianMRStarEndpoint / 10) / 17 :=
    div_le_div_of_nonneg_left hnum1 (by norm_num only) (by linarith only [hs])
  have hnum2 : 0 ≤ 1839 * gaussianMRStarEndpoint / 1000 := by norm_num only [gaussianMRStarEndpoint]
  have hterm2 :
    (1839 * gaussianMRStarEndpoint / 1000) / r ≤ (1839 * gaussianMRStarEndpoint / 1000) / 294 :=
    div_le_div_of_nonneg_left hnum2 (by norm_num only) (by linarith only [hr])
  have htail :
    (63 * gaussianMRStarEndpoint / 10) / s + (1839 * gaussianMRStarEndpoint / 1000) / r ≤
      (63 * gaussianMRStarEndpoint / 10) / 17 + (1839 * gaussianMRStarEndpoint / 1000) / 294 :=
    add_le_add hterm1 hterm2
  have hratio0 : 0 ≤ m / (m - 1) := div_nonneg (by linarith only [hm, hK0]) hmden.le
  have htailbound0 :
    0 ≤ (63 * gaussianMRStarEndpoint / 10) / 17 + (1839 * gaussianMRStarEndpoint / 1000) / 294 := by
    positivity
  have htailK :
    (m / (m - 1)) *
        ((63 * gaussianMRStarEndpoint / 10) / s + (1839 * gaussianMRStarEndpoint / 1000) / r) ≤
      (gaussianMRStarIndex / (gaussianMRStarIndex - 1)) *
        ((63 * gaussianMRStarEndpoint / 10) / 17 +
          (1839 * gaussianMRStarEndpoint / 1000) / 294) := by
    calc
      _ ≤
          (m / (m - 1)) *
            ((63 * gaussianMRStarEndpoint / 10) / 17 +
              (1839 * gaussianMRStarEndpoint / 1000) / 294) :=
        mul_le_mul_of_nonneg_left htail hratio0
      _ ≤ _ := mul_le_mul_of_nonneg_right hgamma htailbound0
  have hconst : 13 / (m - 1) ≤ 13 / (gaussianMRStarIndex - 1) := by
    apply div_le_div_of_nonneg_left
    · norm_num only
    · exact hKden
    · linarith only [hm]
  have htermEq :
    63 * gaussianMRStarEndpoint / (10 * s) + 1839 * gaussianMRStarEndpoint / (1000 * r) =
      (63 * gaussianMRStarEndpoint / 10) / s + (1839 * gaussianMRStarEndpoint / 1000) / r := by
    field_simp
  rw [htermEq]
  norm_num [gaussianMRStarIndex, gaussianMRStarEndpoint] at htailK hconst ⊢
  nlinarith only [hA, htailK, hconst]

/-- The new radius equation contradicts the normalized relative comparison
for every index at least `10^9`, once the conductor cost is at most `L` and
the ambient error satisfies the proved uniform budget. -/
theorem gaussianMRStar_large_index_comparison_impossible {m s r A L : ℝ}
    (hm : gaussianMRStarIndex ≤ m) (hs : 17 ≤ s) (hr : 294 ≤ r)
    (hgamma : m / (m - 1) ≤ gaussianMRStarIndex / (gaussianMRStarIndex - 1))
    (hA : A ≤ 125191 / 4500)
    (hroot : gaussianMRStarD * r = gaussianMRStarConductor * L + gaussianMRStarBeta * s + 29)
    (hcmp :
      gaussianMRStarD * r ≤
        gaussianMRStarConductor * L + gaussianMRStarBeta * s +
          (m / (m - 1)) *
            (63 * gaussianMRStarEndpoint / (10 * s) + 1839 * gaussianMRStarEndpoint / (1000 * r)) +
          13 / (m - 1) +
          A) :
    False := by
  have herr := gaussianMRStar_scalar_error_lt hm hs hr hgamma hA
  linarith only [hroot, hcmp, herr]

/-- The index-four comparison with conductor cost `2L` is incompatible with
the classified radius once its remaining scalar error is below `33`. -/
theorem gaussianMRStar_triple_comparison_impossible {L : ℝ} (hL : 600 ≤ L)
    (hcmp :
      ((4 * gaussianMRStarMass - gaussianMRStarEndpoint) / 3) * gaussianMRStarRadius L ≤
        (161 / 600 : ℝ) * L +
          (4 / 3 : ℝ) * (gaussianMRStarMass / 3 + 3 / 10) * gaussianMRStarRoot L +
          33) :
    False := by
  let r := gaussianMRStarRadius L
  let s := gaussianMRStarRoot L
  have hrlo : (49 / 100 : ℝ) * L ≤ r := gaussianMRStarRadius_lower hL
  have hrhi : r < L := by
    have hh := gaussianMRStarRadius_upper hL
    linarith only [hh, hL]
  have hspos : 0 < s := gaussianMRStarRoot_pos hL
  have hsSq : s ^ 2 = r := by rfl
  have hLsq : L ≤ (L / 24) ^ 2 := by
    have hLpos : 0 < L := by linarith only [hL]
    have hprod : 0 ≤ L * (L - 576) := mul_nonneg (le_of_lt hLpos) (by linarith only [hL])
    have hsq : 0 ≤ L ^ 2 - 576 * L := by nlinarith only [hprod]
    nlinarith only [hsq]
  have hsle : s ≤ L / 24 := by
    by_contra hnot
    have hdiff : 0 < s - L / 24 := by linarith only [hnot]
    have hsum : 0 < s + L / 24 := by positivity
    have hsq' : (L / 24) ^ 2 < s ^ 2 := by nlinarith only [hdiff, hsum]
    have hLlt : L < r := by
      calc
        L ≤ (L / 24) ^ 2 := hLsq
        _ < r := by simpa only [hsSq] using hsq'
    exact (not_lt_of_ge hrhi.le) hLlt
  have hcoeff :
    ((4 * gaussianMRStarMass - gaussianMRStarEndpoint) / 3) * (49 / 100) - (161 / 600 : ℝ) -
        ((4 / 3 : ℝ) * (gaussianMRStarMass / 3 + 3 / 10)) / 24 -
        33 / 600 =
      89608127 / 27000000000 := by
    norm_num [gaussianMRStarMass, gaussianMRStarEndpoint]
  have hpositive : (89608127 / 27000000000 : ℝ) * L > 0 :=
    mul_pos (by norm_num) (by linarith only [hL])
  have h600 : (33 : ℝ) ≤ (33 / 600) * L := by nlinarith only [hL]
  have hlinear :
    (161 / 600 : ℝ) * L + (4 / 3 : ℝ) * (gaussianMRStarMass / 3 + 3 / 10) * (L / 24) + 33 <
      ((4 * gaussianMRStarMass - gaussianMRStarEndpoint) / 3) * ((49 / 100 : ℝ) * L) := by
    rw [show
        ((4 / 3 : ℝ) * (gaussianMRStarMass / 3 + 3 / 10)) * (L / 24) =
          ((4 / 3 : ℝ) * (gaussianMRStarMass / 3 + 3 / 10)) / 24 * L
        by ring]
    rw [show
        ((4 * gaussianMRStarMass - gaussianMRStarEndpoint) / 3) * ((49 / 100 : ℝ) * L) =
          ((4 * gaussianMRStarMass - gaussianMRStarEndpoint) / 3) * (49 / 100) * L
        by ring]
    nlinarith only [hcoeff, hpositive, h600]
  have hDpos : 0 ≤ (4 * gaussianMRStarMass - gaussianMRStarEndpoint) / 3 := by
    norm_num [gaussianMRStarMass, gaussianMRStarEndpoint]
  have hBpos : 0 ≤ (4 / 3 : ℝ) * (gaussianMRStarMass / 3 + 3 / 10) := by
    norm_num [gaussianMRStarMass]
  have hrlowScaled := mul_le_mul_of_nonneg_left hrlo hDpos
  have hsScaled := mul_le_mul_of_nonneg_left hsle hBpos
  have hstrict :
    (161 / 600 : ℝ) * L + (4 / 3 : ℝ) * (gaussianMRStarMass / 3 + 3 / 10) * s + 33 <
      ((4 * gaussianMRStarMass - gaussianMRStarEndpoint) / 3) * r := by
    calc
      (161 / 600 : ℝ) * L + (4 / 3 : ℝ) * (gaussianMRStarMass / 3 + 3 / 10) * s + 33 ≤
          (161 / 600 : ℝ) * L + (4 / 3 : ℝ) * (gaussianMRStarMass / 3 + 3 / 10) * (L / 24) + 33 :=
        by nlinarith only [hsScaled]
      _ < ((4 * gaussianMRStarMass - gaussianMRStarEndpoint) / 3) * ((49 / 100 : ℝ) * L) := hlinear
      _ ≤ ((4 * gaussianMRStarMass - gaussianMRStarEndpoint) / 3) * r := hrlowScaled
  dsimp only [r, s] at hstrict
  exact (not_le_of_gt hstrict) hcmp

/-- At index four, the ambient term, inverse-radius terms and normalized
constant are below `33` for the classified radius. -/
theorem gaussianMRStar_triple_scalar_error_lt {s r A : ℝ} (hs : 17 ≤ s) (hr : 294 ≤ r)
    (hA : A ≤ 125191 / 4500) :
    (4 / 3 : ℝ) *
          (63 * gaussianMRStarEndpoint / (10 * s) + 1839 * gaussianMRStarEndpoint / (1000 * r)) +
        13 / 3 +
        A <
      33 := by
  have hnum1 : 0 ≤ 63 * gaussianMRStarEndpoint := by norm_num [gaussianMRStarEndpoint]
  have hden1 : 0 < 10 * (17 : ℝ) := by norm_num
  have hterm1 : 63 * gaussianMRStarEndpoint / (10 * s) ≤ 63 * gaussianMRStarEndpoint / (10 * 17) :=
    div_le_div_of_nonneg_left hnum1 hden1 (by nlinarith only [hs])
  have hnum2 : 0 ≤ 1839 * gaussianMRStarEndpoint := by norm_num [gaussianMRStarEndpoint]
  have hden2 : 0 < 1000 * (294 : ℝ) := by norm_num
  have hterm2 :
    1839 * gaussianMRStarEndpoint / (1000 * r) ≤ 1839 * gaussianMRStarEndpoint / (1000 * 294) :=
    div_le_div_of_nonneg_left hnum2 hden2 (by nlinarith only [hr])
  have hconst :
    (4 / 3 : ℝ) *
          (63 * gaussianMRStarEndpoint / (10 * 17) + 1839 * gaussianMRStarEndpoint / (1000 * 294)) +
        13 / 3 +
        125191 / 4500 <
      33 := by
    norm_num [gaussianMRStarEndpoint]
  have htail := add_le_add hterm1 hterm2
  nlinarith only [htail, hA, hconst]

/-- For a real subgroup index at least `10^9`, retain the exact normalized
mass and endpoint coefficients and compare them with the fixed index `10^9`. -/
theorem gaussianMRStar_index_coefficients {m : ℝ} (hm : gaussianMRStarIndex ≤ m) :
    gaussianMRStarD ≤ (m * gaussianMRStarMass - gaussianMRStarEndpoint) / (m - 1) ∧
      m / (m - 1) ≤ gaussianMRStarIndex / (gaussianMRStarIndex - 1) ∧
      (m / (m - 1)) * (gaussianMRStarMass / 3 + 3 / 10) ≤ gaussianMRStarBeta := by
  have hK : (1 : ℝ) < gaussianMRStarIndex := by norm_num only [gaussianMRStarIndex]
  have hden : 0 < m - 1 := by linarith only [hm, hK]
  have hKden : 0 < gaussianMRStarIndex - 1 := by linarith only [hK]
  have hgamma : m / (m - 1) ≤ gaussianMRStarIndex / (gaussianMRStarIndex - 1) := by
    rw [div_le_div_iff₀ hden hKden]
    norm_num [gaussianMRStarIndex] at hm ⊢
    nlinarith only [hm]
  have hbase : 0 ≤ gaussianMRStarMass / 3 + 3 / 10 := by norm_num [gaussianMRStarMass]
  refine ⟨?_, hgamma, ?_⟩
  · dsimp only [gaussianMRStarD]
    rw [div_le_div_iff₀ hKden hden]
    norm_num [gaussianMRStarIndex, gaussianMRStarMass, gaussianMRStarEndpoint] at hm ⊢
    nlinarith only [hm]
  · dsimp only [gaussianMRStarBeta]
    calc
      _ ≤ (gaussianMRStarIndex / (gaussianMRStarIndex - 1)) * (gaussianMRStarMass / 3 + 3 / 10) :=
        mul_le_mul_of_nonneg_right hgamma hbase
      _ = gaussianMRStarBeta := by rfl

end PseudoPrime.Analysis
