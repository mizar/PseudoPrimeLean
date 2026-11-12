/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevScaleError
import PseudoPrime.Analysis.NumericalLogBounds
import PseudoPrime.Analysis.PreciseLogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountErrorNumerics

/-! # A logarithm-square Chebyshev bound from a zero-count estimate -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The exact logarithm certificate at 25000000 and monotonicity give
`17 ≤ log x` for every larger real `x`. -/
private theorem log_seventeen_of_25m {x : ℝ} (hx : 25000000 ≤ x) : 17 ≤ Real.log x := by
  have hcert : Analysis.preciseLogCheck 25000000 25 32 17 18 = true := by decide +kernel
  have hl := (Analysis.preciseLogCheck_sound hcert).1
  norm_num only [Rat.cast_ofNat] at hl
  have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 25000000) hx
  exact hl.trans hm

/-- Elementary normalized budget for logarithmic scale at least 17. -/
private theorem normalized_square_budget {L u v δ c e : ℝ} (hL : 17 ≤ L) (hd : δ ≤ 1 / 100)
    (hu0 : 0 ≤ u) (hu : u ≤ L / 2) (hv0 : 0 ≤ v) (hv : v ≤ L / 2) (hc : c ≤ 1) (he : e ≤ 1) :
    4 + c + (1 + δ / 2) * (u ^ 2 / (2 * Real.pi) + 1) + (1 + δ) * v / Real.pi + e ≤
      (1 / 12 : ℝ) * L ^ 2 := by
  have hu2 : u ^ 2 ≤ L ^ 2 / 4 := by
    have hh :=
      mul_nonneg (show 0 ≤ L / 2 - u by linarith only [hu])
        (show 0 ≤ L / 2 + u by linarith only [hL, hu0])
    nlinarith only [hh]
  have hA : u ^ 2 / (2 * Real.pi) ≤ L ^ 2 / 24 := by
    have hh :=
      div_le_div_of_nonneg_left (sq_nonneg u) (show (0 : ℝ) < 6 by norm_num only)
        (show (6 : ℝ) ≤ 2 * Real.pi by linarith only [Real.pi_gt_three])
    nlinarith only [hh, hu2]
  have hB : v / Real.pi ≤ L / 6 := by
    have hh := div_le_div_of_nonneg_left hv0 (show (0 : ℝ) < 3 by norm_num only) Real.pi_gt_three.le
    linarith only [hh, hv]
  have hA0 : 0 ≤ 1 + u ^ 2 / (2 * Real.pi) := by
    have hh := div_nonneg (sq_nonneg u) (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) Real.pi_pos.le)
    linarith only [hh]
  have hV0 : 0 ≤ v / Real.pi := div_nonneg hv0 Real.pi_pos.le
  have hm1 :=
    mul_le_mul (show 1 + δ / 2 ≤ (101 / 100 : ℝ) by linarith only [hd]) (add_le_add_right hA 1) hA0
      (by norm_num only : (0 : ℝ) ≤ 101 / 100)
  have hm2 :=
    mul_le_mul (show 1 + δ ≤ (101 / 100 : ℝ) by linarith only [hd]) hB hV0
      (by norm_num only : (0 : ℝ) ≤ 101 / 100)
  rw [mul_div_assoc]
  nlinarith only [hm1, hm2, hc, he, hL, sq_nonneg (L - 17)]

/-- The normalized explicit-formula estimate at width `8 * sqrt x` implies
this one-sided logarithm-square bound once `x` and `log x` are sufficiently
large. The normalized bound is supplied independently of its zero inputs. -/
private theorem psi_lower_square_of_norm {x : ℝ} (hx : 25000000 ≤ x) (hlog : 17 ≤ Real.log x)
    (hN :
      ∀ h δ : ℝ,
        0 < h →
          1 < x - h →
          1000 ≤ 2 / δ →
          0 < δ →
          δ ≤ 1 / 2 →
          h = x * δ →
          δ = 8 / Real.sqrt x →
          |Chebyshev.psi x - x| / Real.sqrt x ≤
            h / (2 * Real.sqrt x) + Real.log (2 * Real.pi) / Real.sqrt x +
              (1 + δ / 2) * ((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1) +
              (1 + δ) * Real.log (2 / δ) / Real.pi +
              1 / (h * Real.sqrt x)) :
    x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x := by
  have hx0 : 0 < x := by linarith only [hx]
  let r : ℝ := Real.sqrt x
  have hr : (5000 : ℝ) ≤ r := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hx]
  have hr0 : 0 < r := by linarith only [hr]
  have hrsq : r ^ 2 = x := Real.sq_sqrt hx0.le
  let δ : ℝ := 8 / r
  let h : ℝ := 8 * r
  have hd0 : 0 < δ := div_pos (by norm_num only) hr0
  have hd : δ ≤ 1 / 100 := by
    dsimp only [δ]
    apply (div_le_iff₀ hr0).2
    linarith only [hr]
  have hh : 0 < h := by
    dsimp only [h]; nlinarith only [hr]
  have hmid : 1 < x - h := by
    dsimp only [h]; nlinarith only [hr, hrsq]
  have heq : (2 : ℝ) / δ = r / 4 := by
    dsimp only [δ]
    have hrne : r ≠ 0 := hr0.ne'
    field_simp
    norm_num only
  have hT : 1000 ≤ 2 / δ := by
    rw [heq]; linarith only [hr]
  have hwidth : h = x * δ := by
    dsimp only [h, δ]
    have hrne : r ≠ 0 := hr0.ne'
    field_simp
    nlinarith only [hrsq]
  have hb := hN h δ hh hmid hT hd0 (by linarith only [hd]) hwidth rfl
  have hden : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hden1 : 1 ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  have hTpos : 0 < 2 / δ := by linarith only [hT]
  have hbase : 1 ≤ (2 / δ) / (2 * Real.pi) := by
    apply (le_div_iff₀ hden).2
    linarith only [hT, Real.pi_lt_four]
  have hu0 : 0 ≤ Real.log ((2 / δ) / (2 * Real.pi)) := Real.log_nonneg hbase
  have hTr : 2 / δ ≤ r := by
    rw [heq]; linarith only [hr]
  have hAr : (2 / δ) / (2 * Real.pi) ≤ r := le_trans (div_le_self hTpos.le hden1) hTr
  have hu : Real.log ((2 / δ) / (2 * Real.pi)) ≤ Real.log x / 2 := by
    have hh := Real.log_le_log (div_pos hTpos hden) hAr
    change Real.log ((2 / δ) / (2 * Real.pi)) ≤ Real.log (Real.sqrt x) at hh
    rw [Real.log_sqrt hx0.le] at hh
    exact hh
  have hv0 : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by linarith only [hT])
  have hv : Real.log (2 / δ) ≤ Real.log x / 2 := by
    have hh := Real.log_le_log hTpos hTr
    change Real.log (2 / δ) ≤ Real.log (Real.sqrt x) at hh
    rw [Real.log_sqrt hx0.le] at hh
    exact hh
  have hc : Real.log (2 * Real.pi) / r ≤ 1 := by
    apply (div_le_one₀ hr0).2
    have hh := Analysis.log_two_mul_pi_lt
    linarith only [hh, hr]
  have he : 1 / (h * r) ≤ 1 := by
    have hd : 0 < h * r := mul_pos hh hr0
    apply (div_le_one₀ hd).2
    dsimp only [h]
    nlinarith only [hr]
  have hf : h / (2 * r) = 4 := by
    dsimp only [h]
    have hrne : r ≠ 0 := hr0.ne'
    field_simp
    norm_num only
  change |Chebyshev.psi x - x| / r ≤ _ at hb
  rw [hf] at hb
  have hc2 := normalized_square_budget hlog hd hu0 hu hv0 hv hc he
  have hnorm := hb.trans hc2
  have hfinal := (div_le_iff₀ hr0).mp hnorm
  have hdiff := (abs_le.mp hfinal).1
  change x - (1 / 12 : ℝ) * r * Real.log x ^ 2 ≤ Chebyshev.psi x
  nlinarith only [hdiff]

/-- Under RH, the stated zero-count estimate through `sqrt x / 4` and the
inverse-square ordinate-tail bound at that cutoff imply the one-sided
logarithm-square Chebyshev bound for `x ≥ 25000000` and `17 ≤ log x`. -/
theorem psi_lower_square_log_tail (hRH : RiemannHypothesis) {x : ℝ} (hx : 25000000 ≤ x)
    (hlog : 17 ≤ Real.log x)
    (hQ :
      ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) (Real.sqrt x / 4),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t)
    (hTail :
      ordinateTail (Real.sqrt x / 4) ≤ Real.log (Real.sqrt x / 4) / (Real.pi * (Real.sqrt x / 4))) :
    x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x := by
  apply psi_lower_square_of_norm hx hlog
  intro h δ hh hmid hT hd hd2 hwidth hchoice
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith only [hx])
  have heq : (2 : ℝ) / δ = Real.sqrt x / 4 := by
    rw [hchoice]
    have hsne : Real.sqrt x ≠ 0 := hs.ne'
    field_simp
    norm_num only
  have hQ' :
    ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) (2 / δ),
      |positiveZeroCount t -
            (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
        Real.log t := by
    rw [heq]
    exact hQ
  have hTail' : ordinateTail (2 / δ) ≤ Real.log (2 / δ) / (Real.pi * (2 / δ)) := by
    rw [heq]
    exact hTail
  exact psi_error_normalized_tail hRH (by linarith only [hx]) hh hmid hT hd hd2 hwidth hQ' hTail'

/-- Under RH and a positive-height zero-count error bounded by `log t`,
`x ≥ 25000000` and `17 ≤ log x` imply the one-sided logarithm-square bound.
Use the normalized explicit formula at width `8 * sqrt x`. -/
theorem psi_lower_square_log_coarse (hRH : RiemannHypothesis) {x : ℝ} (hx : 25000000 ≤ x)
    (hlog : 17 ≤ Real.log x)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x := by
  apply psi_lower_square_of_norm hx hlog
  intro h δ hh hmid hT hd hd2 hwidth hchoice
  exact psi_error_normalized_coarse hRH (by linarith only [hx]) hh hmid hT hd hd2 hwidth hQ

/-- Under RH and the stated Rosser-type zero-count estimate, a positive real
`x ≥ 25000000` of logarithmic scale at least 17 satisfies the displayed
one-sided logarithm-square Chebyshev bound. The width `8 * sqrt x` and cutoff
`sqrt x / 4` are substituted into the normalized zero-sum estimate. -/
theorem psi_lower_square_log (hRH : RiemannHypothesis) {x : ℝ} (hx : 25000000 ≤ x)
    (hlog : 17 ≤ Real.log x)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x := by
  apply psi_lower_square_log_coarse hRH hx hlog
  intro t ht
  exact (hQ t ht).trans (rosser_error_le_log ht)

/-- Under RH, the stated finite zero-count estimate and ordinate-tail bound
imply the one-sided logarithm-square Chebyshev lower bound for `x ≥ 25000000`.
An exact logarithm certificate supplies the logarithmic scale condition. -/
theorem psi_lower_square_tail (hRH : RiemannHypothesis) {x : ℝ} (hx : 25000000 ≤ x)
    (hQ :
      ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) (Real.sqrt x / 4),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t)
    (hTail :
      ordinateTail (Real.sqrt x / 4) ≤ Real.log (Real.sqrt x / 4) / (Real.pi * (Real.sqrt x / 4))) :
    x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x := by
  exact psi_lower_square_log_tail hRH hx (log_seventeen_of_25m hx) hQ hTail

/-- Under RH and a positive-height zero-count error at most `log t`, the
one-sided logarithm-square Chebyshev lower bound holds for `x ≥ 25000000`.
A finite logarithm certificate establishes the required scale bound. -/
theorem psi_lower_square_coarse (hRH : RiemannHypothesis) {x : ℝ} (hx : 25000000 ≤ x)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x := by
  exact psi_lower_square_log_coarse hRH hx (log_seventeen_of_25m hx) hQ

/-- Under RH and the stated Rosser-type zero-count estimate, the one-sided
logarithm-square Chebyshev lower bound holds for every `x ≥ 25000000`. An exact
logarithm certificate supplies the scale hypothesis for the normalized bound. -/
theorem psi_lower_square_count (hRH : RiemannHypothesis) {x : ℝ} (hx : 25000000 ≤ x)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x := by
  apply psi_lower_square_coarse hRH hx
  intro t ht
  exact (hQ t ht).trans (rosser_error_le_log ht)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
