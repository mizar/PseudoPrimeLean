/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerZeta94
public import PseudoPrime.Analysis.LogPowerTailIntegral
import PseudoPrime.Analysis.CorrectedTrapezoid
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentAbel
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SumIntegralComparisons

/-! # Corrected tails of the four zeta moments in section 94 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- After k differentiations, the power of x decreases by k and the
logarithmic factor follows the polynomial product-rule recurrence. -/
private noncomputable def momentPoly (j : ℕ) : ℕ → Polynomial ℝ
  | 0 => Polynomial.X ^ j
  | k + 1 => (momentPoly j k).derivative - Polynomial.C (38 / 25 + k : ℝ) * momentPoly j k

/-- Power-logarithm derivatives for the zeta moments at 38/25. -/
private noncomputable def momentDeriv (j k : ℕ) (x : ℝ) : ℝ :=
  x ^ (-(38 / 25 + k : ℝ)) * (momentPoly j k).eval (Real.log x)

/-- On the positive half-line the recurrence gives the next derivative. -/
private theorem moment_deriv_step (j k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (momentDeriv j k) (momentDeriv j (k + 1) x) x := by
  have hp := (momentPoly j k).hasDerivAt (Real.log x)
  have hl := hp.comp x (Real.hasDerivAt_log hx.ne')
  have hr := Real.hasDerivAt_rpow_const (x := x) (p := -(38 / 25 + k : ℝ)) (Or.inl hx.ne')
  apply (hr.mul hl).congr_deriv
  dsimp only [momentDeriv, momentPoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Function.comp_def]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 from Nat.cast_succ k,
    show -(38 / 25 + ((k : ℝ) + 1)) = -(38 / 25 + k) - 1 by ring, Real.rpow_sub hx, Real.rpow_one,
    div_eq_mul_inv]
  ring

/-- At order zero the derivative chain is exactly the Dirichlet integrand. -/
private theorem moment_deriv_zero (j : ℕ) {x : ℝ} (hx : 0 < x) :
    momentDeriv j 0 x = Real.log x ^ j / x ^ (38 / 25 : ℝ) := by
  simp only [momentDeriv, momentPoly, Nat.cast_zero, add_zero, Polynomial.eval_pow,
    Polynomial.eval_X, Real.rpow_neg hx.le, div_eq_mul_inv, mul_comm]

/-- Every member of the derivative chain is continuous on positive intervals. -/
private theorem moment_deriv_cont (j k : ℕ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (momentDeriv j k) (Set.Ici a) := by
  intro x hx
  exact (moment_deriv_step j k (ha.trans_le hx)).continuousAt.continuousWithinAt

/-- The first derivative comes from one step of the log-polynomial recurrence. -/
private theorem moment_deriv_one (j : ℕ) (x : ℝ) :
    momentDeriv j 1 x =
      x ^ (-(63 / 25 : ℝ)) * ((j : ℝ) * Real.log x ^ (j - 1) - (38 / 25) * Real.log x ^ j) := by
  simp only [momentDeriv, momentPoly, Nat.cast_zero, Nat.cast_one, add_zero,
    Polynomial.derivative_X_pow, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  norm_num only

/-- Both the moment and the first derivative vanish at the upper endpoint
of the corrected trapezoid rule. -/
private theorem moment_boundary_zero (j : ℕ) :
    Filter.Tendsto (momentDeriv j 0) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (momentDeriv j 1) Filter.atTop (nhds 0) := by
  constructor
  · apply (Analysis.log_pow_mul_neg_rpow_tendsto (r := 38 / 25) (by norm_num only) j).congr
    intro x
    simp only [momentDeriv, momentPoly, Nat.cast_zero, add_zero, Polynomial.eval_pow,
      Polynomial.eval_X]
  · have ha :=
      (Analysis.log_pow_mul_neg_rpow_tendsto (r := 63 / 25) (by norm_num only) (j - 1)).const_mul
        (j : ℝ)
    have hb :=
      (Analysis.log_pow_mul_neg_rpow_tendsto (r := 63 / 25) (by norm_num only) j).const_mul
        (38 / 25)
    have hh := ha.sub hb
    simp only [mul_zero, sub_zero] at hh
    apply hh.congr
    intro x
    rw [moment_deriv_one]
    ring

/-- The real zeta moment splits into a finite arithmetic sum and an
explicit corrected tail. Its error is bounded by the supplied summable
majorant for the fourth derivative on unit intervals. -/
private theorem moment_corrected_tail (j N : ℕ) (hN : 0 < N) (M : ℕ → ℝ)
    (hM : ∀ n : ℕ, ∀ x ∈ Set.Icc ((N : ℝ) + n) ((N : ℝ) + n + 1), |momentDeriv j 4 x| ≤ M n)
    (hm : Summable M) :
    |quarterZetaMoment j -
          ((∑ n ∈ Finset.range N, if n = 0 then 0 else (Real.log n) ^ j / (n : ℝ) ^ (38 / 25 : ℝ)) +
              (N : ℝ) ^ (-(13 / 25 : ℝ)) * Analysis.logPowerTailPoly (13 / 25) j (Real.log N) +
              momentDeriv j 0 N / 2 -
            momentDeriv j 1 N / 12)| ≤
      (∑' n : ℕ, M n) / 720 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show (1 : ℕ) ≤ N from hN)
  have he {x : ℝ} (hx : 0 < x) : momentDeriv j 0 x = Real.log x ^ j * x ^ (-(13 / 25 : ℝ) - 1) := by
    rw [moment_deriv_zero j hx, div_eq_mul_inv, ← Real.rpow_neg hx.le,
      show -(13 / 25 : ℝ) - 1 = -(38 / 25 : ℝ) by norm_num only]
  have hI := Analysis.log_power_tail_integrable (r := 13 / 25) (by norm_num only) hn₁ j
  have hI' : MeasureTheory.IntegrableOn (momentDeriv j 0) (Set.Ioi (N : ℝ)) :=
    hI.congr_fun (fun x hx ↦ (he (hn.trans hx)).symm) measurableSet_Ioi
  have hS := (summable_nat_add_iff N).mpr (quarter_zeta_moment_summable j)
  have hS' : Summable (fun n : ℕ ↦ momentDeriv j 0 ((N : ℝ) + n)) := by
    apply hS.congr
    intro n
    rw [ite_eq_right (Nat.lt_add_of_pos_right hN).ne_zero, Nat.cast_add, add_comm (n : ℝ),
      moment_deriv_zero j (add_pos_of_pos_of_nonneg hn (Nat.cast_nonneg _))]
  have h :=
    Analysis.corrected_trapezoid_tsum (momentDeriv j) N M
      (fun k x hx ↦ moment_deriv_step j k (hn.trans hx)) (fun k _ ↦ moment_deriv_cont j k hn) hM hI'
      hS' hm (moment_boundary_zero j).1 (moment_boundary_zero j).2
  have hval :
    (∫ x in Set.Ioi (N : ℝ), momentDeriv j 0 x) =
      (N : ℝ) ^ (-(13 / 25 : ℝ)) * Analysis.logPowerTailPoly (13 / 25) j (Real.log N) := by
    rw [← Analysis.log_power_tail_integral (by norm_num only : 0 < (13 / 25 : ℝ)) hn₁ j]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ he (hn.trans hx))
  rw [hval] at h
  rw [quarter_zeta_moment_split j N hN]
  simp_rw [← moment_deriv_zero j (add_pos_of_pos_of_nonneg hn (Nat.cast_nonneg _))]
  convert h using 2
  ring

/-- At orders zero through three, the fourth derivative polynomial is
bounded by 153 times its highest logarithmic power once log x is at least four. -/
private theorem moment_poly_four_bound (j : Fin 4) {z : ℝ} (hz : 4 ≤ z) :
    |(momentPoly j.val 4).eval z| ≤ 153 * z ^ j.val := by
  have h0 : 0 ≤ z := by linarith only [hz]
  have h1 : 0 ≤ z ^ 2 := sq_nonneg z
  have h2 : 0 ≤ z ^ 3 := pow_nonneg h0 3
  have h3 : 4 * z ≤ z ^ 2 := by nlinarith only [mul_nonneg h0 (sub_nonneg.mpr hz)]
  have h4 : 4 * z ^ 2 ≤ z ^ 3 := by nlinarith only [mul_nonneg h1 (sub_nonneg.mpr hz)]
  fin_cases j <;>
    norm_num only [momentPoly, Fin.val_zero, Fin.reduceFinMk, Nat.cast_ofNat, Nat.cast_zero,
      add_zero, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
      Polynomial.derivative_X_pow, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_zero,
      Polynomial.eval_one, Polynomial.derivative_X, Polynomial.derivative_one, zero_mul, mul_zero,
      mul_one, one_mul, sub_zero, zero_sub, add_zero, zero_add] <;>
    apply abs_le.mpr <;>
    constructor <;>
    nlinarith only [hz, h0, h1, h2, h3, h4]

/-- The common fourth-derivative majorant for the four logarithmic moments.
The decreasing log-cubic weight is used on the whole tail above 127. -/
private noncomputable def momentMajorant (x : ℝ) : ℝ :=
  Real.log x ^ 3 * x ^ (-(138 / 25 : ℝ))

/-- The tail majorant is decreasing and nonnegative from 127 onwards,
and integrable over the half-line by the logarithmic moment formula. -/
private theorem moment_majorant_properties :
    AntitoneOn momentMajorant (Set.Ici 127) ∧
      MeasureTheory.IntegrableOn momentMajorant (Set.Ioi (127 : ℝ)) ∧
      (∀ x ∈ Set.Ici (127 : ℝ), 0 ≤ momentMajorant x) := by
  have he :=
    (Analysis.rationalLogIntervalCheck_sound (N := 127) (j := 7) (n := 24) (lo := 4) (hi := 97 / 20)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at he
  have hf : momentMajorant = AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (138 / 25) 3 := by
    funext x
    unfold momentMajorant AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hf]
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    · exact fun x hx ↦
        (AnalyticNumberTheory.Arithmetic.mangoldt_moment_weight_deriv (138 / 25) 3
            (by linarith only [show (127 : ℝ) ≤ x from hx])).continuousAt.continuousWithinAt
    · exact fun x hx ↦
        (AnalyticNumberTheory.Arithmetic.mangoldt_moment_weight_deriv (138 / 25) 3
            (by linarith only [show (127 : ℝ) ≤ x from interior_subset hx])).hasDerivWithinAt
    · intro x hx
      have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 127) (interior_subset hx)
      exact
        AnalyticNumberTheory.Arithmetic.mangoldt_moment_deriv_nonpos 3 (by norm_num only)
          (by linarith only [show (127 : ℝ) ≤ x from interior_subset hx])
          (by
            norm_num only [Nat.cast_ofNat]; linarith only [he, h])
  · unfold momentMajorant
    rw [show -(138 / 25 : ℝ) = -(113 / 25 : ℝ) - 1 by norm_num only]
    exact Analysis.log_power_tail_integrable (by norm_num only) (by norm_num only) 3
  · intro x hx
    have h₀ : (1 : ℝ) ≤ x := le_trans (by norm_num only : (1 : ℝ) ≤ 127) hx
    unfold momentMajorant
    exact
      mul_nonneg (pow_nonneg (Real.log_nonneg h₀) _) (Real.rpow_nonneg (by linarith only [h₀]) _)

/-- On each unit interval of the tail the fourth derivative is bounded
by the left endpoint of the common decreasing majorant, scaled by 153. -/
private theorem moment_majorant_cell (j : Fin 4) (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc ((128 : ℝ) + n) ((128 : ℝ) + n + 1)) :
    |momentDeriv j.val 4 x| ≤ 153 * momentMajorant (128 + n) := by
  have ha : (127 : ℝ) ≤ 128 + n := by linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hb := ha.trans hx.1
  have h₀ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 127) (j := 7) (n := 24) (lo := 4) (hi := 97 / 20)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at h₀
  have hz := h₀.trans (Real.log_le_log (by norm_num only) hb)
  have hj := Nat.le_of_lt_succ j.isLt
  have hpow := pow_le_pow_right₀ (show 1 ≤ Real.log x by linarith only [hz]) hj
  have hxp : 0 ≤ x := by linarith only [hb]
  unfold momentDeriv
  rw [show -(38 / 25 + ((4 : ℕ) : ℝ)) = -(138 / 25 : ℝ) by norm_num only, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hxp _)]
  calc
    _ ≤ x ^ (-(138 / 25 : ℝ)) * (153 * Real.log x ^ j.val) :=
      mul_le_mul_of_nonneg_left (moment_poly_four_bound j hz) (Real.rpow_nonneg hxp _)
    _ ≤ 153 * momentMajorant x := by
      unfold momentMajorant
      have h := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hxp (-(138 / 25 : ℝ)))
      linarith only [h]
    _ ≤ _ := mul_le_mul_of_nonneg_left (moment_majorant_properties.1 ha hb hx.1) (by norm_num only)

/-- The sum of all fourth-derivative bounds divided by 720 is at most
two billionths. A single integral at 127 bounds the whole majorant series. -/
private theorem moment_majorant_total :
    Summable (fun n : ℕ ↦ 153 * momentMajorant (128 + n)) ∧
      (∑' n : ℕ, 153 * momentMajorant (128 + n)) / 720 ≤ 2 / 1000000000 := by
  obtain ⟨hm, hi, hn⟩ := moment_majorant_properties
  have hN : ∀ t ∈ Set.Ioi (127 : ℝ), 0 ≤ momentMajorant t := fun t ht ↦
    hn t (Set.mem_Ici.mpr (Set.mem_Ioi.mp ht).le)
  have hs := (summable_nat_add_iff 128).mpr (hm.summable_of_integrableOn_Ioi hi hN)
  have hs' : Summable (fun n : ℕ ↦ momentMajorant (128 + n)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat, add_comm] using hs
  refine ⟨hs'.mul_left 153, ?_⟩
  have h := hm.tsum_comp_add_le_integral 127 hi hN
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h
  rw [show (fun n : ℕ ↦ momentMajorant ((n : ℝ) + 127 + 1)) = (fun n : ℕ ↦ momentMajorant (128 + n))
      from funext (fun n ↦ congrArg momentMajorant (by ring))] at h
  have hI :
    (∫ x in Set.Ioi (127 : ℝ), momentMajorant x) =
      (127 : ℝ) ^ (-(113 / 25 : ℝ)) * Analysis.logPowerTailPoly (113 / 25) 3 (Real.log 127) := by
    unfold momentMajorant
    simp_rw [show -(138 / 25 : ℝ) = -(113 / 25 : ℝ) - 1 by norm_num only]
    exact Analysis.log_power_tail_integral (by norm_num only) (by norm_num only) 3
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 127) (j := 7) (n := 24) (lo := 4) (hi := 97 / 20)
        (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 127) (p := 113) (d :=
        25) (lo := 0) (hi := 31 / 100000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hp
  have hpoly :=
    Analysis.log_power_tail_poly_mono (by norm_num only : 0 < (113 / 25 : ℝ))
      (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 127)) hlog 3
  have hpos :=
    Analysis.log_power_tail_poly_nonneg (by norm_num only : 0 < (113 / 25 : ℝ))
      (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 127)) 3
  have he := mul_le_mul hp hpoly hpos (by norm_num only)
  have hval :
    (31 / 100000000000 : ℝ) * Analysis.logPowerTailPoly (113 / 25) 3 (97 / 20) ≤
      94 / 10000000000 := by
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.reduceAdd]
  rw [tsum_mul_left]
  linarith only [he.trans hval, h, hI]

/-- The four real moments use the same cutoff 128. Their explicit
corrected tails, added to the finite prefix, differ from the full moments
by at most two billionths. -/
theorem quarter_zeta_moment_corrected (j : Fin 4) :
    |quarterZetaMoment j.val -
          ((∑ n ∈ Finset.range 128,
                if n = 0 then 0 else (Real.log n) ^ j.val / (n : ℝ) ^ (38 / 25 : ℝ)) +
              (128 : ℝ) ^ (-(13 / 25 : ℝ)) *
                Analysis.logPowerTailPoly (13 / 25) j.val (Real.log 128) +
              Real.log 128 ^ j.val / (128 : ℝ) ^ (38 / 25 : ℝ) / 2 -
            (128 : ℝ) ^ (-(63 / 25 : ℝ)) *
                ((j.val : ℝ) * Real.log 128 ^ (j.val - 1) - (38 / 25) * Real.log 128 ^ j.val) /
              12)| ≤
      2 / 1000000000 := by
  have h :=
    moment_corrected_tail j.val 128 (by decide) (fun n ↦ 153 * momentMajorant (128 + n))
      (fun n x hx ↦ moment_majorant_cell j n hx) moment_majorant_total.1
  rw [moment_deriv_zero j.val (by norm_num only), moment_deriv_one] at h
  exact h.trans moment_majorant_total.2

end PseudoPrime.PrimeTestBounds.MillerRabin
