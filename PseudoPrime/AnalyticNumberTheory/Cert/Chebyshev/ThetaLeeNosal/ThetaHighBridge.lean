/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.Analysis.ScaledRationalPhase

import PseudoPrime.Analysis.SecondDerivativeInterpolation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhase
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteGridApprox
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadMidpointRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadDistance100
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt81Million
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.NormalizedLowerTail
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPhaseDefect
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPhaseEndpoints
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocal100Brackets
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevThetaPhaseCell
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevThetaHighRH
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Data.List.Forall2
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Lower Lee–Nosal bound from 279 billion onward -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Input: a rational phase with absolute value at most 4096.
Claim: length 16 and twelve squares on grid 10^12 have error at most 2125763/10^12.
Proof: bound the reduced phase by one and certify the finite budgets.
Role: provide uniform numerical parameters for low-frequency endpoint certificates. -/
private theorem pilot_grid_error (v : ℚ) (hv : |(v : ℝ)| ≤ 4096) :
    ‖Complex.exp (Complex.I * (v : ℂ)) -
          PseudoPrime.Analysis.rationalComplexCast
            (PseudoPrime.Analysis.rationalScaledPhase (10 ^ 12) v 16 12)‖ ≤
      (2125763 / 1000000000000 : ℝ) := by
  have hq : |((v / (2 : ℚ) ^ 12 : ℚ) : ℝ)| ≤ 1 := by
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, abs_div, abs_of_pos]
    linarith only [hv]
  have hp := pow_le_pow_left₀ (abs_nonneg ((v / (2 : ℚ) ^ 12 : ℚ) : ℝ)) hq 16
  have h :=
    PseudoPrime.Analysis.norm_scaled_phase_error (by norm_num only : 0 < 10 ^ 12) v 16 12
      (by
        norm_num only; linarith only [hq])
      (by
        norm_num only [Nat.factorial] at hp ⊢; nlinarith only [hp])
      (by
        intro j hj
        interval_cases j <;>
          norm_num only [PseudoPrime.Analysis.roundedSquareBudget, Rat.cast_div, Rat.cast_sub,
            Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast])
  norm_num only [PseudoPrime.Analysis.roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] at h
  exact h

/-- Input: a phase within epsilon of a rational center of magnitude at most 4096.
Claim: the scaled rational phase has error at most epsilon+2125763/10^12.
Proof: combine unit-phase stability and the certified scaled evaluator.
Role: supply a uniform phase uncertainty allowance at spectral nodes. -/
private theorem pilot_interval_error {θ ε : ℝ} (v : ℚ) (hv : |(v : ℝ)| ≤ 4096)
    (hε : |θ - (v : ℝ)| ≤ ε) :
    ‖Complex.exp (Complex.I * θ) -
          PseudoPrime.Analysis.rationalComplexCast
            (PseudoPrime.Analysis.rationalScaledPhase (10 ^ 12) v 16 12)‖ ≤
      ε + 2125763 / 1000000000000 := by
  have ht :=
    norm_sub_le_norm_sub_add_norm_sub (Complex.exp (Complex.I * θ))
      (Complex.exp (Complex.I * (v : ℂ)))
      (PseudoPrime.Analysis.rationalComplexCast
        (PseudoPrime.Analysis.rationalScaledPhase (10 ^ 12) v 16 12))
  have hc := PseudoPrime.Analysis.norm_phase_exp_sub_le θ (v : ℝ)
  simp only [Complex.ofReal_ratCast] at hc
  exact ht.trans (add_le_add (hc.trans hε) (pilot_grid_error v hv))

/-- Positive weights transport the two coordinate errors to a signed numerator bound. -/
private theorem pilot_weighted_error {z w : ℂ} {e g : ℝ} (hg : 0 ≤ g) (h : ‖z - w‖ ≤ e) :
    z.re + 2 * g * z.im ≤ w.re + 2 * g * w.im + (1 + 2 * g) * e := by
  have hr := (le_abs_self _).trans ((Complex.abs_re_le_norm (z - w)).trans h)
  have hi := (le_abs_self _).trans ((Complex.abs_im_le_norm (z - w)).trans h)
  rw [Complex.sub_re] at hr
  rw [Complex.sub_im] at hi
  have hw := mul_le_mul_of_nonneg_left hi (mul_nonneg (zero_le_two : (0 : ℝ) ≤ 2) hg)
  linarith only [hr, hw]

/-- Bound the signed center contribution for an actual real phase using the rounded evaluator. -/
private theorem pilot_center_bound (v : ℚ) (θ g : ℝ) (hg : 0 ≤ g) (hv : |(v : ℝ)| ≤ 4096) :
    let z := Complex.exp (Complex.I * θ)
    let w :=
      PseudoPrime.Analysis.rationalComplexCast
        (PseudoPrime.Analysis.rationalScaledPhase (10 ^ 12) v 16 12)
    (z.re + 2 * g * z.im) / (1 / 4 + g * g) ≤
      (w.re + 2 * g * w.im + (1 + 2 * g) * (|θ - (v : ℝ)| + 2125763 / 1000000000000)) /
        (1 / 4 + g * g) := by
  have he := pilot_interval_error v hv (le_refl |θ - (v : ℝ)|)
  exact
    div_le_div_of_nonneg_right (pilot_weighted_error hg he)
      (add_nonneg (by norm_num only) (mul_self_nonneg g))

private noncomputable def realTerm (g t : ℚ) : ℝ :=
  let z := Complex.exp (Complex.I * ((g * t : ℚ) : ℝ))
  (z.re + 2 * (g : ℝ) * z.im) / (1 / 4 + (g : ℝ) * g)

private def upperTerm (g t v : ℚ) : ℚ :=
  let z := PseudoPrime.Analysis.rationalScaledPhase (10 ^ 12) v 16 12
  let e := 2125763 / 1000000000000 + |g * t - v|
  (z.1 + 2 * g * z.2 + (1 + 2 * g) * e) / (1 / 4 + g * g)

private theorem term_le_upper (g t v : ℚ) (hg : 0 ≤ g) (hv : |v| ≤ 4096) :
    realTerm g t ≤ (upperTerm g t v : ℝ) := by
  have h :=
    pilot_center_bound v ((g * t : ℚ) : ℝ) (g : ℝ) (by exact_mod_cast hg) (by exact_mod_cast hv)
  simp only [realTerm, upperTerm, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_abs, Rat.cast_one, Rat.cast_ofNat, PseudoPrime.Analysis.rationalComplexCast] at h ⊢
  simpa only [add_comm (2125763 / 1000000000000 : ℝ)] using h

private theorem sum_le_upper (t : ℚ) (ps : List (ℚ × ℚ)) (h : ∀ p ∈ ps, 0 ≤ p.1 ∧ |p.2| ≤ 4096) :
    (ps.map (fun p => realTerm p.1 t)).sum ≤
      (((ps.map (fun p => upperTerm p.1 t p.2)).sum : ℚ) : ℝ) := by
  induction ps with
  | nil => exact le_of_eq Rat.cast_zero.symm
  | cons p ps ih =>
    have hp := h p List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, Rat.cast_add]
    exact
      add_le_add (term_le_upper _ _ _ hp.1 hp.2) (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)))

private def pairs0 : List (ℚ × ℚ) :=
  [((361953 / 25600), (781441391 / 2097152)), ((269139 / 12800), (2324239385 / 4194304)),
    ((640403 / 25600), (11060826375 / 16777216)), ((779003 / 25600), (1681834901 / 2097152)),
    ((843253 / 25600), (14564383713 / 16777216)), ((120291 / 3200), (8310503639 / 8388608)),
    ((261907 / 6400), (9047140171 / 8388608)), ((554639 / 12800), (19159078517 / 16777216)),
    ((1229053 / 25600), (2653474031 / 2097152)), ((159291 / 3200), (22009766901 / 16777216)),
    ((1356153 / 25600), (23423020927 / 16777216)), ((180641 / 3200), (12479883681 / 8388608)),
    ((1519403 / 25600), (13121310157 / 8388608)), ((1557403 / 25600), (26898943601 / 16777216)),
    ((1667003 / 25600), (28791918135 / 16777216)), ((1717353 / 25600), (29661546491 / 16777216)),
    ((1780503 / 25600), (30752252165 / 16777216)), ((461257 / 6400), (31866706379 / 16777216)),
    ((1938153 / 25600), (33475130225 / 16777216)), ((493757 / 6400), (34112022889 / 16777216)),
    ((2031153 / 25600), (4385174389 / 2097152)), ((530657 / 6400), (18330660355 / 8388608)),
    ((2169353 / 25600), (37468339279 / 16777216)), ((2238203 / 25600), (19328746723 / 8388608)),
    ((568407 / 6400), (39269342195 / 16777216)), ((2367903 / 25600), (5112203557 / 2097152)),
    ((1211589 / 12800), (10463079941 / 4194304)), ((2454403 / 25600), (21195813759 / 8388608)),
    ((2530203 / 25600), (2731301235 / 1048576))]

private noncomputable def centerSum0 : ℝ :=
  (pairs0.map (fun p => realTerm p.1 (2635447 / 100000))).sum

/-- Scalar upper bound for the actual center sum at this pilot node. -/
private theorem realNode0 : centerSum0 ≤ 7 / 256 := by
  have h := sum_le_upper (2635447 / 100000) pairs0 (by decide +kernel)
  have hq : (pairs0.map (fun p => upperTerm p.1 (2635447 / 100000) p.2)).sum ≤ 7 / 256 := by
    decide +kernel
  exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hq)

private def pairs1 : List (ℚ × ℚ) :=
  [((361953 / 25600), (6260161403 / 16777216)), ((269139 / 12800), (2327448011 / 4194304)),
    ((640403 / 25600), (11076095911 / 16777216)), ((779003 / 25600), (13473253471 / 16777216)),
    ((843253 / 25600), (7292244965 / 8388608)), ((120291 / 3200), (4160988169 / 4194304)),
    ((261907 / 6400), (9059629801 / 8388608)), ((554639 / 12800), (19185527737 / 16777216)),
    ((1229053 / 25600), (21257097339 / 16777216)), ((159291 / 3200), (22040151513 / 16777216)),
    ((1356153 / 25600), (23455356545 / 16777216)), ((180641 / 3200), (24994224467 / 16777216)),
    ((1519403 / 25600), (26278848405 / 16777216)), ((1557403 / 25600), (13468038875 / 8388608)),
    ((1667003 / 25600), (28831665547 / 16777216)), ((1717353 / 25600), (14851247215 / 8388608)),
    ((1780503 / 25600), (30794705829 / 16777216)), ((461257 / 6400), (31910698553 / 16777216)),
    ((1938153 / 25600), (16760671419 / 8388608)), ((493757 / 6400), (2134944671 / 1048576)),
    ((2031153 / 25600), (1097807037 / 524288)), ((530657 / 6400), (18355965939 / 8388608)),
    ((2169353 / 25600), (9380016135 / 4194304)), ((2238203 / 25600), (19355430171 / 8388608)),
    ((568407 / 6400), (39323553751 / 16777216)), ((2367903 / 25600), (40954087871 / 16777216)),
    ((1211589 / 12800), (2619381071 / 1048576)), ((2454403 / 25600), (1326567169 / 524288)),
    ((2530203 / 25600), (43761148997 / 16777216))]

private noncomputable def centerSum1 : ℝ :=
  (pairs1.map (fun p => realTerm p.1 (10556341 / 400000))).sum

/-- Scalar upper bound for the actual center sum at this pilot node. -/
private theorem realNode1 : centerSum1 ≤ 49 / 256 := by
  have h := sum_le_upper (10556341 / 400000) pairs1 (by decide +kernel)
  have hq : (pairs1.map (fun p => upperTerm p.1 (10556341 / 400000) p.2)).sum ≤ 49 / 256 := by
    decide +kernel
  exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hq)

private def pairs2 : List (ℚ × ℚ) :=
  [((361953 / 25600), (6268791679 / 16777216)), ((269139 / 12800), (9322626549 / 16777216)),
    ((640403 / 25600), (5545682723 / 8388608)), ((779003 / 25600), (6745913867 / 8388608)),
    ((843253 / 25600), (14604596147 / 16777216)), ((120291 / 3200), (8333449037 / 8388608)),
    ((261907 / 6400), (18144238861 / 16777216)), ((554639 / 12800), (19211976957 / 16777216)),
    ((1229053 / 25600), (10643201215 / 8388608)), ((159291 / 3200), (22070536125 / 16777216)),
    ((1356153 / 25600), (11743846081 / 8388608)), ((180641 / 3200), (25028681571 / 16777216)),
    ((1519403 / 25600), (26315076495 / 16777216)), ((1557403 / 25600), (26973211899 / 16777216)),
    ((1667003 / 25600), (14435706479 / 8388608)), ((1717353 / 25600), (464741287 / 262144)),
    ((1780503 / 25600), (30837159493 / 16777216)), ((461257 / 6400), (3994336341 / 2097152)),
    ((1938153 / 25600), (33567555451 / 16777216)), ((493757 / 6400), (34206206583 / 16777216)),
    ((2031153 / 25600), (35178255255 / 16777216)), ((530657 / 6400), (18381271523 / 8388608)),
    ((2169353 / 25600), (18785894901 / 8388608)), ((2238203 / 25600), (38764227237 / 16777216)),
    ((568407 / 6400), (9844441327 / 4194304)), ((2367903 / 25600), (20505273643 / 8388608)),
    ((1211589 / 12800), (41967874509 / 16777216)), ((2454403 / 25600), (21254335649 / 8388608)),
    ((2530203 / 25600), (21910739117 / 8388608))]

private noncomputable def centerSum2 : ℝ :=
  (pairs2.map (fun p => realTerm p.1 (5285447 / 200000))).sum

/-- Scalar upper bound for the actual center sum at this pilot node. -/
private theorem realNode2 : centerSum2 ≤ 41 / 256 := by
  have h := sum_le_upper (5285447 / 200000) pairs2 (by decide +kernel)
  have hq : (pairs2.map (fun p => upperTerm p.1 (5285447 / 200000) p.2)).sum ≤ 41 / 256 := by
    decide +kernel
  exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hq)

private def pairs3 : List (ℚ × ℚ) :=
  [((361953 / 25600), (3138710977 / 8388608)), ((269139 / 12800), (9335461053 / 16777216)),
    ((640403 / 25600), (5553317491 / 8388608)), ((779003 / 25600), (6755200999 / 8388608)),
    ((843253 / 25600), (3656175591 / 4194304)), ((120291 / 3200), (16689843471 / 16777216)),
    ((261907 / 6400), (18169218121 / 16777216)), ((554639 / 12800), (19238426177 / 16777216)),
    ((1229053 / 25600), (10657853761 / 8388608)), ((159291 / 3200), (22100920737 / 16777216)),
    ((1356153 / 25600), (5880006945 / 4194304)), ((180641 / 3200), (6265784669 / 4194304)),
    ((1519403 / 25600), (13175652293 / 8388608)), ((1557403 / 25600), (422036657 / 262144)),
    ((1667003 / 25600), (14455580185 / 8388608)), ((1717353 / 25600), (29784390307 / 16777216)),
    ((1780503 / 25600), (30879613157 / 16777216)), ((461257 / 6400), (31998682903 / 16777216)),
    ((1938153 / 25600), (262607563 / 131072)), ((493757 / 6400), (17126649215 / 8388608)),
    ((2031153 / 25600), (17613342663 / 8388608)), ((530657 / 6400), (36813154213 / 16777216)),
    ((2169353 / 25600), (4702939383 / 2097152)), ((2238203 / 25600), (38817594133 / 16777216)),
    ((568407 / 6400), (39431976865 / 16777216)), ((2367903 / 25600), (20533503351 / 8388608)),
    ((1211589 / 12800), (42025651881 / 16777216)), ((2454403 / 25600), (42567193187 / 16777216)),
    ((2530203 / 25600), (2742612967 / 1048576))]

private noncomputable def centerSum3 : ℝ :=
  (pairs3.map (fun p => realTerm p.1 (10585447 / 400000))).sum

/-- Scalar upper bound for the actual center sum at this pilot node. -/
private theorem realNode3 : centerSum3 ≤ 24 / 256 := by
  have h := sum_le_upper (10585447 / 400000) pairs3 (by decide +kernel)
  have hq : (pairs3.map (fun p => upperTerm p.1 (10585447 / 400000) p.2)).sum ≤ 24 / 256 := by
    decide +kernel
  exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hq)

private def pairs4 : List (ℚ × ℚ) :=
  [((361953 / 25600), (6286052229 / 16777216)), ((269139 / 12800), (9348295557 / 16777216)),
    ((640403 / 25600), (11121904517 / 16777216)), ((779003 / 25600), (13528976261 / 16777216)),
    ((843253 / 25600), (14644808581 / 16777216)), ((120291 / 3200), (16712788869 / 16777216)),
    ((261907 / 6400), (18194197381 / 16777216)), ((554639 / 12800), (19264875397 / 16777216)),
    ((1229053 / 25600), (21345012613 / 16777216)), ((159291 / 3200), (22131305349 / 16777216)),
    ((1356153 / 25600), (23552363397 / 16777216)), ((180641 / 3200), (25097595781 / 16777216)),
    ((1519403 / 25600), (26387532677 / 16777216)), ((1557403 / 25600), (27047480197 / 16777216)),
    ((1667003 / 25600), (28950907781 / 16777216)), ((1717353 / 25600), (29825338245 / 16777216)),
    ((1780503 / 25600), (30922066821 / 16777216)), ((461257 / 6400), (32042675077 / 16777216)),
    ((1938153 / 25600), (33659980677 / 16777216)), ((493757 / 6400), (34300390277 / 16777216)),
    ((2031153 / 25600), (35275115397 / 16777216)), ((530657 / 6400), (36863765381 / 16777216)),
    ((2169353 / 25600), (37675240325 / 16777216)), ((2238203 / 25600), (38870961029 / 16777216)),
    ((568407 / 6400), (39486188421 / 16777216)), ((2367903 / 25600), (41123466117 / 16777216)),
    ((1211589 / 12800), (42083429253 / 16777216)), ((2454403 / 25600), (42625715077 / 16777216)),
    ((2530203 / 25600), (43942136709 / 16777216))]

private noncomputable def centerSum4 : ℝ :=
  (pairs4.map (fun p => realTerm p.1 (53 / 2))).sum

/-- Scalar upper bound for the actual center sum at this pilot node. -/
private theorem realNode4 : centerSum4 ≤ -57 / 256 := by
  have h := sum_le_upper (53 / 2) pairs4 (by decide +kernel)
  have hq : (pairs4.map (fun p => upperTerm p.1 (53 / 2) p.2)).sum ≤ -57 / 256 := by decide +kernel
  exact
    h.trans
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using (Rat.cast_le (K := ℝ)).2 hq)

/-- Signed oscillation at height g before division by the positive denominator. -/
private noncomputable def osc (g t : ℝ) : ℝ :=
  Real.cos (g * t) + 2 * g * Real.sin (g * t)

/-- First derivative of the signed numerator. -/
private noncomputable def velocity (g t : ℝ) : ℝ :=
  -g * Real.sin (g * t) + 2 * g ^ 2 * Real.cos (g * t)

private theorem osc_deriv (g t : ℝ) : HasDerivAt (osc g) (velocity g t) t := by
  have h := (hasDerivAt_id t).const_mul g
  convert
    ((Real.hasDerivAt_cos _).comp t h).add
      (((Real.hasDerivAt_sin _).comp t h).const_mul (2 * g)) using
    1
  · rfl
  · dsimp only [velocity, id_eq]
    ring

private theorem velocity_deriv (g t : ℝ) : HasDerivAt (velocity g) (-(g ^ 2) * osc g t) t := by
  have h := (hasDerivAt_id t).const_mul g
  convert
    (((Real.hasDerivAt_sin _).comp t h).const_mul (-g)).add
      (((Real.hasDerivAt_cos _).comp t h).const_mul (2 * g ^ 2)) using
    1
  · rfl
  · dsimp only [osc, id_eq]
    ring

/-- A square identity bounds curvature without summing absolute sine and cosine coefficients. -/
private theorem osc_cap (g t : ℝ) (hg : 0 < g) : g * osc g t ≤ 2 * (1 / 4 + g * g) := by
  have hs := Real.sin_sq_add_cos_sq (g * t)
  have hsq := sq_nonneg (2 * g * Real.cos (g * t) - Real.sin (g * t))
  have hnorm : (osc g t) ^ 2 ≤ 1 + 4 * g ^ 2 := by
    unfold osc
    nlinarith only [hsq, hs, congrArg (fun x : ℝ => 4 * g ^ 2 * x) hs]
  by_contra! h
  have hp := mul_self_lt_mul_self (by positivity : 0 ≤ 2 * (1 / 4 + g * g)) h
  nlinarith only [hp, mul_le_mul_of_nonneg_left hnorm (sq_nonneg g), sq_nonneg g]

/-- The negative center sum and its first two derivatives use the same heights. -/
private noncomputable def moments (gs : List ℝ) (t : ℝ) (k : Nat) : ℝ :=
  (gs.map
      (fun g =>
        (match k with
          | 0 => -(osc g t)
          | 1 => -(velocity g t)
          | _ => g ^ 2 * osc g t) /
          (1 / 4 + g * g))).sum

private theorem moments_deriv (gs : List ℝ) (t : ℝ) :
    HasDerivAt (fun x => moments gs x 0) (moments gs t 1) t ∧
      HasDerivAt (fun x => moments gs x 1) (moments gs t 2) t := by
  induction gs with
  | nil => exact ⟨hasDerivAt_const t 0, hasDerivAt_const t 0⟩
  | cons g gs ih =>
    have h := ((osc_deriv g t).neg.div_const (1 / 4 + g * g)).add ih.1
    have h' := ((velocity_deriv g t).neg.div_const (1 / 4 + g * g)).add ih.2
    rw [neg_mul, neg_neg] at h'
    exact ⟨h, h'⟩

private theorem moments_cap (gs : List ℝ) (t : ℝ) (hp : ∀ g ∈ gs, 0 < g) :
    moments gs t 2 ≤ 2 * gs.sum := by
  induction gs with
  | nil => exact le_of_eq (mul_zero 2).symm
  | cons g gs ih =>
    have hg := hp g List.mem_cons_self
    have hd : 0 < 1 / 4 + g * g := by positivity
    have hb := mul_le_mul_of_nonneg_left (osc_cap g t hg) hg.le
    have hterm : g ^ 2 * osc g t / (1 / 4 + g * g) ≤ 2 * g :=
      (div_le_iff₀ hd).mpr (by nlinarith only [hb])
    change _ + moments gs t 2 ≤ 2 * (g + gs.sum)
    rw [mul_add]
    exact add_le_add hterm (ih (fun z hz => hp z (List.mem_cons_of_mem _ hz)))

/-- Endpoint upper bounds extend over the cell with curvature cost sum(g) times width²/4. -/
private theorem centers_chord (gs : List ℝ) (hp : ∀ g ∈ gs, 0 < g) {a b x c : ℝ} (hab : a < b)
    (hx : x ∈ Set.Icc a b) (ha : -moments gs a 0 ≤ c) (hb : -moments gs b 0 ≤ c) :
    -moments gs x 0 ≤ c + gs.sum * (b - a) ^ 2 / 4 := by
  have hpos := List.sum_nonneg (fun g hg => (hp g hg).le)
  have h :=
    PseudoPrime.Analysis.lower_bound_on_interval_of_second_deriv_le hab
      (mul_nonneg zero_le_two hpos) (fun y _ => (moments_deriv gs y).1)
      (fun y _ => (moments_deriv gs y).2) (fun y _ => moments_cap gs y hp) (neg_le.mp ha)
      (neg_le.mp hb) hx
  linarith only [h]

private theorem velocity_cap (g t : ℝ) : -velocity g t / (1 / 4 + g * g) ≤ 2 := by
  have hs := Real.sin_sq_add_cos_sq (g * t)
  have hs' := congrArg (fun x : ℝ => g ^ 2 * (1 + 4 * g ^ 2) * x) hs
  have hsq := sq_nonneg (g * Real.cos (g * t) + 2 * g ^ 2 * Real.sin (g * t))
  have hn : (velocity g t) ^ 2 ≤ g ^ 2 * (1 + 4 * g ^ 2) := by
    unfold velocity
    nlinarith only [hs', hsq]
  have hd : 0 < 1 / 4 + g * g := add_pos_of_pos_of_nonneg (by norm_num only) (mul_self_nonneg g)
  apply (div_le_iff₀ hd).mpr
  by_contra! h
  have hh := mul_self_lt_mul_self (mul_nonneg zero_le_two hd.le) h
  nlinarith only [hh, hn, sq_nonneg g]

private theorem slope_cap (gs : List ℝ) (t : ℝ) : moments gs t 1 ≤ 2 * gs.length := by
  induction gs with
  | nil =>
    exact
      le_of_eq
        (by
          norm_num only [moments, List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero,
            mul_zero])
  | cons g gs ih =>
    change -velocity g t / _ + moments gs t 1 ≤ _
    rw [List.length_cons, Nat.cast_add_one]
    linarith only [velocity_cap g t, ih]

/-- Move left of the sampled endpoint at cost two per center per unit distance. -/
private theorem left_shift (gs : List ℝ) {x a : ℝ} (hx : x ≤ a) :
    -moments gs x 0 ≤ -moments gs a 0 + 2 * gs.length * (a - x) := by
  rcases hx.eq_or_lt with rfl | hlt
  · rw [sub_self, mul_zero, add_zero]
  obtain ⟨c, _, hc⟩ :=
    exists_hasDerivAt_eq_slope (fun y => moments gs y 0) (fun y => moments gs y 1) hlt
      (fun y _ => (moments_deriv gs y).1.continuousAt.continuousWithinAt)
      (fun y _ => (moments_deriv gs y).1)
  have h := slope_cap gs c
  rw [hc] at h
  linarith only [(div_le_iff₀ (sub_pos.mpr hlt)).mp h]

private theorem center_sum_eq (ps : List (ℚ × ℚ)) (t : ℚ) :
    -moments (ps.map (fun p => (p.1 : ℝ))) (t : ℝ) 0 = (ps.map (fun p => realTerm p.1 t)).sum := by
  induction ps with
  | nil => exact neg_zero
  | cons p ps ih =>
    change -(_ + moments _ _ 0) = realTerm p.1 t + _
    rw [neg_add, ih]
    congr 1
    simp only [realTerm, osc, mul_comm Complex.I, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Rat.cast_mul, neg_div, neg_neg]

/-- The smoothing ratio decreases from any left endpoint at least two. -/
private theorem ratio_le_left {a L : ℝ} (ha : 2 ≤ a) (hL : a ≤ L) :
    L / Real.exp (L / 2) ≤ a / Real.exp (a / 2) := by
  have he := Real.add_one_le_exp ((L - a) / 2)
  have hp := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hL)
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ a by linarith only [ha])
  have h : L ≤ a * Real.exp ((L - a) / 2) := by nlinarith only [hm, hp]
  apply (div_le_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)).mpr
  have hsum : (L - a) / 2 + a / 2 = L / 2 := by ring
  simpa only [mul_assoc, ← Real.exp_add, hsum] using
    mul_le_mul_of_nonneg_right h (Real.exp_pos (a / 2)).le

/-- A certified endpoint cap bounds the log shift throughout the closed smoothing cell. -/
private theorem smooth_mem {a b L D : ℝ} (ha : 2 ≤ a) (hL : L ∈ Set.Icc a b)
    (hcap : a / Real.exp (a / 2) / 4 ≤ D) (hD : D < 1) :
    L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2) ∈ Set.Icc (a - D / (2 - D)) b := by
  let u := L / Real.exp (L / 2) / 4
  have hu : u ≤ D :=
    (div_le_div_of_nonneg_right (ratio_le_left ha hL.1) (by norm_num only : (0 : ℝ) ≤ 4)).trans hcap
  have hu0 : 0 ≤ u :=
    div_nonneg (div_nonneg (by linarith only [ha, hL.1]) (Real.exp_pos _).le) (by norm_num only)
  have harg : 0 < 1 - u / 2 := by linarith only [hu, hD]
  have hlog := Real.one_sub_inv_le_log_of_pos harg
  have hlo : -(D / (2 - D)) ≤ 1 - (1 - u / 2)⁻¹ := by
    have hd : 0 < 2 - D := by linarith only [hD]
    have heq : 1 + D / (2 - D) = 2 / (2 - D) := by
      field_simp [hd.ne']
      ring
    have hc : (1 - u / 2)⁻¹ ≤ 2 / (2 - D) := by
      rw [← one_div, div_le_div_iff₀ harg hd]
      linarith only [hu]
    linarith only [hc, heq]
  change L + Real.log (1 - u / 2) ∈ Set.Icc _ _
  constructor
  · linarith only [hlo, hlog, hL.1]
  · linarith only [Real.log_le_sub_one_of_pos harg, hu0, hL.2]

private def expLower (a : ℚ) : ℚ :=
  (Finset.range 56).sum (fun i => (a / 2) ^ i / i.factorial)

private theorem cap_of_ticks (a D : ℚ) (ha : 0 ≤ a) (hd : 0 ≤ D) (h : a ≤ 4 * D * expLower a) :
    (a : ℝ) / Real.exp (a / 2) / 4 ≤ D := by
  have he :=
    Real.sum_le_exp_of_nonneg (x := (a : ℝ) / 2) (div_nonneg (by exact_mod_cast ha) zero_le_two) 56
  have hc : (expLower a : ℝ) ≤ Real.exp (a / 2) := by
    simpa only [expLower, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_ofNat] using he
  have hr : (a : ℝ) ≤ 4 * (D : ℝ) * (expLower a : ℝ) := by exact_mod_cast h
  have hd' : 0 ≤ (D : ℝ) := by exact_mod_cast hd
  have hm := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hd')
  apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 4)).mpr
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith only [hr, hm]

/-- The lower midpoint used by the explicit formula is positive and has the sampled log phase. -/
private theorem midpoint_phase (L u : ℝ) (hu : u < 1) :
    let x := Real.exp L
    0 < (x - x * u + x) / 2 ∧ Real.log ((x - x * u + x) / 2) = L + Real.log (1 - u / 2) := by
  have hf : 0 < 1 - u / 2 := by linarith only [hu]
  have he : (Real.exp L - Real.exp L * u + Real.exp L) / 2 = Real.exp L * (1 - u / 2) := by ring
  dsimp only
  rw [he, Real.log_mul (Real.exp_pos L).ne' hf.ne', Real.log_exp]
  exact ⟨mul_pos (Real.exp_pos L) hf, rfl⟩

/-- A Taylor lower bound at a rational argument certifies decay throughout a cell. -/
private theorem decay_tick (q U : ℚ) {z : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ U) (hz : (q : ℝ) ≤ z)
    (hc : 1 ≤ U * expLower (2 * q)) : Real.exp (-z) ≤ (U : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg (by exact_mod_cast hq : 0 ≤ (q : ℝ)) 56
  have hl : (expLower (2 * q) : ℝ) ≤ Real.exp (q : ℝ) := by
    simpa only [expLower, mul_div_cancel_left₀ q (by decide : (2 : ℚ) ≠ 0), Rat.cast_sum,
      Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using he
  have hr := (Rat.cast_le (K := ℝ)).2 hc
  rw [Rat.cast_one, Rat.cast_mul] at hr
  rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos z)]
  exact
    hr.trans (mul_le_mul_of_nonneg_left (hl.trans (Real.exp_le_exp.mpr hz)) (by exact_mod_cast hu))

/-- Certify a Lee-Nosal floor at a rational left endpoint; the same floor holds to its right. -/
private theorem coefficient_tick (a q c : ℚ) {L : ℝ} (ha : 1 ≤ a) (hq : 0 ≤ q) (hc : 0 ≤ c)
    (hqa : q ≤ a) (he : a ≤ expLower (2 * q)) (hprod : c * (8 * (31416 / 10000)) ≤ a * (a - q))
    (hL : (a : ℝ) ≤ L) : (c : ℝ) ≤ L * (L - Real.log L) / (8 * Real.pi) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hp : (0 : ℝ) < a := zero_lt_one.trans_le ha'
  have ht := Real.sum_le_exp_of_nonneg (by exact_mod_cast hq : 0 ≤ (q : ℝ)) 56
  have hx : (expLower (2 * q) : ℝ) ≤ Real.exp (q : ℝ) := by
    simpa only [expLower, mul_div_cancel_left₀ q (by decide : (2 : ℚ) ≠ 0), Rat.cast_sum,
      Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using ht
  have hlog := (Real.log_le_iff_le_exp hp).2 (((Rat.cast_le (K := ℝ)).2 he).trans hx)
  have hratio := Real.log_le_sub_one_of_pos (div_pos (hp.trans_le hL) hp)
  rw [Real.log_div (hp.trans_le hL).ne' hp.ne'] at hratio
  have hr : L / a - 1 ≤ L - a := by
    have h := mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr ha')
    have hdiv := (div_le_iff₀ hp).mpr (show L ≤ (L - a + 1) * a by nlinarith only [h])
    linarith only [hdiv]
  have hd : (a : ℝ) - q ≤ L - Real.log L := by linarith only [hratio, hr, hlog]
  have hn : (0 : ℝ) ≤ a - q := sub_nonneg.mpr ((Rat.cast_le (K := ℝ)).2 hqa)
  have hm := mul_le_mul hL hd hn (hp.trans_le hL).le
  have hc' := (Rat.cast_le (K := ℝ)).2 hprod
  norm_num only [Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at hc'
  apply (le_div_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).mpr
  have hpi :=
    mul_le_mul_of_nonneg_left
      (show 8 * Real.pi ≤ 8 * (31416 / 10000 : ℝ) by linarith only [Real.pi_lt_d4])
      (show (0 : ℝ) ≤ c by exact_mod_cast hc)
  linarith only [hpi, hc', hm]

private noncomputable def pole (g : ℝ) : ℂ :=
  ⟨1 / 2, g⟩

private noncomputable def wave (g t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (g * t : ℝ))

private theorem pole_norm (g : ℝ) : g ≤ ‖pole g‖ :=
  (le_abs_self g).trans (Complex.abs_im_le_norm (pole g))

private theorem pole_gap (g c : ℝ) : ‖pole c - pole g‖ = |g - c| := by
  have he : pole c - pole g = ((c - g : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp only [pole, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
      ring
  rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]

private theorem wave_gap (g c t : ℝ) : ‖wave g t - wave c t‖ ≤ |g - c| * |t| := by
  simpa only [wave, ← sub_mul, abs_mul] using
    PseudoPrime.Analysis.norm_phase_exp_sub_le (g * t) (c * t)

/-- Changing the ordinate costs one phase displacement and one reciprocal displacement. -/
private theorem pole_wave_gap (g c t a : ℝ) (ha : 0 < a) (hg : a ≤ g) (hc : a ≤ c) :
    ‖wave g t / pole g - wave c t / pole c‖ ≤ |g - c| * (|t| / a + 1 / a ^ 2) := by
  have h1 := hg.trans (pole_norm g)
  have h2 := hc.trans (pole_norm c)
  have ng := (norm_pos_iff.mp (ha.trans_le h1))
  have nc := (norm_pos_iff.mp (ha.trans_le h2))
  have he :
    wave g t / pole g - wave c t / pole c =
      (wave g t - wave c t) / pole g + wave c t * (pole c - pole g) / (pole g * pole c) := by
    field_simp [ng, nc]
    ring
  have hw : ‖wave c t‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  have hprod : a ^ 2 ≤ ‖pole g‖ * ‖pole c‖ := by
    rw [pow_two]
    exact mul_le_mul h1 h2 ha.le (ha.trans_le h1).le
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, norm_div, norm_mul, norm_mul, hw, one_mul, pole_gap]
  have hleft := div_le_div₀ (mul_nonneg (abs_nonneg (g - c)) (abs_nonneg t)) (wave_gap g c t) ha h1
  have hright := div_le_div_of_nonneg_left (abs_nonneg (g - c)) (sq_pos_of_pos ha) hprod
  calc
    _ ≤ |g - c| * |t| / a + |g - c| / a ^ 2 := add_le_add hleft hright
    _ = _ := by ring

/-- Each box has radius 1 / 200; the signed zero term uses twice the real part. -/
private theorem box_term_le {g t a b : ℝ} (ha : 0 < a) (hg : g ∈ Set.Icc a (a + 1 / 100))
    (ht : |t| ≤ b) :
    2 * (wave g t / pole g).re ≤
      2 * (wave (a + 1 / 200) t / pole (a + 1 / 200)).re + (1 / 100) * (b / a + 1 / a ^ 2) := by
  let c := a + 1 / 200
  have hr : |g - c| ≤ 1 / 200 :=
    abs_le.mpr
      ⟨by
        dsimp only [c]; linarith only [hg.1], by
        dsimp only [c]; linarith only [hg.2]⟩
  have he :=
    pole_wave_gap g c t a ha hg.1
      (by
        dsimp only [c]; linarith only)
  have h := (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans he)
  rw [Complex.sub_re] at h
  have hb := add_le_add (div_le_div_of_nonneg_right ht ha.le) (le_refl (1 / a ^ 2))
  have hn := add_nonneg (div_nonneg (abs_nonneg t) ha.le) (one_div_nonneg.mpr (sq_nonneg a))
  have hm := mul_le_mul hr hb hn (by norm_num only : (0 : ℝ) ≤ 1 / 200)
  change 2 * _ ≤ 2 * (wave c t / pole c).re + _
  linarith only [h, hm]

private theorem boxes_sum_le {n : ℕ} (g a : Fin n → ℝ) {t b : ℝ} (ha : ∀ i, 0 < a i)
    (hg : ∀ i, g i ∈ Set.Icc (a i) (a i + 1 / 100)) (ht : |t| ≤ b) :
    ∑ i, 2 * (wave (g i) t / pole (g i)).re ≤
      (∑ i, 2 * (wave (a i + 1 / 200) t / pole (a i + 1 / 200)).re) +
        ∑ i, (1 / 100) * (b / a i + 1 / (a i) ^ 2) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => box_term_le (ha i) (hg i) ht)

private theorem signed_eq (g t : ℝ) : 2 * (wave g t / pole g).re = osc g t / (1 / 4 + g * g) := by
  simp only [wave, pole, osc, Complex.div_re, Complex.normSq_apply, mul_comm Complex.I,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring_nf

private noncomputable def boxCost (cs : List ℝ) (b : ℝ) : ℝ :=
  (cs.map (fun c => (1 / 100) * (b / (c - 1 / 200) + 1 / (c - 1 / 200) ^ 2))).sum

private def rationalPhaseCap (cs : List ℚ) (k a b d : ℚ) : ℚ :=
  k / 256 + cs.sum * (b - a) ^ 2 / 4 + 58 * (d / (2 - d)) +
    (cs.map (fun c => (1 / 100) * (b / (c - 1 / 200) + 1 / (c - 1 / 200) ^ 2))).sum

private theorem cast_phase_cap (cs : List ℚ) (k a b d : ℚ) :
    (rationalPhaseCap cs k a b d : ℝ) =
      (k : ℝ) / 256 + (cs.map ((↑) : ℚ → ℝ)).sum * ((b : ℝ) - a) ^ 2 / 4 +
        58 * ((d : ℝ) / (2 - d)) +
        boxCost (cs.map ((↑) : ℚ → ℝ)) b := by
  simp only [rationalPhaseCap, boxCost, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
    pow_two, Rat.cast_one, Rat.cast_ofNat, Rat.cast_list_sum, List.map_map, Function.comp_def]

private def inside (g c : ℝ) : Prop :=
  0 < c - 1 / 200 ∧ g ∈ Set.Icc (c - 1 / 200) (c - 1 / 200 + 1 / 100)

private theorem boxed_moments {gs cs : List ℝ} (h : List.Forall₂ inside gs cs) {t b : ℝ}
    (ht : |t| ≤ b) : -moments gs t 0 ≤ -moments cs t 0 + boxCost cs b := by
  induction h with
  | nil =>
    exact
      le_of_eq
        (by
          change -(0 : ℝ) = -0 + 0; ring)
  | @cons g c gs cs hgc _ ih =>
    have he := box_term_le hgc.1 hgc.2 ht
    rw [sub_add_cancel, signed_eq, signed_eq] at he
    change -(-osc g t / _ + moments gs t 0) ≤ -(-osc c t / _ + moments cs t 0) + (_ + boxCost cs b)
    simp only [neg_div, neg_add, neg_neg]
    linarith only [he, ih]

private theorem pole_eq (g : ℝ) : pole g = ((1 / 2 : ℝ) : ℂ) + (g : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp only [pole, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    ring

/-- Translate the enumerated signed phase to the cell sum with the same ordinate order. -/
private theorem head_eq_moments {n : ℕ} (g : Fin n → ℝ) (t : ℝ) :
    AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g t = -moments (List.ofFn g) t 0 := by
  simp only [AnalyticNumberTheory.RiemannZeta.zeroHeadPhase, Complex.re_sum, Finset.mul_sum,
    moments, List.map_ofFn, List.sum_ofFn, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [wave, pole_eq, mul_comm Complex.I, Function.comp_apply, neg_div, neg_neg] using
    signed_eq (g i) t

private noncomputable def heights : List ℝ :=
  pairs0.map (fun p => (p.1 : ℝ))

private theorem heights_pos : ∀ g ∈ heights, 0 < g := by
  intro g hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  have h : ∀ p ∈ pairs0, 0 < p.1 := by decide +kernel
  exact_mod_cast h p hp

private theorem bound0 : -moments heights ((2635447 / 100000 : ℚ) : ℝ) 0 ≤ 7 / 256 := by
  change -moments (pairs0.map (fun p => (p.1 : ℝ))) _ 0 ≤ _
  rw [center_sum_eq]
  exact realNode0

private theorem bound1 : -moments heights ((10556341 / 400000 : ℚ) : ℝ) 0 ≤ 49 / 256 := by
  change -moments (pairs1.map (fun p => (p.1 : ℝ))) _ 0 ≤ _
  rw [center_sum_eq]
  exact realNode1

private theorem bound2 : -moments heights ((5285447 / 200000 : ℚ) : ℝ) 0 ≤ 41 / 256 := by
  change -moments (pairs2.map (fun p => (p.1 : ℝ))) _ 0 ≤ _
  rw [center_sum_eq]
  exact realNode2

private theorem bound3 : -moments heights ((10585447 / 400000 : ℚ) : ℝ) 0 ≤ 24 / 256 := by
  change -moments (pairs3.map (fun p => (p.1 : ℝ))) _ 0 ≤ _
  rw [center_sum_eq]
  exact realNode3

private theorem bound4 : -moments heights ((53 / 2 : ℚ) : ℝ) 0 ≤ -57 / 256 := by
  change -moments (pairs4.map (fun p => (p.1 : ℝ))) _ 0 ≤ _
  rw [center_sum_eq]
  exact realNode4

private abbrev low (i : Fin 29) : ℚ :=
  AnalyticNumberTheory.RiemannZeta.lowZero100Lower i

private theorem boxes_of_bounds (g : Fin 29 → ℝ)
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    List.Forall₂ inside (List.ofFn g) heights := by
  have eqs : pairs0.map Prod.fst = List.ofFn (fun i => low i + 1 / 200) := by decide +kernel
  have pos : ∀ i, 0 < low i := by decide +kernel
  have he : heights = List.ofFn (fun i => ((low i + 1 / 200 : ℚ) : ℝ)) := by
    change (pairs0.map ((fun q : ℚ => (q : ℝ)) ∘ Prod.fst)) = _
    rw [← List.map_map (g := (fun q : ℚ => (q : ℝ))) (f := Prod.fst), eqs, List.map_ofFn]
    rfl
  rw [he, List.forall₂_iff_get]
  refine ⟨by simp only [List.length_ofFn], ?_⟩
  intro j h₁ h₂
  let i : Fin 29 := ⟨j, by simpa only [List.length_ofFn] using h₁⟩
  simp only [List.get_ofFn, Fin.cast_mk]
  change inside (g i) ((low i + 1 / 200 : ℚ) : ℝ)
  simp only [inside, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, add_sub_cancel_right]
  exact ⟨(Rat.cast_pos (K := ℝ)).2 (pos i), hl i, hu i⟩

private def left0 : ℚ :=
  2635447 / 100000

private def right0 : ℚ :=
  10556341 / 400000

private theorem cell0 (x : ℝ) (hx : x ∈ Set.Icc (left0 : ℝ) (right0 : ℝ)) :
    -moments heights x 0 ≤ 49 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 := by
  have hab : left0 < right0 := by decide +kernel
  exact
    centers_chord heights heights_pos (by exact_mod_cast hab) hx (bound0.trans (by norm_num only))
      (bound1.trans (by norm_num only))

private theorem shifted0 (x d : ℝ) (hd : 0 ≤ d) (hx : x ∈ Set.Icc ((left0 : ℝ) - d) (right0 : ℝ)) :
    -moments heights x 0 ≤ 49 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 + 58 * d := by
  have hlen : heights.length = 29 := rfl
  have hcost : 0 ≤ heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (List.sum_nonneg (fun g hg => (heights_pos g hg).le)) (sq_nonneg _))
      (by norm_num only)
  by_cases hl : (left0 : ℝ) ≤ x
  · linarith only [cell0 x ⟨hl, hx.2⟩, hd]
  have hs := left_shift heights (le_of_not_ge hl)
  rw [hlen, Nat.cast_ofNat] at hs
  have ha : -moments heights (left0 : ℝ) 0 ≤ 49 / 256 := bound0.trans (by norm_num only)
  have hlo : (left0 : ℝ) - d ≤ x := hx.1
  linarith only [hs, ha, hlo, hcost]

private def delta0 : ℚ :=
  2494731690341 / 200000000000000000

private theorem smoothed0 (L : ℝ) (hL : L ∈ Set.Icc (left0 : ℝ) (right0 : ℝ)) :
    let D : ℝ := delta0;
    -moments heights (L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2)) 0 ≤
      49 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 + 58 * (D / (2 - D)) := by
  have ha : (2 : ℚ) ≤ left0 := by decide +kernel
  have hd : 0 ≤ delta0 := by decide +kernel
  have hd1 : delta0 < 1 := by decide +kernel
  have cap := cap_of_ticks left0 delta0 (by decide +kernel) hd (by decide +kernel)
  have hx := smooth_mem (by exact_mod_cast ha) hL cap (by exact_mod_cast hd1)
  have h : (delta0 : ℝ) < 1 := by exact_mod_cast hd1
  exact shifted0 _ _ (div_nonneg (by exact_mod_cast hd) (by linarith only [h])) hx

private theorem boxed0 (gs : List ℝ) (hg : List.Forall₂ inside gs heights) (L : ℝ)
    (hL : L ∈ Set.Icc (left0 : ℝ) (right0 : ℝ)) :
    let D : ℝ := delta0;
    let t := L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2);
    -moments gs t 0 ≤
      49 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 + 58 * (D / (2 - D)) +
        boxCost heights right0 := by
  have ha : (2 : ℝ) ≤ left0 := by exact_mod_cast (by decide +kernel : (2 : ℚ) ≤ left0)
  have hd : (delta0 : ℝ) < 1 := by exact_mod_cast (by decide +kernel : delta0 < 1)
  have cap := cap_of_ticks left0 delta0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hx := smooth_mem ha hL cap hd
  have hfrac : (delta0 : ℝ) / (2 - delta0) ≤ 1 :=
    (div_le_one (by linarith only [hd])).mpr (by linarith only [hd])
  have ht := abs_le.mpr ⟨by linarith only [hx.1, hx.2, ha, hfrac], hx.2⟩
  exact (boxed_moments hg ht).trans (add_le_add (smoothed0 L hL) (le_refl _))

private theorem midpoint0 (g : Fin 29 → ℝ) (hg : List.Forall₂ inside (List.ofFn g) heights) (L : ℝ)
    (hL : L ∈ Set.Icc (left0 : ℝ) (right0 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta0;
    0 < t ∧
      AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g (Real.log t) ≤
        49 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right0 := by
  have ha : (2 : ℝ) ≤ left0 := by exact_mod_cast (by decide +kernel : (2 : ℚ) ≤ left0)
  have hd : (delta0 : ℝ) < 1 := by exact_mod_cast (by decide +kernel : delta0 < 1)
  have cap := cap_of_ticks left0 delta0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hu :=
    (div_le_div_of_nonneg_right (ratio_le_left ha hL.1) (by norm_num only : (0 : ℝ) ≤ 4)).trans cap
  obtain ⟨hp, he⟩ := midpoint_phase L _ (hu.trans_lt hd)
  refine ⟨hp, ?_⟩
  rw [head_eq_moments, he]
  exact boxed0 _ hg L hL

private theorem bracketMidpoint0 (g : Fin 29 → ℝ)
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (L : ℝ)
    (hL : L ∈ Set.Icc (left0 : ℝ) (right0 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta0;
    0 < t ∧
      AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g (Real.log t) ≤
        49 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right0 :=
  midpoint0 g (boxes_of_bounds g hl hu) L hL

private theorem ledger0 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left0 : ℝ) (right0 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta0;
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            ((t : ℂ) ^ ρ / ρ)).re ≤
      Real.sqrt t *
        (49 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right0) := by
  obtain ⟨g, hm, hp, hh, hz, hl, hu⟩ :=
    AnalyticNumberTheory.RiemannZeta.low_zero_100_of_signs
      AnalyticNumberTheory.RiemannZeta.low_zero_100_sign_changes
  obtain ⟨ht, hb⟩ := bracketMidpoint0 g hl hu L hL
  dsimp only
  rw [AnalyticNumberTheory.RiemannZeta.zero_head_phase_of_count hRH
      (by norm_num only : (0 : ℝ) ≤ 100) ht g hm.injective hp hh hz
      (by
        norm_num only [Nat.cast_ofNat]
        exact AnalyticNumberTheory.RiemannZeta.zero_count_100_le_58_of_RH hRH)]
  exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

private theorem defect0 (L : ℝ) (hL : (left0 : ℝ) ≤ L) :
    1 + 4 / 5 * Real.exp (-L / 4) + Real.exp (-L / 6) + 81 / 100 * Real.exp (-L / 3) +
        Real.exp (-3 * L / 10) +
        81 / 100 * Real.exp (-2 * L / 5) ≤
      (10139914141 / 10000000000) := by
  have b0 :=
    decay_tick (1647 / 250) (1721 / 1250000) (z := 1 * L / 4) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1647 / 250 : ℚ) ≤ 1 * left0 / 4 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b1 :=
    decay_tick (549 / 125) (309399 / 25000000) (z := 1 * L / 6) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (549 / 125 : ℚ) ≤ 1 * left0 / 6 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b2 :=
    decay_tick (1098 / 125) (15317 / 100000000) (z := 1 * L / 3) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1098 / 125 : ℚ) ≤ 1 * left0 / 3 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b3 :=
    decay_tick (3953 / 500) (36853 / 100000000) (z := 3 * L / 10) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (3953 / 500 : ℚ) ≤ 3 * left0 / 10 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b4 :=
    decay_tick (10541 / 1000) (661 / 25000000) (z := 2 * L / 5) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (10541 / 1000 : ℚ) ≤ 2 * left0 / 5 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  simp only [one_mul, neg_div, neg_mul] at b0 b1 b2 b3 b4 ⊢
  linarith only [b0, b1, b2, b3, b4]

private theorem coefficient0 (L : ℝ) (hl : (left0 : ℝ) ≤ L) :
    (4840971 / 200000) ≤ L * (L - Real.log L) / (8 * Real.pi) := by
  have h :=
    coefficient_tick left0 (1635819 / 500000) (4840971 / 200000) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hl
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The Lee-Nosal lower bound holds at every logarithmic coordinate of this cell. -/
private theorem lowerCell0 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left0 : ℝ) (right0 : ℝ)) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hp : rationalPhaseCap (pairs0.map Prod.fst) (49) left0 right0 delta0 ≤ 945416 / 1000000 := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).2 hp
  rw [cast_phase_cap] at hr
  simp only [List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_ofNat] at hr
  have hm := max_le (by norm_num only : (0 : ℝ) ≤ 945416 / 1000000) hr
  have ha : (22 : ℝ) ≤ left0 := by exact_mod_cast (by decide +kernel : (22 : ℚ) ≤ left0)
  have hb : (right0 : ℝ) ≤ 27 := by exact_mod_cast (by decide +kernel : right0 ≤ (27 : ℚ))
  have hg :=
    AnalyticNumberTheory.RiemannZeta.theta_phase_error hRH ha hb hL (ledger0 hRH L hL)
      (defect0 L hL.1)
  dsimp only [heights] at hg
  let c :=
    (right0 : ℝ) / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / ((left0 : ℝ) * (6283 / 8000)))
  have hc :
    (right0 : ℝ) / 8 + 7 / 50000 + 945416 / 1000000 + 3640 * (1 / 999) ^ 2 / 24 +
        ((c ^ 2 + 2 * c + 2) / (6283 / 1000) - 143 / 125) ≤
      (4840971 / 200000) - (10139914141 / 10000000000) := by
    norm_num only [c, right0, left0, Rat.cast_div, Rat.cast_ofNat]
  dsimp only [c] at hc
  linarith only [hg, hm, hc, coefficient0 L hL.1]

private def left1 : ℚ :=
  10556341 / 400000

private def right1 : ℚ :=
  5285447 / 200000

private theorem cell1 (x : ℝ) (hx : x ∈ Set.Icc (left1 : ℝ) (right1 : ℝ)) :
    -moments heights x 0 ≤ 49 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 := by
  have hab : left1 < right1 := by decide +kernel
  exact
    centers_chord heights heights_pos (by exact_mod_cast hab) hx (bound1.trans (by norm_num only))
      (bound2.trans (by norm_num only))

private theorem shifted1 (x d : ℝ) (hd : 0 ≤ d) (hx : x ∈ Set.Icc ((left1 : ℝ) - d) (right1 : ℝ)) :
    -moments heights x 0 ≤ 49 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 + 58 * d := by
  have hlen : heights.length = 29 := rfl
  have hcost : 0 ≤ heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (List.sum_nonneg (fun g hg => (heights_pos g hg).le)) (sq_nonneg _))
      (by norm_num only)
  by_cases hl : (left1 : ℝ) ≤ x
  · linarith only [cell1 x ⟨hl, hx.2⟩, hd]
  have hs := left_shift heights (le_of_not_ge hl)
  rw [hlen, Nat.cast_ofNat] at hs
  have ha : -moments heights (left1 : ℝ) 0 ≤ 49 / 256 := bound1.trans (by norm_num only)
  have hlo : (left1 : ℝ) - d ≤ x := hx.1
  linarith only [hs, ha, hlo, hcost]

private def delta1 : ℚ :=
  6132853996701 / 500000000000000000

private theorem smoothed1 (L : ℝ) (hL : L ∈ Set.Icc (left1 : ℝ) (right1 : ℝ)) :
    let D : ℝ := delta1;
    -moments heights (L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2)) 0 ≤
      49 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 + 58 * (D / (2 - D)) := by
  have ha : (2 : ℚ) ≤ left1 := by decide +kernel
  have hd : 0 ≤ delta1 := by decide +kernel
  have hd1 : delta1 < 1 := by decide +kernel
  have cap := cap_of_ticks left1 delta1 (by decide +kernel) hd (by decide +kernel)
  have hx := smooth_mem (by exact_mod_cast ha) hL cap (by exact_mod_cast hd1)
  have h : (delta1 : ℝ) < 1 := by exact_mod_cast hd1
  exact shifted1 _ _ (div_nonneg (by exact_mod_cast hd) (by linarith only [h])) hx

private theorem boxed1 (gs : List ℝ) (hg : List.Forall₂ inside gs heights) (L : ℝ)
    (hL : L ∈ Set.Icc (left1 : ℝ) (right1 : ℝ)) :
    let D : ℝ := delta1;
    let t := L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2);
    -moments gs t 0 ≤
      49 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 + 58 * (D / (2 - D)) +
        boxCost heights right1 := by
  have ha : (2 : ℝ) ≤ left1 := by exact_mod_cast (by decide +kernel : (2 : ℚ) ≤ left1)
  have hd : (delta1 : ℝ) < 1 := by exact_mod_cast (by decide +kernel : delta1 < 1)
  have cap := cap_of_ticks left1 delta1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hx := smooth_mem ha hL cap hd
  have hfrac : (delta1 : ℝ) / (2 - delta1) ≤ 1 :=
    (div_le_one (by linarith only [hd])).mpr (by linarith only [hd])
  have ht := abs_le.mpr ⟨by linarith only [hx.1, hx.2, ha, hfrac], hx.2⟩
  exact (boxed_moments hg ht).trans (add_le_add (smoothed1 L hL) (le_refl _))

private theorem midpoint1 (g : Fin 29 → ℝ) (hg : List.Forall₂ inside (List.ofFn g) heights) (L : ℝ)
    (hL : L ∈ Set.Icc (left1 : ℝ) (right1 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta1;
    0 < t ∧
      AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g (Real.log t) ≤
        49 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right1 := by
  have ha : (2 : ℝ) ≤ left1 := by exact_mod_cast (by decide +kernel : (2 : ℚ) ≤ left1)
  have hd : (delta1 : ℝ) < 1 := by exact_mod_cast (by decide +kernel : delta1 < 1)
  have cap := cap_of_ticks left1 delta1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hu :=
    (div_le_div_of_nonneg_right (ratio_le_left ha hL.1) (by norm_num only : (0 : ℝ) ≤ 4)).trans cap
  obtain ⟨hp, he⟩ := midpoint_phase L _ (hu.trans_lt hd)
  refine ⟨hp, ?_⟩
  rw [head_eq_moments, he]
  exact boxed1 _ hg L hL

private theorem bracketMidpoint1 (g : Fin 29 → ℝ)
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (L : ℝ)
    (hL : L ∈ Set.Icc (left1 : ℝ) (right1 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta1;
    0 < t ∧
      AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g (Real.log t) ≤
        49 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right1 :=
  midpoint1 g (boxes_of_bounds g hl hu) L hL

private theorem ledger1 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left1 : ℝ) (right1 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta1;
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            ((t : ℂ) ^ ρ / ρ)).re ≤
      Real.sqrt t *
        (49 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right1) := by
  obtain ⟨g, hm, hp, hh, hz, hl, hu⟩ :=
    AnalyticNumberTheory.RiemannZeta.low_zero_100_of_signs
      AnalyticNumberTheory.RiemannZeta.low_zero_100_sign_changes
  obtain ⟨ht, hb⟩ := bracketMidpoint1 g hl hu L hL
  dsimp only
  rw [AnalyticNumberTheory.RiemannZeta.zero_head_phase_of_count hRH
      (by norm_num only : (0 : ℝ) ≤ 100) ht g hm.injective hp hh hz
      (by
        norm_num only [Nat.cast_ofNat]
        exact AnalyticNumberTheory.RiemannZeta.zero_count_100_le_58_of_RH hRH)]
  exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

private theorem defect1 (L : ℝ) (hL : (left1 : ℝ) ≤ L) :
    1 + 4 / 5 * Real.exp (-L / 4) + Real.exp (-L / 6) + 81 / 100 * Real.exp (-L / 3) +
        Real.exp (-3 * L / 10) +
        81 / 100 * Real.exp (-2 * L / 5) ≤
      (5069508329 / 5000000000) := by
  have b0 :=
    decay_tick (6597 / 1000) (68223 / 50000000) (z := 1 * L / 4) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (6597 / 1000 : ℚ) ≤ 1 * left1 / 4 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b1 :=
    decay_tick (2199 / 500) (76887 / 6250000) (z := 1 * L / 6) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (2199 / 500 : ℚ) ≤ 1 * left1 / 6 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b2 :=
    decay_tick (2199 / 250) (7567 / 50000000) (z := 1 * L / 3) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (2199 / 250 : ℚ) ≤ 1 * left1 / 3 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b3 :=
    decay_tick (7917 / 1000) (729 / 2000000) (z := 3 * L / 10) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (7917 / 1000 : ℚ) ≤ 3 * left1 / 10 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b4 :=
    decay_tick (2639 / 250) (651 / 25000000) (z := 2 * L / 5) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (2639 / 250 : ℚ) ≤ 2 * left1 / 5 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  simp only [one_mul, neg_div, neg_mul] at b0 b1 b2 b3 b4 ⊢
  linarith only [b0, b1, b2, b3, b4]

private theorem coefficient1 (L : ℝ) (hl : (left1 : ℝ) ≤ L) :
    (971001 / 40000) ≤ L * (L - Real.log L) / (8 * Real.pi) := by
  have h :=
    coefficient_tick left1 (1636509 / 500000) (971001 / 40000) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hl
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The Lee-Nosal lower bound holds at every logarithmic coordinate of this cell. -/
private theorem lowerCell1 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left1 : ℝ) (right1 : ℝ)) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hp : rationalPhaseCap (pairs0.map Prod.fst) (49) left1 right1 delta1 ≤ 945625 / 1000000 := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).2 hp
  rw [cast_phase_cap] at hr
  simp only [List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_ofNat] at hr
  have hm := max_le (by norm_num only : (0 : ℝ) ≤ 945625 / 1000000) hr
  have ha : (22 : ℝ) ≤ left1 := by exact_mod_cast (by decide +kernel : (22 : ℚ) ≤ left1)
  have hb : (right1 : ℝ) ≤ 27 := by exact_mod_cast (by decide +kernel : right1 ≤ (27 : ℚ))
  have hg :=
    AnalyticNumberTheory.RiemannZeta.theta_phase_error hRH ha hb hL (ledger1 hRH L hL)
      (defect1 L hL.1)
  dsimp only [heights] at hg
  let c :=
    (right1 : ℝ) / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / ((left1 : ℝ) * (6283 / 8000)))
  have hc :
    (right1 : ℝ) / 8 + 7 / 50000 + 945625 / 1000000 + 3640 * (1 / 999) ^ 2 / 24 +
        ((c ^ 2 + 2 * c + 2) / (6283 / 1000) - 143 / 125) ≤
      (971001 / 40000) - (5069508329 / 5000000000) := by
    norm_num only [c, right1, left1, Rat.cast_div, Rat.cast_ofNat]
  dsimp only [c] at hc
  linarith only [hg, hm, hc, coefficient1 L hL.1]

private def left2 : ℚ :=
  5285447 / 200000

private def right2 : ℚ :=
  10585447 / 400000

private theorem cell2 (x : ℝ) (hx : x ∈ Set.Icc (left2 : ℝ) (right2 : ℝ)) :
    -moments heights x 0 ≤ 41 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 := by
  have hab : left2 < right2 := by decide +kernel
  exact
    centers_chord heights heights_pos (by exact_mod_cast hab) hx (bound2.trans (by norm_num only))
      (bound3.trans (by norm_num only))

private theorem shifted2 (x d : ℝ) (hd : 0 ≤ d) (hx : x ∈ Set.Icc ((left2 : ℝ) - d) (right2 : ℝ)) :
    -moments heights x 0 ≤ 41 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 + 58 * d := by
  have hlen : heights.length = 29 := rfl
  have hcost : 0 ≤ heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (List.sum_nonneg (fun g hg => (heights_pos g hg).le)) (sq_nonneg _))
      (by norm_num only)
  by_cases hl : (left2 : ℝ) ≤ x
  · linarith only [cell2 x ⟨hl, hx.2⟩, hd]
  have hs := left_shift heights (le_of_not_ge hl)
  rw [hlen, Nat.cast_ofNat] at hs
  have ha : -moments heights (left2 : ℝ) 0 ≤ 41 / 256 := bound2.trans (by norm_num only)
  have hlo : (left2 : ℝ) - d ≤ x := hx.1
  linarith only [hs, ha, hlo, hcost]

private def delta2 : ℚ :=
  6030600694633 / 500000000000000000

private theorem smoothed2 (L : ℝ) (hL : L ∈ Set.Icc (left2 : ℝ) (right2 : ℝ)) :
    let D : ℝ := delta2;
    -moments heights (L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2)) 0 ≤
      41 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 + 58 * (D / (2 - D)) := by
  have ha : (2 : ℚ) ≤ left2 := by decide +kernel
  have hd : 0 ≤ delta2 := by decide +kernel
  have hd1 : delta2 < 1 := by decide +kernel
  have cap := cap_of_ticks left2 delta2 (by decide +kernel) hd (by decide +kernel)
  have hx := smooth_mem (by exact_mod_cast ha) hL cap (by exact_mod_cast hd1)
  have h : (delta2 : ℝ) < 1 := by exact_mod_cast hd1
  exact shifted2 _ _ (div_nonneg (by exact_mod_cast hd) (by linarith only [h])) hx

private theorem boxed2 (gs : List ℝ) (hg : List.Forall₂ inside gs heights) (L : ℝ)
    (hL : L ∈ Set.Icc (left2 : ℝ) (right2 : ℝ)) :
    let D : ℝ := delta2;
    let t := L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2);
    -moments gs t 0 ≤
      41 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 + 58 * (D / (2 - D)) +
        boxCost heights right2 := by
  have ha : (2 : ℝ) ≤ left2 := by exact_mod_cast (by decide +kernel : (2 : ℚ) ≤ left2)
  have hd : (delta2 : ℝ) < 1 := by exact_mod_cast (by decide +kernel : delta2 < 1)
  have cap := cap_of_ticks left2 delta2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hx := smooth_mem ha hL cap hd
  have hfrac : (delta2 : ℝ) / (2 - delta2) ≤ 1 :=
    (div_le_one (by linarith only [hd])).mpr (by linarith only [hd])
  have ht := abs_le.mpr ⟨by linarith only [hx.1, hx.2, ha, hfrac], hx.2⟩
  exact (boxed_moments hg ht).trans (add_le_add (smoothed2 L hL) (le_refl _))

private theorem midpoint2 (g : Fin 29 → ℝ) (hg : List.Forall₂ inside (List.ofFn g) heights) (L : ℝ)
    (hL : L ∈ Set.Icc (left2 : ℝ) (right2 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta2;
    0 < t ∧
      AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g (Real.log t) ≤
        41 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right2 := by
  have ha : (2 : ℝ) ≤ left2 := by exact_mod_cast (by decide +kernel : (2 : ℚ) ≤ left2)
  have hd : (delta2 : ℝ) < 1 := by exact_mod_cast (by decide +kernel : delta2 < 1)
  have cap := cap_of_ticks left2 delta2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hu :=
    (div_le_div_of_nonneg_right (ratio_le_left ha hL.1) (by norm_num only : (0 : ℝ) ≤ 4)).trans cap
  obtain ⟨hp, he⟩ := midpoint_phase L _ (hu.trans_lt hd)
  refine ⟨hp, ?_⟩
  rw [head_eq_moments, he]
  exact boxed2 _ hg L hL

private theorem bracketMidpoint2 (g : Fin 29 → ℝ)
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (L : ℝ)
    (hL : L ∈ Set.Icc (left2 : ℝ) (right2 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta2;
    0 < t ∧
      AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g (Real.log t) ≤
        41 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right2 :=
  midpoint2 g (boxes_of_bounds g hl hu) L hL

private theorem ledger2 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left2 : ℝ) (right2 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta2;
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            ((t : ℂ) ^ ρ / ρ)).re ≤
      Real.sqrt t *
        (41 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right2) := by
  obtain ⟨g, hm, hp, hh, hz, hl, hu⟩ :=
    AnalyticNumberTheory.RiemannZeta.low_zero_100_of_signs
      AnalyticNumberTheory.RiemannZeta.low_zero_100_sign_changes
  obtain ⟨ht, hb⟩ := bracketMidpoint2 g hl hu L hL
  dsimp only
  rw [AnalyticNumberTheory.RiemannZeta.zero_head_phase_of_count hRH
      (by norm_num only : (0 : ℝ) ≤ 100) ht g hm.injective hp hh hz
      (by
        norm_num only [Nat.cast_ofNat]
        exact AnalyticNumberTheory.RiemannZeta.zero_count_100_le_58_of_RH hRH)]
  exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

private theorem defect2 (L : ℝ) (hL : (left2 : ℝ) ≤ L) :
    1 + 4 / 5 * Real.exp (-L / 4) + Real.exp (-L / 6) + 81 / 100 * Real.exp (-L / 3) +
        Real.exp (-3 * L / 10) +
        81 / 100 * Real.exp (-2 * L / 5) ≤
      (10138124387 / 10000000000) := by
  have b0 :=
    decay_tick (3303 / 500) (16903 / 12500000) (z := 1 * L / 4) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (3303 / 500 : ℚ) ≤ 1 * left2 / 4 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b1 :=
    decay_tick (1101 / 250) (1222833 / 100000000) (z := 1 * L / 6) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1101 / 250 : ℚ) ≤ 1 * left2 / 6 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b2 :=
    decay_tick (8809 / 1000) (14939 / 100000000) (z := 1 * L / 3) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (8809 / 1000 : ℚ) ≤ 1 * left2 / 3 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b3 :=
    decay_tick (991 / 125) (36051 / 100000000) (z := 3 * L / 10) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (991 / 125 : ℚ) ≤ 3 * left2 / 10 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b4 :=
    decay_tick (1057 / 100) (321 / 12500000) (z := 2 * L / 5) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1057 / 100 : ℚ) ≤ 2 * left2 / 5 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  simp only [one_mul, neg_div, neg_mul] at b0 b1 b2 b3 b4 ⊢
  linarith only [b0, b1, b2, b3, b4]

private theorem coefficient2 (L : ℝ) (hl : (left2 : ℝ) ≤ L) :
    (12172649 / 500000) ≤ L * (L - Real.log L) / (8 * Real.pi) := by
  have h :=
    coefficient_tick left2 (818599 / 250000) (12172649 / 500000) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hl
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The Lee-Nosal lower bound holds at every logarithmic coordinate of this cell. -/
private theorem lowerCell2 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left2 : ℝ) (right2 : ℝ)) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hp : rationalPhaseCap (pairs0.map Prod.fst) (41) left2 right2 delta2 ≤ 914585 / 1000000 := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).2 hp
  rw [cast_phase_cap] at hr
  simp only [List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_ofNat] at hr
  have hm := max_le (by norm_num only : (0 : ℝ) ≤ 914585 / 1000000) hr
  have ha : (22 : ℝ) ≤ left2 := by exact_mod_cast (by decide +kernel : (22 : ℚ) ≤ left2)
  have hb : (right2 : ℝ) ≤ 27 := by exact_mod_cast (by decide +kernel : right2 ≤ (27 : ℚ))
  have hg :=
    AnalyticNumberTheory.RiemannZeta.theta_phase_error hRH ha hb hL (ledger2 hRH L hL)
      (defect2 L hL.1)
  dsimp only [heights] at hg
  let c :=
    (right2 : ℝ) / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / ((left2 : ℝ) * (6283 / 8000)))
  have hc :
    (right2 : ℝ) / 8 + 7 / 50000 + 914585 / 1000000 + 3640 * (1 / 999) ^ 2 / 24 +
        ((c ^ 2 + 2 * c + 2) / (6283 / 1000) - 143 / 125) ≤
      (12172649 / 500000) - (10138124387 / 10000000000) := by
    norm_num only [c, right2, left2, Rat.cast_div, Rat.cast_ofNat]
  dsimp only [c] at hc
  linarith only [hg, hm, hc, coefficient2 L hL.1]

private def left3 : ℚ :=
  10585447 / 400000

private def right3 : ℚ :=
  53 / 2

private theorem cell3 (x : ℝ) (hx : x ∈ Set.Icc (left3 : ℝ) (right3 : ℝ)) :
    -moments heights x 0 ≤ 24 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 := by
  have hab : left3 < right3 := by decide +kernel
  exact
    centers_chord heights heights_pos (by exact_mod_cast hab) hx (bound3.trans (by norm_num only))
      (bound4.trans (by norm_num only))

private theorem shifted3 (x d : ℝ) (hd : 0 ≤ d) (hx : x ∈ Set.Icc ((left3 : ℝ) - d) (right3 : ℝ)) :
    -moments heights x 0 ≤ 24 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 + 58 * d := by
  have hlen : heights.length = 29 := rfl
  have hcost : 0 ≤ heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (List.sum_nonneg (fun g hg => (heights_pos g hg).le)) (sq_nonneg _))
      (by norm_num only)
  by_cases hl : (left3 : ℝ) ≤ x
  · linarith only [cell3 x ⟨hl, hx.2⟩, hd]
  have hs := left_shift heights (le_of_not_ge hl)
  rw [hlen, Nat.cast_ofNat] at hs
  have ha : -moments heights (left3 : ℝ) 0 ≤ 24 / 256 := bound3.trans (by norm_num only)
  have hlo : (left3 : ℝ) - d ≤ x := hx.1
  linarith only [hs, ha, hlo, hcost]

private def delta3 : ℚ :=
  5930041026339 / 500000000000000000

private theorem smoothed3 (L : ℝ) (hL : L ∈ Set.Icc (left3 : ℝ) (right3 : ℝ)) :
    let D : ℝ := delta3;
    -moments heights (L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2)) 0 ≤
      24 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 + 58 * (D / (2 - D)) := by
  have ha : (2 : ℚ) ≤ left3 := by decide +kernel
  have hd : 0 ≤ delta3 := by decide +kernel
  have hd1 : delta3 < 1 := by decide +kernel
  have cap := cap_of_ticks left3 delta3 (by decide +kernel) hd (by decide +kernel)
  have hx := smooth_mem (by exact_mod_cast ha) hL cap (by exact_mod_cast hd1)
  have h : (delta3 : ℝ) < 1 := by exact_mod_cast hd1
  exact shifted3 _ _ (div_nonneg (by exact_mod_cast hd) (by linarith only [h])) hx

private theorem boxed3 (gs : List ℝ) (hg : List.Forall₂ inside gs heights) (L : ℝ)
    (hL : L ∈ Set.Icc (left3 : ℝ) (right3 : ℝ)) :
    let D : ℝ := delta3;
    let t := L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2);
    -moments gs t 0 ≤
      24 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 + 58 * (D / (2 - D)) +
        boxCost heights right3 := by
  have ha : (2 : ℝ) ≤ left3 := by exact_mod_cast (by decide +kernel : (2 : ℚ) ≤ left3)
  have hd : (delta3 : ℝ) < 1 := by exact_mod_cast (by decide +kernel : delta3 < 1)
  have cap := cap_of_ticks left3 delta3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hx := smooth_mem ha hL cap hd
  have hfrac : (delta3 : ℝ) / (2 - delta3) ≤ 1 :=
    (div_le_one (by linarith only [hd])).mpr (by linarith only [hd])
  have ht := abs_le.mpr ⟨by linarith only [hx.1, hx.2, ha, hfrac], hx.2⟩
  exact (boxed_moments hg ht).trans (add_le_add (smoothed3 L hL) (le_refl _))

private theorem midpoint3 (g : Fin 29 → ℝ) (hg : List.Forall₂ inside (List.ofFn g) heights) (L : ℝ)
    (hL : L ∈ Set.Icc (left3 : ℝ) (right3 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta3;
    0 < t ∧
      AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g (Real.log t) ≤
        24 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right3 := by
  have ha : (2 : ℝ) ≤ left3 := by exact_mod_cast (by decide +kernel : (2 : ℚ) ≤ left3)
  have hd : (delta3 : ℝ) < 1 := by exact_mod_cast (by decide +kernel : delta3 < 1)
  have cap := cap_of_ticks left3 delta3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hu :=
    (div_le_div_of_nonneg_right (ratio_le_left ha hL.1) (by norm_num only : (0 : ℝ) ≤ 4)).trans cap
  obtain ⟨hp, he⟩ := midpoint_phase L _ (hu.trans_lt hd)
  refine ⟨hp, ?_⟩
  rw [head_eq_moments, he]
  exact boxed3 _ hg L hL

private theorem bracketMidpoint3 (g : Fin 29 → ℝ)
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (L : ℝ)
    (hL : L ∈ Set.Icc (left3 : ℝ) (right3 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta3;
    0 < t ∧
      AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g (Real.log t) ≤
        24 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right3 :=
  midpoint3 g (boxes_of_bounds g hl hu) L hL

private theorem ledger3 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left3 : ℝ) (right3 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta3;
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            ((t : ℂ) ^ ρ / ρ)).re ≤
      Real.sqrt t *
        (24 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right3) := by
  obtain ⟨g, hm, hp, hh, hz, hl, hu⟩ :=
    AnalyticNumberTheory.RiemannZeta.low_zero_100_of_signs
      AnalyticNumberTheory.RiemannZeta.low_zero_100_sign_changes
  obtain ⟨ht, hb⟩ := bracketMidpoint3 g hl hu L hL
  dsimp only
  rw [AnalyticNumberTheory.RiemannZeta.zero_head_phase_of_count hRH
      (by norm_num only : (0 : ℝ) ≤ 100) ht g hm.injective hp hh hz
      (by
        norm_num only [Nat.cast_ofNat]
        exact AnalyticNumberTheory.RiemannZeta.zero_count_100_le_58_of_RH hRH)]
  exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

private theorem defect3 (L : ℝ) (hL : (left3 : ℝ) ≤ L) :
    1 + 4 / 5 * Real.exp (-L / 4) + Real.exp (-L / 6) + 81 / 100 * Real.exp (-L / 3) +
        Real.exp (-3 * L / 10) +
        81 / 100 * Real.exp (-2 * L / 5) ≤
      (10137239031 / 10000000000) := by
  have b0 :=
    decay_tick (1323 / 200) (33503 / 25000000) (z := 1 * L / 4) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1323 / 200 : ℚ) ≤ 1 * left3 / 4 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b1 :=
    decay_tick (441 / 100) (607759 / 50000000) (z := 1 * L / 6) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (441 / 100 : ℚ) ≤ 1 * left3 / 6 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b2 :=
    decay_tick (8821 / 1000) (14761 / 100000000) (z := 1 * L / 3) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (8821 / 1000 : ℚ) ≤ 1 * left3 / 3 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b3 :=
    decay_tick (7939 / 1000) (35657 / 100000000) (z := 3 * L / 10) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (7939 / 1000 : ℚ) ≤ 3 * left3 / 10 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b4 :=
    decay_tick (2117 / 200) (253 / 10000000) (z := 2 * L / 5) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (2117 / 200 : ℚ) ≤ 2 * left3 / 5 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  simp only [one_mul, neg_div, neg_mul] at b0 b1 b2 b3 b4 ⊢
  linarith only [b0, b1, b2, b3, b4]

private theorem coefficient3 (L : ℝ) (hl : (left3 : ℝ) ≤ L) :
    (976627 / 40000) ≤ L * (L - Real.log L) / (8 * Real.pi) := by
  have h :=
    coefficient_tick left3 (3275771 / 1000000) (976627 / 40000) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hl
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The Lee-Nosal lower bound holds at every logarithmic coordinate of this cell. -/
private theorem lowerCell3 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left3 : ℝ) (right3 : ℝ)) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hp : rationalPhaseCap (pairs0.map Prod.fst) (24) left3 right3 delta3 ≤ 848388 / 1000000 := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).2 hp
  rw [cast_phase_cap] at hr
  simp only [List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_ofNat] at hr
  have hm := max_le (by norm_num only : (0 : ℝ) ≤ 848388 / 1000000) hr
  have ha : (22 : ℝ) ≤ left3 := by exact_mod_cast (by decide +kernel : (22 : ℚ) ≤ left3)
  have hb : (right3 : ℝ) ≤ 27 := by exact_mod_cast (by decide +kernel : right3 ≤ (27 : ℚ))
  have hg :=
    AnalyticNumberTheory.RiemannZeta.theta_phase_error hRH ha hb hL (ledger3 hRH L hL)
      (defect3 L hL.1)
  dsimp only [heights] at hg
  let c :=
    (right3 : ℝ) / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / ((left3 : ℝ) * (6283 / 8000)))
  have hc :
    (right3 : ℝ) / 8 + 7 / 50000 + 848388 / 1000000 + 3640 * (1 / 999) ^ 2 / 24 +
        ((c ^ 2 + 2 * c + 2) / (6283 / 1000) - 143 / 125) ≤
      (976627 / 40000) - (10137239031 / 10000000000) := by
    norm_num only [c, right3, left3, Rat.cast_div, Rat.cast_ofNat]
  dsimp only [c] at hc
  linarith only [hg, hm, hc, coefficient3 L hL.1]

/-- Join the adjacent lower bounds on their closed logarithmic interval. -/
private theorem lowerBand (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left0 : ℝ) (right3 : ℝ)) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  by_cases h1 : L ≤ (right1 : ℝ)
  · by_cases h0 : L ≤ (right0 : ℝ)
    · exact lowerCell0 hRH L ⟨hL.1, h0⟩
    · exact lowerCell1 hRH L ⟨(lt_of_not_ge h0).le, h1⟩
  · by_cases h2 : L ≤ (right2 : ℝ)
    · exact lowerCell2 hRH L ⟨(lt_of_not_ge h1).le, h2⟩
    · exact lowerCell3 hRH L ⟨(lt_of_not_ge h2).le, hL.2⟩

/-- The lower phase bound on the full integer-endpoint band. -/
public theorem theta_lower_from_279_billion (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 279000000000 ≤ x) :
    (x - Chebyshev.theta x) / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  have hp : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  rcases le_total (53 / 2 : ℝ) (Real.log x) with h | h
  · exact AnalyticNumberTheory.Arithmetic.theta_lower_log_half53 hRH hp h
  have hc :=
    PseudoPrime.Analysis.rationalLogIntervalCheck_sound
      (show
        PseudoPrime.Analysis.rationalLogIntervalCheck 279000000000 38 12 (2635447 / 100000)
            (2635449 / 100000) =
          true
        from by decide +kernel)
  have hl := hc.1.trans (Real.log_le_log (by norm_num only) hx)
  have hr : Real.log x ≤ ((53 / 2 : ℚ) : ℝ) := by simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  have hg := lowerBand hRH (Real.log x) ⟨hl, hr⟩
  simpa only [Real.exp_log hp] using hg

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
