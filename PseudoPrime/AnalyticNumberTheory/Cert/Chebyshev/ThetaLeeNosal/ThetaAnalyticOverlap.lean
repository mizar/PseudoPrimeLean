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
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Data.List.Forall2
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Lower Lee–Nosal bound on the finite-to-analytic overlap -/

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
  [((361953 / 25600), (5405644121 / 16777216)), ((269139 / 12800), (4019498811 / 8388608)),
    ((640403 / 25600), (9564199529 / 16777216)), ((779003 / 25600), (363566971 / 524288)),
    ((843253 / 25600), (12593694823 / 16777216)), ((120291 / 3200), (1796504897 / 2097152)),
    ((261907 / 6400), (15645965469 / 16777216)), ((554639 / 12800), (8283343555 / 8388608)),
    ((1229053 / 25600), (4588871431 / 4194304)), ((159291 / 3200), (19031652347 / 16777216)),
    ((1356153 / 25600), (20253680705 / 16777216)), ((180641 / 3200), (2697811483 / 2097152)),
    ((1519403 / 25600), (11345881779 / 8388608)), ((1557403 / 25600), (11629640273 / 8388608)),
    ((1667003 / 25600), (24896119019 / 16777216)), ((1717353 / 25600), (25648079029 / 16777216)),
    ((1780503 / 25600), (830975083 / 524288)), ((461257 / 6400), (13777430719 / 8388608)),
    ((1938153 / 25600), (14472825713 / 8388608)), ((493757 / 6400), (29496366925 / 16777216)),
    ((2031153 / 25600), (30334574583 / 16777216)), ((530657 / 6400), (31700722387 / 16777216)),
    ((2169353 / 25600), (32398544263 / 16777216)), ((2238203 / 25600), (33426795439 / 16777216)),
    ((568407 / 6400), (8488963921 / 4194304)), ((2367903 / 25600), (35363820529 / 16777216)),
    ((1211589 / 12800), (1130916679 / 524288)), ((2454403 / 25600), (36655668411 / 16777216)),
    ((2530203 / 25600), (37787715457 / 16777216))]

private noncomputable def centerSum0 : ℝ :=
  (pairs0.map (fun p => realTerm p.1 (22788479 / 1000000))).sum

/-- Scalar upper bound for the actual center sum at this pilot node. -/
private theorem realNode0 : centerSum0 ≤ 104 / 256 := by
  have h := sum_le_upper (22788479 / 1000000) pairs0 (by decide +kernel)
  have hq : (pairs0.map (fun p => upperTerm p.1 (22788479 / 1000000) p.2)).sum ≤ 104 / 256 := by
    decide +kernel
  exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hq)

private def pairs1 : List (ℚ × ℚ) :=
  [((361953 / 25600), (2702874797 / 8388608)), ((269139 / 12800), (2009788619 / 4194304)),
    ((640403 / 25600), (9564386143 / 16777216)), ((779003 / 25600), (5817185037 / 8388608)),
    ((843253 / 25600), (12593940547 / 16777216)), ((120291 / 3200), (14372319599 / 16777216)),
    ((261907 / 6400), (3911567687 / 4194304)), ((554639 / 12800), (8283505177 / 8388608)),
    ((1229053 / 25600), (9177921935 / 8388608)), ((159291 / 3200), (9516011843 / 8388608)),
    ((1356153 / 25600), (20254075887 / 16777216)), ((180641 / 3200), (10791456487 / 8388608)),
    ((1519403 / 25600), (22692206311 / 16777216)), ((1557403 / 25600), (23259734373 / 16777216)),
    ((1667003 / 25600), (24896604783 / 16777216)), ((1717353 / 25600), (25648579465 / 16777216)),
    ((1780503 / 25600), (13295860747 / 8388608)), ((461257 / 6400), (13777699539 / 8388608)),
    ((1938153 / 25600), (7236554051 / 4194304)), ((493757 / 6400), (1843558903 / 1048576)),
    ((2031153 / 25600), (7583791615 / 4194304)), ((530657 / 6400), (3962667615 / 2097152)),
    ((2169353 / 25600), (8099794103 / 4194304)), ((2238203 / 25600), (16713723825 / 8388608)),
    ((568407 / 6400), (16978259109 / 8388608)), ((2367903 / 25600), (35364510535 / 16777216)),
    ((1211589 / 12800), (36190039841 / 16777216)), ((2454403 / 25600), (36656383623 / 16777216)),
    ((2530203 / 25600), (37788452757 / 16777216))]

private noncomputable def centerSum1 : ℝ :=
  (pairs1.map (fun p => realTerm p.1 (1458491113 / 64000000))).sum

/-- Scalar upper bound for the actual center sum at this pilot node. -/
private theorem realNode1 : centerSum1 ≤ 103 / 256 := by
  have h := sum_le_upper (1458491113 / 64000000) pairs1 (by decide +kernel)
  have hq : (pairs1.map (fun p => upperTerm p.1 (1458491113 / 64000000) p.2)).sum ≤ 103 / 256 := by
    decide +kernel
  exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hq)

private def pairs2 : List (ℚ × ℚ) :=
  [((361953 / 25600), (5405855067 / 16777216)), ((269139 / 12800), (4019655665 / 8388608)),
    ((640403 / 25600), (2391143189 / 4194304)), ((779003 / 25600), (11634597075 / 16777216)),
    ((843253 / 25600), (6297093135 / 8388608)), ((120291 / 3200), (14372600021 / 16777216)),
    ((261907 / 6400), (7823288013 / 8388608)), ((554639 / 12800), (16567333597 / 16777216)),
    ((1229053 / 25600), (18356202015 / 16777216)), ((159291 / 3200), (1189524689 / 1048576)),
    ((1356153 / 25600), (10127235535 / 8388608)), ((180641 / 3200), (5395833521 / 4194304)),
    ((1519403 / 25600), (22692649065 / 16777216)), ((1557403 / 25600), (2907523525 / 2097152)),
    ((1667003 / 25600), (24897090547 / 16777216)), ((1717353 / 25600), (25649079901 / 16777216)),
    ((1780503 / 25600), (6648060083 / 4194304)), ((461257 / 6400), (27555936719 / 16777216)),
    ((1938153 / 25600), (28946780981 / 16777216)), ((493757 / 6400), (14748758985 / 8388608)),
    ((2031153 / 25600), (15167879169 / 8388608)), ((530657 / 6400), (31701959453 / 16777216)),
    ((2169353 / 25600), (32399808561 / 16777216)), ((2238203 / 25600), (16714049931 / 8388608)),
    ((568407 / 6400), (33957180753 / 16777216)), ((2367903 / 25600), (35365200541 / 16777216)),
    ((1211589 / 12800), (18095372977 / 8388608)), ((2454403 / 25600), (9164274709 / 4194304)),
    ((2530203 / 25600), (18894595029 / 8388608))]

private noncomputable def centerSum2 : ℝ :=
  (pairs2.map (fun p => realTerm p.1 (145851957 / 6400000))).sum

/-- Scalar upper bound for the actual center sum at this pilot node. -/
private theorem realNode2 : centerSum2 ≤ 102 / 256 := by
  have h := sum_le_upper (145851957 / 6400000) pairs2 (by decide +kernel)
  have hq : (pairs2.map (fun p => upperTerm p.1 (145851957 / 6400000) p.2)).sum ≤ 102 / 256 := by
    decide +kernel
  exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hq)

private def pairs3 : List (ℚ × ℚ) :=
  [((361953 / 25600), (5406066013 / 16777216)), ((269139 / 12800), (4019812519 / 8388608)),
    ((640403 / 25600), (4782472991 / 8388608)), ((779003 / 25600), (11635051077 / 16777216)),
    ((843253 / 25600), (6297338859 / 8388608)), ((120291 / 3200), (14373160865 / 16777216)),
    ((261907 / 6400), (15647186583 / 16777216)), ((554639 / 12800), (16567980083 / 16777216)),
    ((1229053 / 25600), (18356918307 / 16777216)), ((159291 / 3200), (9516568851 / 8388608)),
    ((1356153 / 25600), (20255261435 / 16777216)), ((180641 / 3200), (1349011019 / 1048576)),
    ((1519403 / 25600), (5673383643 / 4194304)), ((1557403 / 25600), (23261095853 / 16777216)),
    ((1667003 / 25600), (24898062075 / 16777216)), ((1717353 / 25600), (25650080773 / 16777216)),
    ((1780503 / 25600), (3324159751 / 2097152)), ((461257 / 6400), (861156625 / 524288)),
    ((1938153 / 25600), (28947910535 / 16777216)), ((493757 / 6400), (29498669015 / 16777216)),
    ((2031153 / 25600), (7584235523 / 4194304)), ((530657 / 6400), (31703196519 / 16777216)),
    ((2169353 / 25600), (16200536429 / 8388608)), ((2238203 / 25600), (33429404285 / 16777216)),
    ((568407 / 6400), (16979252911 / 8388608)), ((2367903 / 25600), (17683290277 / 8388608)),
    ((1211589 / 12800), (36192158181 / 16777216)), ((2454403 / 25600), (9164632315 / 4194304)),
    ((2530203 / 25600), (18895332329 / 8388608))]

private noncomputable def centerSum3 : ℝ :=
  (pairs3.map (fun p => realTerm p.1 (364644121 / 16000000))).sum

/-- Scalar upper bound for the actual center sum at this pilot node. -/
private theorem realNode3 : centerSum3 ≤ 99 / 256 := by
  have h := sum_le_upper (364644121 / 16000000) pairs3 (by decide +kernel)
  have hq : (pairs3.map (fun p => upperTerm p.1 (364644121 / 16000000) p.2)).sum ≤ 99 / 256 := by
    decide +kernel
  exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hq)

private def pairs4 : List (ℚ × ℚ) :=
  [((361953 / 25600), (5406487905 / 16777216)), ((269139 / 12800), (8040252455 / 16777216)),
    ((640403 / 25600), (9565692435 / 16777216)), ((779003 / 25600), (5817979541 / 8388608)),
    ((843253 / 25600), (3148915153 / 4194304)), ((120291 / 3200), (14374282553 / 16777216)),
    ((261907 / 6400), (15648407697 / 16777216)), ((554639 / 12800), (517789783 / 524288)),
    ((1229053 / 25600), (18358350889 / 16777216)), ((159291 / 3200), (19034623057 / 16777216)),
    ((1356153 / 25600), (20256842165 / 16777216)), ((180641 / 3200), (21585860743 / 16777216)),
    ((1519403 / 25600), (11347652793 / 8388608)), ((1557403 / 25600), (2907863895 / 2097152)),
    ((1667003 / 25600), (6225001283 / 4194304)), ((1717353 / 25600), (12826041259 / 8388608)),
    ((1780503 / 25600), (1662209585 / 1048576)), ((461257 / 6400), (13779581281 / 8388608)),
    ((1938153 / 25600), (7237542411 / 4194304)), ((493757 / 6400), (14750485553 / 8388608)),
    ((2031153 / 25600), (15169654801 / 8388608)), ((530657 / 6400), (7926417663 / 4194304)),
    ((2169353 / 25600), (32403601453 / 16777216)), ((2238203 / 25600), (8358003283 / 4194304)),
    ((568407 / 6400), (4245144495 / 2097152)), ((2367903 / 25600), (17684670289 / 8388608)),
    ((1211589 / 12800), (18097491317 / 8388608)), ((2454403 / 25600), (36661390109 / 16777216)),
    ((2530203 / 25600), (9448403465 / 4194304))]

private noncomputable def centerSum4 : ℝ :=
  (pairs4.map (fun p => realTerm p.1 (182336289 / 8000000))).sum

/-- Scalar upper bound for the actual center sum at this pilot node. -/
private theorem realNode4 : centerSum4 ≤ 93 / 256 := by
  have h := sum_le_upper (182336289 / 8000000) pairs4 (by decide +kernel)
  have hq : (pairs4.map (fun p => upperTerm p.1 (182336289 / 8000000) p.2)).sum ≤ 93 / 256 := by
    decide +kernel
  exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hq)

private def pairs5 : List (ℚ × ℚ) :=
  [((361953 / 25600), (5407331689 / 16777216)), ((269139 / 12800), (8041507287 / 16777216)),
    ((640403 / 25600), (9567185341 / 16777216)), ((779003 / 25600), (2909443773 / 4194304)),
    ((843253 / 25600), (12597626401 / 16777216)), ((120291 / 3200), (7188262965 / 8388608)),
    ((261907 / 6400), (15650849925 / 16777216)), ((554639 / 12800), (8285929501 / 8388608)),
    ((1229053 / 25600), (18361216055 / 16777216)), ((159291 / 3200), (19037593767 / 16777216)),
    ((1356153 / 25600), (10130001813 / 8388608)), ((180641 / 3200), (10794614811 / 8388608)),
    ((1519403 / 25600), (11349423807 / 8388608)), ((1557403 / 25600), (11633270887 / 8388608)),
    ((1667003 / 25600), (24903891245 / 16777216)), ((1717353 / 25600), (25656086007 / 16777216)),
    ((1780503 / 25600), (415617251 / 262144)), ((461257 / 6400), (27563463687 / 16777216)),
    ((1938153 / 25600), (28954687861 / 16777216)), ((493757 / 6400), (14752787643 / 8388608)),
    ((2031153 / 25600), (7586011155 / 4194304)), ((530657 / 6400), (31710618917 / 16777216)),
    ((2169353 / 25600), (32408658643 / 16777216)), ((2238203 / 25600), (33437230825 / 16777216)),
    ((568407 / 6400), (33966456235 / 16777216)), ((2367903 / 25600), (8843715157 / 4194304)),
    ((1211589 / 12800), (9050157885 / 4194304)), ((2454403 / 25600), (36667111807 / 16777216)),
    ((2530203 / 25600), (37799512263 / 16777216))]

private noncomputable def centerSum5 : ℝ :=
  (pairs5.map (fun p => realTerm p.1 (91182373 / 4000000))).sum

/-- Scalar upper bound for the actual center sum at this pilot node. -/
private theorem realNode5 : centerSum5 ≤ 79 / 256 := by
  have h := sum_le_upper (91182373 / 4000000) pairs5 (by decide +kernel)
  have hq : (pairs5.map (fun p => upperTerm p.1 (91182373 / 4000000) p.2)).sum ≤ 79 / 256 := by
    decide +kernel
  exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hq)

private def pairs6 : List (ℚ × ℚ) :=
  [((361953 / 25600), (5409019257 / 16777216)), ((269139 / 12800), (8044016951 / 16777216)),
    ((640403 / 25600), (9570171153 / 16777216)), ((779003 / 25600), (1455175889 / 2097152)),
    ((843253 / 25600), (3150389495 / 4194304)), ((120291 / 3200), (14381012683 / 16777216)),
    ((261907 / 6400), (3913933595 / 4194304)), ((554639 / 12800), (16577030895 / 16777216)),
    ((1229053 / 25600), (18366946385 / 16777216)), ((159291 / 3200), (4760883797 / 4194304)),
    ((1356153 / 25600), (10133163273 / 8388608)), ((180641 / 3200), (21595967379 / 16777216)),
    ((1519403 / 25600), (22705931671 / 16777216)), ((1557403 / 25600), (11636901501 / 8388608)),
    ((1667003 / 25600), (24911663471 / 16777216)), ((1717353 / 25600), (25664092985 / 16777216)),
    ((1780503 / 25600), (831493921 / 524288)), ((461257 / 6400), (1723254121 / 1048576)),
    ((1938153 / 25600), (3620465537 / 2097152)), ((493757 / 6400), (14757391823 / 8388608)),
    ((2031153 / 25600), (15176757329 / 8388608)), ((530657 / 6400), (31720515447 / 16777216)),
    ((2169353 / 25600), (1013086657 / 524288)), ((2238203 / 25600), (33447666211 / 16777216)),
    ((568407 / 6400), (33977056787 / 16777216)), ((2367903 / 25600), (35385900727 / 16777216)),
    ((1211589 / 12800), (36211929353 / 16777216)), ((2454403 / 25600), (36678555203 / 16777216)),
    ((2530203 / 25600), (9452827267 / 4194304))]

private noncomputable def centerSum6 : ℝ :=
  (pairs6.map (fun p => realTerm p.1 (9121083 / 400000))).sum

/-- Scalar upper bound for the actual center sum at this pilot node. -/
private theorem realNode6 : centerSum6 ≤ 51 / 256 := by
  have h := sum_le_upper (9121083 / 400000) pairs6 (by decide +kernel)
  have hq : (pairs6.map (fun p => upperTerm p.1 (9121083 / 400000) p.2)).sum ≤ 51 / 256 := by
    decide +kernel
  exact h.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hq)

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

private theorem bound0 : -moments heights ((22788479 / 1000000 : ℚ) : ℝ) 0 ≤ 104 / 256 := by
  change -moments (pairs0.map (fun p => (p.1 : ℝ))) _ 0 ≤ _
  rw [center_sum_eq]
  exact realNode0

private theorem bound1 : -moments heights ((1458491113 / 64000000 : ℚ) : ℝ) 0 ≤ 103 / 256 := by
  change -moments (pairs1.map (fun p => (p.1 : ℝ))) _ 0 ≤ _
  rw [center_sum_eq]
  exact realNode1

private theorem bound2 : -moments heights ((145851957 / 6400000 : ℚ) : ℝ) 0 ≤ 102 / 256 := by
  change -moments (pairs2.map (fun p => (p.1 : ℝ))) _ 0 ≤ _
  rw [center_sum_eq]
  exact realNode2

private theorem bound3 : -moments heights ((364644121 / 16000000 : ℚ) : ℝ) 0 ≤ 99 / 256 := by
  change -moments (pairs3.map (fun p => (p.1 : ℝ))) _ 0 ≤ _
  rw [center_sum_eq]
  exact realNode3

private theorem bound4 : -moments heights ((182336289 / 8000000 : ℚ) : ℝ) 0 ≤ 93 / 256 := by
  change -moments (pairs4.map (fun p => (p.1 : ℝ))) _ 0 ≤ _
  rw [center_sum_eq]
  exact realNode4

private theorem bound5 : -moments heights ((91182373 / 4000000 : ℚ) : ℝ) 0 ≤ 79 / 256 := by
  change -moments (pairs5.map (fun p => (p.1 : ℝ))) _ 0 ≤ _
  rw [center_sum_eq]
  exact realNode5

private theorem bound6 : -moments heights ((9121083 / 400000 : ℚ) : ℝ) 0 ≤ 51 / 256 := by
  change -moments (pairs6.map (fun p => (p.1 : ℝ))) _ 0 ≤ _
  rw [center_sum_eq]
  exact realNode6

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
  22788479 / 1000000

private def right0 : ℚ :=
  1458491113 / 64000000

private theorem cell0 (x : ℝ) (hx : x ∈ Set.Icc (left0 : ℝ) (right0 : ℝ)) :
    -moments heights x 0 ≤ 104 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 := by
  have hab : left0 < right0 := by decide +kernel
  exact
    centers_chord heights heights_pos (by exact_mod_cast hab) hx (bound0.trans (by norm_num only))
      (bound1.trans (by norm_num only))

private theorem shifted0 (x d : ℝ) (hd : 0 ≤ d) (hx : x ∈ Set.Icc ((left0 : ℝ) - d) (right0 : ℝ)) :
    -moments heights x 0 ≤ 104 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 + 58 * d := by
  have hlen : heights.length = 29 := rfl
  have hcost : 0 ≤ heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (List.sum_nonneg (fun g hg => (heights_pos g hg).le)) (sq_nonneg _))
      (by norm_num only)
  by_cases hl : (left0 : ℝ) ≤ x
  · linarith only [cell0 x ⟨hl, hx.2⟩, hd]
  have hs := left_shift heights (le_of_not_ge hl)
  rw [hlen, Nat.cast_ofNat] at hs
  have ha : -moments heights (left0 : ℝ) 0 ≤ 104 / 256 := bound0.trans (by norm_num only)
  have hlo : (left0 : ℝ) - d ≤ x := hx.1
  linarith only [hs, ha, hlo, hcost]

private def delta0 : ℚ :=
  16037623601729 / 250000000000000000

private theorem smoothed0 (L : ℝ) (hL : L ∈ Set.Icc (left0 : ℝ) (right0 : ℝ)) :
    let D : ℝ := delta0;
    -moments heights (L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2)) 0 ≤
      104 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 + 58 * (D / (2 - D)) := by
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
      104 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
        104 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
        104 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
        (104 / 256 + heights.sum * ((right0 : ℝ) - left0) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
      (10266708767 / 10000000000) := by
  have b0 :=
    decay_tick (5697 / 1000) (167801 / 50000000) (z := 1 * L / 4) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (5697 / 1000 : ℚ) ≤ 1 * left0 / 4 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b1 :=
    decay_tick (1899 / 500) (560389 / 25000000) (z := 1 * L / 6) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1899 / 500 : ℚ) ≤ 1 * left0 / 6 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b2 :=
    decay_tick (1899 / 250) (25123 / 50000000) (z := 1 * L / 3) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1899 / 250 : ℚ) ≤ 1 * left0 / 3 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b3 :=
    decay_tick (1709 / 250) (1343 / 1250000) (z := 3 * L / 10) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1709 / 250 : ℚ) ≤ 3 * left0 / 10 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b4 :=
    decay_tick (1823 / 200) (11001 / 100000000) (z := 2 * L / 5) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1823 / 200 : ℚ) ≤ 2 * left0 / 5 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  simp only [one_mul, neg_div, neg_mul] at b0 b1 b2 b3 b4 ⊢
  linarith only [b0, b1, b2, b3, b4]

private theorem coefficient0 (L : ℝ) (hl : (left0 : ℝ) ≤ L) :
    (8914091 / 500000) ≤ L * (L - Real.log L) / (8 * Real.pi) := by
  have h :=
    coefficient_tick left0 (195391 / 62500) (8914091 / 500000) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hl
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The Lee-Nosal lower bound holds at every logarithmic coordinate of this cell. -/
private theorem lowerCell0 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left0 : ℝ) (right0 : ℝ)) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hp :
    rationalPhaseCap (pairs0.map Prod.fst) (104) left0 right0 delta0 ≤ 543339 / 1000000 := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).2 hp
  rw [cast_phase_cap] at hr
  simp only [List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_ofNat] at hr
  have hm := max_le (by norm_num only : (0 : ℝ) ≤ 543339 / 1000000) hr
  have ha : (22 : ℝ) ≤ left0 := by exact_mod_cast (by decide +kernel : (22 : ℚ) ≤ left0)
  have hb : (right0 : ℝ) ≤ 27 := by exact_mod_cast (by decide +kernel : right0 ≤ (27 : ℚ))
  have hg :=
    AnalyticNumberTheory.RiemannZeta.theta_phase_error hRH ha hb hL (ledger0 hRH L hL)
      (defect0 L hL.1)
  dsimp only [heights] at hg
  let c :=
    (right0 : ℝ) / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / ((left0 : ℝ) * (6283 / 8000)))
  have hc :
    (right0 : ℝ) / 8 + 7 / 50000 + 543339 / 1000000 + 3640 * (1 / 999) ^ 2 / 24 +
        ((c ^ 2 + 2 * c + 2) / (6283 / 1000) - 143 / 125) ≤
      (8914091 / 500000) - (10266708767 / 10000000000) := by
    norm_num only [c, right0, left0, Rat.cast_div, Rat.cast_ofNat]
  dsimp only [c] at hc
  linarith only [hg, hm, hc, coefficient0 L hL.1]

private def left1 : ℚ :=
  1458491113 / 64000000

private def right1 : ℚ :=
  145851957 / 6400000

private theorem cell1 (x : ℝ) (hx : x ∈ Set.Icc (left1 : ℝ) (right1 : ℝ)) :
    -moments heights x 0 ≤ 103 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 := by
  have hab : left1 < right1 := by decide +kernel
  exact
    centers_chord heights heights_pos (by exact_mod_cast hab) hx (bound1.trans (by norm_num only))
      (bound2.trans (by norm_num only))

private theorem shifted1 (x d : ℝ) (hd : 0 ≤ d) (hx : x ∈ Set.Icc ((left1 : ℝ) - d) (right1 : ℝ)) :
    -moments heights x 0 ≤ 103 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 + 58 * d := by
  have hlen : heights.length = 29 := rfl
  have hcost : 0 ≤ heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (List.sum_nonneg (fun g hg => (heights_pos g hg).le)) (sq_nonneg _))
      (by norm_num only)
  by_cases hl : (left1 : ℝ) ≤ x
  · linarith only [cell1 x ⟨hl, hx.2⟩, hd]
  have hs := left_shift heights (le_of_not_ge hl)
  rw [hlen, Nat.cast_ofNat] at hs
  have ha : -moments heights (left1 : ℝ) 0 ≤ 103 / 256 := bound1.trans (by norm_num only)
  have hlo : (left1 : ℝ) - d ≤ x := hx.1
  linarith only [hs, ha, hlo, hcost]

private def delta1 : ℚ :=
  64137485437381 / 1000000000000000000

private theorem smoothed1 (L : ℝ) (hL : L ∈ Set.Icc (left1 : ℝ) (right1 : ℝ)) :
    let D : ℝ := delta1;
    -moments heights (L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2)) 0 ≤
      103 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 + 58 * (D / (2 - D)) := by
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
      103 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
        103 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
        103 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
        (103 / 256 + heights.sum * ((right1 : ℝ) - left1) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
      (10266708767 / 10000000000) := by
  have b0 :=
    decay_tick (5697 / 1000) (167801 / 50000000) (z := 1 * L / 4) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (5697 / 1000 : ℚ) ≤ 1 * left1 / 4 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b1 :=
    decay_tick (1899 / 500) (560389 / 25000000) (z := 1 * L / 6) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1899 / 500 : ℚ) ≤ 1 * left1 / 6 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b2 :=
    decay_tick (1899 / 250) (25123 / 50000000) (z := 1 * L / 3) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1899 / 250 : ℚ) ≤ 1 * left1 / 3 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b3 :=
    decay_tick (1709 / 250) (1343 / 1250000) (z := 3 * L / 10) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1709 / 250 : ℚ) ≤ 3 * left1 / 10 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b4 :=
    decay_tick (1823 / 200) (11001 / 100000000) (z := 2 * L / 5) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1823 / 200 : ℚ) ≤ 2 * left1 / 5 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  simp only [one_mul, neg_div, neg_mul] at b0 b1 b2 b3 b4 ⊢
  linarith only [b0, b1, b2, b3, b4]

private theorem coefficient1 (L : ℝ) (hl : (left1 : ℝ) ≤ L) :
    (4457229 / 250000) ≤ L * (L - Real.log L) / (8 * Real.pi) := by
  have h :=
    coefficient_tick left1 (125051 / 40000) (4457229 / 250000) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hl
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The Lee-Nosal lower bound holds at every logarithmic coordinate of this cell. -/
private theorem lowerCell1 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left1 : ℝ) (right1 : ℝ)) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hp :
    rationalPhaseCap (pairs0.map Prod.fst) (103) left1 right1 delta1 ≤ 539435 / 1000000 := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).2 hp
  rw [cast_phase_cap] at hr
  simp only [List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_ofNat] at hr
  have hm := max_le (by norm_num only : (0 : ℝ) ≤ 539435 / 1000000) hr
  have ha : (22 : ℝ) ≤ left1 := by exact_mod_cast (by decide +kernel : (22 : ℚ) ≤ left1)
  have hb : (right1 : ℝ) ≤ 27 := by exact_mod_cast (by decide +kernel : right1 ≤ (27 : ℚ))
  have hg :=
    AnalyticNumberTheory.RiemannZeta.theta_phase_error hRH ha hb hL (ledger1 hRH L hL)
      (defect1 L hL.1)
  dsimp only [heights] at hg
  let c :=
    (right1 : ℝ) / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / ((left1 : ℝ) * (6283 / 8000)))
  have hc :
    (right1 : ℝ) / 8 + 7 / 50000 + 539435 / 1000000 + 3640 * (1 / 999) ^ 2 / 24 +
        ((c ^ 2 + 2 * c + 2) / (6283 / 1000) - 143 / 125) ≤
      (4457229 / 250000) - (10266708767 / 10000000000) := by
    norm_num only [c, right1, left1, Rat.cast_div, Rat.cast_ofNat]
  dsimp only [c] at hc
  linarith only [hg, hm, hc, coefficient1 L hL.1]

private def left2 : ℚ :=
  145851957 / 6400000

private def right2 : ℚ :=
  364644121 / 16000000

private theorem cell2 (x : ℝ) (hx : x ∈ Set.Icc (left2 : ℝ) (right2 : ℝ)) :
    -moments heights x 0 ≤ 102 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 := by
  have hab : left2 < right2 := by decide +kernel
  exact
    centers_chord heights heights_pos (by exact_mod_cast hab) hx (bound2.trans (by norm_num only))
      (bound3.trans (by norm_num only))

private theorem shifted2 (x d : ℝ) (hd : 0 ≤ d) (hx : x ∈ Set.Icc ((left2 : ℝ) - d) (right2 : ℝ)) :
    -moments heights x 0 ≤ 102 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 + 58 * d := by
  have hlen : heights.length = 29 := rfl
  have hcost : 0 ≤ heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (List.sum_nonneg (fun g hg => (heights_pos g hg).le)) (sq_nonneg _))
      (by norm_num only)
  by_cases hl : (left2 : ℝ) ≤ x
  · linarith only [cell2 x ⟨hl, hx.2⟩, hd]
  have hs := left_shift heights (le_of_not_ge hl)
  rw [hlen, Nat.cast_ofNat] at hs
  have ha : -moments heights (left2 : ℝ) 0 ≤ 102 / 256 := bound2.trans (by norm_num only)
  have hlo : (left2 : ℝ) - d ≤ x := hx.1
  linarith only [hs, ha, hlo, hcost]

private def delta2 : ℚ :=
  64124479081501 / 1000000000000000000

private theorem smoothed2 (L : ℝ) (hL : L ∈ Set.Icc (left2 : ℝ) (right2 : ℝ)) :
    let D : ℝ := delta2;
    -moments heights (L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2)) 0 ≤
      102 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 + 58 * (D / (2 - D)) := by
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
      102 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
        102 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
        102 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
        (102 / 256 + heights.sum * ((right2 : ℝ) - left2) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
      (10266708767 / 10000000000) := by
  have b0 :=
    decay_tick (5697 / 1000) (167801 / 50000000) (z := 1 * L / 4) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (5697 / 1000 : ℚ) ≤ 1 * left2 / 4 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b1 :=
    decay_tick (1899 / 500) (560389 / 25000000) (z := 1 * L / 6) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1899 / 500 : ℚ) ≤ 1 * left2 / 6 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b2 :=
    decay_tick (1899 / 250) (25123 / 50000000) (z := 1 * L / 3) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1899 / 250 : ℚ) ≤ 1 * left2 / 3 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b3 :=
    decay_tick (1709 / 250) (1343 / 1250000) (z := 3 * L / 10) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1709 / 250 : ℚ) ≤ 3 * left2 / 10 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b4 :=
    decay_tick (1823 / 200) (11001 / 100000000) (z := 2 * L / 5) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1823 / 200 : ℚ) ≤ 2 * left2 / 5 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  simp only [one_mul, neg_div, neg_mul] at b0 b1 b2 b3 b4 ⊢
  linarith only [b0, b1, b2, b3, b4]

private theorem coefficient2 (L : ℝ) (hl : (left2 : ℝ) ≤ L) :
    (17829649 / 1000000) ≤ L * (L - Real.log L) / (8 * Real.pi) := by
  have h :=
    coefficient_tick left2 (625259 / 200000) (17829649 / 1000000) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hl
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The Lee-Nosal lower bound holds at every logarithmic coordinate of this cell. -/
private theorem lowerCell2 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left2 : ℝ) (right2 : ℝ)) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hp :
    rationalPhaseCap (pairs0.map Prod.fst) (102) left2 right2 delta2 ≤ 535802 / 1000000 := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).2 hp
  rw [cast_phase_cap] at hr
  simp only [List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_ofNat] at hr
  have hm := max_le (by norm_num only : (0 : ℝ) ≤ 535802 / 1000000) hr
  have ha : (22 : ℝ) ≤ left2 := by exact_mod_cast (by decide +kernel : (22 : ℚ) ≤ left2)
  have hb : (right2 : ℝ) ≤ 27 := by exact_mod_cast (by decide +kernel : right2 ≤ (27 : ℚ))
  have hg :=
    AnalyticNumberTheory.RiemannZeta.theta_phase_error hRH ha hb hL (ledger2 hRH L hL)
      (defect2 L hL.1)
  dsimp only [heights] at hg
  let c :=
    (right2 : ℝ) / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / ((left2 : ℝ) * (6283 / 8000)))
  have hc :
    (right2 : ℝ) / 8 + 7 / 50000 + 535802 / 1000000 + 3640 * (1 / 999) ^ 2 / 24 +
        ((c ^ 2 + 2 * c + 2) / (6283 / 1000) - 143 / 125) ≤
      (17829649 / 1000000) - (10266708767 / 10000000000) := by
    norm_num only [c, right2, left2, Rat.cast_div, Rat.cast_ofNat]
  dsimp only [c] at hc
  linarith only [hg, hm, hc, coefficient2 L hL.1]

private def left3 : ℚ :=
  364644121 / 16000000

private def right3 : ℚ :=
  182336289 / 8000000

private theorem cell3 (x : ℝ) (hx : x ∈ Set.Icc (left3 : ℝ) (right3 : ℝ)) :
    -moments heights x 0 ≤ 99 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 := by
  have hab : left3 < right3 := by decide +kernel
  exact
    centers_chord heights heights_pos (by exact_mod_cast hab) hx (bound3.trans (by norm_num only))
      (bound4.trans (by norm_num only))

private theorem shifted3 (x d : ℝ) (hd : 0 ≤ d) (hx : x ∈ Set.Icc ((left3 : ℝ) - d) (right3 : ℝ)) :
    -moments heights x 0 ≤ 99 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 + 58 * d := by
  have hlen : heights.length = 29 := rfl
  have hcost : 0 ≤ heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (List.sum_nonneg (fun g hg => (heights_pos g hg).le)) (sq_nonneg _))
      (by norm_num only)
  by_cases hl : (left3 : ℝ) ≤ x
  · linarith only [cell3 x ⟨hl, hx.2⟩, hd]
  have hs := left_shift heights (le_of_not_ge hl)
  rw [hlen, Nat.cast_ofNat] at hs
  have ha : -moments heights (left3 : ℝ) 0 ≤ 99 / 256 := bound3.trans (by norm_num only)
  have hlo : (left3 : ℝ) - d ≤ x := hx.1
  linarith only [hs, ha, hlo, hcost]

private def delta3 : ℚ :=
  6409847420863 / 100000000000000000

private theorem smoothed3 (L : ℝ) (hL : L ∈ Set.Icc (left3 : ℝ) (right3 : ℝ)) :
    let D : ℝ := delta3;
    -moments heights (L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2)) 0 ≤
      99 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 + 58 * (D / (2 - D)) := by
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
      99 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
        99 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
        99 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
        (99 / 256 + heights.sum * ((right3 : ℝ) - left3) ^ 2 / 4 + 58 * (D / (2 - D)) +
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
      (2566674269 / 2500000000) := by
  have b0 :=
    decay_tick (5697 / 1000) (167801 / 50000000) (z := 1 * L / 4) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (5697 / 1000 : ℚ) ≤ 1 * left3 / 4 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b1 :=
    decay_tick (1899 / 500) (560389 / 25000000) (z := 1 * L / 6) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1899 / 500 : ℚ) ≤ 1 * left3 / 6 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b2 :=
    decay_tick (1899 / 250) (25123 / 50000000) (z := 1 * L / 3) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1899 / 250 : ℚ) ≤ 1 * left3 / 3 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b3 :=
    decay_tick (6837 / 1000) (26833 / 25000000) (z := 3 * L / 10) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (6837 / 1000 : ℚ) ≤ 3 * left3 / 10 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b4 :=
    decay_tick (2279 / 250) (1099 / 10000000) (z := 2 * L / 5) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (2279 / 250 : ℚ) ≤ 2 * left3 / 5 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  simp only [one_mul, neg_div, neg_mul] at b0 b1 b2 b3 b4 ⊢
  linarith only [b0, b1, b2, b3, b4]

private theorem coefficient3 (L : ℝ) (hl : (left3 : ℝ) ≤ L) :
    (4457779 / 250000) ≤ L * (L - Real.log L) / (8 * Real.pi) := by
  have h :=
    coefficient_tick left3 (1563167 / 500000) (4457779 / 250000) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hl
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The Lee-Nosal lower bound holds at every logarithmic coordinate of this cell. -/
private theorem lowerCell3 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left3 : ℝ) (right3 : ℝ)) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hp : rationalPhaseCap (pairs0.map Prod.fst) (99) left3 right3 delta3 ≤ 525163 / 1000000 := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).2 hp
  rw [cast_phase_cap] at hr
  simp only [List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_ofNat] at hr
  have hm := max_le (by norm_num only : (0 : ℝ) ≤ 525163 / 1000000) hr
  have ha : (22 : ℝ) ≤ left3 := by exact_mod_cast (by decide +kernel : (22 : ℚ) ≤ left3)
  have hb : (right3 : ℝ) ≤ 27 := by exact_mod_cast (by decide +kernel : right3 ≤ (27 : ℚ))
  have hg :=
    AnalyticNumberTheory.RiemannZeta.theta_phase_error hRH ha hb hL (ledger3 hRH L hL)
      (defect3 L hL.1)
  dsimp only [heights] at hg
  let c :=
    (right3 : ℝ) / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / ((left3 : ℝ) * (6283 / 8000)))
  have hc :
    (right3 : ℝ) / 8 + 7 / 50000 + 525163 / 1000000 + 3640 * (1 / 999) ^ 2 / 24 +
        ((c ^ 2 + 2 * c + 2) / (6283 / 1000) - 143 / 125) ≤
      (4457779 / 250000) - (2566674269 / 2500000000) := by
    norm_num only [c, right3, left3, Rat.cast_div, Rat.cast_ofNat]
  dsimp only [c] at hc
  linarith only [hg, hm, hc, coefficient3 L hL.1]

private def left4 : ℚ :=
  182336289 / 8000000

private def right4 : ℚ :=
  91182373 / 4000000

private theorem cell4 (x : ℝ) (hx : x ∈ Set.Icc (left4 : ℝ) (right4 : ℝ)) :
    -moments heights x 0 ≤ 93 / 256 + heights.sum * ((right4 : ℝ) - left4) ^ 2 / 4 := by
  have hab : left4 < right4 := by decide +kernel
  exact
    centers_chord heights heights_pos (by exact_mod_cast hab) hx (bound4.trans (by norm_num only))
      (bound5.trans (by norm_num only))

private theorem shifted4 (x d : ℝ) (hd : 0 ≤ d) (hx : x ∈ Set.Icc ((left4 : ℝ) - d) (right4 : ℝ)) :
    -moments heights x 0 ≤ 93 / 256 + heights.sum * ((right4 : ℝ) - left4) ^ 2 / 4 + 58 * d := by
  have hlen : heights.length = 29 := rfl
  have hcost : 0 ≤ heights.sum * ((right4 : ℝ) - left4) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (List.sum_nonneg (fun g hg => (heights_pos g hg).le)) (sq_nonneg _))
      (by norm_num only)
  by_cases hl : (left4 : ℝ) ≤ x
  · linarith only [cell4 x ⟨hl, hx.2⟩, hd]
  have hs := left_shift heights (le_of_not_ge hl)
  rw [hlen, Nat.cast_ofNat] at hs
  have ha : -moments heights (left4 : ℝ) 0 ≤ 93 / 256 := bound4.trans (by norm_num only)
  have hlo : (left4 : ℝ) - d ≤ x := hx.1
  linarith only [hs, ha, hlo, hcost]

private def delta4 : ℚ :=
  16011623950979 / 250000000000000000

private theorem smoothed4 (L : ℝ) (hL : L ∈ Set.Icc (left4 : ℝ) (right4 : ℝ)) :
    let D : ℝ := delta4;
    -moments heights (L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2)) 0 ≤
      93 / 256 + heights.sum * ((right4 : ℝ) - left4) ^ 2 / 4 + 58 * (D / (2 - D)) := by
  have ha : (2 : ℚ) ≤ left4 := by decide +kernel
  have hd : 0 ≤ delta4 := by decide +kernel
  have hd1 : delta4 < 1 := by decide +kernel
  have cap := cap_of_ticks left4 delta4 (by decide +kernel) hd (by decide +kernel)
  have hx := smooth_mem (by exact_mod_cast ha) hL cap (by exact_mod_cast hd1)
  have h : (delta4 : ℝ) < 1 := by exact_mod_cast hd1
  exact shifted4 _ _ (div_nonneg (by exact_mod_cast hd) (by linarith only [h])) hx

private theorem boxed4 (gs : List ℝ) (hg : List.Forall₂ inside gs heights) (L : ℝ)
    (hL : L ∈ Set.Icc (left4 : ℝ) (right4 : ℝ)) :
    let D : ℝ := delta4;
    let t := L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2);
    -moments gs t 0 ≤
      93 / 256 + heights.sum * ((right4 : ℝ) - left4) ^ 2 / 4 + 58 * (D / (2 - D)) +
        boxCost heights right4 := by
  have ha : (2 : ℝ) ≤ left4 := by exact_mod_cast (by decide +kernel : (2 : ℚ) ≤ left4)
  have hd : (delta4 : ℝ) < 1 := by exact_mod_cast (by decide +kernel : delta4 < 1)
  have cap := cap_of_ticks left4 delta4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hx := smooth_mem ha hL cap hd
  have hfrac : (delta4 : ℝ) / (2 - delta4) ≤ 1 :=
    (div_le_one (by linarith only [hd])).mpr (by linarith only [hd])
  have ht := abs_le.mpr ⟨by linarith only [hx.1, hx.2, ha, hfrac], hx.2⟩
  exact (boxed_moments hg ht).trans (add_le_add (smoothed4 L hL) (le_refl _))

private theorem midpoint4 (g : Fin 29 → ℝ) (hg : List.Forall₂ inside (List.ofFn g) heights) (L : ℝ)
    (hL : L ∈ Set.Icc (left4 : ℝ) (right4 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta4;
    0 < t ∧
      AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g (Real.log t) ≤
        93 / 256 + heights.sum * ((right4 : ℝ) - left4) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right4 := by
  have ha : (2 : ℝ) ≤ left4 := by exact_mod_cast (by decide +kernel : (2 : ℚ) ≤ left4)
  have hd : (delta4 : ℝ) < 1 := by exact_mod_cast (by decide +kernel : delta4 < 1)
  have cap := cap_of_ticks left4 delta4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hu :=
    (div_le_div_of_nonneg_right (ratio_le_left ha hL.1) (by norm_num only : (0 : ℝ) ≤ 4)).trans cap
  obtain ⟨hp, he⟩ := midpoint_phase L _ (hu.trans_lt hd)
  refine ⟨hp, ?_⟩
  rw [head_eq_moments, he]
  exact boxed4 _ hg L hL

private theorem bracketMidpoint4 (g : Fin 29 → ℝ)
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (L : ℝ)
    (hL : L ∈ Set.Icc (left4 : ℝ) (right4 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta4;
    0 < t ∧
      AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g (Real.log t) ≤
        93 / 256 + heights.sum * ((right4 : ℝ) - left4) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right4 :=
  midpoint4 g (boxes_of_bounds g hl hu) L hL

private theorem ledger4 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left4 : ℝ) (right4 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta4;
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            ((t : ℂ) ^ ρ / ρ)).re ≤
      Real.sqrt t *
        (93 / 256 + heights.sum * ((right4 : ℝ) - left4) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right4) := by
  obtain ⟨g, hm, hp, hh, hz, hl, hu⟩ :=
    AnalyticNumberTheory.RiemannZeta.low_zero_100_of_signs
      AnalyticNumberTheory.RiemannZeta.low_zero_100_sign_changes
  obtain ⟨ht, hb⟩ := bracketMidpoint4 g hl hu L hL
  dsimp only
  rw [AnalyticNumberTheory.RiemannZeta.zero_head_phase_of_count hRH
      (by norm_num only : (0 : ℝ) ≤ 100) ht g hm.injective hp hh hz
      (by
        norm_num only [Nat.cast_ofNat]
        exact AnalyticNumberTheory.RiemannZeta.zero_count_100_le_58_of_RH hRH)]
  exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

private theorem defect4 (L : ℝ) (hL : (left4 : ℝ) ≤ L) :
    1 + 4 / 5 * Real.exp (-L / 4) + Real.exp (-L / 6) + 81 / 100 * Real.exp (-L / 3) +
        Real.exp (-3 * L / 10) +
        81 / 100 * Real.exp (-2 * L / 5) ≤
      (5133333113 / 5000000000) := by
  have b0 :=
    decay_tick (2849 / 500) (335267 / 100000000) (z := 1 * L / 4) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (2849 / 500 : ℚ) ≤ 1 * left4 / 4 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b1 :=
    decay_tick (1899 / 500) (560389 / 25000000) (z := 1 * L / 6) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (1899 / 500 : ℚ) ≤ 1 * left4 / 6 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b2 :=
    decay_tick (7597 / 1000) (12549 / 25000000) (z := 1 * L / 3) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (7597 / 1000 : ℚ) ≤ 1 * left4 / 3 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b3 :=
    decay_tick (6837 / 1000) (26833 / 25000000) (z := 3 * L / 10) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (6837 / 1000 : ℚ) ≤ 3 * left4 / 10 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b4 :=
    decay_tick (2279 / 250) (1099 / 10000000) (z := 2 * L / 5) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (2279 / 250 : ℚ) ≤ 2 * left4 / 5 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  simp only [one_mul, neg_div, neg_mul] at b0 b1 b2 b3 b4 ⊢
  linarith only [b0, b1, b2, b3, b4]

private theorem coefficient4 (L : ℝ) (hl : (left4 : ℝ) ≤ L) :
    (356681 / 20000) ≤ L * (L - Real.log L) / (8 * Real.pi) := by
  have h :=
    coefficient_tick left4 (781603 / 250000) (356681 / 20000) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hl
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The Lee-Nosal lower bound holds at every logarithmic coordinate of this cell. -/
private theorem lowerCell4 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left4 : ℝ) (right4 : ℝ)) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hp : rationalPhaseCap (pairs0.map Prod.fst) (93) left4 right4 delta4 ≤ 506026 / 1000000 := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).2 hp
  rw [cast_phase_cap] at hr
  simp only [List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_ofNat] at hr
  have hm := max_le (by norm_num only : (0 : ℝ) ≤ 506026 / 1000000) hr
  have ha : (22 : ℝ) ≤ left4 := by exact_mod_cast (by decide +kernel : (22 : ℚ) ≤ left4)
  have hb : (right4 : ℝ) ≤ 27 := by exact_mod_cast (by decide +kernel : right4 ≤ (27 : ℚ))
  have hg :=
    AnalyticNumberTheory.RiemannZeta.theta_phase_error hRH ha hb hL (ledger4 hRH L hL)
      (defect4 L hL.1)
  dsimp only [heights] at hg
  let c :=
    (right4 : ℝ) / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / ((left4 : ℝ) * (6283 / 8000)))
  have hc :
    (right4 : ℝ) / 8 + 7 / 50000 + 506026 / 1000000 + 3640 * (1 / 999) ^ 2 / 24 +
        ((c ^ 2 + 2 * c + 2) / (6283 / 1000) - 143 / 125) ≤
      (356681 / 20000) - (5133333113 / 5000000000) := by
    norm_num only [c, right4, left4, Rat.cast_div, Rat.cast_ofNat]
  dsimp only [c] at hc
  linarith only [hg, hm, hc, coefficient4 L hL.1]

private def left5 : ℚ :=
  91182373 / 4000000

private def right5 : ℚ :=
  9121083 / 400000

private theorem cell5 (x : ℝ) (hx : x ∈ Set.Icc (left5 : ℝ) (right5 : ℝ)) :
    -moments heights x 0 ≤ 79 / 256 + heights.sum * ((right5 : ℝ) - left5) ^ 2 / 4 := by
  have hab : left5 < right5 := by decide +kernel
  exact
    centers_chord heights heights_pos (by exact_mod_cast hab) hx (bound5.trans (by norm_num only))
      (bound6.trans (by norm_num only))

private theorem shifted5 (x d : ℝ) (hd : 0 ≤ d) (hx : x ∈ Set.Icc ((left5 : ℝ) - d) (right5 : ℝ)) :
    -moments heights x 0 ≤ 79 / 256 + heights.sum * ((right5 : ℝ) - left5) ^ 2 / 4 + 58 * d := by
  have hlen : heights.length = 29 := rfl
  have hcost : 0 ≤ heights.sum * ((right5 : ℝ) - left5) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (List.sum_nonneg (fun g hg => (heights_pos g hg).le)) (sq_nonneg _))
      (by norm_num only)
  by_cases hl : (left5 : ℝ) ≤ x
  · linarith only [cell5 x ⟨hl, hx.2⟩, hd]
  have hs := left_shift heights (le_of_not_ge hl)
  rw [hlen, Nat.cast_ofNat] at hs
  have ha : -moments heights (left5 : ℝ) 0 ≤ 79 / 256 := bound5.trans (by norm_num only)
  have hlo : (left5 : ℝ) - d ≤ x := hx.1
  linarith only [hs, ha, hlo, hcost]

private def delta5 : ℚ :=
  31971332121219 / 500000000000000000

private theorem smoothed5 (L : ℝ) (hL : L ∈ Set.Icc (left5 : ℝ) (right5 : ℝ)) :
    let D : ℝ := delta5;
    -moments heights (L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2)) 0 ≤
      79 / 256 + heights.sum * ((right5 : ℝ) - left5) ^ 2 / 4 + 58 * (D / (2 - D)) := by
  have ha : (2 : ℚ) ≤ left5 := by decide +kernel
  have hd : 0 ≤ delta5 := by decide +kernel
  have hd1 : delta5 < 1 := by decide +kernel
  have cap := cap_of_ticks left5 delta5 (by decide +kernel) hd (by decide +kernel)
  have hx := smooth_mem (by exact_mod_cast ha) hL cap (by exact_mod_cast hd1)
  have h : (delta5 : ℝ) < 1 := by exact_mod_cast hd1
  exact shifted5 _ _ (div_nonneg (by exact_mod_cast hd) (by linarith only [h])) hx

private theorem boxed5 (gs : List ℝ) (hg : List.Forall₂ inside gs heights) (L : ℝ)
    (hL : L ∈ Set.Icc (left5 : ℝ) (right5 : ℝ)) :
    let D : ℝ := delta5;
    let t := L + Real.log (1 - L / Real.exp (L / 2) / 4 / 2);
    -moments gs t 0 ≤
      79 / 256 + heights.sum * ((right5 : ℝ) - left5) ^ 2 / 4 + 58 * (D / (2 - D)) +
        boxCost heights right5 := by
  have ha : (2 : ℝ) ≤ left5 := by exact_mod_cast (by decide +kernel : (2 : ℚ) ≤ left5)
  have hd : (delta5 : ℝ) < 1 := by exact_mod_cast (by decide +kernel : delta5 < 1)
  have cap := cap_of_ticks left5 delta5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hx := smooth_mem ha hL cap hd
  have hfrac : (delta5 : ℝ) / (2 - delta5) ≤ 1 :=
    (div_le_one (by linarith only [hd])).mpr (by linarith only [hd])
  have ht := abs_le.mpr ⟨by linarith only [hx.1, hx.2, ha, hfrac], hx.2⟩
  exact (boxed_moments hg ht).trans (add_le_add (smoothed5 L hL) (le_refl _))

private theorem midpoint5 (g : Fin 29 → ℝ) (hg : List.Forall₂ inside (List.ofFn g) heights) (L : ℝ)
    (hL : L ∈ Set.Icc (left5 : ℝ) (right5 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta5;
    0 < t ∧
      AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g (Real.log t) ≤
        79 / 256 + heights.sum * ((right5 : ℝ) - left5) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right5 := by
  have ha : (2 : ℝ) ≤ left5 := by exact_mod_cast (by decide +kernel : (2 : ℚ) ≤ left5)
  have hd : (delta5 : ℝ) < 1 := by exact_mod_cast (by decide +kernel : delta5 < 1)
  have cap := cap_of_ticks left5 delta5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hu :=
    (div_le_div_of_nonneg_right (ratio_le_left ha hL.1) (by norm_num only : (0 : ℝ) ≤ 4)).trans cap
  obtain ⟨hp, he⟩ := midpoint_phase L _ (hu.trans_lt hd)
  refine ⟨hp, ?_⟩
  rw [head_eq_moments, he]
  exact boxed5 _ hg L hL

private theorem bracketMidpoint5 (g : Fin 29 → ℝ)
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (L : ℝ)
    (hL : L ∈ Set.Icc (left5 : ℝ) (right5 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta5;
    0 < t ∧
      AnalyticNumberTheory.RiemannZeta.zeroHeadPhase g (Real.log t) ≤
        79 / 256 + heights.sum * ((right5 : ℝ) - left5) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right5 :=
  midpoint5 g (boxes_of_bounds g hl hu) L hL

private theorem ledger5 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left5 : ℝ) (right5 : ℝ)) :
    let x := Real.exp L
    let u := L / Real.exp (L / 2) / 4
    let t := (x - x * u + x) / 2
    let D : ℝ := delta5;
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            ((t : ℂ) ^ ρ / ρ)).re ≤
      Real.sqrt t *
        (79 / 256 + heights.sum * ((right5 : ℝ) - left5) ^ 2 / 4 + 58 * (D / (2 - D)) +
          boxCost heights right5) := by
  obtain ⟨g, hm, hp, hh, hz, hl, hu⟩ :=
    AnalyticNumberTheory.RiemannZeta.low_zero_100_of_signs
      AnalyticNumberTheory.RiemannZeta.low_zero_100_sign_changes
  obtain ⟨ht, hb⟩ := bracketMidpoint5 g hl hu L hL
  dsimp only
  rw [AnalyticNumberTheory.RiemannZeta.zero_head_phase_of_count hRH
      (by norm_num only : (0 : ℝ) ≤ 100) ht g hm.injective hp hh hz
      (by
        norm_num only [Nat.cast_ofNat]
        exact AnalyticNumberTheory.RiemannZeta.zero_count_100_le_58_of_RH hRH)]
  exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

private theorem defect5 (L : ℝ) (hL : (left5 : ℝ) ≤ L) :
    1 + 4 / 5 * Real.exp (-L / 4) + Real.exp (-L / 6) + 81 / 100 * Real.exp (-L / 3) +
        Real.exp (-3 * L / 10) +
        81 / 100 * Real.exp (-2 * L / 5) ≤
      (5133212847 / 5000000000) := by
  have b0 :=
    decay_tick (2849 / 500) (335267 / 100000000) (z := 1 * L / 4) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (2849 / 500 : ℚ) ≤ 1 * left5 / 4 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b1 :=
    decay_tick (3799 / 1000) (559829 / 25000000) (z := 1 * L / 6) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (3799 / 1000 : ℚ) ≤ 1 * left5 / 6 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b2 :=
    decay_tick (3799 / 500) (25073 / 50000000) (z := 1 * L / 3) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (3799 / 500 : ℚ) ≤ 1 * left5 / 3 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b3 :=
    decay_tick (3419 / 500) (4289 / 4000000) (z := 3 * L / 10) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (3419 / 500 : ℚ) ≤ 3 * left5 / 10 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  have b4 :=
    decay_tick (4559 / 500) (1371 / 12500000) (z := 2 * L / 5) (by decide +kernel)
      (by decide +kernel)
      (by
        have hq : (4559 / 500 : ℚ) ≤ 2 * left5 / 5 := by decide +kernel
        have hr := (Rat.cast_le (K := ℝ)).2 hq
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hr ⊢
        linarith only [hr, hL])
      (by decide +kernel)
  simp only [one_mul, neg_div, neg_mul] at b0 b1 b2 b3 b4 ⊢
  linarith only [b0, b1, b2, b3, b4]

private theorem coefficient5 (L : ℝ) (hl : (left5 : ℝ) ≤ L) :
    (8919959 / 500000) ≤ L * (L - Real.log L) / (8 * Real.pi) := by
  have h :=
    coefficient_tick left5 (390821 / 125000) (8919959 / 500000) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hl
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The Lee-Nosal lower bound holds at every logarithmic coordinate of this cell. -/
private theorem lowerCell5 (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left5 : ℝ) (right5 : ℝ)) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hp : rationalPhaseCap (pairs0.map Prod.fst) (79) left5 right5 delta5 ≤ 468503 / 1000000 := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).2 hp
  rw [cast_phase_cap] at hr
  simp only [List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_ofNat] at hr
  have hm := max_le (by norm_num only : (0 : ℝ) ≤ 468503 / 1000000) hr
  have ha : (22 : ℝ) ≤ left5 := by exact_mod_cast (by decide +kernel : (22 : ℚ) ≤ left5)
  have hb : (right5 : ℝ) ≤ 27 := by exact_mod_cast (by decide +kernel : right5 ≤ (27 : ℚ))
  have hg :=
    AnalyticNumberTheory.RiemannZeta.theta_phase_error hRH ha hb hL (ledger5 hRH L hL)
      (defect5 L hL.1)
  dsimp only [heights] at hg
  let c :=
    (right5 : ℝ) / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / ((left5 : ℝ) * (6283 / 8000)))
  have hc :
    (right5 : ℝ) / 8 + 7 / 50000 + 468503 / 1000000 + 3640 * (1 / 999) ^ 2 / 24 +
        ((c ^ 2 + 2 * c + 2) / (6283 / 1000) - 143 / 125) ≤
      (8919959 / 500000) - (5133212847 / 5000000000) := by
    norm_num only [c, right5, left5, Rat.cast_div, Rat.cast_ofNat]
  dsimp only [c] at hc
  linarith only [hg, hm, hc, coefficient5 L hL.1]

/-- Join the adjacent lower bounds on their closed logarithmic interval. -/
private theorem lowerBand (hRH : RiemannHypothesis) (L : ℝ)
    (hL : L ∈ Set.Icc (left0 : ℝ) (right5 : ℝ)) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  by_cases h2 : L ≤ (right2 : ℝ)
  · by_cases h1 : L ≤ (right1 : ℝ)
    · by_cases h0 : L ≤ (right0 : ℝ)
      · exact lowerCell0 hRH L ⟨hL.1, h0⟩
      · exact lowerCell1 hRH L ⟨(lt_of_not_ge h0).le, h1⟩
    · exact lowerCell2 hRH L ⟨(lt_of_not_ge h1).le, h2⟩
  · by_cases h4 : L ≤ (right4 : ℝ)
    · by_cases h3 : L ≤ (right3 : ℝ)
      · exact lowerCell3 hRH L ⟨(lt_of_not_ge h2).le, h3⟩
      · exact lowerCell4 hRH L ⟨(lt_of_not_ge h3).le, h4⟩
    · exact lowerCell5 hRH L ⟨(lt_of_not_ge h4).le, hL.2⟩

/-- The lower phase bound on the full integer-endpoint band. -/
public theorem theta_lower_analytic_overlap (hRH : RiemannHypothesis) {x : ℝ} (hx : 7886980184 ≤ x)
    (hy : x ≤ 8000000000) :
    (x - Chebyshev.theta x) / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  have hp : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hl :=
    PseudoPrime.Analysis.rationalLogIntervalCheck_sound
      (show
        PseudoPrime.Analysis.rationalLogIntervalCheck 7886980184 33 20 (22788479 / 1000000)
            (227884793 / 10000000) =
          true
        from by decide +kernel)
  have hr :=
    PseudoPrime.Analysis.rationalLogIntervalCheck_sound
      (show
        PseudoPrime.Analysis.rationalLogIntervalCheck 8000000000 33 20 (228027072 / 10000000)
            (9121083 / 400000) =
          true
        from by decide +kernel)
  have hle : ((22788479 / 1000000 : ℚ) : ℝ) ≤ Real.log 7886980184 := by
    simpa only [Rat.cast_ofNat] using hl.1
  have hre : Real.log 8000000000 ≤ ((9121083 / 400000 : ℚ) : ℝ) := by
    simpa only [Rat.cast_ofNat] using hr.2
  have h :=
    lowerBand hRH (Real.log x)
      ⟨hle.trans (Real.log_le_log (by norm_num only) hx), (Real.log_le_log hp hy).trans hre⟩
  simpa only [Real.exp_log hp] using h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
