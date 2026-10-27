/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorGrowth
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LeftVerticalDigammaBound
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Vertical gamma-factor regularity and logarithmic growth

Positive real part avoids all gamma poles. Continuity controls a bounded height interval;
the central-strip logarithmic estimate controls its complement.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Positive real part and a nonnegative real shift exclude nonpositive integral
half-arguments. Compare real parts of a purported equality. This verifies the gamma
regularity conditions for both character parities. -/
theorem half_add_ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    (s + (a : ℂ)) / 2 ≠ -(m : ℂ) := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re, Complex.neg_re,
    Complex.natCast_re] at hr
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith only [hr, hs, ha, hm]

/-- For any character and a point with positive real part, the gamma factor is analytic
there. Both parity half-arguments avoid nonpositive integers; differentiability on the
open half-plane gives analyticity. This supports local logarithmic derivatives. -/
theorem analyticAt_gammaFactor_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : AnalyticAt ℂ χ.gammaFactor s := by
  have hd : DifferentiableOn ℂ χ.gammaFactor {z : ℂ | 0 < z.re} := by
    intro z hz
    have h0 : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
      simpa only [Complex.ofReal_zero, add_zero] using
        half_add_ne_neg_nat_of_re_pos hz (a := 0) le_rfl
    rcases χ.even_or_odd with he | ho
    · exact (differentiableAt_gammaFactor_of_even_of_half_ne_neg_nat he h0).differentiableWithinAt
    · exact
        (differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat ho
            (by
              simpa only [Complex.ofReal_one] using
                half_add_ne_neg_nat_of_re_pos hz (a := 1) zero_le_one)).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

/-- At a point with positive real part, either parity gamma factor is nonzero. Apply the
regular half-argument formulas. This permits analytic division in the gamma-factor
logarithmic derivative. -/
theorem gammaFactor_ne_zero_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · apply gammaFactor_ne_zero_of_even_of_half_ne_neg_nat he
    simpa only [Complex.ofReal_zero, add_zero] using
      half_add_ne_neg_nat_of_re_pos hs (a := 0) le_rfl
  · apply gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat ho
    simpa only [Complex.ofReal_one] using half_add_ne_neg_nat_of_re_pos hs (a := 1) zero_le_one

/--
Inputs: a nontrivial Dirichlet character, a point with real part greater than one, and a
derivative order.

Claim: the iterated logarithmic derivative of the ordinary $L$ function equals that of the
completed $L$ function minus the corresponding gamma-factor derivative.

Proof: use the regular-point logarithmic derivative identity throughout the open half-plane and
differentiate that local equality.

Role: supplies the exact transfer from completed-zero detection to the ordinary $L$ derivatives
counted by the Euler-tail large sieve.
-/
theorem iteratedDeriv_logDeriv_LFunction_eq_completed_sub_gammaFactor {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s =
      iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) s -
        iteratedDeriv n (logDeriv (DirichletCharacter.gammaFactor χ)) s := by
  let U : Set ℂ := {z | 1 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hEq :
    Set.EqOn (logDeriv (DirichletCharacter.LFunction χ))
      (fun z =>
        logDeriv (DirichletCharacter.completedLFunction χ) z -
          logDeriv (DirichletCharacter.gammaFactor χ) z)
      U := by
    intro z hz
    change 1 < z.re at hz
    have hz1 : 1 ≤ z.re := le_of_lt hz
    have hL : DirichletCharacter.LFunction χ z ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) hz1
    have hΓ := gammaFactor_ne_zero_of_re_pos χ (by linarith only [hz])
    have hquot :=
      DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z
        (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne))
    have hF : DirichletCharacter.completedLFunction χ z ≠ 0 := by
      intro hzero
      apply hL
      rw [hquot, hzero, zero_div]
    have hdΓ := (analyticAt_gammaFactor_of_re_pos χ (by linarith only [hz])).differentiableAt
    exact logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne hF hΓ hdΓ
  have hpoint := (Set.EqOn.iteratedDeriv_of_isOpen hEq hU n) hs
  have hcompleted : AnalyticAt ℂ (logDeriv (DirichletCharacter.completedLFunction χ)) s := by
    rw [logDeriv]
    have hF := DirichletCharacter.differentiable_completedLFunction hne
    have hFa := hF.analyticAt s
    have hL : DirichletCharacter.LFunction χ s ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (le_of_lt hs)
    have hquot :=
      DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s
        (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne))
    have hFne : DirichletCharacter.completedLFunction χ s ≠ 0 := by
      intro hzero
      apply hL
      rw [hquot, hzero, zero_div]
    exact hFa.deriv.div hFa hFne
  have hgamma : AnalyticAt ℂ (logDeriv (DirichletCharacter.gammaFactor χ)) s := by
    rw [logDeriv]
    have hΓ := analyticAt_gammaFactor_of_re_pos χ (by linarith only [hs])
    exact hΓ.deriv.div hΓ (gammaFactor_ne_zero_of_re_pos χ (by linarith only [hs]))
  have hfun :
    (fun z =>
        logDeriv (DirichletCharacter.completedLFunction χ) z -
          logDeriv (DirichletCharacter.gammaFactor χ) z) =
      logDeriv (DirichletCharacter.completedLFunction χ) -
        logDeriv (DirichletCharacter.gammaFactor χ) :=
    rfl
  calc
    iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s =
        iteratedDeriv n
          (fun z =>
            logDeriv (DirichletCharacter.completedLFunction χ) z -
              logDeriv (DirichletCharacter.gammaFactor χ) z)
          s :=
      hpoint
    _ =
        iteratedDeriv n
          (logDeriv (DirichletCharacter.completedLFunction χ) -
            logDeriv (DirichletCharacter.gammaFactor χ))
          s :=
      by rw [hfun]
    _ = _ := iteratedDeriv_sub hcompleted.contDiffAt hgamma.contDiffAt

/--
Inputs: a completed logarithmic-derivative lower bound and a bound for the gamma-factor
correction at the same point and order.

Claim: the ordinary $L$-function logarithmic derivative has the lower bound obtained by
subtracting the gamma correction.

Proof: rewrite the completed derivative as the sum of the ordinary derivative and the gamma
derivative, then apply the triangle inequality.

Role: transfers local zero detection into the large-value set used by the Euler-tail large sieve.
-/
theorem norm_iteratedDeriv_logDeriv_LFunction_ge_of_completed {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) (n : ℕ) {A G : ℝ}
    (hcompleted : A ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) s‖)
    (hgamma : ‖iteratedDeriv n (logDeriv (DirichletCharacter.gammaFactor χ)) s‖ ≤ G) :
    A - G ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ := by
  have hidentity := iteratedDeriv_logDeriv_LFunction_eq_completed_sub_gammaFactor hne hs n
  have hsum :
    iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) s =
      iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s +
        iteratedDeriv n (logDeriv (DirichletCharacter.gammaFactor χ)) s := by
    rw [hidentity]
    ring
  have htriangle :=
    norm_add_le (iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s)
      (iteratedDeriv n (logDeriv (DirichletCharacter.gammaFactor χ)) s)
  rw [← hsum] at htriangle
  linarith only [hcompleted, hgamma, htriangle]

/--
Inputs: a Dirichlet character and a point in the fixed strip `3/4 ≤ Re s ≤ 3/2`.

Claim: the gamma-factor logarithmic derivative is bounded by a constant times
`log (2 |Im s| + 2) + 1`, uniformly over all moduli and character parities.

Proof: use the exact parity formulas for the gamma factor and the explicit uniform digamma
bound on the resulting positive-real-part half-arguments.

Role: supplies the pointwise majorant needed for Cauchy bounds on higher gamma-factor derivatives.
-/
theorem exists_uniform_norm_logDeriv_gammaFactor_on_strip :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ},
          3 / 4 ≤ s.re →
            s.re ≤ 3 / 2 →
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ ≤
              C * (Real.log (2 * |s.im| + 2) + 1) := by
  obtain ⟨Cψ, hCψ, hψ⟩ := exists_C_forall_norm_digamma_explicit_le
  have hdigamma :
    ∀ (a u : ℝ),
      3 / 8 ≤ a →
        a ≤ 5 / 4 →
        ‖Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ ≤ Cψ * (50 + Real.log (4 * |u| + 2)) := by
    intro a u ha₀ ha₁
    have haabs : |a| ≤ (2 : ℝ) + 2 := by
      rw [abs_of_nonneg (by linarith only [ha₀])]
      linarith only [ha₁]
    have hasep : ∀ q : ℕ, (1 : ℝ) / 4 ≤ |a + (q : ℝ)| := by
      intro q
      have hnonneg : 0 ≤ a + (q : ℝ) := add_nonneg (by linarith only [ha₀]) (Nat.cast_nonneg q)
      rw [abs_of_nonneg hnonneg]
      have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
      norm_num only
      linarith only [ha₀, hq]
    have hbound := hψ 2 (by norm_num only) a u haabs hasep
    have hlog : Real.log (2 * |u| + 2) ≤ Real.log (4 * |u| + 2) := by
      apply Real.log_le_log
      · nlinarith only [abs_nonneg u]
      · nlinarith only [abs_nonneg u]
    have hbound' :
      ‖Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ ≤ Cψ * (50 + Real.log (4 * |u| + 2)) := by
      have hnum : ((2 : ℝ) + 5) ^ 2 + 1 = 50 := by norm_num only
      norm_num only at hbound
      calc
        _ ≤ Cψ * (50 + Real.log (2 * |u| + 2)) := hbound
        _ ≤ _ := by
          have hlog' : 50 + Real.log (2 * |u| + 2) ≤ 50 + Real.log (4 * |u| + 2) := by
            linarith only [hlog]
          exact mul_le_mul_of_nonneg_left hlog' hCψ
    exact hbound'
  let C : ℝ := ‖Complex.log (Real.pi : ℂ)‖ + 50 * Cψ + 1
  have hC : 0 ≤ C := by
    dsimp only [C]
    linarith only [norm_nonneg (Complex.log (Real.pi : ℂ)), hCψ]
  refine ⟨C, hC, ?_⟩
  intro N χ s hslo hshi
  let L : ℝ := Real.log (2 * |s.im| + 2)
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact Real.log_nonneg (by nlinarith only [abs_nonneg s.im])
  have hcoef : ‖Complex.log (Real.pi : ℂ)‖ / 2 + Cψ * (50 + L) / 2 ≤ C * (L + 1) := by
    have hLplus : 1 ≤ L + 1 := by linarith only [hL]
    have hpi' := mul_le_mul_of_nonneg_left hLplus (norm_nonneg (Complex.log (Real.pi : ℂ)))
    have hpi : ‖Complex.log (Real.pi : ℂ)‖ ≤ ‖Complex.log (Real.pi : ℂ)‖ * (L + 1) := by
      simpa only [mul_one] using hpi'
    have hlogarg : 50 + L ≤ 50 * (L + 1) := by nlinarith only [hL]
    have hpsi := mul_le_mul_of_nonneg_left hlogarg hCψ
    have hsum :
      ‖Complex.log (Real.pi : ℂ)‖ + Cψ * (50 + L) ≤
        (‖Complex.log (Real.pi : ℂ)‖ + 50 * Cψ) * (L + 1) := by
      calc
        _ ≤ ‖Complex.log (Real.pi : ℂ)‖ * (L + 1) + Cψ * (50 * (L + 1)) := add_le_add hpi hpsi
        _ = _ := by ring
    have hsum' := div_le_div_of_nonneg_right hsum (by norm_num only : (0 : ℝ) ≤ 2)
    dsimp only [C]
    have hbase : 0 ≤ ‖Complex.log (Real.pi : ℂ)‖ + 50 * Cψ := by positivity
    have hcoef' : (‖Complex.log (Real.pi : ℂ)‖ + 50 * Cψ) / 2 ≤ C := by
      dsimp only [C]
      linarith only [hbase]
    have hLplus0 : 0 ≤ L + 1 := le_trans (by norm_num only : (0 : ℝ) ≤ 1) hLplus
    calc
      ‖Complex.log (Real.pi : ℂ)‖ / 2 + Cψ * (50 + L) / 2 =
          (‖Complex.log (Real.pi : ℂ)‖ + Cψ * (50 + L)) / 2 :=
        by ring
      _ ≤ (‖Complex.log (Real.pi : ℂ)‖ + 50 * Cψ) * (L + 1) / 2 := hsum'
      _ = ((‖Complex.log (Real.pi : ℂ)‖ + 50 * Cψ) / 2) * (L + 1) := by ring
      _ ≤ C * (L + 1) := mul_le_mul_of_nonneg_right hcoef' hLplus0
  rcases χ.even_or_odd with he | ho
  · have hhalf : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m
      simpa only [Complex.ofReal_zero, add_zero] using
        half_add_ne_neg_nat_of_re_pos (by linarith only [hslo]) (a := 0) le_rfl m
    have hformula := logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat he hhalf
    have harg : s / 2 = ((s.re / 2 : ℝ) : ℂ) + ((s.im / 2 : ℝ) : ℂ) * Complex.I := by
      calc
        s / 2 = ((s / 2).re : ℂ) + (s / 2).im * Complex.I := (Complex.re_add_im (s / 2)).symm
        _ = ((s.re / 2 : ℝ) : ℂ) + ((s.im / 2 : ℝ) : ℂ) * Complex.I := by
          rw [Complex.div_ofNat_re, Complex.div_ofNat_im]
    have hdig := hdigamma (s.re / 2) (s.im / 2) (by linarith only [hslo]) (by linarith only [hshi])
    have him : 4 * |s.im / 2| = 2 * |s.im| := by
      rw [abs_div, abs_of_pos (by norm_num only : (0 : ℝ) < 2)]
      ring
    have hdig' : ‖Complex.digamma (s / 2)‖ ≤ Cψ * (50 + L) := by
      rw [harg]
      rw [him] at hdig
      simpa only [L] using hdig
    have hdigHalf : ‖Complex.digamma (s / 2)‖ / 2 ≤ Cψ * (50 + L) / 2 := by
      apply (div_le_div_iff_of_pos_right (by norm_num only : (0 : ℝ) < 2)).2
      exact hdig'
    rw [hformula]
    calc
      ‖-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2) / 2‖ ≤
          ‖Complex.log (Real.pi : ℂ)‖ / 2 + ‖Complex.digamma (s / 2)‖ / 2 :=
        by
        calc
          _ ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ + ‖Complex.digamma (s / 2) / 2‖ := norm_add_le _ _
          _ = _ := by simp only [norm_div, norm_neg, Complex.norm_ofNat]
      _ ≤ ‖Complex.log (Real.pi : ℂ)‖ / 2 + Cψ * (50 + L) / 2 := by nlinarith only [hdigHalf]
      _ ≤ _ := hcoef
  · have hhalf : ∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ) := by
      intro m
      exact half_add_ne_neg_nat_of_re_pos (by linarith only [hslo]) (a := 1) zero_le_one m
    have hformula := logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat ho hhalf
    have harg : (s + 1) / 2 = (((s.re + 1) / 2 : ℝ) : ℂ) + ((s.im / 2 : ℝ) : ℂ) * Complex.I := by
      calc
        (s + 1) / 2 = (((s + 1) / 2).re : ℂ) + ((s + 1) / 2).im * Complex.I :=
          (Complex.re_add_im ((s + 1) / 2)).symm
        _ = (((s.re + 1) / 2 : ℝ) : ℂ) + ((s.im / 2 : ℝ) : ℂ) * Complex.I := by
          rw [Complex.div_ofNat_re, Complex.div_ofNat_im]
          simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
    have hdig :=
      hdigamma ((s.re + 1) / 2) (s.im / 2) (by linarith only [hslo]) (by linarith only [hshi])
    have him : 4 * |s.im / 2| = 2 * |s.im| := by
      rw [abs_div, abs_of_pos (by norm_num only : (0 : ℝ) < 2)]
      ring
    have hdig' : ‖Complex.digamma ((s + 1) / 2)‖ ≤ Cψ * (50 + L) := by
      rw [harg]
      rw [him] at hdig
      simpa only [L] using hdig
    have hdigHalf : ‖Complex.digamma ((s + 1) / 2)‖ / 2 ≤ Cψ * (50 + L) / 2 := by
      apply (div_le_div_iff_of_pos_right (by norm_num only : (0 : ℝ) < 2)).2
      exact hdig'
    rw [hformula]
    calc
      ‖-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2‖ ≤
          ‖Complex.log (Real.pi : ℂ)‖ / 2 + ‖Complex.digamma ((s + 1) / 2)‖ / 2 :=
        by
        calc
          _ ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ + ‖Complex.digamma ((s + 1) / 2) / 2‖ :=
            norm_add_le _ _
          _ = _ := by simp only [norm_div, norm_neg, Complex.norm_ofNat]
      _ ≤ ‖Complex.log (Real.pi : ℂ)‖ / 2 + Cψ * (50 + L) / 2 := by nlinarith only [hdigHalf]
      _ ≤ _ := hcoef

/-- For a fixed positive real part, the gamma-factor logarithmic derivative is continuous on
the entire vertical line. Analyticity and nonvanishing give an analytic quotient; compose
with the vertical parametrization. This controls bounded height intervals. -/
theorem continuous_logDeriv_gammaFactor_vertical {N : ℕ} (χ : DirichletCharacter ℂ N) {σ : ℝ}
    (hσ : 0 < σ) : Continuous (fun t : ℝ => logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hs : 0 < ((σ : ℂ) + Complex.I * t).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hσ
  have hg := analyticAt_gammaFactor_of_re_pos χ hs
  have hl : AnalyticAt ℂ (logDeriv χ.gammaFactor) ((σ : ℂ) + Complex.I * t) :=
    hg.deriv.div hg (gammaFactor_ne_zero_of_re_pos χ hs)
  exact
    hl.continuousAt.comp (f := fun t : ℝ => (σ : ℂ) + Complex.I * t)
      ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousAt)

/--
Inputs: a derivative order, a center with real part in `[1,5/4]`, and a bound on its height.
Claim: all character gamma logarithmic derivatives have a uniform Cauchy bound at that center.
Content: apply the strip estimate on the closed radius-one-quarter disk around the center.
Role: controls the high-order gamma correction when transferring completed derivatives to
ordinary Dirichlet L-function derivatives in the central strip.
-/
theorem exists_uniform_norm_iteratedDeriv_gammaFactor_vertical_le (n : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) {c : ℂ} {T : ℝ},
          1 ≤ c.re →
            c.re ≤ 5 / 4 →
            0 ≤ T →
            |c.im| ≤ T →
            ‖iteratedDeriv n (logDeriv χ.gammaFactor) c‖ ≤
              (n.factorial : ℝ) * C * (Real.log (4 * T + 4) + 1) / (1 / 4 : ℝ) ^ n := by
  obtain ⟨C, hC, hstrip⟩ := exists_uniform_norm_logDeriv_gammaFactor_on_strip
  refine ⟨C, hC, ?_⟩
  intro N χ c T hcLo hcHi hT hcT
  let r : ℝ := 1 / 4
  have hr : 0 < r := by norm_num only [r]
  have hball : ∀ z ∈ Metric.closedBall c r, 3 / 4 ≤ z.re ∧ z.re ≤ 3 / 2 ∧ |z.im| ≤ T + 1 / 4 := by
    intro z hz
    have hznorm : ‖z - c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hlow : c.re - z.re ≤ ‖z - c‖ := by
      have h := Complex.re_le_norm (c - z)
      rw [Complex.sub_re, norm_sub_rev] at h
      linarith only [h]
    have hup : z.re - c.re ≤ ‖z - c‖ := by
      have h := Complex.re_le_norm (z - c)
      rw [Complex.sub_re] at h
      exact h
    have him : |z.im - c.im| ≤ ‖z - c‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - c)
    have hct := abs_le.mp hcT
    have hdiff := abs_le.mp (le_trans him hznorm)
    constructor
    · dsimp only [r] at hznorm hlow
      linarith only [hznorm, hlow, hcLo]
    constructor
    · calc
        z.re ≤ c.re + ‖z - c‖ := by linarith only [hup]
        _ ≤ 5 / 4 + 1 / 4 := add_le_add hcHi hznorm
        _ = 3 / 2 := by norm_num only
    · apply abs_le.mpr
      constructor <;> dsimp only [r] at hdiff <;> linarith only [hct.1, hct.2, hdiff.1, hdiff.2, hT]
  have hanalytic : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ (logDeriv χ.gammaFactor) z := by
    intro z hz
    have hzre : 0 < z.re := by
      exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 3 / 4) (hball z hz).1
    have hg := analyticAt_gammaFactor_of_re_pos χ hzre
    have hfun : logDeriv χ.gammaFactor = fun w => deriv χ.gammaFactor w / χ.gammaFactor w := by
      funext w
      exact logDeriv_apply χ.gammaFactor w
    rw [hfun]
    exact hg.deriv.div hg (gammaFactor_ne_zero_of_re_pos χ hzre)
  have hdifferentiable : DifferentiableOn ℂ (logDeriv χ.gammaFactor) (Metric.closedBall c r) := by
    intro z hz
    exact (hanalytic z hz).differentiableAt.differentiableWithinAt
  have hcontinuous : ContinuousOn (logDeriv χ.gammaFactor) (Metric.closedBall c r) := by
    intro z hz
    exact (hanalytic z hz).continuousAt.continuousWithinAt
  have hbound :
    ∀ z ∈ Metric.sphere c r, ‖logDeriv χ.gammaFactor z‖ ≤ C * (Real.log (4 * T + 4) + 1) := by
    intro z hz
    have hclosed := Metric.sphere_subset_closedBall hz
    obtain ⟨hzlo, hzhi, hzim⟩ := hball z hclosed
    have hpoint := hstrip χ hzlo hzhi
    have harg : 2 * |z.im| + 2 ≤ 4 * T + 4 := by nlinarith only [hzim, hT]
    have hargpos : 0 < 2 * |z.im| + 2 := by positivity
    have htoppos : 0 < 4 * T + 4 := by positivity
    have hlog := Real.log_le_log hargpos harg
    calc
      ‖logDeriv χ.gammaFactor z‖ ≤ C * (Real.log (2 * |z.im| + 2) + 1) := hpoint
      _ ≤ C * (Real.log (4 * T + 4) + 1) := by
        apply mul_le_mul_of_nonneg_left _ hC
        linarith only [hlog]
  have hCauchy :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := logDeriv χ.gammaFactor) (c :=
      c) (R := r) (C := C * (Real.log (4 * T + 4) + 1)) n hr
      (DiffContOnCl.mk_ball (hdifferentiable.mono Metric.ball_subset_closedBall) hcontinuous) hbound
  simpa only [r, mul_assoc] using hCauchy

/--
Inputs: a derivative order, a center with real part in `[1, 5/4]`, and a bound on its height.
Claim: one constant bounds all character gamma logarithmic derivatives at every derivative order.
Proof: use the strip bound for the gamma logarithmic derivative and Cauchy's estimate on a
radius-`1/4` disk around each center.
Role: provides an order-independent constant for comparing high-order zero signals with the
gamma correction.
-/
theorem exists_uniform_norm_iteratedDeriv_gammaFactor_vertical_le_all :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ n : ℕ,
          ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) {c : ℂ} {T : ℝ},
            1 ≤ c.re →
              c.re ≤ 5 / 4 →
              0 ≤ T →
              |c.im| ≤ T →
              ‖iteratedDeriv n (logDeriv χ.gammaFactor) c‖ ≤
                (n.factorial : ℝ) * C * (Real.log (4 * T + 4) + 1) / (1 / 4 : ℝ) ^ n := by
  obtain ⟨C, hC, hstrip⟩ := exists_uniform_norm_logDeriv_gammaFactor_on_strip
  refine ⟨C, hC, ?_⟩
  intro n N χ c T hcLo hcHi hT hcT
  let r : ℝ := 1 / 4
  have hr : 0 < r := by norm_num only [r]
  have hball : ∀ z ∈ Metric.closedBall c r, 3 / 4 ≤ z.re ∧ z.re ≤ 3 / 2 ∧ |z.im| ≤ T + 1 / 4 := by
    intro z hz
    have hznorm : ‖z - c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hlow : c.re - z.re ≤ ‖z - c‖ := by
      have h := Complex.re_le_norm (c - z)
      rw [Complex.sub_re, norm_sub_rev] at h
      linarith only [h]
    have hup : z.re - c.re ≤ ‖z - c‖ := by
      have h := Complex.re_le_norm (z - c)
      rw [Complex.sub_re] at h
      exact h
    have him : |z.im - c.im| ≤ ‖z - c‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - c)
    have hct := abs_le.mp hcT
    have hdiff := abs_le.mp (le_trans him hznorm)
    constructor
    · dsimp only [r] at hznorm hlow
      linarith only [hznorm, hlow, hcLo]
    constructor
    · calc
        z.re ≤ c.re + ‖z - c‖ := by linarith only [hup]
        _ ≤ 5 / 4 + 1 / 4 := add_le_add hcHi hznorm
        _ = 3 / 2 := by norm_num only
    · apply abs_le.mpr
      constructor <;> dsimp only [r] at hdiff <;> linarith only [hct.1, hct.2, hdiff.1, hdiff.2, hT]
  have hanalytic : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ (logDeriv χ.gammaFactor) z := by
    intro z hz
    have hzre : 0 < z.re := by
      exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 3 / 4) (hball z hz).1
    have hg := analyticAt_gammaFactor_of_re_pos χ hzre
    have hfun : logDeriv χ.gammaFactor = fun w => deriv χ.gammaFactor w / χ.gammaFactor w := by
      funext w
      exact logDeriv_apply χ.gammaFactor w
    rw [hfun]
    exact hg.deriv.div hg (gammaFactor_ne_zero_of_re_pos χ hzre)
  have hdifferentiable : DifferentiableOn ℂ (logDeriv χ.gammaFactor) (Metric.closedBall c r) := by
    intro z hz
    exact (hanalytic z hz).differentiableAt.differentiableWithinAt
  have hcontinuous : ContinuousOn (logDeriv χ.gammaFactor) (Metric.closedBall c r) := by
    intro z hz
    exact (hanalytic z hz).continuousAt.continuousWithinAt
  have hbound :
    ∀ z ∈ Metric.sphere c r, ‖logDeriv χ.gammaFactor z‖ ≤ C * (Real.log (4 * T + 4) + 1) := by
    intro z hz
    have hclosed := Metric.sphere_subset_closedBall hz
    obtain ⟨hzlo, hzhi, hzim⟩ := hball z hclosed
    have hpoint := hstrip χ hzlo hzhi
    have harg : 2 * |z.im| + 2 ≤ 4 * T + 4 := by nlinarith only [hzim, hT]
    have hargpos : 0 < 2 * |z.im| + 2 := by positivity
    have htoppos : 0 < 4 * T + 4 := by positivity
    have hlog := Real.log_le_log hargpos harg
    calc
      ‖logDeriv χ.gammaFactor z‖ ≤ C * (Real.log (2 * |z.im| + 2) + 1) := hpoint
      _ ≤ C * (Real.log (4 * T + 4) + 1) := by
        apply mul_le_mul_of_nonneg_left _ hC
        linarith only [hlog]
  have hCauchy :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := logDeriv χ.gammaFactor) (c :=
      c) (R := r) (C := C * (Real.log (4 * T + 4) + 1)) n hr
      (DiffContOnCl.mk_ball (hdifferentiable.mono Metric.ball_subset_closedBall) hcontinuous) hbound
  simpa only [r, mul_assoc] using hCauchy

/--
Inputs: a completed logarithmic-derivative lower bound at a point just right of `1`, and a height
bound for that point.
Claim: the ordinary Dirichlet L-function logarithmic derivative is large after subtracting a
uniform high-order gamma correction.
Content: combine the Cauchy estimate for gamma derivatives with the completed-to-ordinary
derivative identity.
Role: transfers the local zero-detection output into the large-value set counted by the Euler-tail
large sieve.
-/
theorem exists_uniform_gamma_subtraction_for_ordinary_LFunction_derivative (n : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N},
          χ ≠ 1 →
            ∀ {s : ℂ} {T : ℝ},
              1 < s.re →
                1 ≤ s.re →
                s.re ≤ 5 / 4 →
                0 ≤ T →
                |s.im| ≤ T →
                ∀ {A : ℝ},
                  A ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) s‖ →
                    A - (n.factorial : ℝ) * C * (Real.log (4 * T + 4) + 1) / (1 / 4 : ℝ) ^ n ≤
                      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ := by
  obtain ⟨C, hC, hgamma⟩ := exists_uniform_norm_iteratedDeriv_gammaFactor_vertical_le n
  refine ⟨C, hC, ?_⟩
  intro N _ χ hne s T hs hslo hshi hT hsi A hA
  apply norm_iteratedDeriv_logDeriv_LFunction_ge_of_completed hne hs n hA
  exact hgamma χ hslo hshi hT hsi

/--
Inputs: a nontrivial Dirichlet character, a point in the right strip, a height bound, and an
arbitrary derivative order.
Claim: one absolute constant bounds the gamma correction in the completed-to-ordinary derivative
comparison simultaneously for every order.
Proof: apply the all-orders Cauchy estimate for the gamma logarithmic derivative and the
completed-to-ordinary derivative identity.
Role: lets later arguments choose a sufficiently high detector order without changing the
constant in the gamma error.
-/
theorem exists_uniform_gamma_subtraction_for_ordinary_LFunction_derivative_all :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ n : ℕ,
          ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N},
            χ ≠ 1 →
              ∀ {s : ℂ} {T : ℝ},
                1 < s.re →
                  1 ≤ s.re →
                  s.re ≤ 5 / 4 →
                  0 ≤ T →
                  |s.im| ≤ T →
                  ∀ {A : ℝ},
                    A ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) s‖ →
                      A - (n.factorial : ℝ) * C * (Real.log (4 * T + 4) + 1) / (1 / 4 : ℝ) ^ n ≤
                        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ := by
  obtain ⟨C, hC, hgamma⟩ := exists_uniform_norm_iteratedDeriv_gammaFactor_vertical_le_all
  refine ⟨C, hC, ?_⟩
  intro n N hN χ hne s T hs hslo hshi hT hsi A hA
  apply norm_iteratedDeriv_logDeriv_LFunction_ge_of_completed hne hs n hA
  exact hgamma n χ hslo hshi hT hsi

/-- For a fixed real part in (0,2], the gamma-factor logarithmic derivative on its vertical
line is bounded by A times log(4+abs t)+1 for some positive A. Use compact continuity
near height zero and the logarithmic strip estimate elsewhere. This supplies full-line
Mellin integrability. -/
theorem exists_norm_logDeriv_gammaFactor_vertical_le_log {N : ℕ} (χ : DirichletCharacter ℂ N)
    {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ t : ℝ,
          ‖logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t)‖ ≤ A * (Real.log (4 + |t|) + 1) := by
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
      (continuous_logDeriv_gammaFactor_vertical χ hσ).continuousOn
  let D : ℝ := ‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound + 4
  let A : ℝ := 1 + |D| + max M 0
  have hA1 : 1 ≤ A := by
    dsimp only [A]; linarith only [abs_nonneg D, le_max_right M 0]
  have hDM : D ≤ |D| := le_abs_self D
  refine ⟨A, zero_lt_one.trans_le hA1, fun t => ?_⟩
  have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  by_cases ht : 1 ≤ |t|
  · have hsr : |((σ : ℂ) + Complex.I * t).re| ≤ 2 := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, abs_of_pos hσ] using hσ'
    have hsi : 1 ≤ |((σ : ℂ) + Complex.I * t).im| := by
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_mul, zero_add] using ht
    have hb := norm_logDeriv_gammaFactor_le_log χ hsr hsi
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_mul, zero_add] at hb
    have hD : D ≤ A := by
      dsimp only [A]; linarith only [hDM, le_max_right M 0]
    change ‖logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t)‖ ≤ A * _
    dsimp only [D] at hD
    nlinarith only [hb, hD, hA1, hL]
  · have htb : |t| ≤ 1 := (lt_of_not_ge ht).le
    have hm := hM t (abs_le.mp htb)
    have hMA : M ≤ A := by
      dsimp only [A]
      linarith only [le_max_left M 0, abs_nonneg D]
    nlinarith only [hm, hMA, hA1, hL]

/-- The principal character of modulus one is even. Its gamma factor is `Gammaℝ`,
so it supplies a fixed reference function independent of the modulus. -/
theorem principal_modulus_one_even : (1 : DirichletCharacter ℂ 1).Even := by
  rw [DirichletCharacter.Even, Subsingleton.elim (-1 : ZMod 1) 1, map_one]

/-- At a point with positive real part, any character gamma logarithmic derivative equals
the modulus-one reference derivative either at that point or translated by one.
Parity identifies the gamma factors and the translation chain rule has derivative one.
This reduces bounds uniform in characters to two fixed functions. -/
theorem logDeriv_gammaFactor_eq_one_or_one_shift {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) :
    logDeriv χ.gammaFactor s = logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor s ∨
      logDeriv χ.gammaFactor s = logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (s + 1) := by
  classical
  have h1 : (1 : DirichletCharacter ℂ 1).Even := by
    rw [DirichletCharacter.Even, Subsingleton.elim (-1 : ZMod 1) 1, map_one]
  rcases χ.even_or_odd with he | ho
  · left
    have hfun : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
      funext z
      rw [he.gammaFactor_def, h1.gammaFactor_def]
    rw [hfun]
  · right
    have hfun :
      χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor ∘ (fun z : ℂ => z + 1) := by
      funext z
      rw [ho.gammaFactor_def, Function.comp_apply, h1.gammaFactor_def]
    rw [hfun,
      logDeriv_comp (g := fun z : ℂ => z + 1) (x := s)
        (analyticAt_gammaFactor_of_re_pos (1 : DirichletCharacter ℂ 1)
            (by
              simp only [Complex.add_re, Complex.one_re]; linarith only [hs])).differentiableAt
        (differentiableAt_id.add_const 1)]
    simp only [deriv_add_const, deriv_id'', mul_one]

/-- For a fixed positive real part, the gamma logarithmic derivatives of all characters
are uniformly bounded for heights of absolute value at most one. Reduce parity to the
modulus-one gamma factor at two real parts, and use continuity on the compact interval.
This supplies a modulus-independent bound near height zero. -/
theorem exists_uniform_norm_logDeriv_gammaFactor_compact_le {σ : ℝ} (hσ : 0 < σ) :
    ∃ M : ℝ,
      ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (t : ℝ),
        |t| ≤ 1 → ‖logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t)‖ ≤ M := by
  obtain ⟨M0, hb0⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
      (continuous_logDeriv_gammaFactor_vertical (1 : DirichletCharacter ℂ 1) hσ).continuousOn
  obtain ⟨M1, hb1⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
      (continuous_logDeriv_gammaFactor_vertical (1 : DirichletCharacter ℂ 1) (σ := σ + 1)
          (by linarith only [hσ])).continuousOn
  refine ⟨max M0 M1, fun N χ t ht => ?_⟩
  have hs : 0 < ((σ : ℂ) + Complex.I * t).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hσ
  rcases logDeriv_gammaFactor_eq_one_or_one_shift χ hs with he | he
  · rw [he]
    exact (hb0 t (abs_le.mp ht)).trans (le_max_left M0 M1)
  · rw [he]
    have hh : (((σ + 1 : ℝ) : ℂ) + Complex.I * t) = ((σ : ℂ) + Complex.I * t) + 1 := by
      rw [Complex.ofReal_add, Complex.ofReal_one]
      ring
    rw [← hh]
    exact (hb1 t (abs_le.mp ht)).trans (le_max_right M0 M1)

/-- For a fixed real part in (0,2], a positive logarithmic growth constant works for every
modulus and character. Combine the uniform compact-height bound with the gamma strip
estimate outside that interval. This controls both the central Mellin line and reflected
right lines in the primitive functional equation. -/
theorem exists_uniform_norm_logDeriv_gammaFactor_vertical_le_log {σ : ℝ} (hσ : 0 < σ)
    (hσ' : σ ≤ 2) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (t : ℝ),
          ‖logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t)‖ ≤ A * (Real.log (4 + |t|) + 1) := by
  obtain ⟨M, hM⟩ := exists_uniform_norm_logDeriv_gammaFactor_compact_le hσ
  let D : ℝ := ‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound + 4
  let A : ℝ := 1 + |D| + max M 0
  have hA1 : 1 ≤ A := by
    dsimp only [A]; linarith only [abs_nonneg D, le_max_right M 0]
  have hDM : D ≤ |D| := le_abs_self D
  refine ⟨A, zero_lt_one.trans_le hA1, fun N χ t => ?_⟩
  have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  by_cases ht : 1 ≤ |t|
  · have hsr : |((σ : ℂ) + Complex.I * t).re| ≤ 2 := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, abs_of_pos hσ] using hσ'
    have hsi : 1 ≤ |((σ : ℂ) + Complex.I * t).im| := by
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_mul, zero_add] using ht
    have hb := norm_logDeriv_gammaFactor_le_log χ hsr hsi
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_mul, zero_add] at hb
    have hD : D ≤ A := by
      dsimp only [A]; linarith only [hDM, le_max_right M 0]
    change ‖logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t)‖ ≤ A * _
    dsimp only [D] at hD
    nlinarith only [hb, hD, hA1, hL]
  · have htb : |t| ≤ 1 := (lt_of_not_ge ht).le
    have hm := hM N χ t htb
    have hMA : M ≤ A := by
      dsimp only [A]
      linarith only [le_max_left M 0, abs_nonneg D]
    nlinarith only [hm, hMA, hA1, hL]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
