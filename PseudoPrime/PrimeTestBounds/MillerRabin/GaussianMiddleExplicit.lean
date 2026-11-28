/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleContour
public import PseudoPrime.LLS.PaperStatements.ShiftedPoleExplicitFormula
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleContour
import PseudoPrime.LLS.PaperStatements.ReciprocalGapReflectedDigamma
import PseudoPrime.LLS.PaperStatements.MellinKernelVerticalIntegrability

/-! # Signed explicit formula for the middle Gaussian profiles -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The shifted Mellin weight at a logarithmic cutoff, in exponential form. -/
private theorem middle_exp_cpow (x : ℝ) (s : ℂ) :
    (Real.exp x : ℂ) ^ s = Complex.exp (s * (x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'), ←
    Complex.ofReal_log (Real.exp_nonneg x), Real.log_exp, mul_comm]

/-- The normalized physical Mangoldt sum equals the signed oscillating zero sum
and the two contour integrals on the common lines at plus and minus nine sixteenths.
A pole rate of at least one makes the common contour width one eighth. -/
public theorem middle_pole_signed_contours (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a b x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) (κ : ℝ) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 1).trans_le ha
    let K := fun i : ℕ ↦ LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha'
    let S := Finset.Ico 3 (N + 1)
    let c := fun i ↦ ((Q ^ 2).coeff (N - i) : ℂ)
    let W := fun s : ℂ ↦ (∑ i ∈ S, c i * (K i).function s) * Complex.exp (s * (x : ℂ))
    let B := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let w := middlePrincipalWeight B (κ * Real.exp (-a * (x + b))) (x + b) (a - 1 / 2)
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑ n ∈ Finset.Ioc 0 ⌊Real.exp (x + b)⌋₊,
        ((ArithmeticFunction.vonMangoldt n * w n : ℝ) : ℂ) * χ n) =
      (κ : ℂ) *
        (-(∑' γ : ℂ, ∑ i ∈ S, c i * (K i).oscillatingZeroTerm χ (Real.exp x) γ) +
          D * (∫ v : ℝ, -logDeriv χ.completedLFunction (l v + 1 / 2) * W (l v)) +
          D * (∫ v : ℝ, logDeriv Complex.Gammaℝ (r v + 1 / 2) * W (r v))) := by
  intro ha' K S c W B w l r D
  have hX : 1 ≤ Real.exp x := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hx
  have h :=
    LLS.PaperStatements.shiftedPole_polynomial_contours S (fun i ↦ max 1 i) c
      (fun _ ↦ le_max_left _ _) (b := b) ha' hX hq hGRH hp hne hinv
  have hd : min ((a - 1 / 2) / 4) (1 / 8) = 1 / 8 := min_eq_right (by linarith only [ha])
  dsimp only at h
  rw [hd] at h
  have hL : (-1 / 2 - (1 / 8) / 2 : ℝ) = -9 / 16 := by norm_num only
  have hR : (1 / 2 + (1 / 8) / 2 : ℝ) = 9 / 16 := by norm_num only
  rw [hL, hR] at h
  simp only [LLS.PaperStatements.shiftedPole_weightedResidue_zero, mul_zero, Finset.sum_const_zero,
    zero_sub] at h
  rw [← middle_pole_forward_sum Q hQ ha' κ χ]
  rw [LLS.PaperStatements.shiftedPole_summand_tsum _ _ _ (fun _ ↦ le_max_left _ _) ha'
      (Real.exp_pos x) χ]
  dsimp only [W, K, S, c, l, r, D] at h ⊢
  have hfactor (g s : ℂ) :
    (∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (g *
            ((LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha').function
                s *
              (Real.exp x : ℂ) ^ s))) =
      g *
        ((∑ i ∈ Finset.Ico 3 (N + 1),
            ((Q ^ 2).coeff (N - i) : ℂ) *
              (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha').function
                s) *
          Complex.exp (s * (x : ℂ))) := by
    rw [Finset.sum_mul, Finset.mul_sum, middle_exp_cpow]
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl
  simp only [hfactor] at h
  have hg : χ.gammaFactor = Complex.Gammaℝ := funext heven.gammaFactor_def
  rw [hg] at h
  exact congrArg ((κ : ℂ) * ·) h

/-- Reflect the completed logarithmic derivative on the left line, separating
the conductor, ordinary Euler logarithmic derivative and the even Gamma factor. -/
public theorem middle_left_log_reflect {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ = χ) (heven : χ.Even) (s : ℂ)
    (hs : s.re < -1 / 2) :
    -logDeriv χ.completedLFunction (s + 1 / 2) =
      Complex.log q + logDeriv χ.LFunction (1 / 2 - s) + logDeriv Complex.Gammaℝ (1 / 2 - s) := by
  have hr : 1 ≤ (1 / 2 - s).re := by
    rw [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith only [hs]
  have hpos := zero_lt_one.trans_le hr
  have hn := AnalyticNumberTheory.DirichletLFunction.completed_ne_zero_of_one_le_re hne hr
  have he :=
    AnalyticNumberTheory.DirichletLFunction.completedLogDeriv_functionalEq hp hne (s := 1 / 2 - s)
      (show χ⁻¹.completedLFunction (1 / 2 - s) ≠ 0 from hinv.symm ▸ hn)
  have hz : (1 : ℂ) - (1 / 2 - s) = s + 1 / 2 := by ring
  rw [hz, hinv] at he
  have hdiff := AnalyticNumberTheory.DirichletLFunction.analyticAt_gammaFactor_of_re_pos χ hpos
  have h :=
    AnalyticNumberTheory.DirichletLFunction.L_logDeriv_sub_gamma_of_regular hne hn
      (AnalyticNumberTheory.DirichletLFunction.gammaFactor_ne_zero_of_re_pos χ hpos)
      hdiff.differentiableAt
  have hg : χ.gammaFactor = Complex.Gammaℝ := funext heven.gammaFactor_def
  rw [hg] at h
  rw [he, h]
  ring

/-- On the reflected Gamma line, an integrable quadratic-decay weight makes
the digamma term integrable, including its constant part. -/
private theorem middle_left_gamma_integrable (W : ℝ → ℂ) (hW : Continuous W)
    (hiW : MeasureTheory.Integrable W) {A : ℝ} (hA : ∀ t, ‖W t‖ ≤ A / (1 + t ^ 2)) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        logDeriv Complex.Gammaℝ (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) * W t) := by
  let β : ℝ := 17 / 32
  let e := fun t : ℝ ↦ Complex.digamma ((β : ℂ) - Complex.I * (t / 2)) - Complex.digamma (β : ℂ)
  let B := (Complex.digamma (β : ℂ) - Complex.log (Real.pi : ℂ)) / 2
  have hb : 0 < β := by norm_num only [β]
  have he (t : ℝ) :
    (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) / 2 =
      (β : ℂ) - Complex.I * (((t / 2 : ℝ) : ℂ)) := by
    simp only [β, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring
  have hg (t : ℝ) :
    logDeriv Complex.Gammaℝ (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) = B + e t / 2 := by
    have hp : 0 < ((1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) / 2).re := by
      rw [he]
      simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using hb
    rw [AnalyticNumberTheory.DirichletLFunction.logDeriv_Gammaℝ_of_half_ne_neg_nat
        (AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp),
      he]
    simp only [B, e, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have hi := LLS.PaperStatements.integrable_quadratic_reflected_digamma hb W hW hA
  simp only [hg, add_mul, div_eq_mul_inv (e _) 2, mul_comm (e _) ((2 : ℂ)⁻¹), mul_assoc]
  exact (hiW.const_mul B).add (hi.const_mul ((2 : ℂ)⁻¹))

/-- Split the actual left contour into conductor, ordinary Euler, and Gamma
integrals. The three integrands are integrable for the middle pole weight. -/
public theorem middle_left_integral_split (Q : Polynomial ℚ) (N : ℕ) {a : ℝ} (ha : 1 ≤ a) (b x : ℝ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ = χ) (heven : χ.Even) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 1).trans_le ha
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let F := fun s ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha').function s
    let W := fun t : ℝ ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    (∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W t) =
      (∫ t : ℝ, Complex.log q * W t) + (∫ t : ℝ, logDeriv χ.LFunction (1 / 2 - l t) * W t) +
        (∫ t : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l t) * W t) := by
  intro ha' l F W
  have hc : 0 < (-9 / 16 : ℝ) + a := by linarith only [ha]
  obtain ⟨hW, hiW⟩ := middle_pole_weight_regular Q N ha' hc b x
  obtain ⟨A, hA⟩ :=
    middle_pole_weight_quadratic Q N ha' ha (c := -9 / 16) (by norm_num only) (by norm_num only)
      (by norm_num only) b x
  change Continuous W at hW
  change MeasureTheory.Integrable W at hiW
  change ∀ t, ‖W t‖ ≤ A / (1 + t ^ 2) at hA
  have hg := middle_left_gamma_integrable W hW hiW hA
  change MeasureTheory.Integrable (fun t ↦ logDeriv Complex.Gammaℝ (1 / 2 - l t) * W t) at hg
  let K := fun i : ℕ ↦ LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha'
  let D := fun t : ℝ ↦ -logDeriv χ.completedLFunction (l t + 1 / 2)
  have hi (i : ℕ) :
    MeasureTheory.Integrable
      (fun t ↦ D t * ((K i).function (l t) * Complex.exp (l t * (x : ℂ)))) := by
    have hd : (K i).delta = 1 / 8 := by
      dsimp only [K]
      rw [LLS.PaperStatements.shiftedPoleKernel_delta, min_eq_right (by linarith only [ha])]
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_completed_left_line (K i) hp hne (hinv.symm ▸ hne)
        (c := -9 / 16)
        (by
          rw [hd]; norm_num only)
        (by norm_num only) (by norm_num only) (Real.exp_pos x)
    simpa only [D, l, middle_exp_cpow] using h
  have hD : MeasureTheory.Integrable (fun t ↦ D t * W t) := by
    refine
      (MeasureTheory.integrable_finsetSum (Finset.Ico 3 (N + 1))
            (fun i _ ↦ (hi i).const_mul (((Q ^ 2).coeff (N - i) : ℂ)))).congr
        ?_
    refine Filter.Eventually.of_forall fun t ↦ ?_
    dsimp only [W, F, K]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl
  have href (t : ℝ) :=
    middle_left_log_reflect hp hne hinv heven (l t)
      (by
        norm_num only [l, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero])
  have hcond := hiW.const_mul (Complex.log q)
  have heul : MeasureTheory.Integrable (fun t ↦ logDeriv χ.LFunction (1 / 2 - l t) * W t) := by
    refine ((hD.sub hcond).sub hg).congr (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [Pi.sub_apply, D, href, add_mul]
    ring
  calc
    _ =
        ∫ t : ℝ,
          (Complex.log q * W t + logDeriv χ.LFunction (1 / 2 - l t) * W t) +
            logDeriv Complex.Gammaℝ (1 / 2 - l t) * W t :=
      by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun t ↦ by simp only [href, add_mul]
    _ = _ := by
      have h := MeasureTheory.integral_add (hcond.add heul) hg
      simp only [Pi.add_apply] at h
      rw [h, MeasureTheory.integral_add hcond heul]

/-- The physical forward sum for an even self-dual character equals the zero
term and the split contour integrals. These are the conductor, reflected Euler
and two Gamma contributions used in the middle residual. -/
public theorem middle_pole_explicit_split (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a b x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) (κ : ℝ) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ = χ) (heven : χ.Even) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 1).trans_le ha
    let K := fun i : ℕ ↦ LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha'
    let S := Finset.Ico 3 (N + 1)
    let c := fun i ↦ ((Q ^ 2).coeff (N - i) : ℂ)
    let W := fun s : ℂ ↦ (∑ i ∈ S, c i * (K i).function s) * Complex.exp (s * (x : ℂ))
    let B := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let w := middlePrincipalWeight B (κ * Real.exp (-a * (x + b))) (x + b) (a - 1 / 2)
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑ n ∈ Finset.Ioc 0 ⌊Real.exp (x + b)⌋₊,
        ((ArithmeticFunction.vonMangoldt n * w n : ℝ) : ℂ) * χ n) =
      (κ : ℂ) *
        (-(∑' γ : ℂ, ∑ i ∈ S, c i * (K i).oscillatingZeroTerm χ (Real.exp x) γ) +
          D *
            ((∫ v : ℝ, Complex.log q * W (l v)) +
              (∫ v : ℝ, logDeriv χ.LFunction (1 / 2 - l v) * W (l v)) +
              (∫ v : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l v) * W (l v))) +
          D * (∫ v : ℝ, logDeriv Complex.Gammaℝ (r v + 1 / 2) * W (r v))) := by
  intro ha' K S c W B w l r D
  have h := middle_pole_signed_contours Q hQ (b := b) ha hx κ hq hGRH hp hne (hinv.symm ▸ hne) heven
  have hsplit := middle_left_integral_split Q N ha b x hp hne hinv heven
  dsimp only [K, S, c, W, B, w, l, r, D] at h hsplit ⊢
  rw [← hsplit]
  exact h

/-- Evaluate the conductor and reflected Euler integrals in the signed
formula. The remaining real terms are the weighted zero sum and Gamma budget. -/
public theorem middle_explicit_euler_real (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a b x : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (κ : ℝ) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ = χ) (heven : χ.Even) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 1).trans_le ha
    let K := fun i : ℕ ↦ LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha'
    let S := Finset.Ico 3 (N + 1)
    let c := fun i ↦ ((Q ^ 2).coeff (N - i) : ℂ)
    let W := fun s : ℂ ↦ (∑ i ∈ S, c i * (K i).function s) * Complex.exp (s * (x : ℂ))
    let B := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let w := middlePrincipalWeight B (κ * Real.exp (-a * (x + b))) (x + b) (a - 1 / 2)
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑ n ∈ Finset.Ioc 0 ⌊Real.exp (x + b)⌋₊, ArithmeticFunction.vonMangoldt n * ((χ n).re * w n)) +
        middleReflectedSum B (fun n ↦ (χ n).re) κ a b x =
      -((κ : ℂ) * (∑' γ : ℂ, ∑ i ∈ S, c i * (K i).oscillatingZeroTerm χ (Real.exp x) γ)).re +
        Real.log q * (κ * Real.exp (-a * (x + b))) * B.eval (x + b) +
        κ *
          ((D * (∫ v : ℝ, logDeriv Complex.Gammaℝ (r v + 1 / 2) * W (r v))).re +
            (D * (∫ v : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l v) * W (l v))).re) := by
  intro ha' K S c W B w l r D
  have ha₀ : 9 / 16 < a := (by norm_num only : (9 / 16 : ℝ) < 1).trans_le ha
  have h :=
    congrArg Complex.re (middle_pole_explicit_split Q hQ (b := b) ha hx κ hq hGRH hp hne hinv heven)
  have hc := middle_pole_conductor_integral Q hQ ha₀ hb hx κ (Real.log q)
  have he := middle_pole_reflected_integral Q hQ ha₀ hb hx κ χ
  have hline (t : ℝ) : ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ) = 1 / 2 - l t := by
    simp only [l, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring
  dsimp only [K, S, c, W, B, w, l, r, D] at h hc he ⊢
  dsimp only [l] at hline
  simp only [middle_exp_cpow, Polynomial.eval₂_eq_eval_map] at hc
  simp only [hline, middle_exp_cpow, neg_mul, MeasureTheory.integral_neg, mul_neg,
    Complex.neg_re] at he
  simp only [← Complex.natCast_log, mul_add, Complex.add_re, mul_neg, Complex.neg_re] at h
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hc he ⊢
  simp only [mul_assoc, mul_comm (middlePrincipalWeight _ _ _ _ _) ((χ _).re)] at h
  rw [← mul_add (-a) x b] at h
  change
    (∑ n ∈ Finset.Ioc 0 ⌊Real.exp (x + b)⌋₊, ArithmeticFunction.vonMangoldt n * ((χ n).re * w n)) +
        _ =
      _
  change
    (∑ n ∈ Finset.Ioc 0 ⌊Real.exp (x + b)⌋₊, ArithmeticFunction.vonMangoldt n * ((χ n).re * w n)) =
      _ at h
  generalize
    (∑ n ∈ Finset.Ioc 0 ⌊Real.exp (x + b)⌋₊, ArithmeticFunction.vonMangoldt n * ((χ n).re * w n)) =
    E at h ⊢
  linear_combination h + hc - he

/-- The reflected Euler series for the sum of three bounded traces equals the
sum of the individual series. Absolute convergence justifies the grouping. -/
public theorem middle_reflected_add_three (B : Polynomial ℝ) (τ₁ τ₂ τ₃ : ℕ → ℝ)
    (h₁ : ∀ n, |τ₁ n| ≤ 3) (h₂ : ∀ n, |τ₂ n| ≤ 3) (h₃ : ∀ n, |τ₃ n| ≤ 3) {κ a b x : ℝ}
    (ha : 1 / 2 < a) :
    middleReflectedSum B (fun n ↦ τ₁ n + τ₂ n + τ₃ n) κ a b x =
      middleReflectedSum B τ₁ κ a b x + middleReflectedSum B τ₂ κ a b x +
        middleReflectedSum B τ₃ κ a b x := by
  have hσ : 1 < a + 1 / 2 := by linarith only [ha]
  have hs₁ := summable_reflected_log_poly τ₁ h₁ B hσ (x + b)
  have hs₂ := summable_reflected_log_poly τ₂ h₂ B hσ (x + b)
  have hs₃ := summable_reflected_log_poly τ₃ h₃ B hσ (x + b)
  simp only [middleReflectedSum, mul_add, add_mul]
  rw [(hs₁.add hs₂).tsum_add hs₃, hs₁.tsum_add hs₂]
  simp only [mul_add]

end PseudoPrime.PrimeTestBounds.MillerRabin
