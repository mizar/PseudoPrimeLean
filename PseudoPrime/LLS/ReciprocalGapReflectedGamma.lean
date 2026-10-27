/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapReflectedDigamma

/-! # Signed real-axis evaluation of the adjustable left contour and witness separation -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.DirichletLFunction in
/-- For any character, a fixed real parity shift between zero and one half expresses its
Gamma logarithmic derivative through digamma at every point of positive real part.
Split character parity and exclude Gamma poles using positivity.
This keeps one common affine representation on the reflected line and the real axis. -/
theorem gammaFactor_logDeriv_eq_affine_digamma {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∃ κ : ℝ,
      0 ≤ κ ∧
        κ ≤ 1 / 2 ∧
        ∀ {s : ℂ},
          0 < s.re →
            logDeriv χ.gammaFactor s =
              (-Complex.log Real.pi + Complex.digamma (s / 2 + (κ : ℂ))) / 2 := by
  rcases χ.even_or_odd with he | ho
  · refine ⟨0, le_refl _, by norm_num only, ?_⟩
    intro s hs
    have hp : 0 < (s / 2).re := by
      rw [complex_div_two_re]; linarith only [hs]
    rw [logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat he
        (fun n ↦ AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n)]
    simp only [Complex.ofReal_zero, add_zero]
    ring
  · refine ⟨1 / 2, by norm_num only, le_refl _, ?_⟩
    intro s hs
    have hp : 0 < ((s + 1) / 2).re := by
      rw [complex_div_two_re, Complex.add_re, Complex.one_re]
      linarith only [hs]
    rw [logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat ho
        (fun n ↦ AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n)]
    have hz : (s + 1) / 2 = s / 2 + ((1 / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hz]
    ring

/-- For positive gap and a line left of -1/2, choose a positive reflected digamma base.
The same parity shift represents the whole reflected Gamma line and its value at 1+h.
Normalize the affine arguments. This is the scalar interface for exact Gamma integration. -/
theorem reciprocalGap_reflected_gammaFactor_data {q : ℕ} (χ : DirichletCharacter ℂ q) {h c : ℝ}
    (hh : 0 < h) (hcu : c < -1 / 2) :
    ∃ b : ℝ,
      0 < b ∧
        (∀ t : ℝ,
          logDeriv χ.gammaFactor (1 / 2 - ((c : ℂ) + Complex.I * t)) =
            (-Complex.log Real.pi + Complex.digamma ((b : ℂ) - Complex.I * (t / 2))) / 2) ∧
        logDeriv χ.gammaFactor ((1 + h : ℝ) : ℂ) =
          (-Complex.log Real.pi + Complex.digamma ((b + (c + (1 / 2 + h)) / 2 : ℝ) : ℂ)) / 2 := by
  obtain ⟨κ, hk, _, he⟩ := gammaFactor_logDeriv_eq_affine_digamma χ
  let b := 1 / 4 - c / 2 + κ
  refine
    ⟨b, by
      dsimp only [b]; linarith only [hk, hcu], ?_, ?_⟩
  · intro t
    have hp : 0 < (1 / 2 - ((c : ℂ) + Complex.I * t)).re := by
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul,
        mul_zero, sub_zero, add_zero]
      linarith only [hcu]
    rw [he hp]
    congr 2
    dsimp only [b]
    push_cast
    congr 1
    ring
  · rw [he
        (by
          rw [Complex.ofReal_re]; linarith only [hh])]
    congr 2
    dsimp only [b]
    push_cast
    congr 1
    ring

/-- For any character, a line between the poles and positive scale, the weighted reflected
Gamma logarithmic derivative is integrable. Split the affine digamma representation into
an integrable constant and the integrable full digamma weight.
This discharges convergence before integrating the completed reflected derivative. -/
theorem integrable_reciprocalGap_reflected_gammaFactor {q : ℕ} (χ : DirichletCharacter ℂ q)
    {h c x : ℝ} (hcl : -1 / 2 - h < c) (hcu : c < -1 / 2) (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        logDeriv χ.gammaFactor (1 / 2 - ((c : ℂ) + Complex.I * t)) *
          reciprocalGapMiddleWeight h c x t) := by
  obtain ⟨b, hb, he, _⟩ :=
    reciprocalGap_reflected_gammaFactor_data χ (by linarith only [hcl, hcu]) hcu
  have hW := integrable_reciprocalGapMiddleWeight hcl hcu hx
  have hD := integrable_reciprocalGap_reflected_digamma hcl hcu hx hb
  exact
    ((hW.const_mul (-Complex.log Real.pi / 2)).add (hD.const_mul (1 / 2 : ℂ))).congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          change
            (-Complex.log Real.pi / 2) * reciprocalGapMiddleWeight h c x t +
                (1 / 2 : ℂ) *
                  (Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) *
                    reciprocalGapMiddleWeight h c x t) =
              logDeriv χ.gammaFactor (1 / 2 - ((c : ℂ) + Complex.I * t)) *
                reciprocalGapMiddleWeight h c x t
          rw [he]
          ring))

/-- For any character, positive gap, a line between the poles and x>=1, the normalized
reflected Gamma integral equals -x^(-1/2-h)/h times its Gamma logarithmic derivative
at 1+h. Apply exact digamma inversion and restore the constant log(pi) term.
No GRH or character nontriviality is required. -/
theorem reciprocalGap_reflected_gammaFactor_integral {q : ℕ} (χ : DirichletCharacter ℂ q)
    {h c x : ℝ} (hh : 0 < h) (hcl : -1 / 2 - h < c) (hcu : c < -1 / 2) (hx : 1 ≤ x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor (1 / 2 - ((c : ℂ) + Complex.I * t)) *
            reciprocalGapMiddleWeight h c x t) =
      ((-x ^ (-1 / 2 - h) / h : ℝ) : ℂ) * logDeriv χ.gammaFactor ((1 + h : ℝ) : ℂ) := by
  obtain ⟨b, hb, he, hf⟩ := reciprocalGap_reflected_gammaFactor_data χ hh hcu
  let W := reciprocalGapMiddleWeight h c x
  have hx0 := zero_lt_one.trans_le hx
  have hW := integrable_reciprocalGapMiddleWeight hcl hcu hx0
  have hD := integrable_reciprocalGap_reflected_digamma hcl hcu hx0 hb
  have ht (t : ℝ) :
    logDeriv χ.gammaFactor (1 / 2 - ((c : ℂ) + Complex.I * t)) * W t =
      (-Complex.log Real.pi / 2) * W t +
        (1 / 2 : ℂ) * (Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) * W t) := by
    rw [he]
    ring
  have hM := reciprocalGap_left_kernel_integral hh hcl hcu hx
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, W t) = _ at hM
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, logDeriv χ.gammaFactor (1 / 2 - ((c : ℂ) + Complex.I * t)) * W t) =
      _
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ ht),
    MeasureTheory.integral_add (hW.const_mul _) (hD.const_mul _), mul_add,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    mul_left_comm _ (-Complex.log Real.pi / 2), hM, mul_left_comm _ (1 / 2 : ℂ),
    reciprocalGap_reflected_digamma_integral hh hcl hcu hx hb, hf]
  ring

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal data with nonprincipal inverse, positive gap and x>=1,
the actual reflected completed integral equals -x^(-1/2-h)/h times the inverse
character's completed logarithmic derivative at 1+h. Split the integrable ordinary and
Gamma terms, evaluate them exactly and recombine. No GRH is required. -/
theorem reciprocalGap_reflectedIntegral_eq_realAxis {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    reciprocalGapReflectedIntegral h hh χ x =
      ((-x ^ (-1 / 2 - h) / h : ℝ) : ℂ) * logDeriv χ⁻¹.completedLFunction ((1 + h : ℝ) : ℂ) := by
  let K := reciprocalGapMellinKernel h hh
  let c := -1 / 2 - K.delta / 2
  let W := reciprocalGapMiddleWeight h c x
  have hd := K.delta_pos
  have hδ : K.delta ≤ h / 4 := min_le_left _ _
  have hcu : c < -1 / 2 := by
    dsimp only [c]; linarith only [hd]
  have hcl : -1 / 2 - h < c := by
    dsimp only [c]; linarith only [hδ, hh]
  have hx0 := zero_lt_one.trans_le hx
  have he {s : ℂ} (hs : 1 ≤ s.re) :
    logDeriv χ⁻¹.completedLFunction s = logDeriv χ⁻¹.LFunction s + logDeriv χ⁻¹.gammaFactor s := by
    have hs0 : 0 < s.re := zero_lt_one.trans_le hs
    have hf :=
      logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hinv
        (completedLFunction_ne_zero_of_one_le_re hinv hs) (gammaFactor_ne_zero_of_re_pos χ⁻¹ hs0)
        (analyticAt_gammaFactor_of_re_pos χ⁻¹ hs0).differentiableAt
    rw [hf]
    ring
  have hr (t : ℝ) : 1 ≤ (1 / 2 - ((c : ℂ) + Complex.I * t)).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul,
      mul_zero, sub_zero, add_zero]
    linarith only [hcu]
  have hiC := integrable_reciprocalGap_reflected_line hh hp hne hinv hx0
  change
    MeasureTheory.Integrable
      (fun t : ℝ ↦ logDeriv χ⁻¹.completedLFunction (1 / 2 - ((c : ℂ) + Complex.I * t)) * W t) at hiC
  have hiG := integrable_reciprocalGap_reflected_gammaFactor χ⁻¹ hcl hcu hx0
  have hiL :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ logDeriv χ⁻¹.LFunction (1 / 2 - ((c : ℂ) + Complex.I * t)) * W t) :=
    (hiC.sub hiG).congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          change
            logDeriv χ⁻¹.completedLFunction (1 / 2 - ((c : ℂ) + Complex.I * t)) * W t -
                logDeriv χ⁻¹.gammaFactor (1 / 2 - ((c : ℂ) + Complex.I * t)) * W t =
              _
          rw [he (hr t)]
          ring))
  have ht (t : ℝ) :
    logDeriv χ⁻¹.completedLFunction (1 / 2 - ((c : ℂ) + Complex.I * t)) * W t =
      logDeriv χ⁻¹.LFunction (1 / 2 - ((c : ℂ) + Complex.I * t)) * W t +
        logDeriv χ⁻¹.gammaFactor (1 / 2 - ((c : ℂ) + Complex.I * t)) * W t := by
    rw [he (hr t), add_mul]
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, logDeriv χ⁻¹.completedLFunction (1 / 2 - ((c : ℂ) + Complex.I * t)) * W t) =
      _
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ ht),
    MeasureTheory.integral_add hiL hiG, mul_add]
  have hE := reflected_logDeriv_integral χ⁻¹ hh hcl hcu hx
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, logDeriv χ⁻¹.LFunction (1 / 2 - ((c : ℂ) + Complex.I * t)) * W t) =
      _ at hE
  rw [hE, reciprocalGap_reflected_gammaFactor_integral χ⁻¹ hh hcl hcu hx,
    he
      (by
        rw [Complex.ofReal_re]; linarith only [hh])]
  ring

/-- For primitive nonprincipal data with nonprincipal inverse, positive gap and x>=1,
the actual left integral equals -x^(-1/2-h)/h times log(q) plus the inverse character's
completed logarithmic derivative at 1+h. Retain the signed conductor term and use the
exact reflected integral. This removes the near-contour-distance loss without GRH. -/
theorem reciprocalGap_leftIntegral_eq_realAxis {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    reciprocalGapLeftIntegral h hh χ x =
      ((-x ^ (-1 / 2 - h) / h : ℝ) : ℂ) *
        (Complex.log q + logDeriv χ⁻¹.completedLFunction ((1 + h : ℝ) : ℂ)) := by
  rw [reciprocalGap_leftIntegral_eq_conductor_add_reflected hh hp hne hinv hx,
    reciprocalGap_reflectedIntegral_eq_realAxis hh hp hne hinv hx, ← Complex.natCast_log]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- The real signed value of the adjustable left integral after reflection, expressed
through log(q) and the inverse character's completed logarithmic derivative at 1+h.
Inputs are a nonzero modulus, character, gap and scale, with totalized real operations.
Later theorems require primitivity, nontriviality, positive gap and scale at least one. -/
noncomputable def reciprocalGapRealAxisLeftValue {q : ℕ} [NeZero q] (h : ℝ)
    (χ : DirichletCharacter ℂ q) (x : ℝ) : ℝ :=
  (-x ^ (-1 / 2 - h) / h) * (Real.log q + (logDeriv χ⁻¹.completedLFunction ((1 + h : ℝ) : ℂ)).re)

/-- For primitive nonprincipal data with nonprincipal inverse, positive gap and x>=1,
the real part of the actual left integral is the signed real-axis value.
Take real parts of the exact complex formula. This replaces a norm budget in separation. -/
theorem reciprocalGap_leftIntegral_re_eq_realAxis {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    (reciprocalGapLeftIntegral h hh χ x).re = reciprocalGapRealAxisLeftValue h χ x := by
  rw [reciprocalGap_leftIntegral_eq_realAxis hh hp hne hinv hx, ← Complex.natCast_log]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re]
  rfl

/-- For primitive nonprincipal GRH data with nonprincipal inverse, q>=8, h>0 and x>=1,
bound the completed remainder by the existing pole bound, exact signed left value and
signed Gamma budget. Preserve the actual left integral's real part instead of taking its
norm. This carries the reflection improvement into the witness remainder. -/
theorem reciprocalGap_remainder_re_le_realAxis_budget {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    (hq : 8 ≤ q) {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (reciprocalGapCompletedRemainder h hh χ x).re ≤
      ((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) + reciprocalGapRealAxisLeftValue h χ x +
        reciprocalGapSignedGammaBudget h x := by
  let P :=
    MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
      (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)
  have hΓ := reciprocalGap_remainder_gamma_re_le_signed_budget hh hx χ
  have hP :=
    (Complex.re_le_norm P).trans
      (reciprocalGap_poleResidue_norm_le hh hq hp hne hGRH (zero_lt_one.trans_le hx))
  simp only [Complex.sub_re] at hΓ
  rw [reciprocalGap_leftIntegral_re_eq_realAxis hh hp hne hinv hx] at hΓ
  dsimp only [P] at hP
  linarith only [hΓ, hP]

/-- For primitive nonprincipal GRH data at level at least eight, positive gap, admissible
zero-test coordinate and scale at least one, separation with the exact signed left value
produces a prime non-one witness below the scale. Combine the existing zero-prefix test
and pole/Gamma bounds with the new real-axis remainder estimate.
A concrete uniform coefficient or starting point is not assumed to have been improved. -/
theorem exists_prime_not_one_of_reciprocalGap_realAxis_separation {h c : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] (hq : 8 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ}
    (hx : 1 ≤ x) (B : Finset ℕ)
    (hgap :
      (1 / c) *
            (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
                (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
              ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) +
          (((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) +
            reciprocalGapRealAxisLeftValue h χ x +
            reciprocalGapSignedGammaBudget h x) <
        (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  apply
    exists_prime_not_one_of_reciprocalGap_separation hh ((by norm_num only : 2 ≤ 8).trans hq) hGRH
      hp hne hinv hc hbound hx B
  have hr := reciprocalGap_remainder_re_le_realAxis_budget hh hq hp hne hinv hGRH hx
  exact (add_le_add (le_refl _) hr).trans_lt hgap

end PseudoPrime.LLS.PaperStatements
