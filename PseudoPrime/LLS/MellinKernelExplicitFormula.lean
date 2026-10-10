/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelResidueSeries
public import PseudoPrime.LLS.MellinKernelArithmeticMellin
public import PseudoPrime.LLS.MellinKernelGammaBounds
public import PseudoPrime.LLS.MellinKernelLeftBounds
public import PseudoPrime.LLS.MellinKernelPoleBounds

/-!
# Exact explicit formula for general Mellin kernels

Separate the completed contour into the arithmetic logarithmic derivative and gamma factor.
The weighted Mangoldt series is expressed using the pole, zero series and vertical integrals.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

open AnalyticNumberTheory.DirichletLFunction in
/-- For a nonprincipal character and a point with real part at least one, the weighted
negative ordinary logarithmic derivative equals its completed counterpart plus the
weighted gamma logarithmic derivative. All factors are nonzero in this half-plane.
This separates the arithmetic contour into completed and archimedean parts. -/
theorem arithmetic_logDeriv_eq_completed_add_gamma {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) (w : ℂ) :
    -logDeriv (DirichletCharacter.LFunction χ) s * w =
      -logDeriv χ.completedLFunction s * w + logDeriv (DirichletCharacter.gammaFactor χ) s * w := by
  have hp : 0 < s.re := zero_lt_one.trans_le hs
  rw [logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hs) (gammaFactor_ne_zero_of_re_pos χ hp)
      (analyticAt_gammaFactor_of_re_pos χ hp).differentiableAt]
  ring

/-- The real Mellin normalization, cast to the complex numbers, cancels the nonzero
factor `2π`. This converts completed contour integrals into normalized arithmetic sums. -/
theorem mellin_normalization_mul_two_pi :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi : ℂ) = 1 := by
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
  exact
    div_mul_cancel₀ _ (mul_ne_zero (by norm_num only) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data, scale at least one, and admissible lines enclosing
the shifted zeros and kernel pole, the smoothed Mangoldt series equals the pole residue
minus the oscillatory zero sum plus the normalized left completed integral and right gamma
integral. The Euler-series formula, completion factorization and infinite contour identity
prove this exact equality. Uniform estimates of its remaining integrals yield Lemma 6.1. -/
theorem tsum_summand_eq_completed_residue_formula (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a < b)
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (ha' : -3 / 2 ≤ a) (hb' : b ≤ 3 / 2)
    (hx : 1 ≤ x) (haleft : a < -1 / 2) (hbright : 1 / 2 < b) :
    let W := fun s : ℂ => K.function s * (x : ℂ) ^ s
    let F := fun s : ℂ => -logDeriv χ.completedLFunction (s + 1 / 2) * W s
    (∑' n : ℕ, K.summand χ x n) =
      weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
          (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F ((a : ℂ) + Complex.I * t)) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv (DirichletCharacter.gammaFactor χ) (((b : ℂ) + Complex.I * t) + 1 / 2) *
              W ((b : ℂ) + Complex.I * t)) := by
  let W := fun s : ℂ => K.function s * (x : ℂ) ^ s
  let F := fun s : ℂ => -logDeriv χ.completedLFunction (s + 1 / 2) * W s
  let G := fun t : ℝ =>
    logDeriv (DirichletCharacter.gammaFactor χ) (((b : ℂ) + Complex.I * t) + 1 / 2) *
      W ((b : ℂ) + Complex.I * t)
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hiF := integrable_completed_right_line K hne hbright hb hb' hxpos
  have hiG : MeasureTheory.Integrable G := by
    simpa only [G, W, mul_assoc] using
      integrable_gammaFactor_power_line K χ (by linarith only [hbright]) hb hb' hxpos
  have he :
    (∫ t : ℝ,
        -logDeriv (DirichletCharacter.LFunction χ) (((b : ℂ) + Complex.I * t) + 1 / 2) *
          W ((b : ℂ) + Complex.I * t)) =
      (∫ t : ℝ, F ((b : ℂ) + Complex.I * t)) + (∫ t : ℝ, G t) := by
    rw [←
      MeasureTheory.integral_add (f := fun t : ℝ => F ((b : ℂ) + Complex.I * t)) (g := G) (μ :=
        MeasureTheory.volume)
        (show MeasureTheory.Integrable (fun t : ℝ => F ((b : ℂ) + Complex.I * t)) from hiF) hiG]
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    apply arithmetic_logDeriv_eq_completed_add_gamma hne
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.div_ofNat_re,
      Complex.one_re]
    linarith only [hbright]
  have hv :=
    completed_vertical_difference_eq_residues K hq hGRH hp hne hinv hab ha hb ha' hb' hx haleft
      hbright
  have hv' :
    (∫ t : ℝ, F ((b : ℂ) + Complex.I * t)) =
      (∫ t : ℝ, F ((a : ℂ) + Complex.I * t)) +
        (2 * Real.pi : ℂ) *
          (weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
            ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) := by
    apply sub_eq_iff_eq_add'.mp
    simpa only [F, W, mul_comm] using hv
  dsimp only
  rw [tsum_summand_eq_integral_logDeriv K χ hxpos hbright hb, he, hv', mul_add, mul_add, ←
    mul_assoc, mellin_normalization_mul_two_pi, one_mul]
  ring

/-- Under primitive nonprincipal GRH data, the arithmetic sum minus the pole residue,
negative oscillatory zero sum and left completed integral has bounded norm. A positive
bound depending only on the kernel works for every modulus, character, scale at least one
and allowed pair of lines. The exact formula identifies this remainder with the right
gamma integral, whose uniform bound is proved. This removes the archimedean error field. -/
theorem exists_norm_summand_completed_remainder_le (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q],
          2 ≤ q →
            ∀ {χ : DirichletCharacter ℂ q},
              AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ {a b x : ℝ},
                  a < b →
                    -1 / 2 - K.delta < a →
                    b ≤ 1 / 2 + K.delta →
                    -3 / 2 ≤ a →
                    b ≤ 3 / 2 →
                    1 ≤ x →
                    a < -1 / 2 →
                    1 / 2 < b →
                    ‖(∑' n : ℕ, K.summand χ x n) -
                          (weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x
                                (-1 / 2) -
                              (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) +
                            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                              (∫ t : ℝ,
                                -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) *
                                  (K.function ((a : ℂ) + Complex.I * t) *
                                    (x : ℂ) ^ ((a : ℂ) + Complex.I * t))))‖ ≤
                      C := by
  obtain ⟨C, hC, hbC⟩ := exists_norm_gammaIntegral_le K
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hGRH hp hne hinv a b x hab ha hb ha' hb' hx hal hbr
  have h :=
    tsum_summand_eq_completed_residue_formula K hq hGRH hp hne hinv hab ha hb ha' hb' hx hal hbr
  dsimp only at h
  rw [h, add_sub_cancel_left]
  exact hbC q χ hx (by linarith only [hbr]) hb hb'

/-- For a fixed allowed left line, primitive nonprincipal GRH data give an arithmetic
Mellin sum equal to the kernel-pole residue minus the oscillatory zero sum up to a remainder
of norm at most C(1 + log q / sqrt x). The positive constant depends only on the kernel
and left line and works for all moduli, characters, scales at least one and allowed right
lines. Combine the exact formula with the uniform gamma and left completed integral
bounds. This removes both vertical integral error inputs from the primitive formula. -/
theorem exists_norm_summand_residue_remainder_le_of_left_line (K : MellinKernel) {a : ℝ}
    (ha : -1 / 2 - K.delta < a) (hal : a < -1 / 2) (ha2 : -3 / 2 ≤ a) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q],
          2 ≤ q →
            ∀ {χ : DirichletCharacter ℂ q},
              AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ {b x : ℝ},
                  b ≤ 1 / 2 + K.delta →
                    b ≤ 3 / 2 →
                    1 ≤ x →
                    1 / 2 < b →
                    ‖(∑' n : ℕ, K.summand χ x n) -
                          (weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x
                              (-1 / 2) -
                            (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ))‖ ≤
                      C * (1 + Real.log q / Real.sqrt x) := by
  obtain ⟨Cg, hCg, hg⟩ := exists_norm_summand_completed_remainder_le K
  obtain ⟨Cl, hCl, hl⟩ := exists_norm_left_completedIntegral_le_log_div_sqrt K ha hal ha2
  refine ⟨Cg + Cl, add_pos hCg hCl, ?_⟩
  intro q _ hq χ hGRH hp hne hinv b x hb hb2 hx hbr
  have hab : a < b := by linarith only [hal, hbr]
  let P :=
    weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
      (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ)
  let L :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t)))
  have hγ : ‖(∑' n : ℕ, K.summand χ x n) - (P + L)‖ ≤ Cg :=
    hg hq hGRH hp hne hinv hab ha hb ha2 hb2 hx hal hbr
  have hleft : ‖L‖ ≤ Cl * Real.log q / Real.sqrt x := hl q χ hq hp hne hinv hx
  have he : (∑' n : ℕ, K.summand χ x n) - P = ((∑' n : ℕ, K.summand χ x n) - (P + L)) + L := by ring
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (by linarith only [hq] : 1 ≤ q)
  have hnonneg : 0 ≤ Real.log q / Real.sqrt x :=
    div_nonneg (Real.log_nonneg hqR) (Real.sqrt_nonneg x)
  change ‖(∑' n : ℕ, K.summand χ x n) - P‖ ≤ _
  rw [he]
  have hn := norm_add_le ((∑' n : ℕ, K.summand χ x n) - (P + L)) L
  have hleft' : ‖L‖ ≤ Cl * (Real.log q / Real.sqrt x) := by simpa only [mul_div_assoc] using hleft
  nlinarith only [hn, hγ, hleft', hnonneg, hCg, hCl]

/-- Every positive kernel strip contains left and right lines suitable for the completed
explicit formula. Choose symmetric offsets equal to the smaller of delta/2 and 1/2.
They avoid the kernel pole and stay within the vertical growth bounds. -/
private theorem exists_admissible_explicitFormula_lines (K : MellinKernel) :
    ∃ a b : ℝ,
      -1 / 2 - K.delta < a ∧
        a < -1 / 2 ∧ -3 / 2 ≤ a ∧ b ≤ 1 / 2 + K.delta ∧ b ≤ 3 / 2 ∧ 1 / 2 < b := by
  let e := min (K.delta / 2) (1 / 2)
  have he : 0 < e := lt_min (half_pos K.delta_pos) (by norm_num only)
  have heδ : e < K.delta :=
    (min_le_left _ _).trans_lt (by linarith only [K.delta_pos] : K.delta / 2 < K.delta)
  have he2 : e ≤ 1 / 2 := min_le_right _ _
  refine ⟨-1 / 2 - e, 1 / 2 + e, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [he, heδ, he2]

/-- Under primitive nonprincipal GRH data, the arithmetic Mellin sum differs from the
kernel-pole residue minus the oscillatory zero sum by at most C(1 + log q / sqrt x) in norm.
A positive constant depending only on the kernel works for all moduli at least two,
characters and scales at least one. Choose allowed lines from the kernel strip and apply
the uniform gamma and conductor error bounds. No contour data are additional inputs.
This is the primitive-character remainder estimate for the general explicit formula. -/
theorem exists_norm_summand_residue_remainder_le (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q],
          2 ≤ q →
            ∀ {χ : DirichletCharacter ℂ q},
              AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ {x : ℝ},
                  1 ≤ x →
                    ‖(∑' n : ℕ, K.summand χ x n) -
                          (weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x
                              (-1 / 2) -
                            (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ))‖ ≤
                      C * (1 + Real.log q / Real.sqrt x) := by
  obtain ⟨a, b, ha, hal, ha2, hb, hb2, hbr⟩ := exists_admissible_explicitFormula_lines K
  obtain ⟨C, hC, hbound⟩ := exists_norm_summand_residue_remainder_le_of_left_line K ha hal ha2
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hGRH hp hne hinv x hx
  exact hbound hq hGRH hp hne hinv hb hb2 hx hbr

/-- For every kernel, primitive nonprincipal GRH data at moduli at least eight give
arithmetic sum plus oscillatory zero sum of norm at most C(1 + log q / sqrt x) for scales
at least one. The positive constant depends only on the kernel. Combine the primitive
explicit formula's remainder with the endpoint bound for the possible kernel pole.
No integral or pole estimates remain as assumptions. This is the primitive-character
input for the real zero-mass representation in Lemma 6.1. -/
theorem exists_norm_summand_add_oscillatingZeroSum_le (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q],
          8 ≤ q →
            ∀ {χ : DirichletCharacter ℂ q},
              AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ {x : ℝ},
                  1 ≤ x →
                    ‖(∑' n : ℕ, K.summand χ x n) + (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ)‖ ≤
                      C * (1 + Real.log q / Real.sqrt x) := by
  obtain ⟨Ca, hCa, ha⟩ := exists_norm_summand_residue_remainder_le K
  obtain ⟨Cp, hCp, hpole⟩ := exists_norm_completed_poleResidue_le_log_div_sqrt K
  refine ⟨Ca + Cp, add_pos hCa hCp, ?_⟩
  intro q _ hq χ hGRH hp hne hinv x hx
  let S := ∑' n : ℕ, K.summand χ x n
  let Z := ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ
  let P := weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x (-1 / 2)
  have harith : ‖S - (P - Z)‖ ≤ Ca * (1 + Real.log q / Real.sqrt x) :=
    ha ((by norm_num only : 2 ≤ 8).trans hq) hGRH hp hne hinv hx
  have hpole' : ‖P‖ ≤ Cp * (Real.log q / Real.sqrt x) := by
    simpa only [mul_div_assoc] using hpole hq hGRH hp hne hx
  have he : S + Z = (S - (P - Z)) + P := by ring
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (by linarith only [hq] : 1 ≤ q)
  have hn : 0 ≤ Real.log q / Real.sqrt x := div_nonneg (Real.log_nonneg hqR) (Real.sqrt_nonneg x)
  change ‖S + Z‖ ≤ _
  rw [he]
  have h := norm_add_le (S - (P - Z)) P
  nlinarith only [h, harith, hpole', hCp, hn]

/-- For primitive nonprincipal GRH data of modulus at least eight, the real arithmetic
Mellin sum equals a real coefficient of absolute value at most one times the actual absolute
kernel zero mass, plus a remainder bounded by C(1 + log q / sqrt x) for scales at least one.
The positive constant depends only on the kernel. Use the oscillatory zero-sum coefficient
and take the real part of the completed primitive formula. This isolates the remaining
sharp comparison between actual zero mass and the kernel's integral mass in Lemma 6.1. -/
theorem exists_real_summand_formula_zeroMass (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q],
          8 ≤ q →
            ∀ {χ : DirichletCharacter ℂ q},
              AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ {x : ℝ},
                  1 ≤ x →
                    ∃ θ r : ℝ,
                      |θ| ≤ 1 ∧
                        |r| ≤ C * (1 + Real.log q / Real.sqrt x) ∧
                        (∑' n : ℕ, K.summand χ x n).re =
                          θ * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) + r := by
  obtain ⟨C, hC, hb⟩ := exists_norm_summand_add_oscillatingZeroSum_le K
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hGRH hp hne hinv x hx
  have hq2 : 2 ≤ q := (by norm_num only : 2 ≤ 8).trans hq
  obtain ⟨θ, hθ, he⟩ := exists_theta_zero_sum K hq2 hGRH hp hne hinv (zero_lt_one.trans_le hx)
  let S := ∑' n : ℕ, K.summand χ x n
  let Z := ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ
  refine ⟨-θ, (S + Z).re, ?_, ?_, ?_⟩
  · simpa only [abs_neg] using hθ
  · exact (Complex.abs_re_le_norm (S + Z)).trans (hb hq hGRH hp hne hinv hx)
  · change S.re = -θ * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) + (S + Z).re
    rw [Complex.add_re, show Z.re = θ * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) from he]
    ring

/-- For primitive nonprincipal GRH data of conductor m between three and an ambient
modulus q at least 20000, the arithmetic sum plus oscillatory zero sum has norm at most
C(1 + log q / sqrt x) for x at least one, with C depending only on the kernel. Enlarge
the contour remainder's conductor logarithm and apply the ambient pole bound. This
prepares the general-character estimate even when the primitive conductor is small. -/
theorem exists_norm_summand_add_oscillatingZeroSum_le_ambient (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q m : ℕ} [NeZero m],
          20000 ≤ q →
            3 ≤ m →
            m ≤ q →
            ∀ {χ : DirichletCharacter ℂ m},
              PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ {x : ℝ},
                  1 ≤ x →
                    ‖(∑' n : ℕ, K.summand χ x n) + (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ)‖ ≤
                      C * (1 + Real.log q / Real.sqrt x) := by
  obtain ⟨Ca, hCa, ha⟩ := exists_norm_summand_residue_remainder_le K
  obtain ⟨Cp, hCp, hpole⟩ := exists_norm_completed_poleResidue_le_ambient_log_div_sqrt K
  refine ⟨Ca + Cp, add_pos hCa hCp, ?_⟩
  intro q m _ hq hm hmq χ hGRH hp hne hinv x hx
  let S := ∑' n : ℕ, K.summand χ x n
  let Z := ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ
  let P := weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x (-1 / 2)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by linarith only [hm] : 0 < m)
  have hmqR : (m : ℝ) ≤ q := by exact_mod_cast hmq
  have hlmq : Real.log m ≤ Real.log q := Real.log_le_log hmpos hmqR
  have harith0 : ‖S - (P - Z)‖ ≤ Ca * (1 + Real.log m / Real.sqrt x) :=
    ha ((by norm_num only : 2 ≤ 3).trans hm) hGRH hp hne hinv hx
  have harith : ‖S - (P - Z)‖ ≤ Ca * (1 + Real.log q / Real.sqrt x) :=
    harith0.trans
      (mul_le_mul_of_nonneg_left
        (add_le_add_right (div_le_div_of_nonneg_right hlmq (Real.sqrt_nonneg x)) 1) hCa.le)
  have hpole' : ‖P‖ ≤ Cp * (Real.log q / Real.sqrt x) := by
    simpa only [mul_div_assoc] using hpole hq hm hmq hGRH hp hne hx
  have he : S + Z = (S - (P - Z)) + P := by ring
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (by linarith only [hq] : 1 ≤ q)
  have hn : 0 ≤ Real.log q / Real.sqrt x := div_nonneg (Real.log_nonneg hqR) (Real.sqrt_nonneg x)
  change ‖S + Z‖ ≤ _
  rw [he]
  have h := norm_add_le (S - (P - Z)) P
  nlinarith only [h, harith, hpole', hCp, hn]

/-- For primitive nonprincipal GRH data of conductor m between three and an ambient
modulus q at least 20000, the real arithmetic sum equals an absolute-zero-mass term with
coefficient of absolute value at most one and a real error bounded by
C(1 + log q / sqrt x) for x at least one. The constant depends only on the kernel.
Take real parts of the ambient completed formula and normalize the oscillatory zero sum.
This supplies the primitive part of Lemma 6.1 after a level change. -/
theorem exists_real_summand_formula_zeroMass_ambient (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q m : ℕ} [NeZero m],
          20000 ≤ q →
            3 ≤ m →
            m ≤ q →
            ∀ {χ : DirichletCharacter ℂ m},
              PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ {x : ℝ},
                  1 ≤ x →
                    ∃ θ r : ℝ,
                      |θ| ≤ 1 ∧
                        |r| ≤ C * (1 + Real.log q / Real.sqrt x) ∧
                        (∑' n : ℕ, K.summand χ x n).re =
                          θ * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) + r := by
  obtain ⟨C, hC, hb⟩ := exists_norm_summand_add_oscillatingZeroSum_le_ambient K
  refine ⟨C, hC, ?_⟩
  intro q m _ hq hm hmq χ hGRH hp hne hinv x hx
  have hm2 : 2 ≤ m := (by norm_num only : 2 ≤ 3).trans hm
  obtain ⟨θ, hθ, he⟩ := exists_theta_zero_sum K hm2 hGRH hp hne hinv (zero_lt_one.trans_le hx)
  let S := ∑' n : ℕ, K.summand χ x n
  let Z := ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ
  refine ⟨-θ, (S + Z).re, ?_, ?_, ?_⟩
  · simpa only [abs_neg] using hθ
  · exact (Complex.abs_re_le_norm (S + Z)).trans (hb hq hm hmq hGRH hp hne hinv hx)
  · change S.re = -θ * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) + (S + Z).re
    rw [Complex.add_re, show Z.re = θ * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) from he]
    ring

end PseudoPrime.LLS.PaperStatements.MellinKernel
