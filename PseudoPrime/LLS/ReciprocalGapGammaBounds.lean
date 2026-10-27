/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapKernelComparison

/-! # Gap-uniform Gamma errors and separated reciprocal contour costs -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For every nonnegative gap, the central kernel norm is at most 4/(1+t^2).
Use the two-pole resolvent bound with width one half and compare denominators.
This majorant is uniform as the positive gap approaches zero. -/
theorem reciprocalGap_central_norm_le {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    ‖Analysis.reciprocalGapFunction h (Complex.I * t)‖ ≤ 4 / (1 + t ^ 2) := by
  have hr :=
    Analysis.reciprocalGapFunction_norm_le_resolvent (h := h) (t := t) (c := 1 / 2)
      (by norm_num only) (by nlinarith only [hh])
  have hd : 0 < (1 / 2 : ℝ) ^ 2 + t ^ 2 := by nlinarith only [sq_nonneg t]
  have hd' : 0 < 1 + t ^ 2 := by linarith only [sq_nonneg t]
  apply hr.trans
  rw [div_le_div_iff₀ hd hd']
  nlinarith only [sq_nonneg t]

/-- One positive constant bounds all central gamma integrals for every positive gap,
all characters and levels, and every positive scale. Integrate the common logarithmic
Gamma-factor majorant against the gap-independent inverse-square kernel majorant.
This keeps the archimedean error uniform when optimizing the gap. -/
theorem exists_uniform_reciprocalGap_central_gamma_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (h : ℝ),
          0 < h →
            ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) {x : ℝ},
              0 < x →
                ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
                      (∫ t : ℝ,
                        logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                          (Analysis.reciprocalGapFunction h (Complex.I * t) *
                            (x : ℂ) ^ (Complex.I * t)))‖ ≤
                  C := by
  obtain ⟨A, hA, hbA⟩ :=
    AnalyticNumberTheory.DirichletLFunction.exists_uniform_norm_logDeriv_gammaFactor_vertical_le_log
      (σ := 1 / 2) (by norm_num only) (by norm_num only)
  let H := fun t : ℝ ↦ (Real.log (4 + |t|) + 1) / (1 + t ^ 2)
  let D := (A * 4) * (∫ t : ℝ, H t)
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  refine ⟨1 + ‖d‖ * max D 0, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (norm_nonneg _) (le_max_right _ _))
  · intro h hh q χ x hx
    let K := reciprocalGapMellinKernel h hh
    let F := fun t : ℝ ↦
      logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
        (Analysis.reciprocalGapFunction h (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))
    have hiF : MeasureTheory.Integrable F := by
      have hc' : (0 : ℝ) ≤ 1 / 2 + K.delta := by linarith only [K.delta_pos]
      have hi :=
        MellinKernel.integrable_gammaFactor_power_line K χ (c := 0) (by norm_num only) hc'
          (by norm_num only) hx
      simpa only [F, K, reciprocalGapMellinKernel, Complex.ofReal_zero, zero_add, mul_assoc] using
        hi
    have hb (t : ℝ) : ‖F t‖ ≤ (A * 4) * H t := by
      have hL : 0 ≤ Real.log (4 + |t|) + 1 := by
        have hl := Real.log_nonneg (show (1 : ℝ) ≤ 4 + |t| by linarith only [abs_nonneg t])
        linarith only [hl]
      have hγ := hbA q χ t
      rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, add_comm (1 / 2 : ℂ)] at hγ
      dsimp only [F]
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
      calc
        _ ≤ (A * (Real.log (4 + |t|) + 1)) * (4 / (1 + t ^ 2)) :=
          mul_le_mul hγ (reciprocalGap_central_norm_le hh.le t) (norm_nonneg _)
            (mul_nonneg hA.le hL)
        _ = _ := by
          dsimp only [H]; ring
    have hiH : MeasureTheory.Integrable (fun t : ℝ ↦ (A * 4) * H t) :=
      Analysis.integrable_log_add_abs_div_one_add_sq.const_mul _
    have hi :=
      (MeasureTheory.norm_integral_le_integral_norm F).trans
        (MeasureTheory.integral_mono hiF.norm hiH hb)
    rw [MeasureTheory.integral_const_mul] at hi
    change ‖∫ t : ℝ, F t‖ ≤ D at hi
    change ‖d * ∫ t : ℝ, F t‖ ≤ _
    rw [norm_mul]
    exact
      (mul_le_mul_of_nonneg_left (hi.trans (le_max_left D 0)) (norm_nonneg d)).trans
        (le_add_of_nonneg_left zero_le_one)

/-- The same positive constant bounds all admissible right gamma integrals uniformly in the
positive gap, character and level, at scales at least one. Shift the line to the center.
This connects the common central bound to the actual completed contour remainder. -/
theorem exists_uniform_reciprocalGap_gamma_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (h : ℝ) (hh : 0 < h) (q : ℕ) (χ : DirichletCharacter ℂ q) {x b : ℝ},
          1 ≤ x →
            0 ≤ b →
            b ≤ 1 / 2 + (reciprocalGapMellinKernel h hh).delta →
            b ≤ 3 / 2 →
            ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
                      ((reciprocalGapMellinKernel h hh).function ((b : ℂ) + Complex.I * t) *
                        (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))‖ ≤
              C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_reciprocalGap_central_gamma_bound
  refine ⟨C, hC, ?_⟩
  intro h hh q χ x b hx hb0 hbK hb2
  rw [MellinKernel.gammaIntegral_eq_central (reciprocalGapMellinKernel h hh) χ hb0 hbK hb2 hx]
  exact hb h hh q χ (zero_lt_one.trans_le hx)

/-- The normalized completed logarithmic-derivative integral on the left line of the gap kernel.
The line has real part -1/2-delta(h)/2. Its contribution remains explicit in the remainder.
Positive gap provides the admissible line used by the contour identity. -/
noncomputable def reciprocalGapLeftIntegral {q : ℕ} [NeZero q] (h : ℝ) (hh : 0 < h)
    (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  let K := reciprocalGapMellinKernel h hh
  let a := -1 / 2 - K.delta / 2
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      -logDeriv χ.completedLFunction ((((a : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
        (K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t)))

/-- After subtracting the first-pole residue and left integral, one positive constant bounds
the completed remainder for all positive gaps and scales at least one.
The exact definition leaves the right gamma integral; use its gap-uniform estimate.
This separates the two potentially gap-dependent costs from the uniform archimedean cost. -/
theorem exists_uniform_reciprocalGap_remainder_sub_pole_left_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (h : ℝ) (hh : 0 < h) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ},
          1 ≤ x →
            ‖reciprocalGapCompletedRemainder h hh χ x -
                  MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
                    (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
                  reciprocalGapLeftIntegral h hh χ x‖ ≤
              C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_reciprocalGap_gamma_bound
  refine ⟨C, hC, ?_⟩
  intro h hh q _ χ x hx
  let K := reciprocalGapMellinKernel h hh
  have hd := K.delta_pos
  have hu : K.delta ≤ (1 / 8 : ℝ) := min_le_right _ _
  have hg :=
    hb h hh q χ (b := 1 / 2 + K.delta / 2) hx (by linarith only [hd]) (by linarith only [hd])
      (by linarith only [hu])
  have he :
    reciprocalGapCompletedRemainder h hh χ x -
        MellinKernel.weightedResidue K (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
        reciprocalGapLeftIntegral h hh χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor ((((1 / 2 + K.delta / 2 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((1 / 2 + K.delta / 2 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((1 / 2 + K.delta / 2 : ℝ) : ℂ) + Complex.I * t))) := by
    dsimp only [reciprocalGapCompletedRemainder, reciprocalGapLeftIntegral, K]
    ring
  rw [he]
  exact hg

/-- Under primitive nonprincipal GRH data at level at least eight, the completed remainder is
bounded by ((7/6) log(q)+4)/(h sqrt(x)), the norm of the left integral, and a common positive
constant independent of h, q, character and scale x at least one.
Combine the explicit pole bound and uniform gamma bound by the triangle inequality.
The left integral still needs an explicit numerical estimate for witness cutoffs. -/
theorem exists_uniform_reciprocalGap_remainder_split_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (h : ℝ) (hh : 0 < h) {q : ℕ} [NeZero q],
          8 ≤ q →
            ∀ {χ : DirichletCharacter ℂ q},
              χ.IsPrimitive →
                χ ≠ 1 →
                AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                ∀ {x : ℝ},
                  1 ≤ x →
                    ‖reciprocalGapCompletedRemainder h hh χ x‖ ≤
                      ((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) +
                        ‖reciprocalGapLeftIntegral h hh χ x‖ +
                        C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_reciprocalGap_remainder_sub_pole_left_bound
  refine ⟨C, hC, ?_⟩
  intro h hh q _ hq χ hp hne hGRH x hx
  let P :=
    MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
      (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)
  let L := reciprocalGapLeftIntegral h hh χ x
  let R := reciprocalGapCompletedRemainder h hh χ x
  have he : R = (R - P - L) + P + L := by ring
  have hn :=
    (norm_add_le ((R - P - L) + P) L).trans (add_le_add (norm_add_le (R - P - L) P) (le_refl ‖L‖))
  have hγ : ‖R - P - L‖ ≤ C := hb h hh q χ hx
  have hpole : ‖P‖ ≤ ((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) :=
    reciprocalGap_poleResidue_norm_le hh hq hp hne hGRH (zero_lt_one.trans_le hx)
  rw [← he] at hn
  change ‖R‖ ≤ _
  linarith only [hn, hγ, hpole]

/-- One gap-independent positive Gamma allowance gives a prime non-one witness whenever
the principal finite sum exceeds the zero-prefix budget, explicit pole cost, left integral
norm and that allowance. Assume primitive nonprincipal GRH data at level at least eight.
Bound the remainder real part by the separated norm estimate and apply prime separation.
This criterion exposes the left integral as the remaining gap-dependent analytic cost. -/
theorem exists_uniform_reciprocalGap_prime_separation :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (h : ℝ) (hh : 0 < h) {q : ℕ} [NeZero q],
          8 ≤ q →
            ∀ {χ : DirichletCharacter ℂ q},
              AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ {c x : ℝ},
                  (1 / 2 : ℝ) < c →
                    c ^ 2 ≤ 1 / 4 + h / 2 →
                    1 ≤ x →
                    ∀ B : Finset ℕ,
                      (1 / c) *
                              (Real.log q / 2 +
                                  (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
                                  (∑' n : ℕ,
                                    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
                                ∑ n ∈ B,
                                  (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n /
                                    (n : ℝ) ^ (1 / 2 + c)) +
                            (((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) +
                              ‖reciprocalGapLeftIntegral h hh χ x‖ +
                              C) <
                          (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re →
                        ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_reciprocalGap_remainder_split_bound
  refine ⟨C, hC, ?_⟩
  intro h hh q _ hq χ hGRH hp hne hinv c x hc hbound hx B hgap
  apply
    exists_prime_not_one_of_reciprocalGap_separation hh ((by norm_num only : 2 ≤ 8).trans hq) hGRH
      hp hne hinv hc hbound hx B
  have hr :=
    (Complex.re_le_norm (reciprocalGapCompletedRemainder h hh χ x)).trans
      (hb h hh hq hp hne hGRH hx)
  exact (add_le_add (le_refl _) hr).trans_lt hgap

end PseudoPrime.LLS.PaperStatements
