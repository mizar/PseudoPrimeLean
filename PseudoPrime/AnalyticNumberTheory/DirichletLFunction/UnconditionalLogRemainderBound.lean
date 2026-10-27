/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogOriginRegularization

/-! # Uniform origin-free remainder bounds for half-scale character sums -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- One positive absolute constant bounds the regularized half-scale remainder
by `C * (log x + 1)` for all primitive nonprincipal characters and `x ≥ 4`.
The odd gamma factor is fixed, the even correction is explicit, the completed
logarithmic derivative at two is uniformly bounded, and both trivial corrections
have norm at most one. This removes every uncontrolled origin-derivative term
from the arithmetic error bound without RH or an exceptional-zero hypothesis. -/
theorem exists_norm_regularized_logarithmicHalfRemainder_le_log :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive →
            ∀ (hne : χ ≠ 1),
              ∀ (x : ℝ),
                4 ≤ x →
                  ‖logarithmicHalfRemainder hne x -
                        (Real.log 2 : ℂ) *
                          (logDeriv χ.completedLFunction 2 - logDeriv χ.completedLFunction 0)‖ ≤
                    C * (Real.log x + 1) := by
  obtain ⟨B, hB, hderiv⟩ :=
    exists_norm_completed_logDeriv_small_shift_bound (r := 1) (by norm_num only) le_rfl
  let G := 4 + B * (Real.log 4 + 1)
  let a := ‖(Real.log 2 : ℂ)‖
  let E := ‖(Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2‖
  let D := ‖logDeriv (fun s : ℂ ↦ Complex.Gammaℝ (s + 1)) 0‖
  let R := a * (G + E + D) + a ^ 2 / 2 + 2
  let C := R + a + 1
  have ha : 0 ≤ a := norm_nonneg _
  have hE : 0 ≤ E := norm_nonneg _
  have hD : 0 ≤ D := norm_nonneg _
  have hG : 0 ≤ G := by
    dsimp only [G]
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
    have hp := mul_nonneg hB.le (by linarith only [hlog4] : 0 ≤ Real.log 4 + 1)
    linarith only [hp]
  have hR : 0 ≤ R := by
    dsimp only [R]
    have hp := mul_nonneg ha (by linarith only [hG, hE, hD] : 0 ≤ G + E + D)
    nlinarith only [hp, sq_nonneg a]
  refine
    ⟨C, by
      dsimp only [C]; linarith only [hR, ha], ?_⟩
  intro q _ χ hp hne x hx
  have hxpos : 0 < x := by linarith only [hx]
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hlognorm : ‖Complex.log (x : ℂ)‖ = Real.log x := by
    rw [← Complex.ofReal_log hxpos.le, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogx]
  have hF : ‖logDeriv χ.completedLFunction 2‖ ≤ G := by
    have h := hderiv χ hne 0
    norm_num only [Complex.ofReal_zero, mul_zero, add_zero, div_one, abs_zero] at h
    exact h
  have ht1 := norm_logarithmicTrivialCorrection_le_one χ (by linarith only [hx] : 2 ≤ x)
  have ht2 := norm_logarithmicTrivialCorrection_le_one χ (by linarith only [hx] : 2 ≤ x / 2)
  have hnorm :
    ‖logarithmicHalfRemainder hne x -
          (Real.log 2 : ℂ) * (logDeriv χ.completedLFunction 2 - logDeriv χ.completedLFunction 0)‖ ≤
      R + a * Real.log x := by
    rcases χ.even_or_odd with he | ho
    · rw [logarithmicHalfRemainder_regularized_of_even hp hne he hxpos]
      let u := -(Real.log 2 : ℂ) * logDeriv χ.completedLFunction 2
      let v :=
        (Real.log 2 : ℂ) * ((Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2)
      let w := Complex.log (x : ℂ) * (Real.log 2 : ℂ)
      let z := (Real.log 2 : ℂ) ^ 2 / 2
      have heq :
        -(Real.log 2 : ℂ) * logDeriv χ.completedLFunction 2 -
              (Real.log 2 : ℂ) * (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) /
                2 -
              Complex.log (x : ℂ) * (Real.log 2 : ℂ) +
            (Real.log 2 : ℂ) ^ 2 / 2 =
          u - v - w + z := by
        dsimp only [u, v, w, z]
        ring
      rw [heq]
      have h1 := norm_sub_le u v
      have h2 := norm_sub_le (u - v) w
      have h3 := norm_add_le (u - v - w) z
      have h4 := norm_add_le (u - v - w + z) (logarithmicTrivialCorrection χ x)
      have h5 :=
        norm_sub_le (u - v - w + z + logarithmicTrivialCorrection χ x)
          (logarithmicTrivialCorrection χ (x / 2))
      have hu : ‖u‖ ≤ a * G := by
        dsimp only [u]
        rw [norm_mul, norm_neg]
        exact mul_le_mul_of_nonneg_left hF ha
      have hv : ‖v‖ = a * E := norm_mul _ _
      have hw : ‖w‖ = Real.log x * a := by
        dsimp only [w]
        rw [norm_mul, hlognorm]
      have hz : ‖z‖ = a ^ 2 / 2 := by
        dsimp only [z]
        rw [norm_div, norm_pow]
        norm_num only [Complex.norm_ofNat]
        rfl
      dsimp only [R]
      have had := mul_nonneg ha hD
      nlinarith only [h1, h2, h3, h4, h5, hu, hv, hw, hz, ht1, ht2, had]
    · rw [logarithmicHalfRemainder_regularized_of_odd hp hne ho hxpos]
      have hg : DirichletCharacter.gammaFactor χ = fun s : ℂ ↦ Complex.Gammaℝ (s + 1) :=
        funext ho.gammaFactor_def
      have hgamma : ‖logDeriv (DirichletCharacter.gammaFactor χ) 0‖ = D := by rw [hg]
      have h1 :=
        norm_sub_le ((Real.log 2 : ℂ) * logDeriv (DirichletCharacter.gammaFactor χ) 0)
          ((Real.log 2 : ℂ) * logDeriv χ.completedLFunction 2)
      have h2 :=
        norm_add_le
          ((Real.log 2 : ℂ) * logDeriv (DirichletCharacter.gammaFactor χ) 0 -
            (Real.log 2 : ℂ) * logDeriv χ.completedLFunction 2)
          (logarithmicTrivialCorrection χ x)
      have h3 :=
        norm_sub_le
          ((Real.log 2 : ℂ) * logDeriv (DirichletCharacter.gammaFactor χ) 0 -
              (Real.log 2 : ℂ) * logDeriv χ.completedLFunction 2 +
            logarithmicTrivialCorrection χ x)
          (logarithmicTrivialCorrection χ (x / 2))
      rw [norm_mul, norm_mul, hgamma] at h1
      have hmul := mul_le_mul_of_nonneg_left hF ha
      have haE := mul_nonneg ha hE
      have halog := mul_nonneg ha hlogx
      change _ ≤ a * (G + E + D) + a ^ 2 / 2 + 2 + a * Real.log x
      nlinarith only [h1, h2, h3, hmul, ht1, ht2, haE, halog, sq_nonneg a]
  dsimp only [C]
  have hpR := mul_nonneg hR hlogx
  linarith only [hnorm, hpR, hlogx, ha]

/-- Uniformly for primitive nonprincipal characters with nonprincipal inverse,
modulus at least two, and scale at least four, the half-scale arithmetic sum is
bounded by the absolute regularized zero sum and an absolute logarithmic error.
Combine the exact regularized formula, absolute convergence, and the uniform
remainder estimate. This is the origin-free interface for the density argument. -/
theorem exists_norm_characterLogWeightedSum_half_le_regularized_zero_sum :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (x : ℝ),
                  4 ≤ x →
                    ‖Arithmetic.characterLogWeightedSum x χ -
                          Arithmetic.characterLogWeightedSum (x / 2) χ‖ ≤
                      (∑' ρ : ℂ, ‖regularizedLogHalfZeroTerm χ x ρ‖) + C * (Real.log x + 1) := by
  obtain ⟨C, hC, hrem⟩ := exists_norm_regularized_logarithmicHalfRemainder_le_log
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hp hne hinv x hx
  have hx2 : 2 < x := by linarith only [hx]
  rw [characterLogWeightedSum_half_regularized_formula_unconditionally hq hp hne hinv hx2]
  have hs := (summable_regularizedLogHalfZeroTerm_unconditionally hq hp hne hinv hx2.le).norm
  have hn :=
    norm_add_le (-(∑' ρ : ℂ, regularizedLogHalfZeroTerm χ x ρ))
      (logarithmicHalfRemainder hne x -
        (Real.log 2 : ℂ) * (logDeriv χ.completedLFunction 2 - logDeriv χ.completedLFunction 0))
  rw [norm_neg] at hn
  exact hn.trans (add_le_add (norm_tsum_le_tsum_norm hs) (hrem q χ hp hne x hx))

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
