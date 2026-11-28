/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterContour600
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftIntervals
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterArithmetic600
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflected600
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Signed zero comparison for section 99 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the arithmetic and reflected comparisons give an upper
bound on the signed sum of the three oscillating zero series in section 99. -/
theorem section99_signed_zero_upper {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) (ea : a.Even) (eb : b.Even)
    (ec : c.Even) {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    0.717289 * r - 0.29136 - 0.0273 + (if r ≤ 299 then 0.002237 else 0.002229) -
          1.517 * (if r ≤ 299 then 0.00281 else 0.002721) +
        0.09239 +
        (if r ≤ 299 then 0.01154 else 0.01232) +
        (if r ≤ 299 then 0.02549 else 0.02537) +
        ((∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm a X ρ).re +
          (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm b X ρ).re +
          (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm c X ρ).re) <
      section99Conductor r - 3 * (if r ≤ 299 then 0.03434 else 0.0364) := by
  dsimp only
  have h := section99_arithmetic_of_RH hG.riemann a b c hl hu ht hA hB hC
  have hr := section99_reflected_integrals hG.riemann hl hu a b c ht hA hB hC
  have hc :=
    section99_triple_signed_upper hG a b c hp hq hs pa pb pc na nb nc ia ib ic ea eb ec hl hu hlog
      h.le
  have hq₀ : 0 ≤ quarterWeight570 (r ^ 2) 1 := by
    rw [section99_weight_eq_density (by linarith only [hl])]
    exact le_trans (by norm_num only) (section99_density_300 hl hu)
  have hb :=
    mul_le_mul_of_nonneg_right
      (show 3 * Real.log (2 * Real.pi) ≤ 5.517 by linarith only [Analysis.log_two_mul_pi_lt]) hq₀
  have hb' :=
    mul_le_mul_of_nonneg_left (section99_boundary_caps hl) (by norm_num only : (0 : ℝ) ≤ 1.517)
  linarith only [hc, hr, hb, hb']

/-- The two-shift phase gain exceeds the section 99 linear coefficient
minus the corresponding signed remainder budget on each radius interval. -/
theorem section99_twoShift_lower (p q s : ℕ) [NeZero p] [NeZero q] [NeZero s] (hp : Odd p)
    (hq : Odd q) (hs : Odd s) {r : ℝ} (hl : 292 ≤ r) (hRH : RiemannHypothesis) :
    0.0014337 * r - (if r ≤ 299 then 0.13 else 0.125) <
      twoShiftPhaseCoeff * r + twoShiftSignedRemainder p q s hp hq hs r (r ^ 2) := by
  have hc := mul_lt_mul_of_pos_right twoShiftPhaseCoeff_lower (show 0 < r by linarith only [hl])
  split_ifs with hh
  · linarith only [hc, twoShiftRemainder_low p q s hp hq hs hl hh le_rfl hRH]
  · linarith only [hc, twoShiftRemainder_from299 p q s hp hq hs (le_of_not_ge hh) le_rfl hRH]

/-- The section 99 comparison rejects the joint mass and phase estimates
when the signed zero sum has its passing-triple upper bound. This combines
the analytic envelope with the two positive endpoint gaps. -/
theorem section99_zero_bounds_contradict {r M Z : ℝ} (hr : r ∈ Set.Icc 292 300)
    (hM :
      M <
        3 / 4 * r - 13.4154 + 4 * positiveTail570 (r ^ 2) - (if r ≤ 299 then 0.02169 else 0.02179))
    (hP : 0.0014337 * r - (if r ≤ 299 then 0.13 else 0.125) ≤ M + Z)
    (hZ :
      0.717289 * r - 0.29136 - 0.0273 + (if r ≤ 299 then 0.002237 else 0.002229) -
            1.517 * (if r ≤ 299 then 0.00281 else 0.002721) +
          0.09239 +
          (if r ≤ 299 then 0.01154 else 0.01232) +
          (if r ≤ 299 then 0.02549 else 0.02537) +
          Z <
        section99Conductor r - 3 * (if r ≤ 299 then 0.03434 else 0.0364)) :
    False := by
  have h := section99_full_gamma_gap hr
  dsimp only at h
  by_cases hrow : r ≤ 299
  · simp only [ite_eq_left hrow] at h hM hP hZ
    linarith only [h, hM, hP, hZ]
  · simp only [ite_eq_right hrow] at h hM hP hZ
    linarith only [h, hM, hP, hZ]

end PseudoPrime.PrimeTestBounds.MillerRabin
