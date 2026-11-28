/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformLow76
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformAnyCutoff
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsi08Certificates
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFiniteMajorant
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredPsiLower
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.Analysis.NumericalLogBounds
import Mathlib.Tactic.Ring

/-! # Shared lower-range quarter-square witness bound -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The positive central gap bounds the closed-tail budget, including the
principal boundary coefficient from the four-fifths Chebyshev estimate. -/
private theorem psi08_budget {r : ℝ} (hr : 1 ≤ r) (hgap : 0 < quarterPsi08Gap r) :
    (4 * r) * quarterReflectedScale r + (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 + quarterMomentScale r +
            (3 / 4 : ℝ) * r -
          (3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap (r ^ 2) ≤
      (27 / 25 : ℝ) ^ 5 * ((24439 / 50000 : ℝ) * r - 1151 / 5000 - 351 / (200 * r)) -
        3 * Real.log (2 * Real.pi) * quarterReflectedScale r := by
  have hp : 0 < r := lt_of_lt_of_le (by norm_num only) hr
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ r ^ 2 by nlinarith only [hr])
  have hpos : 0 ≤ quarterReflectedScale r := by
    unfold quarterReflectedScale
    positivity
  have hpi :=
    mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3) hpos)
  obtain ⟨hc, hm⟩ :=
    quarter_finite_reflected_upper hr (le_refl (Real.log (r ^ 2)))
      (le_refl ((r ^ 2) ^ (-(27 / 25 : ℝ))))
  have hcond :=
    mul_le_mul_of_nonneg_left hc (show 0 ≤ 4 * r + (5517 / 1000 : ℝ) by linarith only [hr])
  have he : (r ^ 2) ^ (-(27 / 25 : ℝ)) = r ^ (-(54 / 25 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hp.le]
    norm_num only
  rw [he, Real.log_pow, Nat.cast_ofNat] at hcond hm
  unfold quarterPsi08Gap at hgap
  linarith only [hpi, hcond, hm, hgap]

/-- Under GRH, every odd uniform Korselt triple with log in [76,533]
has a prime Miller–Rabin witness at the squared half-logarithm cutoff. -/
private theorem uniform_witness_76_to533 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 76 533) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log n / 2) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hl : (76 : ℝ) ≤ Real.log n := hL.1
  have hh : Real.log n ≤ (533 : ℝ) := hL.2
  have hr : 38 ≤ r := by
    dsimp only [r]; linarith only [hl]
  have hmax : r ≤ 533 / 2 := div_le_div_of_nonneg_right hh (by norm_num only)
  have hr0 : 0 < r := by linarith only [hr]
  have hx : 1423 ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 38)]
  have htop : r ^ 2 ≤ 1000000 := by exact (pow_le_pow_left₀ hr0.le hmax 2).trans (by norm_num only)
  have hpsi := (AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million hx htop)
  rw [Real.sqrt_sq hr0.le] at hpsi
  have hM : (0 : ℝ) ≤ 4 / 5 * r := mul_nonneg (by norm_num only) hr0.le
  have hr1 : (1 : ℝ) ≤ r := by linarith only [hr]
  have hcenter := quarter_combined_of_psi hGRH.riemann hr1 hM (abs_le.mp hpsi).1
  have hf :
    ((61 / 250 : ℝ) * (4 / 5 * r) + 351 / 200) / r = 61 / 250 * (4 / 5) + 351 / (200 * r) := by
    field_simp [hr0.ne']
  rw [hf, div_eq_mul_inv (3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2)),
    mul_assoc (3 * Real.log (2 * Real.pi)), ← div_eq_mul_inv (refinedWeight (1 / r ^ 2)),
    quarter_reflected_scale_eq hr0] at hcenter
  have href :=
    quarter_reflected_of_moments (show (1 : ℝ) ≤ r ^ 2 by linarith only [hx])
      (quarter_moment_bounds_of_integrals hGRH.riemann quarter_moment_integral_bounds)
  have hgamma : 0 ≤ quarterGammaFirstCorrection (Real.log (r ^ 2) + 21 / 8) := by
    apply quarter_gamma_first_nonneg
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ r ^ 2 by linarith only [hx])
    linarith only [hlog]
  have hg := psi08_budget hr1 (quarter_psi08_gap_positive hL)
  have hlog : Real.log n = 2 * r := by
    dsimp only [r]; ring
  have hx' : (625 : ℝ) ≤ r ^ 2 := by linarith only [hx]
  change ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)
  apply
    quarter_uniform_bounds_any hn ho hu hGRH hx' href hlog.le ∅
      (fun k hk ↦ (Finset.notMem_empty k hk).elim) le_rfl le_rfl
  dsimp only [quarterUniformClosedBudget, quarterReflectedScale, quarterMomentScale] at hg hcenter ⊢
  simp only [Finset.sum_empty, mul_zero, sub_zero]
  linarith only [hg, hcenter, hgamma]

/-- Under GRH, a uniform Korselt triple with logarithm at most 533 admits a
prime rejecting base bounded by the square of its half-logarithm. -/
public theorem uniform_witness_through533 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hU : Real.log n ≤ 533) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log n / 2) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h76 : Real.log n ≤ 76
  · rw [show (Real.log n / 2) ^ 2 = (1 / 4 : ℝ) * Real.log n ^ 2 by ring]
    exact quarter_uniform_low76 hn ho hu hGRH h76
  exact uniform_witness_76_to533 hn ho hu hGRH ⟨le_of_not_ge h76, hU⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
