/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Integer endpoints of the phase interval for the lower Chebyshev theta bound -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Partial exponential series used to certify logarithmic endpoints. -/
private def endpointSeries (q : ℚ) : ℚ :=
  (Finset.range 24).sum (fun i => q ^ i / i.factorial)

/-- Certify a rational upper bound for the exponential on the unit interval. -/
private theorem exp_endpoint_upper {q u : ℚ} (hq : 0 ≤ q) (h1 : q ≤ 1)
    (h : endpointSeries q + q ^ 24 * 25 / (Nat.factorial 24 * 24) ≤ u) :
    Real.exp (q : ℝ) ≤ (u : ℝ) := by
  have hb :=
    Real.exp_bound' (by exact_mod_cast hq : 0 ≤ (q : ℝ)) (by exact_mod_cast h1 : (q : ℝ) ≤ 1) (n :=
      24) (by decide)
  have hc := (Rat.cast_le (K := ℝ)).2 h
  norm_num only [endpointSeries, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] at hc hb
  exact hb.trans hc

/-- Certify a rational lower bound using positive terms of the exponential series. -/
private theorem exp_endpoint_lower {q u : ℚ} (hq : 0 ≤ q) (h : u ≤ endpointSeries q) :
    (u : ℝ) ≤ Real.exp (q : ℝ) := by
  have hb := Real.sum_le_exp_of_nonneg (by exact_mod_cast hq : 0 ≤ (q : ℝ)) 24
  have hc := (Rat.cast_le (K := ℝ)).2 h
  simp only [endpointSeries, Rat.cast_sum, Rat.cast_pow, Rat.cast_div, Rat.cast_natCast] at hc
  exact hc.trans hb

/-- Recover the full exponential after reducing its argument by a factor of 32. -/
private theorem exp_endpoint_pow (a : ℚ) : Real.exp (a : ℝ) = Real.exp ((a / 32 : ℚ) : ℝ) ^ 32 := by
  rw [← Real.exp_nat_mul, Rat.cast_div, Rat.cast_ofNat]
  congr 1
  ring

/-- The left logarithmic endpoint lies below eight billion in exponential coordinates. -/
private theorem exp_eight_billion :
    Real.exp ((2280270737862624671 / 100000000000000000 : ℚ) : ℝ) ≤ 8000000000 := by
  let a : ℚ := 2280270737862624671 / 100000000000000000
  let u : ℚ := 3186336130288318693 / 1562500000000000000
  have he :=
    exp_endpoint_upper (q := a / 32) (u := u) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le he 32
  have hc : u ^ 32 ≤ 8000000000 := by decide +kernel
  rw [exp_endpoint_pow a]
  exact hp.trans (by exact_mod_cast hc)

/-- The right logarithmic endpoint covers 279 billion in exponential coordinates. -/
private theorem exp_last_endpoint :
    279000000000 ≤ Real.exp ((13177238809383888661 / 500000000000000000 : ℚ) : ℝ) := by
  let a : ℚ := 13177238809383888661 / 500000000000000000
  let u : ℚ := 22786369279849273631 / 10000000000000000000
  have he := exp_endpoint_lower (q := a / 32) (u := u) (by decide +kernel) (by decide +kernel)
  have hp := pow_le_pow_left₀ (by exact_mod_cast (by decide +kernel : 0 ≤ u) : (0 : ℝ) ≤ u) he 32
  have hc : 279000000000 ≤ u ^ 32 := by decide +kernel
  rw [exp_endpoint_pow a]
  exact le_trans (by exact_mod_cast hc) hp

/-- Transfer the closed logarithmic phase band to every real x between the integer endpoints. -/
theorem theta_lower_phase_interval
    (h :
      ∀
        L ∈
          Set.Icc ((2280270737862624671 / 100000000000000000 : ℚ) : ℝ)
            ((13177238809383888661 / 500000000000000000 : ℚ) : ℝ),
        (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
          L * (L - Real.log L) / (8 * Real.pi))
    {x : ℝ} (hx : 8000000000 ≤ x) (hy : x ≤ 279000000000) :
    (x - Chebyshev.theta x) / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  have hp := (Real.exp_pos _).trans_le (exp_eight_billion.trans hx)
  have hl := (Real.le_log_iff_exp_le hp).2 (exp_eight_billion.trans hx)
  have hu := (Real.log_le_iff_le_exp hp).2 (hy.trans exp_last_endpoint)
  simpa only [Real.exp_log hp] using h (Real.log x) ⟨hl, hu⟩

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
