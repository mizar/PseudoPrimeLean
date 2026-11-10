/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentTailClosed

/-! Rational interval majorants for the closed Euler-tail envelope. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A monotone polynomial majorant for one closed Euler moment tail. Inputs `L`, `P` and `Q`
respectively bound the logarithm and the negative powers with exponents `29/50` and `83/100`. -/
noncomputable def quarterMomentClosedUpper (k : ℕ) (L P Q : ℝ) : ℝ :=
  2 * Q * L ^ k + P * Analysis.logPowerTailPoly (29 / 50) k L +
    (3 / 4 : ℝ) * Q * Analysis.logPowerTailPoly (83 / 100) k L

/-- An upper logarithm bound and nonnegative negative-power bounds majorize the closed Euler
moment tail. Monotonicity of the tail polynomials reduces its evaluation to rational arithmetic. -/
theorem quarter_moment_closed_upper (k : ℕ) {X L P Q : ℝ} (hX : 1 ≤ X) (hL : Real.log X ≤ L)
    (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) (hP : X ^ (-(29 / 50 : ℝ)) ≤ P) (hQ : X ^ (-(83 / 100 : ℝ)) ≤ Q) :
    quarterMomentClosedTail k X ≤ quarterMomentClosedUpper k L P Q := by
  have hlog0 := Real.log_nonneg hX
  have hlpow := pow_le_pow_left₀ hlog0 hL k
  have hpoly1 :=
    Analysis.log_power_tail_poly_mono (r := (29 / 50 : ℝ)) (by norm_num only) hlog0 hL k
  have hpoly2 :=
    Analysis.log_power_tail_poly_mono (r := (83 / 100 : ℝ)) (by norm_num only) hlog0 hL k
  have hp10 := Analysis.log_power_tail_poly_nonneg (r := (29 / 50 : ℝ)) (by norm_num only) hlog0 k
  have hp20 := Analysis.log_power_tail_poly_nonneg (r := (83 / 100 : ℝ)) (by norm_num only) hlog0 k
  have hb0 := mul_le_mul hQ hlpow (pow_nonneg hlog0 k) hQ0
  have hb1 := mul_le_mul hP hpoly1 hp10 hP0
  have hb2 := mul_le_mul hQ hpoly2 hp20 hQ0
  have hx : X ^ (-(79 / 50 : ℝ)) * X ^ (3 / 4 : ℝ) = X ^ (-(83 / 100 : ℝ)) := by
    rw [← Real.rpow_add (zero_lt_one.trans_le hX)]
    norm_num only
  have he :
    2 * (X ^ (-(79 / 50 : ℝ)) * Real.log X ^ k) * X ^ (3 / 4 : ℝ) =
      2 * (X ^ (-(83 / 100 : ℝ)) * Real.log X ^ k) := by
    rw [← hx]
    ring
  dsimp only [quarterMomentClosedTail, quarterMomentClosedUpper,
    AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
  rw [he]
  linarith only [hb0, hb1, hb2]

/-- Rational-ready majorant for the three-moment closed Euler tail, using common upper
bounds for the cutoff logarithm and the two negative powers. -/
noncomputable def quarterEulerClosedUpper (L P Q : ℝ) : ℝ :=
  (3 / 8 : ℝ) * quarterMomentClosedUpper 0 L P Q +
    (81 / 200 : ℝ) * quarterMomentClosedUpper 1 L P Q +
    (729 / 5000 : ℝ) * quarterMomentClosedUpper 2 L P Q

/-- The closed Euler tail is bounded by a rational-ready three-moment majorant whenever the
logarithm and negative-power interval hypotheses hold. -/
theorem quarter_euler_closed_upper {X L P Q : ℝ} (hX : 1 ≤ X) (hL : Real.log X ≤ L) (hP0 : 0 ≤ P)
    (hQ0 : 0 ≤ Q) (hP : X ^ (-(29 / 50 : ℝ)) ≤ P) (hQ : X ^ (-(83 / 100 : ℝ)) ≤ Q) :
    quarterEulerClosedTailCap X ≤ quarterEulerClosedUpper L P Q := by
  have h0 := quarter_moment_closed_upper 0 hX hL hP0 hQ0 hP hQ
  have h1 := quarter_moment_closed_upper 1 hX hL hP0 hQ0 hP hQ
  have h2 := quarter_moment_closed_upper 2 hX hL hP0 hQ0 hP hQ
  dsimp only [quarterEulerClosedTailCap, quarterEulerClosedUpper]
  linarith only [h0, h1, h2]

end PseudoPrime.PrimeTestBounds.MillerRabin
