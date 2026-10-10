/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ResiduePrimePowerIntervals

/-! Rational checks for the shared analytic residue interval majorant. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Computable rational form of the normalized square and odd-power bound.
Inputs are lower modulus and radius, upper cutoff logarithm, prime-count and
exponent bounds, and natural root certificates. The same finite sum as the real
bound is evaluated over rational numbers for kernel checks. -/
def residuePrimePowerIntervalBoundRat (q s T : ℚ) (W K : ℕ) (b c : ℕ → ℕ) : ℚ :=
  (2 : ℚ) ^ W * T ^ 2 / 4 * (1 / q + 1 / s) +
    (∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℚ) * (b k + (c k : ℚ) / 20)) / s

/-- Computable rational form of the common normalized parity-gap majorant.
Lower modulus, totient and radius endpoints and upper logarithm endpoints determine
the expression, together with prime-count, exponent and root data.
Its real coercion is the analytic interval majorant, so finite rational checks
can supply the strict gap without evaluating real division. -/
def residueParityIntervalMajorantRat (q h s L T : ℚ) (W K : ℕ) (b c : ℕ → ℕ) : ℚ :=
  residuePrimePowerIntervalBoundRat q s T W K b c +
    (1 + 19 / 6 / s) * (693148 / 1000000 / h + (T + 2323148 / 1000000) / s ^ 2) +
    (19 / 6 * (L - 1719 / 1000) +
        (T ^ 2 + (2 / 3 * (L - 1144 / 1000) + 4) * T + T / 2 * (693148 / 1000000 + T))) /
      s +
    2 / h * (1 + 19 / 6 / s) * (T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s)) +
    1 / (20 * h) +
    (1839 / 1000 * T + 1 + 1 / 20 + (W : ℚ) * T ^ 2 / 2) / (h * s)

/-- For rational endpoints and natural root data, coercing the rational majorant
gives exactly the real analytic majorant. Distribute the coercion through arithmetic,
powers and the finite sum. This validates the expression used by numeric certificates. -/
theorem residueParityIntervalMajorantRat_cast (q h s L T : ℚ) (W K : ℕ) (b c : ℕ → ℕ) :
    (residueParityIntervalMajorantRat q h s L T W K b c : ℝ) =
      residueParityIntervalMajorant h s L T
        (residuePrimePowerIntervalBound q s T W K (fun k ↦ (b k : ℝ)) (fun k ↦ (c k : ℝ))) W := by
  simp only [residueParityIntervalMajorantRat, residuePrimePowerIntervalBoundRat,
    residueParityIntervalMajorant, residueCharacterEndpointError, residuePrimePowerIntervalBound,
    Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_sum,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]

/-- A kernel-checked rational majorant below 1.719 supplies the strict real gap.
Reflect the Boolean comparison and apply the majorant coercion identity.
This is the numeric input to the common least-prime interval theorem. -/
theorem residueParityIntervalGap_of_rational_check {q h s L T : ℚ} {W K : ℕ} {b c : ℕ → ℕ}
    (hc : decide (residueParityIntervalMajorantRat q h s L T W K b c < 1719 / 1000) = true) :
    residueParityIntervalMajorant h s L T
        (residuePrimePowerIntervalBound q s T W K (fun k ↦ (b k : ℝ)) (fun k ↦ (c k : ℝ))) W <
      1719 / 1000 := by
  have hr : residueParityIntervalMajorantRat q h s L T W K b c < 1719 / 1000 := of_decide_eq_true hc
  have ht := (Rat.cast_lt (K := ℝ)).mpr hr
  rw [residueParityIntervalMajorantRat_cast] at ht
  simpa only [Rat.cast_div, Rat.cast_ofNat] using ht

end PseudoPrime.LLS.PaperStatements
