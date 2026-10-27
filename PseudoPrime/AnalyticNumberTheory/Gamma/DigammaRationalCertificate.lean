/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.RealDigammaTrapezoid
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Kernel-checked rational intervals for real digamma values -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The exact rational reciprocal prefix at base r and length N.
Casting this finite sum gives the prefix in the proved real digamma enclosure. -/
def rationalDigammaPrefix (r : ℚ) (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range N, (r + k)⁻¹

/-- The lower digamma endpoint from the rational logarithm certificate,
the exact reciprocal prefix, and the proved quadratic remainder 1/(8(r+N)²).
Parameters j and t specify the power-of-two logarithm scale and Taylor length. -/
def rationalDigammaLower (r : ℚ) (N j t : ℕ) : ℚ :=
  Analysis.rationalLogLower (r + N) j t - (1 / 2 : ℚ) * (r + N)⁻¹ - (1 / 8 : ℚ) * (r + N)⁻¹ ^ 2 -
    rationalDigammaPrefix r N

/-- The upper digamma endpoint from the rational logarithm certificate
and the exact reciprocal prefix. The real digamma upper remainder is zero. -/
def rationalDigammaUpper (r : ℚ) (N j t : ℕ) : ℚ :=
  Analysis.rationalLogUpper (r + N) j t - (1 / 2 : ℚ) * (r + N)⁻¹ - rationalDigammaPrefix r N

/-- Check the base condition, logarithm displacement, and containment
of both computed digamma endpoints in the proposed rational interval.
A true result is reflected into the real analytic interval theorem. -/
def rationalDigammaIntervalCheck (r : ℚ) (N j t : ℕ) (lo hi : ℚ) : Bool :=
  decide
    ((1 / 2 : ℚ) ≤ r ∧
      |1 - (r + N) / 2 ^ j| < 1 ∧
      lo ≤ rationalDigammaLower r N j t ∧ rationalDigammaUpper r N j t ≤ hi)

/-- Casting the exact rational reciprocal prefix preserves its finite
sum and inverses. This connects the computable certificate with real digamma. -/
theorem rationalDigammaPrefix_cast (r : ℚ) (N : ℕ) :
    (rationalDigammaPrefix r N : ℝ) = ∑ k ∈ Finset.range N, ((r : ℝ) + k)⁻¹ := by
  change (Rat.castHom ℝ) (∑ k ∈ Finset.range N, (r + k)⁻¹) = _
  rw [map_sum]
  simp only [Rat.coe_castHom, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast]

/-- At rational r≥1/2 and a valid logarithm displacement, the computed
endpoints enclose Re ψ(r). Combine the certified real logarithm bounds
with the finite digamma recurrence and its proved quadratic tail. -/
theorem rationalDigammaBounds_sound {r : ℚ} (hr : (1 / 2 : ℚ) ≤ r) (N j t : ℕ)
    (hx : |1 - (r + N) / 2 ^ j| < 1) :
    (rationalDigammaLower r N j t : ℝ) ≤ (Complex.digamma (r : ℂ)).re ∧
      (Complex.digamma (r : ℂ)).re ≤ (rationalDigammaUpper r N j t : ℝ) := by
  have hrR : (1 / 2 : ℝ) ≤ (r : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hr
  have hpos : 0 < r + (N : ℚ) :=
    lt_of_lt_of_le (by norm_num only : (0 : ℚ) < 1 / 2)
      (hr.trans (le_add_of_nonneg_right (Nat.cast_nonneg N)))
  have hl := Analysis.rationalLogBounds_sound hpos j t hx
  have hd := real_digamma_finite_prefix_bounds hrR N
  simp only [Rat.cast_add, Rat.cast_natCast] at hl
  simp only [Complex.ofReal_ratCast] at hd
  simp only [rationalDigammaLower, rationalDigammaUpper, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_pow,
    rationalDigammaPrefix_cast]
  constructor <;> linarith only [hl.1, hl.2, hd.1, hd.2]

/-- A successful finite rational interval check encloses the actual real
digamma value. Extract the checked base, displacement and endpoint conditions,
then apply the analytic endpoint theorem and cast the rational comparisons. -/
theorem rationalDigammaIntervalCheck_sound {r lo hi : ℚ} {N j t : ℕ}
    (h : rationalDigammaIntervalCheck r N j t lo hi = true) :
    (lo : ℝ) ≤ (Complex.digamma (r : ℂ)).re ∧ (Complex.digamma (r : ℂ)).re ≤ (hi : ℝ) := by
  have hc :
    (1 / 2 : ℚ) ≤ r ∧
      |1 - (r + N) / 2 ^ j| < 1 ∧
      lo ≤ rationalDigammaLower r N j t ∧ rationalDigammaUpper r N j t ≤ hi :=
    of_decide_eq_true h
  have ht := rationalDigammaBounds_sound hc.1 N j t hc.2.1
  exact
    ⟨((Rat.cast_le (K := ℝ)).mpr hc.2.2.1).trans ht.1,
      ht.2.trans ((Rat.cast_le (K := ℝ)).mpr hc.2.2.2)⟩

end PseudoPrime.AnalyticNumberTheory.Gamma
