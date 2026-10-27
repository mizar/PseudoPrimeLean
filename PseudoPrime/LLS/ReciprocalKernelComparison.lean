/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalKernelArithmetic
public import PseudoPrime.LLS.ReciprocalKernelZeroBounds

/-! # Finite reciprocal character sums with a retained positive Euler prefix -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: a character and a real cutoff x.
Definition: the finite sum Lambda(n) chi(n) (1-n/x)/sqrt(x) over positive n <= floor(x).
Output: the actual compact reciprocal arithmetic sum.
Role: evaluate the rational test kernel using finite prime-power data. -/
noncomputable def reciprocalCharacterSum {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
    (ArithmeticFunction.vonMangoldt n / Real.sqrt x : ℝ) * χ n * (1 - (n : ℝ) / x : ℝ)

/-- Input: a character of nonzero level and a real scale.
Definition: the completed pole term and the two contour integrals at -9/16 and 9/16.
Output: the exact remainder after removing the oscillatory zero sum.
Role: keep all remaining analytic costs explicit in the finite arithmetic comparison. -/
noncomputable def reciprocalCompletedRemainder {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x : ℝ) : ℂ :=
  let W := fun s : ℂ ↦ reciprocalMellinFunction s * (x : ℂ) ^ s
  let F := fun s : ℂ ↦ -logDeriv χ.completedLFunction (s + 1 / 2) * W s
  MellinKernel.weightedResidue reciprocalMellinKernel (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2))
      x (-1 / 2) +
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) +
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          W (((9 / 16 : ℝ) : ℂ) + Complex.I * t))

/-- Input: GRH, primitive nonprincipal data with nonprincipal inverse, q >= 2 and x >= 1.
Claim: the finite arithmetic sum is minus the actual zero sum plus the completed remainder.
Proof: specialize the exact rational-kernel contour formula and regroup the remainder.
Role: expose the finite kernel explicit formula in a compact reusable interface. -/
theorem reciprocalCharacterSum_eq_zeroSum_add_remainder {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    reciprocalCharacterSum χ x =
      -(∑' ρ : ℂ, reciprocalMellinKernel.oscillatingZeroTerm χ x ρ) +
        reciprocalCompletedRemainder χ x := by
  rw [reciprocalCharacterSum,
    reciprocalMellinKernel_finite_sum_eq_completed_formula hq hGRH hp hne hinv hx]
  dsimp only [reciprocalCompletedRemainder]
  ring

/-- Input: the same analytic data, 1/2 < a with a squared <= 3/4, and any finite index set.
Claim: the real finite character sum is bounded by the signed real-axis prefix budget and remainder.
Proof: use the actual zero-sum estimate and bound its negative real part by its norm.
Role: connect the nonnegative Euler-prefix gain all the way to finite arithmetic. -/
theorem reciprocalCharacterSum_re_le_positive_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a x : ℝ} (ha : 1 / 2 < a)
    (hau : a ^ 2 ≤ 3 / 4) (hx : 1 ≤ x) (B : Finset ℕ) :
    (reciprocalCharacterSum χ x).re ≤
      (1 / a) *
          (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + a) : ℂ)).re +
              (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + a)) -
            ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + a)) +
        (reciprocalCompletedRemainder χ x).re := by
  have hZ :=
    norm_reciprocal_zeroSum_le_positive_prefix hq hGRH hp hne hinv ha hau (zero_lt_one.trans_le hx)
      B
  have hR := Complex.re_le_norm (-(∑' ρ : ℂ, reciprocalMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hR
  rw [reciprocalCharacterSum_eq_zeroSum_add_remainder hq hGRH hp hne hinv hx, Complex.add_re,
    Complex.neg_re]
  linarith only [hZ, hR]

end PseudoPrime.LLS.PaperStatements
