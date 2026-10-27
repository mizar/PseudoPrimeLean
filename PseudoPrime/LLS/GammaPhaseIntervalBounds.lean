/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64MomentInterpolation
public import PseudoPrime.LLS.GammaPhase64CompactBounds

/-! # Arithmetic Gamma bounds from a finite rounded interval cover -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: GRH, a primitive nonprincipal character and its nonprincipal inverse,
3<=m<=q with q>=20000, scale x>=2 with |log x|<=8, and a finite rounded endpoint cover.
Claim: the actual Gamma arithmetic sum is bounded by the signed prefix budget and remainder.
Proof: transfer rounded endpoints, interpolate using the logarithmic moment, and apply
the global phase bound to the explicit formula.
Role: replace an infinite spectral premise by finitely many endpoint and cover obligations. -/
theorem gamma_primitive_sum_re_le_phase64_of_rounded_cover {ι : Type*} {q m : ℕ} [NeZero m]
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (hlog : |Real.log x| ≤ 8) (B : Finset ℕ)
    {G : ℕ} (hG : 0 < G) (S : Finset ι) (a b : ι → ℚ)
    (hvalid :
      ∀ i ∈ S,
        (a i : ℝ) < b i ∧
          (b i : ℝ) - a i ≤ 1 / 2000 ∧
          |(a i : ℝ)| ≤ 5 ∧
          |(b i : ℝ)| ≤ 5 ∧
          (1 / 10000 : ℝ) + ((1 / 25000 : ℝ) + 32768 / (G : ℝ)) ≤
            Analysis.roundedPhase64Gap G x (a i) ∧
          (1 / 10000 : ℝ) + ((1 / 25000 : ℝ) + 32768 / (G : ℝ)) ≤
            Analysis.roundedPhase64Gap G x (b i))
    (hcover : ∀ t : ℝ, |t| ≤ 5 → ∃ i ∈ S, t ∈ Set.Icc (a i : ℝ) (b i : ℝ)) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ
          Analysis.phaseResolvent64Coefficients B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hphase :=
    Analysis.phase64_signed_phase_le_of_rounded_cover
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx) hlog hG S a b hvalid hcover
  exact
    gamma_primitive_sum_re_le_phase64_of_compact hq hm hmq hGRH hp hne hinv hx B
      (fun t _ ↦ hphase t)

end PseudoPrime.LLS.PaperStatements
