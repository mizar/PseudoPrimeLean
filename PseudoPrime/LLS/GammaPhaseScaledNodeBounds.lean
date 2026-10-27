/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ScaledGammaPhaseNodes
public import PseudoPrime.LLS.GammaPhaseIntervalBounds

/-! # Arithmetic Gamma bounds from rational phase nodes -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: GRH, primitive-character hypotheses, a bounded scale, a finite interval cover,
and scaled rational lower bounds with certified phase enclosures at its endpoints.
Claim: the actual Gamma sum satisfies the signed-prefix and certified-remainder bound.
Proof: transfer each finite endpoint lower bound to the rounded phase cover theorem.
Role: expose only scaled rational node computations and logarithmic enclosures to a certificate. -/
theorem gamma_primitive_sum_re_le_phase64_of_scaled_nodes {ι : Type*} {q m : ℕ} [NeZero m]
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (hlog : |Real.log x| ≤ 8) (B : Finset ℕ)
    {G : ℕ} (hG : 0 < G) (S : Finset ι) (a b : ι → ℚ) (v ε : ℚ → ℚ)
    (hshape :
      ∀ i ∈ S, (a i : ℝ) < b i ∧ (b i : ℝ) - a i ≤ 1 / 2000 ∧ |(a i : ℝ)| ≤ 5 ∧ |(b i : ℝ)| ≤ 5)
    (hnodes :
      ∀ i ∈ S,
        ∀ t ∈ [a i, b i],
          |(v t : ℝ)| ≤ 128 ∧
            |(t : ℝ) * Real.log (256 * x) - (v t : ℝ)| ≤ (ε t : ℝ) ∧
            (1 / 10000 : ℝ) + ((1 / 25000 : ℝ) + 32768 / (G : ℝ)) ≤
              (Analysis.rationalScaledPhase64Lower G t (v t) (ε t) : ℝ))
    (hcover : ∀ t : ℝ, |t| ≤ 5 → ∃ i ∈ S, t ∈ Set.Icc (a i : ℝ) (b i : ℝ)) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ
          Analysis.phaseResolvent64Coefficients B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  apply
    gamma_primitive_sum_re_le_phase64_of_rounded_cover hq hm hmq hGRH hp hne hinv hx hlog B hG S a b
      _ hcover
  intro i hi
  obtain ⟨hab, hw, ha, hb⟩ := hshape i hi
  have hA := hnodes i hi (a i) List.mem_cons_self
  have hB := hnodes i hi (b i) (List.mem_cons_of_mem _ List.mem_cons_self)
  exact
    ⟨hab, hw, ha, hb,
      hA.2.2.trans (Analysis.rationalScaledPhase64Lower_le G (a i) (v (a i)) (ε (a i)) hA.1 hA.2.1),
      hB.2.2.trans (Analysis.rationalScaledPhase64Lower_le G (b i) (v (b i)) (ε (b i)) hB.1 hB.2.1)⟩

end PseudoPrime.LLS.PaperStatements
