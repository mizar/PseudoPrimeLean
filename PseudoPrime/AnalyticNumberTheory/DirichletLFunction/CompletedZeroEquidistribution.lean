/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedZeroFunctional
public import PseudoPrime.Analysis.CircleAverage

/-!
# Uniform weighted completed-zero distribution on the circle

Integer moments and a common functional norm bound give convergence for every continuous
circle test function to half its uniform average, uniformly over primitive characters.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The uniform convergence predicate for a fixed continuous circle test function.
For every positive error, sufficiently large moduli make its normalized completed-zero
evaluation differ from half its circle average by at most that error, for all primitive
nonprincipal characters satisfying individual RH with nonprincipal inverse.
This local predicate organizes the linear-span and uniform-approximation proof. -/
private def ConvergesToHalfCircleAverage (f : C(Circle, ℂ)) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
      ∃ Q : ℕ,
        ∃ hQ : 2 ≤ Q,
          ∀ (q : ℕ) [NeZero q],
            ∀ hq : Q ≤ q,
              ∀ (χ : DirichletCharacter ℂ q),
                ∀ hRH : GRH.DirichletRiemannHypothesis χ,
                  ∀ hp : χ.IsPrimitive,
                    ∀ hne : χ ≠ 1,
                      ∀ hinv : χ⁻¹ ≠ 1,
                        ‖normalizedCompletedZeroFunctional (hQ.trans hq) hRH hp hne hinv f -
                              (1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage f‖ ≤
                          ε

/-- Every integer circle monomial satisfies the uniform convergence predicate.
For degree zero, use the constant-one mass limit; otherwise use the vanishing moment.
The circle average has the corresponding value one or zero.
This supplies the generators of the dense test space. -/
private theorem converges_monomial (k : ℤ) :
    ConvergesToHalfCircleAverage (PseudoPrime.Analysis.circleMonomial k) := by
  intro ε hε
  by_cases hk : k = 0
  · rw [hk]
    have h := exists_uniform_normalizedCompletedZeroFunctional_const_one_error_le hε
    have hmono : PseudoPrime.Analysis.circleMonomial 0 = ContinuousMap.const Circle (1 : ℂ) := by
      ext p; exact zpow_zero _
    simpa only [hmono, PseudoPrime.Analysis.circleAverage_const_one, mul_one] using h
  · have h :=
      exists_uniform_normalizedCompletedZeroFunctional_monomial_le hk
        (PseudoPrime.Analysis.circleMonomial k) (fun p => rfl) hε
    simpa only [PseudoPrime.Analysis.circleAverage_circleMonomial, ite_eq_right hk, mul_zero,
      sub_zero] using h

/-- The zero circle function satisfies the convergence predicate at every modulus.
Both linear functionals vanish on zero. This starts the span induction. -/
private theorem converges_zero : ConvergesToHalfCircleAverage 0 := by
  intro ε hε
  refine ⟨2, le_rfl, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  simp only [map_zero, mul_zero, sub_zero, norm_zero]
  exact hε.le

/-- If two continuous circle functions satisfy uniform normalized-zero convergence,
their sum does too. Use half the error for each function, take the maximum conductor
threshold, and combine the two linear evaluation errors by the triangle inequality.
This closes the convergent test space under addition. -/
private theorem converges_add {f g : C(Circle, ℂ)} (hf : ConvergesToHalfCircleAverage f)
    (hg : ConvergesToHalfCircleAverage g) : ConvergesToHalfCircleAverage (f + g) := by
  intro ε hε
  have he : (0 : ℝ) < ε / 2 := div_pos hε zero_lt_two
  obtain ⟨Qf, hQf, hbf⟩ := hf (ε / 2) he
  obtain ⟨Qg, hQg, hbg⟩ := hg (ε / 2) he
  refine ⟨max Qf Qg, hQf.trans (Nat.le_max_left _ _), ?_⟩
  intro q _ hq χ hRH hp hne hinv
  have hfq := hbf q ((Nat.le_max_left _ _).trans hq) χ hRH hp hne hinv
  have hgq := hbg q ((Nat.le_max_right _ _).trans hq) χ hRH hp hne hinv
  rw [map_add, map_add, mul_add,
    show
      normalizedCompletedZeroFunctional (hQf.trans ((Nat.le_max_left _ _).trans hq)) hRH hp hne hinv
              f +
            normalizedCompletedZeroFunctional (hQf.trans ((Nat.le_max_left _ _).trans hq)) hRH hp
              hne hinv g -
          ((1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage f +
            (1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage g) =
        (normalizedCompletedZeroFunctional (hQf.trans ((Nat.le_max_left _ _).trans hq)) hRH hp hne
              hinv f -
            (1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage f) +
          (normalizedCompletedZeroFunctional (hQf.trans ((Nat.le_max_left _ _).trans hq)) hRH hp hne
              hinv g -
            (1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage g)
      by ring]
  apply (norm_add_le _ _).trans
  linarith only [hfq, hgq]

/-- Multiplying a convergent continuous circle test function by any complex scalar
preserves uniform normalized-zero convergence. For a nonzero scalar, divide the desired
error by its positive norm; the zero scalar gives the zero function.
This closes the convergent test space under complex linear combinations. -/
private theorem converges_smul (c : ℂ) {f : C(Circle, ℂ)} (hf : ConvergesToHalfCircleAverage f) :
    ConvergesToHalfCircleAverage (c • f) := by
  by_cases hc : c = 0
  · rw [hc, zero_smul]
    exact converges_zero
  intro ε hε
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨Q, hQ, hb⟩ := hf (ε / ‖c‖) (div_pos hε hcn)
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    show
      c * normalizedCompletedZeroFunctional (hQ.trans hq) hRH hp hne hinv f -
          (1 / 2 : ℂ) * (c * PseudoPrime.Analysis.circleAverage f) =
        c *
          (normalizedCompletedZeroFunctional (hQ.trans hq) hRH hp hne hinv f -
            (1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage f)
      by ring,
    norm_mul]
  have h := mul_le_mul_of_nonneg_left (hb q hq χ hRH hp hne hinv) hcn.le
  simpa only [mul_div_cancel₀ _ (ne_of_gt hcn)] using h

/-- Every finite complex linear combination of integer circle monomials satisfies
uniform normalized-zero convergence. Induct on span membership using the moment estimates
and closure under zero, addition, and scalar multiplication.
This provides the dense family to which continuous functions are approximated. -/
private theorem converges_span {f : C(Circle, ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range PseudoPrime.Analysis.circleMonomial)) :
    ConvergesToHalfCircleAverage f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf; exact converges_monomial k
  | zero => exact converges_zero
  | add f g _ _ hf hg => exact converges_add hf hg
  | smul c f _ hf => exact converges_smul c hf

/-- Half the uniform circle average of a continuous function has norm at most its
supremum norm. Combine the average's operator norm at most one with the scalar norm
one half. This controls the limiting functional in the approximation estimate. -/
private theorem norm_halfCircleAverage_le (f : C(Circle, ℂ)) :
    ‖(1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage f‖ ≤ ‖f‖ := by
  rw [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
  have h0 := PseudoPrime.Analysis.circleAverage.le_opNorm f
  have h1 :=
    mul_le_mul_of_nonneg_right PseudoPrime.Analysis.norm_circleAverage_le_one (norm_nonneg f)
  have h2 : 0 ≤ ‖f‖ := norm_nonneg f
  nlinarith only [h0, h1, h2]

/-- Every continuous circle function satisfies uniform normalized-zero convergence.
Approximate it within one quarter of the error by a finite monomial combination, use
half the error for that combination, and bound the two approximation errors by the
common norm bound and the average bound. This removes the restriction to polynomial tests. -/
private theorem converges_all (f : C(Circle, ℂ)) : ConvergesToHalfCircleAverage f := by
  intro ε hε
  have he4 : (0 : ℝ) < ε / 4 := div_pos hε (by norm_num only : (0 : ℝ) < 4)
  obtain ⟨g, hg, hfg⟩ := PseudoPrime.Analysis.exists_circleMonomial_approximation f he4
  obtain ⟨Q0, hQ0, hb0⟩ := exists_uniform_norm_normalizedCompletedZeroFunctional_le_one
  obtain ⟨Q1, hQ1, hb1⟩ := converges_span hg (ε / 2) (div_pos hε zero_lt_two)
  refine ⟨max Q0 Q1, hQ0.trans (Nat.le_max_left _ _), ?_⟩
  intro q _ hq χ hRH hp hne hinv
  let A :=
    normalizedCompletedZeroFunctional ((hQ0.trans (Nat.le_max_left _ _)).trans hq) hRH hp hne hinv
  have hA : ‖A‖ ≤ 1 := hb0 q ((Nat.le_max_left _ _).trans hq) χ hRH hp hne hinv
  have hBg : ‖A g - (1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage g‖ ≤ ε / 2 :=
    hb1 q ((Nat.le_max_right _ _).trans hq) χ hRH hp hne hinv
  have ha0 := A.le_opNorm (f - g)
  have ha1 := mul_le_mul_of_nonneg_right hA (norm_nonneg (f - g))
  have ha : ‖A (f - g)‖ < ε / 4 :=
    lt_of_le_of_lt (ha0.trans (by simpa only [one_mul] using ha1)) hfg
  have hl : ‖(1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage (g - f)‖ < ε / 4 := by
    apply lt_of_le_of_lt (norm_halfCircleAverage_le (g - f))
    rwa [norm_sub_rev]
  change ‖A f - (1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage f‖ ≤ ε
  calc
    _ =
        ‖(A (f - g) + (A g - (1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage g)) +
            (1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage (g - f)‖ :=
      by
      congr 1
      rw [map_sub, map_sub]
      ring
    _ ≤
        (‖A (f - g)‖ + ‖A g - (1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage g‖) +
          ‖(1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage (g - f)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ε := by linarith only [ha, hBg, hl]

/-- For every continuous complex circle function and epsilon > 0, all sufficiently large
moduli make the normalized completed-zero functional differ from half the uniform circle
average by norm at most epsilon, uniformly over primitive nonprincipal characters with
nonprincipal inverse satisfying individual RH. Prove convergence on integer monomials,
extend by linearity to their span, and use uniform approximation with the common operator
norm bound. This is the continuous-test-function form of the weighted zero distribution. -/
theorem exists_uniform_normalizedCompletedZeroFunctional_error_le (f : C(Circle, ℂ)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Q : ℕ,
      ∃ hQ : 2 ≤ Q,
        ∀ (q : ℕ) [NeZero q],
          ∀ hq : Q ≤ q,
            ∀ (χ : DirichletCharacter ℂ q),
              ∀ hRH : GRH.DirichletRiemannHypothesis χ,
                ∀ hp : χ.IsPrimitive,
                  ∀ hne : χ ≠ 1,
                    ∀ hinv : χ⁻¹ ≠ 1,
                      ‖normalizedCompletedZeroFunctional (hQ.trans hq) hRH hp hne hinv f -
                            (1 / 2 : ℂ) * PseudoPrime.Analysis.circleAverage f‖ ≤
                        ε :=
  converges_all f ε hε

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
