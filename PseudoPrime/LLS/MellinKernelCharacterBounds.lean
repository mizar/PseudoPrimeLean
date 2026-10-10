/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelAmbientZeroMass
public import PseudoPrime.LLS.MellinKernelPrincipalBounds
public import PseudoPrime.LLS.SmoothedSubgroupBounds

/-! # Principal and nonprincipal character estimates for Mellin kernels

Combine the principal-character contour estimate, the primitive-character explicit
formula, the level-change correction and the sharp ambient zero mass to prove Lemma 6.1.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- GRH implies the complete principal and nonprincipal estimates of Lemma 6.1 for
every admissible Mellin kernel. The error constant is independent of epsilon, modulus,
subgroup, character and scale. Sum the two existing remainder constants, use the sharp
ambient bound for the inducing primitive character, and express its bounded real
zero contribution by a theta of absolute value at most one. This supplies the analytic
input to subgroup averaging and Proposition 6.1. -/
theorem lemma61 : lls_lemma61 := by
  intro hGRH K
  obtain ⟨Cp, hCp, hbP⟩ := exists_principal_summand_remainder_le K hGRH.riemann
  obtain ⟨Cn, hCn, hbN⟩ := exists_real_summand_formula_primitive_zeroMass K
  refine ⟨Cp + Cn, add_pos hCp hCn, ?_⟩
  intro ε hε
  obtain ⟨N, _, hbM⟩ := exists_uniform_kernelZeroSum_le_mass_ambient K hGRH hε
  refine ⟨max 20000 N, (by norm_num only : 3 ≤ 20000).trans (Nat.le_max_left _ _), ?_⟩
  intro q _ hq H _ χ _ x hx
  have hq0 : 20000 ≤ q := (Nat.le_max_left 20000 N).trans hq
  have hqN : N ≤ q := (Nat.le_max_right 20000 N).trans hq
  have hU : 0 ≤ 1 + Real.log q * Real.log x / Real.sqrt x :=
    add_nonneg zero_le_one
      (div_nonneg (mul_nonneg (Real.log_natCast_nonneg q) (Real.log_nonneg (by linarith only [hx])))
        (Real.sqrt_nonneg x))
  refine ⟨summable_summand K χ (by linarith only [hx]), ?_, ?_⟩
  · intro he
    subst χ
    exact (hbP hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCn.le) hU)
  · intro hne
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    obtain ⟨θ, r, hθ, hr, he⟩ := hbN hq0 χ hne hGRH hx
    have hn := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
    have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
    have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
    have hmass :=
      hbM q χ.conductor hqN ((by norm_num only : 2 ≤ 3).trans hm) hmq χ.primitiveCharacter
        (DirichletCharacter.primitiveCharacter_isPrimitive χ) hn (inv_ne_one.mpr hn)
    let M := ∑' ρ : ℂ, ‖K.kernelZeroTerm χ.primitiveCharacter ρ‖
    have hM : 0 ≤ M := tsum_nonneg (fun ρ ↦ norm_nonneg _)
    have ht : |θ * M| ≤ (1 + ε) * K.mass * Real.log q := by
      rw [abs_mul, abs_of_nonneg hM]
      exact (mul_le_mul_of_nonneg_right hθ hM).trans (by simpa only [one_mul] using hmass)
    obtain ⟨θ', hθ', he'⟩ := LLS.exists_theta_mul_of_abs_le ht
    refine ⟨θ', r, hθ', hr.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCp.le) hU), ?_⟩
    change (∑' n : ℕ, K.summand χ x n).re = θ * M + r at he
    rw [he, he']
    ring

/-- Under GRH, if every prime not dividing q up to X lies in a proper subgroup H,
the finite principal smoothed sum is bounded by the principal main term, index minus
one sharp kernel-mass contributions, and index times the uniform remainder. The
constant depends only on the kernel. Apply the proved Lemma 6.1 to the orthogonality
comparison. This is the finite upper estimate used in Proposition 6.1. -/
theorem exists_principal_sum_le (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ ε : ℝ,
          0 < ε →
            ∃ Q : ℕ,
              3 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ H : Subgroup (ZMod q)ˣ,
                      H ≠ ⊤ →
                        ∀ x : ℝ,
                          2 ≤ x →
                            ∀ X : ℝ,
                              (∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) →
                                (H.index : ℝ) *
                                    ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
                                      (K.summand (1 : DirichletCharacter ℂ q) x n).re ≤
                                  (K.function (1 / 2)).re * Real.sqrt x +
                                    ((H.index : ℝ) - 1) * ((1 + ε) * Real.log q * K.mass) +
                                    H.index *
                                      (C * (1 + Real.log q * Real.log x / Real.sqrt x)) := by
  exact principal_sum_le_of_lemma61 lemma61 hGRH K

end PseudoPrime.LLS.PaperStatements.MellinKernel
