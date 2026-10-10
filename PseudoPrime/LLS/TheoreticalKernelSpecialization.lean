/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TheoreticalKernelProfiles
public import PseudoPrime.LLS.TriangularKernelIdentities
public import PseudoPrime.LLS.TriangularKernel
public import PseudoPrime.LLS.GammaKernel

/-! # Kernel specializations of Proposition 6.1

The Section 6.2 and 6.3 inequalities follow from the general proposition and
explicit kernel identities. These conditional results preserve the outstanding
analytic inputs rather than supplying them as axioms.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under Proposition 6.1, a positive triangular-kernel parameter and
`lambda=1` give the coefficient inequality of Section 6.2. The concrete kernel
supplies admissibility, transform, mass and endpoint identities. Substitution
into the general proposition isolates the coefficient of `sqrt X`. -/
theorem triangular_kernel_inequality (hp : lls_proposition61) (α : ℝ) (hα : 0 < α)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 1 < h) (ε : ℝ)
    (he : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (q : ℕ) [NeZero q],
        Q ≤ q →
          ∀ H : Subgroup (ZMod q)ˣ,
            H.index = h →
              ∀ X : ℝ,
                0 < X →
                  (∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) →
                  triangularKernelCoefficient h α * Real.sqrt X ≤
                    (1 + ε) * (2 * α * ((h : ℝ) - 1)) * Real.log q := by
  let K := triangularMellinKernel hα
  have hf : K.function = Analysis.triangularMellinFunction α := rfl
  have ht := fun u hu ↦ triangular_transform_of_function K hα hf (u := u) hu
  have hm := triangular_mass_of_function K hα hf
  have hv : (K.function (1 / 2)).re = 4 * (Real.exp (α / 2) - Real.exp (-α / 2)) ^ 2 := by
    rw [hf]
    exact Analysis.triangularMellinFunction_half hα.ne'
  obtain ⟨Q, hQ⟩ := hp hGRH K h hh 1 (by norm_num only) ε he
  have hi :
    (∫ u in (0 : ℝ)..1, (K.transform u).re / Real.sqrt u) = 4 * α - 4 + 4 * Real.exp (-α) := by
    rw [← integral_triangularKernelProfile hα.le]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num only : (0 : ℝ) ≤ 1)
    intro u hu
    exact congrArg (fun r : ℝ ↦ r / Real.sqrt u) (ht u hu.1)
  refine ⟨Q, ?_⟩
  intro q _ hq H hH X hX hprimes
  have hb := hQ q hq H hH X hX hprimes
  rw [hi, hv, hm, Real.sqrt_one] at hb
  unfold triangularKernelCoefficient
  nlinarith only [hb]

/-- Under Proposition 6.1, the constructed gamma kernel and a positive parameter
give the coefficient inequality of Section 6.3. Its admissibility, transform,
and endpoint value are proved. The mass remains the actual kernel mass. -/
theorem gamma_kernel_inequality (hp : lls_proposition61)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 1 < h) (lambda : ℝ)
    (hl : 0 < lambda) (ε : ℝ) (he : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (q : ℕ) [NeZero q],
        Q ≤ q →
          ∀ H : Subgroup (ZMod q)ˣ,
            H.index = h →
              ∀ X : ℝ,
                0 < X →
                  (∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) →
                  ((h : ℝ) - 1 - h * Real.exp (-lambda)) * Real.sqrt X ≤
                    (1 + ε) * Real.sqrt lambda * ((h : ℝ) - 1) * Real.log q *
                      gammaMellinKernel.mass := by
  have hK : gammaMellinKernel.function = fun s : ℂ ↦ Complex.Gamma (s + 1 / 2) := rfl
  have hv := gamma_endpoint_of_function gammaMellinKernel hK
  have hi :
    (∫ u in (0 : ℝ)..lambda, (gammaMellinKernel.transform u).re / Real.sqrt u) =
      1 - Real.exp (-lambda) := by
    rw [← integral_gammaKernelProfile hl]
    apply intervalIntegral.integral_congr_Ioo_of_le hl.le
    intro u hu
    exact
      congrArg (fun r : ℝ ↦ r / Real.sqrt u) (gamma_transform_of_function gammaMellinKernel hK hu.1)
  obtain ⟨Q, hQ⟩ := hp hGRH gammaMellinKernel h hh lambda hl ε he
  refine ⟨Q, ?_⟩
  intro q _ hq H hH X hX hprimes
  have hb := hQ q hq H hH X hX hprimes
  rw [hi, hv] at hb
  nlinarith only [hb]

/-- Under Proposition 6.1, the constructed triangular kernel and index at least
28 gives the squared endpoint bound of Section 6.2, with explicit relative
error. Specialize the parameter to half the logarithm of twice the index,
then apply the positive coefficient estimate. This supplies the cutoff
bound used to control the least outside prime. -/
theorem triangular_large_index_cutoff_bound (hp : lls_proposition61) (h : ℕ) (hh : 28 ≤ h)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (ε : ℝ) (he : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (q : ℕ) [NeZero q],
        Q ≤ q →
          ∀ H : Subgroup (ZMod q)ˣ,
            H.index = h →
              ∀ X : ℝ,
                0 < X →
                  (∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) →
                  X ≤
                    (((1 + ε) * Real.log (2 * (h : ℝ)) * ((h : ℝ) - 1) * Real.log q) /
                        (2 * (h : ℝ) * (Real.log (2 * (h : ℝ)) - 4))) ^
                      2 := by
  have hhR : (28 : ℝ) ≤ h := by exact_mod_cast hh
  have hlog := four_lt_log_two_mul hhR
  have ha : 0 < Real.log (2 * (h : ℝ)) / 2 := by linarith only [hlog]
  have hh1 : 1 < h := lt_of_lt_of_le (by norm_num only) hh
  obtain ⟨Q, hQ⟩ := triangular_kernel_inequality hp _ ha hg h hh1 ε he
  refine ⟨max Q 2, ?_⟩
  intro q _ hq H hH X hX hpr
  have hq2 : 2 ≤ q := (le_max_right Q 2).trans hq
  have hql : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq2)
  have hi := hQ q ((le_max_left Q 2).trans hq) H hH X hX hpr
  have hi' :
    triangularKernelCoefficient h (Real.log (2 * (h : ℝ)) / 2) * Real.sqrt X ≤
      (1 + ε) * Real.log (2 * (h : ℝ)) * ((h : ℝ) - 1) * Real.log q := by
    calc
      _ ≤ _ := hi
      _ = _ := by ring
  apply triangular_kernel_bound_of_large_index hhR hX.le _ hi'
  have hhpos : 0 ≤ (h : ℝ) - 1 := by linarith only [hhR]
  exact
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith only [he]) (by linarith only [hlog])) hhpos)
      hql.le

end PseudoPrime.LLS.PaperStatements
