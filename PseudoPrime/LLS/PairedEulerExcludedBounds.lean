/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleGammaCharacterBounds
public import PseudoPrime.LLS.QuadraticExcludedBudget

/-! # Paired Euler savings with a combined quadratic exclusion budget -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For weights supported on Mangoldt indices below the prime-triviality cutoff,
the paired character sum equals twice the principal sum minus the exact excluded
defect. Rearrange the weighted defect identity without positivity assumptions. -/
theorem paired_weighted_sum_eq_of_ambient_trivial {q N : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hw : ∀ n ∈ S, ArithmeticFunction.vonMangoldt n = 0 → w n = 0)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    (∑ n ∈ S, (1 + (χ n).re) * w n) = 2 * (∑ n ∈ S, w n) - excludedCharacterDefect χ N S w := by
  have he := weighted_defect_eq_excluded_of_ambient_trivial χ S w hS hw ht
  have hs : (∑ n ∈ S, (1 + (χ n).re) * w n) = (∑ n ∈ S, w n) + (∑ n ∈ S, (χ n).re * w n) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  linarith only [he, hs]

/-- For a quadratic character under prime triviality, nonnegative Mangoldt weights
give a paired-sum lower bound with the structural exclusion budget. Combine the
exact identity and square cancellation. No RH or primitivity is required. -/
theorem paired_weighted_sum_ge_quadratic_budget {q N : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) {b : ℝ} (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hw : ∀ n ∈ S, ArithmeticFunction.vonMangoldt n = 0 → w n = 0) (hw0 : ∀ n ∈ S, 0 ≤ w n)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    2 * (∑ n ∈ S, w n) - quadraticExcludedBudget q N S w ≤ (∑ n ∈ S, (1 + (χ n).re) * w n) := by
  rw [paired_weighted_sum_eq_of_ambient_trivial χ S w hS hw ht]
  exact sub_le_sub_left (excludedCharacterDefect_le_quadratic_budget χ hquad N S w hw0) _

end PseudoPrime.AnalyticNumberTheory.Arithmetic

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Combine two real-axis Euler weights before charging excluded prime powers.
The parameters are two exponents and the coefficient of the logarithmic term.
This weight retains both savings from the signed two-pole zero-mass comparison. -/
noncomputable def pairedEulerPrefixWeight (σ τ c : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ +
    c * Real.log n * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ

/-- For nonnegative logarithmic coefficient, the combined Euler weight is
nonnegative at every natural index. Each Mangoldt, logarithm and power factor has
the required sign. This permits the quadratic structural exclusion estimate. -/
theorem pairedEulerPrefixWeight_nonneg (σ τ : ℝ) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ pairedEulerPrefixWeight σ τ c n := by
  exact
    add_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ))
      (div_nonneg
        (mul_nonneg (mul_nonneg hc (Real.log_natCast_nonneg n))
          ArithmeticFunction.vonMangoldt_nonneg)
        (Real.rpow_nonneg (Nat.cast_nonneg n) τ))

/-- If the Mangoldt value vanishes, the combined Euler weight vanishes for any
real parameters. This discharges the support premise in the exact defect identity. -/
theorem pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero (σ τ c : ℝ) {n : ℕ}
    (hn : ArithmeticFunction.vonMangoldt n = 0) : pairedEulerPrefixWeight σ τ c n = 0 := by
  simp only [pairedEulerPrefixWeight, hn, zero_div, mul_zero, add_zero]

/-- For any finite support, combine the ordinary and logarithmic paired Euler
prefixes into one weighted sum. Distribute finite sums and multiply algebraically.
This avoids bounding the two excluded-support costs separately. -/
theorem paired_euler_prefixes_eq_weight {q : ℕ} (χ : DirichletCharacter ℂ q) (σ τ c : ℝ)
    (S : Finset ℕ) :
    (∑ n ∈ S, DirichletLFunction.realPairedEulerTerm χ σ n) +
        c * (∑ n ∈ S, Real.log n * DirichletLFunction.realPairedEulerTerm χ τ n) =
      ∑ n ∈ S, (1 + (χ n).re) * pairedEulerPrefixWeight σ τ c n := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only [DirichletLFunction.realPairedEulerTerm, pairedEulerPrefixWeight]
  ring

end PseudoPrime.AnalyticNumberTheory.Arithmetic

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For primitive nonprincipal quadratic individual-RH data, prime triviality below
an ambient cutoff bounds the convergent Gamma zero mass by a principal finite sum
and its quadratic exclusion budget. Combine the signed two-pole profile with the
weighted defect identity. The exclusion modulus need not equal the conductor. -/
theorem gamma_zeroMass_le_twoPole_quadratic_budget {q N : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {b : ℝ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, (n : ℝ) ≤ b) (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    Summable
        (fun ρ : ℂ ↦
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ∧
      (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ≤
        Real.log q / 2 + 419 / 50 -
            2 * (∑ n ∈ S, Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n) +
          Arithmetic.quadraticExcludedBudget q N S
            (Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) := by
  have h := gamma_zeroMass_le_twoPole_rational_retained hq hRH hp hne hinv S S
  have he := Arithmetic.paired_euler_prefixes_eq_weight χ (5 / 4) (11 / 4) (3 / 4) S
  have hb :=
    Arithmetic.paired_weighted_sum_ge_quadratic_budget χ hquad S
      (Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) hS
      (fun n _ hn ↦ Arithmetic.pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero _ _ _ hn)
      (fun n _ ↦ Arithmetic.pairedEulerPrefixWeight_nonneg _ _ (by norm_num only) n) ht
  refine ⟨h.1, ?_⟩
  linarith only [h.2, he, hb]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.DirichletLFunction AnalyticNumberTheory.Arithmetic in
/-- For primitive nonprincipal quadratic GRH data of modulus at least eight, prime
triviality gives a Gamma arithmetic upper bound with one combined exclusion cost.
Use the retained-prefix comparison and the same-modulus explicit remainder.
This supplies the upper side of a finite-scale witness contradiction. -/
theorem gamma_primitive_sum_re_le_twoPole_quadratic_budget {q N : ℕ} [NeZero q] (hq : 8 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x b : ℝ}
    (hx : 1 ≤ x) (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      Real.log q / 2 + 419 / 50 -
          2 * (∑ n ∈ S, pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n) +
        quadraticExcludedBudget q N S (pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) +
        64 / 9 +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log q + 28) + 1) := by
  have h := gamma_primitive_sum_re_le_twoPole_from_eight hq hGRH hp hne hinv hx S S
  have he := paired_euler_prefixes_eq_weight χ (5 / 4) (11 / 4) (3 / 4) S
  have hb :=
    paired_weighted_sum_ge_quadratic_budget χ hquad S
      (pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) hS
      (fun n _ hn ↦ pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero _ _ _ hn)
      (fun n _ ↦ pairedEulerPrefixWeight_nonneg _ _ (by norm_num only) n) ht
  linarith only [h, he, hb]

end PseudoPrime.LLS.PaperStatements
