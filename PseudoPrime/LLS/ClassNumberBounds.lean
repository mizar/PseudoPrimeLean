/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements
public import PseudoPrime.LLS.LValueNumerics
public import Mathlib.Tactic
public import PseudoPrime.NumberTheory.PrimePowerIdealNormCount
public import PseudoPrime.AnalyticNumberTheory.NumberField.DedekindLFunction

/-!
# Explicit class-number bounds for imaginary quadratic fields

The class-number formula transfers the upper L-value bound and reciprocal L-value bound
to the two inequalities of Corollary 1.3. Ideal-count and prime-splitting hypotheses give
arithmetic interfaces for constructing the matching primitive character.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a number field, positive q and a character modulo q, transfer both
explicit L-value bounds to the class number, assuming the identity
h_K=sqrt q norm(L(1,chi))/pi. Positivity of the actual class number forces a
positive L-value norm; invert the reciprocal inequality and rescale both bounds.
This algebraic transfer is used after the class-number identity and the L-value
bounds have been established for the matching character in Corollary 1.3. -/
theorem classNumber_bounds_of_LValue_bounds (q : ℕ) [NeZero q] (K : Type) [Field K] [NumberField K]
    (χ : DirichletCharacter ℂ q) (hq : 0 < q)
    (hformula : (NumberField.classNumber K : ℝ) = Real.sqrt q / Real.pi * ‖χ.LFunction 1‖)
    (hb :
      ‖χ.LFunction 1‖ ≤ 2 * Real.exp Real.eulerMascheroniConstant * lValueUpperFactor q ∧
        1 / ‖χ.LFunction 1‖ ≤
          12 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2 * lValueReciprocalFactor q) :
    Real.pi / (12 * Real.exp Real.eulerMascheroniConstant) * Real.sqrt q *
          (lValueReciprocalFactor q)⁻¹ ≤
        (NumberField.classNumber K : ℝ) ∧
      (NumberField.classNumber K : ℝ) ≤
        2 * Real.exp Real.eulerMascheroniConstant / Real.pi * Real.sqrt q *
          lValueUpperFactor q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hf0 : 0 < Real.sqrt q / Real.pi := div_pos (Real.sqrt_pos.mpr hqR) Real.pi_pos
  have hc0 : (0 : ℝ) < NumberField.classNumber K := by exact_mod_cast NumberField.classNumber_pos K
  have hL0 : 0 < ‖χ.LFunction 1‖ := by
    by_contra h
    have hn := mul_nonpos_of_nonneg_of_nonpos hf0.le (le_of_not_gt h)
    rw [← hformula] at hn
    exact (not_le_of_gt hc0) hn
  have hm := mul_le_mul_of_nonneg_left hb.1 hf0.le
  have hpos :
    0 < 12 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2 * lValueReciprocalFactor q :=
    (div_pos (by norm_num only : (0 : ℝ) < 1) hL0).trans_le hb.2
  have hW : lValueReciprocalFactor q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  have hinv := one_div_le_one_div_of_le (div_pos (by norm_num only : (0 : ℝ) < 1) hL0) hb.2
  rw [one_div_one_div] at hinv
  have hlow := mul_le_mul_of_nonneg_left hinv hf0.le
  rw [← hformula] at hlow hm
  constructor
  · convert hlow using 1
    field_simp [Real.pi_ne_zero, Real.exp_ne_zero Real.eulerMascheroniConstant, hW]
  · convert hm using 1
    ring

/-- Under GRH, a primitive character whose divisor sum counts integral ideals
of positive norm gives the bounds of Corollary 1.3 for the specified quadratic
field and q ≥ 10^10. Derive factorization and the residue identity from the
coefficient formula, then apply Theorem 1.5 and the specialized class-number
formula. The assumed coefficient identity connects the field to the character. -/
theorem imaginaryQuadratic_classNumber_bounds_of_ideal_count (q : ℕ) [NeZero q] (hq : 10 ^ 10 ≤ q)
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 2)
    (hd : NumberField.discr K = -(q : ℤ)) (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (hc :
      ∀ n : ℕ,
        n ≠ 0 →
          (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n } : ℂ) =
            ∑ p ∈ n.divisorsAntidiagonal, χ (p.2 : ℕ))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    Real.pi / (12 * Real.exp Real.eulerMascheroniConstant) * Real.sqrt q *
          (lValueReciprocalFactor q)⁻¹ ≤
        (NumberField.classNumber K : ℝ) ∧
      (NumberField.classNumber K : ℝ) ≤
        2 * Real.exp Real.eulerMascheroniConstant / Real.pi * Real.sqrt q *
          lValueUpperFactor q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 10 ^ 10) hq
  have hq4 : 4 < q := lt_of_lt_of_le (by norm_num only : (4 : ℕ) < 10 ^ 10) hq
  have hq3 : 3 ≤ q := le_trans (by norm_num only : (3 : ℕ) ≤ 10 ^ 10) hq
  have hL :=
    AnalyticNumberTheory.norm_LFunction_one_eq_dedekindZeta_residue_of_ideal_count K χ
      (primitiveCharacter_ne_one_of_three_le hq3 hp) hc
  exact
    classNumber_bounds_of_LValue_bounds q K χ hq0
      (AnalyticNumberTheory.imaginaryQuadratic_classNumber_formula_of_residue q hq4 K hdeg hd χ hL)
      ⟨lValue_upper_bound χ hq hp hGRH, lValue_reciprocal_bound χ hq hp hGRH⟩

/-- Given a primitive character whose divisor sum counts integral ideals in each
imaginary quadratic field of discriminant `-q` and `q ≥ 10^10`, prove Corollary 1.3.
Take the character and use the coefficient-to-class-number bound. Factorization,
residue identification and the numerical bounds follow from the coefficient identity.
This interface converts an arithmetic character construction to the numbered statement. -/
theorem lls_corollary13_of_ideal_count
    (hcount :
      ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [NumberField K],
        10 ^ 10 ≤ q →
          Module.finrank ℚ K = 2 →
          NumberField.discr K = -(q : ℤ) →
          ∃ χ : DirichletCharacter ℂ q,
            χ.IsPrimitive ∧
              ∀ n : ℕ,
                n ≠ 0 →
                  (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n } :
                      ℂ) =
                    ∑ p ∈ n.divisorsAntidiagonal, χ (p.2 : ℕ)) :
    lls_corollary13 := by
  intro hGRH q K _ _ hq hdeg hd
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 10 ^ 10) hq
  let : NeZero q := ⟨Nat.ne_of_gt hq0⟩
  obtain ⟨χ, hp, hc⟩ := hcount q K hq hdeg hd
  exact imaginaryQuadratic_classNumber_bounds_of_ideal_count q hq K hdeg hd χ hp hc hGRH

/-- If each imaginary quadratic field has a primitive character whose values agree
with the splitting of every rational prime, prove Corollary 1.3 as originally stated.
The local splitting condition gives the prime-power ideal counts; multiplicativity
extends them to all positive norms. The existing coefficient-to-class-number proof
then supplies factorization, the residue formula, and the bounds of Theorem 1.5.
The splitting-character hypothesis is the arithmetic input to this interface. -/
theorem lls_corollary13_of_prime_splitting
    (hsplit :
      ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [NumberField K],
        10 ^ 10 ≤ q →
          Module.finrank ℚ K = 2 →
          NumberField.discr K = -(q : ℤ) →
          ∃ χ : DirichletCharacter ℂ q,
            χ.IsPrimitive ∧ ∀ p : ℕ, p.Prime → NumberTheory.quadraticPrimeSplittingAt K χ p) :
    lls_corollary13 := by
  apply lls_corollary13_of_ideal_count
  intro q hq K hF hNF hbound hdeg hd
  obtain ⟨χ, hprim, hlocal⟩ := hsplit q K hbound hdeg hd
  exact ⟨χ, hprim, NumberTheory.ideal_count_eq_divisor_sum_of_splitting K χ hlocal⟩

end PseudoPrime.LLS.PaperStatements
