/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrincipalRampEndpointBounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import PseudoPrime.LLS.Phase64Scale1700JacobiBudget

/-! # Harmonic-scale interpolation without additional arithmetic certificates -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: nonnegative weights summing to one and an affine reciprocal-scale
identity. Claim: each exponential atom is below the weighted endpoint atoms.
Apply convexity of exp after rewriting its argument. Role: interpolate positive
Laplace sums without evaluating any new scale. -/
theorem exponential_atom_le_harmonic_chord {x y z a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hscale : 1 / z = a / x + b / y) (n : ℕ) :
    Real.exp (-(n : ℝ) / z) ≤ a * Real.exp (-(n : ℝ) / x) + b * Real.exp (-(n : ℝ) / y) := by
  have he := convexOn_exp.2 (Set.mem_univ (-(n : ℝ) / x)) (Set.mem_univ (-(n : ℝ) / y)) ha hb hab
  have hh : a * (-(n : ℝ) / x) + b * (-(n : ℝ) / y) = -(n : ℝ) / z := by
    calc
      _ = -(n : ℝ) * (a / x + b / y) := by ring
      _ = _ := by
        rw [← hscale]; ring
  simpa only [smul_eq_mul, hh] using he

/-- Input: positive endpoint and interior scales, nonnegative weights summing
to one, and 1/z = a/x + b/y. Claim: the actual principal exponential mass at z
is below the endpoint chord. Sum the atom inequalities with nonnegative Mangoldt
weights using summability. Role: retain position dependence inside a scale cell. -/
theorem principalExponentialMass_le_harmonic_chord {x y z a b : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hscale : 1 / z = a / x + b / y) :
    principalExponentialMass z ≤
      a * principalExponentialMass x + b * principalExponentialMass y := by
  have hsx := (summable_principalExponentialMass hx).mul_left a
  have hsy := (summable_principalExponentialMass hy).mul_left b
  have ht :=
    Summable.tsum_le_tsum
      (fun (n : ℕ) ↦
        show
          Real.exp (-(n : ℝ) / z) * ArithmeticFunction.vonMangoldt n ≤
            a * (Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n) +
              b * (Real.exp (-(n : ℝ) / y) * ArithmeticFunction.vonMangoldt n)
          from by
          have hm :=
            mul_le_mul_of_nonneg_right (exponential_atom_le_harmonic_chord ha hb hab hscale n)
              (ArithmeticFunction.vonMangoldt_nonneg (n := n))
          nlinarith only [hm])
      (summable_principalExponentialMass hz) (hsx.add hsy)
  simpa only [principalExponentialMass, hsx.tsum_add hsy, tsum_mul_left] using ht

/-- Input: endpoint mass upper bounds, a ramp lower bound at x <= z, harmonic
weights, and nonnegative numerator lower bound C. Claim: C/R bounds the actual
principal-ramp difference below when sqrt(z) <= R. Combine ramp monotonicity
and the mass chord before dividing. Role: reuse endpoint arithmetic certificates
in the strict gap required for Jacobi witness extraction. -/
theorem principalRampDifference_lower_of_harmonic_chord {x y z a b A P Q C R : ℝ} (hx : 0 < x)
    (hy : 0 < y) (hxz : x ≤ z) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hscale : 1 / z = a / x + b / y)
    (hA : A ≤ AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x)
    (hP : principalExponentialMass x ≤ P) (hQ : principalExponentialMass y ≤ Q)
    (hC : C ≤ 2 * A - (a * P + b * Q)) (hC0 : 0 ≤ C) (hR : Real.sqrt z ≤ R) :
    C / R ≤ principalRampDifference z := by
  have hz := hx.trans_le hxz
  have hm := principalExponentialMass_le_harmonic_chord hx hy hz ha hb hab hscale
  have hp := mul_le_mul_of_nonneg_left hP ha
  have hq := mul_le_mul_of_nonneg_left hQ hb
  have hr := AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum_mono hx hxz
  have hn :
    C ≤
      2 * AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum z -
        principalExponentialMass z := by
    linarith only [hC, hA, hm, hp, hq, hr]
  rw [principalRampDifference_eq_mass hz]
  exact
    (div_le_div_of_nonneg_left hC0 (Real.sqrt_pos.mpr hz) hR).trans
      (div_le_div_of_nonneg_right hn (Real.sqrt_nonneg z))

/-- Under GRH and the transported phase hypotheses, two endpoint mass caps
and one ramp lower bound give an odd-prime negative Jacobi witness whenever
the numerical budget is below the harmonic-chord lower bound C/R. Apply the
interpolated principal-ramp estimate to the existing witness extraction theorem.
Role: use compact endpoint data throughout a scale cell without new finite sums. -/
theorem exists_odd_prime_negative_of_harmonic_transported_gap {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b L : ℝ} (hlo : 1600 ≤ x)
    (hhi : x ≤ 1700) (hb : 500 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x) (hLlo : 64 ≤ L)
    (hLhi : L ≤ 64001 / 1000) (δ : ℚ) (hd : |Real.log x - Real.log (L ^ 2 / (99 / 40))| ≤ (δ : ℝ))
    {a0 a1 u v A P Q C R : ℝ} (ha0 : 0 < a0) (ha1 : 0 < a1) (ha0x : a0 ≤ x) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (huv : u + v = 1) (hscale : 1 / x = u / a0 + v / a1)
    (hA : A ≤ AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum a0)
    (hP : principalExponentialMass a0 ≤ P) (hQ : principalExponentialMass a1 ≤ Q)
    (hC : C ≤ 2 * A - (u * P + v * Q)) (hC0 : 0 ≤ C) (hR : Real.sqrt x ≤ R)
    (hgap : phase64TransportedNumericalBudget n q x δ < C / R) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  have hc :=
    principalRampDifference_lower_of_harmonic_chord ha0 ha1 ha0x hu hv huv hscale hA hP hQ hC hC0 hR
  exact
    exists_odd_prime_negative_of_transported_phase64_numerical_gap_1700 bridge hGRH hq hmq hlo hhi
      hb hbx hLlo hLhi δ hd (hgap.trans_le hc)

end PseudoPrime.LLS
