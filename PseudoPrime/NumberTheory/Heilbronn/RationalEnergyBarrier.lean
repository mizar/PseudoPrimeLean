/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalEnergyScales

/-! # The necessary exponent gap for the current rational energy method -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For natural scale parameters b+d=2a, the height injectivity condition
dm<a and the leading energy balance force 13a<7b. Multiply the opposite
gap by m and combine the two budgets. This is a restriction of the current
method, not a lower bound for the least Fermat or Miller-Rabin witness. -/
theorem thirteen_sevenths_gap_of_leading_energy_balance {a b d m : ℕ} (hscale : b + d = 2 * a)
    (hinj : d * m < a) (henergy : 7 * (a * m) + 2 * (d * m) + a < 4 * (b * m)) :
    13 * a < 7 * b := by
  by_contra hgap
  have hd : a ≤ 7 * d := by nlinarith only [hscale, Nat.le_of_not_gt hgap]
  have hm := Nat.mul_le_mul_right m hd
  have hs := congrArg (fun x : ℕ ↦ x * m) hscale
  nlinarith only [hm, hs, hinj, henergy]

/-- For all natural parameters, the full congruence height exponent contains
the pair-count contribution 2nmr. The divisor and quotient losses are
nonnegative. This extracts the unavoidable part of the current budget. -/
theorem pair_count_le_congruencePolynomialHeightExponent (m n r : ℕ) :
    2 * (n * m * r) ≤ congruencePolynomialHeightExponent m n r := by
  simp only [congruencePolynomialHeightExponent, Nat.add_assoc]
  exact Nat.le_add_right _ _

/-- Any natural parameters meeting the full current polynomial energy
balance and height injectivity at b+d=2a must satisfy 13a<7b. Drop only
nonnegative height losses, cancel nr and apply the leading-budget barrier.
Thus allowing arbitrary m,n,r cannot bypass the same exponent gap. -/
theorem thirteen_sevenths_gap_of_polynomial_energy_balance {a b d m n r : ℕ}
    (hscale : b + d = 2 * a) (hinj : d * (2 * m) < 2 * a)
    (hbalance :
      a * (7 * (n * m * r)) + d * congruencePolynomialHeightExponent m n r + a * (n * r) <
        b * (4 * (n * m * r))) :
    13 * a < 7 * b := by
  have hi : d * m < a := by nlinarith only [hinj]
  have hh := Nat.mul_le_mul_left d (pair_count_le_congruencePolynomialHeightExponent m n r)
  have he : (n * r) * (7 * (a * m) + 2 * (d * m) + a) < (n * r) * (4 * (b * m)) := by
    nlinarith only [hh, hbalance]
  exact thirteen_sevenths_gap_of_leading_energy_balance hscale hi (Nat.lt_of_mul_lt_mul_left he)

/-- For b<2a, some positive polynomial parameters m,n,r satisfy the current
height and energy conditions exactly when 13a<7b. The forward direction
allows every m; the reverse direction reuses the certified choice m=7.
This identifies precisely the parameter-optimization range of this method. -/
theorem exists_polynomial_energy_parameters_iff {a b : ℕ} (hsmall : b < 2 * a) :
    (∃ m n r : ℕ,
        0 < m ∧
          0 < n ∧
          0 < r ∧
          (2 * a - b) * (2 * m) < 2 * a ∧
          a * (7 * (n * m * r)) + (2 * a - b) * congruencePolynomialHeightExponent m n r +
              a * (n * r) <
            b * (4 * (n * m * r))) ↔
      13 * a < 7 * b := by
  constructor
  · rintro ⟨m, n, r, _, _, _, hinj, hbalance⟩
    exact
      thirteen_sevenths_gap_of_polynomial_energy_balance (Nat.add_sub_of_le hsmall.le) hinj hbalance
  · intro hgap
    obtain ⟨n, r, hn, hr, hinj, hbalance⟩ := exists_rational_energy_parameters hgap hsmall
    exact ⟨7, n, r, by decide, hn, hr, hinj, hbalance⟩

end PseudoPrime.NumberTheory.Heilbronn
