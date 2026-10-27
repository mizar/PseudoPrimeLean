/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.CongruenceGrowthBudget
public import PseudoPrime.NumberTheory.Heilbronn.DivisorPowerBounds

/-! # Polynomial full-congruence bounds and the energy comparison -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The explicit polynomial bound in p,H for the 2*n*m*r-th power of the full congruence count.
Its coefficients depend only on m,n,r through divisorPowerBoundConstant and
quotientPowerBoundConstant. It contains no divisor counts, logarithms, energies
or unknown counts. -/
def congruenceCountPolynomialBound (p H m n r : ℕ) : ℕ :=
  ((144 * H ^ 2) ^ (n * m * r) * H ^ (((m - 1) * m) * r) * (p - 1) ^ (n * r)) *
    ((divisorPowerBoundConstant r * H) ^ (2 * (n * m)) *
      (quotientPowerBoundConstant r * (H ^ (2 * m)) ^ 2) ^ (n ^ 2 * (m - 1)))

/-- For odd prime p and positive H,m,n,r with H^(2m) less than p^2, bound the actual full
congruence count raised to 2*n*m*r by congruenceCountPolynomialBound.
Raise the proved growth bound to r and replace both divisor and ceiling-logarithmic losses
by their explicit power bounds. All sign and equal-ratio multiplicities have been counted. -/
theorem boundedCongruenceCount_power_le_polynomial {p H m n r : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hH : 0 < H) (hm : 0 < m) (hn : 0 < n) (hr : 0 < r) (hmod : H ^ (2 * m) < p ^ 2) :
    boundedCongruenceCount p H ^ (2 * (n * m * r)) ≤ congruenceCountPolynomialBound p H m n r := by
  have h0 := Nat.pow_le_pow_left (boundedCongruenceCount_power_le_growth_bound hodd hH hm hn hmod) r
  have hd := Nat.pow_le_pow_left (maxDivisorCount_pow_le_explicit H hr) (2 * (n * m))
  have hc :=
    Nat.pow_le_pow_left
      (quotientPowerConstant_pow_le_explicit (U := H ^ (2 * m)) (Nat.pow_pos hH) hr)
      (n ^ 2 * (m - 1))
  have ht :=
    Nat.mul_le_mul_left ((144 * H ^ 2) ^ (n * m * r) * H ^ (((m - 1) * m) * r) * (p - 1) ^ (n * r))
      (Nat.mul_le_mul hd hc)
  have h0' :
    boundedCongruenceCount p H ^ (2 * (n * m * r)) ≤
      ((144 * H ^ 2) ^ (n * m * r) * H ^ (((m - 1) * m) * r) * (p - 1) ^ (n * r)) *
        ((maxDivisorCount H ^ r) ^ (2 * (n * m)) *
          (quotientPowerConstant (H ^ (2 * m)) ^ r) ^ (n ^ 2 * (m - 1))) := by
    simpa only [congruenceCountPowerBound, mul_pow, ← pow_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using h0
  exact h0'.trans ht

/-- Under subgroup injectivity and positive parameters, the explicit polynomial gap
(18874370*p^7)^(n*m*r)*congruenceCountPolynomialBound less than k^(4*n*m*r)
implies p*heilbronnEnergy*fullCount less than k^2. Apply the generic even-power budget
to the unconditional energy bound and the proved polynomial congruence-count estimate. -/
theorem boundedCongruence_energy_budget_of_polynomial {p H m n r k : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hH : 0 < H) (hm : 0 < m) (hn : 0 < n) (hr : 0 < r) (hmod : H ^ (2 * m) < p ^ 2)
    (hgap :
      (18874370 * p ^ 7) ^ (n * m * r) * congruenceCountPolynomialBound p H m n r <
        k ^ (4 * (n * m * r))) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  apply
    counting_budget_of_even_power (Nat.mul_pos (Nat.mul_pos hn hm) hr)
      (heilbronnEnergy_square_le_uniform hodd)
      (boundedCongruenceCount_power_le_polynomial hodd hH hm hn hr hmod)
  have he : p ^ 2 * (18874370 * p ^ 5) = 18874370 * p ^ 7 := by ring
  simpa only [he] using hgap

end PseudoPrime.NumberTheory.Heilbronn
