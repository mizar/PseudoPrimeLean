/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.PolynomialCongruenceGrowth

/-! # Natural power scales for weighted Heilbronn energy comparisons -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The natural coefficient of the full-congruence polynomial, independent of p,H.
Collect the fixed numerical, divisor and quotient-growth constants
without evaluating their values. -/
def congruencePolynomialCoefficient (m n r : ℕ) : ℕ :=
  144 ^ (n * m * r) * divisorPowerBoundConstant r ^ (2 * (n * m)) *
    quotientPowerBoundConstant r ^ (n ^ 2 * (m - 1))

/-- The total natural exponent of H in the full-congruence polynomial.
Separate the pair-count height, divisor loss and quotient loss for later exponent comparisons. -/
def congruencePolynomialHeightExponent (m n r : ℕ) : ℕ :=
  2 * (n * m * r) + ((m - 1) * m) * r + 2 * (n * m) + ((2 * m) * 2) * (n ^ 2 * (m - 1))

/-- The natural coefficient after inserting the energy-square bound in the count polynomial.
It depends only on m,n,r and retains all fixed constants symbolically. -/
def congruenceEnergyCoefficient (m n r : ℕ) : ℕ :=
  18874370 ^ (n * m * r) * congruencePolynomialCoefficient m n r

/-- Factor the full-congruence bound into its fixed coefficient, total H power and p-1 power.
Use natural power identities without evaluating the coefficients. -/
theorem congruenceCountPolynomialBound_factor (p H m n r : ℕ) :
    congruenceCountPolynomialBound p H m n r =
      congruencePolynomialCoefficient m n r * H ^ congruencePolynomialHeightExponent m n r *
        (p - 1) ^ (n * r) := by
  simp only [congruenceCountPolynomialBound, congruencePolynomialCoefficient,
    congruencePolynomialHeightExponent, mul_pow, pow_add, ← pow_mul, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm]

/-- Factor the product of the energy bound and count polynomial, separating p,H from its
fixed coefficient. This is the input to the power-scale comparison. -/
theorem congruence_energy_polynomial_factor (p H m n r : ℕ) :
    (18874370 * p ^ 7) ^ (n * m * r) * congruenceCountPolynomialBound p H m n r =
      congruenceEnergyCoefficient m n r * p ^ (7 * (n * m * r)) *
        H ^ congruencePolynomialHeightExponent m n r *
        (p - 1) ^ (n * r) := by
  rw [congruenceCountPolynomialBound_factor, congruenceEnergyCoefficient]
  simp only [mul_pow, ← pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Under H^a at most p^d, bound the a-th power of the energy polynomial by its coefficient
to the a-th power times p to an explicit exponent. The height contributes d times its exponent. -/
theorem congruence_energy_power_le_of_height {p H m n r a d : ℕ} (hH : H ^ a ≤ p ^ d) :
    ((18874370 * p ^ 7) ^ (n * m * r) * congruenceCountPolynomialBound p H m n r) ^ a ≤
      congruenceEnergyCoefficient m n r ^ a *
        p ^
          (a * (7 * (n * m * r)) + d * congruencePolynomialHeightExponent m n r + a * (n * r)) := by
  have hh := Nat.pow_le_pow_left hH (congruencePolynomialHeightExponent m n r)
  have hp := Nat.pow_le_pow_left (Nat.sub_le p 1) (a * (n * r))
  have ht :=
    Nat.mul_le_mul
      (Nat.mul_le_mul_left (congruenceEnergyCoefficient m n r ^ a * p ^ (a * (7 * (n * m * r)))) hh)
      hp
  rw [congruence_energy_polynomial_factor]
  simpa only [mul_pow, pow_add, ← pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht

/-- For p greater than 1 and positive a, X^a at most A^a*p^e, A^a less than p,
e less than b*c, and p^b at most k^a imply X less than k^c.
Absorb the fixed coefficient in one p power and compare positive natural powers. -/
theorem power_gap_of_monomial_bound {p k a b c e A X : ℕ} (hp : 1 < p) (ha : 0 < a)
    (hcut : p ^ b ≤ k ^ a) (hX : X ^ a ≤ A ^ a * p ^ e) (hcoefficient : A ^ a < p)
    (hbalance : e < b * c) : X < k ^ c := by
  apply (Nat.pow_lt_pow_iff_left (ne_of_gt ha)).mp
  have hp0 : 0 < p := lt_trans (by decide : 0 < 1) hp
  have hconst := Nat.mul_lt_mul_of_pos_right hcoefficient (Nat.pow_pos (n := e) hp0)
  have hpow := Nat.pow_le_pow_right hp0 hbalance
  have hkpow := Nat.pow_le_pow_left hcut c
  calc
    _ ≤ _ := hX
    _ < p * p ^ e := hconst
    _ = p ^ (e + 1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ p ^ (b * c) := hpow
    _ ≤ _ := by simpa only [← pow_mul, Nat.mul_comm] using hkpow

/-- For positive a and p greater than 1, H^a at most p^d and d*b less than 2a imply
H^b less than p^2. Raise the height inequality to b and compare a-th powers. -/
theorem power_height_injectivity {H p a b d : ℕ} (ha : 0 < a) (hp : 1 < p) (hpow : H ^ a ≤ p ^ d)
    (hexponent : d * b < 2 * a) : H ^ b < p ^ 2 := by
  have hle : (H ^ b) ^ a ≤ p ^ (d * b) := by
    simpa only [← pow_mul, Nat.mul_comm] using Nat.pow_le_pow_left hpow b
  have hlt := Nat.pow_lt_pow_right hp hexponent
  have hfinal : (H ^ b) ^ a < (p ^ 2) ^ a := by simpa only [← pow_mul] using hle.trans_lt hlt
  exact (Nat.pow_lt_pow_iff_left (ne_of_gt ha)).mp hfinal

/-- For positive p and b at most d*a, p^b at most k^a implies floor(p^d/k)^a at most p^(d*a-b).
Raise floor division, multiply the cutoff bound and cancel the positive p power. -/
theorem floor_power_budget {p k d a b : ℕ} (hp : 0 < p) (hbalance : b ≤ d * a)
    (hcut : p ^ b ≤ k ^ a) : (p ^ d / k) ^ a ≤ p ^ (d * a - b) := by
  have h1 := Nat.pow_le_pow_left (Nat.div_mul_le_self (p ^ d) k) a
  rw [mul_pow, ← pow_mul] at h1
  have h2 := Nat.mul_le_mul_left ((p ^ d / k) ^ a) hcut
  have ht := h2.trans h1
  have he : p ^ (d * a) = p ^ (d * a - b) * p ^ b := by rw [← pow_add, Nat.sub_add_cancel hbalance]
  rw [he] at ht
  exact Nat.le_of_mul_le_mul_right ht (Nat.pow_pos hp)

/-- The fixed energy coefficient for an arbitrary natural multiplier M on p*E*N.
Multiply the previous coefficient by M^(2*n*m*r), independent of p,H,k.
This retains any fixed strictness constant needed by a later Fourier argument. -/
def weightedCongruenceEnergyCoefficient (M m n r : ℕ) : ℕ :=
  M ^ (2 * (n * m * r)) * congruenceEnergyCoefficient m n r

/-- Under H^a at most p^d, the weighted energy polynomial has the same p-exponent bound.
The arbitrary fixed multiplier changes its coefficient, not the height or exponent balance. -/
theorem weighted_congruence_energy_power_le_of_height {p H M m n r a d : ℕ} (hH : H ^ a ≤ p ^ d) :
    ((M ^ 2 * 18874370 * p ^ 7) ^ (n * m * r) * congruenceCountPolynomialBound p H m n r) ^ a ≤
      weightedCongruenceEnergyCoefficient M m n r ^ a *
        p ^
          (a * (7 * (n * m * r)) + d * congruencePolynomialHeightExponent m n r + a * (n * r)) := by
  have he :
    (M ^ 2 * 18874370 * p ^ 7) ^ (n * m * r) * congruenceCountPolynomialBound p H m n r =
      M ^ (2 * (n * m * r)) *
        ((18874370 * p ^ 7) ^ (n * m * r) * congruenceCountPolynomialBound p H m n r) := by
    simp only [mul_pow, ← pow_mul, Nat.mul_assoc]
  rw [he, mul_pow]
  have ht :=
    Nat.mul_le_mul_left ((M ^ (2 * (n * m * r))) ^ a)
      (congruence_energy_power_le_of_height (m := m) (n := n) (r := r) hH)
  simpa only [weightedCongruenceEnergyCoefficient, mul_pow, Nat.mul_assoc] using ht

/-- For odd prime p, positive height and power parameters, subgroup injectivity and power
scales H^a at most p^d and p^b at most k^a, coefficient absorption and the explicit balance
yield M*p*energy*fullCount less than k^2. Combine the generic polynomial comparison with
the proved energy and full-count bounds; no count estimate is supplied as a premise. -/
theorem weighted_energy_budget_of_power_scales {p H M m n r a b d k : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hH : 0 < H) (hm : 0 < m) (hn : 0 < n) (hr : 0 < r) (ha : 0 < a) (hp : 1 < p)
    (hmod : H ^ (2 * m) < p ^ 2) (hheight : H ^ a ≤ p ^ d) (hcut : p ^ b ≤ k ^ a)
    (hcoefficient : weightedCongruenceEnergyCoefficient M m n r ^ a < p)
    (hbalance :
      a * (7 * (n * m * r)) + d * congruencePolynomialHeightExponent m n r + a * (n * r) <
        b * (4 * (n * m * r))) :
    (M * p) * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  apply
    counting_budget_of_even_power (Nat.mul_pos (Nat.mul_pos hn hm) hr)
      (heilbronnEnergy_square_le_uniform hodd)
      (boundedCongruenceCount_power_le_polynomial hodd hH hm hn hr hmod)
  have he : (M * p) ^ 2 * (18874370 * p ^ 5) = M ^ 2 * 18874370 * p ^ 7 := by ring
  rw [he]
  exact
    power_gap_of_monomial_bound hp ha hcut (weighted_congruence_energy_power_le_of_height hheight)
      hcoefficient hbalance

end PseudoPrime.NumberTheory.Heilbronn
