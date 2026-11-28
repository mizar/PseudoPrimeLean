/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredSeries
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredTail
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Floor

/-! # Computable Bernstein evaluation of the H27 remainder polynomial -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Compute the coefficients of `(d - ∂)² B` from a cached row of profile coefficients. -/
private def remainderCoeff (d : ℚ) (b : ℕ → ℚ) (j : ℕ) : ℚ :=
  centeredCoeff d (centeredCoeff d b) j

/-- The executable second-derivative coefficients give the rational polynomial of H27. -/
private theorem remainder_coeff_eq (K : HighGaussianKernel) (j : ℕ) :
    remainderCoeff (K.pole - 1 / 2) (highProfileCoeff K) j = (highRemainderRatPoly K).coeff j := by
  simp only [remainderCoeff, centeredCoeff, highRemainderRatPoly, Polynomial.coeff_add,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_derivative,
    high_profile_coeff_eq, Nat.cast_add, Nat.cast_one]
  ring

/-- The cached affine evaluation gives the absolute Bernstein average of a polynomial. -/
private theorem remainder_cell_mass_eq (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n) (l w : ℚ) :
    headCellMass n (fun j ↦ P.coeff j) l w Nat.fast_choose =
      w *
        ((∑ k : Fin (n + 1),
            |Analysis.bernsteinRatCoeff (P.comp (Polynomial.C w * Polynomial.X + Polynomial.C l)) n
                k|) /
          ((n : ℚ) + 1)) := by
  rw [head_cell_mass_eq]
  simp only [Analysis.bernsteinRatCoeff, Analysis.rational_affine_coeff _ _ hP,
    ← Nat.choose_eq_fast_choose, ← Fin.sum_univ_eq_sum_range]

/-- Compute the weighted Bernstein charges with shared coefficients and binomial values. -/
private def remainderCharges (K : HighGaussianKernel) (N m : ℕ) (s : ℚ) (p : ℕ → ℚ) : List ℚ :=
  let n := 2 * K.degree + 3
  let compact := headCoeffCache (2 * K.degree + 1) (headCompactCoeff K)
  let choose := headCoeffCache (n + 1) (fun k ↦ headCoeffCache (n + 1) (Nat.fast_choose k))
  let b := headCoeffCache (n + 3) (highProfileFrom K compact)
  let c := headCoeffCache (n + 1) (remainderCoeff (K.pole - 1 / 2) (headCached b))
  List.ofFn fun j : Fin N ↦
    headExpUpper (s * p j) m *
      headCellMass n (fun i ↦ headCached c i) (p j) (p (j + 1) - p j)
        (fun k ↦ headCached (headCached choose k))

/-- Sum the exact Bernstein charges for a rational partition. -/
public def highRemainderBernsteinCharge (K : HighGaussianKernel) (N m : ℕ) (s : ℚ) (p : ℕ → ℚ) :
    ℚ :=
  (remainderCharges K N m s p).sum

/-- The executable sum bounds the absolute H27 integral for a certified rational partition. -/
public theorem high_remainder_integral_le_charge (K : HighGaussianKernel) (N m : ℕ) {s : ℚ}
    (hs : 0 ≤ s) (p : ℕ → ℚ) (hp : ∀ j < N, p j < p (j + 1)) (h0 : ∀ j < N, 0 ≤ p j) :
    let D := (highRemainderRatPoly K).map (Rat.castHom ℝ)
    (∫ x in (p 0 : ℝ)..(p N : ℝ), Real.exp (-(s : ℝ) * x) * |D.eval x|) ≤
      (highRemainderBernsteinCharge K N m s p : ℝ) := by
  let e := fun j ↦ headExpUpper (s * p j) m
  have he (j : ℕ) (hj : j < N) : Real.exp (-(s : ℝ) * (p j : ℝ)) ≤ (e j : ℝ) := by
    simpa only [e, Rat.cast_mul, neg_mul] using head_exp_upper_sound (mul_nonneg hs (h0 j hj)) m
  have h := high_remainder_integral_bernstein K N (Rat.cast_nonneg.mpr hs) p e hp he
  have hb :
    highProfileFrom K (headCoeffCache (2 * K.degree + 1) (headCompactCoeff K)) =
      highProfileCoeff K :=
    rfl
  simpa only [highRemainderBernsteinCharge, remainderCharges, List.sum_ofFn, head_coeff_cache_eq,
    hb, remainder_coeff_eq, remainder_cell_mass_eq _ _ (high_remainder_rat_degree K),
    ← Fin.sum_univ_eq_sum_range, e] using h

/-- Combine the executable finite Bernstein charge with the remaining absolute tail bound. -/
public theorem high_remainder_tail_le_charge (K : HighGaussianKernel) (N m : ℕ) {s : ℚ} (hs : 0 < s)
    (p : ℕ → ℚ) (hp : ∀ j < N, p j < p (j + 1)) (h0 : ∀ j < N, 0 ≤ p j) (ha : 0 ≤ p 0)
    (hab : p 0 ≤ p N) :
    let D := (highRemainderRatPoly K).map (Rat.castHom ℝ)
    let Q := D.comp (Polynomial.X + Polynomial.C (p N : ℝ))
    (∫ t in Set.Ioi (p 0 : ℝ), Real.exp (-(s : ℝ) * t) * |D.eval t|) ≤
      (highRemainderBernsteinCharge K N m s p : ℝ) +
        Real.exp (-(s : ℝ) * (p N : ℝ)) *
          ∑ k ∈ Finset.range (Q.natDegree + 1),
            |Q.coeff k| * ((k.factorial : ℝ) / (s : ℝ) ^ (k + 1)) := by
  exact
    high_remainder_tail_le K (Rat.cast_pos.mpr hs) (Rat.cast_nonneg.mpr ha) (Rat.cast_le.mpr hab)
      (high_remainder_integral_le_charge K N m hs.le p hp h0)

/-- Round each local Bernstein charge up before summing the integer ticks. -/
public def highRemainderChargeTicks (K : HighGaussianKernel) (N m scale : ℕ) (s : ℚ) (p : ℕ → ℚ) :
    ℤ :=
  ((remainderCharges K N m s p).map fun q ↦ ⌈q * (scale : ℚ)⌉).sum

/-- Summing rounded charges bounds the rational sum at any positive scale. -/
private theorem sum_le_charge_ticks (qs : List ℚ) {scale : ℕ} (hscale : 0 < scale) :
    qs.sum ≤ (((qs.map fun q ↦ ⌈q * (scale : ℚ)⌉).sum : ℤ) : ℚ) / (scale : ℚ) := by
  have hs : (0 : ℚ) < (scale : ℚ) := Nat.cast_pos.mpr hscale
  induction qs with
  | nil => simp only [List.sum_nil, List.map_nil, Int.cast_zero, zero_div, le_refl]
  | cons q qs ih =>
    simp only [List.sum_cons, List.map_cons, Int.cast_add, add_div]
    exact add_le_add ((le_div_iff₀ hs).mpr (Int.le_ceil _)) ih

/-- The integral is bounded by an integer sum and a single division by the tick scale. -/
public theorem high_remainder_integral_le_ticks (K : HighGaussianKernel) (N m scale : ℕ)
    (hscale : 0 < scale) {s : ℚ} (hs : 0 ≤ s) (p : ℕ → ℚ) (hp : ∀ j < N, p j < p (j + 1))
    (h0 : ∀ j < N, 0 ≤ p j) :
    let D := (highRemainderRatPoly K).map (Rat.castHom ℝ)
    (∫ x in (p 0 : ℝ)..(p N : ℝ), Real.exp (-(s : ℝ) * x) * |D.eval x|) ≤
      (highRemainderChargeTicks K N m scale s p : ℝ) / (scale : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr (sum_le_charge_ticks (remainderCharges K N m s p) hscale)
  refine (high_remainder_integral_le_charge K N m hs p hp h0).trans ?_
  simpa only [highRemainderBernsteinCharge, highRemainderChargeTicks, Rat.cast_div,
    Rat.cast_intCast, Rat.cast_natCast] using h

/-- Restricting the enumerated charges to a prefix gives the shorter partition computation. -/
private theorem remainder_charges_take (K : HighGaussianKernel) (N m k : ℕ) (s : ℚ) (p : ℕ → ℚ)
    (hk : k ≤ N) : (remainderCharges K N m s p).take k = remainderCharges K k m s p := by
  apply List.ext_getElem?
  intro i
  simp only [remainderCharges, List.getElem?_take, List.getElem?_ofFn]
  by_cases hi : i < k
  · simp only [hi, hi.trans_le hk, dite_true, ite_true]
  · simp only [hi, dite_false, ite_false]

/-- Compute all cumulative integer upper bounds in one traversal of the local charges. -/
private def remainderPrefixTicks (K : HighGaussianKernel) (N m scale : ℕ) (s : ℚ) (p : ℕ → ℚ) :
    List ℤ :=
  ((remainderCharges K N m s p).map fun q ↦ ⌈q * (scale : ℚ)⌉).scanl (· + ·) 0

/-- Read the cumulative upper bound through endpoint index `k` of the partition. -/
public def highRemainderPrefixTicks (K : HighGaussianKernel) (N m scale : ℕ) (s : ℚ) (p : ℕ → ℚ)
    (k : ℕ) : ℤ :=
  ((remainderPrefixTicks K N m scale s p)[k]?).getD 0

/-- A prefix lookup returns the same integer as evaluating only that shorter partition. -/
public theorem high_remainder_prefix_ticks_eq (K : HighGaussianKernel) (N m scale : ℕ) (s : ℚ)
    (p : ℕ → ℚ) {k : ℕ} (hk : k ≤ N) :
    highRemainderPrefixTicks K N m scale s p k = highRemainderChargeTicks K k m scale s p := by
  have hlen : (remainderCharges K N m s p).length = N := by
    simp only [remainderCharges, List.length_ofFn]
  simp only [highRemainderPrefixTicks, remainderPrefixTicks, List.getElem?_scanl, List.length_map,
    hlen, hk, ite_true, Option.getD_some, ← List.map_take, remainder_charges_take K N m k s p hk,
    highRemainderChargeTicks, List.sum_eq_foldl]

/-- A single cumulative computation certifies the integral at every partition endpoint. -/
public theorem high_remainder_integral_le_prefix (K : HighGaussianKernel) (N m scale : ℕ)
    (hscale : 0 < scale) {s : ℚ} (hs : 0 ≤ s) (p : ℕ → ℚ) (hp : ∀ j < N, p j < p (j + 1))
    (h0 : ∀ j < N, 0 ≤ p j) {k : ℕ} (hk : k ≤ N) :
    let D := (highRemainderRatPoly K).map (Rat.castHom ℝ)
    (∫ x in (p 0 : ℝ)..(p k : ℝ), Real.exp (-(s : ℝ) * x) * |D.eval x|) ≤
      (highRemainderPrefixTicks K N m scale s p k : ℝ) / (scale : ℝ) := by
  rw [high_remainder_prefix_ticks_eq K N m scale s p hk]
  exact
    high_remainder_integral_le_ticks K k m scale hscale hs p (fun j hj ↦ hp j (hj.trans_le hk))
      (fun j hj ↦ h0 j (hj.trans_le hk))

end PseudoPrime.PrimeTestBounds.MillerRabin
