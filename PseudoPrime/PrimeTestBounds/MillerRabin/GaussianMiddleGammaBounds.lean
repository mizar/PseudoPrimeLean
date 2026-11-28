/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Polynomial.Taylor
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaPowers
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaZero
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaPowers
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaZero

/-! # Coefficient enclosures for the middle Gamma polynomials -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The exact low-pole coefficient added at derivative order `j`.
The second pole is included for K141 and represented separately for K156. -/
@[expose]
def middleGammaPoleShift (a : ℚ) (second : Bool) (j : ℕ) : ℚ :=
  1 / (a - 1 / 2) ^ (j + 1) - (if second then (-1 : ℚ) ^ j / (5 / 2 - a) ^ (j + 1) else 0)

/-- The full derivative coefficient after adding the rational pole shifts.
Order zero uses the digamma baseline and higher orders use reciprocal powers. -/
noncomputable def middleGammaDerivCoeff (a : ℚ) (second : Bool) : ℕ → ℝ
  | 0 => gammaZeroCoeff a + (middleGammaPoleShift a second 0 : ℝ)
  | j + 1 => gammaHigherCoeff a j + (middleGammaPoleShift a second (j + 1) : ℝ)

/-- Rational lower and upper endpoints for each derivative order.
Positive orders use an integer grid with denominator `D`. -/
@[expose]
def middleGammaDerivBounds (a : ℚ) (second : Bool) (N D : ℕ) : ℕ → ℚ × ℚ
  | 0 =>
    ((gammaZeroBounds a).1 + middleGammaPoleShift a second 0,
      (gammaZeroBounds a).2 + middleGammaPoleShift a second 0)
  | j + 1 =>
    ((gammaHigherGrid a j N D).1 / (D : ℚ) + middleGammaPoleShift a second (j + 1),
      (gammaHigherGrid a j N D).2 / (D : ℚ) + middleGammaPoleShift a second (j + 1))

/-- The rational endpoints enclose the shifted coefficient at every
derivative order for either middle pole rate. -/
theorem middle_gamma_deriv_bounds {a : ℚ} (ha₀ : 1 / 2 ≤ a) (ha₁ : a ≤ 7 / 2) (second : Bool)
    (N D j : ℕ) (hD : 0 < D) :
    ((middleGammaDerivBounds a second N D j).1 : ℝ) ≤ middleGammaDerivCoeff a second j ∧
      middleGammaDerivCoeff a second j ≤ ((middleGammaDerivBounds a second N D j).2 : ℝ) := by
  cases j with
  | zero =>
    obtain ⟨hl, hu⟩ := gamma_zero_bounds ha₀ ha₁
    simpa only [middleGammaDerivBounds, middleGammaDerivCoeff, Rat.cast_add] using
      And.intro (add_le_add_left hl (middleGammaPoleShift a second 0 : ℝ))
        (add_le_add_left hu (middleGammaPoleShift a second 0 : ℝ))
  | succ
    j =>
    have ha : -(1 / 2 : ℚ) < a := (by norm_num only : -(1 / 2 : ℚ) < 1 / 2).trans_le ha₀
    have ha' : a < 9 / 2 := ha₁.trans_lt (by norm_num only)
    obtain ⟨hl, hu⟩ := gamma_higher_grid ha ha' j N D hD
    simpa only [middleGammaDerivBounds, middleGammaDerivCoeff, Rat.cast_add, Rat.cast_div,
      Rat.cast_intCast, Rat.cast_natCast] using
      And.intro (add_le_add_left hl (middleGammaPoleShift a second (j + 1) : ℝ))
        (add_le_add_left hu (middleGammaPoleShift a second (j + 1) : ℝ))

/-- Recombine the residual derivative terms into one sum with rationally
enclosed coefficients. K141 selects both shifts and K156 selects the first. -/
theorem middle_gamma_deriv_sum (P : Polynomial ℝ) (a : ℚ) (second : Bool) (z : ℝ) :
    let v := fun j : ℕ ↦ ((Polynomial.derivative^[j]) P).eval z
    (∑ j ∈ Finset.range (P.natDegree + 1), middleGammaDerivCoeff a second j * v j) =
      gammaZeroCoeff a * P.eval z +
          (∑ j ∈ Finset.range P.natDegree, gammaHigherCoeff a j * v (j + 1)) +
          (∑ j ∈ Finset.range (P.natDegree + 1), v j / ((a : ℝ) - 1 / 2) ^ (j + 1)) -
        (if second then
          ∑ j ∈ Finset.range (P.natDegree + 1), (-1 : ℝ) ^ j * v j / (5 / 2 - (a : ℝ)) ^ (j + 1)
        else 0) := by
  intro v
  have h (j : ℕ) :
    middleGammaDerivCoeff a second j =
      (if j = 0 then gammaZeroCoeff a else gammaHigherCoeff a (j - 1)) +
        (middleGammaPoleShift a second j : ℝ) := by
    cases j <;>
      simp only [middleGammaDerivCoeff, ite_true, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
  simp only [h, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ']
  simp only [v, Nat.succ_ne_zero, ite_false, ite_true, Nat.succ_sub_one,
    Function.iterate_zero_apply, add_comm (∑ _ ∈ _, _)]
  cases second <;>
    simp only [middleGammaPoleShift, Bool.false_eq_true, ite_false, ite_true, sub_zero,
      Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat, sub_mul,
      Finset.sum_sub_distrib, div_mul_eq_mul_div] <;>
    ring_nf

/-- Express the coefficient sum in the real pole coordinates used by
the middle contour formulas. -/
theorem middle_gamma_deriv_sum_real (P : Polynomial ℝ) (a : ℚ) (second : Bool) (z : ℝ) :
    let a' := (a : ℝ)
    let d := 9 / 2 - a'
    let e := a' + 1 / 2
    let v := fun j : ℕ ↦ ((Polynomial.derivative^[j]) P).eval z
    let B :=
      ((Complex.digamma ((d / 2 : ℝ) : ℂ)).re + (Complex.digamma ((e / 2 : ℝ) : ℂ)).re) / 2 -
        Real.log Real.pi
    let C := fun j : ℕ ↦
      -((-1 : ℝ) ^ (j + 1) * (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2))) -
        ∑' n : ℕ, 1 / (e + 2 * n) ^ (j + 2)
    (∑ j ∈ Finset.range (P.natDegree + 1), middleGammaDerivCoeff a second j * v j) =
      B * P.eval z + (∑ j ∈ Finset.range P.natDegree, C j * v (j + 1)) +
          (∑ j ∈ Finset.range (P.natDegree + 1), v j / (a' - 1 / 2) ^ (j + 1)) -
        (if second then
          ∑ j ∈ Finset.range (P.natDegree + 1), (-1 : ℝ) ^ j * v j / (5 / 2 - a') ^ (j + 1)
        else 0) := by
  intro a' d e v B C
  simpa only [gammaZeroCoeff, gammaHigherCoeff, B, C, d, e, a', v, Rat.cast_sub, Rat.cast_add,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one, Complex.ofReal_ratCast] using
    middle_gamma_deriv_sum P a second z

/-- K141 uses the same reciprocal spacing on both contours. At odd order
only the exact low-pole shifts remain, and at even order one grid suffices. -/
@[expose]
def middleK141GammaBounds (N D : ℕ) : ℕ → ℚ × ℚ
  | 0 => middleGammaDerivBounds 2 true N D 0
  | j + 1 =>
    let c := middleGammaPoleShift 2 true (j + 1)
    if Odd (j + 1) then (c, c)
    else
      let G := gammaPolePowerGrid (5 / 2) j N D
      (c - 2 * (G.2 : ℚ) / D, c - 2 * (G.1 : ℚ) / D)

/-- The symmetric coefficient enclosure uses exact cancellation at odd
orders and a single rigorous reciprocal-power enclosure at even orders. -/
theorem middle_k141_gamma_bounds (N D j : ℕ) (hD : 0 < D) :
    ((middleK141GammaBounds N D j).1 : ℝ) ≤ middleGammaDerivCoeff 2 true j ∧
      middleGammaDerivCoeff 2 true j ≤ ((middleK141GammaBounds N D j).2 : ℝ) := by
  cases j with
  | zero => exact middle_gamma_deriv_bounds (by norm_num only) (by norm_num only) true N D 0 hD
  | succ j =>
    have hf : (9 / 2 - (2 : ℚ)) = 5 / 2 := by norm_num only
    have hr : (2 : ℚ) + 1 / 2 = 5 / 2 := by norm_num only
    by_cases ho : Odd (j + 1)
    · simp only [middleK141GammaBounds, ite_eq_left ho, middleGammaDerivCoeff, gammaHigherCoeff, hf,
        hr, ho.neg_one_pow, neg_one_mul, neg_neg, sub_self, zero_add, le_refl, and_self]
    · have he : Even (j + 1) := Nat.not_odd_iff_even.mp ho
      have h := gamma_pole_power_grid_cast (by norm_num only : (0 : ℚ) < 5 / 2) j N D hD
      simp only [middleK141GammaBounds, ite_eq_right ho, middleGammaDerivCoeff, gammaHigherCoeff,
        hf, hr, he.neg_one_pow, one_mul, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_intCast, Rat.cast_natCast, mul_div_assoc]
      exact ⟨by linarith only [h.2], by linarith only [h.1]⟩

/-- An interval for a signed Gamma coefficient gives a product upper
bound by charging its width only against the negative part of the derivative. -/
theorem middle_gamma_mul_le {g l u v : ℝ} (hl : l ≤ g) (hu : g ≤ u) :
    g * v ≤ u * v + (u - l) * max 0 (-v) := by
  by_cases hv : 0 ≤ v
  · rw [max_eq_left (neg_nonpos.mpr hv), mul_zero, add_zero]
    exact mul_le_mul_of_nonneg_right hu hv
  · have hv' := (lt_of_not_ge hv).le
    rw [max_eq_right (neg_nonneg.mpr hv')]
    exact (mul_le_mul_of_nonpos_right hl hv').trans_eq (by ring)

/-- The K141 coefficient enclosure bounds the entire signed derivative
sum; its certified odd orders contribute no interval-width correction. -/
theorem middle_k141_gamma_sum_le (P : Polynomial ℝ) (z : ℝ) (N D : ℕ) (hD : 0 < D) :
    let v := fun j : ℕ ↦ ((Polynomial.derivative^[j]) P).eval z
    let b := middleK141GammaBounds N D
    (∑ j ∈ Finset.range (P.natDegree + 1), middleGammaDerivCoeff 2 true j * v j) ≤
      ∑ j ∈ Finset.range (P.natDegree + 1),
        (((b j).2 : ℝ) * v j + (((b j).2 : ℝ) - ((b j).1 : ℝ)) * max 0 (-v j)) := by
  intro v b
  apply Finset.sum_le_sum
  intro j _
  obtain ⟨hl, hu⟩ := middle_k141_gamma_bounds N D j hD
  exact middle_gamma_mul_le hl hu

/-- The K156 coefficient enclosure bounds the entire signed derivative
sum, with the second forward pole handled separately. -/
theorem middle_k156_gamma_sum_le (P : Polynomial ℝ) (z : ℝ) (N D : ℕ) (hD : 0 < D) :
    let v := fun j : ℕ ↦ ((Polynomial.derivative^[j]) P).eval z
    let b := middleGammaDerivBounds (49 / 20) false N D
    (∑ j ∈ Finset.range (P.natDegree + 1), middleGammaDerivCoeff (49 / 20) false j * v j) ≤
      ∑ j ∈ Finset.range (P.natDegree + 1),
        (((b j).2 : ℝ) * v j + (((b j).2 : ℝ) - ((b j).1 : ℝ)) * max 0 (-v j)) := by
  intro v b
  apply Finset.sum_le_sum
  intro j _
  obtain ⟨hl, hu⟩ :=
    middle_gamma_deriv_bounds (a := 49 / 20) (by norm_num only) (by norm_num only) false N D j hD
  exact middle_gamma_mul_le hl hu

/-- Bound the absolute profile on a centered interval by one Taylor
coefficient row at the center. This is used for coefficient-width budgets. -/
theorem middle_poly_center_cap (P : Polynomial ℝ) {c z h : ℝ} (hz : |z - c| ≤ h) :
    |P.eval z| ≤
      ∑ k ∈ Finset.range ((Polynomial.taylor c P).natDegree + 1),
        |(Polynomial.taylor c P).coeff k| * h ^ k := by
  rw [← Polynomial.taylor_eval_sub c P z, Polynomial.eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hz k) (abs_nonneg _)

/-- The fixed coefficient grid for K141 uses 17 prefix entries at each
even derivative order and no reciprocal-power checks at odd orders. -/
@[expose]
def middleK141GammaRow (j : ℕ) : ℚ × ℚ :=
  middleK141GammaBounds 16 (10 ^ 16) j

/-- The fixed coefficient grid for K156 bounds both reciprocal spacings,
with the second pole handled by its independent Taylor polynomial. -/
@[expose]
def middleK156GammaRow (j : ℕ) : ℚ × ℚ :=
  middleGammaDerivBounds (49 / 20) false 16 (10 ^ 16) j

/-- The fixed K141 row encloses every coefficient of the derivative sum. -/
theorem middle_k141_gamma_row_sound (j : ℕ) :
    ((middleK141GammaRow j).1 : ℝ) ≤ middleGammaDerivCoeff 2 true j ∧
      middleGammaDerivCoeff 2 true j ≤ ((middleK141GammaRow j).2 : ℝ) := by
  exact middle_k141_gamma_bounds 16 (10 ^ 16) j (by norm_num only)

/-- The fixed K156 row encloses every coefficient of the derivative sum. -/
theorem middle_k156_gamma_row_sound (j : ℕ) :
    ((middleK156GammaRow j).1 : ℝ) ≤ middleGammaDerivCoeff (49 / 20) false j ∧
      middleGammaDerivCoeff (49 / 20) false j ≤ ((middleK156GammaRow j).2 : ℝ) := by
  exact
    middle_gamma_deriv_bounds (by norm_num only) (by norm_num only) false 16 (10 ^ 16) j
      (by norm_num only)

/-- Centering a polynomial commutes with every ordinary derivative,
allowing all derivative bounds on a cell to use the same translated row. -/
private theorem middle_taylor_derivatives (P : Polynomial ℝ) (c : ℝ) (j : ℕ) :
    Polynomial.taylor c ((Polynomial.derivative^[j]) P) =
      (Polynomial.derivative^[j]) (Polynomial.taylor c P) := by
  induction j with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
  | succ j ih =>
    rw [Function.iterate_succ_apply', Polynomial.taylor_derivative, ih,
      Function.iterate_succ_apply']

/-- Read the centered cap for derivative order `j` from one polynomial
row, using zero padding and descending factorial weights. -/
theorem middle_deriv_center_cap (P : Polynomial ℝ) {c z h : ℝ} (hz : |z - c| ≤ h) (j : ℕ) :
    |((Polynomial.derivative^[j]) P).eval z| ≤
      ∑ k ∈ Finset.range (P.natDegree - j + 1),
        |(Polynomial.taylor c P).coeff (k + j)| * ((k + j).descFactorial j : ℝ) * h ^ k := by
  refine (middle_poly_center_cap ((Polynomial.derivative^[j]) P) hz).trans ?_
  rw [middle_taylor_derivatives]
  have hdeg := Polynomial.natDegree_iterate_derivative (Polynomial.taylor c P) j
  rw [Polynomial.natDegree_taylor] at hdeg
  have hh := (abs_nonneg _).trans hz
  refine
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hdeg))
          (fun k _ _ ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hh k))).trans_eq
      ?_
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.coeff_iterate_derivative, nsmul_eq_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
    mul_comm ((k + j).descFactorial j : ℝ)]

/-- Bound the correction for an enclosed Gamma derivative sum using one
centered row and nonnegative widths. All terms involve finite coefficient sums. -/
theorem middle_gamma_center_le (P : Polynomial ℝ) {c z h : ℝ} (hz : |z - c| ≤ h) (g l u : ℕ → ℝ)
    (hl : ∀ j ≤ P.natDegree, l j ≤ g j) (hu : ∀ j ≤ P.natDegree, g j ≤ u j) :
    let v := fun j : ℕ ↦ ((Polynomial.derivative^[j]) P).eval z
    (∑ j ∈ Finset.range (P.natDegree + 1), g j * v j) ≤
      (∑ j ∈ Finset.range (P.natDegree + 1), u j * v j) +
        ∑ j ∈ Finset.range (P.natDegree + 1),
          (u j - l j) *
            ∑ k ∈ Finset.range (P.natDegree - j + 1),
              |(Polynomial.taylor c P).coeff (k + j)| * ((k + j).descFactorial j : ℝ) * h ^ k := by
  intro v
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  refine (middle_gamma_mul_le (hl j hj') (hu j hj')).trans ?_
  have hv : max 0 (-v j) ≤ |v j| := max_le (abs_nonneg _) (neg_le_abs _)
  exact
    add_le_add_right
      (mul_le_mul_of_nonneg_left (hv.trans (middle_deriv_center_cap P hz j))
        (sub_nonneg.mpr ((hl j hj').trans (hu j hj'))))
      _

/-- Compute the coefficient-width correction in rational arithmetic
from a centered row and the coefficient enclosure endpoints. -/
noncomputable def middleGammaWidthBudget (P : Polynomial ℚ) (c h : ℚ) (b : ℕ → ℚ × ℚ) : ℚ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    ((b j).2 - (b j).1) *
      ∑ k ∈ Finset.range (P.natDegree - j + 1),
        |(Polynomial.taylor c P).coeff (k + j)| * ((k + j).descFactorial j : ℚ) * h ^ k

/-- The rational width budget transports the derivative sum to the upper
coefficient row uniformly on the centered cell. -/
theorem middle_gamma_width_le (P : Polynomial ℚ) (b : ℕ → ℚ × ℚ) (g : ℕ → ℝ) {c h : ℚ} {z : ℝ}
    (hz : |z - (c : ℝ)| ≤ (h : ℝ))
    (hb : ∀ j ≤ P.natDegree, ((b j).1 : ℝ) ≤ g j ∧ g j ≤ ((b j).2 : ℝ)) :
    let R := P.map (Rat.castHom ℝ)
    let v := fun j : ℕ ↦ ((Polynomial.derivative^[j]) R).eval z
    (∑ j ∈ Finset.range (P.natDegree + 1), g j * v j) ≤
      (∑ j ∈ Finset.range (P.natDegree + 1), ((b j).2 : ℝ) * v j) +
        (middleGammaWidthBudget P c h b : ℝ) := by
  intro R v
  have hd : R.natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (f := Rat.castHom ℝ) Rat.cast_injective _
  have hcenter : Polynomial.taylor (c : ℝ) R = (Polynomial.taylor c P).map (Rat.castHom ℝ) :=
    (Polynomial.map_taylor P c (Rat.castHom ℝ)).symm
  have h :=
    middle_gamma_center_le R hz g (fun j ↦ ((b j).1 : ℝ)) (fun j ↦ ((b j).2 : ℝ))
      (fun j hj ↦ (hb j (hj.trans_eq hd)).1) (fun j hj ↦ (hb j (hj.trans_eq hd)).2)
  simpa only [middleGammaWidthBudget, Rat.cast_sum, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast,
    Rat.cast_abs, Rat.cast_pow, hd, hcenter, v, Rat.coe_castHom, Polynomial.coeff_map] using h

/-- Reindex a finite triangular sum by total order. This isolates the
weight that is shared by all cells of the same radius. -/
private theorem middle_sum_total_order (f : ℕ → ℕ → ℚ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n - j + 1), f j k) =
      ∑ t ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (t + 1), f j (t - j) := by
  induction n with
  | zero => simp only [Finset.sum_range_one, Nat.zero_sub, Nat.zero_add]
  | succ n
    ih =>
    rw [Finset.sum_range_succ (fun j ↦ ∑ k ∈ Finset.range (n + 1 - j + 1), f j k) (n + 1),
      Finset.sum_range_succ (fun t ↦ ∑ j ∈ Finset.range (t + 1), f j (t - j)) (n + 1)]
    have hs (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      (∑ k ∈ Finset.range (n + 1 - j + 1), f j k) =
        (∑ k ∈ Finset.range (n - j + 1), f j k) + f j (n + 1 - j) := by
      have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have he : n + 1 - j = n - j + 1 := by
        rw [Nat.add_comm n 1, Nat.add_sub_assoc hj', Nat.add_comm 1]
      rw [Finset.sum_range_succ, he]
    rw [Finset.sum_congr rfl hs, Finset.sum_add_distrib, ih]
    rw [Finset.sum_range_succ (fun j ↦ f j (n + 1 - j)) (n + 1), Nat.sub_self, Nat.zero_add,
      Finset.sum_range_one]
    exact add_assoc _ _ _

/-- The radius-dependent weight at total derivative order `k`. Its
evaluation can be shared by all cells with the same radius. -/
@[expose]
def middleGammaWidthWeight (h : ℚ) (b : ℕ → ℚ × ℚ) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k + 1), ((b j).2 - (b j).1) * (k.descFactorial j : ℚ) * h ^ (k - j)

/-- The width correction is a dot product with a single centered row.
This avoids repeating the triangular weighted sum for each cell. -/
theorem middle_gamma_width_dot (P : Polynomial ℚ) (c h : ℚ) (b : ℕ → ℚ × ℚ) :
    middleGammaWidthBudget P c h b =
      ∑ k ∈ Finset.range (P.natDegree + 1),
        |(Polynomial.taylor c P).coeff k| * middleGammaWidthWeight h b k := by
  simp only [middleGammaWidthBudget, Finset.mul_sum]
  rw [middle_sum_total_order]
  apply Finset.sum_congr rfl
  intro k _
  simp only [middleGammaWidthWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.sub_add_cancel (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  ring

/-- A finite dot-product certificate may pad the profile degree and
round the common radius weights upwards before multiplying by magnitudes. -/
theorem middle_gamma_width_dot_le (P : Polynomial ℚ) (c h : ℚ) (b : ℕ → ℚ × ℚ) {N : ℕ}
    (hN : P.natDegree ≤ N) (w : ℕ → ℚ) (hw : ∀ k ≤ N, middleGammaWidthWeight h b k ≤ w k)
    (hw₀ : ∀ k ≤ N, 0 ≤ w k) :
    middleGammaWidthBudget P c h b ≤
      ∑ k ∈ Finset.range (N + 1), |(Polynomial.taylor c P).coeff k| * w k := by
  rw [middle_gamma_width_dot]
  refine
    (Finset.sum_le_sum fun k hk ↦
          mul_le_mul_of_nonneg_left (hw k ((Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hN))
            (abs_nonneg _)).trans
      ?_
  exact
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hN))
      (fun k hk _ ↦ mul_nonneg (abs_nonneg _) (hw₀ k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))

/-- The width of the K156 coefficient interval can be checked from the
two tail widths alone at each positive order. -/
theorem middle_k156_gamma_width_succ (j : ℕ) :
    (middleK156GammaRow (j + 1)).2 - (middleK156GammaRow (j + 1)).1 ≤
      gammaPoleGridWidth (9 / 2 - 49 / 20) j 16 (10 ^ 16) +
        gammaPoleGridWidth (49 / 20 + 1 / 2) j 16 (10 ^ 16) := by
  have h := gamma_higher_grid_width (49 / 20) j 16 (10 ^ 16) (by norm_num only) (by norm_num only)
  simp only [middleK156GammaRow, middleGammaDerivBounds]
  rw [add_sub_add_right_eq_sub, ← sub_div]
  simpa only [Int.cast_sub] using h

/-- The width of the K141 coefficient interval vanishes at odd order
and is bounded by twice the single tail width at even order. -/
theorem middle_k141_gamma_width_succ (j : ℕ) :
    (middleK141GammaRow (j + 1)).2 - (middleK141GammaRow (j + 1)).1 ≤
      if Odd (j + 1) then 0 else 2 * gammaPoleGridWidth (5 / 2) j 16 (10 ^ 16) := by
  by_cases ho : Odd (j + 1)
  · simp only [middleK141GammaRow, middleK141GammaBounds, ite_eq_left ho, sub_self, le_refl]
  · simp only [middleK141GammaRow, middleK141GammaBounds, ite_eq_right ho]
    have h := gamma_pole_grid_width_le (5 / 2) j 16 (10 ^ 16) (by norm_num only)
    simp only [Int.cast_sub] at h
    linear_combination 2 * h

/-- Cheap width majorants for K141. Only even positive orders need a
reciprocal-power tail width. -/
@[expose]
def middleK141GammaWidth : ℕ → ℚ
  | 0 => gammaZeroWidth 2
  | j + 1 => if Odd (j + 1) then 0 else 2 * gammaPoleGridWidth (5 / 2) j 16 (10 ^ 16)

/-- Cheap width majorants for K156. The two reciprocal-power tail widths
are added at each positive order. -/
@[expose]
def middleK156GammaWidth : ℕ → ℚ
  | 0 => gammaZeroWidth (49 / 20)
  | j + 1 =>
    gammaPoleGridWidth (9 / 2 - 49 / 20) j 16 (10 ^ 16) +
      gammaPoleGridWidth (49 / 20 + 1 / 2) j 16 (10 ^ 16)

/-- The K141 width majorant covers every checked coefficient. -/
theorem middle_k141_gamma_width_le (j : ℕ) :
    (middleK141GammaRow j).2 - (middleK141GammaRow j).1 ≤ middleK141GammaWidth j := by
  cases j with
  | zero =>
    simp only [middleK141GammaRow, middleK141GammaBounds, middleGammaDerivBounds,
      middleK141GammaWidth, add_sub_add_right_eq_sub, gamma_zero_width_eq, le_refl]
  | succ j => exact middle_k141_gamma_width_succ j

/-- The K156 width majorant covers every checked coefficient. -/
theorem middle_k156_gamma_width_le (j : ℕ) :
    (middleK156GammaRow j).2 - (middleK156GammaRow j).1 ≤ middleK156GammaWidth j := by
  cases j with
  | zero =>
    simp only [middleK156GammaRow, middleGammaDerivBounds, middleK156GammaWidth,
      add_sub_add_right_eq_sub, gamma_zero_width_eq, le_refl]
  | succ j => exact middle_k156_gamma_width_succ j

/-- Compute radius weights from width majorants, with no evaluation of
the reciprocal or digamma prefixes used in the original coefficient endpoints. -/
@[expose]
def middleGammaRadiusWeight (h : ℚ) (width : ℕ → ℚ) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k + 1), width j * (k.descFactorial j : ℚ) * h ^ (k - j)

/-- Nonnegative radii let the coefficient-width majorants pass through
the finite radius-weight sum. -/
theorem middle_gamma_radius_weight_le {h : ℚ} (hh : 0 ≤ h) (b : ℕ → ℚ × ℚ) (width : ℕ → ℚ)
    (hwidth : ∀ j, (b j).2 - (b j).1 ≤ width j) (k : ℕ) :
    middleGammaWidthWeight h b k ≤ middleGammaRadiusWeight h width k := by
  apply Finset.sum_le_sum
  intro j _
  exact
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hwidth j) (Nat.cast_nonneg _))
      (pow_nonneg hh _)

end PseudoPrime.PrimeTestBounds.MillerRabin
