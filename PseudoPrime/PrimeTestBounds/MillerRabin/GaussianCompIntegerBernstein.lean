/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms
public import PseudoPrime.Analysis.BernsteinCompensation

/-! # Integer Bernstein coefficients for compensation certificates -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Evaluate a finite linear combination of falling factorials without
constructing binomial coefficients or dividing by a factorial. -/
@[expose]
public def fallingHorner : ℕ → ℕ → ℕ → (ℕ → ℤ) → ℤ
  | 0, _, _, _ => 0
  | l + 1, i, o, f => f o + (i : ℤ) * fallingHorner l (i - 1) (o + 1) f

/-- A positive-length falling factorial starts with its argument, even
when the argument is zero. -/
private theorem falling_step (i k : ℕ) : i.descFactorial (k + 1) = i * (i - 1).descFactorial k := by
  cases i with
  | zero => rw [Nat.zero_descFactorial_succ, Nat.zero_mul]
  | succ i => rw [Nat.succ_descFactorial_succ, Nat.succ_sub_one]

/-- The Horner recurrence equals the finite falling-factorial sum. -/
private theorem falling_horner_eq (l i o : ℕ) (f : ℕ → ℤ) :
    fallingHorner l i o f = ∑ k ∈ Finset.range l, f (o + k) * (i.descFactorial k : ℤ) := by
  induction l generalizing i o with
  | zero => simp only [fallingHorner, Finset.range_zero, Finset.sum_empty]
  | succ l
    ih =>
    rw [fallingHorner, ih, Finset.sum_range_succ', Nat.descFactorial_zero, Nat.cast_one,
      Nat.add_zero, mul_one, add_comm (f o), Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [falling_step, Nat.cast_mul, Nat.add_right_comm o 1 k, Nat.add_assoc o k 1]
    ring

/-- Compute the Bernstein numerator using the common scale
given by the power row denominator times the degree factorial. -/
@[expose]
public def MiddleIntRow.bernsteinNum (row : MiddleIntRow) (n i : ℕ) : ℤ :=
  fallingHorner (min n i + 1) i 0 (fun k ↦ row.num k * ((n - k).factorial : ℤ))

/-- Recover the binomial sum for the correctness proof of the integer transform. -/
private theorem bernstein_num_sum (row : MiddleIntRow) (n i : ℕ) :
    row.bernsteinNum n i =
      ∑ k ∈ Finset.range (min n i + 1),
        row.num k * (Nat.fast_choose i k : ℤ) * (k.factorial : ℤ) * ((n - k).factorial : ℤ) := by
  simp only [MiddleIntRow.bernsteinNum, falling_horner_eq, Nat.zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.choose_eq_fast_choose]
  ring

/-- The factorial identity puts every Bernstein coefficient summand
over the same denominator. -/
private theorem bernstein_shared_den (q d : ℚ) (n i k : ℕ) (hk : k ≤ n) :
    (q / d) * ((Nat.fast_choose i k : ℚ) / (Nat.fast_choose n k : ℚ)) =
      (q * (Nat.fast_choose i k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ)) /
        (d * (n.factorial : ℚ)) := by
  have h := congrArg (fun t : ℕ ↦ (t : ℚ)) (Nat.choose_mul_factorial_mul_factorial hk)
  simp only [Nat.cast_mul, Nat.choose_eq_fast_choose] at h
  have hpos : ((k.factorial : ℚ) * ((n - k).factorial : ℚ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne')
      (Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne')
  rw [div_mul_div_comm]
  calc
    _ =
        ((q * (Nat.fast_choose i k : ℚ)) * ((k.factorial : ℚ) * ((n - k).factorial : ℚ))) /
          ((d * (Nat.fast_choose n k : ℚ)) * ((k.factorial : ℚ) * ((n - k).factorial : ℚ))) :=
      (mul_div_mul_right _ _ hpos).symm
    _ = _ := by
      rw [show
          (d * (Nat.fast_choose n k : ℚ)) * ((k.factorial : ℚ) * ((n - k).factorial : ℚ)) =
            d * (n.factorial : ℚ)
          by
          rw [← h]; ring]
      congr 1
      ring

/-- The integer numerator divided by the common scale is exactly the
rational Bernstein coefficient of the verified power row. -/
public theorem MiddleIntRow.bernstein_num_eq (row : MiddleIntRow) (n i : ℕ) :
    Analysis.bernsteinRatCoeff (row.poly n) n i =
      (row.bernsteinNum n i : ℚ) / ((row.den : ℚ) * (n.factorial : ℚ)) := by
  have hsub : Finset.range (min n i + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (Nat.succ_le_succ (min_le_left n i))
  simp only [Analysis.bernsteinRatCoeff, bernstein_num_sum, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast, Finset.sum_div]
  rw [Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro k hk
    have h := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [row.poly_coeff h]
    exact bernstein_shared_den (row.num k) row.den n i k h
  · intro k hk hki
    have hn := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hi : i < k :=
      Nat.lt_of_not_ge fun hi ↦ hki (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_min hn hi)))
    simp only [← Nat.choose_eq_fast_choose, Nat.choose_eq_zero_of_lt hi, Nat.cast_zero, mul_zero,
      zero_mul, zero_div]

/-- The clipped integer numerator scales to the clipped rational
Bernstein coefficient when the row denominator is positive. -/
public theorem MiddleIntRow.bernstein_clip_eq (row : MiddleIntRow) (n i : ℕ) (hd : 0 < row.den) :
    max 0 (-Analysis.bernsteinRatCoeff (row.poly n) n i) =
      (max 0 (-row.bernsteinNum n i) : ℤ) / ((row.den : ℚ) * (n.factorial : ℚ)) := by
  have hp : 0 ≤ (row.den : ℚ) * (n.factorial : ℚ) :=
    mul_nonneg ((Int.cast_pos.mpr hd : (0 : ℚ) < row.den).le) (Nat.cast_nonneg _)
  rw [row.bernstein_num_eq, ← neg_div]
  simp only [Int.cast_max, Int.cast_zero, Int.cast_neg, ← max_div_div_right hp, zero_div]

/-- Neighbor differences preserve the common scale. This avoids normalizing
rational coefficients during differentiation in the Bernstein basis. -/
public theorem bernstein_derivative_int_scale (n i : ℕ) (c : ℕ → ℤ) (D : ℚ) :
    Analysis.bernsteinDerivativeCoeff n (fun j ↦ (c j : ℚ) / D) i =
      (Analysis.bernsteinDerivativeCoeff n c i : ℤ) / D := by
  simp only [Analysis.bernsteinDerivativeCoeff, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast]
  ring

/-- A common coefficient denominator can be moved out of the entire
Taylor-weighted moment sum. -/
public theorem comp_moment_div (n m : ℕ) (h s D : ℚ) (c : Fin (n + 1) → ℚ) :
    Analysis.compensationMomentSum n m h s (fun i ↦ c i / D) =
      Analysis.compensationMomentSum n m h s c / D := by
  unfold Analysis.compensationMomentSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_div_assoc, Finset.sum_div]
  apply congrArg ((-s) ^ j / (j.factorial : ℚ) * ·)
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Absolute variation retains the common positive coefficient denominator.
The derivative is evaluated with integer neighbor differences. -/
public theorem comp_variation_abs_div (n i : ℕ) (d h D : ℚ) (c : ℕ → ℤ) (hD : 0 ≤ D) :
    |Analysis.bernsteinVariationDirect n i d h (fun j ↦ (c j : ℚ) / D)| =
      |d * (c i : ℚ) - h⁻¹ * (Analysis.bernsteinDerivativeCoeff n c i : ℤ)| / D := by
  rw [Analysis.bernsteinVariationDirect, bernstein_derivative_int_scale, ← mul_div_assoc, ←
    mul_div_assoc, ← sub_div, abs_div, abs_of_nonneg hD]

/-- Clear the common factorial denominator of the monomial Bernstein moment. -/
private theorem comp_moment_weight (n i j : ℕ) (hi : i ≤ n) :
    (n.fast_choose i : ℚ) / ((n + j).fast_choose (i + j) : ℚ) / ((n + j : ℕ) + 1) =
      ((i + j).descFactorial j : ℚ) * (n.factorial : ℚ) / ((n + j + 1).factorial : ℚ) := by
  have hij := Nat.add_le_add_right hi j
  have a := Nat.choose_mul_factorial_mul_factorial hi
  have b := Nat.choose_mul_factorial_mul_factorial hij
  have c := Nat.factorial_mul_descFactorial (Nat.le_add_left j i)
  rw [Nat.add_sub_add_right] at b
  rw [Nat.add_sub_cancel] at c
  have ac := congrArg (fun k : ℕ ↦ (k : ℚ)) a
  have bc := congrArg (fun k : ℕ ↦ (k : ℚ)) b
  have cc := congrArg (fun k : ℕ ↦ (k : ℚ)) c
  simp only [Nat.cast_mul] at ac bc cc
  rw [← Nat.choose_eq_fast_choose, ← Nat.cast_succ, div_div,
    div_eq_div_iff
      (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos hij)))
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    Nat.factorial_succ, Nat.cast_mul, ← bc, ← cc, ← ac]
  ring

/-- Evaluate all coefficients at each Taylor order using an integer dot
product, and apply the shared factorial denominator outside that sum. -/
@[expose]
public def compIntMoments (n m : ℕ) (h s : ℚ) (c : Fin (n + 1) → ℤ) : ℚ :=
  ∑ j ∈ Finset.range (2 * m + 1),
    ((-s) ^ j / (j.factorial : ℚ)) *
      ((h ^ (j + 1) * (n.factorial : ℚ) / ((n + j + 1).factorial : ℚ)) *
        ((∑ i : Fin (n + 1), c i * ((i.val + j).descFactorial j : ℤ)) : ℚ))

/-- The integer dot products give the rational Taylor-weighted moments
exactly for every coefficient row, width, and Taylor rate. -/
public theorem comp_int_moments_eq (n m : ℕ) (h s : ℚ) (c : Fin (n + 1) → ℤ) :
    compIntMoments n m h s c = Analysis.compensationMomentSum n m h s (fun i ↦ (c i : ℚ)) := by
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.mul_sum, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_div_assoc, comp_moment_weight n i.val j (Nat.le_of_lt_succ i.isLt)]
  ring

/-- Clear the positive denominator of the variation, including at width zero. -/
@[expose]
public def compIntVariation (q : ℚ) (c d : ℤ) : ℤ :=
  |9 * (q.den : ℤ) * c - 4 * q.num * d|

/-- Dividing the integer variation by its common scale recovers the
absolute value with pole offset nine quarters and inverse width q. -/
public theorem comp_int_variation_eq (q : ℚ) (c d : ℤ) :
    (compIntVariation q c d : ℚ) / (4 * (q.den : ℚ)) = |(9 / 4 : ℚ) * (c : ℚ) - q * (d : ℚ)| := by
  have h : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_pos q).ne'
  have hp : 0 ≤ 4 * (q.den : ℚ) := mul_nonneg (by decide) (Nat.cast_nonneg _)
  have hq := (div_eq_iff h).mp (Rat.num_div_den q)
  simp only [compIntVariation, Int.cast_abs, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
    Int.cast_natCast]
  rw [← show |4 * (q.den : ℚ)| = 4 * (q.den : ℚ) from abs_of_nonneg hp, ← abs_div]
  apply congrArg abs
  apply (div_eq_iff (mul_ne_zero (by decide) h)).mpr
  linear_combination -4 * (d : ℚ) * hq

end PseudoPrime.PrimeTestBounds.MillerRabin
