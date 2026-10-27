/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ChebyshevPrimeCountLower
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A pointwise elementary prime-count lower bound -/

public section

namespace PseudoPrime.NumberTheory

/-- For w≥64 and B=w^4, the elementary Chebyshev bound gives
B/4≤pi(B) log B. Bound log B by 4w and retain the square-root error.
This supplies a small explicit starting point without prime enumeration. -/
theorem quarter_le_primeCounting_mul_log_of_fourth_power {B : ℕ} {w : ℝ} (hw : 64 ≤ w)
    (hB : w ^ 4 = B) : (B : ℝ) / 4 ≤ (B.primeCounting : ℝ) * Real.log B := by
  have hw0 : 0 ≤ w := le_trans (by norm_num only) hw
  have hBp : (0 : ℝ) < B := hB ▸ pow_pos (lt_of_lt_of_le (by norm_num only) hw) 4
  have hB1 : (1 : ℝ) ≤ B := by
    rw [← hB]
    exact one_le_pow₀ (le_trans (by norm_num only) hw)
  have hlogB : Real.log B ≤ 4 * w := by
    rw [← hB, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (Real.log_le_self hw0) (by norm_num only)
  have hlogadd : Real.log ((B : ℝ) + 1) ≤ 1 + 4 * w := by
    have hh :=
      Real.log_le_log (by linarith only [hBp] : (0 : ℝ) < B + 1)
        (by linarith only [hB1] : (B : ℝ) + 1 ≤ 2 * B)
    rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hBp.ne'] at hh
    linarith only [hh, hlogB, Real.log_two_lt_d9]
  have hsqrt : Real.sqrt (B : ℝ) = w ^ 2 := by
    rw [← hB, show w ^ 4 = (w ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg w)]
  have herror :=
    mul_le_mul_of_nonneg_left hlogB (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (sq_nonneg w))
  have hmain := chebyshev_lower_le_primeCounting_mul_log B
  rw [hsqrt] at hmain
  have hlogtwo :=
    mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ Real.log 2 by linarith only [Real.log_two_gt_d9])
      (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  have hmargin := mul_nonneg (sub_nonneg.mpr hw) (pow_nonneg hw0 3)
  have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ (le_trans (by norm_num only) hw)
  have hw3 : w ≤ w ^ 3 := by nlinarith only [mul_le_mul_of_nonneg_right hw2 hw0]
  nlinarith only [hB, hmain, herror, hlogadd, hlogtwo, hmargin, hw3, hw]

/-- For B≥64^4 the prime count satisfies B/4≤pi(B) log B.
Take two square roots and apply the fourth-power form above.
No enumeration or externally supplied estimate enters this bound. -/
theorem quarter_le_primeCounting_mul_log {B : ℕ} (hB : 64 ^ 4 ≤ B) :
    (B : ℝ) / 4 ≤ (B.primeCounting : ℝ) * Real.log B := by
  let w := Real.sqrt (Real.sqrt (B : ℝ))
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw4 : w ^ 4 = B := by
    calc
      w ^ 4 = (w ^ 2) ^ 2 := by ring
      _ = (B : ℝ) := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg B)]
  have hw : 64 ≤ w := by
    apply (pow_le_pow_iff_left₀ (by norm_num only : (0 : ℝ) ≤ 64) hw0 (by decide : 4 ≠ 0)).mp
    rw [hw4]
    exact_mod_cast hB
  exact quarter_le_primeCounting_mul_log_of_fourth_power hw hw4

/-- For $B=w^4$ and $w\ge64$, the elementary Chebyshev lower expression
gives $B/2\le\pi(B)\log B$. The logarithmic error is bounded by $B/6$,
while $\log 2\ge2/3$. This sharper pointwise estimate supplies a stronger
prime-count input for the scale-$19/10$ smooth-number argument. -/
theorem half_le_primeCounting_mul_log_of_fourth_power {B : ℕ} {w : ℝ} (hw : 64 ≤ w)
    (hB : w ^ 4 = B) : (B : ℝ) / 2 ≤ (B.primeCounting : ℝ) * Real.log B := by
  have hw0 : 0 ≤ w := le_trans (by norm_num only) hw
  have hBp : (0 : ℝ) < B := hB ▸ pow_pos (lt_of_lt_of_le (by norm_num only) hw) 4
  have hB1 : (1 : ℝ) ≤ B := by
    rw [← hB]
    exact one_le_pow₀ (le_trans (by norm_num only) hw)
  have hlogB : Real.log B ≤ 4 * w := by
    rw [← hB, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (Real.log_le_self hw0) (by norm_num only)
  have hlogadd : Real.log ((B : ℝ) + 1) ≤ 1 + 4 * w := by
    have hh :=
      Real.log_le_log (by linarith only [hBp] : (0 : ℝ) < B + 1)
        (by linarith only [hB1] : (B : ℝ) + 1 ≤ 2 * B)
    rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hBp.ne'] at hh
    linarith only [hh, hlogB, Real.log_two_lt_d9]
  have hsqrt : Real.sqrt (B : ℝ) = w ^ 2 := by
    rw [← hB, show w ^ 4 = (w ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg w)]
  have herror :=
    mul_le_mul_of_nonneg_left hlogB (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (sq_nonneg w))
  have hmain := chebyshev_lower_le_primeCounting_mul_log B
  rw [hsqrt] at hmain
  have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlogtwo := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  have hw3 : 0 ≤ w ^ 3 := pow_nonneg hw0 3
  have hpoly1 : 8 * w ^ 3 ≤ w ^ 4 / 8 := by
    have hmul := mul_le_mul_of_nonneg_right hw hw3
    nlinarith only [hmul, hw]
  have hmul2 := mul_le_mul_of_nonneg_right hw hw0
  have hpoly2 : 1 + 4 * w ≤ w ^ 2 := by nlinarith only [hmul2, hw]
  have hpoly3 : w ^ 2 ≤ w ^ 4 / 24 := by
    have hsq : 0 ≤ w ^ 2 := sq_nonneg w
    have hmul := mul_le_mul_of_nonneg_left hw hsq
    nlinarith only [hmul, hw]
  have herrorBound : 1 + 4 * w + 8 * w ^ 3 ≤ w ^ 4 / 6 := by nlinarith only [hpoly1, hpoly2, hpoly3]
  nlinarith only [hB, hmain, herror, hlogadd, hlogtwo, herrorBound, hw]

/-- If $B\ge64^4$, then $B/2\le\pi(B)\log B$. Reduce to the fourth-power
case using two square roots. This bound is twice the coefficient in the
quarter-strength estimate above. -/
theorem half_le_primeCounting_mul_log {B : ℕ} (hB : 64 ^ 4 ≤ B) :
    (B : ℝ) / 2 ≤ (B.primeCounting : ℝ) * Real.log B := by
  let w := Real.sqrt (Real.sqrt (B : ℝ))
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw4 : w ^ 4 = B := by
    calc
      w ^ 4 = (w ^ 2) ^ 2 := by ring
      _ = (B : ℝ) := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg B)]
  have hw : 64 ≤ w := by
    apply (pow_le_pow_iff_left₀ (by norm_num only : (0 : ℝ) ≤ 64) hw0 (by decide : 4 ≠ 0)).mp
    rw [hw4]
    exact_mod_cast hB
  exact half_le_primeCounting_mul_log_of_fourth_power hw hw4

/-- For $B=w^4$ and $w\ge64$, the Chebyshev lower expression gives
$(568/1000)B\le\pi(B)\log B$. Bound the logarithmic and square-root errors
separately by $513B/4096$. -/
theorem seventy_one_one_hundred_twentyfifths_le_primeCounting_mul_log_of_fourth_power {B : ℕ}
    {w : ℝ} (hw : 64 ≤ w) (hB : w ^ 4 = B) :
    (568 / 1000 : ℝ) * B ≤ (B.primeCounting : ℝ) * Real.log B := by
  have hw0 : 0 ≤ w := le_trans (by norm_num only) hw
  have hBp : (0 : ℝ) < B := hB ▸ pow_pos (lt_of_lt_of_le (by norm_num only) hw) 4
  have hB1 : (1 : ℝ) ≤ B := by
    rw [← hB]
    exact one_le_pow₀ (le_trans (by norm_num only) hw)
  have hlogB : Real.log B ≤ 4 * w := by
    rw [← hB, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (Real.log_le_self hw0) (by norm_num only)
  have hlogadd : Real.log ((B : ℝ) + 1) ≤ 1 + 4 * w := by
    have hh :=
      Real.log_le_log (by linarith only [hBp] : (0 : ℝ) < B + 1)
        (by linarith only [hB1] : (B : ℝ) + 1 ≤ 2 * B)
    rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hBp.ne'] at hh
    linarith only [hh, hlogB, Real.log_two_lt_d9]
  have hsqrt : Real.sqrt (B : ℝ) = w ^ 2 := by
    rw [← hB, show w ^ 4 = (w ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg w)]
  have herror :=
    mul_le_mul_of_nonneg_left hlogB (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (sq_nonneg w))
  have hmain := chebyshev_lower_le_primeCounting_mul_log B
  rw [hsqrt] at hmain
  have hlogtwo : (6931 / 10000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlogtwo' := mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  have hw3 : 0 ≤ w ^ 3 := pow_nonneg hw0 3
  have hpoly1 : 8 * w ^ 3 ≤ w ^ 4 / 8 := by
    have hmul := mul_le_mul_of_nonneg_right hw hw3
    nlinarith only [hmul, hw]
  have hmul2 := mul_le_mul_of_nonneg_right hw hw0
  have hpoly2 : 15 * (1 + 4 * w) ≤ w ^ 2 := by nlinarith only [hmul2, hw]
  have hpoly3 : w ^ 2 ≤ w ^ 4 / 4096 := by
    have hmul := mul_le_mul_of_nonneg_left (show 4096 ≤ w ^ 2 by nlinarith only [hw]) (sq_nonneg w)
    nlinarith only [hmul]
  have hpoly4 : 1 + 4 * w ≤ (1 / 60000 : ℝ) * w ^ 4 := by nlinarith only [hpoly2, hpoly3]
  have herrorBound : 1 + 4 * w + 8 * w ^ 3 ≤ (1 / 8 + 1 / 60000 : ℝ) * w ^ 4 := by
    nlinarith only [hpoly1, hpoly4]
  nlinarith only [hB, hmain, herror, hlogadd, hlogtwo', herrorBound, hw]

/-- For every $B\ge64^4$, $(568/1000)B\le\pi(B)\log B$. Take two square
roots and apply the fourth-power estimate. This supplies the prime-count
input for the sharper floor-cutoff theorem below. -/
theorem seventy_one_one_hundred_twentyfifths_le_primeCounting_mul_log {B : ℕ} (hB : 64 ^ 4 ≤ B) :
    (568 / 1000 : ℝ) * B ≤ (B.primeCounting : ℝ) * Real.log B := by
  let w := Real.sqrt (Real.sqrt (B : ℝ))
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw4 : w ^ 4 = B := by
    calc
      w ^ 4 = (w ^ 2) ^ 2 := by ring
      _ = (B : ℝ) := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg B)]
  have hw : 64 ≤ w := by
    apply (pow_le_pow_iff_left₀ (by norm_num only : (0 : ℝ) ≤ 64) hw0 (by decide : 4 ≠ 0)).mp
    rw [hw4]
    exact_mod_cast hB
  exact seventy_one_one_hundred_twentyfifths_le_primeCounting_mul_log_of_fourth_power hw hw4

/-- The earlier $9/16$ form follows from the stronger $568/1000$ estimate. -/
theorem nine_sixteenths_le_primeCounting_mul_log_of_fourth_power {B : ℕ} {w : ℝ} (hw : 64 ≤ w)
    (hB : w ^ 4 = B) : (9 / 16 : ℝ) * B ≤ (B.primeCounting : ℝ) * Real.log B := by
  have h := seventy_one_one_hundred_twentyfifths_le_primeCounting_mul_log_of_fourth_power hw hB
  have hB0 : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
  nlinarith only [h, hB0]

/-- For every $B\ge64^4$, the older $9/16$ estimate follows from the
stronger $568/1000$ estimate. -/
theorem nine_sixteenths_le_primeCounting_mul_log {B : ℕ} (hB : 64 ^ 4 ≤ B) :
    (9 / 16 : ℝ) * B ≤ (B.primeCounting : ℝ) * Real.log B := by
  have h := seventy_one_one_hundred_twentyfifths_le_primeCounting_mul_log hB
  have hB0 : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
  nlinarith only [h, hB0]

/-- For 0<A≤2 and L>1, a floor cutoff above 64^4 and the quantitative
gap L^(A-b)≥32 log L imply pi(floor(L^A))≥2L^b. Keep the floor loss
and apply the elementary quarter lower bound, without an eventual premise. -/
theorem two_mul_rpow_le_primeCounting_floor_of_gap {L A b : ℝ} (hL : 1 < L) (hA : 0 < A)
    (hA2 : A ≤ 2) (hB : 64 ^ 4 ≤ Nat.floor (L ^ A)) (hgap : 32 * Real.log L ≤ L ^ (A - b)) :
    2 * L ^ b ≤ ((Nat.floor (L ^ A)).primeCounting : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans hL
  have hz : 0 < Real.log L := Real.log_pos hL
  have hpow : 0 ≤ L ^ b := Real.rpow_nonneg hLp.le b
  have hB1 : (1 : ℝ) ≤ Nat.floor (L ^ A) := by exact_mod_cast (le_trans (by decide : 1 ≤ 64 ^ 4) hB)
  have hf := Nat.lt_floor_add_one (L ^ A)
  have hhalf : L ^ A ≤ 2 * (Nat.floor (L ^ A) : ℝ) := by linarith only [hf, hB1]
  have hlogB :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hB1) (Nat.floor_le (Real.rpow_nonneg hLp.le A))
  rw [Real.log_rpow hLp A] at hlogB
  have hpi := quarter_le_primeCounting_mul_log hB
  have hm :=
    mul_le_mul_of_nonneg_left hlogB
      (Nat.cast_nonneg ((Nat.floor (L ^ A)).primeCounting) : (0 : ℝ) ≤ _)
  have hg := mul_le_mul_of_nonneg_right hgap hpow
  rw [← Real.rpow_add hLp, sub_add_cancel] at hg
  have hs := mul_nonneg (sub_nonneg.mpr hA2) (mul_nonneg hpow hz.le)
  apply (mul_le_mul_iff_left₀ (mul_pos hA hz)).mp
  nlinarith only [hpi, hm, hhalf, hg, hs]

/-- For $0<A\le2$ and $L>1$, the stronger pointwise prime-count bound and
the gap $L^{A-b}\ge16\log L$ imply $\pi(\lfloor L^A\rfloor)\ge2L^b$.
The floor loss is retained explicitly. -/
theorem two_mul_rpow_le_primeCounting_floor_of_half_gap {L A b : ℝ} (hL : 1 < L) (hA : 0 < A)
    (hA2 : A ≤ 2) (hB : 64 ^ 4 ≤ Nat.floor (L ^ A)) (hgap : 16 * Real.log L ≤ L ^ (A - b)) :
    2 * L ^ b ≤ ((Nat.floor (L ^ A)).primeCounting : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans hL
  have hz : 0 < Real.log L := Real.log_pos hL
  have hpow : 0 ≤ L ^ b := Real.rpow_nonneg hLp.le b
  have hB1 : (1 : ℝ) ≤ Nat.floor (L ^ A) := by exact_mod_cast (le_trans (by decide : 1 ≤ 64 ^ 4) hB)
  have hf := Nat.lt_floor_add_one (L ^ A)
  have hhalf : L ^ A ≤ 2 * (Nat.floor (L ^ A) : ℝ) := by linarith only [hf, hB1]
  have hlogB :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hB1) (Nat.floor_le (Real.rpow_nonneg hLp.le A))
  rw [Real.log_rpow hLp A] at hlogB
  have hpi := half_le_primeCounting_mul_log (B := Nat.floor (L ^ A)) hB
  have hm :=
    mul_le_mul_of_nonneg_left hlogB
      (Nat.cast_nonneg ((Nat.floor (L ^ A)).primeCounting) : (0 : ℝ) ≤ _)
  have hg := mul_le_mul_of_nonneg_right hgap hpow
  rw [← Real.rpow_add hLp, sub_add_cancel] at hg
  have hs := mul_nonneg (sub_nonneg.mpr hA2) (mul_nonneg hpow hz.le)
  apply (mul_le_mul_iff_left₀ (mul_pos hA hz)).mp
  nlinarith only [hpi, hm, hhalf, hg, hs]

/-- If $0<A\le1900001/1000000$, $L>1$, the cutoff exceeds $64^4$, and
$L^{A-b}\ge(13381/1000)\log L$, then $\pi(\lfloor L^A\rfloor)\ge2L^b$.
The coefficient uses the $568/1000$ prime-count bound and retains the floor loss. -/
theorem two_mul_rpow_le_primeCounting_floor_of_13381_over_1000_gap {L A b : ℝ} (hL : 1 < L)
    (hA : 0 < A) (hA2 : A ≤ 1900001 / 1000000) (hB : 64 ^ 4 ≤ Nat.floor (L ^ A))
    (hgap : (13381 / 1000 : ℝ) * Real.log L ≤ L ^ (A - b)) :
    2 * L ^ b ≤ ((Nat.floor (L ^ A)).primeCounting : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans hL
  have hz : 0 < Real.log L := Real.log_pos hL
  have hpow : 0 ≤ L ^ b := Real.rpow_nonneg hLp.le b
  have hB1 : (1 : ℝ) ≤ Nat.floor (L ^ A) := by exact_mod_cast (le_trans (by decide : 1 ≤ 64 ^ 4) hB)
  have hf := Nat.lt_floor_add_one (L ^ A)
  have hhalf : L ^ A ≤ 2 * (Nat.floor (L ^ A) : ℝ) := by linarith only [hf, hB1]
  have hlogB :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hB1) (Nat.floor_le (Real.rpow_nonneg hLp.le A))
  rw [Real.log_rpow hLp A] at hlogB
  have hpi :=
    seventy_one_one_hundred_twentyfifths_le_primeCounting_mul_log (B := Nat.floor (L ^ A)) hB
  have hm :=
    mul_le_mul_of_nonneg_left hlogB
      (Nat.cast_nonneg ((Nat.floor (L ^ A)).primeCounting) : (0 : ℝ) ≤ _)
  have hg := mul_le_mul_of_nonneg_right hgap hpow
  rw [← Real.rpow_add hLp, sub_add_cancel] at hg
  have hr : 4000 * A ≤ 568 * (13381 / 1000 : ℝ) := by nlinarith only [hA2]
  have hmargin : 0 ≤ (568 / 1000 : ℝ) * (13381 / 1000) / 2 - 2 * A := by nlinarith only [hr]
  have hs := mul_nonneg hmargin (mul_nonneg hpow hz.le)
  apply (mul_le_mul_iff_left₀ (mul_pos hA hz)).mp
  nlinarith only [hpi, hm, hhalf, hg, hs]

end PseudoPrime.NumberTheory
