/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleSpacing
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! # Natural-number transfer for the low-range spacing bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If positive natural numbers satisfy `a ∣ b` and the 2-adic valuation of
`b` is strictly larger, then `2a ∣ b`. The quotient has positive 2-adic
valuation, so it is even. This upgrades the middle Korselt divisibility. -/
theorem twice_dvd_of_two_val_lt {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ∣ b)
    (hv : padicValNat 2 a < padicValNat 2 b) : 2 * a ∣ b := by
  obtain ⟨c, rfl⟩ := hab
  have hc : c ≠ 0 := right_ne_zero_of_mul hb
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv0 : padicValNat 2 c ≠ 0 := by
    intro hz
    rw [padicValNat.mul ha hc, hz, add_zero] at hv
    exact (lt_irrefl _) hv
  obtain ⟨k, hk⟩ := padicValNat.dvd_of_ne_zero hv0
  refine ⟨k, ?_⟩
  rw [hk]
  ac_rfl

/-- A factor gap of at least two makes the natural Korselt gap expression
positive for every nonnegative second gap. This discharges the positivity
input of the spacing transfer once the ordered odd factors are separated. -/
theorem triple_gap_pos {d f : ℕ} (hd : 2 ≤ d) : 0 < d * (f + 1) - f := by
  apply Nat.sub_pos_of_lt
  have hm := Nat.mul_le_mul_right (f + 1) hd
  nlinarith only [hm]

/-- The middle-factor Korselt divisor divides the natural gap expression.
For ordered factors with a gap at least two, expand the two nonnegative
subtractions and remove the multiple `(q-1)(p+f+1)`; positivity is supplied
by `triple_gap_pos`. This prepares the stronger 2-adic divisibility claim. -/
theorem triple_gap_dvd {p q f : ℕ} (hp : 1 ≤ p) (hpq : p + 2 ≤ q) (hk : q - 1 ∣ p * (q + f) - 1) :
    q - 1 ∣ (q - p) * (f + 1) - f := by
  have hpq' : p ≤ q := by linarith only [hpq]
  have hd : 2 ≤ q - p := by
    have h := Nat.sub_add_cancel hpq'
    linarith only [hpq, h]
  have ht := triple_gap_pos (f := f) hd
  have ht' : f ≤ (q - p) * (f + 1) := Nat.le_of_lt (Nat.sub_pos_iff_lt.mp ht)
  have hpr : 1 ≤ p * (q + f) := Nat.mul_pos hp (by linarith only [hp, hpq])
  have hq : 1 ≤ q := by linarith only [hp, hpq]
  have h1 := Nat.sub_add_cancel hpq'
  have h2 := Nat.sub_add_cancel hq
  have h3 := Nat.sub_add_cancel hpr
  have h4 := Nat.sub_add_cancel ht'
  have h5 := congrArg (fun x : ℕ ↦ x * (f + 1)) h1
  have h6 := congrArg (fun x : ℕ ↦ x * (p + f + 1)) h2
  have hid : p * (q + f) - 1 + ((q - p) * (f + 1) - f) = (q - 1) * (p + f + 1) := by
    nlinarith only [h3, h4, h5, h6]
  have hdiv : q - 1 ∣ p * (q + f) - 1 + ((q - p) * (f + 1) - f) :=
    hid ▸ dvd_mul_right (q - 1) (p + f + 1)
  exact (Nat.dvd_add_iff_right hk).mpr hdiv

/-- A natural-number version of the divisibility-derived spacing inequality
implies the corresponding real square bound for ordered factors. Cast both
subtractions using the ordering hypotheses and apply the real spacing lemma.
This connects integer Korselt data to the low-range logarithmic estimate. -/
theorem triple_spacing_square_nat {p q f : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hgap : 2 * (q - 1) ≤ (q - p) * (f + 1)) :
    (p : ℝ) * q + q * (4 * Real.sqrt ((p : ℝ) - 1) - 2) ≤ ((q : ℝ) + f) ^ 2 := by
  have hq : 1 ≤ q := hp.trans hpq
  have hgapR := (Nat.cast_le (α := ℝ)).mpr hgap
  norm_num only [Nat.cast_mul, Nat.cast_sub hq, Nat.cast_sub hpq, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat] at hgapR
  have hpR : (1 : ℝ) ≤ p := by simpa only [Nat.cast_one] using (Nat.cast_le (α := ℝ)).mpr hp
  exact triple_spacing_square hpR ((Nat.cast_le (α := ℝ)).mpr hpq) (Nat.cast_nonneg f) hgapR

/-- If the positive natural gap expression is divisible by twice `q-1`,
then the ordered factors satisfy the real square-spacing bound. A positive
multiple is at least its divisor, and the subtraction can only decrease the
gap expression. This transfers the intended 2-adic divisibility input. -/
theorem triple_spacing_of_even_dvd {p q f : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hpos : 0 < (q - p) * (f + 1) - f) (hdiv : 2 * (q - 1) ∣ (q - p) * (f + 1) - f) :
    (p : ℝ) * q + q * (4 * Real.sqrt ((p : ℝ) - 1) - 2) ≤ ((q : ℝ) + f) ^ 2 := by
  exact triple_spacing_square_nat hp hpq ((Nat.le_of_dvd hpos hdiv).trans (Nat.sub_le _ _))

/-- Ordered natural factors satisfying the middle Korselt divisibility and
a strict increase of 2-adic valuation in the positive gap obey the real
square-spacing bound. The valuation comparison upgrades the divisor to twice
the middle predecessor, connecting integer inputs to the analytic estimate. -/
theorem triple_spacing_of_val_lt {p q f : ℕ} (hp : 1 ≤ p) (hpq : p + 2 ≤ q)
    (hk : q - 1 ∣ p * (q + f) - 1)
    (hv : padicValNat 2 (q - 1) < padicValNat 2 ((q - p) * (f + 1) - f)) :
    (p : ℝ) * q + q * (4 * Real.sqrt ((p : ℝ) - 1) - 2) ≤ ((q : ℝ) + f) ^ 2 := by
  have hpq' : p ≤ q := by linarith only [hpq]
  have hd : 2 ≤ q - p := by
    have h := Nat.sub_add_cancel hpq'
    linarith only [hpq, h]
  have hpos := triple_gap_pos (f := f) hd
  have hq : q - 1 ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt (by linarith only [hp, hpq]))
  have ht : (q - p) * (f + 1) - f ≠ 0 := Nat.ne_of_gt hpos
  have hdiv := triple_gap_dvd hp hpq hk
  exact triple_spacing_of_even_dvd hp hpq' hpos (twice_dvd_of_two_val_lt hq ht hdiv hv)

end PseudoPrime.PrimeTestBounds.MillerRabin
