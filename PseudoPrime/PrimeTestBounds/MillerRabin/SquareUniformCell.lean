/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareCoverageRows

/-! # Uniform coefficient cells for prime squares -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A logarithmic interval and an index of the square coverage row used on that interval.
Its rational endpoints permit a finite check of coverage and the coefficient budget. -/
structure SquareUniformCell where
  /-- Index of the certified square coverage row. -/
  row : ℕ
  /-- Left logarithmic endpoint. -/
  lo : ℚ
  /-- Right logarithmic endpoint. -/
  hi : ℚ

/-- Check that a square coverage row reaches the cell and its prime cutoff is at most
`(371/1000) * lo²`. The lower endpoint is required to be nonnegative. -/
def SquareUniformCell.check (c : SquareUniformCell) : Bool :=
  match squareCoverages[c.row]? with
  | none => false
  | some d =>
    decide (0 ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.hi ≤ d.target ∧ (d.bound : ℚ) ≤ (371 / 1000) * c.lo ^ 2)

/-- Under RH, a checked cell bounds an odd prime square's rejecting prime by
`(371/1000) * (log n)²` throughout the cell. The row supplies the witness, and monotonicity
of squaring on nonnegative inputs transfers the rational budget to `log n`. -/
theorem SquareUniformCell.sound {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (c : SquareUniformCell) (hcheck : c.check = true)
    (hlo : (c.lo : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (c.hi : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (371 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  cases heq : squareCoverages[c.row]? with
  | none => simp only [SquareUniformCell.check, heq, Bool.false_eq_true] at hcheck
  | some
    d =>
    have hc :
      0 ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.hi ≤ d.target ∧ (d.bound : ℚ) ≤ (371 / 1000) * c.lo ^ 2 := by
      apply of_decide_eq_true
      simpa only [SquareUniformCell.check, heq] using hcheck
    have hlo0 : (0 : ℝ) ≤ c.lo := by exact_mod_cast hc.1
    have hsq : (c.lo : ℝ) ^ 2 ≤ (Real.log n) ^ 2 := pow_le_pow_left₀ hlo0 hlo 2
    have hbudget : (d.bound : ℝ) ≤ (371 / 1000 : ℝ) * (c.lo : ℝ) ^ 2 := by
      have h := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2
      simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
        h
    have htarget : Real.log n ≤ (d.target : ℝ) := hhi.trans ((Rat.cast_le (K := ℝ)).mpr hc.2.2.1)
    obtain ⟨r, hr, hrB, hfail⟩ :=
      squareCoverages_sound hn ho hp hp2 hpow hRH d (List.mem_of_getElem? heq) htarget
    have hrB' : (r : ℝ) ≤ d.bound := by exact_mod_cast hrB
    refine ⟨r, hr, ?_, hfail⟩
    nlinarith only [hrB', hbudget, hsq]

end PseudoPrime.PrimeTestBounds.MillerRabin
