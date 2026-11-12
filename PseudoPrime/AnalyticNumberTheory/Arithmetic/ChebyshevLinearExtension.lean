/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevFiveTerm
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevBounds

/-! # Extending linear Chebyshev bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- On a closed interval, an upper bound for `psi` at the right endpoint implies a linear
bound throughout the interval if it fits the linear budget at the left endpoint. This lets
finite certificates cover many arguments with one endpoint check. -/
theorem psi_le_linear_on_interval {C a b x : ℝ} (hC : 0 ≤ C) (ha : a ≤ x) (hb : x ≤ b)
    (hpoint : Chebyshev.psi b ≤ C * a) : Chebyshev.psi x ≤ C * x := by
  exact (Chebyshev.psi_mono hb).trans (hpoint.trans (mul_le_mul_of_nonneg_left ha hC))

/-- A bound at an integer endpoint controls the cell ending just before the next integer.
The Chebyshev function is constant between consecutive integers, so one endpoint
certificate proves the linear bound throughout this half-open interval. -/
theorem psi_le_linear_on_nat_cell {C x : ℝ} {a b : ℕ} (hC : 0 ≤ C) (hx0 : 0 ≤ x) (ha : (a : ℝ) ≤ x)
    (hb : x < (b : ℝ) + 1) (hpoint : Chebyshev.psi b ≤ C * a) : Chebyshev.psi x ≤ C * x := by
  have hf : Nat.floor x ≤ b := by
    apply Nat.lt_succ_iff.mp
    apply (Nat.floor_lt hx0).mpr
    simpa only [Nat.cast_succ] using hb
  rw [Chebyshev.psi_eq_psi_coe_floor]
  exact
    (Chebyshev.psi_mono (Nat.cast_le.mpr hf)).trans (hpoint.trans (mul_le_mul_of_nonneg_left ha hC))

/-- A linear bound through `Y` extends to every nonnegative argument when the five-term
increment error fits the remaining budget above `Y`. Strong induction on integer arguments
uses the bound at the floor of one sixth of the current argument. -/
theorem psi_le_linear_of_prefix {C Y : ℝ} (hC : 0 ≤ C) (hY : 30 ≤ Y)
    (hprefix : ∀ x : ℝ, 0 ≤ x → x ≤ Y → Chebyshev.psi x ≤ C * x)
    (htail : ∀ x : ℝ, Y < x → chebyshevSlope * x + 5 * Real.log x - 7 + C * (x / 6) ≤ C * x) :
    ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ C * x := by
  have hNat : ∀ n : ℕ, Chebyshev.psi (n : ℝ) ≤ C * n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hsmall : (n : ℝ) ≤ Y
      · exact hprefix n (Nat.cast_nonneg n) hsmall
      · have hn : Y < (n : ℝ) := lt_of_not_ge hsmall
        let m : ℕ := ⌊(n : ℝ) / 6⌋₊
        have hdiv : (0 : ℝ) ≤ n / 6 := div_nonneg (Nat.cast_nonneg n) (by norm_num only)
        have hm : (m : ℝ) ≤ (n : ℝ) / 6 := Nat.floor_le hdiv
        have hmn : m < n := by
          have hnpos : (0 : ℝ) < n := by linarith only [hY, hn]
          have hmR : (m : ℝ) < n := by linarith only [hm, hnpos]
          exact_mod_cast hmR
        have hpsi : Chebyshev.psi ((n : ℝ) / 6) ≤ C * ((n : ℝ) / 6) := by
          rw [Chebyshev.psi_eq_psi_coe_floor]
          exact (ih m hmn).trans (mul_le_mul_of_nonneg_left hm hC)
        have hinc := psi_diff_upper_fiveTerm (x := (n : ℝ)) (by linarith only [hY, hn])
        have hbudget := htail n hn
        linarith only [hpsi, hinc, hbudget]
  intro x hx
  rw [Chebyshev.psi_eq_psi_coe_floor]
  exact (hNat ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left (Nat.floor_le hx) hC)

/-- A bound for `psi` up to 11723 extends to all nonnegative arguments with coefficient 111/100.
The five-term increment and a tangent logarithm estimate control the tail. -/
theorem psi_le_111_of_prefix
    (hprefix : ∀ x : ℝ, 0 ≤ x → x ≤ 11723 → Chebyshev.psi x ≤ (111 / 100 : ℝ) * x) :
    ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ (111 / 100 : ℝ) * x := by
  apply psi_le_linear_of_prefix (by norm_num only) (by norm_num only) hprefix
  intro x hx
  have hx0 : 0 < x := by linarith only [hx]
  have hcheck : Analysis.rationalLogIntervalCheck (11723 / 8192) 2 16 0 (36 / 100) = true := by
    decide +kernel
  have hrat := (Analysis.rationalLogIntervalCheck_sound hcheck).2
  have hlog : Real.log (11723 : ℝ) ≤ 946 / 100 := by
    have heq : (11723 : ℝ) = 2 ^ (13 : ℕ) * (11723 / 8192) := by norm_num only
    rw [heq, Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    norm_num only [Nat.cast_ofNat, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hrat ⊢
    linarith only [hrat, Real.log_two_lt_d9]
  have ht := Analysis.log_le_log_add_sub_div (a := (11723 : ℝ)) (y := x) (by norm_num only) hx0
  have hs := chebyshevSlope_bounds.2
  have hm := mul_le_mul_of_nonneg_right hs hx0.le
  nlinarith only [ht, hlog, hm, hx]

/-- Integer endpoint certificates covering every integer from one through 11723 imply the
global `111/100` bound for `psi`. Each cell retains its own endpoint inequality; the real
prefix follows from the floor identity and the tail from the five-term estimate. -/
theorem psi_le_111_of_nat_cells
    (hcells :
      ∀ n : ℕ,
        1 ≤ n → n ≤ 11723 → ∃ a b : ℕ, a ≤ n ∧ n ≤ b ∧ Chebyshev.psi b ≤ (111 / 100 : ℝ) * a) :
    ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ (111 / 100 : ℝ) * x := by
  apply psi_le_111_of_prefix
  intro x hx hxY
  by_cases hsmall : x < 1
  · rw [Chebyshev.psi_eq_zero_of_lt_two (by linarith only [hsmall])]
    exact mul_nonneg (by norm_num only) hx
  · have hx1 : 1 ≤ x := le_of_not_gt hsmall
    have hn1 : 1 ≤ Nat.floor x := Nat.le_floor (by simpa only [Nat.cast_one] using hx1)
    have hnY : Nat.floor x ≤ 11723 := Nat.floor_le_of_le hxY
    obtain ⟨a, b, ha, hb, hpoint⟩ := hcells (Nat.floor x) hn1 hnY
    have haR : (a : ℝ) ≤ x := (Nat.cast_le.mpr ha).trans (Nat.floor_le hx)
    have hbR : x < (b : ℝ) + 1 := by
      have hf := Nat.lt_floor_add_one x
      have hb' : (Nat.floor x : ℝ) ≤ b := Nat.cast_le.mpr hb
      linarith only [hf, hb']
    exact psi_le_linear_on_nat_cell (by norm_num only) hx haR hbR hpoint

end PseudoPrime.AnalyticNumberTheory.Arithmetic
