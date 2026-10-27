/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaDyadicIntervalBounds
public import PseudoPrime.Analysis.GammaRamifiedDualParameterBounds

/-! # Signed finite-prefix interval bounds across ramp joins -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The exponential ramp weight is antitone on the whole real line.
Compare the exponential and linear factors on each branch and use
continuity of the joined formulas at the endpoints. This supports safe
cell bounds even when a prime power crosses either ramp join. -/
theorem exponentialRampWeight_antitone : Antitone exponentialRampWeight := by
  intro u v huv
  have he := Real.exp_le_exp.mpr (neg_le_neg huv)
  by_cases hv : v ≤ 247 / 100
  · rw [exponentialRampWeight_eq_exp_of_le_left hv,
      exponentialRampWeight_eq_exp_of_le_left (huv.trans hv)]
    exact he
  by_cases hu : u ≤ 247 / 100
  · rw [exponentialRampWeight_eq_exp_of_le_left hu]
    exact (exponentialRampWeight_bounds v).2.trans he
  by_cases hvr : v ≤ 99 / 40
  · have hur := huv.trans hvr
    rw [exponentialRampWeight_eq_middle (le_of_not_ge hv) hvr,
      exponentialRampWeight_eq_middle (le_of_not_ge hu) hur]
    exact
      div_le_div_of_nonneg_right
        (mul_le_mul he (sub_le_sub_left huv (99 / 40)) (sub_nonneg.mpr hvr) (Real.exp_pos (-u)).le)
        (by norm_num only : (0 : ℝ) ≤ 1 / 200)
  · rw [exponentialRampWeight_eq_zero (le_of_not_ge hvr)]
    exact (exponentialRampWeight_bounds u).1

/-- On a positive scale interval lo ≤ x ≤ hi, a ramified local term
is bounded by twice the ramp at the upper scale minus the exponential
at the lower scale. Use global ramp monotonicity and exp monotonicity.
This retains signed cancellation in finite cell certificates. -/
theorem gamma_ramified_local_term_le_signed_cell {a x lo hi : ℝ} (ha : 0 ≤ a) (hlo : 0 < lo)
    (hlox : lo ≤ x) (hxhi : x ≤ hi) {k : ℕ} (hk : 0 < k) :
    exponentialRampLocalCorrection 0 (a / x) k ≤
      2 * exponentialRampWeight (a / hi) - Real.exp (-(a / lo)) := by
  have hx := hlo.trans_le hlox
  have hdivhi : a / hi ≤ a / x := div_le_div₀ ha le_rfl hx hxhi
  have hdivlo : a / x ≤ a / lo := div_le_div₀ ha le_rfl hlo hlox
  have hw := exponentialRampWeight_antitone hdivhi
  have he := Real.exp_le_exp.mpr (neg_le_neg hdivlo)
  simp only [exponentialRampLocalCorrection, zero_pow hk.ne', add_zero, Complex.one_re, one_mul]
  linarith only [hw, he]

/-- On a positive scale interval, the actual signed ramified series
is bounded by the nonnegative part of a finite signed cell prefix,
divided by sqrt lo. Drop only the nonpositive cutoff tail, preserve
both terms in each retained correction, and control the denominator.
This improves the exponential-only interval bound near small scales. -/
theorem gamma_ramified_series_le_signed_cell_prefix {p : ℕ} (hp : 1 < p) {x lo hi : ℝ}
    (hlo : 0 < lo) (hlox : lo ≤ x) (hxhi : x ≤ hi) :
    (∑' k : ℕ, exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / x) (k + 1)) / Real.sqrt x ≤
      max
          (∑ k ∈ Finset.range ⌊Real.log ((99 / 40 : ℝ) * hi) / Real.log p⌋₊,
            (2 * exponentialRampWeight ((p : ℝ) ^ (k + 1) / hi) -
              Real.exp (-((p : ℝ) ^ (k + 1) / lo))))
          0 /
        Real.sqrt lo := by
  have hx : 0 < x := hlo.trans_le hlox
  have hhi : 0 < hi := hx.trans_le hxhi
  let m := ⌊Real.log ((99 / 40 : ℝ) * hi) / Real.log p⌋₊
  let u := fun k : ℕ ↦ (p : ℝ) ^ (k + 1) / x
  have hdiv (k : ℕ) : (p : ℝ) ^ (k + 1) / hi ≤ u k :=
    div_le_div₀ (pow_nonneg (Nat.cast_nonneg p) _) le_rfl hx hxhi
  have ht : ∀ k, 99 / 40 ≤ u (k + m) := fun k ↦
    (prime_power_tail_above_cutoff hp hhi (Nat.le_add_left m k)).trans (hdiv _)
  have hs :=
    exponentialRampLocalCorrection_tsum_le_prefix (Or.inl rfl) hx u
      (prime_power_div_scale_ge_linear hp hx) m ht
  have hb :=
    Finset.sum_le_sum (s := Finset.range m)
      (fun k hk ↦
        gamma_ramified_local_term_le_signed_cell (pow_nonneg (Nat.cast_nonneg p) (k + 1)) hlo hlox
          hxhi (Nat.succ_pos k))
  have hm := (hs.trans hb).trans (le_max_left _ 0)
  exact
    (div_le_div_of_nonneg_right hm (Real.sqrt_nonneg x)).trans
      (div_le_div₀ (le_max_right _ _) le_rfl (Real.sqrt_pos.mpr hlo) (Real.sqrt_le_sqrt hlox))

/-- The actual signed combined ramified allowance on a positive scale
interval is bounded by its exact Euler cost and the finite signed cell
prefix. Add the common Euler cost to the interval series bound.
This is the local quantity to enclose by rational finite certificates. -/
theorem gamma_ramified_signed_cost_le_signed_cell {p : ℕ} (hp : 1 < p) {x lo hi : ℝ} (hlo : 0 < lo)
    (hlox : lo ≤ x) (hxhi : x ≤ hi) :
    gammaRamifiedSignedCombinedCost p x ≤
      gammaPrimeEulerCost p +
        max
            (∑ k ∈ Finset.range ⌊Real.log ((99 / 40 : ℝ) * hi) / Real.log p⌋₊,
              (2 * exponentialRampWeight ((p : ℝ) ^ (k + 1) / hi) -
                Real.exp (-((p : ℝ) ^ (k + 1) / lo))))
            0 /
          Real.sqrt lo := by
  exact add_le_add le_rfl (gamma_ramified_series_le_signed_cell_prefix hp hlo hlox hxhi)

/-- The upper allowance for a ramified prime on a positive scale cell.
It keeps the exact signed Euler cost and the nonnegative part of the
finite signed ramp prefix. This is independent of the varying scale x. -/
noncomputable def gammaRamifiedSignedCellAllowance (p : ℕ) (lo hi : ℝ) : ℝ :=
  gammaPrimeEulerCost p +
    max
        (∑ k ∈ Finset.range ⌊Real.log ((99 / 40 : ℝ) * hi) / Real.log p⌋₊,
          (2 * exponentialRampWeight ((p : ℝ) ^ (k + 1) / hi) -
            Real.exp (-((p : ℝ) ^ (k + 1) / lo))))
        0 /
      Real.sqrt lo

/-- For nonnegative theta and lo ≤ x ≤ hi with lo positive, the positive
signed dual excess at x is bounded by the cell allowance minus
theta/sqrt hi. Bound the cost above and the subtracted parameter below.
This retains the parameter's cancellation in the entire scale cell. -/
theorem gamma_ramified_theta_excess_le_signed_cell {p : ℕ} (hp : 1 < p) {θ x lo hi : ℝ} (hθ : 0 ≤ θ)
    (hlo : 0 < lo) (hlox : lo ≤ x) (hxhi : x ≤ hi) :
    max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0 ≤
      max (gammaRamifiedSignedCellAllowance p lo hi - θ / Real.sqrt hi) 0 := by
  have hx := hlo.trans_le hlox
  have hc := gamma_ramified_signed_cost_le_signed_cell hp hlo hlox hxhi
  change gammaRamifiedSignedCombinedCost p x ≤ gammaRamifiedSignedCellAllowance p lo hi at hc
  have hm : θ / Real.sqrt hi ≤ gammaRamifiedThetaParameter θ x :=
    div_le_div₀ hθ le_rfl (Real.sqrt_pos.mpr hx) (Real.sqrt_le_sqrt hxhi)
  apply max_le_max _ le_rfl
  linarith only [hc, hm]

/-- Every finite prime excess sum on a positive cell is bounded by the
sum of signed cell allowances with the parameter lower bound retained.
Apply the pointwise cell estimate and nonnegativity of prime logarithms.
This supplies rational interval targets for the fixed support sum. -/
theorem gamma_ramified_theta_excess_sum_le_signed_cell (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime)
    {θ x lo hi : ℝ} (hθ : 0 ≤ θ) (hlo : 0 < lo) (hlox : lo ≤ x) (hxhi : x ≤ hi) :
    (∑ p ∈ R,
        Real.log p *
          max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0) ≤
      ∑ p ∈ R,
        Real.log p * max (gammaRamifiedSignedCellAllowance p lo hi - θ / Real.sqrt hi) 0 := by
  exact
    Finset.sum_le_sum
      (fun p hp ↦
        mul_le_mul_of_nonneg_left
          (gamma_ramified_theta_excess_le_signed_cell (hR p hp).one_lt hθ hlo hlox hxhi)
          (Real.log_nonneg (by exact_mod_cast (hR p hp).one_le)))

end PseudoPrime.Analysis
