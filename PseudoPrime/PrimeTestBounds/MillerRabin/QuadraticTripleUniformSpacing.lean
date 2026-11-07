/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleValuation
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030KorseltParameters

/-! # Spacing for uniform Korselt triples -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The ordered odd prime factors of a uniform Korselt triple satisfy the
weighted square bound for the largest factor. The common valuations and the
middle predecessor divisibility supply the arithmetic spacing hypotheses;
this bound is used in the low-range local-modulus comparison. -/
theorem uniformKorselt_square_spacing {n p q r : ℕ} (hn : n = p * q * r) (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpO : Odd p) (hqO : Odd q) (hrO : Odd r) (hpq : p < q)
    (hqr : q < r) (hu : UniformKorseltTriple n) :
    (p : ℝ) * q + q * (4 * Real.sqrt ((p : ℝ) - 1) - 2) ≤ (r : ℝ) ^ 2 := by
  have hpn : p ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) r
  have hqn : q ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) r
  have hrn : r ∣ n := hn ▸ dvd_mul_left r (p * q)
  have hv := hu.2.2.2 p q hp hq hpn hqn
  have hvr := hu.2.2.2 q r hq hr hqn hrn
  have hpr : 1 ≤ p * r := Nat.mul_pos hp.one_lt.le hr.one_lt.le
  have hq' : q - 1 ∣ p * r * q - 1 := by
    simpa only [hn, mul_assoc, mul_comm, mul_left_comm] using hu.2.2.1 q hq hqn
  have hk := korselt_predecessor_factor hpr hq.one_lt.le hq'
  have hpq2 : p + 2 ≤ q := by
    have hd := (Nat.Odd.sub_odd hqO hpO).two_dvd
    have hpos : 0 < q - p := Nat.sub_pos_of_lt hpq
    have htwo : 2 ≤ q - p := Nat.le_of_dvd hpos hd
    have hs := Nat.sub_add_cancel hpq.le
    linarith only [htwo, hs]
  exact triple_square_of_korselt hp.one_lt hq.one_lt hr.one_lt hpO hqO hrO hpq2 hqr.le hv hvr hk

/-- A nonnegative weighted square gap yields a logarithmic improvement for
the product of the two smaller positive factors. Monotonicity of the logarithm
converts the ratio bound, and logarithm identities express the result in
terms of the full and pair products for the local witness estimate. -/
theorem log_pair_shift_of_square {p q r b : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hb : 0 ≤ b)
    (hgap : p * q + q * b ≤ r ^ 2) :
    Real.log (1 + b / p) ≤ 2 * Real.log (p * q * r) - 3 * Real.log (p * q) := by
  have hpq : 0 < p * q := mul_pos hp hq
  have hbase : 0 < 1 + b / p := by
    have hdiv : 0 ≤ b / p := div_nonneg hb hp.le
    linarith only [hdiv]
  have hratio : 1 + b / p ≤ r ^ 2 / (p * q) := by
    apply (le_div_iff₀ hpq).2
    have heq : (1 + b / p) * (p * q) = p * q + q * b := by
      rw [add_mul, one_mul, ← mul_assoc, div_mul_cancel₀ b hp.ne']
      ring
    rw [heq]
    exact hgap
  have hl := Real.log_le_log hbase hratio
  rw [Real.log_div (pow_ne_zero _ hr.ne') hpq.ne', Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  rw [Real.log_mul hpq.ne' hr.ne']
  linarith only [hl]

/-- The ordered factors of a uniform Korselt triple satisfy a logarithmic
pair-modulus shift for any nonnegative lower bound on the weighted spacing.
The square spacing bound feeds the real logarithmic conversion, which is
suited to inserting certified numerical lower bounds in the low-range cells. -/
theorem uniformKorselt_log_pair_shift {n p q r : ℕ} (hn : n = p * q * r) (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpO : Odd p) (hqO : Odd q) (hrO : Odd r) (hpq : p < q)
    (hqr : q < r) (hu : UniformKorseltTriple n) (b : ℝ) (hb : 0 ≤ b)
    (hb' : b ≤ 4 * Real.sqrt ((p : ℝ) - 1) - 2) :
    Real.log (1 + b / p) ≤ 2 * Real.log n - 3 * Real.log ((p : ℝ) * q) := by
  have hg := uniformKorselt_square_spacing hn hp hq hr hpO hqO hrO hpq hqr hu
  have hm := mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hgap : (p : ℝ) * q + q * b ≤ (r : ℝ) ^ 2 := by linarith only [hg, hm]
  have hl :=
    log_pair_shift_of_square (Nat.cast_pos.mpr hp.pos) (Nat.cast_pos.mpr hq.pos)
      (Nat.cast_pos.mpr hr.pos) hb hgap
  simpa only [hn, Nat.cast_mul] using hl

/-- The spacing correction `(4√(x-1)-2)/x` decreases on `[5, ∞)`.
Writing both inputs as squares of their square roots factors the difference
into nonnegative terms, yielding the uniform correction used for each cell. -/
theorem spacing_correction_antitone {p P : ℝ} (hp : 5 ≤ p) (hpP : p ≤ P) :
    (4 * Real.sqrt (P - 1) - 2) / P ≤ (4 * Real.sqrt (p - 1) - 2) / p := by
  have hp0 : 0 < p := by linarith only [hp]
  have hP0 : 0 < P := by linarith only [hp, hpP]
  have hps : 0 ≤ p - 1 := by linarith only [hp]
  have hPs : 0 ≤ P - 1 := by linarith only [hp, hpP]
  have hs := Real.sq_sqrt hps
  have ht := Real.sq_sqrt hPs
  have hst := Real.sqrt_le_sqrt (sub_le_sub_right hpP 1)
  have hs0 := Real.sqrt_nonneg (p - 1)
  have hs2 : 2 ≤ Real.sqrt (p - 1) := by nlinarith only [hp, hs, hs0]
  have hcore :
    0 ≤
      4 * (Real.sqrt (p - 1) * Real.sqrt (P - 1) - 1) -
        2 * (Real.sqrt (p - 1) + Real.sqrt (P - 1)) := by
    nlinarith only [hs2, hst, mul_nonneg (sub_nonneg.mpr hs2) (sub_nonneg.mpr hst)]
  have hm := mul_nonneg (sub_nonneg.mpr hst) hcore
  have hp' : p = Real.sqrt (p - 1) ^ 2 + 1 := by linarith only [hs]
  have hP' : P = Real.sqrt (P - 1) ^ 2 + 1 := by linarith only [ht]
  apply (div_le_div_iff₀ hP0 hp0).2
  conv_lhs => rw [hp']
  conv_rhs => rw [hP']
  nlinarith only [hm]

/-- A known upper bound `P` for the smallest factor gives a uniform positive
logarithmic shift for the pair modulus of a uniform Korselt triple, provided
the smallest factor is at least five. The correction is decreased to its
value at `P` before applying monotonicity of the logarithm. -/
theorem uniformKorselt_log_shift_of_bound {n p q r : ℕ} (hn : n = p * q * r) (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpO : Odd p) (hqO : Odd q) (hrO : Odd r) (hpq : p < q)
    (hqr : q < r) (hu : UniformKorseltTriple n) (P : ℝ) (hp5 : 5 ≤ (p : ℝ)) (hpP : (p : ℝ) ≤ P) :
    Real.log (1 + (4 * Real.sqrt (P - 1) - 2) / P) ≤
      2 * Real.log n - 3 * Real.log ((p : ℝ) * q) := by
  have hPs : 0 ≤ P - 1 := by linarith only [hp5, hpP]
  have hP0 : 0 < P := by linarith only [hp5, hpP]
  have hsq := Real.sq_sqrt hPs
  have hs0 := Real.sqrt_nonneg (P - 1)
  have hs2 : 2 ≤ Real.sqrt (P - 1) := by nlinarith only [hp5, hpP, hsq, hs0]
  have hnum : 0 ≤ 4 * Real.sqrt (P - 1) - 2 := by linarith only [hs2]
  have hbase : 0 < 1 + (4 * Real.sqrt (P - 1) - 2) / P := by
    have hd := div_nonneg hnum hP0.le
    linarith only [hd]
  have hps : 0 ≤ (p : ℝ) - 1 := by linarith only [hp5]
  have hsq' := Real.sq_sqrt hps
  have hs0' := Real.sqrt_nonneg ((p : ℝ) - 1)
  have hs2' : 2 ≤ Real.sqrt ((p : ℝ) - 1) := by nlinarith only [hp5, hsq', hs0']
  have hb : 0 ≤ 4 * Real.sqrt ((p : ℝ) - 1) - 2 := by linarith only [hs2']
  have hl :=
    uniformKorselt_log_pair_shift hn hp hq hr hpO hqO hrO hpq hqr hu
      (4 * Real.sqrt ((p : ℝ) - 1) - 2) hb le_rfl
  have hc := spacing_correction_antitone hp5 hpP
  have hc' : 1 + (4 * Real.sqrt (P - 1) - 2) / P ≤ 1 + (4 * Real.sqrt ((p : ℝ) - 1) - 2) / p := by
    linarith only [hc]
  exact le_trans (Real.log_le_log hbase hc') hl

/-- An ordered positive triple whose product is `n` has smallest factor below
`P` whenever `log n < 3 log P`. The product dominates the smallest factor's
cube; logarithmic monotonicity then gives the contradiction for `P ≤ p`. -/
theorem smallest_factor_lt_of_log_bound {n p q r : ℕ} (hn : n = p * q * r) (hp : 0 < p)
    (hpq : p ≤ q) (hqr : q ≤ r) {P : ℝ} (hP : 0 < P) (hlog : Real.log n < 3 * Real.log P) :
    (p : ℝ) < P := by
  have hc : p ^ 3 ≤ n := by
    rw [hn, pow_succ, pow_two]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left p hpq) (hpq.trans hqr)
  have hcR : (p : ℝ) ^ 3 ≤ n := by exact_mod_cast hc
  have hlogp := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hp) 3) hcR
  rw [Real.log_pow] at hlogp
  norm_num only [Nat.cast_ofNat] at hlogp
  by_contra h
  have hPp : P ≤ (p : ℝ) := le_of_not_gt h
  have hplog := Real.log_le_log hP hPp
  linarith only [hplog, hlogp, hlog]

/-- A logarithmic upper bound on a uniform Korselt triple supplies the fixed
pair-modulus shift at `P` when its least prime factor is at least five. The
factor bound follows from the ordered product before applying the spacing
estimate. This is the arithmetic input to the low-range witness cells. -/
theorem uniformKorselt_log_shift_of_log_bound {n p q r : ℕ} (hn : n = p * q * r) (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpO : Odd p) (hqO : Odd q) (hrO : Odd r) (hpq : p < q)
    (hqr : q < r) (hu : UniformKorseltTriple n) (P : ℝ) (hp5 : 5 ≤ (p : ℝ)) (hP : 0 < P)
    (hlog : Real.log n < 3 * Real.log P) :
    Real.log (1 + (4 * Real.sqrt (P - 1) - 2) / P) ≤
      2 * Real.log n - 3 * Real.log ((p : ℝ) * q) := by
  have hpP := smallest_factor_lt_of_log_bound hn hp.pos hpq.le hqr.le hP hlog
  exact uniformKorselt_log_shift_of_bound hn hp hq hr hpO hqO hrO hpq hqr hu P hp5 hpP.le

end PseudoPrime.PrimeTestBounds.MillerRabin
