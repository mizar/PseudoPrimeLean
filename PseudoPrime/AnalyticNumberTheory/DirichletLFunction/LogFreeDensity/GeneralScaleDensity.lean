/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.GeneralScaleIncidence

/-! # Exponential bounds for general-scale high-prime zero counting -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- For a natural order envelope, its summed coefficient energy is at most
`3(log 4+4)(n+1)^2 4^n`. Bound every summand by the last-order majorant and sum
the constant over the finite range. This gives an explicit exponential order bound. -/
theorem highPrimeOrderEnvelopeEnergy_le (n : ℕ) :
    highPrimeOrderEnvelopeEnergy n ≤ (3 * (Real.log 4 + 4)) * (n + 1 : ℝ) ^ 2 * (4 : ℝ) ^ n := by
  have hH : 0 ≤ Real.log 4 + 4 := add_nonneg (Real.log_nonneg (by norm_num only)) (by norm_num only)
  have hterm (r : ℕ) (hr : r ∈ Finset.range (n + 1)) :
    ((r + 1 : ℝ) * (2 : ℝ) ^ (2 * r + 1)) * ((3 / 2 : ℝ) * (Real.log 4 + 4)) ≤
      (3 * (Real.log 4 + 4)) * (n + 1 : ℝ) * (4 : ℝ) ^ n := by
    have hrn : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    have hrreal : (r + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hrn 1
    have hpow : (4 : ℝ) ^ r ≤ (4 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num only) hrn
    have hid : (2 : ℝ) ^ (2 * r + 1) = 2 * (4 : ℝ) ^ r := by
      rw [pow_succ, pow_mul]
      norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num only]
      ring
    rw [hid]
    calc
      _ = (3 * (Real.log 4 + 4)) * ((r + 1 : ℝ) * (4 : ℝ) ^ r) := by ring
      _ ≤ (3 * (Real.log 4 + 4)) * ((n + 1 : ℝ) * (4 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hrreal hpow (pow_nonneg (by norm_num only) _)
            (by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
          (mul_nonneg (by norm_num only) hH)
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hterm
  calc
    _ ≤ ∑ _r ∈ Finset.range (n + 1), (3 * (Real.log 4 + 4)) * (n + 1 : ℝ) * (4 : ℝ) ^ n := hsum
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- For a real exponential signal parameter, the squared inverse signal and sampling
exponential combine to `256 exp(3x)`. Expand inverses and combine exponentials.
This isolates the exponential loss in the normalized zero-count estimate. -/
theorem exponential_signal_sampling_factor (x : ℝ) :
    (1 / (Real.exp (-x) / 16) ^ 2) * Real.exp x = 256 * Real.exp (3 * x) := by
  rw [div_pow, Real.exp_neg, inv_pow, one_div_div, div_inv_eq_mul]
  rw [mul_assoc]
  rw [show Real.exp x ^ 2 * Real.exp x = Real.exp (3 * x)
      by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring]
  norm_num only

/-- Given a detector exponent, scaled support coefficient, local multiplicity weight,
and signal and order caps, collect the explicit hybrid zero-count upper bound.
The factors are coefficient energy, squared inverse signal, and physical-window
sampling loss. This separates numerical envelope estimates from actual zero counting. -/
noncomputable def highPrimeGeneralScaleCountEnvelope (D c L : ℝ) (K n : ℕ) : ℝ :=
  (L * (4096 * (1 + (c * K / 8) ^ 2 / 2) * highPrimeOrderEnvelopeEnergy n) /
      (Real.exp (-(D * K)) / 16) ^ 2) *
    (32 * primeLogPowerVariationBound n * Real.exp (D * K))

/-- For a nonnegative local weight, the numerical count envelope is bounded by a
polynomial in the order and support coefficient times one exponential in the order.
Insert the coefficient-energy bound, expand the variation constant, and combine
inverse-signal exponentials. This exposes all order dependence for scale comparison. -/
theorem highPrimeGeneralScaleCountEnvelope_le (D c L : ℝ) (K n : ℕ) (hL : 0 ≤ L) :
    highPrimeGeneralScaleCountEnvelope D c L K n ≤
      603979776 * (Real.log 4 + 4) ^ 2 * L * (n + 1 : ℝ) ^ 3 * (1 + (c * K / 8) ^ 2 / 2) *
        Real.exp (3 * D * K + Real.log 8 * n) := by
  have hH : 0 ≤ Real.log 4 + 4 := add_nonneg (Real.log_nonneg (by norm_num only)) (by norm_num only)
  have hfactor :
    0 ≤
      L * (4096 * (1 + (c * K / 8) ^ 2 / 2)) / (Real.exp (-(D * K)) / 16) ^ 2 *
        (32 * primeLogPowerVariationBound n * Real.exp (D * K)) :=
    mul_nonneg
      (div_nonneg
        (mul_nonneg hL
          (mul_nonneg (by norm_num only)
            (add_nonneg zero_le_one (div_nonneg (sq_nonneg _) (by norm_num only)))))
        (sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num only) (primeLogPowerVariationBound_pos _).le)
        (Real.exp_nonneg _))
  have hbound := mul_le_mul_of_nonneg_right (highPrimeOrderEnvelopeEnergy_le n) hfactor
  have hpower : (4 : ℝ) ^ n * (2 : ℝ) ^ (n + 1) = 2 * (8 : ℝ) ^ n := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num only [show (4 : ℝ) * 2 = 8 by norm_num only]
    ring
  have hexp : (8 : ℝ) ^ n = Real.exp (Real.log 8 * n) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num only)]
  have hsignal := exponential_signal_sampling_factor (D * K)
  have hexpjoin :
    Real.exp (3 * D * K) * Real.exp (Real.log 8 * n) = Real.exp (3 * D * K + Real.log 8 * n) :=
    (Real.exp_add _ _).symm
  calc
    _ =
        highPrimeOrderEnvelopeEnergy n *
          (L * (4096 * (1 + (c * K / 8) ^ 2 / 2)) / (Real.exp (-(D * K)) / 16) ^ 2 *
            (32 * primeLogPowerVariationBound n * Real.exp (D * K))) :=
      by
      dsimp only [highPrimeGeneralScaleCountEnvelope]
      ring
    _ ≤
        ((3 * (Real.log 4 + 4)) * (n + 1 : ℝ) ^ 2 * (4 : ℝ) ^ n) *
          (L * (4096 * (1 + (c * K / 8) ^ 2 / 2)) / (Real.exp (-(D * K)) / 16) ^ 2 *
            (32 * primeLogPowerVariationBound n * Real.exp (D * K))) :=
      hbound
    _ = _ := by
      dsimp only [primeLogPowerVariationBound]
      have hsignal' :
        (1 / (Real.exp (-(D * K)) / 16) ^ 2) * Real.exp (D * K) = 256 * Real.exp (3 * D * K) := by
        simpa only [mul_assoc] using hsignal
      calc
        _ =
            (1179648 * (Real.log 4 + 4) ^ 2 * L * (n + 1 : ℝ) ^ 3 * (1 + (c * K / 8) ^ 2 / 2)) *
              ((4 : ℝ) ^ n * (2 : ℝ) ^ (n + 1)) *
              ((1 / (Real.exp (-(D * K)) / 16) ^ 2) * Real.exp (D * K)) :=
          by ring
        _ = _ := by
          rw [hpower, hsignal', hexp]
          rw [← hexpjoin]
          ring

/-- If the detector cap, support coefficient, and local weight grow at most linearly
in a real scale at least one, their count envelope grows at most exponentially in
that scale. Bound its polynomial factors by the eighth power of the scale and
absorb that power into an exponential. This supplies the finite-exponent log-free bound. -/
theorem highPrimeGeneralScaleCountEnvelope_le_exp (D c L b c₀ l x : ℝ) (N : ℕ) (hD : 0 ≤ D)
    (hc : 0 ≤ c) (hL : 0 ≤ L) (hb : 0 ≤ b) (hc₀ : 0 ≤ c₀) (hl : 0 ≤ l) (hx : 1 ≤ x)
    (hN : (N : ℝ) ≤ b * x) (hcupper : c ≤ c₀ * x) (hLupper : L ≤ l * x) :
    highPrimeGeneralScaleCountEnvelope D c L N (4 * N) ≤
      (603979776 * (Real.log 4 + 4) ^ 2 * l * (4 * b + 1) ^ 3 * (1 + (c₀ * b) ^ 2)) *
        Real.exp ((3 * D * b + 4 * Real.log 8 * b + 8) * x) := by
  have hxnonneg : 0 ≤ x := zero_le_one.trans hx
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num only)
  have hH : 0 ≤ 603979776 * (Real.log 4 + 4) ^ 2 := mul_nonneg (by norm_num only) (sq_nonneg _)
  have hnp : (4 * N + 1 : ℕ) ≤ (4 * b + 1) * x := by
    push_cast
    linarith only [hN, hx]
  have hnp' : (4 * (N : ℝ) + 1) ^ 3 ≤ ((4 * b + 1) * x) ^ 3 :=
    pow_le_pow_left₀ (by linarith only [hNnonneg]) (by exact_mod_cast hnp) 3
  have hprod : c * (N : ℝ) ≤ c₀ * b * x ^ 2 := by
    have h := mul_le_mul hcupper hN hNnonneg (mul_nonneg hc₀ hxnonneg)
    nlinarith only [h]
  have hfrac : c * (N : ℝ) / 8 ≤ c₀ * b * x ^ 2 := by
    have hnonneg := mul_nonneg (mul_nonneg hc₀ hb) (sq_nonneg x)
    linarith only [hprod, hnonneg]
  have hsq := pow_le_pow_left₀ (div_nonneg (mul_nonneg hc hNnonneg) (by norm_num only)) hfrac 2
  have hpoly : 1 + (c * (N : ℝ) / 8) ^ 2 / 2 ≤ (1 + (c₀ * b) ^ 2) * x ^ 4 := by
    have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx
    calc
      _ ≤ 1 + (c₀ * b * x ^ 2) ^ 2 := by nlinarith only [hsq, sq_nonneg (c₀ * b * x ^ 2)]
      _ ≤ x ^ 4 + (c₀ * b) ^ 2 * x ^ 4 := by nlinarith only [hx4]
      _ = _ := by ring
  have hcoef : 0 ≤ 3 * D + 4 * Real.log 8 := by linarith only [hD, hlog8]
  have hexparg :
    3 * D * (N : ℝ) + Real.log 8 * ((4 * N : ℕ) : ℝ) ≤ (3 * D * b + 4 * Real.log 8 * b) * x := by
    have h := mul_le_mul_of_nonneg_left hN hcoef
    push_cast
    nlinarith only [h]
  have hexp := Real.exp_le_exp.mpr hexparg
  have hLL : 0 ≤ l * x := mul_nonneg hl hxnonneg
  have hnn : 0 ≤ ((4 * b + 1) * x) ^ 3 := pow_nonneg (mul_nonneg (by linarith only [hb]) hxnonneg) _
  have hpp : 0 ≤ (1 + (c₀ * b) ^ 2) * x ^ 4 :=
    mul_nonneg (add_nonneg zero_le_one (sq_nonneg _)) (pow_nonneg hxnonneg _)
  have hstep :=
    mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_left hLupper hH) hnp'
        (pow_nonneg (by linarith only [hNnonneg] : 0 ≤ 4 * (N : ℝ) + 1) _) (mul_nonneg hH hLL))
      hpoly (add_nonneg zero_le_one (div_nonneg (sq_nonneg _) (by norm_num only)))
      (mul_nonneg (mul_nonneg hH hLL) hnn)
  have hfinal :=
    mul_le_mul hstep hexp (Real.exp_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg hH hLL) hnn) hpp)
  have hxexp : x ≤ Real.exp x := by linarith only [Real.add_one_le_exp x]
  have hx8 : x ^ 8 ≤ Real.exp (8 * x) := by
    have h := pow_le_pow_left₀ hxnonneg hxexp 8
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using h
  let C := 603979776 * (Real.log 4 + 4) ^ 2 * l * (4 * b + 1) ^ 3 * (1 + (c₀ * b) ^ 2)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg (mul_nonneg hH hl) (pow_nonneg (by linarith only [hb]) _))
      (add_nonneg zero_le_one (sq_nonneg _))
  calc
    _ ≤
        603979776 * (Real.log 4 + 4) ^ 2 * L * ((4 * N : ℕ) + 1 : ℝ) ^ 3 *
          (1 + (c * N / 8) ^ 2 / 2) *
          Real.exp (3 * D * N + Real.log 8 * (4 * N : ℕ)) :=
      highPrimeGeneralScaleCountEnvelope_le D c L N (4 * N) hL
    _ ≤ C * x ^ 8 * Real.exp ((3 * D * b + 4 * Real.log 8 * b) * x) := by
      convert hfinal using 1
      · norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      · dsimp only [C]
        ring
    _ ≤ C * Real.exp (8 * x) * Real.exp ((3 * D * b + 4 * Real.log 8 * b) * x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx8 hC) (Real.exp_nonneg _)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- For conductors and heights bounded by a common scale at least three, the
conductor-height logarithm is at most three times the scale logarithm. Bound its
argument by the cube of the scale and use logarithmic monotonicity.
This compares all family budgets with the density exponent. -/
theorem log_conductor_height_product_le_three (R T : ℕ) (hR : 3 ≤ R) (hT : T ≤ R) :
    Real.log ((R : ℝ) * ((T : ℝ) + 3)) ≤ 3 * Real.log (R : ℝ) := by
  have hRreal : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have hTreal : (T : ℝ) ≤ R := by exact_mod_cast hT
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num only) hRreal
  have harg : (R : ℝ) * ((T : ℝ) + 3) ≤ (R : ℝ) ^ 3 := by
    nlinarith only [hRreal, hTreal, sq_nonneg ((R : ℝ) - 3)]
  have hlog :=
    Real.log_le_log
      (mul_pos hRpos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg T) (by norm_num only))) harg
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

/-- There are absolute positive constants giving an exponential bound for the actual
primitive-family occurrence count in every sufficiently large common conductor scale,
provided the positive shift is small and its scaled logarithm is at least one.
Discharge the detector cap, support length, and local multiplicity weight, insert the
hybrid mean square, and absorb the order envelope into the exponential. No detector
or numerical budget remains as an input. This proves the general-scale small-shift
part of the log-free zero-density estimate. -/
theorem exists_primitiveFamily_small_shift_exponential_count_bound :
    ∃ C A η₀ : ℝ,
      0 < C ∧
        0 < A ∧
        0 < η₀ ∧
        ∃ R₀ : ℕ,
          3 ≤ R₀ ∧
            ∀ (R T : ℕ) (σ η : ℝ),
              R₀ ≤ R →
                T ≤ R →
                σ ≤ 1 →
                1 - σ ≤ η →
                0 < η →
                η ≤ η₀ →
                1 ≤ η * Real.log (R : ℝ) →
                primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight R σ T ≤
                  C * Real.exp (A * (η * Real.log (R : ℝ))) := by
  obtain ⟨B, η₁, hB, hη₁, R₁, hR₁, hdetector⟩ :=
    exists_uniform_general_scale_occurrence_meanSquare_bound
  obtain ⟨η₂, hη₂, hηsmall, _, R₂, hR₂, henergy⟩ :=
    eventually_general_scale_prime_energy_budget B hB
  let D := Real.log 414720
  let b := 4 * B
  let H := Real.log (24 * (Real.log 4 + 4))
  let c₀ := 2 * ((4 + D) * b + H) + 6 + Real.log 3
  let l := 49 * completedZeroLocalLogBoundConstant + 1
  let C := 603979776 * (Real.log 4 + 4) ^ 2 * l * (4 * b + 1) ^ 3 * (1 + (c₀ * b) ^ 2)
  let A := 3 * D * b + 4 * Real.log 8 * b + 8
  have hD : 0 ≤ D := Real.log_nonneg (by norm_num only)
  have hb : 0 ≤ b := mul_nonneg (by norm_num only) hB.le
  have hH : 0 ≤ H :=
    Real.log_nonneg
      (by
        have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
        nlinarith only [hlog4])
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num only)
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num only)
  have hc₀ : 0 ≤ c₀ := by
    dsimp only [c₀]
    have h := mul_nonneg (add_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hD) hb
    linarith only [h, hH, hlog3]
  have hl : 0 ≤ l := by
    dsimp only [l]
    linarith only [completedZeroLocalLogBoundConstant_pos]
  have hC : 0 ≤ C :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) (sq_nonneg _)) hl)
        (pow_nonneg (by linarith only [hb]) _))
      (add_nonneg zero_le_one (sq_nonneg _))
  have hA : 0 < A := by
    have hDb := mul_nonneg hD hb
    have hlogb := mul_nonneg hlog8 hb
    dsimp only [A]
    linarith only [hDb, hlogb]
  refine
    ⟨C + 1, A, min η₁ η₂, by linarith only [hC], hA, lt_min hη₁ hη₂, max R₁ R₂,
      hR₁.trans (le_max_left _ _), ?_⟩
  intro R T σ η hR hT hσ hση hη hηbound hS
  have hRone := (le_max_left R₁ R₂).trans hR
  have hRtwo := (le_max_right R₁ R₂).trans hR
  have hRthree : 3 ≤ R := hR₁.trans hRone
  have hη₂bound : η ≤ η₂ := hηbound.trans (min_le_right _ _)
  have hηdet : η ≤ 1 / 1288 := hη₂bound.trans hηsmall
  have hηone : η ≤ 1 := by linarith only [hηdet]
  let S := η * Real.log (R : ℝ)
  have hSnonneg : 0 ≤ S := zero_le_one.trans hS
  obtain ⟨N, cutoff, M, W, hN, hNupper, hcutoff, hpos, _, hM, hwidth, hgain, hlog, hcount⟩ :=
    hdetector R T σ η 1 hRone hT hσ hση hη (hηbound.trans (min_le_left _ _))
  have hlarge := henergy R hRtwo η hη.le hη₂bound N hNupper
  have hglobal :=
    mul_le_mul_of_nonneg_left (log_conductor_height_product_le_three R R hRthree (le_refl R)) hη.le
  have hNlinear : (N : ℝ) ≤ b * S := by
    dsimp only [b, S]
    nlinarith only [hNupper, hglobal, hS, hB]
  have hheight :=
    mul_le_mul_of_nonneg_left (log_conductor_height_product_le_three R T hRthree hT) hη.le
  let L :=
    (Nat.ceil
        (completedZeroLocalLogBoundConstant * (1 + 16 * η * Real.log ((R : ℝ) * ((T : ℝ) + 3)))) :
      ℝ)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hLlinear : L ≤ l * S := by
    have hlognonneg : 0 ≤ Real.log ((R : ℝ) * ((T : ℝ) + 3)) := by
      apply Real.log_nonneg
      have hRreal : (3 : ℝ) ≤ R := by exact_mod_cast hRthree
      nlinarith only [hRreal, (Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
    have hceil :=
      (Nat.ceil_lt_add_one
          (mul_nonneg completedZeroLocalLogBoundConstant_pos.le
            (add_nonneg zero_le_one
              (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 16) hη.le) hlognonneg)))).le
    have hweight :=
      mul_le_mul_of_nonneg_left
        (show 1 + 16 * η * Real.log ((R : ℝ) * ((T : ℝ) + 3)) ≤ 49 * S
          by
          dsimp only [S]
          nlinarith only [hheight, hS])
        completedZeroLocalLogBoundConstant_pos.le
    dsimp only [L, l]
    nlinarith only [hceil, hweight, hS]
  have hsupport : η * Real.log ((cutoff : ℝ) + 1) ≤ (c₀ * S) * N := by
    have hlog' := hlog
    rw [Nat.cast_pow, Real.log_pow] at hlog'
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hlog'
    have hNs := mul_le_mul_of_nonneg_left hNlinear (add_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hD)
    have hHS := mul_le_mul_of_nonneg_left hS hH
    have hlogη := mul_le_mul_of_nonneg_right hηone hlog3
    have hlogS := mul_le_mul_of_nonneg_left hS hlog3
    have hsmall : η * Real.log ((cutoff : ℝ) + 1) ≤ c₀ * S := by
      dsimp only [c₀, D, H, S] at ⊢ hNs hHS hlogη hlogS
      nlinarith only [hlog', hNs, hHS, hlogη, hlogS]
    exact
      hsmall.trans
        (le_mul_of_one_le_right (mul_nonneg hc₀ hSnonneg)
          (by exact_mod_cast ((by norm_num only : 1 ≤ 4).trans hN)))
  have hraw :=
    highPrime_general_scale_count_le_of_meanSquare
      (primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight R σ T) η D (c₀ * S) L N (4 * N) R
      cutoff T M W ((by norm_num only : 2 ≤ 3).trans hRthree) hT hM hη (by linarith only [hηdet])
      (mul_nonneg hc₀ hSnonneg) hL hwidth hS hgain hsupport hlarge hcount
  have henvelope :=
    highPrimeGeneralScaleCountEnvelope_le_exp D (c₀ * S) L b c₀ l S N hD (mul_nonneg hc₀ hSnonneg)
      hL hb hc₀ hl hS hNlinear (le_refl _) hLlinear
  have hcount' :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight R σ T ≤ C * Real.exp (A * S) :=
    hraw.trans henvelope
  exact
    hcount'.trans (mul_le_mul_of_nonneg_right (by linarith only : C ≤ C + 1) (Real.exp_nonneg _))

/-- There are absolute positive density constants and a fixed positive strip width
such that the original diagonal primitive-family count satisfies a log-free power
bound throughout that strip, for every sufficiently large cutoff. Use the shift
equal to the maximum of the strip distance and the reciprocal logarithm, and absorb
the latter into the absolute constant. This includes the boundary line and arbitrarily
narrow strips, with no scaled-logarithm restriction in the theorem statement. -/
theorem exists_primitiveCharacterFamily_near_one_log_free_density :
    ∃ C A η₀ : ℝ,
      0 < C ∧
        0 < A ∧
        0 < η₀ ∧
        ∃ R₀ : ℕ,
          3 ≤ R₀ ∧
            ∀ (R : ℕ) (σ : ℝ),
              R₀ ≤ R →
                1 - η₀ ≤ σ →
                σ ≤ 1 →
                primitiveCharacterFamilyZeroCount R σ ≤ C * Real.rpow (R : ℝ) (A * (1 - σ)) := by
  obtain ⟨C, A, η₀, hC, hA, hη₀, R₁, hR₁, hcount⟩ :=
    exists_primitiveFamily_small_shift_exponential_count_bound
  have hlog : Filter.Tendsto (fun R : ℕ ↦ Real.log (R : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨R₂, hR₂⟩ :=
    Filter.eventually_atTop.mp (hlog.eventually (Filter.eventually_ge_atTop (1 / η₀)))
  refine
    ⟨C * Real.exp A, A, η₀, mul_pos hC (Real.exp_pos _), hA, hη₀, max R₁ R₂,
      hR₁.trans (le_max_left _ _), ?_⟩
  intro R σ hR hσlow hσ
  have hRone := (le_max_left R₁ R₂).trans hR
  have hRthree : 3 ≤ R := hR₁.trans hRone
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hRthree)
  have hlogR : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hRthree))
  have hrecip : 1 / Real.log (R : ℝ) ≤ η₀ := by
    have h := hR₂ R ((le_max_right R₁ R₂).trans hR)
    exact (div_le_iff₀ hlogR).mpr (by nlinarith only [(div_le_iff₀ hη₀).mp h])
  let η := max (1 - σ) (1 / Real.log (R : ℝ))
  have hη : 0 < η := (div_pos zero_lt_one hlogR).trans_le (le_max_right _ _)
  have hηsmall : η ≤ η₀ := max_le (by linarith only [hσlow]) hrecip
  have hscaled : 1 ≤ η * Real.log (R : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (le_max_right (1 - σ) (1 / Real.log (R : ℝ))) hlogR.le
    rwa [one_div_mul_cancel (ne_of_gt hlogR)] at h
  have hηupper : η ≤ (1 - σ) + 1 / Real.log (R : ℝ) := by
    apply max_le
    · linarith only [div_pos zero_lt_one hlogR]
    · linarith only [hσ]
  have hexparg : A * (η * Real.log (R : ℝ)) ≤ A + Real.log (R : ℝ) * (A * (1 - σ)) := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hηupper hlogR.le) hA.le
    rw [add_mul, one_div_mul_cancel (ne_of_gt hlogR)] at h
    nlinarith only [h]
  have hraw := hcount R R σ η hRone (le_refl R) hσ (le_max_left _ _) hη hηsmall hscaled
  have hcount' :
    primitiveCharacterFamilyZeroCount R σ ≤ C * Real.exp (A * (η * Real.log (R : ℝ))) := by
    rw [← primitiveCharacterFamilyZeroCountAtNatHeight_eq,
      primitiveCharacterFamilyZeroCountAtNatHeight_eq_occurrenceCount]
    exact hraw
  calc
    _ ≤ C * Real.exp (A * (η * Real.log (R : ℝ))) := hcount'
    _ ≤ C * Real.exp (A + Real.log (R : ℝ) * (A * (1 - σ))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexparg) hC.le
    _ = _ := by rw [Real.exp_add, Real.rpow_eq_pow, Real.rpow_def_of_pos hRpos, mul_assoc]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
