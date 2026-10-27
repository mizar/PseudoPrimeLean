/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaLocalRationalCertificates

/-! # Checked rational local-cost rows on closed scale cells -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Common rational scale-cell data for local prime certificates.
The endpoints lo,hi contain the real scale; rootLo and rootHi enclose
their square roots. Theta is nonnegative. A successful check supplies
the sign and denominator invariants shared by every prime row. -/
structure GammaLocalCellData where
  lo : ℚ
  hi : ℚ
  rootLo : ℚ
  rootHi : ℚ
  theta : ℚ

/-- Executable sign and squared-root conditions of the common cell.
All operations are rational comparisons. The real interval is supplied
separately when applying a row to an actual scale. -/
def GammaLocalCellData.check (c : GammaLocalCellData) : Bool :=
  decide
    (0 < c.lo ∧
      c.lo ≤ c.hi ∧
      0 < c.rootLo ∧ c.rootLo ^ 2 ≤ c.lo ∧ 0 < c.rootHi ∧ c.hi ≤ c.rootHi ^ 2 ∧ 0 ≤ c.theta)

/-- The common rational cell check implies positive endpoints, certified
real square-root bounds and a nonnegative parameter. Cast its comparisons
and use the square-root order equivalences. These invariants justify all
denominator changes in the local-cost row soundness theorem. -/
theorem GammaLocalCellData.check_sound (c : GammaLocalCellData) (hc : c.check = true) :
    0 < (c.lo : ℝ) ∧
      (c.lo : ℝ) ≤ (c.hi : ℝ) ∧
      0 < (c.rootLo : ℝ) ∧
      (c.rootLo : ℝ) ≤ Real.sqrt (c.lo : ℝ) ∧
      0 < (c.rootHi : ℝ) ∧ Real.sqrt (c.hi : ℝ) ≤ (c.rootHi : ℝ) ∧ 0 ≤ (c.theta : ℝ) := by
  obtain ⟨hl, hlh, hr, hrsq, hR, hRsq, ht⟩ := of_decide_eq_true hc
  have hlR := (Rat.cast_pos (K := ℝ)).mpr hl
  have hrR := (Rat.cast_pos (K := ℝ)).mpr hr
  have hRR := (Rat.cast_pos (K := ℝ)).mpr hR
  have hrsqR := (Rat.cast_le (K := ℝ)).mpr hrsq
  have hRsqR := (Rat.cast_le (K := ℝ)).mpr hRsq
  norm_num only [Rat.cast_pow] at hrsqR hRsqR
  exact
    ⟨hlR, (Rat.cast_le (K := ℝ)).mpr hlh, hrR, (Real.le_sqrt hrR.le hlR.le).mpr hrsqR, hRR,
      (Real.sqrt_le_left hRR.le).mpr hRsqR, (Rat.cast_nonneg (K := ℝ)).mpr ht⟩

/-- One prime's rational upper certificate on a common cell.
The logarithm and node-power data enclose the exact Euler cost. The natural
cutoff and Taylor data bound the signed ramp prefix. Rounded upper endpoints
for the Euler, ramp, total cost and dual excess permit cheap block sums. -/
structure GammaLocalPrimeRow where
  prime : ℕ
  logScale : ℕ
  logTerms : ℕ
  logLower : ℚ
  logUpper : ℚ
  ratios : ℚ → ℚ × ℚ
  powers : ℕ
  expTerms : ℕ
  eulerUpper : ℚ
  rampUpper : ℚ
  costUpper : ℚ
  excessUpper : ℚ

/-- Exact rational checks for one prime's local cost.
Verify the log and signed geometric intervals, next-power tail condition,
all Taylor conditions and the rounded cost and excess endpoints.
Primality and finite prime coverage remain separate arithmetic certificates. -/
def GammaLocalPrimeRow.check (r : GammaLocalPrimeRow) (c : GammaLocalCellData) : Bool :=
  rationalLogIntervalCheck r.prime r.logScale r.logTerms r.logLower r.logUpper &&
    gammaPrimeEulerIntervalCheck r.prime r.ratios &&
    decide
      (gammaPrimeEulerIntervalUpper r.ratios ≤ r.eulerUpper ∧
        (99 / 40 : ℚ) * c.hi ≤ (r.prime : ℚ) ^ (r.powers + 1) ∧
        (∀ k ∈ Finset.range r.powers,
          ((r.prime : ℚ) ^ (k + 1) / c.lo) / (r.expTerms + 1 : ℕ) ≤ 1 / 2) ∧
        gammaSignedRampPrefixUpper r.prime r.powers c.lo c.hi r.expTerms ≤ r.rampUpper ∧
        r.eulerUpper + max r.rampUpper 0 / c.rootLo ≤ r.costUpper ∧
        max (r.costUpper - c.theta / c.rootHi) 0 ≤ r.excessUpper)

/-- Rational weighted dual-excess upper allowance for a prime row.
Multiply the log upper endpoint by the certified nonnegative excess
endpoint. Block certificates sum these allowances without the input factors. -/
def GammaLocalPrimeRow.allowance (r : GammaLocalPrimeRow) : ℚ :=
  r.logUpper * r.excessUpper

/-- A certified prime row bounds the actual signed combined cost at
every real scale inside its common checked cell. Combine the exact signed
Euler upper bound and finite signed ramp prefix, then use the lower root.
This is the uniform analytic meaning of a local row certificate. -/
theorem GammaLocalPrimeRow.cost_le (r : GammaLocalPrimeRow) (c : GammaLocalCellData)
    (hcell : c.check = true) (hp : r.prime.Prime) (hc : r.check c = true) {x : ℝ}
    (hlox : (c.lo : ℝ) ≤ x) (hxhi : x ≤ (c.hi : ℝ)) :
    gammaRamifiedSignedCombinedCost r.prime x ≤ (r.costUpper : ℝ) := by
  obtain ⟨hlo, hlohi, hslo, hrootlo, hshi, hroothi, htheta⟩ := c.check_sound hcell
  obtain ⟨hab, hnum⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hlog, hEuler⟩ := Bool.and_eq_true_iff.mp hab
  obtain ⟨he, hcut, hsize, hr, hcost, hex⟩ := of_decide_eq_true hnum
  have hE := (gamma_prime_euler_interval_check_sound hEuler).2.trans ((Rat.cast_le (K := ℝ)).mpr he)
  norm_num only [Rat.cast_natCast] at hE
  have hcutR := (Rat.cast_le (K := ℝ)).mpr hcut
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_natCast] at hcutR
  have hS := gamma_ramified_series_le_natural_cell_prefix hp.one_lt hlo hlox hxhi hcutR
  have hP :=
    gamma_signed_ramp_prefix_upper_valid r.prime r.powers ((Rat.cast_pos (K := ℝ)).mp hlo)
      ((Rat.cast_pos (K := ℝ)).mp (hlo.trans_le hlohi)) r.expTerms hsize
  have hmax := max_le_max (hP.trans ((Rat.cast_le (K := ℝ)).mpr hr)) (le_refl (0 : ℝ))
  have hden :=
    (div_le_div_of_nonneg_right hmax (Real.sqrt_nonneg (c.lo : ℝ))).trans
      (div_le_div₀ (le_max_right _ _) le_rfl hslo hrootlo)
  have hR := hS.trans hden
  have hcostR := (Rat.cast_le (K := ℝ)).mpr hcost
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_max, Rat.cast_zero] at hcostR
  exact (add_le_add hE hR).trans hcostR

/-- A certified local prime row bounds its actual logarithm-weighted
positive dual excess throughout the checked cell. Bound the subtracted
parameter below by theta/rootHi and retain the positive part.
This supplies the factor-independent finite sum used by witness comparisons. -/
theorem GammaLocalPrimeRow.weighted_excess_le (r : GammaLocalPrimeRow) (c : GammaLocalCellData)
    (hcell : c.check = true) (hp : r.prime.Prime) (hc : r.check c = true) {x : ℝ}
    (hlox : (c.lo : ℝ) ≤ x) (hxhi : x ≤ (c.hi : ℝ)) :
    Real.log r.prime *
        max (gammaRamifiedSignedCombinedCost r.prime x - gammaRamifiedThetaParameter c.theta x) 0 ≤
      (r.allowance : ℝ) := by
  obtain ⟨hlo, hlohi, hslo, hrootlo, hshi, hroothi, htheta⟩ := c.check_sound hcell
  obtain ⟨hab, hnum⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hlog, hEuler⟩ := Bool.and_eq_true_iff.mp hab
  obtain ⟨he, hcut, hsize, hr, hcost, hex⟩ := of_decide_eq_true hnum
  have hcostReal := r.cost_le c hcell hp hc hlox hxhi
  have hmu : (c.theta : ℝ) / c.rootHi ≤ gammaRamifiedThetaParameter c.theta x :=
    div_le_div₀ htheta le_rfl (Real.sqrt_pos.mpr (hlo.trans_le hlox))
      ((Real.sqrt_le_sqrt hxhi).trans hroothi)
  have hd :
    gammaRamifiedSignedCombinedCost r.prime x - gammaRamifiedThetaParameter c.theta x ≤
      (r.costUpper : ℝ) - c.theta / c.rootHi := by
    linarith only [hcostReal, hmu]
  have hEx := (Rat.cast_le (K := ℝ)).mpr hex
  norm_num only [Rat.cast_max, Rat.cast_sub, Rat.cast_div, Rat.cast_zero] at hEx
  have hbound := (max_le_max hd (le_refl (0 : ℝ))).trans hEx
  have hLog := (rationalLogIntervalCheck_sound hlog).2
  norm_num only [Rat.cast_natCast] at hLog
  have hLog0 := Real.log_nonneg (by exact_mod_cast hp.one_le : (1 : ℝ) ≤ r.prime)
  rw [GammaLocalPrimeRow.allowance, Rat.cast_mul]
  exact mul_le_mul hLog hbound (le_max_right _ _) (hLog0.trans hLog)

/-- A list of distinct certified prime rows covering every prime in a
natural interval gives an upper bound for that interval's actual excess sum.
Sum the uniform row bounds and use the checked exact finite prime coverage.
This permits a short natural-interval partition of the fixed support. -/
theorem gamma_local_prime_block_upper (rows : List GammaLocalPrimeRow) (c : GammaLocalCellData)
    (hcell : c.check = true) (lo hi : ℕ) (hp : rows.Forall (fun r ↦ r.prime.Prime))
    (hc : rows.Forall (fun r ↦ r.check c = true)) (hn : (rows.map GammaLocalPrimeRow.prime).Nodup)
    (hcover : (rows.map GammaLocalPrimeRow.prime).toFinset = (Finset.Ioc lo hi).filter Nat.Prime)
    {x : ℝ} (hlox : (c.lo : ℝ) ≤ x) (hxhi : x ≤ (c.hi : ℝ)) :
    (∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime,
        Real.log p *
          max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter c.theta x) 0) ≤
      (((rows.map GammaLocalPrimeRow.allowance).sum : ℚ) : ℝ) := by
  let F : ℕ → ℝ := fun p ↦
    Real.log p * max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter c.theta x) 0
  have he :
    (∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, F p) = (rows.map (fun r ↦ F r.prime)).sum := by
    rw [← hcover, List.sum_toFinset F hn, List.map_map]
    rfl
  have hb :=
    List.sum_le_sum
      (fun (r : GammaLocalPrimeRow) hr ↦
        r.weighted_excess_le c hcell (List.forall_iff_forall_mem.mp hp r hr)
          (List.forall_iff_forall_mem.mp hc r hr) hlox hxhi)
  change (∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, F p) ≤ _
  rw [he]
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def]
  exact hb

/-- Upper bounds for prime-filtered sums on adjacent natural intervals
add at fixed summand F. Rewrite the filtered sums as conditional full sums
and split the disjoint interval union. This composes certified support blocks. -/
theorem gamma_prime_interval_upper_add (F : ℕ → ℝ) {lo mid hi : ℕ} {a b : ℚ} (hl : lo ≤ mid)
    (hh : mid ≤ hi) (ha : (∑ p ∈ (Finset.Ioc lo mid).filter Nat.Prime, F p) ≤ (a : ℝ))
    (hb : (∑ p ∈ (Finset.Ioc mid hi).filter Nat.Prime, F p) ≤ (b : ℝ)) :
    (∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, F p) ≤ ((a + b : ℚ) : ℝ) := by
  rw [Finset.sum_filter] at ha hb ⊢
  have hdis : Disjoint (Finset.Ioc lo mid) (Finset.Ioc mid hi) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge (Finset.mem_Ioc.mp hp).2) (Finset.mem_Ioc.mp hq).1
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hl hh, Finset.sum_union hdis, Rat.cast_add]
  exact add_le_add ha hb

/-- At a natural real cutoff C, the certificate prime set is the prime
filter of (2,C]. Compare membership and the successor inequality.
This identifies the natural block union with the fixed support used by theta budgets. -/
theorem gamma_certificate_prime_set_nat_eq (C : ℕ) :
    gammaRamifiedCertificatePrimeSet (C : ℝ) = (Finset.Ioc 2 C).filter Nat.Prime := by
  ext p
  simp only [gammaRamifiedCertificatePrimeSet, Nat.floor_natCast, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ioc]
  change ((Nat.succ 2 ≤ p ∧ p ≤ C) ∧ Nat.Prime p) ↔ ((2 < p ∧ p ≤ C) ∧ Nat.Prime p)
  rw [Nat.succ_le_iff]

end PseudoPrime.Analysis
