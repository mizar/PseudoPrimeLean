/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroFreeAllHeights
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroContribution
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.InversePowerZeroMass

/-!
# Unconditional logarithmic zeta-zero sum bounds

The all-height zero-free region suppresses the low zeros. Summable xi inverse-power
masses control both the finite ledgers and the full nontrivial zero series, with a
quantitative inverse-square-root tail above any positive height cutoff.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For positive x and any complex point, the norm of the logarithmic zeta zero
contribution equals x to its real part times multiplicity divided by norm squared.
Expand the complex power norm. This identity does not assume a critical-line location. -/
theorem norm_logZeroContribution {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    ‖riemannZetaLogZeroContribution x ρ‖ =
      x ^ ρ.re * (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ := by
  rw [riemannZetaLogZeroContribution, norm_div, norm_mul, norm_neg, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, norm_pow, ← Complex.normSq_eq_norm_sq]
  ring

/-- A positive all-height squared-log zero gap bounds the real part of every zero
below an absolute height cutoff by the boundary evaluated at that cutoff.
Compare the positive logarithmic denominators. This gives one exponent for finite ledgers. -/
theorem zero_re_le_at_height_cutoff {c T : ℝ} (hc : 0 < c)
    (hg : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 2) ^ 2) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (ht : |ρ.im| ≤ T) : ρ.re ≤ 1 - c / Real.log (T + 2) ^ 2 := by
  have hla : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith only [abs_nonneg ρ.im])
  have hle : Real.log (|ρ.im| + 2) ≤ Real.log (T + 2) :=
    Real.log_le_log (by linarith only [abs_nonneg ρ.im]) (by linarith only [ht])
  have hs : Real.log (|ρ.im| + 2) ^ 2 ≤ Real.log (T + 2) ^ 2 := by
    nlinarith only [hla, hle, sq_nonneg (Real.log (T + 2) - Real.log (|ρ.im| + 2))]
  have hd := div_le_div_of_nonneg_left hc.le (sq_pos_of_pos hla) hs
  linarith only [hg ρ hρ, hd]

/-- Given a positive all-height zero gap and x at least one, a logarithmic zero term
below the height cutoff is bounded by the cutoff exponent times its inverse-square
multiplicity weight. Apply monotonicity of real powers in their exponent. -/
theorem norm_logZeroContribution_le {c T x : ℝ} (hc : 0 < c)
    (hg : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 2) ^ 2) (hx : 1 ≤ x)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (ht : |ρ.im| ≤ T) :
    ‖riemannZetaLogZeroContribution x ρ‖ ≤
      x ^ (1 - c / Real.log (T + 2) ^ 2) * (riemannZetaZeroMultiplicity ρ : ℝ) /
        Complex.normSq ρ := by
  rw [norm_logZeroContribution (zero_lt_one.trans_le hx)]
  exact
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hx (zero_re_le_at_height_cutoff hc hg hρ ht))
        (Nat.cast_nonneg _))
      (Complex.normSq_nonneg _)

/-- For x at least one and any finite set of actual zeta zeros below a common height,
a positive all-height zero gap bounds the logarithmic contribution sum by one power of x
times the finite inverse-square mass. Apply the triangle inequality termwise. -/
theorem norm_sum_logZeroContribution_le {c T x : ℝ} (hc : 0 < c)
    (hg : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 2) ^ 2) (hx : 1 ≤ x)
    (S : Finset ℂ) (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (ht : ∀ ρ ∈ S, |ρ.im| ≤ T) :
    ‖∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ‖ ≤
      x ^ (1 - c / Real.log (T + 2) ^ 2) *
        ∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ := by
  calc
    _ ≤ ∑ ρ ∈ S, ‖riemannZetaLogZeroContribution x ρ‖ := norm_sum_le _ _
    _ ≤
        ∑ ρ ∈ S,
          x ^ (1 - c / Real.log (T + 2) ^ 2) * (riemannZetaZeroMultiplicity ρ : ℝ) /
            Complex.normSq ρ :=
      Finset.sum_le_sum fun ρ hρ ↦ norm_logZeroContribution_le hc hg hx (hz ρ hρ) (ht ρ hρ)
    _ = _ := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ρ _ ↦ mul_div_assoc _ _ _

/-- There is an unconditional positive squared-log width controlling every finite
logarithmic zeta-zero sum below any height cutoff for x at least one.
Instantiate the finite comparison with the proved all-height zero gap. -/
theorem exists_sum_logZeroContribution_bound :
    ∃ c : ℝ,
      0 < c ∧
        ∀ (x T : ℝ),
          1 ≤ x →
            ∀ S : Finset ℂ,
              (∀ ρ ∈ S, riemannZeta ρ = 0) →
                (∀ ρ ∈ S, |ρ.im| ≤ T) →
                ‖∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ‖ ≤
                  x ^ (1 - c / Real.log (T + 2) ^ 2) *
                    ∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ := by
  obtain ⟨c, hc, hg⟩ := exists_zero_gap_all_heights
  exact ⟨c, hc, fun x T hx S hz ht ↦ norm_sum_logZeroContribution_le hc hg hx S hz ht⟩

/-- The inverse-square multiplicity mass of any finite nontrivial zeta-zero family
is bounded by the full unconditional xi inverse-square mass. Transfer each actual zero
and its multiplicity to xi. This supplies the low-zero mass independently of RH. -/
theorem sum_nontrivial_inverse_square_le (S : Finset ℂ) (hz : ∀ ρ ∈ S, riemannZeta ρ = 0)
    (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) ≤
      ∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight 2 ρ := by
  have hxi : ∀ ρ ∈ S, RiemannXi.riemannXi ρ = 0 := fun ρ hρ ↦
    RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
  exact
    RiemannXi.sum_inverse_square_le_mass S
      (fun ρ hρ ↦ (RiemannXi.zeroMultiplicity_eq_zetaMultiplicity_of_zero (hxi ρ hρ)).symm) hxi

/-- For an actual zeta zero of nonnegative real part, its inverse-square multiplicity
weight equals the xi indicator weight. Transfer the zero and analytic multiplicity.
This identifies the summands in unconditional mass and tail estimates. -/
theorem nontrivial_inverse_square_eq_weight {ρ : ℂ} (hz : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re) :
    (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ =
      RiemannXi.inversePowerZeroWeight 2 ρ := by
  have hxi := RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz hre
  rw [RiemannXi.inversePowerZeroWeight, ite_eq_left hxi,
    RiemannXi.zeroMultiplicity_eq_zetaMultiplicity_of_zero hxi, Real.rpow_two,
    Complex.normSq_eq_norm_sq]

/-- For x at least one and positive cutoff T, the logarithmic contributions of any
finite nontrivial zeta-zero family above height T have norm at most x divided by sqrt(T)
times the full xi three-halves power mass. Use the real-part bound one and the norm tail. -/
theorem norm_sum_high_logZero_le {x T : ℝ} (hx : 1 ≤ x) (hT : 0 < T) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (ht : ∀ ρ ∈ S, T ≤ |ρ.im|) :
    ‖∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ‖ ≤
      x * T ^ (-(1 : ℝ) / 2) * ∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight (3 / 2) ρ := by
  have hb :
    ∀ ρ ∈ S, ‖riemannZetaLogZeroContribution x ρ‖ ≤ x * RiemannXi.inversePowerZeroWeight 2 ρ := by
    intro ρ hρ
    rw [norm_logZeroContribution (zero_lt_one.trans_le hx), ←
      nontrivial_inverse_square_eq_weight (hz ρ hρ) (hre ρ hρ)]
    have he := Real.rpow_le_rpow_of_exponent_le hx (re_zero_le_one (hz ρ hρ))
    rw [Real.rpow_one] at he
    rw [← mul_div_assoc]
    exact
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))
        (Complex.normSq_nonneg _)
  have ht' : ∀ ρ ∈ S, T ≤ ‖ρ‖ := fun ρ hρ ↦ (ht ρ hρ).trans (Complex.abs_im_le_norm ρ)
  have hmass :=
    RiemannXi.sum_inverse_square_tail_le (by norm_num only : (1 : ℝ) < 3 / 2)
      (by norm_num only : (3 / 2 : ℝ) ≤ 2) hT S ht'
  norm_num only at hmass
  calc
    _ ≤ ∑ ρ ∈ S, ‖riemannZetaLogZeroContribution x ρ‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ S, x * RiemannXi.inversePowerZeroWeight 2 ρ := Finset.sum_le_sum hb
    _ = x * ∑ ρ ∈ S, RiemannXi.inversePowerZeroWeight 2 ρ := (Finset.mul_sum _ _ _).symm
    _ ≤ x * (T ^ (-(1 : ℝ) / 2) * ∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight (3 / 2) ρ) := by
      simpa only [neg_div] using mul_le_mul_of_nonneg_left hmass (zero_le_one.trans hx)
    _ = _ := by ring

/-- Given an all-height zero gap, split any finite nontrivial zeta-zero ledger at a
positive height T. Low zeros cost x to the cutoff exponent times inverse-square mass;
high zeros cost x divided by sqrt(T) times three-halves mass. All constants are
unconditional and independent of the finite ledger. -/
theorem norm_sum_logZero_split_le {c x T : ℝ} (hc : 0 < c)
    (hg : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 2) ^ 2) (hx : 1 ≤ x)
    (hT : 0 < T) (S : Finset ℂ) (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    ‖∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ‖ ≤
      x ^ (1 - c / Real.log (T + 2) ^ 2) * (∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight 2 ρ) +
        x * T ^ (-(1 : ℝ) / 2) * ∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight (3 / 2) ρ := by
  classical
  let A := S.filter (fun ρ : ℂ ↦ |ρ.im| ≤ T)
  let B := S.filter (fun ρ : ℂ ↦ ¬|ρ.im| ≤ T)
  have hAs : ∀ ρ ∈ A, ρ ∈ S := fun ρ hρ ↦ (Finset.mem_filter.mp hρ).1
  have hBs : ∀ ρ ∈ B, ρ ∈ S := fun ρ hρ ↦ (Finset.mem_filter.mp hρ).1
  have hlo :=
    norm_sum_logZeroContribution_le hc hg hx A (fun ρ hρ ↦ hz ρ (hAs ρ hρ))
      (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2)
  have hmass :=
    sum_nontrivial_inverse_square_le A (fun ρ hρ ↦ hz ρ (hAs ρ hρ)) (fun ρ hρ ↦ hre ρ (hAs ρ hρ))
  have hhi :=
    norm_sum_high_logZero_le hx hT B (fun ρ hρ ↦ hz ρ (hBs ρ hρ)) (fun ρ hρ ↦ hre ρ (hBs ρ hρ))
      (fun ρ hρ ↦ (lt_of_not_ge (Finset.mem_filter.mp hρ).2).le)
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ ↦ |ρ.im| ≤ T)
      (riemannZetaLogZeroContribution x)
  rw [← hsplit]
  exact
    (norm_add_le _ _).trans
      (add_le_add
        (hlo.trans (mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg (zero_le_one.trans hx) _)))
        hhi)

/-- There are unconditional positive zero-gap width and nonnegative mass constants
giving the low-height plus high-tail bound for every finite nontrivial zeta-zero ledger,
every x at least one and every positive cutoff. Instantiate the proved gap and masses. -/
theorem exists_sum_logZero_split_bound :
    ∃ (c C M : ℝ),
      0 < c ∧
        0 ≤ C ∧
        0 ≤ M ∧
        ∀ (x T : ℝ),
          1 ≤ x →
            0 < T →
            ∀ S : Finset ℂ,
              (∀ ρ ∈ S, riemannZeta ρ = 0) →
                (∀ ρ ∈ S, 0 ≤ ρ.re) →
                ‖∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ‖ ≤
                  C * x ^ (1 - c / Real.log (T + 2) ^ 2) + M * x * T ^ (-(1 : ℝ) / 2) := by
  obtain ⟨c, hc, hg⟩ := exists_zero_gap_all_heights
  refine
    ⟨c, (∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight 2 ρ),
      (∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight (3 / 2) ρ), hc,
      tsum_nonneg (RiemannXi.inversePowerZeroWeight_nonneg 2),
      tsum_nonneg (RiemannXi.inversePowerZeroWeight_nonneg (3 / 2)), ?_⟩
  intro x T hx hT S hz hre
  have h := norm_sum_logZero_split_le hc hg hx hT S hz hre
  convert h using 1
  ring

/-- For a cutoff x and complex point, retain its logarithmic zeta zero contribution
exactly when it is an actual zero of nonnegative real part, and return zero otherwise.
This removes trivial zeros and gives an absolutely summable family for x at least one,
used when exhausting finite explicit-formula ledgers. -/
noncomputable def nontrivialLogZeroTerm (x : ℝ) (ρ : ℂ) : ℂ :=
  if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re then riemannZetaLogZeroContribution x ρ else 0

/-- For x at least one, every nontrivial logarithmic zero term is bounded by x times
the unconditional xi inverse-square weight. Use the real-part bound one at actual zeros
and zero elsewhere. This is a summable majorant for finite-ledger exhaustion. -/
theorem norm_nontrivialLogZeroTerm_le {x : ℝ} (hx : 1 ≤ x) (ρ : ℂ) :
    ‖nontrivialLogZeroTerm x ρ‖ ≤ x * RiemannXi.inversePowerZeroWeight 2 ρ := by
  rw [nontrivialLogZeroTerm]
  split
  next
    h =>
    rw [norm_logZeroContribution (zero_lt_one.trans_le hx), ←
      nontrivial_inverse_square_eq_weight h.1 h.2, ← mul_div_assoc]
    have he := Real.rpow_le_rpow_of_exponent_le hx (re_zero_le_one h.1)
    rw [Real.rpow_one] at he
    exact
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))
        (Complex.normSq_nonneg _)
  next h =>
    rw [norm_zero]
    exact mul_nonneg (zero_le_one.trans hx) (RiemannXi.inversePowerZeroWeight_nonneg 2 ρ)

/-- For x at least one, the nontrivial logarithmic zeta-zero contributions form an
absolutely summable complex family. Dominate their norms by x times the unconditional
xi inverse-square mass. No RH or zero enumeration is required. -/
theorem summable_nontrivialLogZeroTerm {x : ℝ} (hx : 1 ≤ x) : Summable (nontrivialLogZeroTerm x) :=
  Summable.of_norm_bounded
    ((RiemannXi.summable_inversePowerZeroWeight (by norm_num only : (1 : ℝ) < 2)).mul_left x)
    (norm_nontrivialLogZeroTerm_le hx)

/-- Given an all-height zero gap, x at least one and positive cutoff T, each
nontrivial logarithmic zero term is bounded by the sum of the low-zero majorant and
the high-tail majorant. Split at the absolute height cutoff and retain nonnegative
unused terms. This permits a direct absolutely convergent infinite-sum estimate. -/
theorem norm_nontrivialLogZeroTerm_split {c x T : ℝ} (hc : 0 < c)
    (hg : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 2) ^ 2) (hx : 1 ≤ x)
    (hT : 0 < T) (ρ : ℂ) :
    ‖nontrivialLogZeroTerm x ρ‖ ≤
      x ^ (1 - c / Real.log (T + 2) ^ 2) * RiemannXi.inversePowerZeroWeight 2 ρ +
        (x * T ^ (-(1 : ℝ) / 2)) * RiemannXi.inversePowerZeroWeight (3 / 2) ρ := by
  have hA : 0 ≤ x ^ (1 - c / Real.log (T + 2) ^ 2) * RiemannXi.inversePowerZeroWeight 2 ρ :=
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)
      (RiemannXi.inversePowerZeroWeight_nonneg 2 ρ)
  have hB : 0 ≤ (x * T ^ (-(1 : ℝ) / 2)) * RiemannXi.inversePowerZeroWeight (3 / 2) ρ :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hx) (Real.rpow_nonneg hT.le _))
      (RiemannXi.inversePowerZeroWeight_nonneg (3 / 2) ρ)
  by_cases ht : |ρ.im| ≤ T
  · rw [nontrivialLogZeroTerm]
    split
    next h =>
      have hlo := norm_logZeroContribution_le hc hg hx h.1 ht
      rw [mul_div_assoc, nontrivial_inverse_square_eq_weight h.1 h.2] at hlo
      exact hlo.trans (le_add_of_nonneg_right hB)
    next h =>
      rw [norm_zero]; exact add_nonneg hA hB
  · have hb := norm_nontrivialLogZeroTerm_le hx ρ
    have hnorm : T ≤ ‖ρ‖ := (lt_of_not_ge ht).le.trans (Complex.abs_im_le_norm ρ)
    have htail :=
      RiemannXi.inverse_square_le_power_tail (by norm_num only : (3 / 2 : ℝ) ≤ 2) hT hnorm
    norm_num only at htail
    have hmul := mul_le_mul_of_nonneg_left htail (zero_le_one.trans hx)
    have hhi :
      ‖nontrivialLogZeroTerm x ρ‖ ≤
        (x * T ^ (-(1 : ℝ) / 2)) * RiemannXi.inversePowerZeroWeight (3 / 2) ρ := by
      have hh := hb.trans hmul
      simpa only [neg_div, mul_assoc] using hh
    exact hhi.trans (le_add_of_nonneg_left hA)

/-- Given the all-height zero gap, x at least one and positive cutoff, the full
nontrivial logarithmic zero sum satisfies the same low-zero plus high-tail bound as
finite ledgers. Sum the pointwise majorant using absolute convergence of both masses.
This is the zero contribution to an unconditional logarithmic explicit formula. -/
theorem norm_tsum_nontrivialLogZero_split {c x T : ℝ} (hc : 0 < c)
    (hg : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 2) ^ 2) (hx : 1 ≤ x)
    (hT : 0 < T) :
    ‖∑' ρ : ℂ, nontrivialLogZeroTerm x ρ‖ ≤
      x ^ (1 - c / Real.log (T + 2) ^ 2) * (∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight 2 ρ) +
        (x * T ^ (-(1 : ℝ) / 2)) * ∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight (3 / 2) ρ := by
  have h2 :=
    (RiemannXi.summable_inversePowerZeroWeight (by norm_num only : (1 : ℝ) < 2)).mul_left
      (x ^ (1 - c / Real.log (T + 2) ^ 2))
  have h3 :=
    (RiemannXi.summable_inversePowerZeroWeight (by norm_num only : (1 : ℝ) < 3 / 2)).mul_left
      (x * T ^ (-(1 : ℝ) / 2))
  have hs := (summable_nontrivialLogZeroTerm hx).norm
  have hb := hs.tsum_le_tsum (norm_nontrivialLogZeroTerm_split hc hg hx hT) (h2.add h3)
  rw [h2.tsum_add h3,
    (RiemannXi.summable_inversePowerZeroWeight (by norm_num only : (1 : ℝ) < 2)).tsum_mul_left,
    (RiemannXi.summable_inversePowerZeroWeight
        (by norm_num only : (1 : ℝ) < 3 / 2)).tsum_mul_left] at hb
  exact (norm_tsum_le_tsum_norm hs).trans hb

/-- There are unconditional positive zero-gap width and nonnegative mass constants
bounding the full nontrivial logarithmic zeta-zero sum by a cutoff power of x plus
x divided by sqrt(T), for all x at least one and positive T. Use the proved all-height
region and summable actual-zero masses, without RH or an assumed PNT error. -/
theorem exists_tsum_nontrivialLogZero_bound :
    ∃ (c C M : ℝ),
      0 < c ∧
        0 ≤ C ∧
        0 ≤ M ∧
        ∀ (x T : ℝ),
          1 ≤ x →
            0 < T →
            ‖∑' ρ : ℂ, nontrivialLogZeroTerm x ρ‖ ≤
              C * x ^ (1 - c / Real.log (T + 2) ^ 2) + M * x * T ^ (-(1 : ℝ) / 2) := by
  obtain ⟨c, hc, hg⟩ := exists_zero_gap_all_heights
  refine
    ⟨c, (∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight 2 ρ),
      (∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight (3 / 2) ρ), hc,
      tsum_nonneg (RiemannXi.inversePowerZeroWeight_nonneg 2),
      tsum_nonneg (RiemannXi.inversePowerZeroWeight_nonneg (3 / 2)), ?_⟩
  intro x T hx hT
  have h := norm_tsum_nontrivialLogZero_split hc hg hx hT
  convert h using 1
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
