/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalFiberProductBounds
public import PseudoPrime.NumberTheory.Heilbronn.HeightRatioPowerBounds
public import PseudoPrime.NumberTheory.Heilbronn.FiberBandCoefficients

/-! # Uniform growth in balanced residue-height bands -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Restricted height-T ratios satisfy a powered polynomial estimate with
the long-height residue factor p²+4T^(2m). Raise the finite-fiber growth
inequality to r and replace the quotient coefficient by its explicit divisor
bound. The fixed m,n,r are independent of the prime and both heights. -/
theorem heightRestrictedRatioSet_fiber_power_le_polynomial {p H T m n r : ℕ} [Fact p.Prime]
    (hHp : H < p) (hT : 0 < T) (hm : 0 < m) (hn : 0 < n) (hr : 0 < r) :
    ((heightRestrictedRatioSet p H T).card ^ m * p) ^ (n * r) ≤
      quotientPowerBoundConstant r ^ (n ^ 2 * (m - 1)) * T ^ heightRatioLossExponent m n r *
        (p ^ 2 + 4 * T ^ (2 * m)) ^ (n * r) := by
  have hres := heightRestrictedRatioSet_has_residues (T := T) hHp
  have hg :=
    Nat.pow_le_pow_left
      (rationalProductSet_power_growth_finite_fibers hT hm hn
        (fun q hq ↦ boundedRationalResidue_canonical_height (Exists.choose_spec (hres q hq))) hres)
      r
  have hq :=
    Nat.pow_le_pow_left
      (quotientPowerConstant_pow_le_explicit (U := T ^ (2 * m)) (Nat.pow_pos hT) hr)
      (n ^ 2 * (m - 1))
  have hg' :
    ((heightRestrictedRatioSet p H T).card ^ m * p) ^ (n * r) ≤
      (quotientPowerConstant (T ^ (2 * m)) ^ r) ^ (n ^ 2 * (m - 1)) * T ^ (((m - 1) * m) * r) *
        (p ^ 2 + 4 * T ^ (2 * m)) ^ (n * r) := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hg
  have hmul :=
    Nat.mul_le_mul_right ((p ^ 2 + 4 * T ^ (2 * m)) ^ (n * r))
      (Nat.mul_le_mul_right (T ^ (((m - 1) * m) * r)) hq)
  apply hg'.trans
  convert hmul using 1
  simp only [quotientPowerBoundConstant, heightRatioLossExponent, divisorPowerBoundConstant,
    mul_pow, pow_add, ← pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  ring

/-- Two balanced monomial bounds on T^m imply that the finite-fiber
numerator p²+4T^(2m) is at most 5pT^m p^(m beta). This algebraic estimate
allows heights on either side of p^(1/m), without injectivity. -/
theorem residue_product_band_bound {p T m : ℕ} {beta : ℝ}
    (hlo : (p : ℝ) ≤ (T : ℝ) ^ m * (p : ℝ) ^ (m * beta))
    (hhi : (T : ℝ) ^ m ≤ (p : ℝ) * (p : ℝ) ^ (m * beta)) :
    ((p ^ 2 + 4 * T ^ (2 * m) : ℕ) : ℝ) ≤ 5 * (p : ℝ) * (T : ℝ) ^ m * (p : ℝ) ^ (m * beta) := by
  have hl := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg p)
  have hh := mul_le_mul_of_nonneg_left hhi (pow_nonneg (Nat.cast_nonneg T) m)
  have he : (T : ℝ) ^ (2 * m) = ((T : ℝ) ^ m) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, he]
  nlinarith only [hl, hh]

/-- The prescribed natural coefficient controls all balanced height bands
for positive degree m and precision c. Use the explicit orders n,r, retain
their factorial coefficient, and extract roots as in the uniform band
estimate. This supplies a numerical coefficient rather than only existence. -/
theorem heightRestrictedRatioSet_le_explicit_fiber_band_bound {m c : ℕ} (hm : 0 < m) (hc : 0 < c) :
    ∀ (p H T : ℕ) [Fact p.Prime],
      H < p →
        0 < T →
        ∀ beta : ℝ,
          (p : ℝ) ≤ (T : ℝ) ^ m * (p : ℝ) ^ (m * beta) →
            (T : ℝ) ^ m ≤ (p : ℝ) * (p : ℝ) ^ (m * beta) →
            ((heightRestrictedRatioSet p H T).card : ℝ) ≤
              fiberBandCoefficient m c * (T : ℝ) ^ (1 + 1 / (c : ℝ)) * (p : ℝ) ^ beta := by
  let n := fiberBandGrowthOrder m c
  let r := fiberBandMomentOrder m c
  have hn : 0 < n := fiberBandGrowthOrder_pos m c
  have hr : 0 < r := fiberBandMomentOrder_pos m c
  have hl : c * heightRatioLossExponent m n r < n * m * r := fiberBand_parameters_small_loss hm c
  let D := quotientPowerBoundConstant r ^ (n ^ 2 * (m - 1))
  let C : ℕ := 5 * (D + 1) + 1
  intro p H T hp hHp hT beta hlo hhi
  change
    ((heightRestrictedRatioSet p H T).card : ℝ) ≤
      (C : ℝ) * (T : ℝ) ^ (1 + 1 / (c : ℝ)) * (p : ℝ) ^ beta
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hT1 : (1 : ℝ) ≤ T := Nat.one_le_cast.mpr hT
  have hnr := Nat.mul_pos hn hr
  have hnrR : (0 : ℝ) < (n * r : ℕ) := Nat.cast_pos.mpr hnr
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  have hpoly := heightRestrictedRatioSet_fiber_power_le_polynomial hHp hT hm hn hr
  have hb := natural_count_le_polynomial_root hnr hpoly
  have he : ((n * r : ℕ) : ℝ) / (n * r : ℕ) = 1 := div_self (ne_of_gt hnrR)
  rw [he, Real.rpow_one] at hb
  have hL : (heightRatioLossExponent m n r : ℝ) / (n * r : ℕ) ≤ (m : ℝ) / c := by
    apply (div_le_div_iff₀ hnrR hcR).mpr
    have h := Nat.cast_le (α := ℝ).mpr hl.le
    simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h
  have ht := Real.rpow_le_rpow_of_exponent_le hT1 hL
  have hband := residue_product_band_bound hlo hhi
  have hb' :
    ((heightRestrictedRatioSet p H T).card : ℝ) ^ m * p ≤
      (D + 1 : ℕ) * (T : ℝ) ^ ((m : ℝ) / c) *
        (5 * (p : ℝ) * (T : ℝ) ^ m * (p : ℝ) ^ (m * beta)) := by
    have hh :=
      mul_le_mul (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (D + 1))) hband
        (Nat.cast_nonneg (p ^ 2 + 4 * T ^ (2 * m)))
        (mul_nonneg (Nat.cast_nonneg (D + 1)) (Real.rpow_nonneg (Nat.cast_nonneg T) _))
    have hb0 :
      ((heightRestrictedRatioSet p H T).card : ℝ) ^ m * p ≤
        (D + 1 : ℕ) * (T : ℝ) ^ ((heightRatioLossExponent m n r : ℝ) / (n * r : ℕ)) *
          ((p ^ 2 + 4 * T ^ (2 * m) : ℕ) : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_pow, D] using hb
    exact hb0.trans hh
  have hCpow : (5 * (D + 1 : ℕ) : ℝ) ≤ (C : ℝ) ^ m := by
    have hpow := Nat.pow_le_pow_right (Nat.succ_pos (5 * (D + 1))) hm
    have hnat : 5 * (D + 1) ≤ C ^ m := (Nat.le_succ _).trans (by simpa only [pow_one] using hpow)
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hnat
  have heT : ((T : ℝ) ^ (1 + 1 / (c : ℝ))) ^ m = (T : ℝ) ^ ((m : ℝ) / c) * (T : ℝ) ^ m := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg T), ← Real.rpow_natCast, ←
      Real.rpow_add (Nat.cast_pos.mpr hT)]
    congr 1
    ring
  have hep : ((p : ℝ) ^ beta) ^ m = (p : ℝ) ^ ((m : ℝ) * beta) := by
    rw [← Real.rpow_mul_natCast hpR.le]
    congr 1
    ring
  apply
    (pow_le_pow_iff_left₀ (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg C) (Real.rpow_nonneg (Nat.cast_nonneg T) _))
          (Real.rpow_nonneg hpR.le _))
        (ne_of_gt hm)).mp
  rw [mul_pow, mul_pow, heT, hep]
  have hcoeff :=
    mul_le_mul_of_nonneg_right hCpow
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg T) ((m : ℝ) / c))
          (pow_nonneg (Nat.cast_nonneg T) m))
        (Real.rpow_nonneg hpR.le ((m : ℝ) * beta)))
  apply (mul_le_mul_iff_left₀ hpR).mp
  calc
    _ ≤ _ := hb'
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hcoeff hpR.le
      simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hh

/-- For fixed degree m and precision c, one positive constant controls every
restricted ratio family in a balanced band about p^(1/m). The constant is
chosen before p,H,T and beta. Extract the polynomial root, absorb the small
height loss, and retain p^beta. This supplies the eight-degree covering step. -/
theorem exists_uniform_height_ratio_fiber_band_bound {m c : ℕ} (hm : 0 < m) (hc : 0 < c) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (p H T : ℕ) [Fact p.Prime],
          H < p →
            0 < T →
            ∀ beta : ℝ,
              (p : ℝ) ≤ (T : ℝ) ^ m * (p : ℝ) ^ (m * beta) →
                (T : ℝ) ^ m ≤ (p : ℝ) * (p : ℝ) ^ (m * beta) →
                ((heightRestrictedRatioSet p H T).card : ℝ) ≤
                  C * (T : ℝ) ^ (1 + 1 / (c : ℝ)) * (p : ℝ) ^ beta := by
  exact
    ⟨fiberBandCoefficient m c, Nat.cast_pos.mpr (fiberBandCoefficient_pos m c),
      heightRestrictedRatioSet_le_explicit_fiber_band_bound hm hc⟩

end PseudoPrime.NumberTheory.Heilbronn
