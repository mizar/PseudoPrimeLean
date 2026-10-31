/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLowFloor

/-! # Residual certificates for low-floor Gaussian profiles -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed inverse-radius coefficient retains the residual allowance D. -/
noncomputable def gaussianLowResidualV (eta D : ℝ) : ℝ :=
  eta * (1839 * gaussian6FifthsEndpoint / 1000) +
    gaussian6FifthsEndpoint * (4 - 7 * D / (6 * gaussianMRRefinedConductor))

/-- A positive floor, the quadratic budget, two signed inverse-pair checks
and a tail certificate imply the strict normalized large-index residual bound.
The actual prefix error is retained, so this feeds the relative comparison. -/
theorem gaussianLow_error_cap {L eta eps D s u P T : ℝ} {q : ℕ} (hu : 0 < u) (hs0 : u ≤ s)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + D ≤ gaussianMRRefinedD * s ^ 2)
    (hq : Real.log q ≤ L) (h1 : 0 ≤ gaussian1000ResidualA eta * u + gaussianLowResidualV eta D)
    (h2 : 0 ≤ gaussian1000ResidualA eta * u + 2 * gaussianLowResidualV eta D)
    (htail : (473 / 10 : ℝ) * ((s ^ 2) ^ 2) ^ (-9 / 16 : ℝ) + (512 / 27 : ℝ) / (s ^ 2) ^ 2 ≤ T)
    (hstrict :
      (12871 / 1000 : ℝ) - 2 * P +
          7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
          gaussian1000ResidualA eta / u +
          gaussianLowResidualV eta D / u ^ 2 +
          eps +
          T <
        D) :
    let r := s ^ 2
    eta *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * r)) +
        eps +
        LLS.PaperStatements.gaussianPrefixError P q (r ^ 2) <
      D := by
  intro r
  have hspos : 0 < s := hu.trans_le hs0
  have hrpos : 0 < r := sq_pos_of_pos hspos
  have hreq : r = s ^ 2 := rfl
  have hpole := gaussianBudget_pole_bound hrpos hreq hG
  have hqPole :
    gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log q + 4) / r) ≤
      gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) := by
    apply mul_le_mul_of_nonneg_left
    · apply div_le_div_of_nonneg_right
      · have hmul := mul_le_mul_of_nonneg_left hq (by norm_num only : (0 : ℝ) ≤ 7 / 6)
        linarith only [hmul]
      · exact hrpos.le
    · norm_num only [gaussian6FifthsEndpoint]
  have hinverse := inverse_pair_le_anchor hu hs0 h1 h2
  have hid :
    eta *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * r)) +
        (7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
            (7 * gaussian6FifthsEndpoint * gaussianMRRefinedBeta /
                (6 * gaussianMRRefinedConductor)) /
              s +
          (gaussian6FifthsEndpoint * (4 - 7 * (D) / (6 * gaussianMRRefinedConductor))) / s ^ 2) =
      7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
        gaussian1000ResidualA eta / s +
        gaussianLowResidualV eta D / s ^ 2 := by
    rw [hreq]
    dsimp only [gaussian1000ResidualA, gaussianLowResidualV]
    ring
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hrpos.le]
  dsimp only [gaussian6FifthsEndpoint] at hpole hqPole hid hstrict ⊢
  linarith only [hpole, hqPole, htail, hid, hinverse, hstrict]

/-- The inverse-root coefficient for the scale 7559/10000 at index four. -/
noncomputable def gaussianLowFourA : ℝ :=
  (4 / (7559 / 10000)) * (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth)) -
    (3 / (7559 / 10000)) *
      (7 * gaussian6FifthsEndpoint * gaussianMRRefinedBeta / (6 * gaussianMRRefinedConductor))

/-- The signed inverse-radius coefficient for the scaled index-four comparison. -/
noncomputable def gaussianLowFourV (D : ℝ) : ℝ :=
  (4 / (7559 / 10000)) * (1839 * gaussian6FifthsEndpoint / 1000) +
    (3 / (7559 / 10000)) *
      (gaussian6FifthsEndpoint * (4 - 7 * D / (6 * gaussianMRRefinedConductor)))

/-- The actual scaled prefix error is below 204/5 when its signed inverse
coefficients and tail satisfy the stated rational anchor checks. The factor 3/alpha
comes from the conductor pole and 4/alpha from smoothing. -/
theorem gaussianLow_four_error {L s P D u T : ℝ} (hu : 0 < u) (hs : u ≤ s)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + D ≤ gaussianMRRefinedD * s ^ 2)
    (h1 : 0 ≤ gaussianLowFourA * u + gaussianLowFourV D)
    (h2 : 0 ≤ gaussianLowFourA * u + 2 * gaussianLowFourV D)
    (hstrict :
      3 * ((12871 / 1000 : ℝ) - 2 * P) +
          (3 / (7559 / 10000)) *
            (7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor)) +
          13 +
          3 * T +
          gaussianLowFourA / u +
          gaussianLowFourV D / u ^ 2 <
        (204 / 5))
    (htail :
      (473 / 10 : ℝ) * (((7559 / 10000 : ℝ) * s ^ 2) ^ 2) ^ (-9 / 16 : ℝ) +
          (512 / 27 : ℝ) / ((7559 / 10000 : ℝ) * s ^ 2) ^ 2 ≤
        T)
    {n : ℕ} (hn : Real.log n ≤ L) :
    let r := s ^ 2
    4 *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * (7559 / 10000) * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * (7559 / 10000) * r)) +
        13 +
        3 * LLS.PaperStatements.gaussianPrefixError P n (((7559 / 10000 : ℝ) * r) ^ 2) <
      (204 / 5) := by
  intro r
  have hspos : 0 < s := hu.trans_le hs
  have hrpos : 0 < r := sq_pos_of_pos hspos
  have hscaledpos : 0 ≤ (7559 / 10000 : ℝ) * r := mul_nonneg (by norm_num only) hrpos.le
  have hpole := gaussianBudget_pole_bound hrpos (show r = s ^ 2 from rfl) hG
  have hqPole :
    gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log n + 4) / r) ≤
      gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) := by
    apply mul_le_mul_of_nonneg_left
    · apply div_le_div_of_nonneg_right
      · have hh := mul_le_mul_of_nonneg_left hn (by norm_num only : (0 : ℝ) ≤ 7 / 6)
        linarith only [hh]
      · exact hrpos.le
    · norm_num only [gaussian6FifthsEndpoint]
  have hinverse := inverse_pair_le_anchor hu hs h1 h2
  have hid :
    4 *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * (7559 / 10000) * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * (7559 / 10000) * r)) +
        (3 / (7559 / 10000)) *
          (7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
              (7 * gaussian6FifthsEndpoint * gaussianMRRefinedBeta /
                  (6 * gaussianMRRefinedConductor)) /
                s +
            (gaussian6FifthsEndpoint * (4 - 7 * D / (6 * gaussianMRRefinedConductor))) / s ^ 2) =
      (3 / (7559 / 10000)) *
          (7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor)) +
        gaussianLowFourA / s +
        gaussianLowFourV D / s ^ 2 := by
    dsimp only [gaussianLowFourA, gaussianLowFourV, r]
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num only
    ring
  have hpoleEq :
    3 * (gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log n + 4) / ((7559 / 10000 : ℝ) * r))) =
      (3 / (7559 / 10000)) * (gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log n + 4) / r)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num only
    ring
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hscaledpos]
  dsimp only [gaussian6FifthsEndpoint] at hpole hqPole hid hstrict hpoleEq ⊢
  linarith only [hpole, hqPole, htail, hid, hinverse, hstrict, hpoleEq]

/-- Above the low anchor and its minimum allowance, the main quadratic
exceeds 204/5. Rational coefficients and a square at the anchor prove the margin. -/
theorem gaussianLow_four_margin_low {s D : ℝ} (hs : 91 / 10 ≤ s) (hD : 93 / 10 ≤ D) :
    (204 / 5 : ℝ) <
      ((7559 / 10000 : ℝ) * (10971611 / 5000000) - 2 * gaussianMRRefinedD) * s ^ 2 -
          (4 * ((7559 / 10000 : ℝ) * (81470555 / 100000000) * (2 / 5) + 1 / (10 * (2 / 5))) -
              2 * gaussianMRRefinedBeta) *
            s +
        2 * D := by
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
    gaussian6FifthsIndex, gaussian6FifthsEndpoint, gaussianMRRefinedWidth]
  nlinarith only [hs, hD, sq_nonneg (s - (91 / 10))]

/-- Exact rational checks for the low index-four common residual budget. -/
theorem gaussianLow_four_checks_low :
    0 ≤ gaussianLowFourA * (91 / 10) + gaussianLowFourV (93 / 10) ∧
      0 ≤ gaussianLowFourA * (91 / 10) + 2 * gaussianLowFourV (93 / 10) ∧
      3 * ((12871 / 1000 : ℝ) - 2 * (901 / 250)) +
          (3 / (7559 / 10000)) *
            (7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor)) +
          13 +
          3 * (458 / 1000) +
          gaussianLowFourA / (91 / 10) +
          gaussianLowFourV (93 / 10) / (91 / 10) ^ 2 <
        204 / 5 := by
  norm_num only [gaussianLowFourA, gaussianLowFourV, gaussian6FifthsEndpoint, gaussianMRRefinedD,
    gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussian6FifthsIndex,
    gaussianMRRefinedConductor, and_self]

/-- Above the upper anchor and its minimum allowance, the main quadratic
exceeds 204/5. Rational coefficients and a square at the anchor prove the margin. -/
theorem gaussianLow_four_margin_upper {s D : ℝ} (hs : 19 / 2 ≤ s) (hD : 813 / 100 ≤ D) :
    (204 / 5 : ℝ) <
      ((7559 / 10000 : ℝ) * (10971611 / 5000000) - 2 * gaussianMRRefinedD) * s ^ 2 -
          (4 * ((7559 / 10000 : ℝ) * (81470555 / 100000000) * (2 / 5) + 1 / (10 * (2 / 5))) -
              2 * gaussianMRRefinedBeta) *
            s +
        2 * D := by
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
    gaussian6FifthsIndex, gaussian6FifthsEndpoint, gaussianMRRefinedWidth]
  nlinarith only [hs, hD, sq_nonneg (s - (19 / 2))]

/-- Exact rational checks for the upper index-four common residual budget. -/
theorem gaussianLow_four_checks_upper :
    0 ≤ gaussianLowFourA * (19 / 2) + gaussianLowFourV (813 / 100) ∧
      0 ≤ gaussianLowFourA * (19 / 2) + 2 * gaussianLowFourV (813 / 100) ∧
      3 * ((12871 / 1000 : ℝ) - 2 * (901 / 250)) +
          (3 / (7559 / 10000)) *
            (7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor)) +
          13 +
          3 * (415 / 1000) +
          gaussianLowFourA / (19 / 2) +
          gaussianLowFourV (813 / 100) / (19 / 2) ^ 2 <
        204 / 5 := by
  norm_num only [gaussianLowFourA, gaussianLowFourV, gaussian6FifthsEndpoint, gaussianMRRefinedD,
    gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussian6FifthsIndex,
    gaussianMRRefinedConductor, and_self]

/-- The low floor uses a coarse pole estimate from c*L<=d*s squared.
Positive inverse coefficients avoid the signed-pair condition that fails at 9.1.
Together with a tail certificate this bounds the actual large-index prefix error. -/
theorem gaussianLow_coarse_error {L eta eps D s u P T : ℝ} {q : ℕ} (hu : 0 < u) (hs0 : u ≤ s)
    (hD : 0 ≤ D)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + D ≤ gaussianMRRefinedD * s ^ 2)
    (hq : Real.log q ≤ L)
    (h1 :
      0 ≤
        (eta * (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth))) * u +
          (eta * (1839 * gaussian6FifthsEndpoint / 1000) + 4 * gaussian6FifthsEndpoint))
    (h2 :
      0 ≤
        (eta * (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth))) * u +
          2 * (eta * (1839 * gaussian6FifthsEndpoint / 1000) + 4 * gaussian6FifthsEndpoint))
    (htail : (473 / 10 : ℝ) * ((s ^ 2) ^ 2) ^ (-9 / 16 : ℝ) + (512 / 27 : ℝ) / (s ^ 2) ^ 2 ≤ T)
    (hstrict :
      (12871 / 1000 : ℝ) - 2 * P +
          7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
          (eta * (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth))) / u +
          (eta * (1839 * gaussian6FifthsEndpoint / 1000) + 4 * gaussian6FifthsEndpoint) / u ^ 2 +
          eps +
          T <
        D) :
    let r := s ^ 2
    eta *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * r)) +
        eps +
        LLS.PaperStatements.gaussianPrefixError P q (r ^ 2) <
      D := by
  intro r
  have hspos : 0 < s := hu.trans_le hs0
  have hrpos : 0 < r := sq_pos_of_pos hspos
  have hreq : r = s ^ 2 := rfl
  have hb := mul_nonneg gaussianMRRefined_coefficients.2.le hspos.le
  have hweak : gaussianMRRefinedConductor * L ≤ gaussianMRRefinedD * r := by
    rw [hreq]
    linarith only [hG, hb, hD]
  have hpole :
    gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) ≤
      7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
        (4 * gaussian6FifthsEndpoint) / s ^ 2 := by
    have hratio : L / r ≤ gaussianMRRefinedD / gaussianMRRefinedConductor := by
      apply (div_le_iff₀ hrpos).mpr
      norm_num only [gaussianMRRefinedConductor] at hweak ⊢
      linarith only [hweak]
    have hm :=
      mul_le_mul_of_nonneg_left hratio
        (by norm_num only [gaussian6FifthsEndpoint] : 0 ≤ gaussian6FifthsEndpoint * (7 / 6))
    have hid :
      gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) =
        gaussian6FifthsEndpoint * (7 / 6) * (L / r) + (4 * gaussian6FifthsEndpoint) / r := by
      ring
    rw [hid, hreq]
    have he :
      gaussian6FifthsEndpoint * (7 / 6) * (gaussianMRRefinedD / gaussianMRRefinedConductor) =
        7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) := by
      ring
    rw [he] at hm
    rw [hreq] at hm
    linarith only [hm]
  have hqPole :
    gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log q + 4) / r) ≤
      gaussian6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) := by
    apply mul_le_mul_of_nonneg_left
    · apply div_le_div_of_nonneg_right
      · have hmul := mul_le_mul_of_nonneg_left hq (by norm_num only : (0 : ℝ) ≤ 7 / 6)
        linarith only [hmul]
      · exact hrpos.le
    · norm_num only [gaussian6FifthsEndpoint]
  have hinverse := inverse_pair_le_anchor hu hs0 h1 h2
  have hid :
    eta *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * r)) +
        (7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
          (4 * gaussian6FifthsEndpoint) / s ^ 2) =
      7 * gaussian6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
        (eta * (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth))) / s +
        (eta * (1839 * gaussian6FifthsEndpoint / 1000) + 4 * gaussian6FifthsEndpoint) / s ^ 2 := by
    rw [hreq]
    ring
  change (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) + (512 / 27 : ℝ) / r ^ 2 ≤ T at htail
  dsimp only [gaussian6FifthsEndpoint] at hinverse
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hrpos.le]
  dsimp only [gaussian6FifthsEndpoint] at hpole hqPole hid hstrict ⊢
  linarith only [hpole, hqPole, htail, hid, hinverse, hstrict]

/-- A residual cap at index one billion bounds every larger index.
The ratio and the independent error both decrease, with nonnegative smoothing. -/
theorem gaussianLow_index_error {m s r P D : ℝ} {q : ℕ} (hs : 0 < s) (hr : 0 < r)
    (hm : gaussian6FifthsIndex ≤ m)
    (hcap :
      (gaussian6FifthsIndex / (gaussian6FifthsIndex - 1)) *
            (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
              1839 * gaussian6FifthsEndpoint / (1000 * r)) +
          13 / (gaussian6FifthsIndex - 1) +
          LLS.PaperStatements.gaussianPrefixError P q (r ^ 2) <
        D) :
    (m / (m - 1)) *
          (21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussian6FifthsEndpoint / (1000 * r)) +
        13 / (m - 1) +
        LLS.PaperStatements.gaussianPrefixError P q (r ^ 2) <
      D := by
  have hmain :
    0 ≤
      21 * gaussian6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
        1839 * gaussian6FifthsEndpoint / (1000 * r) := by
    exact
      add_nonneg
        (div_nonneg (by norm_num only [gaussian6FifthsEndpoint])
          (mul_nonneg (by norm_num only [gaussianMRRefinedWidth]) hs.le))
        (div_nonneg (by norm_num only [gaussian6FifthsEndpoint])
          (mul_nonneg (by norm_num only) hr.le))
  have hcoef := gaussianMRRefined_index_coeffs hm
  have hratio := mul_le_mul_of_nonneg_right hcoef.2.1 hmain
  have hden : gaussian6FifthsIndex - 1 ≤ m - 1 := by linarith only [hm]
  have heps :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 13)
      (by norm_num only [gaussian6FifthsIndex] : 0 < gaussian6FifthsIndex - 1) hden
  linarith only [hcap, hratio, heps]

end PseudoPrime.PrimeTestBounds.MillerRabin
