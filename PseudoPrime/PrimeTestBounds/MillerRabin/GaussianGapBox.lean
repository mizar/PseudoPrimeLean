/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Cutoff
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianKernel137
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianFirstCutoff
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgeBoundary663
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PsiQuarterBridge
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectBox663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMass656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTail663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaEndpoints656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticPairSign
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleCharacters
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleConductors
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflect663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMass656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTail663

/-! # Affine gap bounds for Gaussian witness cells -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- When the coefficient of the radius is nonpositive, evaluating the
combined linear term at the right endpoint gives a lower bound throughout
the cell. The division uses the fixed positive scale of that cell. -/
theorem gaussian_gap_right_bound {y right scale α β : ℝ} (hy : y ≤ right) (hs : 0 < scale)
    (hαβ : α * scale ≤ β) : α * right - β * right / scale ≤ α * y - β * y / scale := by
  have hβ := (le_div_iff₀ hs).mpr hαβ
  calc
    α * right - β * right / scale = (α - β / scale) * right := by ring
    _ ≤ (α - β / scale) * y := mul_le_mul_of_nonpos_left hy (sub_nonpos.mpr hβ)
    _ = α * y - β * y / scale := by ring

/-- For a fixed scale, a positive rational-box comparison at the right
endpoint implies positivity of the radius-dependent gap throughout the
cell. The independent term and the residual may use different bounds. -/
theorem gaussian_gap_box_pos {y right scale α β independent independentLo cost costHi : ℝ}
    (hy : y ≤ right) (hs : 0 < scale) (hαβ : α * scale ≤ β) (hi : independentLo ≤ independent)
    (hc : cost ≤ costHi) (hbox : 0 < independentLo + α * right - (β * right + costHi) / scale) :
    0 < independent + α * y - (β * y + cost) / scale := by
  have ha := gaussian_gap_right_bound hy hs hαβ
  have hb := div_le_div_of_nonneg_right hc hs.le
  simp only [add_div] at hbox ⊢
  linarith only [ha, hb, hi, hbox]

/-- The actual K137 principal coefficient minus the shifted residue gives
a nonpositive combined slope for every scale in the prescribed interval. -/
theorem gaussian_k137_slope {scale : ℝ} (hs : 0 ≤ scale) (hu : scale ≤ 26 / 25) :
    ((4 * (∫ u : ℝ in (0 : ℝ)..1, (gaussianKernel137.transform u).re / Real.sqrt u) -
            (gaussianKernel137.function (1 / 2)).re) -
          quarterAuxHalfCoeff663) *
        scale ≤
      3 / 4 + quarterAuxMix663 quarterConductorProfile663 := by
  exact
    (mul_le_mul_of_nonneg_right
          (sub_le_sub_right gaussian_principal_delta_upper quarterAuxHalfCoeff663) hs).trans
      (k137_scaled_slope_le hs hu)

private theorem k137_first_linear_lower :
    let scale : ℝ := 250074514713 / 250000000000
    let α :=
      (4 * (∫ u : ℝ in (0 : ℝ)..1, (gaussianKernel137.transform u).re / Real.sqrt u) -
          (gaussianKernel137.function (1 / 2)).re) -
        quarterAuxHalfCoeff663
    let β := 3 / 4 + quarterAuxMix663 quarterConductorProfile663
    (-10.532 : ℝ) ≤ α * (scale * (2653 / 4) / 2) - β * (2653 / 4) / 2 := by
  dsimp only
  linarith only [gaussian_principal_delta_137, quarter_aux_delta_lower_663,
    quarter_aux_half_upper_663]

/-- The right endpoint bounds the combined linear term throughout the first
K137 cell using the actual principal kernel and shifted conductor coefficients. -/
theorem gaussian_k137_first_linear_lower {L : ℝ} (hL : L ≤ 2653 / 4) :
    let scale : ℝ := 250074514713 / 250000000000
    let α :=
      (4 * (∫ u : ℝ in (0 : ℝ)..1, (gaussianKernel137.transform u).re / Real.sqrt u) -
          (gaussianKernel137.function (1 / 2)).re) -
        quarterAuxHalfCoeff663
    let β := 3 / 4 + quarterAuxMix663 quarterConductorProfile663
    (-10.532 : ℝ) ≤ α * (scale * L / 2) - β * (scale * L / 2) / scale := by
  intro scale α β
  have hs : 0 < scale := by norm_num only [scale]
  have hu : scale ≤ 26 / 25 := by norm_num only [scale]
  have h :=
    gaussian_gap_right_bound
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL hs.le)
        (by norm_num only : (0 : ℝ) ≤ 2))
      hs (gaussian_k137_slope hs.le hu)
  rw [show β * (scale * (2653 / 4) / 2) / scale = β * (2653 / 4) / 2
      by
      apply (div_eq_iff hs.ne').mpr
      ring] at h
  exact k137_first_linear_lower.trans h

private theorem k137_wide_linear_endpoint :
    let scale : ℝ := 250074514713 / 250000000000
    let α :=
      (4 * (∫ u : ℝ in (0 : ℝ)..1, (gaussianKernel137.transform u).re / Real.sqrt u) -
          (gaussianKernel137.function (1 / 2)).re) -
        quarterAuxHalfCoeff663
    let β := 3 / 4 + quarterAuxMix663 quarterConductorProfile663
    (-10.536 : ℝ) ≤ α * (scale * (1327 / 2) / 2) - β * (1327 / 2) / 2 := by
  dsimp only
  linarith only [gaussian_principal_delta_137, quarter_aux_delta_lower_663,
    quarter_aux_half_upper_663]

private theorem k137_wide_linear_lower {L : ℝ} (hL : L ≤ 1327 / 2) :
    let scale : ℝ := 250074514713 / 250000000000
    let α :=
      (4 * (∫ u : ℝ in (0 : ℝ)..1, (gaussianKernel137.transform u).re / Real.sqrt u) -
          (gaussianKernel137.function (1 / 2)).re) -
        quarterAuxHalfCoeff663
    let β := 3 / 4 + quarterAuxMix663 quarterConductorProfile663
    (-10.536 : ℝ) ≤ α * (scale * L / 2) - β * (scale * L / 2) / scale := by
  intro scale α β
  have hs : 0 < scale := by norm_num only [scale]
  have hu : scale ≤ 26 / 25 := by norm_num only [scale]
  have h :=
    gaussian_gap_right_bound
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL hs.le)
        (by norm_num only : (0 : ℝ) ≤ 2))
      hs (gaussian_k137_slope hs.le hu)
  rw [show β * (scale * (1327 / 2) / 2) / scale = β * (1327 / 2) / 2
      by
      apply (div_eq_iff hs.ne').mpr
      ring] at h
  exact k137_wide_linear_endpoint.trans h

private theorem k137_first_radius_mem {L : ℝ} (hL : L ∈ Set.Icc 663 (1327 / 2)) :
    (250074514713 / 250000000000 : ℝ) * L / 2 ∈ Set.Icc (663 / 2) 332 := by
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- On radii from 663/2 to 1329/4 and scales at least one, the shifted
conductor and negative half-point residue together cost at most 2.452. -/
theorem gaussian_k137_shift_lower {y scale : ℝ} (hy : y ∈ Set.Icc (663 / 2) (1329 / 4))
    (hscale : 1 ≤ scale) :
    (-2.452 : ℝ) ≤ quarterAuxTheta663 y / scale + quarterAuxNegPole663 / y := by
  have hθ := quarter_theta_lower_from663 hy
  have hs := zero_lt_one.trans_le hscale
  have hmul : (-2.507 : ℝ) * scale ≤ -2.507 := by linarith only [hscale]
  have hθ' : (-2.507 : ℝ) ≤ quarterAuxTheta663 y / scale := (le_div_iff₀ hs).mpr (hmul.trans hθ)
  have hy₀ : 0 < y := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hy.1
  have hp : (0.055 : ℝ) ≤ quarterAuxNegPole663 / y :=
    (le_div_iff₀ hy₀).mpr (by linarith only [hy.2, quarter_aux_neg_pole_box_663.1])
  linarith only [hθ', hp]

/-- Over the K137 radii the shifted reflection contribution is bounded
using the shared Abel moments and the zero-deficit prefix through 322 squared. -/
theorem gaussian_k137_reflect_lower (hRH : RiemannHypothesis) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 4)
    (hp : ∀ n ∈ Finset.Ioc 0 103684, ArithmeticFunction.vonMangoldt n ≠ 0 → a n = 0) {y : ℝ}
    (hy : y ∈ Set.Icc (663 / 2) (1329 / 4)) :
    (-0.003326 : ℝ) ≤
      ∑ i, (quarterCoeff663 i : ℝ) * quarterAuxReflection656 a y (quarterShift663 i : ℝ) := by
  have h₀ : 0 < y := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hy.1
  have hb : y ∈ Set.Icc 328 (1329 / 4) :=
    ⟨(by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hy.1, hy.2⟩
  have he : Real.exp 4 < 328 := by
    rw [show (4 : ℝ) = (4 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    exact (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4).trans_lt (by norm_num only)
  have hl := (Real.lt_log_iff_exp_lt h₀).mpr (he.trans_le hb.1)
  have hlog : 7 ≤ 2 * Real.log y := by linarith only [hl]
  exact
    (quarter_reflect_lower_box_663 hb hlog).trans
      (quarter_reflection_tail_663 hRH (by norm_num only) (by norm_num only) a ha hp h₀ hlog)

/-- Three characters that equal one at primes up to a K137 cutoff
have zero trace deficit on the Mangoldt support through 322 squared. -/
theorem gaussian_k137_deficit_prefix {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {y : ℝ} (hy' : 663 / 2 ≤ y) :
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → b l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → c l = 1) →
      ∀ n ∈ Finset.Ioc 0 103684,
        ArithmeticFunction.vonMangoldt n ≠ 0 → 3 - ((a n).re + (b n).re + (c n).re) = 0 := by
  intro ha hb hc n hn hΛ
  have hy : (322 : ℝ) ≤ y := (by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hy'
  have hn' : (n : ℝ) ≤ 103684 := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hB : (103684 : ℝ) ≤ (322 : ℝ) ^ 2 := by norm_num only
  have hx := hn'.trans (hB.trans (pow_le_pow_left₀ (by norm_num only) hy 2))
  simp only [AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero a ha hx hΛ,
    AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero b hb hx hΛ,
    AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero c hc hx hΛ,
    Complex.one_re]
  norm_num only

/-- The unshifted Euler deficit costs at most 0.000242 over the K137 radii
when all three characters equal one at primes through the cutoff. -/
theorem gaussian_k137_main_reflect {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hRH : RiemannHypothesis) {y : ℝ} (hy : y ∈ Set.Icc (663 / 2) (1329 / 4))
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) :
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → b l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → c l = 1) →
      3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (y ^ 2) -
          (quarterMainEuler656 a (y ^ 2) + quarterMainEuler656 b (y ^ 2) +
            quarterMainEuler656 c (y ^ 2)) ≤
        0.000242 := by
  intro ha hb hc
  have hy' : (328 : ℝ) ≤ y := (by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hy.1
  have h₃₂₂ : (322 : ℝ) ≤ y := (by norm_num only : (322 : ℝ) ≤ 328).trans hy'
  have hB : (103684 : ℝ) ≤ y ^ 2 :=
    (by norm_num only : (103684 : ℝ) ≤ (322 : ℝ) ^ 2).trans
      (pow_le_pow_left₀ (by norm_num only) h₃₂₂ 2)
  exact
    (quarter_main_reflect_cap_656 a b c hRH h₃₂₂ (B := 103684) (by norm_num only) (by norm_num only)
          (by exact_mod_cast hB) ht ha hb hc).trans
      (quarter_main_reflect_box_663 ⟨hy', hy.2⟩)

/-- On the first K137 cell, the two principal terms involving the inverse-scale
profile together cost at most 1.6617 in the zero-based comparison. -/
theorem gaussian_k137_first_main_cost {L : ℝ} (hL : L ∈ Set.Icc 663 (1327 / 2)) :
    let scale : ℝ := 250074514713 / 250000000000
    let y := scale * L / 2
    let R := (gaussianKernel137.transform (y ^ 2)⁻¹).re
    4 * y * R / scale + 3 * Real.log (2 * Real.pi) * R ≤ 1.6617 := by
  intro scale y R
  have hy : (663 / 2 : ℝ) ≤ y := (k137_first_radius_mem hL).1
  have h328 : (328 : ℝ) ≤ y := (by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hy
  have hmid : (1319 / 4 : ℝ) ≤ y := (by norm_num only : (1319 / 4 : ℝ) ≤ 663 / 2).trans hy
  have hc := quarter_main_conductor_box_663 h328
  rw [ite_eq_left hmid] at hc
  change 4 * y * R ≤ _ at hc
  have hc' : 4 * y * R ≤ 1.654812 := by linarith only [hc]
  have hs : 0 < scale := by norm_num only [scale]
  have hs' : (1.654812 : ℝ) ≤ 1.654812 * scale := by norm_num only [scale]
  have hcd : 4 * y * R / scale ≤ 1.654812 := (div_le_iff₀ hs).2 (hc'.trans hs')
  have hlog₀ : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith only [Real.pi_gt_three])
  have hlog : 3 * Real.log (2 * Real.pi) ≤ 5.517 := by linarith only [Analysis.log_two_mul_pi_lt]
  by_cases hR : 0 ≤ R
  · have h1 := mul_le_mul_of_nonneg_right hy hR
    have h2 := mul_le_mul_of_nonneg_right hlog hR
    linarith only [h1, h2, hc', hcd]
  · have h3 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3) hlog₀)
        (le_of_not_ge hR)
    linarith only [h3, hcd]

/-- A lower bound for the remaining terms of the K137 zero-based comparison
above 14.577727 makes the full comparison positive on the first cell.
The remaining terms include the 6.48 multiple of the weight at one. -/
theorem gaussian_k137_first_gap_pos {p q r : ℕ} {L remaining : ℝ} [NeZero p] [NeZero q] [NeZero r]
    (hRH : RiemannHypothesis) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) (hA : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even)
    (hB : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even) (hC : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even)
    (hlev : Real.log p + Real.log q + Real.log r = 2 * L)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hL : L ∈ Set.Icc 663 (2653 / 4)) (hremaining : 14.577727 < remaining) :
    let scale : ℝ := 250074514713 / 250000000000
    let y := scale * L / 2
    let R := (gaussianKernel137.transform (y ^ 2)⁻¹).re
    let α :=
      (4 * (∫ u : ℝ in (0 : ℝ)..1, (gaussianKernel137.transform u).re / Real.sqrt u) -
        (gaussianKernel137.function (1 / 2)).re)
    let β := 3 / 4 + quarterAuxMix663 quarterConductorProfile663
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → b l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → c l = 1) →
      0 <
        remaining + (α * y - β * y / scale) +
            (quarterShiftedForward663 a y + quarterShiftedForward663 b y +
              quarterShiftedForward663 c y) -
          (3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (y ^ 2) -
            (quarterMainEuler656 a (y ^ 2) + quarterMainEuler656 b (y ^ 2) +
              quarterMainEuler656 c (y ^ 2))) -
          (4 * y * R / scale + 3 * Real.log (2 * Real.pi) * R) -
          (3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (y ^ 2)).re +
            6.48 * quarterWeight656 (y ^ 2) 1) := by
  intro scale y R α β ha hb hc
  let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hd (n : ℕ) : 0 ≤ d n ∧ d n ≤ 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have hl := gaussian_k137_first_linear_lower hL.2
  have hw : L ∈ Set.Icc 663 (1327 / 2) := ⟨hL.1, hL.2.trans (by norm_num only)⟩
  have hrad := k137_first_radius_mem hw
  have hy' : y ∈ Set.Icc (663 / 2) (1329 / 4) := ⟨hrad.1, hrad.2.trans (by norm_num only)⟩
  have hs := gaussian_k137_shift_lower (scale := 250074514713 / 250000000000) hy' (by norm_num only)
  have hp := gaussian_k137_deficit_prefix a b c hrad.1 ha hb hc
  have hr := gaussian_k137_reflect_lower hRH d hd hp hy'
  have hm := gaussian_k137_main_reflect a b c hRH hy' ht ha hb hc
  have hcost := gaussian_k137_first_main_cost hw
  have hgamma := quarter_gamma_gaussian_first hy'
  have hy : (328 : ℝ) ≤ y :=
    (by norm_num only : (328 : ℝ) ≤ 663 / 2).trans (k137_first_radius_mem hw).1
  have hlev' : Real.log p + Real.log q + Real.log r = 4 * y / scale := by
    apply (eq_div_iff (by norm_num only [scale] : scale ≠ 0)).mpr
    rw [hlev]
    dsimp only [y]
    ring
  have he := quarter_scaled_shift_mix_663 hA hB hC hRH hy hlev'
  have hz := (abs_le.mp (quarter_shift_xi_cap_663 hRH hy)).1
  dsimp only [α, β, R, y, scale] at hl hs hr hm hcost ⊢
  dsimp only [d, y, scale] at he hz hgamma
  linarith only [hl, hs, hr, hm, hcost, hgamma, he, hz, hremaining]

/-- For the three pair characters of an odd uniform Korselt triple, Gaussian
cutoff passage supplies the prime-triviality and trace hypotheses of the first
K137 comparison. The scale at log 663 supplies the smaller Euler cutoff. -/
theorem gaussian_k137_first_gap_of_pass {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hRH : RiemannHypothesis) (hL : Real.log n ∈ Set.Icc 663 (2653 / 4))
    (hpass :
      ∀ l : ℕ,
        l.Prime →
          (l : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (l : ZMod n))
    {remaining : ℝ} (hremaining : 14.577727 < remaining) :
    let scale : ℝ := 250074514713 / 250000000000
    let y := scale * Real.log n / 2
    let R := (gaussianKernel137.transform (y ^ 2)⁻¹).re
    let α :=
      (4 * (∫ u : ℝ in (0 : ℝ)..1, (gaussianKernel137.transform u).re / Real.sqrt u) -
        (gaussianKernel137.function (1 / 2)).re)
    let β := 3 / 4 + quarterAuxMix663 quarterConductorProfile663
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    0 <
      remaining + (α * y - β * y / scale) +
          (quarterShiftedForward663 a y + quarterShiftedForward663 b y +
            quarterShiftedForward663 c y) -
        (3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (y ^ 2) -
          (quarterMainEuler656 a (y ^ 2) + quarterMainEuler656 b (y ^ 2) +
            quarterMainEuler656 c (y ^ 2))) -
        (4 * y * R / scale + 3 * Real.log (2 * Real.pi) * R) -
        (3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (y ^ 2)).re +
          6.48 * quarterWeight656 (y ^ 2) 1) := by
  intro scale y R α β a b c
  have hpq : p * q ∣ n := ⟨r, hprod⟩
  have hpr : p * r ∣ n := ⟨q, hprod.trans (by ac_rfl)⟩
  have hqr : q * r ∣ n := ⟨p, hprod.trans (by ac_rfl)⟩
  have dp := (dvd_mul_right p q).trans hpq
  have dq := (dvd_mul_left q p).trans hpq
  have dr := (dvd_mul_left r p).trans hpr
  have hpK := hu.2.2.1 p Fact.out dp
  have hqK := hu.2.2.1 q Fact.out dq
  have hrK := hu.2.2.1 r Fact.out dr
  have hvq := hu.2.2.2 q p Fact.out Fact.out dq dp
  have hvr := hu.2.2.2 r p Fact.out Fact.out dr dp
  have ht (l : ℕ) : (a l).re + (b l).re + (c l).re ∈ Set.Icc (-1) 3 := by
    refine ⟨?_, ?_⟩
    · simpa only [a, b, c, Int.cast_natCast] using
        pair_character_sum_ge_neg_one (l : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
    · linarith only [(Complex.re_le_norm _).trans (a.norm_le_one l),
        (Complex.re_le_norm _).trans (b.norm_le_one l),
        (Complex.re_le_norm _).trans (c.norm_le_one l)]
  have hbase (l : ℕ) (hl : l.Prime) (hy : (l : ℝ) ≤ y ^ 2) :=
    hpass l hl (hy.trans (gaussianCutoff_k137_first hL.1))
  have hp₁ : 1 < p := (Fact.out : p.Prime).one_lt
  have hq₁ : 1 < q := (Fact.out : q.Prime).one_lt
  have hq₀ : 0 < q := (Fact.out : q.Prime).pos
  have hr₀ : 0 < r := (Fact.out : r.Prime).pos
  exact
    gaussian_k137_first_gap_pos hRH a b c
      ⟨pair_character_primitive hu.1 hpq _,
        pair_character_ne_one hu.1 hpq _ (hp₁.trans_le (Nat.le_mul_of_pos_right _ hq₀)),
        (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv,
        pair_character_even_of_korselt hn ho hp hq hpK hqK hvq⟩
      ⟨pair_character_primitive hu.1 hpr _,
        pair_character_ne_one hu.1 hpr _ (hp₁.trans_le (Nat.le_mul_of_pos_right _ hr₀)),
        (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv,
        pair_character_even_of_korselt hn ho hp hr hpK hrK hvr⟩
      ⟨pair_character_primitive hu.1 hqr _,
        pair_character_ne_one hu.1 hqr _ (hq₁.trans_le (Nat.le_mul_of_pos_right _ hr₀)),
        (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv,
        pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)⟩
      (pair_level_log_sum hprod) ht hL hremaining
      (fun l hl hy ↦ pair_character_nat_eq_one hn ho hp hq dp dq hpq hpK hqK hvq l (hbase l hl hy))
      (fun l hl hy ↦ pair_character_nat_eq_one hn ho hp hr dp dr hpr hpK hrK hvr l (hbase l hl hy))
      (fun l hl hy ↦
        pair_character_nat_eq_one hn ho hq hr dq dr hqr hqK hrK (hvr.trans hvq.symm) l
          (hbase l hl hy))

/-- The principal part still needed in the first K137 cell. It combines
the weighted prime prefix and recovered powers with the reflected Euler
sum and the two centering terms. -/
noncomputable def gaussian_k137_principal {K : Finset ℕ} (y : ℝ) : ℝ :=
  let x := y ^ 2
  let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
  let Δ :=
    4 * (∫ u : ℝ in (0 : ℝ)..1, (gaussianKernel137.transform u).re / Real.sqrt u) -
      (gaussianKernel137.function (1 / 2)).re
  4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) - Δ * y +
    (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 x n)) +
    3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) x +
    3 * Real.log (2 * Real.pi) * (gaussianKernel137.transform x⁻¹).re +
    6.48 * quarterWeight656 x 1

/-- A strict lower bound on the principal part of the first Gaussian cell
contradicts simultaneous prime triviality of the three pair characters. -/
theorem gaussian_k137_first_impossible {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc 663 (2653 / 4)) (hlev : Real.log p + Real.log q + Real.log r = 2 * L)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) (K : Finset ℕ) :
    let y := (250074514713 / 250000000000 : ℝ) * L / 2
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → b l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → c l = 1) →
      (∀ n ∈ K, y ^ 2 < (n : ℝ)) →
      (∀ n ∈ K, Real.log ((n : ℝ) / y ^ 2) ≤ 21 / 8) →
      (∀ n ∈ K, ∃ l k : ℕ, l.Prime ∧ 2 ≤ k ∧ n = l ^ k) →
      0.02926417 < gaussian_k137_principal (K := K) y → False := by
  intro y hpa hpb hpc hK hU hpow hnum
  have hlev' : Real.log p + Real.log q + Real.log r = 4 * (L / 2) := by linarith only [hlev]
  have hupper :=
    quarter_gaussian_comparison_upper ha hb hc hp hq hr hG
      (k137_first_radius_mem ⟨hL.1, hL.2.trans (by norm_num only)⟩) hlev' ht hpa hpb hpc K hK hU
      hpow
  have hrest : 14.577727 < gaussian_k137_principal (K := K) y + 14.54846283 := by
    linarith only [hnum]
  have hpos := gaussian_k137_first_gap_pos hG.riemann a b c ha hb hc hlev ht hL hrest hpa hpb hpc
  dsimp only [gaussian_k137_principal, gaussianKernel137, y] at hupper hpos
  ring_nf at hupper hpos
  linarith only [hupper, hpos]

/-- In the first K137 cell the already certified prime powers add at least
0.137116529 to the principal part, leaving a negative target for its other terms. -/
theorem gaussian_k137_first_principal_lb {L : ℝ} (hL : L ∈ Set.Icc 663 (1327 / 2)) :
    let y := (250074514713 / 250000000000 : ℝ) * L / 2
    (-0.107852359 : ℝ) < gaussian_k137_principal (K := ∅) y →
      0.02926417 < gaussian_k137_principal (K := fixedPowers663) y := by
  intro y h
  have hy := k137_first_radius_mem hL
  have hb : y ∈ Set.Icc 328 332 := ⟨(by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hy.1, hy.2⟩
  have hg := fixed_power_gain_wide_663 hb
  simp only [gaussian_k137_principal, Finset.sum_empty, add_zero] at h ⊢
  linarith only [h, hg]

/-- After cancelling the principal Gamma term and the centering terms,
the principal part is the recovered power mass plus the signed Abel
error, the negative half-point residue, and the principal zero sum. -/
theorem gaussian_k137_principal_abel (hRH : RiemannHypothesis) (K : Finset ℕ) {y : ℝ} (hy : 1 ≤ y) :
    let x := y ^ 2
    let P := fun t : ℝ ↦ (quarterKernel656.function (t : ℂ) * (x : ℂ) ^ (t : ℂ)).re
    gaussian_k137_principal (K := K) y -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        6.48 * quarterWeight656 x 1 -
        3 * Real.log (2 * Real.pi) * (gaussianKernel137.transform x⁻¹).re =
      (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 x n)) +
          4 * (Chebyshev.psi x - x) * quarterWeight656 x x +
          4 *
            (∫ t in x..x * Real.exp (21 / 8),
              (Chebyshev.psi t - t) * deriv (quarterWeight656 x) t) +
          3 * P (-1 / 2) -
        3 * (∑' ρ, quarterKernel656.zetaOscillatingZeroTerm x ρ).re := by
  intro x P
  have hy₀ := zero_lt_one.trans_le hy
  have hx : 1 ≤ x := one_le_pow₀ hy
  have hx₀ := zero_lt_one.trans_le hx
  have hc := quarter_main_level_cancel_656 hx
  rw [quarter_level_gamma_central_656 hx, quarter_main_xi_zeros_656 hRH hx] at hc
  simp only [Complex.sub_re] at hc
  rw [Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_summand quarterKernel656
        (1 : DirichletCharacter ℂ 1) hx₀)] at hc
  have hA := quarter_principal_abel_663 hx₀
  have hI :=
    quarter_scale_integral_656 hx₀ hx₀
      (le_mul_of_one_le_right hx₀.le (Real.one_le_exp (by norm_num only))) le_rfl
  rw [div_self hx₀.ne', mul_div_cancel_left₀ _ hx₀.ne'] at hI
  change _ = Real.sqrt (y ^ 2) * quarterTailMass663 at hI
  rw [Real.sqrt_sq hy₀.le] at hI
  have hP := (main_poles_656 hy₀).2
  change P (1 / 2) = _ at hP
  have hp : P (1 / 2) = (quarterKernel656.function (1 / 2)).re * y := by
    rw [hP, quarterKernel656, LLS.PaperStatements.rationalPole_half_value]
    norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd]
    ring
  have hmass := congrArg (fun q : ℝ ↦ y * q) tail_mass_split
  dsimp only [gaussian_k137_principal, gaussianKernel137, x, P] at hA hI hp hc ⊢
  ring_nf at hmass hp hA hI hc ⊢
  linear_combination -4 * hA - 4 * hI + 3 * hp - 3 * hc - 4 * hmass

/-- A signed Abel error at most 0.060 contradicts passing prime agreement
if the recovered powers supply the stated scalar budget. -/
theorem gaussian_k137_first_abel_impossible {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc 663 (1327 / 2)) (hlev : Real.log p + Real.log q + Real.log r = 2 * L)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) (K : Finset ℕ) :
    let y := (250074514713 / 250000000000 : ℝ) * L / 2
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → b l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → c l = 1) →
      (∀ n ∈ K, y ^ 2 < (n : ℝ)) →
      (∀ n ∈ K, Real.log ((n : ℝ) / y ^ 2) ≤ 21 / 8) →
      (∀ n ∈ K, ∃ l k : ℕ, l.Prime ∧ 2 ≤ k ∧ n = l ^ k) →
      0.137116529 ≤ (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (y ^ 2) n)) →
      (-4 * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) -
          4 *
            (∫ u in y ^ 2..y ^ 2 * Real.exp (21 / 8),
              (Chebyshev.psi u - u) * deriv (quarterWeight656 (y ^ 2)) u)) ≤
        0.060 →
      False := by
  intro y hpa hpb hpc hK hU hpow hgain hnum
  let scale : ℝ := 250074514713 / 250000000000
  let R := (quarterKernel656.transform (y ^ 2)⁻¹).re
  let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hy := k137_first_radius_mem hL
  have hy' : y ∈ Set.Icc 328 332 := ⟨(by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hy.1, hy.2⟩
  have h1 : 1 ≤ y := (by norm_num only : (1 : ℝ) ≤ 328).trans hy'.1
  have h0 := zero_lt_one.trans_le h1
  have hs : scale ≠ 0 := by norm_num only [scale]
  have hscale : y / scale = L / 2 := by
    apply (div_eq_iff hs).mpr
    dsimp only [y, scale]
    ring
  have hlev' : Real.log p + Real.log q + Real.log r = 4 * (y / scale) := by
    rw [hscale]
    linarith only [hlev]
  have hupper :=
    quarter_gaussian_comparison_upper ha hb hc hp hq hr hG hy hlev' ht hpa hpb hpc K hK hU hpow
  have hd (n : ℕ) : 0 ≤ d n ∧ d n ≤ 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have hywide : y ∈ Set.Icc (663 / 2) (1329 / 4) := ⟨hy.1, hy.2.trans (by norm_num only)⟩
  have hprefix := gaussian_k137_deficit_prefix a b c hy.1 hpa hpb hpc
  have hshift :=
    quarter_scaled_shift_mix_663 ha hb hc hG.riemann hy'.1
      (by simpa only [mul_div_assoc] using hlev')
  have hl := k137_wide_linear_lower hL.2
  have htheta := gaussian_k137_shift_lower (scale := scale) hywide (by norm_num only [scale])
  have href := gaussian_k137_reflect_lower hG.riemann d hd hprefix hywide
  have hxi := (abs_le.mp (quarter_shift_xi_cap_663 hG.riemann hy'.1)).1
  have hm := gaussian_k137_main_reflect a b c hG.riemann hywide ht hpa hpb hpc
  have hgamma := gaussian_k137_principal_abel hG.riemann K h1
  have hzero := (abs_le.mp (quarter_main_zero_abs_656 hG.riemann (one_le_pow₀ h1 : 1 ≤ y ^ 2))).2
  have hpole := (main_poles_656 h0).1
  have hpole' :
    (0.0093267 : ℝ) ≤ ((11 / 10 : ℝ) ^ 5 / (3 / 5) ^ 6 * Real.exp (-(21 / 16))) / y := by
    apply (le_div_iff₀ h0).mpr
    linarith only [hy'.2, negative_pole_lower]
  have hcond := quarter_main_conductor_box_663 hy'.1
  rw [ite_eq_left ((by norm_num only : (1319 / 4 : ℝ) ≤ 663 / 2).trans hy.1)] at hcond
  change 4 * y * R ≤ _ at hcond
  have htR : 4 * (y / scale) * R ≤ 1.654812 := by
    rw [show 4 * (y / scale) * R = (4 * y * R) / scale by ring]
    apply (div_le_iff₀ (by norm_num only [scale] : 0 < scale)).mpr
    have hh : (1.659189 : ℝ) - 0.004377 ≤ 1.654812 * scale := by norm_num only [scale]
    exact hcond.trans hh
  dsimp only [gaussian_k137_principal, gaussianKernel137, d, R, y, scale] at *
  ring_nf at hupper hshift hl hgamma hpole hpole' htR hnum hgain hm hzero htheta href hxi
  linarith only [hupper, hshift, hl, htheta, href, hxi, hm, hgamma, hzero, hpole, hpole', htR,
    hgain, hnum]

/-- The signed Chebyshev boundary charges at most 0.007 to the first K137
cell. The square of its scaled radius stays within the signed walk. -/
theorem gaussian_first_boundary_le {L : ℝ} (hL : L ∈ Set.Icc 663 (1327 / 2)) :
    let y := (250074514713 / 250000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.007 := by
  intro y
  have hy := k137_first_radius_mem hL
  have hlo : (250074514713 / 250000000000 : ℝ) * 663 / 2 ≤ y := by
    dsimp only [y]
    linarith only [hL.1]
  have hhi : y ≤ (250074514713 / 250000000000 : ℝ) * (1327 / 2) / 2 := by
    dsimp only [y]
    linarith only [hL.2]
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_first
      ((by norm_num only : (109957 : ℝ) ≤ ((250074514713 / 250000000000 : ℝ) * 663 / 2) ^ 2).trans
        (pow_le_pow_left₀ (by norm_num only) hlo 2))
      ((pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 663 / 2).trans hy.1) hhi 2).trans
        (by norm_num only))
  have hb :=
    quarter_bridge_boundary_lower (by norm_num only : (0 : ℝ) < 663 / 2) hy.1
      (by norm_num only : (0 : ℝ) ≤ 6) hψ
  dsimp only [y]
  linarith only [hb]

/-- On the first compressed K137 cell `[663, 1327 / 2]`, the existing fixed powers provide all
the recovered mass needed by the Abel comparison. The signed integral
estimate under RH rules out simultaneous prime passage. -/
theorem gaussian_first_cell_abel_false {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc 663 (1327 / 2)) (hlev : Real.log p + Real.log q + Real.log r = 2 * L)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) :
    let y := (250074514713 / 250000000000 : ℝ) * L / 2
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → b l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → c l = 1) → False := by
  intro y hpa hpb hpc
  have hy := k137_first_radius_mem hL
  have hs (n : ℕ) (hn : n ∈ fixedPowers663) :=
    fixed_power_support_wide_663 ⟨(by norm_num only : (325 : ℝ) ≤ 663 / 2).trans hy.1, hy.2⟩ hn
  have hbnd := gaussian_first_boundary_le hL
  have habel := gaussian_first_integral_le hG.riemann ⟨hy.1, hy.2.trans (by norm_num only)⟩
  exact
    gaussian_k137_first_abel_impossible ha hb hc hp hq hr hG hL hlev ht fixedPowers663 hpa hpb hpc
      (fun n hn ↦ (hs n hn).1) (fun n hn ↦ (hs n hn).2.le) (fun _ hn ↦ fixed_power_base_663 hn)
      (fixed_power_gain_wide_663 ⟨(by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hy.1, hy.2⟩)
      (by
        dsimp only [y] at hbnd habel ⊢; linarith only [hbnd, habel])

end PseudoPrime.PrimeTestBounds.MillerRabin
