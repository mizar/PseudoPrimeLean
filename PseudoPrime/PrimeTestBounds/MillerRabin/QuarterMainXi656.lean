/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainGamma656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainGamma656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainEuler656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosinePoles644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSplit656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope656

/-! # Cancellation of the common Gamma terms in the section 132 shifted contours -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The three shifted main contours have one common even Gamma contribution.
Their reflected Euler sums can be written as the level-one contribution plus
the trace deficit already bounded in the section 132 comparison. -/
theorem quarter_shifted_remainders_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) {r h : ℝ} (hr : 0 < r)
    (hx₁ : 1 ≤ r ^ 2 * Real.exp (-(21 / 8 + h))) :
    let x := r ^ 2 * Real.exp (-(21 / 8 + h))
    (contourRemainder656 a x).re + (contourRemainder656 b x).re + (contourRemainder656 c x).re =
      (Real.log p + Real.log q + Real.log s) *
          Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) x⁻¹ +
        3 * ((quarterLevelGamma656 x).re - quarterMainEuler656 (1 : DirichletCharacter ℂ 1) x) +
        quarterAuxReflection656 (fun n ↦ 3 - ((a n).re + (b n).re + (c n).re)) r h := by
  intro x
  have hx : 0 < x := mul_pos (pow_pos hr _) (Real.exp_pos _)
  rw [quarter_main_arch_split_656 ha.1 ha.2.1 ha.2.2.1 hx,
    quarter_main_arch_split_656 hb.1 hb.2.1 hb.2.2.1 hx,
    quarter_main_arch_split_656 hc.1 hc.2.1 hc.2.2.1 hx,
    quarter_even_level_gamma_656 a ha.2.1 ha.2.2.2 x,
    quarter_even_level_gamma_656 b hb.2.1 hb.2.2.2 x,
    quarter_even_level_gamma_656 c hc.2.1 hc.2.2.2 x]
  rw [← quarter_shift_euler_deficit_656 a b c hr hx₁]
  change
    _ =
      _ +
        (3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) x -
          (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x))
  ring

/-- For scales at least one, the normalized right-minus-left pole integral
of the main kernel is its weighted value at either half-unit point. -/
theorem quarter_main_xi_pole_656 {x u : ℝ} (hx : 1 ≤ x) (hl : -9 / 16 < u) (hu : u < 9 / 16) :
    quarterCosinePole quarterKernel656 (9 / 16) u x -
        quarterCosinePole quarterKernel656 (-9 / 16) u x =
      quarterKernel656.function (u : ℂ) * (x : ℂ) ^ (u : ℂ) := by
  apply quarter_cosine_pole_diff quarterKernel656 _ _ hx hl hu
  · norm_num only [quarterKernel656, LLS.PaperStatements.rationalPoleMellinKernel,
      min_eq_right (by norm_num only : (1 / 8 : ℝ) ≤ 3 / 20)]
  · intro z hz _
    have hn : z + (11 / 10 : ℂ) ≠ 0 := by
      intro he
      have hre := congrArg Complex.re he
      have hcast : (11 / 10 : ℂ) = ((11 / 10 : ℝ) : ℂ) := by
        norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
      rw [hcast, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
      linarith only [hz, hre]
    rw [show quarterKernel656.function = fun z : ℂ ↦ _ from funext quarter_function_656]
    have hnum : AnalyticAt ℂ (fun w : ℂ ↦ (11 / 10 : ℂ) ^ 5 * Complex.exp ((21 / 8) * w)) z := by
      fun_prop
    have hden : AnalyticAt ℂ (fun w : ℂ ↦ (w + (11 / 10 : ℂ)) ^ 6) z := by fun_prop
    exact hnum.div hden (pow_ne_zero 6 hn)

/-- On the main left contour, reflect the negative xi logarithmic
derivative to the right half-plane and separate Gamma, zeta and the poles. -/
theorem quarter_main_left_xi_656 (t : ℝ) :
    let z : ℂ := ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w : ℂ := ((17 / 16 : ℝ) : ℂ) - Complex.I * t
    (-logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (z + 1 / 2)) =
      logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor w + logDeriv riemannZeta w -
        1 / (z - 1 / 2) -
        1 / (z + 1 / 2) := by
  intro z w
  have hw : 1 < w.re := by
    simp only [w, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul]
    norm_num only
  have h₁ : z + 1 / 2 = 1 - w := by
    dsimp only [z, w]; push_cast; ring
  have h₂ : w = -(z - 1 / 2) := by linear_combination h₁
  have h₃ : w - 1 = -(z + 1 / 2) := by linear_combination h₂
  rw [h₁, AnalyticNumberTheory.RiemannXi.logDeriv_one_sub, neg_neg,
    AnalyticNumberTheory.RiemannXi.logDeriv_eq_poles_gamma_zeta_of_re_gt_one hw]
  rw [h₃, h₂, div_neg, div_neg]
  ring

/-- The normalized negative xi logarithmic derivative integral of the main
kernel at a real scale and vertical line. The shifted comparison uses the
left and right lines at minus and plus nine sixteenths. -/
noncomputable def quarterMainXiLine656 (d x : ℝ) : ℂ :=
  let z := fun t : ℝ ↦ (d : ℂ) + Complex.I * t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (z t + 1 / 2) *
        (quarterKernel656.function (z t) * (x : ℂ) ^ z t)

/-- The forward level-one sum at positive scale decomposes into the right
xi line, its two pole integrals, and the right Gamma integral. -/
theorem quarter_main_level_forward_656 {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n) =
      quarterMainXiLine656 (9 / 16) x + quarterCosinePole quarterKernel656 (9 / 16) (-1 / 2) x +
        quarterCosinePole quarterKernel656 (9 / 16) (1 / 2) x +
        quarterRightGamma656 (1 : DirichletCharacter ℂ 1) x := by
  have hd : quarterKernel656.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel656, LLS.PaperStatements.rationalPoleMellinKernel,
      min_eq_right (by norm_num only : (1 / 8 : ℝ) ≤ 3 / 20)]
  rw [twoShift_level_one_forward quarterKernel656 hd hx]
  unfold quarterMainXiLine656 quarterCosinePole quarterRightGamma656
  dsimp only
  ring

/-- At positive scale, the left Gamma integral less the reflected Euler
integral equals the left xi line and its two pole integrals in real part. -/
theorem quarter_main_level_left_656 {x : ℝ} (hx : 0 < x) :
    (quarterLevelGamma656 x - quarterRightGamma656 (1 : DirichletCharacter ℂ 1) x).re -
        quarterMainEuler656 (1 : DirichletCharacter ℂ 1) x =
      (quarterMainXiLine656 (-9 / 16) x + quarterCosinePole quarterKernel656 (-9 / 16) (-1 / 2) x +
          quarterCosinePole quarterKernel656 (-9 / 16) (1 / 2) x).re := by
  let z := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  let W := fun t ↦ quarterKernel656.function (z t) * (x : ℂ) ^ z t
  let F := fun t ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (z t + 1 / 2) * W t
  let E := fun t ↦ -logDeriv riemannZeta (w t) * W t
  let P := fun t ↦ (1 / (z t - ((-1 / 2 : ℝ) : ℂ))) * W t
  let Q := fun t ↦ (1 / (z t - ((1 / 2 : ℝ) : ℂ))) * W t
  let G := fun t ↦ logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (w t) * W t
  have hd : quarterKernel656.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel656, LLS.PaperStatements.rationalPoleMellinKernel,
      min_eq_right (by norm_num only : (1 / 8 : ℝ) ≤ 3 / 20)]
  have hl : -1 / 2 - quarterKernel656.delta < (-9 / 16 : ℝ) := by
    rw [hd]; norm_num only
  have hu : (-9 / 16 : ℝ) ≤ 1 / 2 + quarterKernel656.delta := by
    rw [hd]; norm_num only
  have hiF : MeasureTheory.Integrable F :=
    LLS.PaperStatements.MellinKernel.integrable_xi_left_line quarterKernel656 hl (by norm_num only)
      (by norm_num only) hx
  have hiE : MeasureTheory.Integrable E := by
    simpa only [E, w, W, z, Complex.ofReal_neg, mul_neg, ← sub_eq_add_neg,
      DirichletCharacter.LFunction_modOne_eq] using
      quarter_ordinary_integrable_656 (1 : DirichletCharacter ℂ 1) hx
  have hiP : MeasureTheory.Integrable P := by
    simpa only [P, W, z, mul_assoc] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line quarterKernel656 hl hu
        (by norm_num only) (by norm_num only : (-9 / 16 : ℝ) ≠ -1 / 2) hx
  have hiQ : MeasureTheory.Integrable Q := by
    simpa only [Q, W, z, mul_assoc] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line quarterKernel656 hl hu
        (by norm_num only) (by norm_num only : (-9 / 16 : ℝ) ≠ 1 / 2) hx
  have hG : G = (F + E + P + Q) := by
    funext t
    dsimp only [Pi.add_apply, G, F, E, P, Q]
    rw [quarter_main_left_xi_656 t]
    simp only [z, w, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    ring
  have hw (t : ℝ) : 1 / 2 - z t = w t := by
    dsimp only [z, w]
    push_cast
    ring
  unfold quarterLevelGamma656 quarterMainEuler656 quarterMainXiLine656 quarterCosinePole
  dsimp only [z, w] at hw
  simp only [add_sub_cancel_right, hw, DirichletCharacter.LFunction_modOne_eq]
  change (_ * ∫ t, G t).re - (_ * ∫ t, E t).re = (_ * (∫ t, F t) + _ * (∫ t, P t) + _ * ∫ t, Q t).re
  have h₁ := MeasureTheory.integral_add ((hiF.add hiE).add hiP) hiQ
  have h₂ := MeasureTheory.integral_add (hiF.add hiE) hiP
  have h₃ := MeasureTheory.integral_add hiF hiE
  simp only [Pi.add_apply] at h₁ h₂ h₃
  simp only [hG, Pi.add_apply]
  rw [h₁, h₂, h₃]
  simp only [mul_add, Complex.add_re]
  ring

/-- At scale at least one, the principal forward and reflected terms cancel
the two Gamma integrals, leaving the xi line difference and the two residues. -/
theorem quarter_main_level_cancel_656 {x : ℝ} (hx : 1 ≤ x) :
    (quarterLevelGamma656 x).re - quarterMainEuler656 (1 : DirichletCharacter ℂ 1) x -
        (∑' n : ℕ, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re =
      (quarterMainXiLine656 (-9 / 16) x - quarterMainXiLine656 (9 / 16) x -
          quarterKernel656.function ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) -
          quarterKernel656.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re := by
  have hp := zero_lt_one.trans_le hx
  have hL := quarter_main_level_left_656 hp
  have hR := congrArg Complex.re (quarter_main_level_forward_656 hp)
  have ha :=
    congrArg Complex.re
      (quarter_main_xi_pole_656 hx (u := -1 / 2) (by norm_num only) (by norm_num only))
  have hb :=
    congrArg Complex.re
      (quarter_main_xi_pole_656 hx (u := 1 / 2) (by norm_num only) (by norm_num only))
  simp only [Complex.add_re, Complex.sub_re] at hL hR ha hb ⊢
  linarith only [hL, hR, ha, hb]

/-- Under RH and at scale at least one, the main left-minus-right xi contour
is the oscillating zeta zero sum. The main kernel has no extra residue. -/
theorem quarter_main_xi_zeros_656 (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    quarterMainXiLine656 (-9 / 16) x - quarterMainXiLine656 (9 / 16) x =
      ∑' ρ, quarterKernel656.zetaOscillatingZeroTerm x ρ := by
  have hd : quarterKernel656.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel656, LLS.PaperStatements.rationalPoleMellinKernel,
      min_eq_right (by norm_num only : (1 / 8 : ℝ) ≤ 3 / 20)]
  have he :=
    LLS.PaperStatements.MellinKernel.xiContourIdentity quarterKernel656 hRH (a := -9 / 16) (b :=
      9 / 16)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) hx
  simp only [pole_residue_zero_656, zero_sub, mul_comm _ Complex.I] at he
  rw [mul_assoc] at he
  have h := mul_left_cancel₀ Complex.I_ne_zero he
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hi : d * (2 * (Real.pi : ℂ)) = 1 := by
    dsimp only [d]
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div,
      inv_mul_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  have hh := congrArg (fun u : ℂ ↦ d * u) h
  rw [mul_sub, ← mul_assoc, hi, one_mul] at hh
  unfold quarterMainXiLine656
  linear_combination -hh

/-- At a shifted scale at least one, subtract the three level-one forward
sums from the main contours. The remainder consists of conductor and
reflected trace deficit terms, the xi zero sum, and the two residues. -/
theorem quarter_shifted_forward_diff_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r h : ℝ} (hr : 0 < r)
    (hx₁ : 1 ≤ r ^ 2 * Real.exp (-(21 / 8 + h))) :
    let x := r ^ 2 * Real.exp (-(21 / 8 + h))
    (contourRemainder656 a x).re + (contourRemainder656 b x).re + (contourRemainder656 c x).re -
        3 * (∑' n : ℕ, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re =
      (Real.log p + Real.log q + Real.log s) *
          Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) x⁻¹ +
        quarterAuxReflection656 (fun n ↦ 3 - ((a n).re + (b n).re + (c n).re)) r h +
        3 *
          ((∑' ρ, quarterKernel656.zetaOscillatingZeroTerm x ρ) -
              quarterKernel656.function ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) -
              quarterKernel656.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re := by
  intro x
  have hx : 1 ≤ x := hx₁
  have hR := quarter_shifted_remainders_656 ha hb hc hr hx₁
  have hL := quarter_main_level_cancel_656 hx
  rw [quarter_main_xi_zeros_656 hRH hx] at hL
  dsimp only [x] at hR hL ⊢
  linarith only [hR, hL]

/-- The real weighted zeta zero contribution of the seven shifted main kernels.
This is the common oscillatory term after cancellation of the even Gamma factors. -/
noncomputable def quarterMainXiMix656 (r : ℝ) : ℝ :=
  ∑ i,
    quarterAuxCoeff656 i *
      (∑' ρ,
          quarterKernel656.zetaOscillatingZeroTerm (r ^ 2 * Real.exp (-(quarterAuxFrequency656 i)))
            ρ).re

/-- Under RH, three primitive nonprincipal even quadratic characters with total
log conductor four times the radius have a common shifted contour expansion.
The positive half-point residue is already absorbed in the corrected forward sum. -/
theorem quarter_corrected_shift_mix_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r : ℝ} (hr : 322 ≤ r)
    (hL : Real.log p + Real.log q + Real.log s = 4 * r) :
    quarterShiftCorrected656 a r + quarterShiftCorrected656 b r + quarterShiftCorrected656 c r =
      quarterAuxTheta656 r + quarterAuxNegPole656 / r + 3 * quarterMainXiMix656 r +
        ∑ i,
          quarterAuxCoeff656 i *
            quarterAuxReflection656 (fun n ↦ 3 - ((a n).re + (b n).re + (c n).re)) r
              (quarterAuxShift656 i : ℝ) := by
  let x := fun i ↦ r ^ 2 * Real.exp (-(quarterAuxFrequency656 i))
  let P := fun (t : ℝ) (i : Fin 7) ↦ (quarterKernel656.function (t : ℂ) * (x i : ℂ) ^ (t : ℂ)).re
  let Z := fun i ↦ (∑' ρ, quarterKernel656.zetaOscillatingZeroTerm (x i) ρ).re
  let T := fun i ↦
    quarterAuxReflection656 (fun n ↦ 3 - ((a n).re + (b n).re + (c n).re)) r
      (quarterAuxShift656 i : ℝ)
  let A := fun i ↦ 4 * r * (quarterKernel656.transform (x i)⁻¹).re - 3 * P (-1 / 2) i
  let S := fun (i : Fin 7) ↦
    (∑' n, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (x i) n).re
  have hr₀ := (by norm_num only : (0 : ℝ) < 322).trans_le hr
  have hx (i : Fin 7) : 1 ≤ x i :=
    quarter_aux_scale_ge_one_656 (pow_le_pow_left₀ (by norm_num only) hr 2) i
  have hs (i : Fin 7) :
    (contourRemainder656 a (x i)).re - S i + P (1 / 2) i +
        ((contourRemainder656 b (x i)).re - S i + P (1 / 2) i) +
        ((contourRemainder656 c (x i)).re - S i + P (1 / 2) i) =
      A i + 3 * Z i + T i := by
    have h :=
      quarter_shifted_forward_diff_656 ha hb hc hRH hr₀ (h := (quarterAuxShift656 i : ℝ)) (hx i)
    have hp :
      (quarterKernel656.transform (x i)⁻¹).re =
        Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (x i)⁻¹ := by
      rw [quarterKernel656,
        LLS.PaperStatements.rationalPole_transform _ _ _ _
          (inv_pos.mpr (zero_lt_one.trans_le (hx i))),
        Complex.ofReal_re]
    simp only [hL, Complex.sub_re] at h
    dsimp only [A, P, Z, S, T, x, quarterAuxFrequency656] at h hp ⊢
    rw [hp]
    linear_combination h
  have hA : (∑ i, quarterAuxCoeff656 i * A i) = quarterAuxTheta656 r + quarterAuxNegPole656 / r :=
    quarter_aux_shift_signed_656 hr
  rw [← hA]
  unfold quarterShiftCorrected656 quarterShiftedForward656 quarterMainXiMix656
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hp : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [← hp]
  change
    quarterAuxCoeff656 i * ((contourRemainder656 a (x i)).re - S i) +
        quarterAuxCoeff656 i * P (1 / 2) i +
        (quarterAuxCoeff656 i * ((contourRemainder656 b (x i)).re - S i) +
          quarterAuxCoeff656 i * P (1 / 2) i) +
        (quarterAuxCoeff656 i * ((contourRemainder656 c (x i)).re - S i) +
          quarterAuxCoeff656 i * P (1 / 2) i) =
      quarterAuxCoeff656 i * A i + 3 * (quarterAuxCoeff656 i * Z i) + quarterAuxCoeff656 i * T i
  linear_combination quarterAuxCoeff656 i * hs i

/-- On radii 322 through 328, agreement on primes through the squared radius
bounds the reflected cost in the corrected forward sum. The remaining
oscillatory term is the explicit seven-frequency zeta zero contribution. -/
theorem quarter_corrected_shift_lower_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 322 328) (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    quarterAuxTheta656 r + quarterAuxNegPole656 / r + 3 * quarterMainXiMix656 r - 0.00327 ≤
      quarterShiftCorrected656 a r + quarterShiftCorrected656 b r +
        quarterShiftCorrected656 c r := by
  rw [quarter_corrected_shift_mix_656 ha hb hc hRH hr.1 hL]
  rw [sub_eq_add_neg]
  exact add_le_add_right (quarter_aux_character_reflect_656 hRH a b c hr ht hpa hpb hpc) _

end PseudoPrime.PrimeTestBounds.MillerRabin
