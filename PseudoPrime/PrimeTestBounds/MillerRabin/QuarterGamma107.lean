/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterContour600
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterContour600
import all PseudoPrime.Analysis.LogTaylorBounds

/-! # Gamma and even contour bounds on the section 107 interval -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first Gamma convolution exceeds 0.03411 on the whole section 107
shift interval. A single rectangle bounds the three signed moment terms. -/
theorem first_convolution_lower107 {z : ℝ} (hl : 13.41825 ≤ 17 / 18 * z)
    (hu : 17 / 18 * z ≤ 13.4984) :
    0.03411 < ∫ v in Set.Ioi (0 : ℝ), gammaDensity570 v * Real.exp (-(1 / 2) * |v - z|) := by
  let u : ℝ := 17 / 18 * z
  have h₀ : 0 ≤ u := by
    dsimp only [u]; linarith only [hl]
  have h₁ : 13.41825 ≤ u := by
    dsimp only [u]; linarith only [hl]
  have h₂ : u ≤ 13.4984 := by
    dsimp only [u]; linarith only [hu]
  have hp :=
    Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 27 / 25 - 9 / 17) h₀ h₂ 5
  have hq :=
    Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 9 / 17 + 27 / 25)
      (by norm_num only) h₁ 5
  have hA :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1270) (j := 10) (n := 24) (lo := 7.1467) (hi :=
        8) (by decide +kernel)).1
  have hB :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1966000) (j := 21) (n := 24) (lo := 14) (hi :=
        14.4916) (by decide +kernel)).2
  have hD :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2144500) (j := 21) (n := 24) (lo := 14.5783)
        (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hA hB hD
  have he :=
    (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 1270)).mp
      (show 9 / 17 * u ≤ Real.log 1270 by linarith only [h₂, hA])
  have hf :=
    (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 1966000)).mp
      (show Real.log 1966000 ≤ 27 / 25 * u by linarith only [h₁, hB])
  have hg :=
    (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 2144500)).mp
      (show 27 / 25 * u ≤ Real.log 2144500 by linarith only [h₂, hD])
  have ha := one_div_le_one_div_of_le (Real.exp_pos _) he
  have hb := one_div_le_one_div_of_le (by norm_num only) hf
  have hd := one_div_le_one_div_of_le (Real.exp_pos _) hg
  rw [one_div (Real.exp _), ← Real.exp_neg, ← neg_mul] at ha hb hd
  have hP :=
    Analysis.log_power_tail_poly_nonneg (by norm_num only : (0 : ℝ) < 27 / 25 - 9 / 17) h₀ 5
  have hQ :=
    Analysis.log_power_tail_poly_nonneg (by norm_num only : (0 : ℝ) < 9 / 17 + 27 / 25)
      (show 0 ≤ (13.41825 : ℝ) by norm_num only) 5
  have hm := mul_le_mul hb hp hP (by norm_num only)
  have hn := mul_le_mul hd hq hQ (Real.exp_pos _).le
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat] at hm hn
  rw [convolution_rescale_570, show (18 / 17 : ℝ) * (1 / 2) = 9 / 17 by norm_num only,
    quarter_gamma_convolution_expansion h₀ (by norm_num only) (by norm_num only),
    quarter_gamma_tail_poly_zero (by norm_num only)]
  dsimp only [u] at ha hm hn ⊢
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat]
  linarith only [ha, hm, hn]

private noncomputable def gammaFirst107 (x : ℝ) : ℝ :=
  quarterGammaConvolution x (9 / 17)

private noncomputable def gammaRight107 (x : ℝ) : ℝ :=
  ((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-(27 / 25) * x) *
    Analysis.logPowerTailPoly (9 / 17 + 27 / 25) 5 x

private theorem gammaFirst107_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt gammaFirst107 ((9 / 17) * (2 * gammaRight107 x - gammaFirst107 x)) x := by
  let a : ℝ := 27 / 25
  let c : ℝ := 9 / 17
  let K := a ^ 5 / 120
  let P := Analysis.logPowerTailPoly (a + c) 5
  let Q := Analysis.logPowerTailPoly (a - c) 5
  let f := fun y : ℝ ↦ K * Real.exp (-a * y) * (P y - Q y) + K * Real.exp (-c * y) * Q 0
  have hf : f =ᶠ[nhds x] gammaFirst107 := by
    filter_upwards [lt_mem_nhds hx] with y hy
    unfold gammaFirst107 f
    rw [quarter_gamma_convolution_expansion hy.le (by norm_num only) (by norm_num only)]
    unfold a c K P Q
    rw [add_comm (27 / 25 : ℝ) (9 / 17)]
  have hP := Analysis.log_power_tail_poly_deriv (show 0 < a + c by norm_num only [a, c]) 5 x
  have hQ := Analysis.log_power_tail_poly_deriv (show 0 < a - c by norm_num only [a, c]) 5 x
  have hA := (((hasDerivAt_id x).const_mul (-a)).exp).const_mul K
  have hC := (((hasDerivAt_id x).const_mul (-c)).exp).const_mul K
  have hd := ((hA.mul (hP.sub hQ)).add (hC.mul_const (Q 0))).congr_of_eventuallyEq hf.symm
  apply hd.congr_deriv
  rw [← hf.eq_of_nhds]
  unfold gammaRight107 f
  norm_num only [a, c, K, P, Q, Pi.sub_apply, id]
  ring

private theorem gammaRight107_cap {x : ℝ} (hx : x ∈ Set.Icc 13.41825 13.4984) :
    gammaRight107 x < 0.003 := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1966000) (j := 21) (n := 24) (lo := 14) (hi :=
        14.4916) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlog
  have hx0 : 0 ≤ x := by linarith only [hx.1]
  have he :=
    (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 1966000)).mp
      (show Real.log 1966000 ≤ (27 / 25) * x by linarith only [hlog, hx.1])
  have hE := (inv_le_inv₀ (Real.exp_pos _) (by norm_num only : (0 : ℝ) < 1966000)).mpr he
  rw [← Real.exp_neg, ← neg_mul] at hE
  have hP :=
    Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 9 / 17 + 27 / 25) hx0 hx.2 5
  have h :=
    mul_le_mul hE hP (Analysis.log_power_tail_poly_nonneg (by norm_num only) hx0 5)
      (by norm_num only)
  unfold gammaRight107
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat] at h ⊢
  linarith only [h]

private theorem gammaFirst107_antitone : AntitoneOn gammaFirst107 (Set.Icc 13.41825 13.4984) := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc 13.41825 13.4984) :=
    gammaFirst107_deriv (show 0 < x by linarith only [hx.1])
  apply
    antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
  intro x hx
  have hx' := interior_subset hx
  rw [(hd x hx').deriv]
  have hL :=
    first_convolution_lower107 (z := 18 / 17 * x) (by linarith only [hx'.1])
      (by linarith only [hx'.2])
  rw [convolution_rescale_570, show (18 / 17 : ℝ) * (1 / 2) = 9 / 17 by norm_num only,
    show (17 / 18 : ℝ) * (18 / 17 * x) = x by ring] at hL
  change 0.03411 < 18 / 17 * gammaFirst107 x at hL
  exact
    mul_nonpos_of_nonneg_of_nonpos (by norm_num only) (by linarith only [hL, gammaRight107_cap hx'])

private theorem gammaFirst107_endpoint : 0.035 ≤ (18 / 17) * gammaFirst107 13.4984 := by
  let x : ℝ := 13.4984
  have hA :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1270) (j := 10) (n := 24) (lo := 7.1467) (hi :=
        8) (by decide +kernel)).1
  have hB :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2144100) (j := 21) (n := 24) (lo := 14) (hi :=
        14.57824) (by decide +kernel)).2
  have hD :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2144500) (j := 21) (n := 24) (lo := 14.5783)
        (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hA hB hD
  have hInv {t N : ℝ} (hN : 0 < N) : N⁻¹ ≤ Real.exp (-t) ↔ t ≤ Real.log N := by
    rw [Real.exp_neg, inv_le_inv₀ hN (Real.exp_pos _), Real.le_log_iff_exp_le hN]
  have hExpA :=
    (hInv (t := 9 / 17 * x) (N := 1270) (by norm_num only)).mpr
      (by
        dsimp only [x]; linarith only [hA])
  have hExpB : Real.exp (-(27 / 25) * x) ≤ (2144100 : ℝ)⁻¹ := by
    rw [neg_mul, Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) (by norm_num only)]
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    dsimp only [x]
    linarith only [hB]
  have hExpD :=
    (hInv (t := 27 / 25 * x) (N := 2144500) (by norm_num only)).mpr
      (by
        dsimp only [x]; linarith only [hD])
  rw [← neg_mul] at hExpA hExpD
  change 0.035 ≤ (18 / 17) * quarterGammaConvolution x (9 / 17)
  rw [quarter_gamma_convolution_expansion (by norm_num only [x]) (by norm_num only)
      (by norm_num only),
    quarter_gamma_tail_poly_zero (by norm_num only)]
  norm_num only [x, Analysis.logPowerTailPoly, Nat.cast_ofNat] at *
  linarith only [hExpA, hExpB, hExpD]

/-- On the section 107 radius range, the shifted logarithm fits the
certified rectangle and the first Gamma recovery is at least 0.035. -/
theorem section107_first_gamma {r : ℝ} (hl : 300 ≤ r) (hu : r ≤ 313) :
    0.035 ≤
      ∫ v in Set.Ioi (0 : ℝ),
        gammaDensity570 v * Real.exp (-(1 / 2) * |v - (Real.log (r ^ 2) + 14 / 5)|) := by
  have h₁ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 32) (lo := 5703782 / 1000000)
        (hi := 6) (by decide +kernel)).1
  have h₂ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 313) (j := 8) (n := 32) (lo := 5) (hi :=
        5746204 / 1000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h₁ h₂
  rw [Real.log_pow, Nat.cast_ofNat]
  let x := 17 / 18 * (2 * Real.log r + 14 / 5)
  have hx : x ∈ Set.Icc 13.41825 13.4984 := by
    dsimp only [x]
    exact
      ⟨by linarith only [h₁, Real.log_le_log (by norm_num only) hl], by
        linarith only [h₂, Real.log_le_log (by linarith only [hl]) hu]⟩
  rw [convolution_rescale_570, show (18 / 17 : ℝ) * (1 / 2) = 9 / 17 by norm_num only]
  change 0.035 ≤ 18 / 17 * gammaFirst107 x
  exact
    gammaFirst107_endpoint.trans
      (mul_le_mul_of_nonneg_left (gammaFirst107_antitone hx ⟨by norm_num only, le_rfl⟩ hx.2)
        (by norm_num only))

/-- On the section 107 radius interval, an even inverse-nonprincipal
character has the contour bound with the first Gamma recovery of 0.035
and the exact local density term. -/
theorem section107_even_contour_upper {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hi : χ⁻¹ ≠ 1)
    (he : χ.Even) {r : ℝ} (hr : r ∈ Set.Icc 300 313) :
    contourNonEuler570 χ (r ^ 2) ≤
      Real.log q * Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (r ^ 2)⁻¹ - 0.035 -
        (4 / 3 : ℝ) * gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
  have hp : 0 < r := by linarith only [hr.1]
  have hx := sq_pos_of_pos hp
  have hx1 := one_le_pow₀ (show 1 ≤ r by linarith only [hr.1]) (n := 2)
  have hz : 13 ≤ Real.log (r ^ 2) + 14 / 5 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 20) (lo := 227 / 40) (hi :=
          6) (by decide +kernel)).1
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h, Real.log_le_log (by norm_num only) hr.1]
  have hn := central_gamma_convolution_upper χ he hx hz
  rw [← central_gamma_pair_eq_570 χ he hx, ← right_gamma_eq_central_570 χ hx, ←
    reflected_arch_eq_central_570 _ hi hx1, Complex.add_re] at hn
  unfold contourNonEuler570
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _),
    ← Complex.ofReal_mul, Complex.ofReal_re]
  linarith only [hn, section107_first_gamma hr.1 hr.2]

/-- Summing the even contour estimates over the three pair characters on
the section 107 interval leaves the exact local term for cancellation
with the principal boundary. -/
theorem section107_triple_contour_upper {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) (ea : a.Even) (eb : b.Even) (ec : c.Even) {r : ℝ}
    (hr : r ∈ Set.Icc 300 313) (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) :
    contourNonEuler570 a (r ^ 2) + contourNonEuler570 b (r ^ 2) + contourNonEuler570 c (r ^ 2) ≤
      section99Conductor r - 3 * 0.035 - 4 * quarterWeight570 (r ^ 2) 1 := by
  have h1 : 1 ≤ r := by linarith only [hr.1]
  have hpos : 0 ≤ gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
    unfold gammaDensity570
    split_ifs
    · positivity
    · exact le_rfl
  have hm := mul_le_mul_of_nonneg_right hlog hpos
  have ha := section107_even_contour_upper a ia ea hr
  have hb := section107_even_contour_upper b ib eb hr
  have hc := section107_even_contour_upper c ic ec hr
  rw [section99_profile_eq_density h1] at ha hb hc
  rw [section99_conductor_eq_density h1, section99_weight_eq_density h1]
  linarith only [ha, hb, hc, hm]

/-- Under GRH, a lower bound for the pair-character prime sums gives an
upper bound for their signed zero and reflected terms on the section 107 interval. -/
theorem section107_triple_signed_upper {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ea : a.Even) (eb : b.Even) (ec : c.Even) {r A : ℝ} (hr : r ∈ Set.Icc 300 313)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r)
    (hA :
      A ≤
        (∑' n : ℕ, quarterKernel570.summand a (r ^ 2) n).re +
          (∑' n : ℕ, quarterKernel570.summand b (r ^ 2) n).re +
          (∑' n : ℕ, quarterKernel570.summand c (r ^ 2) n).re) :
    A +
        (reflectedIntegral570 a (r ^ 2) + reflectedIntegral570 b (r ^ 2) +
          reflectedIntegral570 c (r ^ 2)) +
        ((∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm a (r ^ 2) ρ).re +
          (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm b (r ^ 2) ρ).re +
          (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm c (r ^ 2) ρ).re) ≤
      section99Conductor r - 3 * 0.035 - 4 * quarterWeight570 (r ^ 2) 1 := by
  have hx := one_le_pow₀ (show 1 ≤ r by linarith only [hr.1]) (n := 2)
  have ia := inv_ne_one.mpr na
  have ib := inv_ne_one.mpr nb
  have ic := inv_ne_one.mpr nc
  rw [section99_prime_sum_eq hp hG pa na ia hx, section99_prime_sum_eq hq hG pb nb ib hx,
    section99_prime_sum_eq hs hG pc nc ic hx] at hA
  linarith only [hA, section107_triple_contour_upper a b c ia ib ic ea eb ec hr hlog]

end PseudoPrime.PrimeTestBounds.MillerRabin
