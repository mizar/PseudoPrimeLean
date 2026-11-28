/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSeries656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosinePoles644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosine656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosinePoles644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSeries656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxEuler656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta

/-! # Decomposition of the section 132 cosine contour -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The cosine kernel has no poles in the comparison strip, so moving a
simple xi pole between the vertical lines adds its weighted residue. -/
theorem quarter_cosine_residue_656 {x p : ℝ} (hx : 1 ≤ x) (hlP : -9 / 16 < p) (huP : p < 9 / 16) :
    quarterCosinePole quarterSymmetricMellin656 (9 / 16) p x -
        quarterCosinePole quarterSymmetricMellin656 (-9 / 16) p x =
      quarterSymmetricKernel656 (p : ℂ) * (x : ℂ) ^ (p : ℂ) := by
  refine quarter_cosine_pole_diff quarterSymmetricMellin656 rfl ?_ hx hlP huP
  let U := Complex.re ⁻¹' Set.Ioo (-(3 / 4 : ℝ)) (3 / 4)
  have hU : IsOpen U := isOpen_Ioo.preimage Complex.continuous_re
  have hD : DifferentiableOn ℂ quarterSymmetricKernel656 U := fun z hz ↦
    (symmetric_diff hz.1.le hz.2.le).differentiableWithinAt
  exact fun z hl hu ↦ (hD.analyticOnNhd hU) z ⟨by linarith only [hl], by linarith only [hu]⟩

/-- At scale at least one, shifting both xi poles from the right comparison
line to the left contributes the sum of their two weighted residues. -/
theorem quarter_cosine_xi_poles_656 {x : ℝ} (hx : 1 ≤ x) :
    let P := quarterCosinePole quarterSymmetricMellin656
    P (9 / 16) (1 / 2) x + P (9 / 16) (-1 / 2) x -
        (P (-9 / 16) (1 / 2) x + P (-9 / 16) (-1 / 2) x) =
      quarterSymmetricKernel656 ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) +
        quarterSymmetricKernel656 ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) := by
  dsimp only
  rw [add_sub_add_comm, quarter_cosine_residue_656 hx (by norm_num only) (by norm_num only),
    quarter_cosine_residue_656 hx (by norm_num only) (by norm_num only)]

/-- The left comparison integral splits into the conductor, the reflected
Euler difference, and the two simple-pole integrals at positive scale. -/
theorem quarter_cosine_left_split_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := fun t : ℝ ↦ -(s t) + 1 / 2
    let W := fun t : ℝ ↦ quarterSymmetricKernel656 (s t) * (x : ℂ) ^ s t
    let C := fun t : ℝ ↦ Complex.log q * W t
    let A := fun {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) (t : ℝ) ↦
      -logDeriv ψ.LFunction (w t) * W t
    let P := fun (p t : ℝ) ↦ (1 / (s t - (p : ℂ))) * W t
    (∫ t : ℝ,
        (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) - 1 / w t -
            1 / (w t - 1)) *
          W t) =
      (∫ t : ℝ, C t) + (∫ t : ℝ, A (1 : DirichletCharacter ℂ 1) t - A χ t) +
        (∫ t : ℝ, P (1 / 2) t) +
        ∫ t : ℝ, P (-1 / 2) t := by
  intro s w W C A P
  have hW := symmetric_line (c := -9 / 16) (by norm_num only) (by norm_num only)
  have hc : Continuous (fun t : ℝ ↦ (x : ℂ) ^ s t) :=
    (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hi : MeasureTheory.Integrable W := by
    apply hW.mul_bdd (c := x ^ (-9 / 16 : ℝ)) hc.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, line_re]
  have hC : MeasureTheory.Integrable C := hi.const_mul _
  have hA :=
    (quarter_reflected_integrable_656 (1 : DirichletCharacter ℂ 1) hx).sub
      (quarter_reflected_integrable_656 χ hx)
  have hP (p : ℝ) (hne : (-9 / 16 : ℝ) ≠ p) : MeasureTheory.Integrable (P p) := by
    simpa only [P, W, s, mul_assoc, quarterSymmetricMellin656] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line quarterSymmetricMellin656
        (by
          change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
        (by
          change (-9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) hne hx
  have hp := hP (1 / 2) (by norm_num only)
  have hm := hP (-1 / 2) (by norm_num only)
  let B := fun t : ℝ ↦ A (1 : DirichletCharacter ℂ 1) t - A χ t
  change MeasureTheory.Integrable B at hA
  have he (t : ℝ) :=
    twoShift_left_pole_split (s t) (W t) (Complex.log q) (logDeriv χ.LFunction (w t))
      (logDeriv riemannZeta (w t))
  calc
    _ = ∫ t : ℝ, ((C + B) + P (1 / 2) + P (-1 / 2)) t := by
      apply MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
      simpa only [C, B, A, P, Pi.add_apply, DirichletCharacter.LFunction_modOne_eq] using he t
    _ = _ := by
      calc
        _ = _ := MeasureTheory.integral_add ((hC.add hA).add hp) hm
        _ = _ := congrArg (· + _) (MeasureTheory.integral_add (hC.add hA) hp)
        _ = _ := congrArg (fun z ↦ z + _ + _) (MeasureTheory.integral_add hC hA)

/-- The single-frequency difference after both gamma cancellations. The reflected
ordinary logarithmic derivatives are evaluated to the right of one, so their
Dirichlet series converge absolutely. -/
noncomputable def quarterCosineEvenDiff656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) :
    ℝ :=
  let W := fun s : ℂ ↦ quarterSymmetricKernel656 s * ((Real.exp b : ℝ) : ℂ) ^ s
  let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  (d *
            ∫ t : ℝ,
              (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) - 1 / w t -
                  1 / (w t - 1)) *
                W (l t)).re -
        (d * ∫ t : ℝ, (1 / (r t - ((-1 / 2 : ℝ) : ℂ))) * W (r t)).re -
        (d * ∫ t : ℝ, (1 / (r t - ((1 / 2 : ℝ) : ℂ))) * W (r t)).re +
      (∑' n, quarterSymmetricMellin656.summand (1 : DirichletCharacter ℂ 1) (Real.exp b) n).re -
    (∑' n, quarterSymmetricMellin656.summand χ (Real.exp b) n).re

/-- For a nonnegative frequency the two right-line pole terms in the even
comparison move to the left line, each subtracting its weighted residue. -/
theorem quarter_cosine_even_left_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 0 ≤ b) :
    let x := Real.exp b
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
    let H := fun s : ℂ ↦ quarterSymmetricKernel656 s * (x : ℂ) ^ s
    let S := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      (∑' n, quarterSymmetricMellin656.summand ψ x n).re
    quarterCosineEvenDiff656 χ b =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                ∫ t : ℝ,
                  (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) -
                      1 / w t -
                      1 / (w t - 1)) *
                    H (l t)).re -
            (quarterCosinePole quarterSymmetricMellin656 (-9 / 16) (-1 / 2) x).re -
            (quarterCosinePole quarterSymmetricMellin656 (-9 / 16) (1 / 2) x).re -
            (H ((-1 / 2 : ℝ) : ℂ)).re -
            (H ((1 / 2 : ℝ) : ℂ)).re +
          S (1 : DirichletCharacter ℂ 1) -
        S χ := by
  intro x l w H S
  have hx : 1 ≤ x := Real.one_le_exp hb
  have hp (p : ℝ) (hl : -9 / 16 < p) (hu : p < 9 / 16) :=
    congrArg Complex.re (quarter_cosine_residue_656 hx hl hu)
  have hm := hp (-1 / 2) (by norm_num only) (by norm_num only)
  have hpos := hp (1 / 2) (by norm_num only) (by norm_num only)
  simp only [Complex.sub_re] at hm hpos
  unfold quarterCosineEvenDiff656
  dsimp only
  have hfun : quarterSymmetricMellin656.function = quarterSymmetricKernel656 := rfl
  simp only [quarterCosinePole, hfun] at hm hpos ⊢
  dsimp only [H, S, w, l, x] at *
  linarith only [hm, hpos]

/-- For a nonnegative frequency the contour comparison consists of the conductor,
the reflected and forward Euler differences, and the two weighted residues. -/
theorem quarter_cosine_even_euler_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 0 ≤ b) :
    let x := Real.exp b
    let H := fun p : ℝ ↦ (quarterSymmetricKernel656 (p : ℂ) * (x : ℂ) ^ (p : ℂ)).re
    let R := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      ∑' n : ℕ,
        (ψ n).re *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile656 (n * x))
    let S := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      (∑' n, quarterSymmetricMellin656.summand ψ x n).re
    let ψ := (1 : DirichletCharacter ℂ 1)
    quarterCosineEvenDiff656 χ b =
      (Complex.log q * (quarterSymmetricProfile656 x⁻¹ : ℂ)).re + (R ψ - R χ) - H (-1 / 2) -
            H (1 / 2) +
          S ψ -
        S χ := by
  intro x H R S ψ
  have hx : 0 < x := Real.exp_pos b
  have hw (t : ℝ) :
    ((17 / 16 : ℝ) : ℂ) - Complex.I * t = -(((-9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2 := by
    push_cast
    ring
  have h := quarter_cosine_even_left_656 χ hb
  dsimp only at h
  simp_rw [hw] at h
  have hs := quarter_cosine_left_split_656 χ hx
  dsimp only at hs
  rw [hs] at h
  simp only [mul_add, Complex.add_re] at h
  have hc := quarter_left_conductor_656 q hx
  have ha := quarter_reflected_euler_difference_656 χ hx
  dsimp only at hc ha
  rw [hc, ha] at h
  unfold quarterCosinePole at h
  dsimp only [quarterSymmetricMellin656] at h
  dsimp only [x, H, R, S, ψ, quarterSymmetricMellin656] at *
  linarith only [h]

/-- The real normalized xi contour difference at frequency b, on the same
left and right lines used for the three pair characters. -/
noncomputable def quarterCosineXi656 (b : ℝ) : ℝ :=
  let F := fun s : ℂ ↦
    -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s + 1 / 2) *
      (quarterSymmetricKernel656 s * ((Real.exp b : ℝ) : ℂ) ^ s)
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
        ∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + Complex.I * t))).re

/-- The left character-minus-xi integrals and the two right simple-pole
integrals remaining after cancellation of the common even gamma factor. -/
noncomputable def quarterCosineLeftDiff656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) :
    ℝ :=
  let W := fun s : ℂ ↦ quarterSymmetricKernel656 s * ((Real.exp b : ℝ) : ℂ) ^ s
  let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  (d * ∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W (l t)).re -
    (d * ∫ t : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l t + 1 / 2) * W (l t)).re -
    (d * ∫ t : ℝ, (1 / (r t - ((-1 / 2 : ℝ) : ℂ))) * W (r t)).re -
    (d * ∫ t : ℝ, (1 / (r t - ((1 / 2 : ℝ) : ℂ))) * W (r t)).re

/-- For an even character at any real frequency the right gamma integral cancels
in the character-minus-xi contour difference. The arithmetic contribution is the
principal forward sum less the character forward sum. -/
theorem quarter_cosine_gamma_cancel_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (he : χ.Even) (b : ℝ) :
    quarterCosineContour656 χ b - quarterCosineXi656 b =
      quarterCosineLeftDiff656 χ b +
          (∑' n, quarterSymmetricMellin656.summand (1 : DirichletCharacter ℂ 1) (Real.exp b) n).re -
        (∑' n, quarterSymmetricMellin656.summand χ (Real.exp b) n).re := by
  have hg : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  have h := twoShift_level_one_forward quarterSymmetricMellin656 rfl (Real.exp_pos b)
  dsimp only at h
  have hk : quarterSymmetricMellin656.function = quarterSymmetricKernel656 := rfl
  rw [show quarterSymmetricMellin656.function = quarterSymmetricKernel656 from hk] at h
  unfold quarterCosineContour656 quarterCosineXi656 quarterCosineLeftDiff656
  dsimp only
  rw [hg, h]
  simp only [mul_sub, mul_add, Complex.sub_re, Complex.add_re]
  ring

/-- For even self-inverse primitive nonprincipal characters, the complete contour
difference at any frequency is the ordinary Euler, conductor and pole expression. -/
theorem quarter_cosine_even_diff_656 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) (b : ℝ) :
    quarterCosineContour656 χ b - quarterCosineXi656 b = quarterCosineEvenDiff656 χ b := by
  have hF :=
    LLS.PaperStatements.MellinKernel.integrable_completed_left_line quarterSymmetricMellin656 hp hn
      (inv_ne_one.mpr hn) (c := -9 / 16) (x := Real.exp b)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) (Real.exp_pos b)
  have hG :=
    LLS.PaperStatements.MellinKernel.integrable_xi_left_line quarterSymmetricMellin656 (c :=
      -9 / 16) (x := Real.exp b)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) (Real.exp_pos b)
  let W := fun t : ℝ ↦
    quarterSymmetricKernel656 (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      ((Real.exp b : ℝ) : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  change MeasureTheory.Integrable (fun t : ℝ ↦ -logDeriv χ.completedLFunction (s t) * W t) at hF
  change
    MeasureTheory.Integrable
      (fun t : ℝ ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t) * W t) at hG
  have h := MeasureTheory.integral_sub hF hG
  have ht (t : ℝ) := congrArg (fun z : ℂ ↦ z * W t) (twoShift_left_log_difference hp hn hi he t)
  have h' :
    (∫ t : ℝ,
        (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) - 1 / w t -
            1 / (w t - 1)) *
          W t) =
      _ :=
    Eq.trans
      (MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun t ↦ by
          simpa only [s, w, add_mul, neg_mul, sub_neg_eq_add] using (ht t).symm))
      h
  rw [quarter_cosine_gamma_cancel_656 χ he b]
  unfold quarterCosineLeftDiff656 quarterCosineEvenDiff656
  dsimp only
  rw [h', mul_sub, Complex.sub_re]

/-- The paired Euler contribution is the difference between the principal
and character sums at the two reciprocal scales. -/
noncomputable def quarterPairedEuler656 {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℝ) : ℝ :=
  let y := Real.exp b
  (quarterSymmetricSum656 (1 : DirichletCharacter ℂ 1) y - quarterSymmetricSum656 χ y) +
    (quarterSymmetricSum656 (1 : DirichletCharacter ℂ 1) y⁻¹ - quarterSymmetricSum656 χ y⁻¹)

/-- For an even primitive self-inverse nonprincipal character, the cosine
contour is the common xi contour plus its conductor and paired Euler difference,
minus the two weighted residues. -/
theorem quarter_cosine_decompose_656 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) {b : ℝ} (hb : 0 ≤ b) :
    let H := fun p : ℝ ↦ (quarterSymmetricKernel656 (p : ℂ) * (Real.exp b : ℂ) ^ (p : ℂ)).re
    quarterCosineContour656 χ b =
      quarterCosineXi656 b + Real.log q * quarterSymmetricProfile656 (Real.exp b)⁻¹ +
          quarterPairedEuler656 χ b -
        H (-1 / 2) -
        H (1 / 2) := by
  intro H
  have hs {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) :
    (∑' n, quarterSymmetricMellin656.summand ψ (Real.exp b) n).re =
      quarterSymmetricSum656 ψ (Real.exp b) := by
    rw [Complex.re_tsum
        (LLS.PaperStatements.MellinKernel.summable_summand quarterSymmetricMellin656 ψ
          (Real.exp_pos b))]
    exact tsum_congr (quarter_symmetric_summand_656 ψ (Real.exp_pos b))
  have h := quarter_cosine_even_euler_656 χ hb
  dsimp only at h
  rw [hs, hs, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg q), ←
    Complex.ofReal_mul, Complex.ofReal_re] at h
  have hd := quarter_cosine_even_diff_656 hp hn hi he b
  simp only [quarterPairedEuler656, quarterSymmetricSum656, div_inv_eq_mul, H] at h ⊢
  linarith only [h, hd]

/-- At a signed frequency, the part of the three cosine contours independent
of the Euler trace is the common xi term, both residues and the conductor. -/
noncomputable def quarterCosineCore656 (L t : ℝ) : ℝ :=
  let y := Real.exp |t|
  let H := fun u : ℝ ↦ (quarterSymmetricKernel656 (u : ℂ) * (y : ℂ) ^ (u : ℂ)).re
  3 * (quarterCosineXi656 |t| - H (-1 / 2) - H (1 / 2)) + L * quarterSymmetricProfile656 y⁻¹

/-- Three even primitive self-inverse characters with prime agreement
have a single paired Euler tail in the decomposition at each frequency. -/
theorem quarter_three_cosine_split_656 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) {X : ℝ} (hX : 0 ≤ X) (t : ℝ)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → c n = 1) :
    quarterCosineContour656 a |t| + quarterCosineContour656 b |t| + quarterCosineContour656 c |t| =
      quarterCosineCore656 (Real.log p + Real.log q + Real.log r) t +
        quarterCosineTail656 a b c X t := by
  rw [quarter_cosine_decompose_656 ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 (abs_nonneg t),
    quarter_cosine_decompose_656 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 (abs_nonneg t),
    quarter_cosine_decompose_656 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 (abs_nonneg t)]
  have h := quarter_cosine_tail_deficits_656 a b c hX t hpa hpb hpc
  dsimp only [quarterCosineCore656, quarterPairedEuler656] at h ⊢
  linear_combination -h

/-- The seven-frequency combination of the three cosine contours has
Euler cost bounded by the same numerical Abel estimate on both intervals. -/
theorem quarter_cosine_euler_cap_656 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {X : ℝ}
    (hX : (322 : ℝ) ^ 2 ≤ X) (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → c n = 1) :
    quarterAuxMix656
        (fun t ↦
          quarterCosineContour656 a |t| + quarterCosineContour656 b |t| +
            quarterCosineContour656 c |t|) ≤
      quarterAuxMix656 (quarterCosineCore656 (Real.log p + Real.log q + Real.log r)) +
        4 * 0.038175553 := by
  have hX₀ := (by norm_num only : (0 : ℝ) ≤ 322 ^ 2).trans hX
  simp only [quarter_three_cosine_split_656 ha hb hc hX₀ _ hpa hpb hpc, aux_mix_add_656]
  exact add_le_add_right (quarter_cosine_tail_cap_656 a b c hRH hX ht) _

/-- The signed shifted remainder after replacing the shifted prime sums
by their common level-one values. -/
noncomputable def quarterShiftedForward656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) :
    ℝ :=
  ∑ i,
    quarterAuxCoeff656 i *
      ((contourRemainder656 χ (X * Real.exp (-(quarterAuxFrequency656 i)))).re -
        (∑' n,
            quarterKernel656.summand (1 : DirichletCharacter ℂ 1)
              (X * Real.exp (-(quarterAuxFrequency656 i))) n).re)

private theorem quarter_single_core_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) {X : ℝ} (hX : (322 : ℝ) ^ 2 ≤ X)
    (hpass : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    (∑' n, quarterKernel656.summand χ X n).re + quarterShiftedForward656 χ X ≤
      quarterCosineContour656 χ 0 + (contourRemainder656 χ X).re +
        quarterAuxMix656 (fun t ↦ quarterCosineContour656 χ |t|) := by
  have h := quarter_seven_contour_656 hq hG hp hn hX hpass
  dsimp only at h
  have hf (i : Fin 7) : |quarterAuxFrequency656 i| = quarterAuxFrequency656 i :=
    abs_of_nonneg ((by norm_num only : (0 : ℝ) ≤ 21 / 8).trans (quarter_aux_frequency_ge_656 i))
  unfold quarterShiftedForward656 quarterAuxMix656
  simp only [hf]
  simp only [mul_add, Finset.sum_add_distrib] at h
  linarith only [h]

/-- The combined forward inequality now includes the certified Euler cost.
The remaining terms are the shared xi, conductor, residues and shifted main
remainders. The same inequality serves both section 132 intervals. -/
theorem quarter_three_forward_euler_656 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : (322 : ℝ) ^ 2 ≤ X)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → c n = 1) :
    (∑' n, quarterKernel656.summand a X n).re + (∑' n, quarterKernel656.summand b X n).re +
        (∑' n, quarterKernel656.summand c X n).re +
        (quarterShiftedForward656 a X + quarterShiftedForward656 b X +
          quarterShiftedForward656 c X) ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a X).re + (contourRemainder656 b X).re +
          (contourRemainder656 c X).re) +
        quarterAuxMix656 (quarterCosineCore656 (Real.log p + Real.log q + Real.log r)) +
        4 * 0.038175553 := by
  have h₁ := quarter_single_core_bound hp hG ha.1 ha.2.1 hX hpa
  have h₂ := quarter_single_core_bound hq hG hb.1 hb.2.1 hX hpb
  have h₃ := quarter_single_core_bound hr hG hc.1 hc.2.1 hX hpc
  have he := quarter_cosine_euler_cap_656 ha hb hc hG.riemann hX ht hpa hpb hpc
  simp only [aux_mix_add_656] at he
  linarith only [h₁, h₂, h₃, he]

end PseudoPrime.PrimeTestBounds.MillerRabin
