/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.MellinKernelZeta
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosinePoles644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineTailRows644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosine644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosinePoles644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSeries644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineTailRows644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaMass644

/-! # Decomposition of the section 122 cosine contour -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The left comparison integral splits into the conductor, the reflected
Euler difference, and the two simple-pole integrals at positive scale. -/
theorem quarter_cosine_left_split_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := fun t : ℝ ↦ -(s t) + 1 / 2
    let W := fun t : ℝ ↦ quarterSymmetricKernel644 (s t) * (x : ℂ) ^ s t
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
    (quarter_reflected_integrable_644 (1 : DirichletCharacter ℂ 1) hx).sub
      (quarter_reflected_integrable_644 χ hx)
  have hP (p : ℝ) (hne : (-9 / 16 : ℝ) ≠ p) : MeasureTheory.Integrable (P p) := by
    simpa only [P, W, s, mul_assoc, quarterSymmetricMellin644] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line quarterSymmetricMellin644
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
noncomputable def quarterCosineEvenDiff644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) :
    ℝ :=
  let W := fun s : ℂ ↦ quarterSymmetricKernel644 s * ((Real.exp b : ℝ) : ℂ) ^ s
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
      (∑' n, quarterSymmetricMellin644.summand (1 : DirichletCharacter ℂ 1) (Real.exp b) n).re -
    (∑' n, quarterSymmetricMellin644.summand χ (Real.exp b) n).re

/-- For a nonnegative frequency the two right-line pole terms in the even
comparison move to the left line, each subtracting its weighted residue. -/
theorem quarter_cosine_even_left_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 0 ≤ b) :
    let x := Real.exp b
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
    let H := fun s : ℂ ↦ quarterSymmetricKernel644 s * (x : ℂ) ^ s
    let S := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      (∑' n, quarterSymmetricMellin644.summand ψ x n).re
    quarterCosineEvenDiff644 χ b =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                ∫ t : ℝ,
                  (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) -
                      1 / w t -
                      1 / (w t - 1)) *
                    H (l t)).re -
            (quarterCosinePole quarterSymmetricMellin644 (-9 / 16) (-1 / 2) x).re -
            (quarterCosinePole quarterSymmetricMellin644 (-9 / 16) (1 / 2) x).re -
            (H ((-1 / 2 : ℝ) : ℂ)).re -
            (H ((1 / 2 : ℝ) : ℂ)).re +
          S (1 : DirichletCharacter ℂ 1) -
        S χ := by
  intro x l w H S
  have hx : 1 ≤ x := Real.one_le_exp hb
  have hp (p : ℝ) (hl : -9 / 16 < p) (hu : p < 9 / 16) :=
    congrArg Complex.re (quarter_cosine_residue_644 hx hl hu)
  have hm := hp (-1 / 2) (by norm_num only) (by norm_num only)
  have hpos := hp (1 / 2) (by norm_num only) (by norm_num only)
  simp only [Complex.sub_re] at hm hpos
  unfold quarterCosineEvenDiff644
  dsimp only
  have hfun : quarterSymmetricMellin644.function = quarterSymmetricKernel644 := rfl
  simp only [quarterCosinePole, hfun] at hm hpos ⊢
  dsimp only [H, S, w, l, x] at *
  linarith only [hm, hpos]

/-- For a nonnegative frequency the contour comparison consists of the conductor,
the reflected and forward Euler differences, and the two weighted residues. -/
theorem quarter_cosine_even_euler_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 0 ≤ b) :
    let x := Real.exp b
    let H := fun p : ℝ ↦ (quarterSymmetricKernel644 (p : ℂ) * (x : ℂ) ^ (p : ℂ)).re
    let R := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      ∑' n : ℕ,
        (ψ n).re *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile644 (n * x))
    let S := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      (∑' n, quarterSymmetricMellin644.summand ψ x n).re
    let ψ := (1 : DirichletCharacter ℂ 1)
    quarterCosineEvenDiff644 χ b =
      (Complex.log q * (quarterSymmetricProfile644 x⁻¹ : ℂ)).re + (R ψ - R χ) - H (-1 / 2) -
            H (1 / 2) +
          S ψ -
        S χ := by
  intro x H R S ψ
  have hx : 0 < x := Real.exp_pos b
  have hw (t : ℝ) :
    ((17 / 16 : ℝ) : ℂ) - Complex.I * t = -(((-9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2 := by
    push_cast
    ring
  have h := quarter_cosine_even_left_644 χ hb
  dsimp only at h
  simp_rw [hw] at h
  have hs := quarter_cosine_left_split_644 χ hx
  dsimp only at hs
  rw [hs] at h
  simp only [mul_add, Complex.add_re] at h
  have hc := quarter_left_conductor_644 q hx
  have ha := quarter_reflected_euler_difference_644 χ hx
  dsimp only at hc ha
  rw [hc, ha] at h
  unfold quarterCosinePole at h
  dsimp only [quarterSymmetricMellin644] at h
  dsimp only [x, H, R, S, ψ, quarterSymmetricMellin644] at *
  linarith only [h]

/-- The real normalized xi contour difference at frequency b, on the same
left and right lines used for the three pair characters. -/
noncomputable def quarterCosineXi644 (b : ℝ) : ℝ :=
  let F := fun s : ℂ ↦
    -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s + 1 / 2) *
      (quarterSymmetricKernel644 s * ((Real.exp b : ℝ) : ℂ) ^ s)
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
        ∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + Complex.I * t))).re

/-- The left character-minus-xi integrals and the two right simple-pole
integrals remaining after cancellation of the common even gamma factor. -/
noncomputable def quarterCosineLeftDiff644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) :
    ℝ :=
  let W := fun s : ℂ ↦ quarterSymmetricKernel644 s * ((Real.exp b : ℝ) : ℂ) ^ s
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
theorem quarter_cosine_gamma_cancel_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (he : χ.Even) (b : ℝ) :
    quarterCosineContour644 χ b - quarterCosineXi644 b =
      quarterCosineLeftDiff644 χ b +
          (∑' n, quarterSymmetricMellin644.summand (1 : DirichletCharacter ℂ 1) (Real.exp b) n).re -
        (∑' n, quarterSymmetricMellin644.summand χ (Real.exp b) n).re := by
  have hg : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  have h := twoShift_level_one_forward quarterSymmetricMellin644 rfl (Real.exp_pos b)
  dsimp only at h
  have hk : quarterSymmetricMellin644.function = quarterSymmetricKernel644 := rfl
  rw [show quarterSymmetricMellin644.function = quarterSymmetricKernel644 from hk] at h
  unfold quarterCosineContour644 quarterCosineXi644 quarterCosineLeftDiff644
  dsimp only
  rw [hg, h]
  simp only [mul_sub, mul_add, Complex.sub_re, Complex.add_re]
  ring

/-- For even self-inverse primitive nonprincipal characters, the complete contour
difference at any frequency is the ordinary Euler, conductor and pole expression. -/
theorem quarter_cosine_even_diff_644 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) (b : ℝ) :
    quarterCosineContour644 χ b - quarterCosineXi644 b = quarterCosineEvenDiff644 χ b := by
  have hF :=
    LLS.PaperStatements.MellinKernel.integrable_completed_left_line quarterSymmetricMellin644 hp hn
      (inv_ne_one.mpr hn) (c := -9 / 16) (x := Real.exp b)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) (Real.exp_pos b)
  have hG :=
    LLS.PaperStatements.MellinKernel.integrable_xi_left_line quarterSymmetricMellin644 (c :=
      -9 / 16) (x := Real.exp b)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) (Real.exp_pos b)
  let W := fun t : ℝ ↦
    quarterSymmetricKernel644 (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
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
  rw [quarter_cosine_gamma_cancel_644 χ he b]
  unfold quarterCosineLeftDiff644 quarterCosineEvenDiff644
  dsimp only
  rw [h', mul_sub, Complex.sub_re]

/-- For an even primitive self-inverse nonprincipal character, the cosine
contour is the common xi contour plus its conductor and paired Euler difference,
minus the two weighted residues. -/
theorem quarter_cosine_decompose_644 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) {b : ℝ} (hb : 0 ≤ b) :
    let H := fun p : ℝ ↦ (quarterSymmetricKernel644 (p : ℂ) * (Real.exp b : ℂ) ^ (p : ℂ)).re
    quarterCosineContour644 χ b =
      quarterCosineXi644 b + Real.log q * threeShiftG122 b / 4 + quarterPairedEuler644 χ b -
        H (-1 / 2) -
        H (1 / 2) := by
  intro H
  have hs {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) :
    (∑' n, quarterSymmetricMellin644.summand ψ (Real.exp b) n).re =
      quarterSymmetricSum644 ψ (Real.exp b) := by
    rw [Complex.re_tsum
        (LLS.PaperStatements.MellinKernel.summable_summand quarterSymmetricMellin644 ψ
          (Real.exp_pos b))]
    exact tsum_congr (quarter_symmetric_summand_644 ψ (Real.exp_pos b))
  have h := quarter_cosine_even_euler_644 χ hb
  dsimp only at h
  rw [hs, hs, quarter_cosine_conductor_644 q hb] at h
  have hd := quarter_cosine_even_diff_644 hp hn hi he b
  simp only [quarterPairedEuler644, quarterSymmetricSum644, div_inv_eq_mul, H] at h ⊢
  linarith only [h, hd]

/-- Under GRH, the cosine-weighted zero mass for an even primitive
self-inverse nonprincipal character equals the xi contour, conductor,
and paired Euler difference after subtracting the two residues. -/
theorem quarter_cosine_zero_split_644 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ = χ) (he : χ.Even) {X b : ℝ} (hx : 0 < X) (hb : 0 ≤ b) :
    let H := fun p : ℝ ↦ (quarterSymmetricKernel644 (p : ℂ) * (Real.exp b : ℂ) ^ (p : ℂ)).re
    (∑' ρ, ‖quarterKernel644.oscillatingZeroTerm χ X ρ‖ * Real.cos (b * ρ.im)) =
      quarterCosineXi644 b + Real.log q * threeShiftG122 b / 4 + quarterPairedEuler644 χ b -
        H (-1 / 2) -
        H (1 / 2) := by
  exact
    (quarter_cosine_contour_644 hq hG hp hn hx hb).trans
      (quarter_cosine_decompose_644 hp hn hi he hb)

/-- At a common frequency, three even primitive self-inverse nonprincipal
characters that are one on primes through `X` have one combined Euler tail.
The common xi and residue terms occur three times. -/
theorem quarter_three_cosine_split_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) {X t : ℝ} (hX : 0 ≤ X) (ht : 0 ≤ t)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    let H := fun u : ℝ ↦ (quarterSymmetricKernel644 (u : ℂ) * (Real.exp t : ℂ) ^ (u : ℂ)).re
    quarterCosineContour644 a t + quarterCosineContour644 b t + quarterCosineContour644 c t =
      3 * (quarterCosineXi644 t - H (-1 / 2) - H (1 / 2)) +
        (Real.log p + Real.log q + Real.log s) * threeShiftG122 t / 4 +
        quarterCosineTail644 a b c X t := by
  dsimp only
  rw [quarter_cosine_decompose_644 ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 ht,
    quarter_cosine_decompose_644 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 ht,
    quarter_cosine_decompose_644 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 ht]
  linear_combination quarter_paired_euler_tail_644 a b c hX t hpa hpb hpc

/-- The signed combination of the three frequencies, zero frequency and
three cross frequencies in the section 122 square completion. -/
noncomputable def quarterCosineMix644 (F : ℝ → ℝ) : ℝ :=
  1.54 * F (2687 / 1000) + (-1.508) * F (2707 / 1000) + (-0.0917) * F (3787 / 1000) +
    (-((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2)) * F 0 +
    (1.54 * 1.508) * F (1 / 50) +
    (1.54 * 0.0917) * F (11 / 10) +
    (-(1.508 * 0.0917)) * F (27 / 25)

/-- Under RH, the signed combination of the three character contours has
the sum of its common xi, residue and conductor terms plus the certified
Euler lower bound on the corresponding radius row. -/
theorem quarter_three_cosine_rows_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r : ℝ} (hr : 316 ≤ r)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let H := fun (t u : ℝ) ↦ (quarterSymmetricKernel644 (u : ℂ) * (Real.exp t : ℂ) ^ (u : ℂ)).re
    let V := fun t ↦
      3 * (quarterCosineXi644 t - H t (-1 / 2) - H t (1 / 2)) +
        (Real.log p + Real.log q + Real.log s) * threeShiftG122 t / 4
    quarterCosineMix644 V +
        (if r ≤ 320 then -0.456620
        else if r ≤ 1287 / 4 then -0.452096 else if r ≤ 1609 / 5 then -0.450144 else -0.450088) ≤
      quarterCosineMix644
        (fun t ↦
          quarterCosineContour644 a t + quarterCosineContour644 b t +
            quarterCosineContour644 c t) := by
  intro H V
  have h (t : ℝ) (ht : 0 ≤ t) :=
    quarter_three_cosine_split_644 ha hb hc (sq_nonneg r) ht hpa hpb hpc
  have hrow := quarter_cosine_tail_rows_644 a b c hRH hr htrace
  dsimp only [quarterCosineMix644, V, H] at hrow ⊢
  rw [h _ (by norm_num only), h _ (by norm_num only), h _ (by norm_num only),
    h _ (by norm_num only), h _ (by norm_num only), h _ (by norm_num only), h _ (by norm_num only)]
  linarith only [hrow]

/-- Under RH, the oscillating xi zero series for the symmetric kernel equals
the normalized difference of the two vertical xi integrals at scale `exp b`.
The kernel is regular at the half-unit point. -/
theorem quarter_symmetric_xi_644 (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 ≤ b) :
    let x := Real.exp b
    let F := fun s : ℂ ↦
      -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s + 1 / 2) *
        (quarterSymmetricKernel644 s * (x : ℂ) ^ s)
    (∑' ρ, quarterSymmetricMellin644.zetaOscillatingZeroTerm x ρ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
          ∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  intro x F
  have h :=
    LLS.PaperStatements.MellinKernel.xiContourIdentity quarterSymmetricMellin644 hRH (a :=
      (-9 / 16 : ℝ)) (b := 9 / 16)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (Real.one_le_exp hb)
  have hz (G : ℂ → ℂ) : quarterSymmetricMellin644.weightedResidue G x (-1 / 2) = 0 := by
    simp only [LLS.PaperStatements.MellinKernel.weightedResidue, ite_true]
    change -logDeriv G (-1 / 2) * (((-1 / 2 : ℂ) + 1 / 2) * _ * _) = 0
    rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]
  change
    Complex.I *
        ((∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + t * Complex.I)) -
          ∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + t * Complex.I)) =
      (2 * Real.pi * Complex.I) *
        (quarterSymmetricMellin644.weightedResidue _ x (-1 / 2) -
          ∑' ρ, quarterSymmetricMellin644.zetaOscillatingZeroTerm x ρ) at h
  rw [hz, zero_sub, mul_comm (2 * (Real.pi : ℂ)) Complex.I, mul_assoc] at h
  have he := mul_left_cancel₀ Complex.I_ne_zero h
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div]
  simp only [mul_comm Complex.I]
  rw [eq_inv_mul_iff_mul_eq₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  linear_combination he

/-- Under RH and at nonnegative frequency, the real xi contour equals the
real part of the symmetric kernel's oscillating xi zero series. -/
theorem quarter_xi_cosine_644 (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 ≤ b) :
    quarterCosineXi644 b =
      ∑' ρ, (quarterSymmetricMellin644.zetaOscillatingZeroTerm (Real.exp b) ρ).re := by
  rw [←
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm quarterSymmetricMellin644
        hRH (Real.exp_pos b))]
  exact (congrArg Complex.re (quarter_symmetric_xi_644 hRH hb)).symm

/-- The xi contour at any nonnegative frequency is bounded by the certified
unmodulated zeta mass. The symmetric kernel on the axis is the main kernel norm. -/
theorem quarter_xi_cosine_abs_644 (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 ≤ b) :
    |quarterCosineXi644 b| ≤ 32 / 75000000 := by
  let K := quarterSymmetricMellin644
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm K hRH (Real.exp_pos b)
  have he (ρ : AnalyticNumberTheory.RiemannXi.Zero) :
    ‖K.zetaOscillatingZeroTerm (Real.exp b) ρ‖ = ‖quarterKernel644.zetaKernelZeroTerm ρ‖ := by
    rw [LLS.PaperStatements.MellinKernel.norm_zetaOscillatingZeroTerm K (Real.exp_pos b)]
    unfold LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm
    rw [norm_mul, norm_mul, quarter_zero_norm_644]
    change _ * ‖quarterSymmetricKernel644 _‖ = _
    rw [symmetric_axis, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [quarter_xi_cosine_644 hRH hb, ← Complex.re_tsum hs]
  exact
    (Complex.abs_re_le_norm _).trans
      ((norm_tsum_le_tsum_norm hs.norm).trans
        ((tsum_congr he).le.trans (quarter_zeta_mass_644 hRH)))

/-- Three copies of the common xi contours in the signed seven-frequency
comparison contribute at least minus 0.000011 under RH. -/
theorem quarter_xi_mix_lower_644 (hRH : RiemannHypothesis) :
    -0.000011 ≤ 3 * quarterCosineMix644 quarterCosineXi644 := by
  have h (t : ℝ) (ht : 0 ≤ t) := abs_le.mp (quarter_xi_cosine_abs_644 hRH ht)
  unfold quarterCosineMix644
  linarith only [(h (2687 / 1000) (by norm_num only)).1, (h (2707 / 1000) (by norm_num only)).2,
    (h (3787 / 1000) (by norm_num only)).2, (h 0 (le_refl 0)).2, (h (1 / 50) (by norm_num only)).1,
    (h (11 / 10) (by norm_num only)).1, (h (27 / 25) (by norm_num only)).2]

/-- The pair of symmetric residues at the two half-unit points is a common
rational factor times the sum of the two real exponentials. -/
theorem quarter_cosine_pole_pair_644 (t : ℝ) :
    let H := fun u : ℝ ↦ (quarterSymmetricKernel644 (u : ℂ) * (Real.exp t : ℂ) ^ (u : ℂ)).re
    H (-1 / 2) + H (1 / 2) =
      ((107 / 100 : ℝ) ^ 5 / ((107 / 100 : ℝ) ^ 2 - 1 / 4) ^ 3) *
        (Real.exp (-t / 2) + Real.exp (t / 2)) := by
  intro H
  have h (u : ℝ) (hu : u ^ 2 = 1 / 4) :
    H u = ((107 / 100 : ℝ) ^ 5 / ((107 / 100 : ℝ) ^ 2 - 1 / 4) ^ 3) * Real.exp (t * u) := by
    have hk :
      quarterSymmetricKernel644 (u : ℂ) =
        (((107 / 100 : ℝ) ^ 5 / (((107 / 100 : ℝ) ^ 2 - 1 / 4) ^ 3) : ℝ) : ℂ) := by
      unfold quarterSymmetricKernel644
      rw [← hu, ← Complex.ofReal_ofNat (107 : ℕ), ← Complex.ofReal_ofNat (100 : ℕ)]
      push_cast
      ring
    dsimp only [H]
    rw [hk, ← Complex.ofReal_cpow (Real.exp_pos t).le, ← Complex.ofReal_mul, Complex.ofReal_re,
      Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
  rw [h _ (by norm_num only), h _ (by norm_num only)]
  rw [show t * (-1 / 2) = -t / 2 by ring, show t * (1 / 2) = t / 2 by ring]
  ring

/-- When the total log conductor is four times the radius, the signed
cosine conductor contribution and the linear shifted pole correction
combine into the certified section 122 gain. -/
theorem quarter_cosine_linear_gain_644 {r L : ℝ} (hr : 0 ≤ r) (hL : L = 4 * r) :
    0.00063602 * r ≤
      quarterCosineMix644 (fun t ↦ L * threeShiftG122 t / 4) -
        (3 * (107 / 100 : ℝ) ^ 5 / (157 / 100) ^ 6) * r *
          (1.54 - 1.508 * Real.exp (-(1 / 100)) - 0.0917 * Real.exp (-(11 / 20))) := by
  calc
    0.00063602 * r ≤ threeShiftGain122 * r :=
      mul_le_mul_of_nonneg_right three_shift_gain_lower122.le hr
    _ = _ := by
      rw [hL]
      unfold threeShiftGain122 quarterCosineMix644
      ring

/-- At a positive radius, the main kernel's half-point value at the
shifted scale gives the pole contribution used in the cosine comparison. -/
theorem quarter_shifted_half_pole_644 {r : ℝ} (hr : 0 < r) (h : ℝ) :
    let x := r ^ 2 * Real.exp (-(2687 / 1000 + h))
    (quarterKernel644.function (1 / 2) * (x : ℂ) ^ (1 / 2 : ℂ)).re =
      ((107 / 100 : ℝ) ^ 5 / (157 / 100) ^ 6) * r * Real.exp (-h / 2) := by
  intro x
  have he : Real.log x * (1 / 2) = Real.log r - (2687 / 1000 + h) / 2 := by
    dsimp only [x]
    rw [Real.log_mul (pow_ne_zero _ hr.ne') (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
    ring
  have hx : 0 < x := mul_pos (pow_pos hr _) (Real.exp_pos _)
  have hf :
    quarterKernel644.function (1 / 2) =
      ((((107 / 100 : ℝ) ^ 5 / (157 / 100) ^ 6) * Real.exp (2687 / 2000) : ℝ) : ℂ) := by
    rw [quarter_function_644, Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    norm_num only
    ring
  rw [hf,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by
      norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat],
    ← Complex.ofReal_cpow hx.le, ← Complex.ofReal_mul, Complex.ofReal_re, Real.rpow_def_of_pos hx,
    he, Real.exp_sub, Real.exp_log hr]
  rw [show ((2687 / 1000 : ℝ) + h) / 2 = 2687 / 2000 + h / 2 by ring, Real.exp_add, neg_div,
    Real.exp_neg]
  field_simp [(Real.exp_pos (2687 / 2000)).ne', (Real.exp_pos (h / 2)).ne']

/-- Under RH and agreement on primes through the squared radius, replace the
three common xi contours in the signed comparison by their uniform lower
bound and combine the conductor with the linear shifted pole correction. -/
theorem quarter_cosine_rows_without_xi_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r : ℝ} (hr : 316 ≤ r)
    (hlog : Real.log p + Real.log q + Real.log s = 4 * r)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let V := fun t ↦
      -3 * ((107 / 100 : ℝ) ^ 5 / ((107 / 100 : ℝ) ^ 2 - 1 / 4) ^ 3) *
        (Real.exp (-t / 2) + Real.exp (t / 2))
    let K := fun h : ℝ ↦
      (quarterKernel644.function (1 / 2) *
          ((r ^ 2 * Real.exp (-(2687 / 1000 + h)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)).re
    let P := 3 * (1.54 * K 0 - 1.508 * K (1 / 50) - 0.0917 * K (11 / 10))
    quarterCosineMix644 V + 0.00063602 * r + P - 0.000011 +
        (if r ≤ 320 then -0.456620
        else if r ≤ 1287 / 4 then -0.452096 else if r ≤ 1609 / 5 then -0.450144 else -0.450088) ≤
      quarterCosineMix644
        (fun t ↦
          quarterCosineContour644 a t + quarterCosineContour644 b t +
            quarterCosineContour644 c t) := by
  intro V K P
  have hrow := quarter_three_cosine_rows_644 ha hb hc hRH hr hpa hpb hpc htrace
  have hxi := quarter_xi_mix_lower_644 hRH
  have hg := quarter_cosine_linear_gain_644 (by linarith only [hr]) hlog
  have hr₀ : 0 < r := by linarith only [hr]
  have hp :
    P =
      (3 * (107 / 100 : ℝ) ^ 5 / (157 / 100) ^ 6) * r *
        (1.54 - 1.508 * Real.exp (-(1 / 100)) - 0.0917 * Real.exp (-(11 / 20))) := by
    dsimp only [P, K]
    rw [quarter_shifted_half_pole_644 hr₀ 0, quarter_shifted_half_pole_644 hr₀ (1 / 50),
      quarter_shifted_half_pole_644 hr₀ (11 / 10)]
    norm_num only [neg_zero, zero_div, Real.exp_zero, mul_one, neg_div]
    ring
  rw [hp]
  dsimp only [quarterCosineMix644, V] at hrow hxi hg ⊢
  have h (t : ℝ) := quarter_cosine_pole_pair_644 t
  linarith only [hrow, hxi, hg, h (2687 / 1000), h (2707 / 1000), h (3787 / 1000), h 0, h (1 / 50),
    h (11 / 10), h (27 / 25)]

end PseudoPrime.PrimeTestBounds.MillerRabin
