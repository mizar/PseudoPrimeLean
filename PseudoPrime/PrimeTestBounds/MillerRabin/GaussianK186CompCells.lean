/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompCellCaps
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompSigned
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompCellCaps
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompSigned
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186CompInteger
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAffineHorner
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPartition
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ForwardMoment
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompIntegerBernstein

/-! # K186 cell bounds from one verified integer Bernstein row -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational polynomial in the unit coordinate of a K186 dyadic cell. -/
private noncomputable def k186CellPoly (i w : ℕ) : Polynomial ℚ :=
  HighGaussianKernel.k186.ratProfile.comp
    (Polynomial.C (logCoordinate w) * Polynomial.X + Polynomial.C (logCoordinate i))

/-- Transfer the certified integer row to the rational cell polynomial. -/
private theorem k186_cell_coeff_eq (i w j : ℕ) :
    Analysis.bernsteinRatCoeff (k186CellPoly i w) 83 j =
      ((k186CompAffine i w).bernsteinNum 83 j : ℚ) /
        (((k186CompAffine i w).den : ℚ) * ((83 : ℕ).factorial : ℚ)) := by
  rw [k186CellPoly, ← k186_comp_affine_poly]
  exact (k186CompAffine i w).bernstein_num_eq 83 j

/-- The common positive scale of the cell's integer Bernstein row. -/
private def k186CellScale (i w : ℕ) : ℤ :=
  (k186CompAffine i w).den * ((83 : ℕ).factorial : ℤ)

/-- Clip after clearing a common denominator. -/
private def k186ClipNum (i w j : ℕ) : ℤ :=
  max 0 (-(k186CompAffine i w).bernsteinNum 83 j)

/-- The integer scale remains positive for all cells. -/
private theorem k186_cell_scale_pos (i w : ℕ) : 0 < k186CellScale i w :=
  mul_pos (k186_comp_affine_pos i w) (Int.natCast_pos.mpr (Nat.factorial_pos _))

/-- The clipped integer row represents the exact rational clipped coefficients. -/
private theorem k186_clip_num_eq (i w j : ℕ) :
    max 0 (-Analysis.bernsteinRatCoeff (k186CellPoly i w) 83 j) =
      (k186ClipNum i w j : ℚ) / (k186CellScale i w : ℚ) := by
  rw [k186CellPoly, ← k186_comp_affine_poly,
    (k186CompAffine i w).bernstein_clip_eq _ _ (k186_comp_affine_pos i w)]
  simp only [k186ClipNum, k186CellScale, Int.cast_mul, Int.cast_natCast]

/-- The integer sum of clipped coefficients supplies the narrow-cell main bound. -/
private theorem k186_cell_main_mean (i w : ℕ) {E : ℚ} (hw : 0 < w)
    (he : Real.exp (-((13 / 4 : ℚ) : ℝ) * (logCoordinate i : ℝ)) ≤ (E : ℝ)) :
    (∫ t in (logCoordinate i : ℝ)..(logCoordinate i : ℝ) + (logCoordinate w : ℝ),
        mainIntegrand .k186 (logCoordinate i) (logCoordinate w) t) ≤
      ((E * logCoordinate w * (∑ j : Fin 84, k186ClipNum i w j : ℤ)) /
          ((k186CellScale i w : ℚ) * 84) :
        ℚ) := by
  have h := high_cell_comp_mean_le .k186 (s := 13 / 4) (by norm_num only) (log_coord_pos hw) he
  have hrate : (HighGaussianKernel.k186.pole + 1 / 2 : ℚ) = 13 / 4 := by
    norm_num only [HighGaussianKernel.pole]
  dsimp only at h
  change
    _ ≤
      (E : ℝ) * (logCoordinate w : ℝ) *
          (↑(∑ j : Fin 84, max 0 (-Analysis.bernsteinRatCoeff (k186CellPoly i w) 83 j.val) : ℚ)) /
        ((83 : ℕ) + (1 : ℝ)) at h
  simp only [mainIntegrand, hrate, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast]
  simp only [k186_clip_num_eq, ← Finset.sum_div, Rat.cast_div, Rat.cast_sum, Rat.cast_intCast,
    Nat.cast_ofNat] at h
  exact
    h.trans_eq
      (by
        rw [Int.cast_sum]; ring)

/-- A variation coefficient can be compared over the common integer scale
without dividing or normalizing its rational value. -/
private theorem k186_cell_var_num (i w : ℕ) (j : Fin 84) :
    |Analysis.bernsteinVariationDirect 83 j.val (9 / 4) (logCoordinate w)
          (fun k ↦ max 0 (-Analysis.bernsteinRatCoeff (k186CellPoly i w) 83 k))| =
      (compIntVariation (logCoordinate w)⁻¹ (k186ClipNum i w j.val)
            (Analysis.bernsteinDerivativeCoeff 83 (k186ClipNum i w) j.val) :
          ℤ) /
        (4 * ((logCoordinate w)⁻¹.den : ℚ) * (k186CellScale i w : ℚ)) := by
  simp only [k186_clip_num_eq]
  rw [comp_variation_abs_div _ _ _ _ _ _ (Int.cast_nonneg (k186_cell_scale_pos i w).le), ←
    comp_int_variation_eq, div_div]

/-- Integer inequalities at the common scale certify a rectangular
variation envelope for a dyadic cell. -/
private theorem k186_cell_var_bound (i w : ℕ) {E M : ℚ} (hw : 0 < w) (hM : 0 ≤ M)
    (he : Real.exp (-(HighGaussianKernel.k186.pole : ℝ) * (logCoordinate i : ℝ)) ≤ E)
    (hc :
      ∀ j : Fin 84,
        (compIntVariation (logCoordinate w)⁻¹ (k186ClipNum i w j.val)
              (Analysis.bernsteinDerivativeCoeff 83 (k186ClipNum i w) j.val) :
            ℤ) ≤
          M * (4 * ((logCoordinate w)⁻¹.den : ℚ) * (k186CellScale i w : ℚ))) :
    (∫ t in (logCoordinate i : ℝ)..(logCoordinate i : ℝ) + (logCoordinate w : ℝ),
        variationIntegrand .k186 (logCoordinate i) (logCoordinate w) t) ≤
      ((logCoordinate w * E * M : ℚ) : ℝ) := by
  have hd : 0 < 4 * ((logCoordinate w)⁻¹.den : ℚ) * (k186CellScale i w : ℚ) :=
    mul_pos (mul_pos (by decide) (Nat.cast_pos.mpr (Rat.den_pos _)))
      (Int.cast_pos.mpr (k186_cell_scale_pos i w))
  have hf :
    ∀ j : Fin 84,
      |Analysis.bernsteinVariationDirect 83 j.val (9 / 4) (logCoordinate w)
            (fun k ↦ max 0 (-Analysis.bernsteinRatCoeff (k186CellPoly i w) 83 k))| ≤
        M := by
    intro j
    rw [k186_cell_var_num]
    exact (div_le_iff₀ hd).mpr (hc j)
  have hrate : HighGaussianKernel.k186.pole - 1 / 2 = (9 / 4 : ℚ) := by
    norm_num only [HighGaussianKernel.pole]
  have h :=
    high_cell_comp_var_max .k186 (log_coord_pos hw) (by norm_num only [HighGaussianKernel.pole]) hM
      he
      (by
        simpa only [HighGaussianKernel.degree, Nat.reduceMul, Nat.reduceAdd, hrate,
          k186CellPoly] using hf)
  simpa only [Rat.cast_mul] using h

/-- Directed Horner evaluation of the shared K186 Laplace polynomial. -/
private def k186MomentAt (i : ℕ) : Analysis.IntegerInterval :=
  forwardMomentRow.evalInterval 83 (5 * (i : ℤ)) 524288

/-- The certified integer row encloses the Laplace polynomial at a dyadic endpoint. -/
private theorem k186_moment_at_contains (i : ℕ) :
    (k186MomentAt i).Contains forwardMomentRow.den
      (((middleMomentPoly HighGaussianKernel.k186.ratProfile (13 / 4) 0).map (Rat.castHom ℝ)).eval
        (logCoordinate i : ℝ)) := by
  have h :=
    forwardMomentRow.eval_interval_contains 83 (5 * (i : ℤ)) 524288 (by decide +kernel) (by decide)
  rw [forward_moment_poly] at h
  norm_num only [HighGaussianKernel.pole, logCoordinate, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
    Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at h ⊢
  exact h

/-- The endpoint lower bound can be clipped at zero for interval multiplication. -/
private def k186ExpLow (x : ℚ) : ℚ :=
  max 0 (negativeEndpointExpLower x)

/-- The signed main charge uses one evaluation of the shared moment row
and two exponential bounds at each endpoint. -/
private def k186NegMainCharge (i w : ℕ) : ℚ :=
  let a := 13 / 4 * logCoordinate i
  let b := 13 / 4 * logCoordinate (i + w)
  let F := ((k186MomentAt i).lower : ℚ) / forwardMomentRow.den
  let G := ((k186MomentAt (i + w)).upper : ℚ) / forwardMomentRow.den
  max (k186ExpLow b * G) (negativeEndpointExpUpper b * G) -
    min (k186ExpLow a * F) (negativeEndpointExpUpper a * F)

/-- All accepted endpoint exponentials are enclosed by the rational
Taylor bounds at arguments in the compensated support. -/
private theorem k186_endpoint_exp_bounds {i : ℕ} (hi : i ≤ 524288) :
    (k186ExpLow (13 / 4 * logCoordinate i) : ℝ) ≤
        Real.exp (-((13 / 4 : ℚ) : ℝ) * (logCoordinate i : ℝ)) ∧
      Real.exp (-((13 / 4 : ℚ) : ℝ) * (logCoordinate i : ℝ)) ≤
        (negativeEndpointExpUpper (13 / 4 * logCoordinate i) : ℝ) := by
  have h0 : 0 ≤ (13 / 4 : ℚ) * logCoordinate i := mul_nonneg (by norm_num only) (log_coord_nonneg i)
  have h5 : logCoordinate i ≤ 5 := by
    have h := (Nat.cast_le (α := ℚ)).mpr hi
    dsimp only [logCoordinate]
    exact
      (div_le_iff₀ (by norm_num only)).mpr
        (by
          simpa only [Nat.cast_ofNat] using
            mul_le_mul_of_nonneg_left h (by norm_num only : (0 : ℚ) ≤ 5))
  have hu :=
    (mul_le_mul_of_nonneg_left h5 (by norm_num only : (0 : ℚ) ≤ 13 / 4)).trans
      (by norm_num only : (13 / 4 : ℚ) * 5 ≤ 264)
  simp only [k186ExpLow, Rat.cast_max, Rat.cast_zero]
  exact
    ⟨max_le (Real.exp_nonneg _)
        (by simpa only [Rat.cast_mul, neg_mul] using negative_endpoint_exp_lower_valid h0 hu),
      by simpa only [Rat.cast_mul, neg_mul] using negative_endpoint_exp_upper_valid h0⟩

/-- Moving the signed endpoint factors outwards preserves the main charge bound. -/
private theorem k186_cell_main_neg (i w : ℕ) (hw : 0 < w) (hend : i + w ≤ 524288)
    (hc : ∀ j ≤ 83, (k186CompAffine i w).bernsteinNum 83 j ≤ 0) :
    (∫ t in (logCoordinate i : ℝ)..(logCoordinate i : ℝ) + (logCoordinate w : ℝ),
        mainIntegrand .k186 (logCoordinate i) (logCoordinate w) t) ≤
      (k186NegMainCharge i w : ℝ) := by
  let a := logCoordinate i
  let b := logCoordinate (i + w)
  let M := middleMomentPoly HighGaussianKernel.k186.ratProfile (13 / 4) 0
  have he : b = a + logCoordinate w := log_coord_add i w
  have hh : b - a = logCoordinate w := by rw [he, add_sub_cancel_left]
  have hab : a < b := he ▸ lt_add_of_pos_right a (log_coord_pos hw)
  have hcoeff : ∀ j ≤ 83, Analysis.bernsteinRatCoeff (k186CellPoly i w) 83 j ≤ 0 := by
    intro j hj
    rw [k186_cell_coeff_eq]
    exact
      div_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr (hc j hj))
        (mul_nonneg (Int.cast_nonneg (k186_comp_affine_pos i w).le) (Nat.cast_nonneg _))
  have hl := k186_endpoint_exp_bounds ((Nat.le_add_right i w).trans hend)
  have hr := k186_endpoint_exp_bounds hend
  have hmain :=
    high_cell_comp_signed_le .k186 (s := 13 / 4) (a := a) (b := b) (by norm_num only)
      (log_coord_nonneg i) hab
      (fun j hj ↦ by
        simpa only [hh, k186CellPoly, a, HighGaussianKernel.degree, Nat.reduceMul,
          Nat.reduceAdd] using hcoeff j hj)
      _ _ _ _ hl hr
  dsimp only at hmain
  rw [hh] at hmain
  have ha := (k186_moment_at_contains i).1
  have hb := (k186_moment_at_contains (i + w)).2
  change _ ≤ (M.map (Rat.castHom ℝ)).eval (Rat.castHom ℝ a) at ha
  change (M.map (Rat.castHom ℝ)).eval (Rat.castHom ℝ b) ≤ _ at hb
  rw [Polynomial.eval_map_apply (p := M) (Rat.castHom ℝ) a, Rat.coe_castHom] at ha
  rw [Polynomial.eval_map_apply (p := M) (Rat.castHom ℝ) b, Rat.coe_castHom] at hb
  have hposL (x : ℚ) : 0 ≤ (k186ExpLow x : ℝ) := Rat.cast_nonneg.mpr (le_max_left _ _)
  have hrates : (HighGaussianKernel.k186.pole + 1 / 2 : ℚ) = 13 / 4 := by
    norm_num only [HighGaussianKernel.pole]
  have hstart : (a : ℝ) + (logCoordinate w : ℝ) = (b : ℝ) := by rw [he, Rat.cast_add]
  rw [hstart]
  simp only [mainIntegrand, hrates]
  refine hmain.trans ?_
  simp only [k186NegMainCharge, Rat.cast_max, Rat.cast_min, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_div, Rat.cast_intCast]
  exact
    sub_le_sub
      (max_le_max (mul_le_mul_of_nonneg_left hb (hposL _))
        (mul_le_mul_of_nonneg_left hb ((Real.exp_nonneg _).trans hr.2)))
      (min_le_min (mul_le_mul_of_nonneg_left ha (hposL _))
        (mul_le_mul_of_nonneg_left ha ((Real.exp_nonneg _).trans hl.2)))

/-- Cache the Bernstein row for the sign, mean, and variation checks. The
extra successor coefficient is included for degree-preserving differences. -/
private def k186CertNum (i w j : ℕ) : ℤ :=
  let r := Array.ofFn (fun k : Fin 85 ↦ (k186CompAffine i w).bernsteinNum 83 k.val)
  if hj : j < 85 then r[j]'(Array.size_ofFn.symm ▸ hj) else (k186CompAffine i w).bernsteinNum 83 j

/-- The cached coefficient agrees with the integer transform at every index. -/
private theorem k186_cert_num_eq (i w j : ℕ) :
    k186CertNum i w j = (k186CompAffine i w).bernsteinNum 83 j := by
  simp only [k186CertNum, Array.getElem_ofFn, dite_eq_ite, ite_self]

/-- Clipping the cache agrees with clipping the underlying integer transform. -/
private theorem k186_cert_clip_eq (i w j : ℕ) : max 0 (-k186CertNum i w j) = k186ClipNum i w j := by
  rw [k186_cert_num_eq, k186ClipNum]

/-- The main charge with the exponential fixed at the left endpoint. -/
private def k186MeanCharge (i w : ℕ) : ℚ :=
  let E := negativeEndpointExpUpper (13 / 4 * logCoordinate i)
  let c := fun j ↦ max 0 (-k186CertNum i w j)
  E * logCoordinate w * (∑ j : Fin 84, c j : ℤ) / ((k186CellScale i w : ℚ) * 84)

/-- The rectangular variation charge using a coefficient cap in units of
ten to the negative eighth power. -/
private def k186VarRect (i w M : ℕ) : ℚ :=
  logCoordinate w * negativeEndpointExpUpper ((11 / 4) * logCoordinate i) * ((M : ℚ) / 10 ^ 8)

/-- Check a nonzero cell. Sign-constant cells use signed endpoint moments.
The other cells use the coefficient mean. Both use integer variation comparisons. -/
private def k186CompCheck (i : ℕ) (c : CompCellCap) (M : ℕ) (neg : Bool) : Bool :=
  let r := k186CertNum i c.width
  let clip := fun j ↦ max 0 (-r j)
  let q := (logCoordinate c.width)⁻¹
  let D := 4 * (q.den : ℤ) * k186CellScale i c.width
  let checkMain :=
    if neg then
      (List.range 84).all (fun j ↦ decide (r j ≤ 0)) &&
        decide (k186NegMainCharge i c.width ≤ (c.main : ℚ) / 10 ^ 20)
    else decide (k186MeanCharge i c.width ≤ (c.main : ℚ) / 10 ^ 20)
  checkMain &&
    (List.range 84).all
      (fun j ↦
        decide
          (10 ^ 8 * compIntVariation q (clip j) (Analysis.bernsteinDerivativeCoeff 83 clip j) ≤
            (M : ℤ) * D)) &&
    decide (k186VarRect i c.width M ≤ (c.variation : ℚ) / 10 ^ 20)

/-- The rational rectangular variation charge follows from the checked
integer inequality at each coefficient. -/
private theorem k186_var_rect_sound (i w M : ℕ) (hw : 0 < w)
    (hc :
      (List.range 84).all
          (fun j ↦
            decide
              (10 ^ 8 *
                  compIntVariation (logCoordinate w)⁻¹ (max 0 (-k186CertNum i w j))
                    (Analysis.bernsteinDerivativeCoeff 83 (fun k ↦ max 0 (-k186CertNum i w k)) j) ≤
                (M : ℤ) * (4 * ((logCoordinate w)⁻¹.den : ℤ) * k186CellScale i w))) =
        true) :
    (∫ t in (logCoordinate i : ℝ)..(logCoordinate i : ℝ) + (logCoordinate w : ℝ),
        variationIntegrand .k186 (logCoordinate i) (logCoordinate w) t) ≤
      k186VarRect i w M := by
  have hq : (0 : ℚ) ≤ (11 / 4) * logCoordinate i :=
    mul_nonneg (by norm_num only) (log_coord_nonneg i)
  have he :
    Real.exp (-(HighGaussianKernel.k186.pole : ℝ) * (logCoordinate i : ℝ)) ≤
      (negativeEndpointExpUpper (11 / 4 * logCoordinate i) : ℝ) := by
    rw [HighGaussianKernel.pole]
    simpa only [Rat.cast_mul, neg_mul] using negative_endpoint_exp_upper_valid hq
  apply
    k186_cell_var_bound i w (M := (M : ℚ) / 10 ^ 8) hw
      (div_nonneg (Nat.cast_nonneg _) (by norm_num only)) he
  intro j
  have h := of_decide_eq_true (List.all_eq_true.mp hc j.val (List.mem_range.mpr j.isLt))
  simp only [k186_cert_clip_eq] at h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by norm_num only : (0 : ℚ) < 10 ^ 8)).mpr
  rw [mul_comm _ (10 ^ 8 : ℚ)]
  exact_mod_cast h

/-- A passing sign/mean and variation check certifies one cell of the
piecewise Abel integrals. -/
private theorem k186_comp_check_sound (i : ℕ) (c : CompCellCap) (M : ℕ) (neg : Bool)
    (hw : 0 < c.width) (hend : i + c.width ≤ 524288) (hc : k186CompCheck i c M neg = true) :
    CompCellCaps .k186 [c] i := by
  simp only [k186CompCheck, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨hm, hv, hvr⟩ := hc
  refine ⟨?_, ?_, True.intro⟩
  · cases neg with
    | false =>
      have he := (k186_endpoint_exp_bounds ((Nat.le_add_right i c.width).trans hend)).2
      have hu := k186_cell_main_mean i c.width hw he
      have hb := (Rat.cast_le (K := ℝ)).mpr (of_decide_eq_true hm)
      exact
        hu.trans
          (by
            simpa only [k186MeanCharge, k186_cert_clip_eq, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
              Rat.cast_ofNat, Rat.cast_intCast] using hb)
    | true =>
      simp only [ite_true, Bool.and_eq_true] at hm
      have hsign (j : ℕ) (hj : j ≤ 83) : (k186CompAffine i c.width).bernsteinNum 83 j ≤ 0 := by
        rw [← k186_cert_num_eq]
        exact
          of_decide_eq_true (List.all_eq_true.mp hm.1 j (List.mem_range.mpr (Nat.lt_succ_of_le hj)))
      exact
        (k186_cell_main_neg i c.width hw hend hsign).trans
          (by
            simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_intCast] using
              (Rat.cast_le (K := ℝ)).mpr (of_decide_eq_true hm.2))
  · exact
      (k186_var_rect_sound i c.width M hw hv).trans
        (by
          simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_intCast] using
            (Rat.cast_le (K := ℝ)).mpr (of_decide_eq_true hvr))

/-- A nonnegative integer row gives the zero correction polynomial. -/
private theorem k186_cell_poly_zero (i w : ℕ) (hc : k186CompSign i w = true) :
    Analysis.bernsteinCompensation (k186CellPoly i w) 83 = 0 := by
  have hden : 0 ≤ ((k186CompAffine i w).den : ℚ) * ((83 : ℕ).factorial : ℚ) :=
    mul_nonneg (Int.cast_nonneg (k186_comp_affine_pos i w).le) (Nat.cast_nonneg _)
  rw [Analysis.bernsteinCompensation]
  apply Finset.sum_eq_zero
  intro j _
  have hs := of_decide_eq_true (List.all_eq_true.mp hc j.val (List.mem_range.mpr j.isLt))
  have hr : 0 ≤ Analysis.bernsteinRatCoeff (k186CellPoly i w) 83 j := by
    rw [k186_cell_coeff_eq]
    exact div_nonneg (Int.cast_nonneg hs) hden
  rw [max_eq_left (neg_nonpos.mpr (Rat.cast_nonneg.mpr hr)), Polynomial.C_0, zero_mul]

/-- A sign-only check suffices for both integral caps in a nonnegative cell. -/
private theorem k186_cell_zero_caps (i w : ℕ) (hc : k186CompSign i w = true) :
    CompCellCaps .k186 [⟨w, 0, 0⟩] i := by
  have h := k186_cell_poly_zero i w hc
  change Analysis.bernsteinCompensation (k186CellPoly i w) (2 * 40 + 3) = 0 at h
  unfold k186CellPoly at h
  refine ⟨?_, ?_, True.intro⟩
  · simp only [mainIntegrand, highCellCompensation, HighGaussianKernel.degree, h,
      Polynomial.eval_zero, mul_zero, intervalIntegral.integral_zero, Int.cast_zero, zero_div,
      le_refl]
  · simp only [variationIntegrand, HighGaussianKernel.degree, h, Polynomial.derivative_zero,
      Polynomial.eval_zero, mul_zero, sub_zero, abs_zero, intervalIntegral.integral_zero,
      Int.cast_zero, zero_div, le_refl]

/-- The first merged K186 cell passes the nonnegative-sign check. -/
private theorem k186_first_sign : k186CompSign 0 3983 = true := by decide +kernel

/-- The first merged K186 cell has identically zero compensation. -/
public theorem k186_comp_first_eq_zero (t : ℝ) :
    highCellCompensation .k186 0 (5 * 3983 / 524288) t = 0 := by
  have h := k186_cell_poly_zero 0 3983 k186_first_sign
  have hzero : logCoordinate 0 = 0 := by
    simp only [logCoordinate, Nat.cast_zero, mul_zero, zero_div]
  rw [← hzero]
  change highCellCompensation .k186 (logCoordinate 0) (logCoordinate 3983) t = 0
  rw [highCellCompensation]
  change (Analysis.bernsteinCompensation (k186CellPoly 0 3983) 83).eval _ = 0
  rw [h, Polynomial.eval_zero]

end PseudoPrime.PrimeTestBounds.MillerRabin
