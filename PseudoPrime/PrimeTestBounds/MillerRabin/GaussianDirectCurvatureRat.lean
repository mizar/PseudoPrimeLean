/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalComputed
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleResidual
import PseudoPrime.Analysis.BernsteinIntegral
import Mathlib.Data.List.Forall2
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # Shared rational coefficients for the Gaussian curvature checks -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Compute each translated coefficient from a finite rational source row.
Powers of the common origin are shared by all output coefficients. -/
@[expose]
public def gaussianShiftRatRow (N : ℕ) (o : ℚ) (q : ℕ → ℚ) : Array ℚ :=
  let powers := Array.ofFn (fun j : Fin (N + 1) ↦ o ^ j.val)
  Array.ofFn
    (fun i : Fin (N + 1) ↦
      ∑ j ∈ Finset.range (N + 1), q j * ((Nat.fast_choose j i.val : ℚ) * powers[j - i.val]?.getD 0))

/-- Each entry of the translated rational row agrees with affine composition. -/
public theorem gaussian_shift_rat_coeff (Q : Polynomial ℚ) (N : ℕ) (o : ℚ) (q : ℕ → ℚ)
    (hQ : Q.natDegree ≤ N) (hq : ∀ j ≤ N, q j = Q.coeff j) {i : ℕ} (hi : i ≤ N) :
    (gaussianShiftRatRow N o q)[i]?.getD 0 = (Q.comp (Polynomial.X + Polynomial.C o)).coeff i := by
  have hi' := Nat.lt_succ_of_le hi
  have h := Analysis.rational_affine_coeff Q N hQ o 1 i
  simp only [Polynomial.C_1, one_mul, one_pow] at h
  rw [h]
  simp only [gaussianShiftRatRow, Array.getElem?_ofFn, dite_eq_left hi', Option.getD_some]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hji := (Nat.sub_le j i).trans_lt hj'
  simp only [dite_eq_left hji, Option.getD_some, hq j (Nat.le_of_lt_succ hj')]

/-- Reuse the translated row to evaluate the absolute coefficient sum at a width.
The scan does not reconstruct the translated polynomial. -/
@[expose]
public def gaussianAbsRatRow (N : ℕ) (row : Array ℚ) (w : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (N + 1), |row[i]?.getD 0| * w ^ i

/-- A single translated rational row evaluates all cell-width caps for its polynomial. -/
private theorem gaussian_abs_rat_row_cast (Q : Polynomial ℚ) (N : ℕ) (o b : ℚ) (q : ℕ → ℚ)
    (hQ : Q.natDegree ≤ N) (hq : ∀ j ≤ N, q j = Q.coeff j) :
    (gaussianAbsRatRow N (gaussianShiftRatRow N o q) (b - o) : ℝ) =
      gaussianShiftedAbsSum (Q.map (Rat.castHom ℝ)) o b := by
  let P := Q.comp (Polynomial.X + Polynomial.C o)
  have hp : P.natDegree ≤ N := by
    refine Polynomial.natDegree_comp_le.trans ?_
    simpa only [Polynomial.natDegree_X_add_C, mul_one] using hQ
  have hm :
    P.map (Rat.castHom ℝ) = (Q.map (Rat.castHom ℝ)).comp (Polynomial.X + Polynomial.C (o : ℝ)) := by
    simp only [P, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Rat.coe_castHom]
  have hr (i : ℕ) (hi : i ∈ Finset.range (N + 1)) :
    ((gaussianShiftRatRow N o q)[i]?.getD 0 : ℝ) = (P.map (Rat.castHom ℝ)).coeff i := by
    rw [gaussian_shift_rat_coeff Q N o q hQ hq (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),
      Polynomial.coeff_map, Rat.coe_castHom]
  rw [gaussianShiftedAbsSum, ← hm]
  simp only [gaussianAbsRatRow, Rat.cast_sum, Rat.cast_mul, Rat.cast_abs, Rat.cast_pow,
    Rat.cast_sub]
  have he :
    (∑ i ∈ Finset.range (N + 1),
        |((gaussianShiftRatRow N o q)[i]?.getD 0 : ℝ)| * ((b : ℝ) - (o : ℝ)) ^ i) =
      ∑ i ∈ Finset.range (N + 1), |(P.map (Rat.castHom ℝ)).coeff i| * ((b : ℝ) - (o : ℝ)) ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hr i hi]
  rw [he]
  symm
  have hd : (P.map (Rat.castHom ℝ)).natDegree ≤ N := Polynomial.natDegree_map_le.trans hp
  apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hd))
  intro j _ hj
  have hz : (P.map (Rat.castHom ℝ)).natDegree < j :=
    Nat.lt_of_succ_le (Nat.le_of_not_lt fun h ↦ hj (Finset.mem_range.mpr h))
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hz, abs_zero, zero_mul]

/-- Compute the signed curvature polynomial coefficient without constructing derivatives. -/
@[expose]
public def gaussianCurvRatCoeff (r : ℚ) (p : ℕ → ℚ) (i : ℕ) : ℚ :=
  (i + 2 : ℕ) * (i + 1 : ℕ) * p (i + 2) - 2 * r * ((i + 1 : ℕ) * p (i + 1)) + r ^ 2 * p i

/-- The fixed-degree curvature compiler computes the second derivative polynomial. -/
private theorem gaussian_curv_rat_coeff_eq (P : Polynomial ℚ) (r : ℚ) (p : ℕ → ℚ)
    (hp : ∀ i, p i = P.coeff i) (i : ℕ) :
    gaussianCurvRatCoeff r p i =
      (P.derivative.derivative - Polynomial.C (2 * r) * P.derivative +
            Polynomial.C (r ^ 2) * P).coeff
        i := by
  simp only [gaussianCurvRatCoeff, hp, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_derivative, Nat.add_assoc, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_one]
  ring

/-- The rational curvature polynomial maps to the real curvature term of the residual. -/
private theorem gaussian_curv_poly_map (P : Polynomial ℚ) (r : ℚ) :
    (P.derivative.derivative - Polynomial.C (2 * r) * P.derivative + Polynomial.C (r ^ 2) * P).map
        (Rat.castHom ℝ) =
      gaussianDecayDeriv (r : ℝ) (gaussianDecayDeriv (r : ℝ) (P.map (Rat.castHom ℝ))) := by
  rw [gaussian_decay_deriv_twice]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.derivative_map, Rat.coe_castHom, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]

/-- The rational scan of a shared curvature row is exactly the real
coefficient majorant used in the middle-cell proof. -/
public theorem gaussian_curv_row_cast (P : Polynomial ℚ) (N : ℕ) (r o b : ℚ) (p : ℕ → ℚ)
    (hP : P.natDegree ≤ N) (hp : ∀ i, p i = P.coeff i) :
    (gaussianAbsRatRow N (gaussianShiftRatRow N o (gaussianCurvRatCoeff r p)) (b - o) : ℝ) =
      gaussianShiftedAbsSum (gaussianDecayDeriv r (gaussianDecayDeriv r (P.map (Rat.castHom ℝ)))) o
        b := by
  let Q := P.derivative.derivative - Polynomial.C (2 * r) * P.derivative + Polynomial.C (r ^ 2) * P
  have hd := (Polynomial.natDegree_derivative_le P).trans ((Nat.sub_le _ _).trans hP)
  have hdd := (Polynomial.natDegree_derivative_le P.derivative).trans ((Nat.sub_le _ _).trans hd)
  have hQ : Q.natDegree ≤ N := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact
        (Polynomial.natDegree_sub_le_of_le hdd ((Polynomial.natDegree_C_mul_le _ _).trans hd)).trans
          (max_le le_rfl le_rfl)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans hP
  have h :=
    gaussian_abs_rat_row_cast Q N o b (gaussianCurvRatCoeff r p) hQ
      (fun i _ ↦ gaussian_curv_rat_coeff_eq P r p hp i)
  simpa only [Q, gaussian_curv_poly_map] using h

/-- A rational bound for the sum of weighted curvature scans is a real
curvature cap on the cell. The exponential caps are supplied separately. -/
public theorem gaussian_mid_curv_le_rat {m : ℕ} {s β x : ℝ} {o a b C : ℚ} (hs : s ≤ 0) (hβ : 0 ≤ β)
    (r E : Fin m → ℚ) (P : Fin m → Polynomial ℚ) (N : ℕ) (p : Fin m → ℕ → ℚ)
    (hP : ∀ i, (P i).natDegree ≤ N) (hp : ∀ i j, p i j = (P i).coeff j) (hr : ∀ i, 0 ≤ r i)
    (ho : o ≤ a) (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) (hE : ∀ i, Real.exp (-(r i : ℝ) * a) ≤ E i)
    (hC :
      (∑ i,
          E i *
            gaussianAbsRatRow N (gaussianShiftRatRow N o (gaussianCurvRatCoeff (r i) (p i)))
              (b - o)) ≤
        C) :
    gaussianMidResidualCurv s β (fun i ↦ (r i : ℝ)) (fun i ↦ (P i).map (Rat.castHom ℝ)) x ≤ C := by
  let B := fun i ↦
    gaussianAbsRatRow N (gaussianShiftRatRow N o (gaussianCurvRatCoeff (r i) (p i))) (b - o)
  refine
    (gaussian_mid_curvature_le hs hβ _ _ (fun i ↦ (E i : ℝ)) (fun i ↦ (B i : ℝ))
          (fun i ↦ Rat.cast_nonneg.mpr (hr i)) (Rat.cast_le.mpr ho) hx hE ?_).trans
      ?_
  · exact fun i ↦ (gaussian_curv_row_cast (P i) N (r i) o b (p i) (hP i) (hp i)).ge
  · have h : ((∑ i, E i * B i : ℚ) : ℝ) ≤ (C : ℝ) := Rat.cast_le.mpr hC
    simpa only [Rat.cast_sum, Rat.cast_mul] using h

/-- Fixed-point Horner evaluation encloses the evaluation of the real polynomial
formed from the same ascending coefficient row. -/
public theorem gaussian_ratio_horner_contains {G p d : ℤ} {row : List Analysis.IntegerInterval}
    {coeff : List ℝ} (hG : 0 < G) (hd : 0 < d)
    (h : List.Forall₂ (fun I x ↦ Analysis.IntegerInterval.Contains I G x) row coeff) :
    (Analysis.intervalRatioHorner p d row).Contains G
      ((coeff.foldr (fun c P ↦ Polynomial.C c + Polynomial.X * P) 0).eval ((p : ℝ) / d)) := by
  have he :
    ((coeff.foldr (fun c P ↦ Polynomial.C c + Polynomial.X * P) 0).eval ((p : ℝ) / d)) =
      coeff.foldr (fun c acc ↦ c + (p : ℝ) * acc / d) 0 := by
    clear h
    induction coeff with
    | nil => simp only [List.foldr_nil, Polynomial.eval_zero]
    | cons c cs ih =>
      simp only [List.foldr_cons, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X, ih, div_mul_eq_mul_div]
  rw [he]
  exact Analysis.interval_ratio_horner_contains hG hd h

/-- Round a common-denominator row outwards at the working integer scale. -/
@[expose]
public def gaussianRoundRow (G D : ℤ) (row : List ℤ) : List Analysis.IntegerInterval :=
  row.map fun c ↦ Analysis.roundedConstant G c D

/-- Each rounded coefficient encloses its value over the common denominator. -/
private theorem gaussian_round_row_contains {G D : ℤ} (hG : 0 < G) (hD : 0 < D) (row : List ℤ) :
    List.Forall₂ (fun I x ↦ Analysis.IntegerInterval.Contains I G x) (gaussianRoundRow G D row)
      (row.map fun c ↦ (c : ℝ) / D) := by
  induction row with
  | nil => exact List.Forall₂.nil
  | cons c cs ih => exact List.Forall₂.cons (Analysis.roundedConstant_contains hG hD) ih

/-- Evaluate a denominator-cleared affine row at the exact local coordinate.
The row identity connects the rounded calculation to the original polynomial. -/
public theorem gaussian_affine_horner_contains {G D p d : ℤ} {o w : ℝ} (hG : 0 < G) (hD : 0 < D)
    (hd : 0 < d) (row : List ℤ) (P : Polynomial ℝ)
    (hrow :
      ((row.map fun c ↦ (c : ℝ) / D).foldr (fun c Q ↦ Polynomial.C c + Polynomial.X * Q) 0) =
        P.comp (Polynomial.X * Polynomial.C w + Polynomial.C o)) :
    (Analysis.intervalRatioHorner p d (gaussianRoundRow G D row)).Contains G
      (P.eval (((p : ℝ) / d) * w + o)) := by
  have h := gaussian_ratio_horner_contains (p := p) hG hd (gaussian_round_row_contains hG hD row)
  simpa only [hrow, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C] using h

/-- Build the integer coefficients of substitution by `a + w * X`.
The powers of both coordinates are computed once for the entire row. -/
@[expose]
public def gaussianAffineIntRow (N : ℕ) (a w : ℤ) (q : ℕ → ℤ) : Array ℤ :=
  let ap := Array.ofFn (fun j : Fin (N + 1) ↦ a ^ j.val)
  let wp := Array.ofFn (fun j : Fin (N + 1) ↦ w ^ j.val)
  Array.ofFn
    (fun i : Fin (N + 1) ↦
      (wp[i.val]?.getD 0) *
        ∑ j ∈ Finset.range (N + 1), q j * ((Nat.fast_choose j i.val : ℤ) * ap[j - i.val]?.getD 0))

/-- Each entry of an integer affine row equals the corresponding rational
coefficient multiplied by the common denominator of the source row. -/
public theorem gaussian_affine_int_coeff (P : Polynomial ℚ) (N : ℕ) (a w H : ℤ) (q : ℕ → ℤ)
    (hP : P.natDegree ≤ N) (hq : ∀ j ≤ N, (q j : ℚ) = (H : ℚ) * P.coeff j) {i : ℕ} (hi : i ≤ N) :
    ((gaussianAffineIntRow N a w q)[i]?.getD 0 : ℚ) =
      (H : ℚ) * (P.comp (Polynomial.C (w : ℚ) * Polynomial.X + Polynomial.C (a : ℚ))).coeff i := by
  have hi' := Nat.lt_succ_of_le hi
  rw [Analysis.rational_affine_coeff P N hP (a : ℚ) (w : ℚ) i]
  simp only [gaussianAffineIntRow, Array.getElem?_ofFn, dite_eq_left hi', Option.getD_some,
    Int.cast_mul, Int.cast_sum, Int.cast_pow, Finset.mul_sum, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hji := (Nat.sub_le j i).trans_lt hj'
  simp only [dite_eq_left hji, Option.getD_some, Int.cast_pow, hq j (Nat.le_of_lt_succ hj')]
  ring

/-- Clear the common coordinate denominator before integer affine substitution.
The returned numerators have the additional common factor `d^N`. -/
@[expose]
public def gaussianAffineRatioRow (N : ℕ) (a w d : ℤ) (q : ℕ → ℤ) : Array ℤ :=
  let dp := Array.ofFn (fun j : Fin (N + 1) ↦ d ^ j.val)
  let cleared := Array.ofFn (fun j : Fin (N + 1) ↦ q j.val * dp[N - j.val]?.getD 0)
  gaussianAffineIntRow N a w (fun j ↦ cleared[j]?.getD 0)

/-- Combine the denominator powers of the two local coordinates. -/
private theorem gaussian_affine_ratio_term (a w d : ℚ) (hd : d ≠ 0) {i j N : ℕ} (hij : i ≤ j)
    (hj : j ≤ N) :
    d ^ N * ((w / d) ^ i * (a / d) ^ (j - i)) = d ^ (N - j) * (w ^ i * a ^ (j - i)) := by
  rw [div_pow, div_pow, div_mul_div_comm, ← pow_add, Nat.add_sub_cancel' hij, ← mul_div_assoc,
    show d ^ N = d ^ (N - j) * d ^ j by rw [← pow_add, Nat.sub_add_cancel hj]]
  rw [show
      d ^ (N - j) * d ^ j * (w ^ i * a ^ (j - i)) = (d ^ (N - j) * (w ^ i * a ^ (j - i))) * d ^ j by
      ring]
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ hd)

/-- Row coefficients for a rational affine coordinate agree after multiplying
by the source denominator and the degree power of the coordinate denominator. -/
public theorem gaussian_affine_ratio_coeff (P : Polynomial ℚ) (N : ℕ) (a w d H : ℤ) (q : ℕ → ℤ)
    (hd : d ≠ 0) (hP : P.natDegree ≤ N) (hq : ∀ j ≤ N, (q j : ℚ) = (H : ℚ) * P.coeff j) {i : ℕ}
    (hi : i ≤ N) :
    ((gaussianAffineRatioRow N a w d q)[i]?.getD 0 : ℚ) =
      ((H : ℚ) * (d : ℚ) ^ N) *
        (P.comp (Polynomial.C ((w : ℚ) / d) * Polynomial.X + Polynomial.C ((a : ℚ) / d))).coeff
          i := by
  have hi' := Nat.lt_succ_of_le hi
  rw [Analysis.rational_affine_coeff P N hP ((a : ℚ) / d) ((w : ℚ) / d) i]
  simp only [gaussianAffineRatioRow, gaussianAffineIntRow, Array.getElem?_ofFn, dite_eq_left hi',
    Option.getD_some, Int.cast_mul, Int.cast_sum, Int.cast_pow, Finset.mul_sum, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hji := (Nat.sub_le j i).trans_lt (Nat.lt_succ_of_le hj')
  have hdj := (Nat.sub_le N j).trans_lt (Nat.lt_succ_self N)
  simp only [dite_eq_left (Nat.lt_succ_of_le hj'), dite_eq_left hji, dite_eq_left hdj,
    Option.getD_some, Int.cast_mul, Int.cast_pow, hq j hj']
  by_cases hij : i ≤ j
  · have h := gaussian_affine_ratio_term (a : ℚ) w d (Int.cast_ne_zero.mpr hd) hij hj'
    calc
      _ =
          (↑H * P.coeff j * (Nat.fast_choose j i : ℚ)) *
            ((d : ℚ) ^ (N - j) * ((w : ℚ) ^ i * (a : ℚ) ^ (j - i))) :=
        by ring
      _ = _ := by
        rw [← h]; ring
  · rw [← Nat.choose_eq_fast_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hij)]
    simp only [Nat.cast_zero, zero_mul, mul_zero]

/-- A checked integer margin gives a lower bound on the real residual
throughout a cell. The separately rounded loss must bound the chord penalty. -/
public theorem gaussian_mid_ticks_lower {m : ℕ} {a c x s b β : ℝ} {G l u M loss target : ℤ}
    (hG : 0 < G) (hM : 0 ≤ M) (r : Fin m → ℝ) (P : Fin m → Polynomial ℝ) (hx : x ∈ Set.Icc a c)
    (hl : (l : ℝ) / G ≤ gaussianMidResidual s b β r P a)
    (hu : (u : ℝ) / G ≤ gaussianMidResidual s b β r P c)
    (hc : ∀ y ∈ Set.Ioo a c, gaussianMidResidualCurv s β r P y ≤ (M : ℝ) / G)
    (hLoss : (M : ℝ) / G * (c - a) ^ 2 / 8 ≤ (loss : ℝ) / G) (hcheck : target < min l u - loss) :
    (target : ℝ) / G < gaussianMidResidual s b β r P x := by
  have hg : (0 : ℝ) < G := Int.cast_pos.mpr hG
  have hm : (0 : ℝ) ≤ M := Int.cast_nonneg_iff.mpr hM
  have hcast : (target : ℝ) < min (l : ℝ) (u : ℝ) - (loss : ℝ) := by
    simpa only [Int.cast_sub, Int.cast_min] using (Int.cast_lt (R := ℝ)).mpr hcheck
  have hmargin := (div_lt_div_iff_of_pos_right hg).mpr hcast
  rw [sub_div, ← min_div_div_right hg.le] at hmargin
  refine hmargin.trans_le ((sub_le_sub_left hLoss _).trans ?_)
  exact
    Analysis.cell_lower_of_curvature hx (div_nonneg hm hg.le)
      (fun y _ ↦ (gaussian_mid_residual_deriv s b β r P y).continuousAt.continuousWithinAt)
      (fun y _ ↦ gaussian_mid_residual_deriv s b β r P y)
      (fun y _ ↦ gaussian_mid_residual_curv s β r P y) hc ((min_le_left _ _).trans hl)
      ((min_le_right _ _).trans hu)

/-- The upper endpoint of the exact-ratio rounding bounds the scaled
curvature loss in the integer cell comparison. -/
public theorem gaussian_mid_rounded_loss {G M p d : ℤ} {a c : ℝ} (hG : 0 < G) (hd : 0 < d)
    (h : (p : ℝ) / d = (c - a) ^ 2 / 8) :
    (M : ℝ) / G * (c - a) ^ 2 / 8 ≤
      (((Analysis.IntegerInterval.mk M M).scaleRatio p d).upper : ℝ) / G := by
  have hm : (Analysis.IntegerInterval.mk M M).Contains G ((M : ℝ) / G) := ⟨le_rfl, le_rfl⟩
  have hu := (Analysis.IntegerInterval.scaleRatio_contains (p := p) hG hd hm).2
  rw [mul_comm (p : ℝ), mul_div_assoc, h, ← mul_div_assoc] at hu
  exact hu

/-- The fixed-point endpoint margin subtracts upper ticks for the costs
from lower ticks for the conductor contribution and intercept. -/
@[expose]
public def gaussianMidEndpointTicks {m : ℕ} (s b Q : ℤ) (T : Fin m → ℤ) : ℤ :=
  s + b - Q - ∑ i, T i

/-- A normalized decay factor and an inversely normalized polynomial value
enclose their original product at the working scale. -/
public theorem gaussian_mid_cost_contains {G : ℤ} {E V : Analysis.IntegerInterval} {k r x v : ℝ}
    (hG : 0 < G) (hk : k ≠ 0) (he : E.Contains G (k * Real.exp (-r * x)))
    (hv : V.Contains G (v / k)) :
    (Analysis.roundedProduct G E V).Contains G (Real.exp (-r * x) * v) := by
  have h := Analysis.roundedProduct_contains hG he hv
  rw [← mul_div_assoc, mul_assoc k, mul_comm k, mul_div_cancel_right₀ _ hk] at h
  exact h

/-- Integer endpoint ticks bound the analytic residual from below, provided
each of the four groups of ticks has its stated real bound. -/
public theorem gaussian_mid_endpoint_ticks_le {m : ℕ} {G S B Q : ℤ} {s b β x : ℝ} (r : Fin m → ℝ)
    (P : Fin m → Polynomial ℝ) (T : Fin m → ℤ) (hs : (S : ℝ) / G ≤ s * Real.exp (x / 2))
    (hb : (B : ℝ) / G ≤ b) (hq : (β / 4) * x ^ 2 ≤ (Q : ℝ) / G)
    (ht : ∀ i, Real.exp (-r i * x) * (P i).eval x ≤ (T i : ℝ) / G) :
    (gaussianMidEndpointTicks S B Q T : ℝ) / G ≤ gaussianMidResidual s b β r P x := by
  simp only [gaussianMidEndpointTicks, Int.cast_sub, Int.cast_add, Int.cast_sum, sub_div, add_div,
    Finset.sum_div, gaussianMidResidual, gaussianDecaySum]
  exact sub_le_sub (sub_le_sub (add_le_add hs hb) hq) (Finset.sum_le_sum fun i _ ↦ ht i)

/-- Compute an upper enclosure for a nonnegative Horner majorant.
Only the upward rounded endpoint is needed for the curvature penalty. -/
@[expose]
public def gaussianAbsHorner (p d : ℤ) (row : List ℤ) : ℤ :=
  row.foldr (fun c acc ↦ c + (Analysis.roundInterval d (acc * p) (acc * p)).upper) 0

/-- Absolute bounds on the coefficients and a nonnegative exact argument
bound the absolute value of the signed Horner evaluation. -/
public theorem gaussian_abs_horner_le {G p d : ℤ} {row : List ℤ} {coeff : List ℝ} {t : ℝ}
    (hG : 0 < G) (hp : 0 ≤ p) (hd : 0 < d) (ht₀ : 0 ≤ t) (ht₁ : t ≤ (p : ℝ) / d)
    (h : List.Forall₂ (fun (c : ℤ) (x : ℝ) ↦ |x| ≤ (c : ℝ) / G) row coeff) :
    |coeff.foldr (fun c acc ↦ c + t * acc) 0| ≤ (gaussianAbsHorner p d row : ℝ) / G := by
  induction h with
  | nil => simp only [List.foldr_nil, gaussianAbsHorner, abs_zero, Int.cast_zero, zero_div, le_refl]
  | @cons c x cs xs hc _ ih =>
    let m := gaussianAbsHorner p d cs
    have hm : (Analysis.IntegerInterval.mk m m).Contains G ((m : ℝ) / G) := ⟨le_rfl, le_rfl⟩
    have hh := (Analysis.IntegerInterval.scaleRatio_contains (p := p) hG hd hm).2
    have hdr : (0 : ℝ) < d := Int.cast_pos.mpr hd
    have hpr : (0 : ℝ) ≤ p := Int.cast_nonneg_iff.mpr hp
    have ht := mul_le_mul ht₁ ih (abs_nonneg _) (div_nonneg hpr hdr.le)
    have hz :
      |t * xs.foldr (fun c acc ↦ c + t * acc) 0| ≤
        (((Analysis.IntegerInterval.mk m m).scaleRatio p d).upper : ℝ) / G := by
      rw [abs_mul, abs_of_nonneg ht₀]
      rw [div_mul_eq_mul_div] at ht
      exact ht.trans hh
    rw [List.foldr_cons]
    refine ((abs_add_le _ _).trans (add_le_add hc hz)).trans ?_
    simp only [gaussianAbsHorner, List.foldr_cons, Int.cast_add, add_div, m,
      Analysis.IntegerInterval.scaleRatio, Analysis.IntegerInterval.scale, ite_eq_left hp,
      mul_comm (p : ℤ), le_refl]

/-- Round a fixed-point product upwards when only an upper bound is needed. -/
@[expose]
public def gaussianUpperProduct (G E B : ℤ) : ℤ :=
  (Analysis.roundInterval G (E * B) (E * B)).upper

/-- Multiply the left exponential cap and the absolute polynomial cap,
cancelling the common normalization before comparison with the signed term. -/
private theorem gaussian_curvature_term_le {G E B : ℤ} {k r a x v : ℝ} (hG : 0 < G) (hk : 0 < k)
    (hr : 0 ≤ r) (ha : a ≤ x) (he : k * Real.exp (-r * a) ≤ (E : ℝ) / G)
    (hv : |v / k| ≤ (B : ℝ) / G) :
    -(Real.exp (-r * x) * v) ≤ (gaussianUpperProduct G E B : ℝ) / G := by
  have hx := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ha (neg_nonpos.mpr hr))
  have he' := (mul_le_mul_of_nonneg_left hx hk.le).trans he
  have he₀ := (mul_pos hk (Real.exp_pos _)).le.trans he'
  have hm := mul_le_mul he' hv (abs_nonneg _) he₀
  rw [abs_div, abs_of_pos hk, ← mul_div_assoc,
    show k * Real.exp (-r * x) * |v| = Real.exp (-r * x) * |v| * k by ring,
    mul_div_cancel_right₀ _ hk.ne'] at hm
  have hp := mul_le_mul_of_nonneg_left (neg_le_abs v) (Real.exp_pos (-r * x)).le
  rw [mul_neg] at hp
  have hi : (Analysis.IntegerInterval.mk B B).Contains G ((B : ℝ) / G) := ⟨le_rfl, le_rfl⟩
  have hu := (Analysis.IntegerInterval.scaleRatio_contains (p := E) hG hG hi).2
  rw [div_mul_div_comm] at hm
  rw [← mul_div_assoc, div_div] at hu
  refine hp.trans (hm.trans ?_)
  by_cases hE : 0 ≤ E
  · simpa only [Analysis.IntegerInterval.scaleRatio, Analysis.IntegerInterval.scale, ite_eq_left hE,
      gaussianUpperProduct] using hu
  · simpa only [Analysis.IntegerInterval.scaleRatio, Analysis.IntegerInterval.scale,
      ite_eq_right hE, gaussianUpperProduct] using hu

/-- Upper-rounded normalized term products bound the signed residual curvature
everywhere to the right of the cell's left endpoint, given the polynomial caps. -/
public theorem gaussian_mid_curv_le_ticks {m : ℕ} {G : ℤ} {s β a x : ℝ} (hG : 0 < G) (hs : s ≤ 0)
    (hβ : 0 ≤ β) (ha : a ≤ x) (r k : Fin m → ℝ) (P : Fin m → Polynomial ℝ) (E B : Fin m → ℤ)
    (hk : ∀ i, 0 < k i) (hr : ∀ i, 0 ≤ r i) (he : ∀ i, k i * Real.exp (-r i * a) ≤ (E i : ℝ) / G)
    (hv :
      ∀ i,
        |(gaussianDecayDeriv (r i) (gaussianDecayDeriv (r i) (P i))).eval x / k i| ≤
          (B i : ℝ) / G) :
    gaussianMidResidualCurv s β r P x ≤
      ((∑ i, gaussianUpperProduct G (E i) (B i) : ℤ) : ℝ) / G := by
  refine (gaussian_mid_curv_le_decay hs hβ r P x).trans ?_
  rw [gaussianDecaySum, ← Finset.sum_neg_distrib, Int.cast_sum, Finset.sum_div]
  exact Finset.sum_le_sum fun i _ ↦ gaussian_curvature_term_le hG (hk i) (hr i) ha (he i) (hv i)

/-- Reconstruct original-coordinate curvature from a polynomial in the
local coordinate. The factors of `w⁻¹` implement the chain rule. -/
@[expose]
public noncomputable def gaussianLocalCurv (Q : Polynomial ℝ) (r w : ℝ) : Polynomial ℝ :=
  Polynomial.C (r ^ 2) * Q - Polynomial.C (2 * r / w) * Q.derivative +
    Polynomial.C (1 / w ^ 2) * Q.derivative.derivative

/-- The coefficient is the sum of the three adjacent contributions used
in the fixed-point curvature row. -/
public theorem gaussian_local_curv_coeff (Q : Polynomial ℝ) (r w : ℝ) (i : ℕ) :
    (gaussianLocalCurv Q r w).coeff i =
      r ^ 2 * Q.coeff i - (2 * r / w) * ((i + 1 : ℕ) : ℝ) * Q.coeff (i + 1) +
        (1 / w ^ 2) * ((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ) * Q.coeff (i + 2) := by
  simp only [gaussianLocalCurv, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one]
  ring

/-- The derivative of the affine argument is the constant width. -/
private theorem gaussian_affine_deriv (o w : ℝ) :
    (Polynomial.X * Polynomial.C w + Polynomial.C o).derivative = Polynomial.C w := by
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_C, mul_zero, one_mul, add_zero]

/-- Local curvature after an affine substitution evaluates to the original
decay curvature. The width must be nonzero to undo the chain-rule factors. -/
public theorem gaussian_local_curv_eval (P : Polynomial ℝ) (r o w t : ℝ) (hw : w ≠ 0) :
    (gaussianLocalCurv (P.comp (Polynomial.X * Polynomial.C w + Polynomial.C o)) r w).eval t =
      (gaussianDecayDeriv r (gaussianDecayDeriv r P)).eval (t * w + o) := by
  simp only [gaussianLocalCurv, gaussian_decay_deriv_twice, Polynomial.derivative_comp,
    gaussian_affine_deriv, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_comp]
  have hc := div_mul_cancel₀ (2 * r) hw
  have hh := div_mul_cancel₀ (1 : ℝ) (pow_ne_zero 2 hw)
  calc
    _ =
        r ^ 2 * P.eval (t * w + o) - ((2 * r / w) * w) * P.derivative.eval (t * w + o) +
          ((1 / w ^ 2) * w ^ 2) * P.derivative.derivative.eval (t * w + o) :=
      by ring
    _ = _ := by
      rw [hc, hh]; ring

/-- Bound the absolute coefficient using the two endpoints of its interval. -/
@[expose]
public def gaussianAbsTick (I : Analysis.IntegerInterval) : ℤ :=
  max (I.lower.natAbs : ℤ) (I.upper.natAbs : ℤ)

/-- An enclosed real value has absolute value bounded by the absolute tick. -/
public theorem gaussian_abs_tick_le {G : ℤ} {I : Analysis.IntegerInterval} {x : ℝ} (hG : 0 < G)
    (hx : I.Contains G x) : |x| ≤ (gaussianAbsTick I : ℝ) / G := by
  have g : (0 : ℝ) < G := Int.cast_pos.mpr hG
  have hl₀ : -I.lower ≤ (I.lower.natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs] using neg_le_abs I.lower
  have hl : -I.lower ≤ gaussianAbsTick I :=
    hl₀.trans (le_max_left (I.lower.natAbs : ℤ) (I.upper.natAbs : ℤ))
  have hu₀ : I.upper ≤ (I.upper.natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs] using le_abs_self I.upper
  have hu : I.upper ≤ gaussianAbsTick I :=
    hu₀.trans (le_max_right (I.lower.natAbs : ℤ) (I.upper.natAbs : ℤ))
  have hcl := (Int.cast_le (R := ℝ)).mpr hl
  rw [Int.cast_neg] at hcl
  exact
    abs_le.mpr
      ⟨(neg_le.mpr
              (by
                rw [← neg_div]
                exact div_le_div_of_nonneg_right hcl g.le)).trans
          hx.1,
        hx.2.trans (div_le_div_of_nonneg_right ((Int.cast_le (R := ℝ)).mpr hu) g.le)⟩

/-- Compute the absolute tick for a curvature coefficient from three
enclosed source coefficients and their exact signed multiplier ratios. -/
@[expose]
public def gaussianCurvAbsTick (a b c d e f : ℤ) (I J K : Analysis.IntegerInterval) : ℤ :=
  gaussianAbsTick ((I.scaleRatio a b).add ((J.scaleRatio c d).add (K.scaleRatio e f)))

/-- The computed tick majorizes the weighted coefficient sum in absolute value.
The three denominators and the common fixed-point scale must be positive. -/
public theorem gaussian_curv_abs_tick_le {G a b c d e f : ℤ} {I J K : Analysis.IntegerInterval}
    {x y z : ℝ} (hG : 0 < G) (hb : 0 < b) (hd : 0 < d) (hf : 0 < f) (hx : I.Contains G x)
    (hy : J.Contains G y) (hz : K.Contains G z) :
    |(a : ℝ) * x / b + ((c : ℝ) * y / d + (e : ℝ) * z / f)| ≤
      (gaussianCurvAbsTick a b c d e f I J K : ℝ) / G := by
  exact
    gaussian_abs_tick_le hG
      (Analysis.IntegerInterval.add_contains (Analysis.IntegerInterval.scaleRatio_contains hG hb hx)
        (Analysis.IntegerInterval.add_contains
          (Analysis.IntegerInterval.scaleRatio_contains hG hd hy)
          (Analysis.IntegerInterval.scaleRatio_contains hG hf hz)))

/-- Horner evaluation of an indexed coefficient row equals its power sum. -/
private theorem gaussian_horner_ofFn (t : ℝ) (n : ℕ) (q : ℕ → ℝ) :
    (List.ofFn (fun i : Fin n ↦ q i.val)).foldr (fun c acc ↦ c + t * acc) 0 =
      ∑ j ∈ Finset.range n, q j * t ^ j := by
  induction n generalizing q with
  | zero => simp only [List.ofFn_zero, List.foldr_nil, Finset.sum_range_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.foldr_cons, Finset.sum_range_succ']
    simp only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
    rw [ih (fun j ↦ q (j + 1)), Finset.mul_sum,
      add_comm (∑ j ∈ Finset.range n, q (j + 1) * t ^ (j + 1)) (q 0)]
    apply congrArg (q 0 + ·)
    exact
      Finset.sum_congr rfl
        (fun j _ ↦ by
          rw [pow_succ]; ring)

/-- Absolute ticks for all coefficients up to a degree bound give a
fixed-point upper bound for the absolute value of the polynomial. -/
public theorem gaussian_abs_horner_poly {G p d : ℤ} {N : ℕ} {t : ℝ} (hG : 0 < G) (hp : 0 ≤ p)
    (hd : 0 < d) (ht₀ : 0 ≤ t) (ht₁ : t ≤ (p : ℝ) / d) (Q : Polynomial ℝ) (hQ : Q.natDegree < N)
    (u : Fin N → ℤ) (h : ∀ i, |Q.coeff i.val| ≤ (u i : ℝ) / G) :
    |Q.eval t| ≤ (gaussianAbsHorner p d (List.ofFn u) : ℝ) / G := by
  have hh :
    List.Forall₂ (fun (c : ℤ) (x : ℝ) ↦ |x| ≤ (c : ℝ) / G) (List.ofFn u)
      (List.ofFn (fun i : Fin N ↦ Q.coeff i.val)) := by
    apply List.forall₂_iff_get.mpr
    simp only [List.length_ofFn, List.get_ofFn, true_and]
    exact fun i hi _ ↦ h ⟨i, by simpa only [List.length_ofFn] using hi⟩
  have hbound := gaussian_abs_horner_le hG hp hd ht₀ ht₁ hh
  rw [gaussian_horner_ofFn, ← Polynomial.eval_eq_sum_range' hQ] at hbound
  exact hbound

/-- A checked local curvature row bounds the original decay curvature
at every local coordinate between zero and the rational scan endpoint. -/
public theorem gaussian_curv_horner_poly {G p d : ℤ} {N : ℕ} {r o w t : ℝ} (hG : 0 < G) (hp : 0 ≤ p)
    (hd : 0 < d) (ht₀ : 0 ≤ t) (ht₁ : t ≤ (p : ℝ) / d) (P : Polynomial ℝ) (hw : w ≠ 0)
    (Q : Polynomial ℝ)
    (hQ : Q = gaussianLocalCurv (P.comp (Polynomial.X * Polynomial.C w + Polynomial.C o)) r w)
    (hN : Q.natDegree < N) (u : Fin N → ℤ) (hu : ∀ i, |Q.coeff i.val| ≤ (u i : ℝ) / G) :
    |(gaussianDecayDeriv r (gaussianDecayDeriv r P)).eval (t * w + o)| ≤
      (gaussianAbsHorner p d (List.ofFn u) : ℝ) / G := by
  have h := gaussian_abs_horner_poly hG hp hd ht₀ ht₁ Q hN u hu
  rw [hQ, gaussian_local_curv_eval P r o w t hw] at h
  exact h

/-- Compute one absolute curvature tick directly from the integer rate and
width ratios, without reducing a rational number for each coefficient. -/
@[expose]
public def gaussianCurvRowTick (rn rd wn wd : ℤ) (row : Array Analysis.IntegerInterval) (j : ℕ) :
    ℤ :=
  let i := (j : ℤ) + 1
  gaussianCurvAbsTick (rn ^ 2) (rd ^ 2) (-2 * rn * i * wd) (rd * wn) (i * (i + 1) * wd ^ 2) (wn ^ 2)
    (row[j]?.getD ⟨0, 0⟩) (row[j + 1]?.getD ⟨0, 0⟩) (row[j + 2]?.getD ⟨0, 0⟩)

/-- The three raw integer ratios give the corresponding local curvature
coefficient. Source coefficient bounds may include zero padding. -/
public theorem gaussian_curv_row_tick_le {G rn rd wn wd : ℤ} (hG : 0 < G) (hrd : 0 < rd)
    (hwn : 0 < wn) (hwd : 0 < wd) (row : Array Analysis.IntegerInterval) (Q : Polynomial ℝ) (j : ℕ)
    (h : ∀ i : ℕ, Analysis.IntegerInterval.Contains (row[i]?.getD ⟨0, 0⟩) G (Q.coeff i)) :
    |(gaussianLocalCurv Q ((rn : ℝ) / rd) ((wn : ℝ) / wd)).coeff j| ≤
      (gaussianCurvRowTick rn rd wn wd row j : ℝ) / G := by
  have ht :=
    gaussian_curv_abs_tick_le (a := rn ^ 2) (c := -2 * rn * ((j : ℤ) + 1) * wd) (e :=
      ((j : ℤ) + 1) * ((j : ℤ) + 1 + 1) * wd ^ 2) hG (pow_pos hrd 2) (mul_pos hrd hwn)
      (pow_pos hwn 2) (h j) (h (j + 1)) (h (j + 2))
  rw [gaussian_local_curv_coeff]
  have hr : (rd : ℝ) ≠ 0 := (Int.cast_pos.mpr hrd : (0 : ℝ) < rd).ne'
  have hw : (wn : ℝ) ≠ 0 := (Int.cast_pos.mpr hwn : (0 : ℝ) < wn).ne'
  have hd : (wd : ℝ) ≠ 0 := (Int.cast_pos.mpr hwd : (0 : ℝ) < wd).ne'
  convert ht using 2
  · simp only [Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_natCast, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp (disch :=
      first
      | exact hr
      | exact hw
      | exact hd)
    ring
  · rfl

/-- Evaluate the absolute curvature enclosure of a shared source row on
all local coordinates up to the certified right endpoint. -/
public theorem gaussian_curv_row_eval_le {G rn rd wn wd p d : ℤ} {N : ℕ} {t : ℝ} (hG : 0 < G)
    (hrd : 0 < rd) (hwn : 0 < wn) (hwd : 0 < wd) (hp : 0 ≤ p) (hd : 0 < d) (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ (p : ℝ) / d) (row : Array Analysis.IntegerInterval) (Q : Polynomial ℝ)
    (hN : (gaussianLocalCurv Q ((rn : ℝ) / rd) ((wn : ℝ) / wd)).natDegree < N)
    (h : ∀ i : ℕ, Analysis.IntegerInterval.Contains (row[i]?.getD ⟨0, 0⟩) G (Q.coeff i)) :
    |(gaussianLocalCurv Q ((rn : ℝ) / rd) ((wn : ℝ) / wd)).eval t| ≤
      (gaussianAbsHorner p d (List.ofFn fun i : Fin N ↦ gaussianCurvRowTick rn rd wn wd row i.val) :
          ℝ) /
        G := by
  exact
    gaussian_abs_horner_poly hG hp hd ht₀ ht₁ _ hN _
      (fun i ↦ gaussian_curv_row_tick_le hG hrd hwn hwd row Q i.val h)

/-- Round the integer affine numerators at scale `G`, retaining indexed
access to the complete enclosure row for the curvature calculation. -/
@[expose]
public def gaussianAffineRound (G H k : ℤ) (N : ℕ) (a w d : ℤ) (q : ℕ → ℤ) :
    Array Analysis.IntegerInterval :=
  (gaussianAffineRatioRow N a w d q).map (fun c ↦ Analysis.roundedConstant G c (H * d ^ N * k))

/-- The shared integer row encloses each normalized affine coefficient,
including the zero coefficients beyond the degree bound. -/
public theorem gaussian_affine_round_contains (P : Polynomial ℚ) (N : ℕ) (a w d H k G : ℤ)
    (q : ℕ → ℤ) (hd : 0 < d) (hH : 0 < H) (hk : 0 < k) (hG : 0 < G) (hP : P.natDegree ≤ N)
    (hq : ∀ j ≤ N, (q j : ℚ) = (H : ℚ) * P.coeff j) (A : Polynomial ℚ)
    (hA : A = P.comp (Polynomial.C ((w : ℚ) / d) * Polynomial.X + Polynomial.C ((a : ℚ) / d)))
    (hN : A.natDegree ≤ N) (i : ℕ) :
    Analysis.IntegerInterval.Contains ((gaussianAffineRound G H k N a w d q)[i]?.getD ⟨0, 0⟩) G
      ((A.coeff i : ℝ) / k) := by
  have hD := mul_pos hH (pow_pos hd N)
  by_cases hi : i ≤ N
  · have hi' := Nat.lt_succ_of_le hi
    have hc := gaussian_affine_ratio_coeff P N a w d H q hd.ne' hP hq hi
    rw [← hA] at hc
    have he :
      (↑((gaussianAffineRatioRow N a w d q)[i]?.getD 0) : ℝ) =
        ((H : ℝ) * (d : ℝ) ^ N) * (A.coeff i : ℝ) := by
      have h := congrArg (fun x : ℚ ↦ (x : ℝ)) hc
      simpa only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_pow] using h
    have hh :=
      Analysis.roundedConstant_contains (p := (gaussianAffineRatioRow N a w d q)[i]?.getD 0) hG
        (mul_pos hD hk)
    have hDr : (H : ℝ) * (d : ℝ) ^ N ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hH.ne') (pow_ne_zero _ (Int.cast_ne_zero.mpr hd.ne'))
    rw [he, Int.cast_mul, Int.cast_mul, Int.cast_pow, mul_div_mul_left _ _ hDr] at hh
    simpa only [gaussianAffineRound, gaussianAffineRatioRow, gaussianAffineIntRow,
      Array.getElem?_map, Array.getElem?_ofFn, dite_eq_left hi', Option.map_some,
      Option.getD_some] using hh
  · have hn := Nat.lt_of_not_ge hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hN.trans_lt hn)]
    simp only [gaussianAffineRound, gaussianAffineRatioRow, gaussianAffineIntRow,
      Array.getElem?_map, Array.getElem?_ofFn,
      dite_eq_right (Nat.not_lt.mpr (Nat.succ_le_of_lt hn)), Option.map_none, Option.getD_none,
      Rat.cast_zero, zero_div, Analysis.IntegerInterval.Contains, Int.cast_zero, le_refl, and_self]

/-- Multiplying a profile by a constant commutes with the decay derivative. -/
private theorem gaussian_decay_deriv_C_mul (r k : ℝ) (P : Polynomial ℝ) :
    gaussianDecayDeriv r (Polynomial.C k * P) = Polynomial.C k * gaussianDecayDeriv r P := by
  simp only [gaussianDecayDeriv, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul,
    zero_add]
  ring

/-- A normalized local curvature row bounds the original decay curvature
divided by the same positive normalizing constant. -/
public theorem gaussian_normal_curv_eval (P : Polynomial ℝ) (k r o w t : ℝ) (hw : w ≠ 0) :
    (gaussianLocalCurv
            ((Polynomial.C k⁻¹ * P).comp (Polynomial.X * Polynomial.C w + Polynomial.C o)) r w).eval
        t =
      (gaussianDecayDeriv r (gaussianDecayDeriv r P)).eval (t * w + o) / k := by
  rw [gaussian_local_curv_eval _ r o w t hw, gaussian_decay_deriv_C_mul, gaussian_decay_deriv_C_mul,
    Polynomial.eval_mul, Polynomial.eval_C, inv_mul_eq_div]

/-- Taking local curvature preserves the degree bound of its source polynomial. -/
public theorem gaussian_local_curv_degree (Q : Polynomial ℝ) (r w : ℝ) :
    (gaussianLocalCurv Q r w).natDegree ≤ Q.natDegree := by
  have hd := (Polynomial.natDegree_derivative_le Q).trans (Nat.sub_le _ _)
  have hdd := ((Polynomial.natDegree_derivative_le Q.derivative).trans (Nat.sub_le _ _)).trans hd
  have hC := (Polynomial.natDegree_C_mul_le (r ^ 2) Q)
  have hD := (Polynomial.natDegree_C_mul_le (2 * r / w) Q.derivative).trans hd
  have hDD := (Polynomial.natDegree_C_mul_le (1 / w ^ 2) Q.derivative.derivative).trans hdd
  exact
    Polynomial.natDegree_add_le_of_degree_le
      ((Polynomial.natDegree_sub_le_of_le hC hD).trans (max_le le_rfl le_rfl)) hDD

/-- Map the rational affine row to the corresponding normalized real profile. -/
public theorem gaussian_affine_round_real (P : Polynomial ℚ) (N : ℕ) (a w d H k G : ℤ) (q : ℕ → ℤ)
    (hd : 0 < d) (hH : 0 < H) (hk : 0 < k) (hG : 0 < G) (hP : P.natDegree ≤ N)
    (hq : ∀ j ≤ N, (q j : ℚ) = (H : ℚ) * P.coeff j) (A : Polynomial ℚ)
    (hA : A = P.comp (Polynomial.C ((w : ℚ) / d) * Polynomial.X + Polynomial.C ((a : ℚ) / d)))
    (hN : A.natDegree ≤ N) (i : ℕ) :
    Analysis.IntegerInterval.Contains ((gaussianAffineRound G H k N a w d q)[i]?.getD ⟨0, 0⟩) G
      (((Polynomial.C ((k : ℝ)⁻¹) * P.map (Rat.castHom ℝ)).comp
            (Polynomial.X * Polynomial.C ((w : ℝ) / d) + Polynomial.C ((a : ℝ) / d))).coeff
        i) := by
  have h := gaussian_affine_round_contains P N a w d H k G q hd hH hk hG hP hq A hA hN i
  have hmap := congrArg (Polynomial.map (Rat.castHom ℝ)) hA
  simp only [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Rat.coe_castHom, Rat.cast_div, Rat.cast_intCast] at hmap
  rw [mul_comm Polynomial.X, Polynomial.C_mul_comp, ← hmap, Polynomial.coeff_C_mul,
    Polynomial.coeff_map, Rat.coe_castHom, inv_mul_eq_div]
  exact h

/-- Evaluate a shared array at one rational local coordinate. This is the
endpoint computation paired with the absolute curvature scan. -/
@[expose]
public def gaussianRowHorner (N : ℕ) (p d : ℤ) (row : Array Analysis.IntegerInterval) :
    Analysis.IntegerInterval :=
  Analysis.intervalRatioHorner p d (List.ofFn fun i : Fin N ↦ row[i.val]?.getD ⟨0, 0⟩)

/-- The indexed source enclosures give an enclosure for the polynomial at
the exact rational coordinate, using the same row as the curvature scan. -/
public theorem gaussian_row_horner_contains {G p d : ℤ} {N : ℕ} (hG : 0 < G) (hd : 0 < d)
    (row : Array Analysis.IntegerInterval) (Q : Polynomial ℝ) (hQ : Q.natDegree < N)
    (h : ∀ i : ℕ, Analysis.IntegerInterval.Contains (row[i]?.getD ⟨0, 0⟩) G (Q.coeff i)) :
    (gaussianRowHorner N p d row).Contains G (Q.eval ((p : ℝ) / d)) := by
  have hh :
    List.Forall₂ (fun I x ↦ Analysis.IntegerInterval.Contains I G x)
      (List.ofFn fun i : Fin N ↦ row[i.val]?.getD ⟨0, 0⟩)
      (List.ofFn fun i : Fin N ↦ Q.coeff i.val) := by
    apply List.forall₂_iff_get.mpr
    simp only [List.length_ofFn, List.get_ofFn, true_and]
    exact fun i _ _ ↦ h i
  have he := Analysis.interval_ratio_horner_contains (p := p) hG hd hh
  have heq :
    (fun c acc : ℝ ↦ c + (p : ℝ) * acc / d) = (fun c acc : ℝ ↦ c + ((p : ℝ) / d) * acc) := by
    funext c acc
    rw [div_mul_eq_mul_div]
  rw [heq, gaussian_horner_ofFn, ← Polynomial.eval_eq_sum_range' hQ] at he
  exact he

/-- The shared coordinate evaluation gives the normalized original profile
value used in the fixed-point endpoint product. -/
public theorem gaussian_normal_eval (P : Polynomial ℝ) (k o w t : ℝ) :
    ((Polynomial.C k⁻¹ * P).comp (Polynomial.X * Polynomial.C w + Polynomial.C o)).eval t =
      P.eval (t * w + o) / k := by
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, inv_mul_eq_div]

/-- Form a rational profile from its integer numerators and common denominator. -/
@[expose]
public noncomputable def gaussianIntProfile (N : ℕ) (H : ℤ) (q : ℕ → ℤ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (N + 1), Polynomial.monomial i ((q i : ℚ) / H)

/-- The profile's degree is bounded by the last index in its source row. -/
public theorem gaussian_int_profile_degree (N : ℕ) (H : ℤ) (q : ℕ → ℤ) :
    (gaussianIntProfile N H q).natDegree ≤ N := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- The common-denominator coefficient identity holds without reducing the
source integer array or evaluating the polynomial. -/
public theorem gaussian_int_profile_coeff (N : ℕ) (H : ℤ) (q : ℕ → ℤ) (hH : H ≠ 0) {i : ℕ}
    (hi : i ≤ N) : (q i : ℚ) = (H : ℚ) * (gaussianIntProfile N H q).coeff i := by
  rw [gaussianIntProfile, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial_apply]
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl, ← mul_div_assoc, mul_comm (H : ℚ),
      mul_div_cancel_right₀ _ (Int.cast_ne_zero.mpr hH)]
  · intro b _ hb
    rw [ite_eq_right hb]
  · exact fun hn ↦ False.elim (hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))

/-- An integer source row supplies both the endpoint enclosure and the
curvature enclosure in the shared affine coordinate. -/
public theorem gaussian_profile_row_bounds (N : ℕ) (G H k a w d rn rd : ℤ) (q : ℕ → ℤ) (hG : 0 < G)
    (hH : 0 < H) (hk : 0 < k) (hw : 0 < w) (hd : 0 < d) (hrd : 0 < rd) :
    let P := (gaussianIntProfile N H q).map (Rat.castHom ℝ)
    let row := gaussianAffineRound G H k N a w d q
    let o := (a : ℝ) / d
    let v := (w : ℝ) / d
    let r := (rn : ℝ) / rd
    (∀ (p e : ℤ),
        0 < e → (gaussianRowHorner (N + 1) p e row).Contains G (P.eval ((p : ℝ) / e * v + o) / k)) ∧
      (∀ (p e : ℤ) (t : ℝ),
        0 ≤ p →
          0 < e →
          0 ≤ t →
          t ≤ (p : ℝ) / e →
          |(gaussianDecayDeriv r (gaussianDecayDeriv r P)).eval (t * v + o) / k| ≤
            (gaussianAbsHorner p e
                  (List.ofFn fun i : Fin (N + 1) ↦ gaussianCurvRowTick rn rd w d row i.val) :
                ℝ) /
              G) := by
  let R := gaussianIntProfile N H q
  let P := R.map (Rat.castHom ℝ)
  let A := R.comp (Polynomial.C ((w : ℚ) / d) * Polynomial.X + Polynomial.C ((a : ℚ) / d))
  let Q :=
    (Polynomial.C ((k : ℝ)⁻¹) * P).comp
      (Polynomial.X * Polynomial.C ((w : ℝ) / d) + Polynomial.C ((a : ℝ) / d))
  let row := gaussianAffineRound G H k N a w d q
  have hR := gaussian_int_profile_degree N H q
  have hP : P.natDegree ≤ N := Polynomial.natDegree_map_le.trans hR
  have hA : A.natDegree ≤ N := by
    apply Polynomial.natDegree_comp_le.trans
    have hf :
      (Polynomial.C ((w : ℚ) / d) * Polynomial.X + Polynomial.C ((a : ℚ) / d)).natDegree ≤ 1 :=
      Polynomial.natDegree_add_le_of_degree_le
        (Polynomial.natDegree_C_mul_le ((w : ℚ) / d) Polynomial.X |>.trans
          Polynomial.natDegree_X.le)
        (by
          rw [Polynomial.natDegree_C]; exact Nat.zero_le 1)
    exact (Nat.mul_le_mul hR hf).trans_eq (Nat.mul_one N)
  have hQ : Q.natDegree ≤ N := by
    apply Polynomial.natDegree_comp_le.trans
    have hf :
      (Polynomial.X * Polynomial.C ((w : ℝ) / d) + Polynomial.C ((a : ℝ) / d)).natDegree ≤ 1 :=
      Polynomial.natDegree_add_le_of_degree_le
        (Polynomial.natDegree_mul_C_le Polynomial.X ((w : ℝ) / d) |>.trans
          Polynomial.natDegree_X.le)
        (by
          rw [Polynomial.natDegree_C]; exact Nat.zero_le 1)
    exact
      (Nat.mul_le_mul ((Polynomial.natDegree_C_mul_le _ P).trans hP) hf).trans_eq (Nat.mul_one N)
  have hc : ∀ i : ℕ, Analysis.IntegerInterval.Contains (row[i]?.getD ⟨0, 0⟩) G (Q.coeff i) :=
    gaussian_affine_round_real R N a w d H k G q hd hH hk hG hR
      (fun j hj ↦ gaussian_int_profile_coeff N H q hH.ne' hj) A rfl hA
  constructor
  · intro p e he
    have h := gaussian_row_horner_contains (p := p) hG he row Q (Nat.lt_succ_of_le hQ) hc
    rw [show Q.eval ((p : ℝ) / e) = P.eval ((p : ℝ) / e * ((w : ℝ) / d) + (a : ℝ) / d) / k from
        gaussian_normal_eval _ _ _ _ _] at h
    exact h
  · intro p e t hp he ht hte
    have hn := (gaussian_local_curv_degree Q ((rn : ℝ) / rd) ((w : ℝ) / d)).trans hQ
    have h := gaussian_curv_row_eval_le hG hrd hw hd hp he ht hte row Q (Nat.lt_succ_of_le hn) hc
    rw [show
        (gaussianLocalCurv Q ((rn : ℝ) / rd) ((w : ℝ) / d)).eval t =
          (gaussianDecayDeriv ((rn : ℝ) / rd) (gaussianDecayDeriv ((rn : ℝ) / rd) P)).eval
              (t * ((w : ℝ) / d) + (a : ℝ) / d) /
            k
        from
        gaussian_normal_curv_eval _ _ _ _ _ _
          (div_pos (Int.cast_pos.mpr hw) (Int.cast_pos.mpr hd)).ne'] at h
    exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
