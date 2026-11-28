/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms
public import PseudoPrime.Analysis.BernsteinCompensation
public import PseudoPrime.Analysis.BernsteinIntegral
import Mathlib.Tactic.Ring

/-! # Integer Bernstein conversion for middle Gaussian compensation -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Convert a power row to Bernstein form with common denominator `den * N!`. -/
@[expose]
public def MiddleIntRow.bernstein (r : MiddleIntRow) (N : ℕ) : MiddleIntRow :=
  ⟨r.den * (N.factorial : ℤ),
    Array.ofFn fun j : Fin (N + 1) ↦
      ∑ k ∈ Finset.range (N + 1),
        r.num k * (Nat.fast_choose j.val k : ℤ) * ((k.factorial : ℤ) * ((N - k).factorial : ℤ))⟩

/-- The reciprocal binomial coefficient is a ratio of factorials. -/
private theorem factorialRatio {N k : ℕ} (hk : k ≤ N) :
    ((k.factorial : ℚ) * ((N - k).factorial : ℚ)) / (N.factorial : ℚ) =
      1 / (Nat.fast_choose N k : ℚ) := by
  have h := congrArg (fun x : ℕ ↦ (x : ℚ)) (Nat.choose_mul_factorial_mul_factorial hk)
  simp only [Nat.cast_mul, Nat.choose_eq_fast_choose] at h
  have hN : (N.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hC : (Nat.fast_choose N k : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (by
        rw [← Nat.choose_eq_fast_choose]; exact (Nat.choose_pos hk).ne')
  apply (div_eq_div_iff hN hC).mpr
  rw [one_mul, ← h]
  ring

/-- Read the `i`-th Bernstein coefficient of the source polynomial from its integer row. -/
public theorem MiddleIntRow.bernstein_coeff (r : MiddleIntRow) {N i : ℕ} (hi : i ≤ N) :
    ((r.bernstein N).num i : ℚ) / (r.bernstein N).den =
      Analysis.bernsteinRatCoeff (r.poly N) N i := by
  have hi' := Nat.lt_succ_of_le hi
  simp only [MiddleIntRow.bernstein, MiddleIntRow.num, Array.getElem?_ofFn, dite_eq_left hi',
    Option.getD_some, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_div,
    Analysis.bernsteinRatCoeff]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [r.poly_coeff hk', mul_assoc, ← div_mul_div_comm, mul_div_assoc (i.fast_choose k : ℚ),
    factorialRatio hk', mul_one_div]
  rfl

/-- The integer Bernstein row on an affine cell represents the exact coefficients
of the source polynomial on the unit interval. -/
public theorem MiddleIntRow.affine_bernstein_coeff (r : MiddleIntRow) {N i : ℕ} (a w b : ℤ)
    (hi : i ≤ N) (hr : r.den ≠ 0) (hb : b ≠ 0) :
    let row := (r.affine N a w b).bernstein N
    (row.num i : ℚ) / row.den =
      Analysis.bernsteinRatCoeff
        ((r.poly N).comp (Polynomial.C ((w : ℚ) / b) * Polynomial.X + Polynomial.C ((a : ℚ) / b))) N
        i := by
  simpa only [r.poly_affine N a w b hr hb] using (r.affine N a w b).bernstein_coeff hi

/-- The width times the mean absolute Bernstein coefficient, calculated with
one integer sum and a shared denominator on the affine cell. -/
@[expose]
public def MiddleIntRow.absCellCharge (r : MiddleIntRow) (N : ℕ) (a w b : ℤ) : ℚ :=
  let row := (r.affine N a w b).bernstein N
  ((w : ℚ) / b) * ((∑ i ∈ Finset.range (N + 1), (row.num i).natAbs : ℕ) : ℚ) /
    ((row.den.natAbs : ℚ) * ((N : ℚ) + 1))

/-- The absolute Bernstein charge is nonnegative for every nonnegative cell width. -/
public theorem MiddleIntRow.abs_cell_nonneg (r : MiddleIntRow) (N : ℕ) (a w b : ℤ)
    (hw : 0 ≤ (w : ℚ) / b) : 0 ≤ r.absCellCharge N a w b := by
  exact
    div_nonneg (mul_nonneg hw (Nat.cast_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _) zero_le_one))

/-- The integer cell charge controls the absolute integral with an exponential
of either sign. The exponential is evaluated at the larger endpoint value. -/
public theorem MiddleIntRow.exp_abs_cell_le (r : MiddleIntRow) (N : ℕ) (a w b : ℤ) (hr : r.den ≠ 0)
    (hb : b ≠ 0) (hw : 0 < (w : ℚ) / b) (s : ℝ) :
    let l := ((a : ℚ) / b : ℚ)
    let d := ((w : ℚ) / b : ℚ)
    (∫ t in (l : ℝ)..((l + d : ℚ) : ℝ), Real.exp (s * t) * |(r.poly N).eval₂ (Rat.castHom ℝ) t|) ≤
      Real.exp (max (s * (l : ℝ)) (s * ((l + d : ℚ) : ℝ))) * (r.absCellCharge N a w b : ℝ) := by
  intro l d
  let row := (r.affine N a w b).bernstein N
  let c := fun i : Fin (N + 1) ↦ (((row.num i : ℚ) / row.den : ℚ) : ℝ)
  have hdeg : (r.poly N).natDegree ≤ N :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)
  have hwidth : ((l + d : ℚ) : ℝ) - (l : ℝ) = (d : ℝ) := by rw [Rat.cast_add, add_sub_cancel_left]
  have hlt : (l : ℝ) < ((l + d : ℚ) : ℝ) := by
    rw [← sub_pos, hwidth]
    exact Rat.cast_pos.mpr hw
  have hrep (x : Set.Icc (0 : ℝ) 1) :
    (r.poly N).eval₂ (Rat.castHom ℝ) ((((l + d : ℚ) : ℝ) - l) * x + l) =
      ∑ i : Fin (N + 1), c i * _root_.bernstein N i x := by
    have h := Analysis.bernstein_rat_affine_eval (r.poly N) N hdeg l (l + d) x
    rw [add_sub_cancel_left] at h
    rw [hwidth]
    refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    dsimp only [c, row]
    rw [r.affine_bernstein_coeff a w b (Nat.le_of_lt_succ i.isLt) hr hb]
  have h :=
    Analysis.exp_abs_bernstein_cell (a := s) _ (Polynomial.continuous_eval₂ _ _) hlt N c hrep
  rw [hwidth] at h
  refine h.trans_eq (congrArg (Real.exp (max (s * (l : ℝ)) (s * ((l + d : ℚ) : ℝ))) * ·) ?_)
  change
    (d : ℝ) * ((∑ i : Fin (N + 1), |(((row.num i : ℚ) / row.den : ℚ) : ℝ)|) / ((N : ℝ) + 1)) =
      ((d * ((∑ i ∈ Finset.range (N + 1), (row.num i).natAbs : ℕ) : ℚ) /
            ((row.den.natAbs : ℚ) * ((N : ℚ) + 1)) :
          ℚ) :
        ℝ)
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_add,
    Rat.cast_one, Nat.cast_sum, Nat.cast_natAbs, abs_div, ← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (f := fun i ↦ |(row.num i : ℝ)|)]
  simp only [Int.cast_abs, Rat.cast_sum, Rat.cast_abs, Rat.cast_intCast, div_eq_mul_inv, mul_inv]
  ring

/-- Read the clipped negative part of a Bernstein coefficient using its integer numerator. -/
@[expose]
public def MiddleIntRow.compensationCoeff (r : MiddleIntRow) (i : ℕ) : ℚ :=
  (max 0 (-r.num i) : ℤ) / (r.den : ℚ)

/-- A row with nonnegative denominator gives the exact clipped rational coefficient. -/
public theorem MiddleIntRow.compensation_coeff (r : MiddleIntRow) {N i : ℕ} (hi : i ≤ N)
    (hd : 0 ≤ (r.bernstein N).den) :
    (r.bernstein N).compensationCoeff i = max 0 (-Analysis.bernsteinRatCoeff (r.poly N) N i) := by
  rw [← r.bernstein_coeff hi]
  have h : (0 : ℚ) ≤ ((r.bernstein N).den : ℚ) := by exact_mod_cast hd
  simp only [MiddleIntRow.compensationCoeff, Int.cast_max, Int.cast_zero, Int.cast_neg,
    ← max_div_div_right h, zero_div, neg_div]

/-- For a positive-width cell, the clipped integer coefficients give a rational upper
bound for the exponentially weighted main compensation integral. -/
public theorem MiddleIntRow.compensation_main_le (r : MiddleIntRow) (N : ℕ) {l h s : ℚ} (hh : 0 < h)
    (hl : 0 ≤ l) (hs : 0 ≤ s) (hd : 0 ≤ (r.bernstein N).den) :
    (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
        Real.exp (-(s : ℝ) * v) *
          (Analysis.bernsteinCompensation (r.poly N) N).eval ((v - (l : ℝ)) / (h : ℝ))) ≤
      (↑(Analysis.compensationExpUpper (s * l) *
            Analysis.compensationMomentSum N 2 h s
              (fun i ↦ (r.bernstein N).compensationCoeff i.val)) :
        ℝ) := by
  have hN : (r.poly N).natDegree ≤ N :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)
  have he (i : Fin (N + 1)) := r.compensation_coeff (Nat.le_of_lt_succ i.isLt) hd
  simpa only [he] using Analysis.bernstein_compensation_rat_cell_le (r.poly N) N hN hh hl hs

/-- For a positive-width cell, the variation row gives a rational upper bound for
the weighted absolute variation of the same compensation polynomial. -/
public theorem MiddleIntRow.compensation_variation_le (r : MiddleIntRow) (N : ℕ) (d : ℚ) {l h s : ℚ}
    (hh : 0 < h) (hl : 0 ≤ l) (hs : 0 ≤ s) (hd : 0 ≤ (r.bernstein N).den) :
    let C := Analysis.bernsteinCompensation (r.poly N) N
    let u := fun v : ℝ ↦ (v - (l : ℝ)) / (h : ℝ)
    let c := (r.bernstein N).compensationCoeff
    (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
        Real.exp (-(s : ℝ) * v) * |(d : ℝ) * C.eval (u v) - (h : ℝ)⁻¹ * C.derivative.eval (u v)|) ≤
      (↑(Analysis.compensationExpUpper (s * l) *
            Analysis.compensationMomentSum N 1 h s
              (fun i ↦ |Analysis.bernsteinVariationDirect N i.val d h c|)) :
        ℝ) := by
  have he (i : Fin (N + 1)) :
    Analysis.bernsteinRatCoeff (Analysis.bernsteinRatVariation (r.poly N) N d h) N i.val =
      Analysis.bernsteinVariationDirect N i.val d h (r.bernstein N).compensationCoeff := by
    rw [Analysis.bernstein_variation_direct_eq, Analysis.bernsteinVariationDirect,
      Analysis.bernsteinVariationDirect, Analysis.bernsteinDerivativeCoeff,
      Analysis.bernsteinDerivativeCoeff]
    have hi := Nat.le_of_lt_succ i.isLt
    rw [← r.compensation_coeff hi hd, ← r.compensation_coeff ((Nat.sub_le i.val 1).trans hi) hd]
    by_cases h : i.val < N
    · rw [r.compensation_coeff (Nat.succ_le_of_lt h) hd]
    · rw [Nat.sub_eq_zero_of_le (le_of_not_gt h), Nat.cast_zero, zero_mul, zero_mul]
  simpa only [he] using Analysis.bernstein_variation_rat_cell_le (r.poly N) N d hh hl hs

/-- Nonnegative Bernstein numerators give zero compensation everywhere on the cell. -/
public theorem MiddleIntRow.compensation_eq_zero (r : MiddleIntRow) (N : ℕ)
    (hd : 0 ≤ (r.bernstein N).den) (hn : ∀ i ≤ N, 0 ≤ (r.bernstein N).num i) :
    Analysis.bernsteinCompensation (r.poly N) N = 0 := by
  rw [Analysis.bernsteinCompensation]
  apply Finset.sum_eq_zero
  intro i _
  have hi := Nat.le_of_lt_succ i.isLt
  have hnq : (0 : ℚ) ≤ ((r.bernstein N).num i.val : ℚ) := by exact_mod_cast hn i.val hi
  have hdq : (0 : ℚ) ≤ ((r.bernstein N).den : ℚ) := by exact_mod_cast hd
  have hq := div_nonneg hnq hdq
  rw [r.bernstein_coeff hi] at hq
  rw [max_eq_left (neg_nonpos.mpr (Rat.cast_nonneg.mpr hq)), Polynomial.C_0, zero_mul]

/-- Compute both cell charges from a shared Bernstein row, skipping zero compensation. -/
@[expose]
public def MiddleIntRow.compensationCharges (r : MiddleIntRow) (N : ℕ) (l h a d : ℚ) : ℚ × ℚ :=
  let row := r.bernstein N
  if (List.range (N + 1)).all (fun i ↦ decide (0 ≤ row.num i)) then (0, 0)
  else
    let c := row.compensationCoeff
    let s := a + 1 / 2
    (Analysis.compensationExpUpper (s * l) *
        Analysis.compensationMomentSum N 2 h s (fun i ↦ c i.val),
      Analysis.compensationExpUpper (a * l) *
        Analysis.compensationMomentSum N 1 h a
          (fun i ↦ |Analysis.bernsteinVariationDirect N i.val d h c|))

/-- The two computed charges bound the main integral and weighted absolute variation
of the same clipped polynomial on the cell. -/
public theorem MiddleIntRow.compensation_charges_le (r : MiddleIntRow) (N : ℕ) {l h a d : ℚ}
    (hh : 0 < h) (hl : 0 ≤ l) (ha : 0 ≤ a) (hd : 0 ≤ (r.bernstein N).den) :
    let C := Analysis.bernsteinCompensation (r.poly N) N
    let u := fun v : ℝ ↦ (v - (l : ℝ)) / (h : ℝ)
    let charge := r.compensationCharges N l h a d
    (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ), Real.exp (-((a + 1 / 2 : ℚ) : ℝ) * v) * C.eval (u v)) ≤
        (charge.1 : ℝ) ∧
      (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
          Real.exp (-(a : ℝ) * v) *
            |(d : ℝ) * C.eval (u v) - (h : ℝ)⁻¹ * C.derivative.eval (u v)|) ≤
        (charge.2 : ℝ) := by
  dsimp only
  unfold MiddleIntRow.compensationCharges
  dsimp only
  by_cases hzero : ((List.range (N + 1)).all (fun i ↦ decide (0 ≤ (r.bernstein N).num i))) = true
  · rw [ite_eq_left hzero]
    have hz :=
      r.compensation_eq_zero N hd
        (fun i hi ↦
          of_decide_eq_true
            (List.all_eq_true.mp hzero i (List.mem_range.mpr (Nat.lt_succ_of_le hi))))
    simp only [hz, Polynomial.eval_zero, Polynomial.derivative_zero, mul_zero, sub_zero, abs_zero,
      intervalIntegral.integral_zero, Rat.cast_zero, le_refl, and_self]
  · rw [ite_eq_right hzero]
    exact
      ⟨r.compensation_main_le N hh hl (add_nonneg ha (by norm_num only)) hd,
        r.compensation_variation_le N d hh hl ha hd⟩

/-- The sum of cell costs is bounded by the sum of their upward-rounded ticks. -/
public theorem middle_sum_le_ticks {S : ℚ} (hS : 0 < S) (N : ℕ) (f : ℕ → ℚ) :
    (∑ i ∈ Finset.range N, f i) ≤ ((∑ i ∈ Finset.range N, ⌈f i * S⌉ : ℤ) : ℚ) / S := by
  apply (le_div_iff₀ hS).mpr
  rw [Finset.sum_mul, Int.cast_sum]
  exact Finset.sum_le_sum (fun i _ ↦ Int.le_ceil (f i * S))

/-- A paired fold sums the two tick coordinates without a second traversal. -/
public theorem middle_ticks_fold (N : ℕ) (f : ℕ → ℤ × ℤ) :
    (List.range N).foldl
        (fun (a, b) i =>
          let (x, y) := f i
          (a + x, b + y))
        (0, 0) =
      (∑ i ∈ Finset.range N, (f i).1, ∑ i ∈ Finset.range N, (f i).2) := by
  induction N with
  | zero => simp only [List.range_zero, List.foldl_nil, Finset.sum_range_zero]
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ (fun i ↦ (f i).1),
      Finset.sum_range_succ (fun i ↦ (f i).2), List.foldl_cons, List.foldl_nil]

/-- A contiguous range sum is the sum of its equal-width blocks. -/
public theorem middle_sum_blocks (w n : ℕ) (f : ℕ → ℤ) :
    (∑ i ∈ Finset.range (w * n), f i) =
      ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range w, f (w * j + i) := by
  induction n with
  | zero => simp only [Nat.mul_zero, Finset.sum_range_zero]
  | succ n ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Verified block tick bounds give a rational upper bound for the sum of cell charges. -/
public theorem middle_sum_le_block_ticks {S : ℚ} (hS : 0 < S) (w n : ℕ) (f : ℕ → ℚ) (U : ℕ → ℤ)
    (h : ∀ j < n, (∑ i ∈ Finset.range w, ⌈f (w * j + i) * S⌉) ≤ U j) :
    (∑ i ∈ Finset.range (w * n), f i) ≤ ((∑ j ∈ Finset.range n, U j : ℤ) : ℚ) / S := by
  refine (middle_sum_le_ticks hS (w * n) f).trans ?_
  rw [middle_sum_blocks]
  exact
    div_le_div_of_nonneg_right
      (Int.cast_le.mpr (Finset.sum_le_sum fun j hj ↦ h j (Finset.mem_range.mp hj))) hS.le

/-- Adjacent integer affine cells give the same compensation at their shared endpoint. -/
public theorem MiddleIntRow.compensation_seam (r : MiddleIntRow) (N : ℕ) (a w v b : ℤ)
    (hr : r.den ≠ 0) (hb : b ≠ 0) :
    (Analysis.bernsteinCompensation ((r.affine N a w b).poly N) N).eval 1 =
      (Analysis.bernsteinCompensation ((r.affine N (a + w) v b).poly N) N).eval 0 := by
  rw [r.poly_affine N a w b hr hb, r.poly_affine N (a + w) v b hr hb]
  have hN : (r.poly N).natDegree ≤ N :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)
  have h :=
    Analysis.bernstein_compensation_seam (r.poly N) N N hN hN ((a : ℚ) / b)
      ((a : ℚ) / b + (w : ℚ) / b) (((a : ℚ) / b + (w : ℚ) / b) + (v : ℚ) / b)
  simpa only [add_sub_cancel_left, Int.cast_add, add_div] using h

/-- Upper bounds on the integrals over adjacent cells bound the full interval integral. -/
public theorem middle_integral_le_sum {n : ℕ} (x : ℕ → ℝ) (f : ℝ → ℝ) (C : ℕ → ℝ)
    (hint : ∀ i < n, IntervalIntegrable f MeasureTheory.volume (x i) (x (i + 1)))
    (h : ∀ i < n, (∫ t in x i..x (i + 1), f t) ≤ C i) :
    (∫ t in x 0..x n, f t) ≤ ∑ i ∈ Finset.range n, C i := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  exact Finset.sum_le_sum (fun i hi ↦ h i (Finset.mem_range.mp hi))

/-- Sum certified scalar charges over a partition with integer endpoints
and a common denominator. Each cell's Bernstein transform is certified once. -/
public theorem MiddleIntRow.exp_abs_partition_le (r : MiddleIntRow) (N m : ℕ) (p : ℕ → ℤ) (b : ℤ)
    (s : ℝ) (C : ℕ → ℚ) (hr : r.den ≠ 0) (hb : b ≠ 0)
    (hp : ∀ i < m, 0 < (((p (i + 1) - p i : ℤ) : ℚ) / b))
    (hC :
      ∀ i < m,
        Real.exp (max (s * (((p i : ℚ) / b : ℚ) : ℝ)) (s * (((p (i + 1) : ℚ) / b : ℚ) : ℝ))) *
            (r.absCellCharge N (p i) (p (i + 1) - p i) b : ℝ) ≤
          (C i : ℝ)) :
    (∫ t in (((p 0 : ℚ) / b : ℚ) : ℝ)..(((p m : ℚ) / b : ℚ) : ℝ),
        Real.exp (s * t) * |(r.poly N).eval₂ (Rat.castHom ℝ) t|) ≤
      ((∑ i ∈ Finset.range m, C i : ℚ) : ℝ) := by
  let x := fun i : ℕ ↦ (((p i : ℚ) / b : ℚ) : ℝ)
  let f := fun t : ℝ ↦ Real.exp (s * t) * |(r.poly N).eval₂ (Rat.castHom ℝ) t|
  have hf : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Polynomial.continuous_eval₂ _ _).abs
  rw [Rat.cast_sum]
  refine
    middle_integral_le_sum x f (fun i ↦ (C i : ℝ))
      (fun i _ ↦ hf.intervalIntegrable (x i) (x (i + 1))) (fun i hi ↦ ?_)
  have h := r.exp_abs_cell_le N (p i) (p (i + 1) - p i) b hr hb (hp i hi) s
  have he : (p i : ℚ) / b + ((p (i + 1) - p i : ℤ) : ℚ) / b = (p (i + 1) : ℚ) / b := by
    rw [← add_div, Int.cast_sub, add_sub_cancel]
  dsimp only at h
  rw [he] at h
  exact h.trans (hC i hi)

/-- On an affine grid, certify all exponential weights from a base bound and
one common ratio bound. The ratio bounds can be reused across adjacent sums. -/
public theorem middle_exp_grid_le {a h E R : ℝ} (hE : Real.exp a ≤ E) (hR : Real.exp h ≤ R)
    (i : ℕ) : Real.exp (a + i * h) ≤ E * R ^ i := by
  have hRn := (Real.exp_pos h).le.trans hR
  induction i with
  | zero => simpa only [Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one] using hE
  | succ j
    hj =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, Real.exp_add, pow_succ, ← mul_assoc]
    exact
      mul_le_mul hj hR (Real.exp_nonneg _)
        (mul_nonneg ((Real.exp_pos a).le.trans hE) (pow_nonneg hRn j))

end PseudoPrime.PrimeTestBounds.MillerRabin
