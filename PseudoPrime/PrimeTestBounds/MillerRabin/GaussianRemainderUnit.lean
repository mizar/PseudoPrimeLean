/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRemainderBernstein
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRemainderBernstein
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadCert
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Ring

/-! # Integer translations for the unit-grid H27 certificate -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Lift the base polynomial to one integer denominator before translating any cell. -/
private def unitRemainderRow (n : ℕ) (f : Fin (n + 1) → ℚ) : ℕ × Array ℤ :=
  let d := Finset.univ.lcm (fun j ↦ (f j).den)
  ⟨d, Array.ofFn fun j ↦ scaledHeadCoeff d (f j)⟩

/-- Translate the integer numerators to an integral left endpoint. -/
private def unitRemainderNumerator (n : ℕ) (row : ℕ × Array ℤ) (l : ℕ) (choose : ℕ → ℕ → ℕ)
    (i : Fin (n + 1)) : ℤ :=
  ∑ j : Fin (n + 1), row.2[j.val]?.getD 0 * ((choose j i * l ^ (j.val - i.val) : ℕ) : ℤ)

/-- Recover the affine rational coefficient from its numerator. -/
private def unitRemainderCoeff (n : ℕ) (row : ℕ × Array ℤ) (l : ℕ) (choose : ℕ → ℕ → ℕ)
    (i : Fin (n + 1)) : ℚ :=
  (unitRemainderNumerator n row l choose i : ℚ) / row.1

/-- Integer translation computes the standard binomial coefficient for width one. -/
private theorem unit_remainder_coeff_eq (n : ℕ) (f : Fin (n + 1) → ℚ) (l : ℕ) (i : Fin (n + 1)) :
    unitRemainderCoeff n (unitRemainderRow n f) l Nat.fast_choose i =
      ∑ j : Fin (n + 1), f j * ((Nat.fast_choose j i : ℚ) * (l : ℚ) ^ (j.val - i.val)) := by
  let d := Finset.univ.lcm (fun j ↦ (f j).den)
  have hd : d ≠ 0 := fun h ↦
    let ⟨j, _, hj⟩ := Finset.lcm_eq_zero_iff.mp h
    (f j).den_nz hj
  have hdiv (j : Fin (n + 1)) : (f j).den ∣ d := Finset.dvd_lcm (Finset.mem_univ j)
  simpa only [unitRemainderRow, unitRemainderCoeff, unitRemainderNumerator, Array.getElem?_ofFn,
    Fin.isLt, dite_true, Option.getD_some, Nat.cast_mul, Nat.cast_pow, d] using
    scaled_head_dot (n + 1) d hd f hdiv (fun j ↦ Nat.fast_choose j i * l ^ (j.val - i.val))

/-- Compute the unit-width Bernstein mass with the fixed integer coefficient row. -/
private def unitRemainderCell (n : ℕ) (row : ℕ × Array ℤ) (l : ℕ) (choose : ℕ → ℕ → ℕ) : ℚ :=
  let shift := Array.ofFn (unitRemainderCoeff n row l choose)
  headBernsteinAbs n (fun i ↦ shift[i.val]?.getD 0 / (choose n i : ℚ)) choose / ((n : ℚ) + 1)

/-- The accelerated cell calculation gives the existing Bernstein bound exactly. -/
private theorem unit_remainder_cell_eq (n : ℕ) (f : Fin (n + 1) → ℚ) (l : ℕ) :
    unitRemainderCell n (unitRemainderRow n f) l Nat.fast_choose =
      headCellMass n f (l : ℚ) 1 Nat.fast_choose := by
  simp only [unitRemainderCell, Array.getElem?_ofFn, Fin.isLt, dite_true, Option.getD_some,
    unit_remainder_coeff_eq, headCellMass, head_affine_row_eq, one_pow, one_mul]

/-- Lift a binomial denominator into the common denominator for Bernstein weights. -/
private theorem unit_binomial_scale (x : ℤ) {d c u : ℕ} (hd : d ≠ 0) (hc : c ≠ 0) (hu : u ≠ 0)
    (hud : u ∣ c) :
    (((x * (c / u : ℕ) : ℤ) : ℚ) / ((d * c : ℕ) : ℚ)) = ((x : ℚ) / (d : ℚ)) / (u : ℚ) := by
  have eq : ((c / u : ℕ) : ℚ) * (u : ℚ) = (c : ℚ) := by rw [← Nat.cast_mul, Nat.div_mul_cancel hud]
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_mul, div_div,
    div_eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr hd) (Nat.cast_ne_zero.mpr hc))
      (mul_ne_zero (Nat.cast_ne_zero.mpr hd) (Nat.cast_ne_zero.mpr hu))]
  calc
    _ = (x : ℚ) * (d : ℚ) * (((c / u : ℕ) : ℚ) * (u : ℚ)) := by ring
    _ = _ := by rw [eq, mul_assoc]

/-- Read a sum of absolute Bernstein numerators over a natural denominator. -/
private theorem unit_abs_integer_sum (n d : ℕ) (numerator : Fin n → ℤ) :
    ((∑ j, |numerator j| : ℤ) : ℚ) / (d : ℚ) = ∑ j, |(numerator j : ℚ) / (d : ℚ)| := by
  simp only [Int.cast_sum, Int.cast_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℚ) d),
    Finset.sum_div]

/-- Precompute one denominator and the integer scaling factor for every Bernstein weight. -/
private def unitBinomialRow (n : ℕ) (choose : ℕ → ℕ → ℕ) : ℕ × Array ℕ :=
  let c := Finset.univ.lcm (fun i : Fin (n + 1) ↦ choose n i)
  ⟨c, Array.ofFn fun i : Fin (n + 1) ↦ c / choose n i⟩

/-- Compute the sum of absolute Bernstein numerators before the final division. -/
private def unitIntegerMass (n : ℕ) (row : ℕ × Array ℤ) (bin : ℕ × Array ℕ) (l : ℕ)
    (choose : ℕ → ℕ → ℕ) : ℤ :=
  let shift :=
    Array.ofFn fun i : Fin (n + 1) ↦
      unitRemainderNumerator n row l choose i * (bin.2[i.val]?.getD 0 : ℕ)
  ∑ k : Fin (n + 1), |∑ i : Fin (n + 1), shift[i.val]?.getD 0 * (choose k i : ℤ)|

/-- Restore the normalization of the Bernstein mass at width one. -/
private def unitIntegerCell (n : ℕ) (row : ℕ × Array ℤ) (bin : ℕ × Array ℕ) (l : ℕ)
    (choose : ℕ → ℕ → ℕ) : ℚ :=
  ((unitIntegerMass n row bin l choose : ℚ) / ((row.1 * bin.1 : ℕ) : ℚ)) / ((n : ℚ) + 1)

/-- The integer mass agrees with the Bernstein mass using rational coordinates. -/
private theorem unit_integer_cell_eq (n : ℕ) (f : Fin (n + 1) → ℚ) (l : ℕ) :
    unitIntegerCell n (unitRemainderRow n f) (unitBinomialRow n Nat.fast_choose) l Nat.fast_choose =
      unitRemainderCell n (unitRemainderRow n f) l Nat.fast_choose := by
  let row := unitRemainderRow n f
  let bin := unitBinomialRow n Nat.fast_choose
  let u := fun i : Fin (n + 1) ↦ Nat.fast_choose n i
  have hu (i : Fin (n + 1)) : u i ≠ 0 := by
    change n.fast_choose i ≠ 0
    rw [← Nat.choose_eq_fast_choose]
    exact (Nat.choose_pos (Nat.le_of_lt_succ i.isLt)).ne'
  have hd : row.1 ≠ 0 := fun h ↦
    let ⟨j, _, hj⟩ :=
      Finset.lcm_eq_zero_iff.mp (show Finset.univ.lcm (fun j ↦ (f j).den) = 0 from h)
    (f j).den_nz hj
  have hc : bin.1 ≠ 0 := fun h ↦
    let ⟨j, _, hj⟩ := Finset.lcm_eq_zero_iff.mp (show Finset.univ.lcm u = 0 from h)
    hu j hj
  have hdiv (i : Fin (n + 1)) : u i ∣ bin.1 := Finset.dvd_lcm (Finset.mem_univ i)
  have hterm (i : Fin (n + 1)) :
    (((unitRemainderNumerator n row l Nat.fast_choose i * (bin.1 / u i : ℕ) : ℤ) : ℚ) /
        ((row.1 * bin.1 : ℕ) : ℚ)) =
      unitRemainderCoeff n row l Nat.fast_choose i / (u i : ℚ) :=
    unit_binomial_scale _ hd hc (hu i) (hdiv i)
  unfold unitIntegerCell unitIntegerMass unitRemainderCell
  dsimp only
  rw [head_bernstein_abs_eq, unit_abs_integer_sum]
  refine congrArg (fun q : ℚ ↦ q / ((n : ℚ) + 1)) ?_
  apply Finset.sum_congr rfl
  intro k _
  refine congrArg abs ?_
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Array.getElem?_ofFn, Fin.isLt, dite_true, Option.getD_some]
  have hbin : bin.2[i.val]?.getD 0 = bin.1 / u i := by
    simp only [bin, unitBinomialRow, Array.getElem?_ofFn, Fin.isLt, dite_true, Option.getD_some, u]
  change
    (((unitRemainderNumerator n row l Nat.fast_choose i * (bin.2[i.val]?.getD 0 : ℕ) : ℤ) *
              (Nat.fast_choose k i : ℤ) :
            ℤ) :
          ℚ) /
        ((row.1 * bin.1 : ℕ) : ℚ) =
      _
  rw [hbin, Int.cast_mul, mul_div_right_comm, hterm i, Int.cast_natCast]

/-- Round a rationally weighted integer fraction using one integer division. -/
private def unitWeightedCeil (a : ℤ) (d scale : ℕ) (w : ℚ) : ℤ :=
  -((-(w.num * a * (scale : ℤ))) / ((w.den * d : ℕ) : ℤ))

/-- The integer division computes the ceiling without normalizing the rational product. -/
private theorem unit_weighted_ceil_eq (a : ℤ) (d scale : ℕ) (w : ℚ) :
    unitWeightedCeil a d scale w = ⌈w * ((a : ℚ) / (d : ℚ)) * (scale : ℚ)⌉ := by
  unfold unitWeightedCeil
  rw [← Rat.ceil_intCast_div_natCast]
  congr 1
  conv_rhs => rw [← w.num_div_den]
  simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul, div_mul_eq_mul_div]
  rw [← mul_div_assoc, div_mul_eq_mul_div, div_div, mul_comm (d : ℚ)]

/-- Prepare the shared integer coefficients for the remainder polynomial. -/
private def unitRemainderData (K : HighGaussianKernel) : ℕ × Array ℤ :=
  let n := 2 * K.degree + 3
  let compact := headCoeffCache (2 * K.degree + 1) (headCompactCoeff K)
  let b := headCoeffCache (n + 3) (highProfileFrom K compact)
  let c := headCoeffCache (n + 1) (remainderCoeff (K.pole - 1 / 2) (headCached b))
  unitRemainderRow n fun j ↦ headCached c j

/-- Construct the per-cell evaluator after the polynomial's integer row is available. -/
private def unitCellWithRow (n : ℕ) (row : ℕ × Array ℤ) (scale : ℕ) (w : ℕ → ℚ) : ℕ → ℤ :=
  let binomial := headCoeffCache (n + 1) (fun k ↦ headCoeffCache (n + 1) (Nat.fast_choose k))
  let bin := unitBinomialRow n (fun k ↦ headCached (headCached binomial k))
  fun x ↦
  unitWeightedCeil (unitIntegerMass n row bin x (fun k ↦ headCached (headCached binomial k)))
    (row.1 * bin.1 * (n + 1)) scale (w x)

/-- Evaluate each rounded charge using the shared integer row. -/
private def unitCellCharge (K : HighGaussianKernel) (scale : ℕ) (w : ℕ → ℚ) : ℕ → ℤ :=
  unitCellWithRow (2 * K.degree + 3) (unitRemainderData K) scale w

/-- Sum the rounded charges over consecutive indices. -/
private def unitTicksWithWeights (K : HighGaussianKernel) (start N scale : ℕ) (w : ℕ → ℚ) : ℤ :=
  let f := unitCellCharge K scale w
  (List.ofFn fun j : Fin N ↦ f (start + j.val)).sum

/-- Read the weighted unit-grid cell charges as rational numbers before rounding. -/
private def unitGridCharges (K : HighGaussianKernel) (N : ℕ) (w : ℕ → ℚ) : List ℚ :=
  let n := 2 * K.degree + 3
  List.ofFn fun j : Fin N ↦
    w j *
      headCellMass n (fun i ↦ remainderCoeff (K.pole - 1 / 2) (highProfileCoeff K) i) (j.val : ℚ) 1
        Nat.fast_choose

/-- The integer computation rounds the same individual rational charges. -/
private theorem unit_ticks_weights_eq (K : HighGaussianKernel) (N scale : ℕ) (w : ℕ → ℚ) :
    unitTicksWithWeights K 0 N scale w =
      ((unitGridCharges K N w).map fun x ↦ ⌈x * (scale : ℚ)⌉).sum := by
  have hb :
    highProfileFrom K (headCoeffCache (2 * K.degree + 1) (headCompactCoeff K)) =
      highProfileCoeff K :=
    rfl
  have hc (n : ℕ) (row : ℕ × Array ℤ) (bin : ℕ × Array ℕ) (l : ℕ) (choose : ℕ → ℕ → ℕ) :
    (unitIntegerMass n row bin l choose : ℚ) / ((row.1 * bin.1 * (n + 1) : ℕ) : ℚ) =
      unitIntegerCell n row bin l choose := by
    simp only [unitIntegerCell, div_div, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [unitTicksWithWeights, unitCellCharge, unitCellWithRow, unitRemainderData,
    unitGridCharges, List.map_ofFn, head_coeff_cache_eq, unit_weighted_ceil_eq, hc,
    unit_integer_cell_eq, unit_remainder_cell_eq, hb, Nat.zero_add]
  rfl

/-- Compute the rounded weights on a unit grid using one Taylor bound per endpoint. -/
public def highRemainderUnitTicks (K : HighGaussianKernel) (N m scale : ℕ) (s : ℚ) : ℤ :=
  unitTicksWithWeights K 0 N scale (fun j ↦ headExpUpper (s * (j : ℚ)) m)

/-- The unit-grid evaluator gives the same rounded charge as the general evaluator. -/
public theorem high_remainder_unit_ticks_eq (K : HighGaussianKernel) (N m scale : ℕ) (s : ℚ) :
    highRemainderUnitTicks K N m scale s =
      highRemainderChargeTicks K N m scale s (fun j ↦ (j : ℚ)) := by
  rw [highRemainderUnitTicks, unit_ticks_weights_eq]
  simp only [highRemainderChargeTicks, remainderCharges, unitGridCharges, head_coeff_cache_eq,
    Nat.cast_add, Nat.cast_one, add_sub_cancel_left]
  rfl

/-- The unit-grid integer sum bounds the absolute remainder integral up to its endpoint. -/
public theorem high_remainder_integral_le_unit (K : HighGaussianKernel) (N m scale : ℕ)
    (hscale : 0 < scale) {s : ℚ} (hs : 0 ≤ s) :
    let D := (highRemainderRatPoly K).map (Rat.castHom ℝ)
    (∫ x in (0 : ℝ)..(N : ℝ), Real.exp (-(s : ℝ) * x) * |D.eval x|) ≤
      (highRemainderUnitTicks K N m scale s : ℝ) / (scale : ℝ) := by
  rw [high_remainder_unit_ticks_eq]
  have h :=
    high_remainder_integral_le_ticks K N m scale hscale hs (fun j ↦ (j : ℚ))
      (fun j _ ↦ Nat.cast_lt.mpr (Nat.lt_succ_self j)) (fun j _ ↦ Nat.cast_nonneg j)
  simpa only [Rat.cast_natCast, Rat.cast_zero, Nat.cast_zero] using h

/-- Use the powers of a single rational exponential upper bound on the unit grid. -/
public def highRemainderGeomTicks (K : HighGaussianKernel) (N scale : ℕ) (q : ℚ) : ℤ :=
  unitTicksWithWeights K 0 N scale (fun j ↦ q ^ j)

/-- Each geometric weight bounds the corresponding real exponential at a unit-grid endpoint. -/
private theorem unit_geom_weight {s q : ℚ} (hq : Real.exp (-(s : ℝ)) ≤ (q : ℝ)) (j : ℕ) :
    Real.exp (-(s : ℝ) * (j : ℝ)) ≤ ((q ^ j : ℚ) : ℝ) := by
  rw [mul_comm, Real.exp_natCast_mul, Rat.cast_pow]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) hq j

/-- A single one-step exponential bound suffices to certify the entire absolute integral. -/
public theorem high_remainder_integral_le_geom (K : HighGaussianKernel) (N scale : ℕ)
    (hscale : 0 < scale) {s q : ℚ} (hs : 0 ≤ s) (hq : Real.exp (-(s : ℝ)) ≤ (q : ℝ)) :
    let D := (highRemainderRatPoly K).map (Rat.castHom ℝ)
    (∫ x in (0 : ℝ)..(N : ℝ), Real.exp (-(s : ℝ) * x) * |D.eval x|) ≤
      (highRemainderGeomTicks K N scale q : ℝ) / (scale : ℝ) := by
  let w := fun j : ℕ ↦ q ^ j
  let p := fun j : ℕ ↦ (j : ℚ)
  have he : ∀ j < N, Real.exp (-(s : ℝ) * (p j : ℝ)) ≤ (w j : ℝ) := by
    intro j _
    simpa only [p, w, Rat.cast_natCast] using unit_geom_weight hq j
  have h :=
    high_remainder_integral_bernstein K N (Rat.cast_nonneg.mpr hs) p w
      (fun j _ ↦ Nat.cast_lt.mpr (Nat.lt_succ_self j)) he
  have hs₁ :
    (∫ x in (0 : ℝ)..(N : ℝ),
        Real.exp (-(s : ℝ) * x) * |((highRemainderRatPoly K).map (Rat.castHom ℝ)).eval x|) ≤
      ((unitGridCharges K N w).sum : ℝ) := by
    simpa only [p, Rat.cast_natCast, Rat.cast_zero, Nat.cast_zero, unitGridCharges, List.sum_ofFn,
      remainder_coeff_eq, remainder_cell_mass_eq _ _ (high_remainder_rat_degree K), Nat.cast_add,
      Nat.cast_one, add_sub_cancel_left, ← Fin.sum_univ_eq_sum_range] using h
  refine hs₁.trans ?_
  have hle := (Rat.cast_le (K := ℝ)).mpr (sum_le_charge_ticks (unitGridCharges K N w) hscale)
  simpa only [highRemainderGeomTicks, unit_ticks_weights_eq, w, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_natCast] using hle

/-- Compute the contribution of the cells starting at the given integral index. -/
public def highRemainderGeomBlock (K : HighGaussianKernel) (start N scale : ℕ) (q : ℚ) : ℤ :=
  unitTicksWithWeights K start N scale (fun j ↦ q ^ j)

/-- Splitting consecutive unit cells preserves the rounded integer sum. -/
private theorem unit_ticks_split (K : HighGaussianKernel) (start N M scale : ℕ) (w : ℕ → ℚ) :
    unitTicksWithWeights K start (N + M) scale w =
      unitTicksWithWeights K start N scale w + unitTicksWithWeights K (start + N) M scale w := by
  let f := unitCellCharge K scale w
  simp only [unitTicksWithWeights, List.sum_ofFn]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ f (start + j)),
    Fin.sum_univ_eq_sum_range (fun j ↦ f (start + j)),
    Fin.sum_univ_eq_sum_range (fun j ↦ f (start + N + j)), Finset.sum_range_add]
  simp only [Nat.add_assoc, Nat.add_comm N]

/-- Two consecutive blocks give the geometric sum up to their combined endpoint. -/
public theorem high_remainder_geom_split (K : HighGaussianKernel) (N M scale : ℕ) (q : ℚ) :
    highRemainderGeomTicks K (N + M) scale q =
      highRemainderGeomTicks K N scale q + highRemainderGeomBlock K N M scale q := by
  simpa only [highRemainderGeomTicks, highRemainderGeomBlock, Nat.zero_add] using
    unit_ticks_split K 0 N M scale (fun j ↦ q ^ j)

/-- Split an arbitrary geometric block into two consecutive blocks. -/
public theorem high_remainder_geom_block_split (K : HighGaussianKernel) (start N M scale : ℕ)
    (q : ℚ) :
    highRemainderGeomBlock K start (N + M) scale q =
      highRemainderGeomBlock K start N scale q +
        highRemainderGeomBlock K (start + N) M scale q := by
  simpa only [highRemainderGeomBlock] using unit_ticks_split K start N M scale (fun j ↦ q ^ j)

end PseudoPrime.PrimeTestBounds.MillerRabin
