/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPartition
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPartition

/-! # Assemble separate upper bounds for the high compensation integrals -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The widths and integral bounds of a single compensation cell. The two
bounds are integers in units of ten to the negative twentieth power. -/
private structure CompCellCap where
  width : ℕ
  main : ℤ
  variation : ℤ

/-- The weight for the main integral on a high compensation cell. -/
private noncomputable def mainIntegrand (K : HighGaussianKernel) (l h : ℚ) (t : ℝ) : ℝ :=
  Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * t) * highCellCompensation K l h t

/-- The cell caps certify the integrals at their consecutive dyadic starts. -/
private def CompCellCaps (K : HighGaussianKernel) : List CompCellCap → ℕ → Prop
  | [], _ => True
  | c :: cs, i =>
    let l := logCoordinate i
    let h := logCoordinate c.width
    (∫ t in (l : ℝ)..(l : ℝ) + (h : ℝ), mainIntegrand K l h t) ≤ (c.main : ℝ) / 10 ^ 20 ∧
      (∫ t in (l : ℝ)..(l : ℝ) + (h : ℝ), variationIntegrand K l h t) ≤
        (c.variation : ℝ) / 10 ^ 20 ∧
      CompCellCaps K cs (i + c.width)

/-- Sum the local integral caps in both components. -/
private theorem sum_comp_cell_caps (K : HighGaussianKernel) (cs : List CompCellCap) (i : ℕ)
    (hc : CompCellCaps K cs i) :
    let ws := cs.map CompCellCap.width
    sumCellIntegrals (mainIntegrand K) ws i ≤ ((cs.map CompCellCap.main).sum : ℤ) / (10 ^ 20 : ℝ) ∧
      sumCellIntegrals (variationIntegrand K) ws i ≤
        ((cs.map CompCellCap.variation).sum : ℤ) / (10 ^ 20 : ℝ) := by
  induction cs generalizing i with
  | nil =>
    simp only [List.map_nil, List.sum_nil, sumCellIntegrals, Int.cast_zero, zero_div, le_refl,
      and_self]
  | cons c cs ih =>
    obtain ⟨hm, hv, ht⟩ := hc
    obtain ⟨hms, hvs⟩ := ih _ ht
    constructor
    · simpa only [List.map_cons, List.sum_cons, Int.cast_add, add_div, sumCellIntegrals] using
        add_le_add hm hms
    · simpa only [List.map_cons, List.sum_cons, Int.cast_add, add_div, sumCellIntegrals] using
        add_le_add hv hvs

/-- The main integrals on adjacent cells combine to the integral of the
assembled continuous compensation. -/
private theorem sum_comp_main_eq (K : HighGaussianKernel) (ws : List ℕ) (i : ℕ)
    (hm : MatchesCells (highCompensation K) (highCellCompensation K) ws i) :
    sumCellIntegrals (mainIntegrand K) ws i =
      ∫ t in (logCoordinate i : ℝ)..(logCoordinate (i + ws.sum) : ℝ),
        Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * t) * highCompensation K t := by
  induction ws generalizing i with
  | nil => rw [sumCellIntegrals, List.sum_nil, Nat.add_zero, intervalIntegral.integral_same]
  | cons w ws
    ih =>
    let f := fun t : ℝ ↦ Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * t) * highCompensation K t
    have hf : Continuous f :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (compensation_on_continuous K _ 0 (widths_positive K))
    have he : (logCoordinate (i + w) : ℝ) = (logCoordinate i : ℝ) + (logCoordinate w : ℝ) := by
      rw [log_coord_add, Rat.cast_add]
    rw [sumCellIntegrals, ← he, ih _ hm.2, List.sum_cons, ← Nat.add_assoc]
    have hcell :
      (∫ t in (logCoordinate i : ℝ)..(logCoordinate (i + w) : ℝ),
          mainIntegrand K (logCoordinate i) (logCoordinate w) t) =
        ∫ t in (logCoordinate i : ℝ)..(logCoordinate (i + w) : ℝ), f t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact congrArg (Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * t) * ·) (hm.1 t ht).symm
    rw [hcell]
    exact
      intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable (logCoordinate i : ℝ) (logCoordinate (i + w) : ℝ))
        (hf.intervalIntegrable (logCoordinate (i + w) : ℝ) (logCoordinate (i + w + ws.sum) : ℝ))

/-- For the actual dyadic partition, the local certificates bound the
two integrals consumed by the Abel argument. -/
private theorem comp_integrals_of_cells (K : HighGaussianKernel) (cs : List CompCellCap)
    (hw : cs.map CompCellCap.width = cellWidths K) (hc : CompCellCaps K cs 0) :
    highCompensationMain K ≤ ((cs.map CompCellCap.main).sum : ℤ) / (10 ^ 20 : ℝ) ∧
      highCompensationVariation K ≤ ((cs.map CompCellCap.variation).sum : ℤ) / (10 ^ 20 : ℝ) := by
  have h := sum_comp_cell_caps K cs 0 hc
  simp only [hw] at h
  rw [sum_comp_main_eq K _ _ (compensation_matches K _ 0 (widths_positive K))] at h
  have h0 : (logCoordinate 0 : ℝ) = 0 := by
    simp only [logCoordinate, Nat.cast_zero, mul_zero, zero_div, Rat.cast_zero]
  have h5 : (logCoordinate (0 + (cellWidths K).sum) : ℝ) = 5 := by
    norm_num only [widths_sum K, Nat.zero_add, logCoordinate, Nat.cast_ofNat, Rat.cast_ofNat,
      Rat.cast_mul, Rat.cast_div]
  simpa only [h0, h5, highCompensationMain, highCompensationVariation] using h

/-- Raw bounds on the two compensation integrals carry over to the
compensation term in the signed Euler comparison. -/
public theorem high_comp_bound_le (K : HighGaussianKernel) (X I V : ℝ)
    (hI : highCompensationMain K ≤ I) (hV : highCompensationVariation K ≤ V) :
    highCompensationBound K X ≤
      (Real.sqrt X * Real.exp (5 / 2)) * I + Real.log (X * Real.exp 5) ^ 2 / 24 * V := by
  exact
    add_le_add (mul_le_mul_of_nonneg_left hI (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)))
      (mul_le_mul_of_nonneg_left hV (div_nonneg (sq_nonneg _) (by norm_num only)))

end PseudoPrime.PrimeTestBounds.MillerRabin
