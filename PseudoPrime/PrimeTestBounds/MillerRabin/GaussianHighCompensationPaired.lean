/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPartition
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPartition

/-! # Shared computation of the high Gaussian compensation bounds -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Compute both compensation bounds from a shared affine coefficient row
and a shared clipped Bernstein row. The two existing moment formulas and
their exponent rates determine the returned main and variation charges. -/
@[expose]
public def HighGaussianKernel.cellChargeBounds (K : HighGaussianKernel) (l h : ℚ) : ℚ × ℚ :=
  let n := 2 * K.degree + 3
  let row := K.cellPowerRow l h
  let c := Array.ofFn (fun i : Fin (n + 1) ↦ max 0 (-cellBernsteinFromPower n i.val row))
  let clipped (j : ℕ) :=
    if hj : j < n + 1 then c[j]'(Array.size_ofFn.symm ▸ hj)
    else max 0 (-cellBernsteinFromPower n j row)
  let v :=
    Array.ofFn
      (fun i : Fin (n + 1) ↦ |Analysis.bernsteinVariationDirect n i.val (K.pole - 1 / 2) h clipped|)
  let s := K.pole + 1 / 2
  (Analysis.compensationExpUpper (s * l) *
      Analysis.compensationMomentSum n 2 h s (fun i ↦ c[i.val]'(Array.size_ofFn.symm ▸ i.isLt)),
    Analysis.compensationExpUpper (K.pole * l) *
      Analysis.compensationMomentSum n 1 h K.pole
        (fun i ↦ v[i.val]'(Array.size_ofFn.symm ▸ i.isLt)))

/-- The shared calculation returns the same two rational charges as the
separate functions used in the analytical bounds. -/
public theorem high_cell_charge_bounds_eq (K : HighGaussianKernel) (l h : ℚ) :
    K.cellChargeBounds l h = (K.cellMainBound l h, K.cellVariationBound l h) := by
  let n := 2 * K.degree + 3
  let P := K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)
  let b (j : ℕ) := max 0 (-cellBernsteinFromPower n j (K.cellPowerRow l h))
  have hcoef (j : ℕ) : max 0 (-Analysis.bernsteinRatCoeff P n j) = b j := by
    rw [high_cell_bernstein_coeff K l h j]
    rfl
  apply Prod.ext
  · rfl
  · simp only [HighGaussianKernel.cellChargeBounds, HighGaussianKernel.cellVariationBound,
      Array.getElem_ofFn]
    apply congrArg (fun t : ℚ ↦ Analysis.compensationExpUpper (K.pole * l) * t)
    apply congrArg (Analysis.compensationMomentSum n 1 h K.pole)
    funext i
    apply congrArg abs
    simp only [dite_eq_ite, ite_self]
    change
      Analysis.bernsteinVariationDirect n i.val (K.pole - 1 / 2) h b =
        Analysis.bernsteinVariationFromRow n i.val
          (Analysis.bernsteinVariationPowerRow n (K.pole - 1 / 2) h (fun j ↦ b j.val))
    rw [Analysis.bernstein_variation_row_eq]
    rw [show
        (fun j : Fin (n + 1) ↦ b j.val) = (fun j ↦ max 0 (-Analysis.bernsteinRatCoeff P n j.val))
        from funext (fun j ↦ (hcoef j.val).symm)]
    rw [← Analysis.bernstein_variation_coeff_eq, Analysis.bernstein_variation_direct_eq]
    simp only [hcoef]

/-- Accumulate both rounded bounds in one traversal of the cell partition. -/
private def accumulateChargePairs (K : HighGaussianKernel) (ws : List ℕ) (i : ℕ) (a : ℤ × ℤ) :
    ℤ × ℤ :=
  (ws.foldl
      (fun (state : ℕ × (ℤ × ℤ)) width ↦
        let bounds := K.cellChargeBounds (logCoordinate state.1) (logCoordinate width)
        (state.1 + width, state.2.1 + chargeTicks bounds.1, state.2.2 + chargeTicks bounds.2))
      (i, a)).2

/-- The paired traversal produces exactly the two separately rounded totals. -/
private theorem charge_pairs_eq (K : HighGaussianKernel) (ws : List ℕ) (i : ℕ) (a : ℤ × ℤ) :
    accumulateChargePairs K ws i a =
      (accumulateCharges K.cellMainBound ws i a.1,
        accumulateCharges K.cellVariationBound ws i a.2) := by
  induction ws generalizing i a with
  | nil => rfl
  | cons w ws ih =>
    let l := logCoordinate i
    let h := logCoordinate w
    change
      accumulateChargePairs K ws (i + w)
          (a.1 + chargeTicks (K.cellChargeBounds l h).1,
            a.2 + chargeTicks (K.cellChargeBounds l h).2) =
        (accumulateCharges K.cellMainBound ws (i + w) (a.1 + chargeTicks (K.cellMainBound l h)),
          accumulateCharges K.cellVariationBound ws (i + w)
            (a.2 + chargeTicks (K.cellVariationBound l h)))
    rw [high_cell_charge_bounds_eq]
    exact ih (i + w) _

/-- The executable certificate can share the Bernstein calculation for each
cell while the analytical results use the existing pair of tick bounds. -/
public def highCompensationPairedTicks (K : HighGaussianKernel) : ℤ × ℤ :=
  accumulateChargePairs K (cellWidths K) 0 (0, 0)

/-- The shared evaluation agrees with the bounds used by the analytical proof. -/
public theorem high_compensation_paired_ticks_eq (K : HighGaussianKernel) :
    highCompensationPairedTicks K = highCompensationChargeTicks K := by
  exact charge_pairs_eq K (cellWidths K) 0 (0, 0)

end PseudoPrime.PrimeTestBounds.MillerRabin
