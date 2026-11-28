/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.MellinLogMoments

/-! # Finite complex Mellin moments of reflected logarithmic polynomials -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The complex Mellin moment of a reflected polynomial on the unit interval.
The inner finite sum integrates each shifted logarithmic monomial. -/
@[expose]
public noncomputable def complexLogPolyMoment (D : Polynomial ℝ) (b : ℝ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (D.natDegree + 1),
    (D.coeff k : ℂ) *
      ∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℂ) * (b : ℂ) ^ (k - j)) * ((j.factorial : ℂ) / s ^ (j + 1))

/-- Integrate the reflected polynomial against the Mellin power up to a positive cutoff.
The monomial expansion is integrable and has an exact finite moment formula. -/
public theorem complex_log_poly_cutoff (D : Polynomial ℝ) (b : ℝ) {s : ℂ} (hs : 0 < s.re) {y : ℝ}
    (hy : 0 < y) :
    let f := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * Complex.ofReal (D.eval (b - Real.log u))
    IntervalIntegrable f MeasureTheory.volume 0 y ∧
      (∫ u in (0 : ℝ)..y, f u) = (y : ℂ) ^ s * complexLogPolyMoment D (b - Real.log y) s := by
  intro f
  let g := fun (k : ℕ) (u : ℝ) ↦
    (D.coeff k : ℂ) * ((u : ℂ) ^ (s - 1) * ((b - Real.log u : ℝ) : ℂ) ^ k)
  have he : f = fun u ↦ ∑ k ∈ Finset.range (D.natDegree + 1), g k u := by
    funext u
    simp only [f, g, Polynomial.eval_eq_sum_range, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_pow, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ ↦ by rw [mul_left_comm])
  have hi (k : ℕ) : IntervalIntegrable (g k) MeasureTheory.volume 0 y :=
    (Analysis.complex_log_moment_integrable k b hs hy).const_mul _
  rw [he]
  constructor
  · have hsum :
      (∑ k ∈ Finset.range (D.natDegree + 1), g k) = fun u ↦
        ∑ k ∈ Finset.range (D.natDegree + 1), g k u := by
      funext u
      exact Finset.sum_apply u _ _
    rw [← hsum]
    exact IntervalIntegrable.sum _ (fun k _ ↦ hi k)
  · rw [intervalIntegral.integral_finsetSum (fun k _ ↦ hi k), complexLogPolyMoment, Finset.mul_sum]
    exact
      Finset.sum_congr rfl
        (fun k _ ↦ by
          rw [intervalIntegral.integral_const_mul, Analysis.complex_log_moment_cutoff k b hs hy,
            mul_left_comm])

end PseudoPrime.PrimeTestBounds.MillerRabin
