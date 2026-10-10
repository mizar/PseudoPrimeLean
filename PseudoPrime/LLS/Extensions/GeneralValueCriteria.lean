/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.ConductorValueExpansion
public import PseudoPrime.LLS.Extensions.DegreeOneValueCorrection
public import PseudoPrime.LLS.Extensions.DegreeOneCutoffOptimization
public import PseudoPrime.LLS.Extensions.PaperStatements
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeSumBounds

/-! Exact remaining inputs for the public general L-value proposition. -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- The exact degree-one endpoint required by the public general L-value claim.
On the degree-one conductor filter, both bounds have the linear factor
`log log C - (log 2 - 1/2)`, with the norm and reciprocal prefactors.
There is no additional error: the public Big-O scale vanishes at degree one.
This isolates the remaining endpoint from the positive-degree arithmetic argument. -/
def DegreeOneValueBounds : Prop :=
  ∀ᶠ f : FixedDegreeFamily 1 in conductorFilter 1,
      let t := Real.log (Real.log f.val.analyticConductor)
      ‖f.val.L 1‖ ≤ (2 * Real.exp Real.eulerMascheroniConstant) * (t - (Real.log 2 - 1 / 2)) ∧
      1 / ‖f.val.L 1‖ ≤
        (12 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2) * (t - (Real.log 2 - 1 / 2))

/-- Second-order Mangoldt and psi bounds, with nonnegative psi constant, together with
the exact degree-one endpoint imply the unchanged public general L-value proposition.
Use zero errors at degree one, and the normalized correction and its uniform
little-o and Big-O estimates at every greater degree.
This reduces the full proposition to explicit arithmetic inputs and the degree-one endpoint. -/
theorem generalL_of_primeSum_bounds_and_degreeOne {A B : ℝ} (hB : 0 ≤ B)
    (hH :
      ∀ᶠ x : ℝ in Filter.atTop,
        |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
              (Real.log (Real.log x) + Real.eulerMascheroniConstant)| ≤
          A / (Real.log x) ^ 2)
    (hψ : ∀ᶠ x : ℝ in Filter.atTop, |Chebyshev.psi x - x| ≤ B * x / (Real.log x) ^ 2)
    (hOne : DegreeOneValueBounds) : lls_generalL := by
  intro d hd
  by_cases hd1 : d = 1
  · subst d
    refine
      ⟨(fun _ ↦ 0), (fun _ ↦ 0), Asymptotics.isLittleO_zero _ _, Asymptotics.isLittleO_zero _ _,
        Asymptotics.isBigO_zero _ _, Asymptotics.isBigO_zero _ _, ?_⟩
    filter_upwards [hOne] with f hf
    dsimp only at hf ⊢
    simpa only [pow_one, Nat.cast_one, Real.log_one, one_mul, mul_zero, zero_add, add_zero,
      Nat.sub_self, pow_zero, mul_one] using hf
  · have hd2 : 1 < d := Nat.lt_of_le_of_ne hd (Ne.symm hd1)
    let e := fun f : FixedDegreeFamily d ↦
      valueUpperCorrection d (Real.log (2 * (d : ℝ)))
        ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1)
        (Real.log (Real.log f.val.analyticConductor))
    have hs :=
      isLittleO_valueUpperCorrection_on_conductorFilter d (Real.log (2 * (d : ℝ)))
        ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1)
    have hb :=
      isBigO_valueUpperCorrection_on_conductorFilter hd2 (Real.log (2 * (d : ℝ)))
        ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1)
    exact
      ⟨e, e, hs, hs, hb, hb, eventually_value_bounds_with_correction_of_mangoldt_errors hd hB hH hψ⟩

/-- The public general L-value proposition implies the exact degree-one endpoint.
Its degree-one Big-O scale is identically zero, so both errors vanish eventually.
Eliminate those errors from the bounds. This shows that the endpoint required by
the sufficiency theorem is necessary under the current statement. -/
theorem degreeOne_bounds_of_generalL (h : lls_generalL) : DegreeOneValueBounds := by
  obtain ⟨eU, eR, _, _, hU, hR, hv⟩ := h 1 (by norm_num only)
  have hzU : ∀ᶠ f in conductorFilter 1, eU f = 0 := by
    filter_upwards [hU.eq_zero_imp] with f hf
    apply hf
    simp only [Nat.cast_one, Real.log_one, zero_pow (by norm_num only : (2 : ℕ) ≠ 0), mul_zero,
      zero_div]
  have hzR : ∀ᶠ f in conductorFilter 1, eR f = 0 := by
    filter_upwards [hR.eq_zero_imp] with f hf
    apply hf
    simp only [Nat.cast_one, Real.log_one, zero_pow (by norm_num only : (2 : ℕ) ≠ 0), mul_zero,
      zero_div]
  filter_upwards [hv, hzU, hzR] with f hf hUf hRf
  dsimp only
  rw [hUf, hRf] at hf
  simpa only [pow_one, Nat.cast_one, Real.log_one, one_mul, mul_zero, zero_add, add_zero,
    Nat.sub_self, pow_zero, mul_one] using hf

/-- Given second-order Mangoldt and psi bounds with nonnegative psi constant,
the public general L-value proposition is equivalent to its exact degree-one endpoint.
Combine the sufficient construction for all degrees with the necessary endpoint.
The arithmetic bounds and exact endpoint remain explicit requirements. -/
theorem generalL_iff_degreeOne_of_primeSum_bounds {A B : ℝ} (hB : 0 ≤ B)
    (hH :
      ∀ᶠ x : ℝ in Filter.atTop,
        |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
              (Real.log (Real.log x) + Real.eulerMascheroniConstant)| ≤
          A / (Real.log x) ^ 2)
    (hψ : ∀ᶠ x : ℝ in Filter.atTop, |Chebyshev.psi x - x| ≤ B * x / (Real.log x) ^ 2) :
    lls_generalL ↔ DegreeOneValueBounds := by
  exact ⟨degreeOne_bounds_of_generalL, generalL_of_primeSum_bounds_and_degreeOne hB hH hψ⟩

/-- The two named unconditional arithmetic hypotheses and the exact degree-one endpoint
imply the public general L-value proposition. Extract their constants and eventual bounds,
then apply the existing sufficient criterion. The arithmetic estimates remain hypotheses. -/
theorem generalL_of_secondOrderBounds_and_degreeOne
    (hψ : AnalyticNumberTheory.Arithmetic.PsiSecondOrderBound)
    (hH : AnalyticNumberTheory.Arithmetic.MangoldtLogSumSecondOrderBound)
    (hOne : DegreeOneValueBounds) : lls_generalL := by
  exact
    hψ.elim
      (fun _ hψb ↦
        hH.elim (fun _ hHa ↦ generalL_of_primeSum_bounds_and_degreeOne hψb.1 hHa.2 hψb.2 hOne))

end PseudoPrime.LLS.Extensions.GeneralLFunction
