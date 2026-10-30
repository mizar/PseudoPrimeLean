/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.GeneralValueCriteria
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtMertens

/-! Separate fixed-degree variants of the general L-value statement. -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- The original value bounds restricted to degrees at least two.
Errors are uniform within each fixed-degree conductor family, with the original rate.
No uniformity across degrees or degree-one endpoint is asserted. -/
def lls_generalL_ge_two : Prop :=
  ∀ d : ℕ,
    1 < d →
      ∃ eUpper eReciprocal : GeneralLFunction.FixedDegreeFamily d → ℝ,
        Asymptotics.IsLittleO (GeneralLFunction.conductorFilter d) eUpper (fun _ ↦ (1 : ℝ)) ∧
          Asymptotics.IsLittleO (GeneralLFunction.conductorFilter d) eReciprocal (fun _ ↦ (1 : ℝ)) ∧
          Asymptotics.IsBigO (GeneralLFunction.conductorFilter d) eUpper
            (fun f ↦ (d : ℝ) ^ 2 * (Real.log d) ^ 2 / Real.log (Real.log f.val.analyticConductor)) ∧
          Asymptotics.IsBigO (GeneralLFunction.conductorFilter d) eReciprocal
            (fun f ↦ (d : ℝ) ^ 2 * (Real.log d) ^ 2 / Real.log (Real.log f.val.analyticConductor)) ∧
          ∀ᶠ f in GeneralLFunction.conductorFilter d,
            ‖f.val.L 1‖ ≤
                (2 * Real.exp Real.eulerMascheroniConstant) ^ d *
                  ((Real.log (Real.log f.val.analyticConductor)) ^ d -
                    ((d : ℝ) * Real.log d + d * (Real.log 2 - 1 / 2) + eUpper f) *
                      (Real.log (Real.log f.val.analyticConductor)) ^ (d - 1)) ∧
              1 / ‖f.val.L 1‖ ≤
                (12 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2) ^ d *
                  ((Real.log (Real.log f.val.analyticConductor)) ^ d -
                    ((d : ℝ) * Real.log d + d * (Real.log 2 - 1 / 2) + eReciprocal f) *
                      (Real.log (Real.log f.val.analyticConductor)) ^ (d - 1))

/-- Value bounds with a nonzero error scale at every positive degree.
Only the error rate changes to `d²(1+log d)²/log log C`; the value bounds stay unchanged.
Uniformity is within each fixed degree, and the original proposition remains separate. -/
def lls_generalL_nonvanishing : Prop :=
  ∀ d : ℕ,
    0 < d →
      ∃ eUpper eReciprocal : GeneralLFunction.FixedDegreeFamily d → ℝ,
        Asymptotics.IsLittleO (GeneralLFunction.conductorFilter d) eUpper (fun _ ↦ (1 : ℝ)) ∧
          Asymptotics.IsLittleO (GeneralLFunction.conductorFilter d) eReciprocal (fun _ ↦ (1 : ℝ)) ∧
          Asymptotics.IsBigO (GeneralLFunction.conductorFilter d) eUpper
            (fun f ↦
              (d : ℝ) ^ 2 * (1 + Real.log d) ^ 2 / Real.log (Real.log f.val.analyticConductor)) ∧
          Asymptotics.IsBigO (GeneralLFunction.conductorFilter d) eReciprocal
            (fun f ↦
              (d : ℝ) ^ 2 * (1 + Real.log d) ^ 2 / Real.log (Real.log f.val.analyticConductor)) ∧
          ∀ᶠ f in GeneralLFunction.conductorFilter d,
            ‖f.val.L 1‖ ≤
                (2 * Real.exp Real.eulerMascheroniConstant) ^ d *
                  ((Real.log (Real.log f.val.analyticConductor)) ^ d -
                    ((d : ℝ) * Real.log d + d * (Real.log 2 - 1 / 2) + eUpper f) *
                      (Real.log (Real.log f.val.analyticConductor)) ^ (d - 1)) ∧
              1 / ‖f.val.L 1‖ ≤
                (12 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2) ^ d *
                  ((Real.log (Real.log f.val.analyticConductor)) ^ d -
                    ((d : ℝ) * Real.log d + d * (Real.log 2 - 1 / 2) + eReciprocal f) *
                      (Real.log (Real.log f.val.analyticConductor)) ^ (d - 1))

namespace GeneralLFunction

/-- The two explicit second-order arithmetic hypotheses imply this fixed-degree variant.
Extract their constants and use the uniform value correction; no degree-one exact
endpoint or additional Riemann hypothesis is assumed. The arithmetic inputs remain unproved. -/
theorem generalL_ge_two_of_bounds (hψ : AnalyticNumberTheory.Arithmetic.PsiSecondOrderBound)
    (hH : AnalyticNumberTheory.Arithmetic.MangoldtLogSumSecondOrderBound) :
    lls_generalL_ge_two := by
  obtain ⟨B, hB, hψb⟩ := hψ
  obtain ⟨A, _, hHa⟩ := hH
  intro d hd
  have hd0 : 0 < d := Nat.zero_lt_of_lt hd
  let e := fun f : FixedDegreeFamily d ↦
    valueUpperCorrection d (Real.log (2 * (d : ℝ))) ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1)
      (Real.log (Real.log f.val.analyticConductor))
  have hs :=
    isLittleO_valueUpperCorrection_on_conductorFilter d (Real.log (2 * (d : ℝ)))
      ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1)
  have hb :=
    isBigO_valueUpperCorrection_on_conductorFilter hd (Real.log (2 * (d : ℝ)))
      ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1)
  exact
    ⟨e, e, hs, hs, hb, hb,
      eventually_value_bounds_with_correction_of_mangoldt_errors hd0 hB hHa hψb⟩

/-- The two explicit second-order arithmetic hypotheses imply this fixed-degree variant.
Extract their constants and use the uniform value correction; no degree-one exact
endpoint or additional Riemann hypothesis is assumed. The arithmetic inputs remain unproved. -/
theorem generalL_nonvanishing_of_bounds (hψ : AnalyticNumberTheory.Arithmetic.PsiSecondOrderBound)
    (hH : AnalyticNumberTheory.Arithmetic.MangoldtLogSumSecondOrderBound) :
    lls_generalL_nonvanishing := by
  obtain ⟨B, hB, hψb⟩ := hψ
  obtain ⟨A, _, hHa⟩ := hH
  intro d hd
  let e := fun f : FixedDegreeFamily d ↦
    valueUpperCorrection d (Real.log (2 * (d : ℝ))) ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1)
      (Real.log (Real.log f.val.analyticConductor))
  have hs :=
    isLittleO_valueUpperCorrection_on_conductorFilter d (Real.log (2 * (d : ℝ)))
      ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1)
  have hb :=
    isBigO_valueUpperCorrection_nonvanishing_on_conductorFilter hd (Real.log (2 * (d : ℝ)))
      ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1)
  exact
    ⟨e, e, hs, hs, hb, hb, eventually_value_bounds_with_correction_of_mangoldt_errors hd hB hHa hψb⟩

/-- A second-order psi estimate alone supplies the degree-at-least-two value bounds.
Derive the logarithmic Mangoldt estimate, including its Euler constant, from psi;
no separate constant-identification hypothesis remains. -/
theorem generalL_ge_two_of_psi (hψ : AnalyticNumberTheory.Arithmetic.PsiSecondOrderBound) :
    lls_generalL_ge_two := by
  exact generalL_ge_two_of_bounds hψ (AnalyticNumberTheory.Arithmetic.mangoldtSecondOrder_of_psi hψ)

/-- A second-order psi estimate alone supplies the nonvanishing error-scale value
bounds in every positive degree. Derive the required Mangoldt input from psi. -/
theorem generalL_nonvanishing_of_psi (hψ : AnalyticNumberTheory.Arithmetic.PsiSecondOrderBound) :
    lls_generalL_nonvanishing := by
  exact
    generalL_nonvanishing_of_bounds hψ
      (AnalyticNumberTheory.Arithmetic.mangoldtSecondOrder_of_psi hψ)

end GeneralLFunction

end PseudoPrime.LLS.Extensions
