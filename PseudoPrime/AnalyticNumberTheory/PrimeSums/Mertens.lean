/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.PrimeSums.PsiError
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtMertens

/-! # Unconditional prime-sum and Mertens consequences -/

public section

namespace PseudoPrime.AnalyticNumberTheory.PrimeSums

/-- The logarithmically weighted Mangoldt prime sum has its second-order estimate
unconditionally, with Euler's constant identified. Apply the proved unconditional
psi input to the established Mangoldt-Mertens transfer. No additional zeta RH is needed. -/
theorem mangoldtSecondOrderBound_unconditional : Arithmetic.MangoldtLogSumSecondOrderBound := by
  exact Arithmetic.mangoldtSecondOrder_of_psi psiSecondOrderBound_unconditional

/-- The psi-error integral constant equals Euler's constant without additional
assumptions. Supply the proved unconditional second-order psi estimate to the
constant-identification theorem. This removes the final arithmetic constant input. -/
theorem psiMertensConstant_eq_euler_unconditional :
    Arithmetic.psiMertensConstant = Real.eulerMascheroniConstant := by
  exact Arithmetic.psiMertensConstant_eq_euler psiSecondOrderBound_unconditional

end PseudoPrime.AnalyticNumberTheory.PrimeSums
