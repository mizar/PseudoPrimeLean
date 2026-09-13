/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.Theorem11S1FullLevel
import PseudoPrime.LLS.PrimitiveLogWeightedBounds
import PseudoPrime.LLS.PrimitiveReciprocalWeightedBounds

/-! # General-character analytic estimates for LLS S1

The primitive logarithmic and reciprocal bounds give the exact full-level upper bound.
The quotient variants retain their explicit additional numerical hypotheses.
-/

namespace PseudoPrime.LLS

/-!
Input/assumptions: a level character with `q ≥ 3000`, `χ ≠ 1`, and GRH.
Conclusion: the generic primitive logarithmic raw bound is supplied to the Part 1 weighted API.
Content: use the radius root `y > 8`, set `x = y²`, and rewrite `sqrt (y²)`, the conductor log,
and the Part 1 definition.  No quadratic or self-duality hypothesis is used.
Role: first exact-conductor handoff from the generic contour theorem to the shared-witness core.
-/

theorem llsPart1PrimitiveWeightedUpperAt_of_grh_generic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    LLSPart1PrimitiveWeightedUpperAt χ
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| := by
  have hprimitive : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hprimne : χ.primitiveCharacter ≠ 1 := by
    intro hp
    have hchange := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [hp] at hchange
    simp only [DirichletCharacter.changeLevel_one] at hchange
    exact hne hchange.symm
  have hinv : χ.primitiveCharacter⁻¹ ≠ 1 := by
    intro hinvone
    apply hprimne
    exact inv_eq_one.mp hinvone
  have hN2 : 2 ≤ χ.conductor := by
    have hN1 : χ.conductor ≠ 1 :=
      AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one
        hprimne
    have hNpos : 0 < χ.conductor := NeZero.pos χ.conductor
    omega
  have hy : (8 : ℝ) < llsTheorem11S1RadiusRoot q := eight_lt_llsTheorem11S1RadiusRoot hq
  have hypos : (0 : ℝ) < llsTheorem11S1RadiusRoot q := lt_trans (by norm_num only) hy
  have hx64 : (64 : ℝ) ≤ (llsTheorem11S1RadiusRoot q) ^ 2 :=
    Analysis.sq_ge_64_of_ge_8 hy.le
  have hsqrt : Real.sqrt ((llsTheorem11S1RadiusRoot q) ^ 2) = llsTheorem11S1RadiusRoot q := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hraw := primitiveGenericLogWeightedUpper_of_grh_generic hN2 hGRH hprimitive hprimne hinv hx64
  rw [hsqrt] at hraw
  have hlogdiv : Real.log ((χ.conductor : ℝ) / Real.pi) = Real.log χ.conductor - Real.log Real.pi :=
    Real.log_div (by exact_mod_cast χ.conductor_ne_zero) Real.pi_ne_zero
  unfold LLSPart1PrimitiveWeightedUpperAt
  rw [hlogdiv]
  convert hraw using 1
  ring

/-!
Input/assumptions: `q ≥ 3000`, a nontrivial level character, and GRH.
Conclusion: the generic reciprocal contour raw estimate supplies the Part 1 zero-mass witness.
Content: specialize `primitiveReciprocalRaw_of_grh` at `x = y²`, with `y` the Part 1 radius root,
and rewrite `sqrt (y²) = y`.
Role: supplies the raw reciprocal bound before exact level/conductor absorption.
-/

theorem llsPart1PrimitiveReciprocalExplicitFormulaRawAt_of_grh_generic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    LLSPart1PrimitiveReciprocalExplicitFormulaRawAt χ
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| := by
  have hprimitive : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hprimne : χ.primitiveCharacter ≠ 1 := by
    intro hp
    have hchange := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [hp] at hchange
    simp only [DirichletCharacter.changeLevel_one] at hchange
    exact hne hchange.symm
  have hinv : χ.primitiveCharacter⁻¹ ≠ 1 := by
    intro hinvone
    apply hprimne
    exact inv_eq_one.mp hinvone
  have hy : (8 : ℝ) < llsTheorem11S1RadiusRoot q := eight_lt_llsTheorem11S1RadiusRoot hq
  have hypos : (0 : ℝ) < llsTheorem11S1RadiusRoot q := lt_trans (by norm_num only) hy
  have hx64 : (64 : ℝ) ≤ (llsTheorem11S1RadiusRoot q) ^ 2 :=
    Analysis.sq_ge_64_of_ge_8 hy.le
  have hsqrt : Real.sqrt ((llsTheorem11S1RadiusRoot q) ^ 2) = llsTheorem11S1RadiusRoot q := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hraw :=
    primitiveReciprocalRaw_of_grh (χ := χ.primitiveCharacter)
      (show 2 ≤ χ.conductor
        by
        have hN1 : χ.conductor ≠ 1 :=
          AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one
            hprimne
        have hNpos : 0 < χ.conductor := NeZero.pos χ.conductor
        omega)
      hGRH hprimitive hprimne hinv hx64
  rw [hsqrt] at hraw
  have hd_ne : (χ.conductor : ℝ) ≠ 0 := by exact_mod_cast χ.conductor_ne_zero
  have hlogd : Real.log ((χ.conductor : ℝ) / Real.pi) = Real.log χ.conductor - Real.log Real.pi :=
    Real.log_div hd_ne Real.pi_ne_zero
  unfold LLSPart1PrimitiveReciprocalExplicitFormulaRawAt
  dsimp
  rw [hlogd]
  have hstep :=
    add_le_add_left hraw
      ((1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
          |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
        1 / 4)
  have hcanon :
    (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
          |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
        1 / 4 +
        (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
            (llsTheorem11S1RadiusRoot q ^ 2) χ.primitiveCharacter).re ≤
      1 / 2 * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) *
        (Real.log χ.conductor - Real.log Real.pi) := by
    calc
      _ =
          (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
                (llsTheorem11S1RadiusRoot q ^ 2) χ.primitiveCharacter).re +
            ((1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
                |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                    χ.primitiveCharacter| +
              1 / 4) :=
        by ring
      _ ≤
          1 / 2 * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) *
                (Real.log χ.conductor - Real.log Real.pi) -
              1 / 4 -
              (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
                |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                    χ.primitiveCharacter| +
            ((1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
                |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                    χ.primitiveCharacter| +
              1 / 4) :=
        hstep
      _ = _ := by ring
  apply (le_sub_iff_add_le).2
  apply (le_sub_iff_add_le).2
  convert hcanon using 1

/-!
The generic exact conductor-absorption step for the reciprocal zero-mass witness.
-/

theorem llsPart1PrimitiveZeroMassFullLevelRawAt_of_grh_generic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h24 : LLSRiemannReciprocalLowerBound) (hsmall : llsTheorem11S1NoSmallPrime χ) :
    LLSPart1PrimitiveZeroMassFullLevelRawAt χ
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| := by
  have hraw := llsPart1PrimitiveReciprocalExplicitFormulaRawAt_of_grh_generic χ hq hne hGRH
  unfold LLSPart1PrimitiveReciprocalExplicitFormulaRawAt at hraw
  have hlevelchange := llsPart1PrimitiveReciprocalLowerWithLevelChangeAt_of_riemann h24 χ hq hsmall
  rw [LLSPart1PrimitiveReciprocalLowerWithLevelChangeAt] at hlevelchange
  have hy : (8 : ℝ) < llsTheorem11S1RadiusRoot q := eight_lt_llsTheorem11S1RadiusRoot hq
  have hx2 : (2 : ℝ) ≤ (llsTheorem11S1RadiusRoot q) ^ 2 := by
    have h64 := Analysis.sq_ge_64_of_ge_8 hy.le
    exact le_trans (by norm_num only) h64
  have hqd : q / χ.conductor ≠ 0 := by
    rw [Nat.div_ne_zero_iff]
    exact
      ⟨χ.conductor_ne_zero, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level⟩
  have habsorb :=
    AnalyticNumberTheory.Arithmetic.primitiveReciprocalConductorAbsorption
      ((llsTheorem11S1RadiusRoot q) ^ 2) χ hx2 hqd
  have hd_ne : (χ.conductor : ℝ) ≠ 0 := by exact_mod_cast χ.conductor_ne_zero
  have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hlogd : Real.log ((χ.conductor : ℝ) / Real.pi) = Real.log χ.conductor - Real.log Real.pi :=
    Real.log_div hd_ne Real.pi_ne_zero
  have hlogq : Real.log ((q : ℝ) / Real.pi) = Real.log q - Real.log Real.pi :=
    Real.log_div hq_ne Real.pi_ne_zero
  rw [hlogd] at hraw
  unfold LLSPart1PrimitiveZeroMassFullLevelRawAt
  rw [hlogq]
  have hlevel :
    (1 / 2) * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) * (Real.log χ.conductor - Real.log Real.pi) -
        (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
            (llsTheorem11S1RadiusRoot q ^ 2) χ.primitiveCharacter).re -
        1 / 4 ≤
      (1 / 2) * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) *
          (Real.log χ.conductor - Real.log Real.pi) -
        llsAuxiliaryTerm q -
        AnalyticNumberTheory.Arithmetic.primitiveReciprocalLevelChangeCorrection
          (llsTheorem11S1RadiusRoot q ^ 2) χ -
        1 / 4 := by
    have h :=
      sub_le_sub_left hlevelchange
        ((1 / 2) * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) *
            (Real.log χ.conductor - Real.log Real.pi) -
          1 / 4)
    convert h using 1 <;> ring
  have habsorb' :
    (1 / 2) * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) * (Real.log χ.conductor - Real.log Real.pi) -
        llsAuxiliaryTerm q -
        AnalyticNumberTheory.Arithmetic.primitiveReciprocalLevelChangeCorrection
          (llsTheorem11S1RadiusRoot q ^ 2) χ -
        1 / 4 ≤
      (1 / 2) * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) * (Real.log q - Real.log Real.pi) -
        llsAuxiliaryTerm q -
        1 / 4 := by
    have h :=
      add_le_add_right habsorb
        (-(1 / 2) * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) * Real.log Real.pi -
          llsAuxiliaryTerm q -
          1 / 4)
    convert h using 1 <;> ring
  have hfinal :
    (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
        |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      (1 / 2) * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) * (Real.log q - Real.log Real.pi) -
        llsAuxiliaryTerm q -
        1 / 4 :=
    hraw.trans (hlevel.trans habsorb')
  convert hfinal using 1

/-!
The generic full-level logarithmic upper bound.  This combines the generic log weighted handoff,
the generic reciprocal zero-mass raw bound, the exact primitive/level identity, and the generic
logarithmic conductor absorption without any quadratic hypothesis.
-/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
theorem characterLogWeightedSum_re_le_fullLevel_of_grh_generic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h24 : LLSRiemannReciprocalLowerBound) (hsmall : llsTheorem11S1NoSmallPrime χ) :
    (characterLogWeightedSum
          ((llsTheorem11S1RadiusRoot q) ^ 2) χ).re ≤
      llsPart1PrimitiveFullLevelUpperBound q := by
  have hweighted := llsPart1PrimitiveWeightedUpperAt_of_grh_generic χ hq hne hGRH
  unfold LLSPart1PrimitiveWeightedUpperAt at hweighted
  have hzeromass := llsPart1PrimitiveZeroMassFullLevelRawAt_of_grh_generic χ hq hne hGRH h24 hsmall
  unfold LLSPart1PrimitiveZeroMassFullLevelRawAt at hzeromass
  have hexact :=
    characterLogWeightedSum_re_primitive_eq_add_levelChangeCorrection
      ((llsTheorem11S1RadiusRoot q) ^ 2) χ
  have hy8 : (8 : ℝ) < llsTheorem11S1RadiusRoot q := eight_lt_llsTheorem11S1RadiusRoot hq
  have hypos : (0 : ℝ) < llsTheorem11S1RadiusRoot q := lt_trans (by norm_num only) hy8
  have hqd : q / χ.conductor ≠ 0 := by
    rw [Nat.div_ne_zero_iff]
    exact
      ⟨χ.conductor_ne_zero, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level⟩
  have hx2 : (2 : ℝ) ≤ (llsTheorem11S1RadiusRoot q) ^ 2 := by
    have h64 := Analysis.sq_ge_64_of_ge_8 hy8.le
    exact le_trans (by norm_num only) h64
  have habsorb :=
    primitiveLogConductorAbsorption
      ((llsTheorem11S1RadiusRoot q) ^ 2) χ hx2 hqd
  have hlogxnn : (0 : ℝ) ≤ Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) :=
    Real.log_nonneg (le_trans (by norm_num only) hx2)
  have hC22nonneg :
    (0 : ℝ) ≤ 2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) := by
    have hroot_nonneg : (0 : ℝ) ≤ llsTheorem11S1RadiusRoot q := le_of_lt hypos
    exact
      add_nonneg (add_nonneg (mul_nonneg (by norm_num only) hroot_nonneg) (by norm_num only))
        hlogxnn
  have hinv2pos : (0 : ℝ) < (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 := by
    have hpos : (0 : ℝ) < 1 - 1 / llsTheorem11S1RadiusRoot q := by
      rw [sub_pos, div_lt_one hypos]
      exact lt_trans (by norm_num only) hy8
    exact sq_pos_of_pos hpos
  have hlogqdiv : Real.log ((q : ℝ) / Real.pi) = Real.log q - Real.log Real.pi :=
    Real.log_div (by exact_mod_cast (NeZero.ne q)) Real.pi_ne_zero
  rw [hlogqdiv] at hzeromass
  have hbdiv :
    |primitiveBRe χ.primitiveCharacter| ≤
      (1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * (Real.log q - Real.log Real.pi) -
          llsAuxiliaryTerm q -
          1 / 4) /
        (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 :=
    (le_div_iff₀ hinv2pos).mpr
      (by
        rw [mul_comm]
        exact hzeromass)
  have hmul := mul_le_mul_of_nonneg_left hbdiv hC22nonneg
  have hmuleq :
    (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
        ((1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * (Real.log q - Real.log Real.pi) -
            llsAuxiliaryTerm q -
            1 / 4) /
          (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2) =
      (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) /
          (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
        (1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * (Real.log q - Real.log Real.pi) -
          llsAuxiliaryTerm q -
          1 / 4) := by
    ring
  rw [hmuleq] at hmul
  unfold llsPart1PrimitiveFullLevelUpperBound
  rw [show Real.log ((χ.conductor : ℝ) / Real.pi) = Real.log χ.conductor - Real.log Real.pi from
      Real.log_div (by exact_mod_cast χ.conductor_ne_zero) Real.pi_ne_zero] at hweighted
  change
    (characterLogWeightedSum
          (llsTheorem11S1RadiusRoot q ^ 2) χ).re ≤
      (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log (llsTheorem11S1RadiusRoot q ^ 2)) /
              (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
            (1 / 2 * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) * (Real.log ↑q - Real.log Real.pi) -
              llsAuxiliaryTerm q -
              1 / 4) +
          1 / 2 * (Real.log ↑q - Real.log Real.pi) * Real.log (llsTheorem11S1RadiusRoot q ^ 2) -
        11 / 4
  change
    (characterLogWeightedSum
          (llsTheorem11S1RadiusRoot q ^ 2) χ.primitiveCharacter).re ≤
      (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log (llsTheorem11S1RadiusRoot q ^ 2)) *
            |primitiveBRe
                χ.primitiveCharacter| +
          (Real.log ↑χ.conductor - Real.log Real.pi) * Real.log (llsTheorem11S1RadiusRoot q ^ 2) /
            2 -
        11 / 4 at hweighted
  have hmain :
    (characterLogWeightedSum
          (llsTheorem11S1RadiusRoot q ^ 2) χ.primitiveCharacter).re ≤
      (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log (llsTheorem11S1RadiusRoot q ^ 2)) /
              (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
            (1 / 2 * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) * (Real.log ↑q - Real.log Real.pi) -
              llsAuxiliaryTerm q -
              1 / 4) +
          (Real.log ↑χ.conductor - Real.log Real.pi) * Real.log (llsTheorem11S1RadiusRoot q ^ 2) /
            2 -
        11 / 4 := by
    exact hweighted.trans (sub_le_sub_right (add_le_add_left hmul _) _)
  have hsub :
    (characterLogWeightedSum
            (llsTheorem11S1RadiusRoot q ^ 2) χ.primitiveCharacter).re -
        primitiveLogLevelChangeCorrection
          (llsTheorem11S1RadiusRoot q ^ 2) χ ≤
      (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log (llsTheorem11S1RadiusRoot q ^ 2)) /
              (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
            (1 / 2 * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) * (Real.log ↑q - Real.log Real.pi) -
              llsAuxiliaryTerm q -
              1 / 4) +
          (Real.log ↑χ.conductor - Real.log Real.pi) * Real.log (llsTheorem11S1RadiusRoot q ^ 2) /
            2 -
        11 / 4 -
        primitiveLogLevelChangeCorrection
          (llsTheorem11S1RadiusRoot q ^ 2) χ :=
    sub_le_sub_right hmain _
  have hcorr :
    (Real.log ↑χ.conductor - Real.log Real.pi) * Real.log (llsTheorem11S1RadiusRoot q ^ 2) / 2 -
        primitiveLogLevelChangeCorrection
          (llsTheorem11S1RadiusRoot q ^ 2) χ ≤
      (Real.log ↑q - Real.log Real.pi) * Real.log (llsTheorem11S1RadiusRoot q ^ 2) / 2 := by
    have h :=
      add_le_add_right habsorb (-Real.log Real.pi * Real.log (llsTheorem11S1RadiusRoot q ^ 2) / 2)
    convert h using 1 <;> ring
  calc
    (characterLogWeightedSum
            (llsTheorem11S1RadiusRoot q ^ 2) χ).re =
        (characterLogWeightedSum
              (llsTheorem11S1RadiusRoot q ^ 2) χ.primitiveCharacter).re -
          primitiveLogLevelChangeCorrection
            (llsTheorem11S1RadiusRoot q ^ 2) χ :=
      by
      rw [hexact]
      ring
    _ ≤ _ :=
      hsub.trans
        (by
          calc
            _ =
                (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log (llsTheorem11S1RadiusRoot q ^ 2)) /
                        (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
                      (1 / 2 * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) *
                          (Real.log ↑q - Real.log Real.pi) -
                        llsAuxiliaryTerm q -
                        1 / 4) +
                    ((Real.log ↑χ.conductor - Real.log Real.pi) *
                          Real.log (llsTheorem11S1RadiusRoot q ^ 2) /
                        2 -
                      primitiveLogLevelChangeCorrection
                        (llsTheorem11S1RadiusRoot q ^ 2) χ) -
                  11 / 4 :=
              by ring
            _ =
                ((Real.log ↑χ.conductor - Real.log Real.pi) *
                          Real.log (llsTheorem11S1RadiusRoot q ^ 2) /
                        2 -
                      primitiveLogLevelChangeCorrection
                        (llsTheorem11S1RadiusRoot q ^ 2) χ) +
                    (2 * llsTheorem11S1RadiusRoot q + 2 +
                          Real.log (llsTheorem11S1RadiusRoot q ^ 2)) /
                        (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
                      (1 / 2 * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) *
                          (Real.log ↑q - Real.log Real.pi) -
                        llsAuxiliaryTerm q -
                        1 / 4) -
                  11 / 4 :=
              by ring
            _ ≤
                (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log (llsTheorem11S1RadiusRoot q ^ 2)) /
                        (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
                      (1 / 2 * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) *
                          (Real.log ↑q - Real.log Real.pi) -
                        llsAuxiliaryTerm q -
                        1 / 4) +
                    (1 / 2 * (Real.log ↑q - Real.log Real.pi) *
                      Real.log (llsTheorem11S1RadiusRoot q ^ 2)) -
                  11 / 4 :=
              by
              convert
                  sub_le_sub_right
                    (add_le_add_left hcorr
                      ((2 * llsTheorem11S1RadiusRoot q + 2 +
                            Real.log (llsTheorem11S1RadiusRoot q ^ 2)) /
                          (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
                        (1 / 2 * (1 - 1 / llsTheorem11S1RadiusRoot q ^ 2) *
                            (Real.log ↑q - Real.log Real.pi) -
                          llsAuxiliaryTerm q -
                          1 / 4)))
                    (11 / 4) using
                  1
              try ring
            _ = _ := by ring)

/-!
The exact generic full-level logarithmic estimate now consumes the existing numerical chain.
The intermediate expression has a historical quadratic name, but is independent of the character;
the proved coarsening bridge therefore supplies the standard Part 1 upper bound without a quotient
slack hypothesis.
-/

theorem characterLogWeightedSum_re_le_upper_of_grh_generic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h24 : LLSRiemannReciprocalLowerBound) (hsmall : llsTheorem11S1NoSmallPrime χ) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
          ((llsTheorem11S1RadiusRoot q) ^ 2) χ).re ≤
      llsTheorem11S1UpperBound q := by
  have hfull := characterLogWeightedSum_re_le_fullLevel_of_grh_generic χ hq hne hGRH h24 hsmall
  have hcoarse := llsPart1PrimitiveFullLevelUpperBound_le_fullLevel hq
  have hinter := llsPart1FullLevelUpperBound_le_intermediate hq
  have hupper := llsPart1IntermediateUpperBound_le_upper hq
  exact hfull.trans (hcoarse.trans (hinter.trans hupper))

/-!
Coefficient bridge for the quotient raw interface.  It isolates the only extra numerical input
needed beyond the reciprocal explicit formula: the max-defined auxiliary term must equal its
untruncated expression (which may be zero), and `log(conductor/π)` must be nonnegative.
-/

theorem llsPart1PrimitiveZeroMassRawUpperWithQuotientAt_of_explicit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (b : ℝ) (hq : 3000 ≤ q)
    (hraw : LLSPart1PrimitiveReciprocalExplicitFormulaRawAt χ b)
    (hlower : LLSPart1PrimitiveReciprocalLowerAtWithQuotient χ)
    (haux :
      llsAuxiliaryTerm q ≤
        2 * Real.log (Real.log q) - 8 / 5 -
          AnalyticNumberTheory.Arithmetic.primeFactorLogSum q)
    (hlog : 0 ≤ Real.log ((χ.conductor : ℝ) / Real.pi)) :
    LLSPart1PrimitiveZeroMassRawUpperWithQuotientAt χ b := by
  have hy : (8 : ℝ) ≤ llsTheorem11S1RadiusRoot q := (eight_lt_llsTheorem11S1RadiusRoot hq).le
  have hroot_gt : (1 : ℝ) < llsTheorem11S1RadiusRoot q := lt_of_lt_of_le (by norm_num only) hy
  have hypos : (0 : ℝ) < llsTheorem11S1RadiusRoot q := lt_of_lt_of_le (by norm_num only) hy
  have ha : (0 : ℝ) < 1 - 1 / llsTheorem11S1RadiusRoot q := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ hypos).2
    rw [one_mul]
    exact hroot_gt
  have ha2 : (0 : ℝ) < (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 := sq_pos_of_pos ha
  have hsub : llsTheorem11S1RadiusRoot q - 1 ≠ 0 := sub_ne_zero.mpr hroot_gt.ne.symm
  have hinv2 :
    (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 =
      (llsTheorem11S1RadiusRoot q) ^ 2 / (llsTheorem11S1RadiusRoot q - 1) ^ 2 := by
    have hfrac :
      1 - 1 / llsTheorem11S1RadiusRoot q =
        (llsTheorem11S1RadiusRoot q - 1) / llsTheorem11S1RadiusRoot q := by
      apply (eq_div_iff hypos.ne').2
      rw [sub_mul, div_mul_cancel₀ _ hypos.ne']
      ring
    rw [hfrac, inv_div, div_pow]
  have hauxnonneg := llsAuxiliaryTerm_nonneg q
  have hbase :
    llsAuxiliaryTerm q =
      2 * Real.log (Real.log q) - 8 / 5 -
        AnalyticNumberTheory.Arithmetic.primeFactorLogSum q := by
    exact le_antisymm haux (le_max_right _ _)
  have hraw' := hraw
  have hlower' := hlower
  unfold LLSPart1PrimitiveReciprocalExplicitFormulaRawAt at hraw'
  unfold LLSPart1PrimitiveReciprocalLowerAtWithQuotient at hlower'
  rw [← hbase] at hlower'
  unfold LLSPart1PrimitiveZeroMassRawUpperWithQuotientAt
    llsPart1PrimitiveReciprocalQuotientCorrection
  dsimp
  apply le_of_mul_le_mul_right ?_ ha2
  have hprod_inv :
    (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 * (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ha.ne']
    rw [one_pow]
  have hmul :
    (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
        ((1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 * (Real.log ((χ.conductor : ℝ) / Real.pi) / 2) -
            llsAuxiliaryTerm q -
            1 / 4 +
          (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 *
            AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor)) =
      Real.log ((χ.conductor : ℝ) / Real.pi) / 2 -
          (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 * (llsAuxiliaryTerm q + 1 / 4) +
        AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor) := by
    calc
      _ =
          ((1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 * (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2) *
                (Real.log ((χ.conductor : ℝ) / Real.pi) / 2) -
              (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 * (llsAuxiliaryTerm q + 1 / 4) +
            ((1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
                (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2) *
              AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor) :=
        by ring
      _ = _ := by
        rw [hprod_inv]; ring
  have hfactor : 0 ≤ (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 := sq_nonneg _
  have hfactor_le : (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 ≤ 1 := by
    have hale : 1 - 1 / llsTheorem11S1RadiusRoot q ≤ 1 := by
      have : 0 < (1 / llsTheorem11S1RadiusRoot q) := one_div_pos.mpr hypos
      exact sub_le_self _ this.le
    have hsq := mul_self_le_mul_self ha.le hale
    calc
      (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 =
          (1 - 1 / llsTheorem11S1RadiusRoot q) * (1 - 1 / llsTheorem11S1RadiusRoot q) :=
        by ring
      _ ≤ 1 * 1 := hsq
      _ = 1 := by ring
  have hlogterm :
    1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * Real.log ((χ.conductor : ℝ) / Real.pi) ≤
      Real.log ((χ.conductor : ℝ) / Real.pi) / 2 := by
    have hcoef : 0 ≤ 1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2 := by
      have hsq := mul_self_le_mul_self (show (0 : ℝ) ≤ 8 by norm_num only) hy
      have : (1 : ℝ) ≤ (llsTheorem11S1RadiusRoot q) ^ 2 := by
        calc
          (1 : ℝ) ≤ 64 := by norm_num only
          _ = 8 * 8 := by norm_num only
          _ ≤ llsTheorem11S1RadiusRoot q * llsTheorem11S1RadiusRoot q := hsq
          _ = (llsTheorem11S1RadiusRoot q) ^ 2 := by ring
      have hone : (0 : ℝ) < 1 := by norm_num only
      exact
        sub_nonneg.mpr
          (by
            simpa only [one_div, ne_eq, one_ne_zero, not_false_eq_true, div_self] using
              (one_div_le_one_div_of_le hone this))
    have hinvnonneg : 0 ≤ 1 / (llsTheorem11S1RadiusRoot q) ^ 2 :=
      div_nonneg (by norm_num only) (sq_nonneg _)
    have hcoef_le : 1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2 ≤ 1 := sub_le_self _ hinvnonneg
    have hprod := mul_le_mul_of_nonneg_right hcoef_le hlog
    calc
      1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * Real.log ((χ.conductor : ℝ) / Real.pi) =
          (1 / 2 : ℝ) *
            ((1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * Real.log ((χ.conductor : ℝ) / Real.pi)) :=
        by ring
      _ ≤ (1 / 2 : ℝ) * (1 * Real.log ((χ.conductor : ℝ) / Real.pi)) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num only)
      _ = Real.log ((χ.conductor : ℝ) / Real.pi) / 2 := by ring
  have hnonneg : 0 ≤ llsAuxiliaryTerm q + 1 / 4 := add_nonneg hauxnonneg (by norm_num only)
  have hauxterm :
    -llsAuxiliaryTerm q - 1 / 4 ≤
      -(1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 * (llsAuxiliaryTerm q + 1 / 4) := by
    have hmul := mul_le_mul_of_nonneg_right hfactor_le hnonneg
    calc
      -llsAuxiliaryTerm q - 1 / 4 = -(1 * (llsAuxiliaryTerm q + 1 / 4)) := by ring
      _ ≤ -((1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 * (llsAuxiliaryTerm q + 1 / 4)) :=
        neg_le_neg hmul
      _ = _ := by ring
  have hbound :
    (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 * b ≤
      Real.log ((χ.conductor : ℝ) / Real.pi) / 2 -
          (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 * (llsAuxiliaryTerm q + 1 / 4) +
        AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor) := by
    have hchar :
      -(AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
                (llsTheorem11S1RadiusRoot q ^ 2) χ.primitiveCharacter).re -
          1 / 4 ≤
        -llsAuxiliaryTerm q - 1 / 4 +
          AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor) := by
      have h := add_le_add (neg_le_neg hlower') (le_refl (-(1 / 4 : ℝ)))
      calc
        _ =
            -(AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
                    (llsTheorem11S1RadiusRoot q ^ 2) χ.primitiveCharacter).re +
              -(1 / 4 : ℝ) :=
          by ring
        _ ≤
            -(llsAuxiliaryTerm q -
                  AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor)) +
              -(1 / 4 : ℝ) :=
          h
        _ = _ := by ring
    calc
      _ ≤
          (1 / 2) * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) *
              Real.log ((χ.conductor : ℝ) / Real.pi) -
            (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
                (llsTheorem11S1RadiusRoot q ^ 2) χ.primitiveCharacter).re -
            1 / 4 :=
        hraw'
      _ ≤
          (1 / 2) * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) *
                Real.log ((χ.conductor : ℝ) / Real.pi) -
              llsAuxiliaryTerm q -
              1 / 4 +
            AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor) :=
        by
        have h :=
          add_le_add
            (le_refl
              ((1 / 2) * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) *
                Real.log ((χ.conductor : ℝ) / Real.pi)))
            hchar
        calc
          _ =
              (1 / 2) * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) *
                  Real.log ((χ.conductor : ℝ) / Real.pi) +
                (-(AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
                        (llsTheorem11S1RadiusRoot q ^ 2) χ.primitiveCharacter).re -
                  1 / 4) :=
            by ring
          _ ≤ _ := h
          _ = _ := by ring
      _ ≤
          Real.log ((χ.conductor : ℝ) / Real.pi) / 2 - llsAuxiliaryTerm q - 1 / 4 +
            AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor) :=
        by
        have h :=
          add_le_add hlogterm
            (le_refl
              (-llsAuxiliaryTerm q - 1 / 4 +
                AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor)))
        calc
          _ =
              (1 / 2) * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) *
                  Real.log ((χ.conductor : ℝ) / Real.pi) +
                (-llsAuxiliaryTerm q - 1 / 4 +
                  AnalyticNumberTheory.Arithmetic.primeFactorLogSum
                    (q / χ.conductor)) :=
            by ring
          _ ≤ _ := h
          _ = _ := by ring
      _ ≤
          Real.log ((χ.conductor : ℝ) / Real.pi) / 2 -
              (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 * (llsAuxiliaryTerm q + 1 / 4) +
            AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor) :=
        by
        have h :=
          add_le_add hauxterm
            (le_refl
              (AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor)))
        calc
          _ =
              Real.log ((χ.conductor : ℝ) / Real.pi) / 2 +
                (-llsAuxiliaryTerm q - 1 / 4 +
                  AnalyticNumberTheory.Arithmetic.primeFactorLogSum
                    (q / χ.conductor)) :=
            by ring
          _ ≤ _ := add_le_add (le_refl (Real.log ((χ.conductor : ℝ) / Real.pi) / 2)) h
          _ = _ := by ring
  calc
    b * (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 = (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 * b :=
      by ring
    _ ≤ _ := hbound
    _ = _ := by
      rw [← hmul]; ring

/-!
Conductor-specialized wrapper for the generic quotient raw bridge.  It removes the conductor-log
sign hypothesis from the caller; only the auxiliary-term branch condition remains explicit.
-/

theorem llsPart1PrimitiveZeroMassRawUpperWithQuotientAt_of_explicit_of_conductor_ge_four {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (b : ℝ) (hq : 3000 ≤ q)
    (hconductor : 4 ≤ χ.conductor) (hraw : LLSPart1PrimitiveReciprocalExplicitFormulaRawAt χ b)
    (hlower : LLSPart1PrimitiveReciprocalLowerAtWithQuotient χ)
    (haux :
      llsAuxiliaryTerm q ≤
        2 * Real.log (Real.log q) - 8 / 5 -
          AnalyticNumberTheory.Arithmetic.primeFactorLogSum q) :
    LLSPart1PrimitiveZeroMassRawUpperWithQuotientAt χ b := by
  exact
    llsPart1PrimitiveZeroMassRawUpperWithQuotientAt_of_explicit χ b hq hraw hlower haux
      (AnalyticNumberTheory.Arithmetic.log_conductor_div_pi_nonneg_of_four_le
        hconductor)

/-!
Restricted raw shared-witness core for the branch where both numerical side conditions are
available.  Keeping these conditions in the interface makes the remaining conductor-two/three
and auxiliary-max branches explicit rather than silently assuming them.
-/

def LLSPart1PrimitiveRawCoreBoundsWithQuotientOfLargeConductor : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 →
      llsTheorem11S1NoSmallPrime χ →
      4 ≤ χ.conductor →
      llsAuxiliaryTerm q ≤
        2 * Real.log (Real.log q) - 8 / 5 -
          AnalyticNumberTheory.Arithmetic.primeFactorLogSum q →
      ∃ b : ℝ,
        0 ≤ b ∧
          LLSPart1PrimitiveWeightedUpperAt χ b ∧
          LLSPart1PrimitiveReciprocalLowerAtWithQuotient χ ∧
          LLSPart1PrimitiveZeroMassRawUpperWithQuotientAt χ b

/-!
The generic analytic estimates construct the restricted quotient raw core with the same
`|PseudoPrime.AnalyticNumberTheory.DirichletLFunction.primitiveBRe|` witness.
-/

theorem llsPart1PrimitiveRawCoreBoundsWithQuotientOfLargeConductor_of_grh_generic
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h24 : LLSRiemannReciprocalLowerBound) :
    LLSPart1PrimitiveRawCoreBoundsWithQuotientOfLargeConductor := by
  intro q _ χ hq hne hsmall hconductor haux
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  refine
    ⟨|AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter|,
      abs_nonneg _, ?_, ?_, ?_⟩
  · exact llsPart1PrimitiveWeightedUpperAt_of_grh_generic χ hq hne hGRH
  · exact llsPart1PrimitiveReciprocalLowerAtWithQuotient_of_riemann h24 χ hq hsmall
  · have hraw := llsPart1PrimitiveReciprocalExplicitFormulaRawAt_of_grh_generic χ hq hne hGRH
    have hlower := llsPart1PrimitiveReciprocalLowerAtWithQuotient_of_riemann h24 χ hq hsmall
    exact
      llsPart1PrimitiveZeroMassRawUpperWithQuotientAt_of_explicit_of_conductor_ge_four χ
        |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| hq
        hconductor hraw hlower haux

/-!
The simplified large-conductor core obtained from the raw core. This consumes
the existing elementary reciprocal-correction simplification and retains the same witness.
-/

def LLSPart1PrimitiveCoreBoundsWithQuotientOfLargeConductor : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 →
      llsTheorem11S1NoSmallPrime χ →
      4 ≤ χ.conductor →
      llsAuxiliaryTerm q ≤
        2 * Real.log (Real.log q) - 8 / 5 -
          AnalyticNumberTheory.Arithmetic.primeFactorLogSum q →
      ∃ b : ℝ,
        0 ≤ b ∧
          LLSPart1PrimitiveWeightedUpperAt χ b ∧ LLSPart1PrimitiveZeroMassUpperWithQuotientAt χ b

/-!
The generic large-conductor raw core feeds the simplified core without changing its witness.
-/

theorem llsPart1PrimitiveCoreBoundsWithQuotientOfLargeConductor_of_grh_generic
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h24 : LLSRiemannReciprocalLowerBound) :
    LLSPart1PrimitiveCoreBoundsWithQuotientOfLargeConductor := by
  intro q _ χ hq hne hsmall hconductor haux
  have hraw :=
    llsPart1PrimitiveRawCoreBoundsWithQuotientOfLargeConductor_of_grh_generic hGRH h24 q χ hq hne
      hsmall hconductor haux
  obtain ⟨b, hb, hweighted, _, hzero⟩ := hraw
  exact ⟨b, hb, hweighted, llsPart1PrimitiveZeroMassSimplificationWithQuotient χ b hq hb hzero⟩

/-!
The combined estimate for the large-conductor branch. The primitive logarithmic comparison
now consumes the generic analytic estimates without reopening the witness construction.
-/

theorem llsPrimitiveLogWeightedSum_re_le_comparisonUpperWithQuotient_of_large_conductor
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h24 : LLSRiemannReciprocalLowerBound) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3000 ≤ q) (hne : χ ≠ 1) (hsmall : llsTheorem11S1NoSmallPrime χ)
    (hconductor : 4 ≤ χ.conductor)
    (haux :
      llsAuxiliaryTerm q ≤
        2 * Real.log (Real.log q) - 8 / 5 -
          AnalyticNumberTheory.Arithmetic.primeFactorLogSum q) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
          ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter).re ≤
      llsTheorem11S1PrimitiveUpperBound χ +
        (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
          llsPart1PrimitiveReciprocalQuotientCorrection χ := by
  have hcore :=
    llsPart1PrimitiveCoreBoundsWithQuotientOfLargeConductor_of_grh_generic hGRH h24 q χ hq hne
      hsmall hconductor haux
  obtain ⟨b, _, hweighted, hzero⟩ := hcore
  exact llsPrimitiveLogWeightedSum_re_le_comparisonUpperWithQuotient hq hweighted hzero

/-!
Original-character comparison for the large-conductor branch. This adds the existing
finite level-to-conductor norm comparison to the generic primitive estimate without introducing a
second witness or a quadratic hypothesis.
-/

theorem characterLogWeightedSum_re_le_comparisonUpperWithQuotient_of_large_conductor
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h24 : LLSRiemannReciprocalLowerBound) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3000 ≤ q) (hne : χ ≠ 1) (hsmall : llsTheorem11S1NoSmallPrime χ)
    (hconductor : 4 ≤ χ.conductor)
    (haux :
      llsAuxiliaryTerm q ≤
        2 * Real.log (Real.log q) - 8 / 5 -
          AnalyticNumberTheory.Arithmetic.primeFactorLogSum q) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
          ((llsTheorem11S1RadiusRoot q) ^ 2) χ).re ≤
      llsTheorem11S1ComparisonUpperBoundWithQuotient χ := by
  have hprimitive :=
    llsPrimitiveLogWeightedSum_re_le_comparisonUpperWithQuotient_of_large_conductor hGRH h24 χ hq
      hne hsmall hconductor haux
  have hy : 0 < llsTheorem11S1RadiusRoot q :=
    (eight_lt_llsTheorem11S1RadiusRoot hq).trans' (by norm_num only)
  have hcomparison :=
    AnalyticNumberTheory.Arithmetic.norm_characterLogWeightedSum_sub_primitive_le
      ((llsTheorem11S1RadiusRoot q) ^ 2) χ (sq_pos_of_pos hy)
  have hre :=
    Complex.re_le_norm
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
          ((llsTheorem11S1RadiusRoot q) ^ 2) χ -
        AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
          ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter)
  rw [llsTheorem11S1ComparisonUpperBoundWithQuotient, llsTheorem11S1ComparisonUpperBound] at ⊢
  calc
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
            ((llsTheorem11S1RadiusRoot q) ^ 2) χ).re =
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
                ((llsTheorem11S1RadiusRoot q) ^ 2) χ -
              AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
                ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter).re +
          (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
              ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter).re :=
      by
      rw [Complex.sub_re]
      ring
    _ ≤
        ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
                ((llsTheorem11S1RadiusRoot q) ^ 2) χ -
              AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
                ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter‖ +
          (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
              ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter).re :=
      add_le_add hre le_rfl
    _ ≤
        (1 / 2 : ℝ) * (q / χ.conductor).primeFactors.card *
            (Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) ^ 2 +
          (llsTheorem11S1PrimitiveUpperBound χ +
            (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
              llsPart1PrimitiveReciprocalQuotientCorrection χ) :=
      add_le_add hcomparison hprimitive
    _ =
        llsTheorem11S1ComparisonUpperBound χ +
          (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
            llsPart1PrimitiveReciprocalQuotientCorrection χ :=
      by
      unfold llsTheorem11S1ComparisonUpperBound
      ring

/-!
Conditional numerical comparison for the quotient correction. The numerical chain controls
`llsTheorem11S1ComparisonUpperBound`; this theorem exposes exactly the additional slack
inequality needed to pass from the quotient-corrected comparison bound to
`llsTheorem11S1UpperBound`.
-/

theorem llsTheorem11S1ComparisonUpperBoundWithQuotient_le_upper_of_correction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q)
    (hcorrection :
      (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
          llsPart1PrimitiveReciprocalQuotientCorrection χ ≤
        llsPart1FullLevelUpperBound q - llsTheorem11S1ComparisonUpperBound χ) :
    llsTheorem11S1ComparisonUpperBoundWithQuotient χ ≤ llsTheorem11S1UpperBound q := by
  have hbase := llsTheorem11S1ComparisonUpperBound_le_fullLevel llsPart1TradeoffCondition χ hq
  have hinter := llsPart1FullLevelUpperBound_le_intermediate hq
  have hupper := llsPart1IntermediateUpperBound_le_upper hq
  unfold llsTheorem11S1ComparisonUpperBoundWithQuotient
  calc
    _ =
        llsTheorem11S1ComparisonUpperBound χ +
          (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log (llsTheorem11S1RadiusRoot q ^ 2)) *
            llsPart1PrimitiveReciprocalQuotientCorrection χ :=
      by ring
    _ ≤
        llsTheorem11S1ComparisonUpperBound χ +
          (llsPart1FullLevelUpperBound q - llsTheorem11S1ComparisonUpperBound χ) :=
      add_le_add_right hcorrection _
    _ = llsPart1FullLevelUpperBound q := by ring
    _ ≤ llsPart1IntermediateUpperBound q := hinter
    _ ≤ llsTheorem11S1UpperBound q := hupper

/-!
The reciprocal quotient correction inherits the preceding logarithmic bound after its
nonnegative radius factor is restored. This is the input for the
Part 1 slack estimate.
-/

theorem llsPart1PrimitiveReciprocalQuotientCorrection_le_log_quotient_factor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    llsPart1PrimitiveReciprocalQuotientCorrection χ ≤
      (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 * Real.log (q / χ.conductor : ℕ) := by
  unfold llsPart1PrimitiveReciprocalQuotientCorrection
  exact
    mul_le_mul_of_nonneg_left
      (AnalyticNumberTheory.Arithmetic.primeFactorLogSum_quotient_le_log χ)
      (sq_nonneg _)

/-!
The arithmetic bounds feed the conditional numerical comparison. The remaining hypothesis is
now stated only as a logarithmic quotient slack, with no prime-factor sum or inverse-square factor.
-/

theorem llsTheorem11S1ComparisonUpperBoundWithQuotient_le_upper_of_log_quotient_slack {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q)
    (hslack :
      (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
          (64 / 49 : ℝ) *
          Real.log (q / χ.conductor : ℕ) ≤
        llsPart1FullLevelUpperBound q - llsTheorem11S1ComparisonUpperBound χ) :
    llsTheorem11S1ComparisonUpperBoundWithQuotient χ ≤ llsTheorem11S1UpperBound q := by
  have hroot : (8 : ℝ) < llsTheorem11S1RadiusRoot q := eight_lt_llsTheorem11S1RadiusRoot hq
  have hlogx : 0 ≤ Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) := by
    apply Real.log_nonneg
    exact le_trans (by norm_num only) (Analysis.sq_ge_64_of_ge_8 hroot.le)
  have hcoefficient :
    0 ≤ 2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) := by
    exact
      add_nonneg
        (add_nonneg (mul_nonneg (by norm_num only) (le_trans (by norm_num only) hroot.le))
          (by norm_num only))
        hlogx
  have hcorr := llsPart1PrimitiveReciprocalQuotientCorrection_le_log_quotient_factor χ
  have hfactor := llsPart1RadiusInverseSq_le_sixtyFour_div_fortyNine hq
  have hcorr' := mul_le_mul_of_nonneg_left hcorr hcoefficient
  have hcorr'' :
    (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
        llsPart1PrimitiveReciprocalQuotientCorrection χ ≤
      (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
        ((64 / 49 : ℝ) * Real.log (q / χ.conductor : ℕ)) := by
    calc
      _ ≤
          (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
            ((1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 * Real.log (q / χ.conductor : ℕ)) :=
        hcorr'
      _ ≤ _ := by gcongr
  apply llsTheorem11S1ComparisonUpperBoundWithQuotient_le_upper_of_correction χ hq
  calc
    _ ≤
        (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
          ((64 / 49 : ℝ) * Real.log (q / χ.conductor : ℕ)) :=
      hcorr''
    _ =
        (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
          (64 / 49 : ℝ) *
          Real.log (q / χ.conductor : ℕ) :=
      by ring
    _ ≤ _ := hslack

end PseudoPrime.LLS
