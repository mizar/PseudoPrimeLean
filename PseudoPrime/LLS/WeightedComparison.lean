/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.Lemma21
import PseudoPrime.LLS.Lemma23

/-!
# The common weighted-comparison core (CP06 of the foundation extraction plan)

This file assembles the four bounds `C1`-`C4` used by both the original-paper Part 2 branch and
the independent `QNeOne` branch into a single reusable core, parameterized by an arbitrary
nontrivial character `ψ` of level `f`, a cutoff `X`, a zero-mass witness `b`, and defect
parameters `dS`, `dR`, `eS`. Neither `ψ`'s level `f` nor `X` is tied to any specific `q`; the two
branches instantiate `X` differently (`(log q)²` for the paper branch, `(log d)²` for the
independent branch).

* `C1` (`weightedLogDefect`, `weightedReciprocalDefect`): the character-free minus character-sum
  defects. These are definitions, not hypotheses.
* `C2` (`ReS_ge_of_defect`, `ReR_ge_of_defect`): the defects transport the general Riemann lower
  bounds (`LLSRiemannWeightedLowerBound`, `LLSRiemannReciprocalLowerBound`) to lower bounds on
  `Re S`, `Re R`.
* `C3` (`primitiveReciprocalRaw_of_grh`, already proved in
  `PrimitiveReciprocalWeightedBounds.lean`): the reciprocal zero-mass upper bound for `b`, stated
  directly in terms of `Re R`.
* `C4` (`primitiveGenericLogWeightedUpper_of_grh_generic`, already proved in
  `PrimitiveLogWeightedBounds.lean`): the logarithmic upper bound for `Re S`, stated with the
  generic error `eS = -11/4` valid for any nontrivial primitive character at `X ≥ 64`. A quadratic
  branch supplying a sharper `eS` is a different input to the same bundle, not a different bundle.

The bundle `LLSWeightedComparisonCore` packages `C2`-`C4` for one `(ψ, X, b, dS, dR, eS)`; `C1`
is not a hypothesis because it is a definition. `weightedComparisonCore_generic_of_grh` in
`WeightedComparisonGRH.lean` supplies it under GRH from the two existing generic theorems,
without any quadraticity hypothesis.
-/

namespace PseudoPrime.LLS

/-- `C1`: the Riemann log-weighted sum minus the real part of the character log-weighted sum. -/
noncomputable def weightedLogDefect {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f) (X : ℝ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum X -
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X ψ).re

/-- `C1`: the Riemann reciprocal-weighted sum minus the real part of the character reciprocal
sum. -/
noncomputable def weightedReciprocalDefect {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f) (X : ℝ) :
    ℝ :=
  AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum X -
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum X ψ).re

/-- The Riemann lower bound `Lζ(X)` from `LLSRiemannWeightedLowerBound`. -/
noncomputable def riemannLogLowerAt (X : ℝ) : ℝ :=
  X - Real.log (2 * Real.pi) * Real.log X - 1 -
    2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt X + 1)

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- `C2`: a bounded log defect transports `LLSRiemannWeightedLowerBound` to a lower bound on
`Re S`. -/
theorem re_characterLogWeightedSum_ge_of_defect_le (h21 : LLSRiemannWeightedLowerBound) {f : ℕ}
    [NeZero f] (ψ : DirichletCharacter ℂ f) {X dS : ℝ} (hX : 1 < X)
    (hdS : weightedLogDefect ψ X ≤ dS) :
    riemannLogLowerAt X - dS ≤ (characterLogWeightedSum X ψ).re := by
  have hriemann := h21 X hX
  unfold weightedLogDefect at hdS
  unfold riemannLogLowerAt
  linarith

/-- `C2`: a bounded reciprocal defect transports `LLSRiemannReciprocalLowerBound` to a lower
bound on `Re R`. -/
theorem re_characterReciprocalWeightedSum_ge_of_defect_le (h24 : LLSRiemannReciprocalLowerBound)
    {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f) {X dR : ℝ} (hX : 2 ≤ X)
    (hdR : weightedReciprocalDefect ψ X ≤ dR) :
    Real.log X - 8 / 5 - dR ≤
      (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum X ψ).re := by
  have hriemann := h24 X hX
  unfold weightedReciprocalDefect at hdR
  linarith

/--
The common weighted-comparison core `C2`-`C4` for one nontrivial character `ψ` of level `f`, a
cutoff `X`, a zero-mass witness `b`, log/reciprocal defect bounds `dS`, `dR`, and a logarithmic
error term `eS`.

`C1` is not a field: `weightedLogDefect`/`weightedReciprocalDefect` are definitions, and
`logDefect_le`/`reciprocalDefect_le` already state the `C1`-defect bound `C2` consumes.
-/
structure LLSWeightedComparisonCore {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f)
    (X b dS dR eS : ℝ) : Prop where
  /-- `C1`+`C2`, log side: the log defect is at most `dS`. -/
  logDefect_le : weightedLogDefect ψ X ≤ dS
  /-- `C1`+`C2`, reciprocal side: the reciprocal defect is at most `dR`. -/
  reciprocalDefect_le : weightedReciprocalDefect ψ X ≤ dR
  /-- `C3`: the reciprocal zero-mass upper bound for `b`, stated directly in terms of `Re R`. -/
  zeroMass_le :
    (1 - 1 / Real.sqrt X) ^ 2 * b ≤
      (1 / 2) * (1 - 1 / X) * Real.log ((f : ℝ) / Real.pi) -
        (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum X ψ).re -
        1 / 4
  /-- `C4`: the logarithmic upper bound for `Re S`. -/
  logWeighted_le :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X ψ).re ≤
      (2 * Real.sqrt X + 2 + Real.log X) * b + (1 / 2) * Real.log ((f : ℝ) / Real.pi) * Real.log X +
        eS

/--
The common core, together with the general Riemann lower bounds, yields both headline
consequences used by the two branches: a lower bound for `Re S` (from `C1`+`C2`) and the
`C3`/`C4` bounds transported to the same `Re S`, `Re R` quantities. This is the "actually derive
the Riemann-side lower bound, the character-side zero mass, and the log-sum upper bound" step:
the three conclusions are stated together so a consumer cannot use the bundle as a mere triple of
disconnected hypotheses.
-/
theorem re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le
    (h21 : LLSRiemannWeightedLowerBound) (h24 : LLSRiemannReciprocalLowerBound) {f : ℕ} [NeZero f]
    {ψ : DirichletCharacter ℂ f} {X b dS dR eS : ℝ} (hX1 : 1 < X) (hX2 : 2 ≤ X)
    (hcore : LLSWeightedComparisonCore ψ X b dS dR eS) :
    riemannLogLowerAt X - dS ≤ (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X ψ).re ∧
      Real.log X - 8 / 5 - dR ≤
        (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum X ψ).re ∧
      (1 - 1 / Real.sqrt X) ^ 2 * b ≤
        (1 / 2) * (1 - 1 / X) * Real.log ((f : ℝ) / Real.pi) -
          (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum X ψ).re -
          1 / 4 ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X ψ).re ≤
        (2 * Real.sqrt X + 2 + Real.log X) * b +
          (1 / 2) * Real.log ((f : ℝ) / Real.pi) * Real.log X +
          eS :=
  ⟨re_characterLogWeightedSum_ge_of_defect_le h21 ψ hX1 hcore.logDefect_le,
    re_characterReciprocalWeightedSum_ge_of_defect_le h24 ψ hX2 hcore.reciprocalDefect_le,
    hcore.zeroMass_le, hcore.logWeighted_le⟩

/-!
### The zero-defect specialization

The two consumers of this core use different cutoffs `X`: the paper branch (`S2`) sets
`X = (log q)²` and supplies `dS = dR = 0` from strict-cutoff triviality; the independent
branch (`SQ`) sets `X = (log d)²` and supplies `dS`, `dR` from the `χ(2) ∈ {0, 1, -1}`
case split. `re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le` above already
takes `X` as a free parameter, so the `SQ` branch applies it directly at `X = (log d)²` with no
extra wrapper. The specialization below simplifies the zero defects. The actual primitive
core is constructed in `WeightedComparisonGRH` and consumed in `Theorem11S2`;
the three quadratic cores are constructed in `Extensions.QNeOneWeightedComparisonInputs`.
-/

/-- The paper branch's pair of zero-defect inequalities at `X = (log q)²`.
`llsWeightedComparisonS2Defects_of_trivialBelow` supplies this predicate from the
strict-cutoff character condition in `Theorem11S2SmallPrimeExclusion`. -/
def LLSWeightedComparisonS2Defects (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  weightedLogDefect χ ((Real.log q) ^ 2) ≤ 0 ∧ weightedReciprocalDefect χ ((Real.log q) ^ 2) ≤ 0

/-- The paper branch's consequences follow from the common core with `dS = dR = 0`
at `X = (log q)²`. The proof simplifies the two zero defects in the general conclusion. -/
theorem re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le_S2
    (h21 : LLSRiemannWeightedLowerBound) (h24 : LLSRiemannReciprocalLowerBound) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq1 : 1 < (Real.log q) ^ 2) (hq2 : 2 ≤ (Real.log q) ^ 2)
    {b eS : ℝ} (hcore : LLSWeightedComparisonCore χ ((Real.log q) ^ 2) b 0 0 eS) :
    riemannLogLowerAt ((Real.log q) ^ 2) ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((Real.log q) ^ 2) χ).re ∧
      Real.log ((Real.log q) ^ 2) - 8 / 5 ≤
        (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum ((Real.log q) ^ 2) χ).re ∧
      (1 - 1 / Real.sqrt ((Real.log q) ^ 2)) ^ 2 * b ≤
        (1 / 2) * (1 - 1 / (Real.log q) ^ 2) * Real.log ((q : ℝ) / Real.pi) -
          (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum ((Real.log q) ^ 2) χ).re -
          1 / 4 ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((Real.log q) ^ 2) χ).re ≤
        (2 * Real.sqrt ((Real.log q) ^ 2) + 2 + Real.log ((Real.log q) ^ 2)) * b +
          (1 / 2) * Real.log ((q : ℝ) / Real.pi) * Real.log ((Real.log q) ^ 2) +
          eS := by
  have h := re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le h21 h24 hq1 hq2 hcore
  simpa using h

end PseudoPrime.LLS
