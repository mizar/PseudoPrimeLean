/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Lemma21
public import PseudoPrime.LLS.Lemma23

/-!
# Comparing logarithmic and reciprocal weighted character sums

For a character ψ modulo a nonzero f and a cutoff X, the defects are the differences between
weighted Mangoldt sums without a character and the real parts of the corresponding character
sums. Bounds on these defects transfer the Riemann lower bounds to the character sums.

LLSWeightedComparisonCore records the two defect bounds, a reciprocal inequality involving
an auxiliary zero-mass parameter b, and a logarithmic upper bound with error eS. The comparison
theorem combines these four inputs with the Riemann lower bounds at the same cutoff.
Nontriviality, primitivity, RH, and identification of b with zero mass are not assumptions of
this algebraic interface; they are needed when supplying particular analytic inputs.

The cutoff remains free for both the Part 2 and QNeOne applications. The final specialization
uses X = (log q)² and zero defect bounds, as required by the Part 2 comparison.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- For a character ψ modulo nonzero f and a real cutoff X, the logarithmic defect is the
weighted Mangoldt sum without a character minus the real part of the character sum.
An upper bound on this real-valued difference transfers a Riemann lower bound to that sum. -/
noncomputable def weightedLogDefect {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f) (X : ℝ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum X -
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X ψ).re

/-- For a character ψ modulo nonzero f and a real cutoff X, the reciprocal defect is the
reciprocal weighted Mangoldt sum without a character minus the real part of the character sum.
An upper bound on this real-valued difference transfers a Riemann lower bound to that sum. -/
noncomputable def weightedReciprocalDefect {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f) (X : ℝ) :
    ℝ :=
  AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum X -
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum X ψ).re

/-- The expression X - log(2π) log X - 1 - 2β(√X + 1), where β is the Riemann zero mass.
It is defined for every real X; LLSRiemannWeightedLowerBound asserts that it bounds the
logarithmic weighted Mangoldt sum from below for X > 1. -/
noncomputable def riemannLogLowerAt (X : ℝ) : ℝ :=
  X - Real.log (2 * Real.pi) * Real.log X - 1 -
    2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt X + 1)

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- Given the Riemann logarithmic lower bound, X > 1, and logarithmic defect at most dS,
the real part of the character sum is at least riemannLogLowerAt X - dS.
The proof unfolds the defect and combines the two inequalities by linear arithmetic. -/
theorem re_characterLogWeightedSum_ge_of_defect_le (h21 : LLSRiemannWeightedLowerBound) {f : ℕ}
    [NeZero f] (ψ : DirichletCharacter ℂ f) {X dS : ℝ} (hX : 1 < X)
    (hdS : weightedLogDefect ψ X ≤ dS) :
    riemannLogLowerAt X - dS ≤ (characterLogWeightedSum X ψ).re := by
  have hriemann := h21 X hX
  unfold weightedLogDefect at hdS
  unfold riemannLogLowerAt
  linarith only [hdS, hriemann]

/-- Given the Riemann reciprocal lower bound, X ≥ 2, and reciprocal defect at most dR,
the real part of the character sum is at least log X - 8/5 - dR.
The proof unfolds the defect and combines the two inequalities by linear arithmetic. -/
theorem re_characterReciprocalWeightedSum_ge_of_defect_le (h24 : LLSRiemannReciprocalLowerBound)
    {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f) {X dR : ℝ} (hX : 2 ≤ X)
    (hdR : weightedReciprocalDefect ψ X ≤ dR) :
    Real.log X - 8 / 5 - dR ≤
      (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum X ψ).re := by
  have hriemann := h24 X hX
  unfold weightedReciprocalDefect at hdR
  linarith only [hdR, hriemann]

/-- Four comparison inequalities for a character ψ modulo nonzero f at a common cutoff X.
The parameters dS and dR bound the logarithmic and reciprocal defects, b is an auxiliary
zero-mass parameter, and eS is the logarithmic error term. The first two fields supply the
defect-transfer lemmas; the last two supply the analytic inequalities in the comparison.

The structure imposes no positivity or cutoff restrictions and does not identify b with zero
mass. Such conditions belong to the constructors or to the theorem using this interface. -/
structure LLSWeightedComparisonCore {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f)
    (X b dS dR eS : ℝ) : Prop where
  /-- Upper bound dS on the logarithmic defect at cutoff X. -/
  logDefect_le : weightedLogDefect ψ X ≤ dS
  /-- Upper bound dR on the reciprocal defect at cutoff X. -/
  reciprocalDefect_le : weightedReciprocalDefect ψ X ≤ dR
  /-- Bound on (1 - 1/√X)² b in terms of the reciprocal character sum and log(f/π). -/
  zeroMass_le :
    (1 - 1 / Real.sqrt X) ^ 2 * b ≤
      (1 / 2) * (1 - 1 / X) * Real.log ((f : ℝ) / Real.pi) -
        (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum X ψ).re -
        1 / 4
  /-- Upper bound on the logarithmic character sum in terms of b, f, X, and error eS. -/
  logWeighted_le :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X ψ).re ≤
      (2 * Real.sqrt X + 2 + Real.log X) * b + (1 / 2) * Real.log ((f : ℝ) / Real.pi) * Real.log X +
        eS

/--
For `X > 1` and `X ≥ 2`, the common core and the two Riemann lower-bound interfaces give lower
bounds for `Re S` and `Re R`, the zero-mass inequality, and the upper bound for `Re S`.
The proof applies the two defect-transfer lemmas and retains the core's analytic fields.
Both witness branches consume this four-part conclusion with the same cutoff and zero-mass
parameter, keeping the Riemann and character comparisons aligned.
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
## Comparison at the Part 2 cutoff

At X = (log q)², nonpositive defects suffice to use the Riemann lower bounds without a loss.
The specialization below takes both defect-bound parameters to be zero.
-/

/-- For a character χ modulo nonzero q, both defects at X = (log q)² are nonpositive.
This predicate supplies the defect fields of the Part 2 core with dS = dR = 0;
it requires upper bounds by zero rather than equality of the defects to zero. -/
def LLSWeightedComparisonS2Defects (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  weightedLogDefect χ ((Real.log q) ^ 2) ≤ 0 ∧ weightedReciprocalDefect χ ((Real.log q) ^ 2) ≤ 0

/-- Given the two Riemann lower bounds, 1 < (log q)², 2 ≤ (log q)², and a comparison core
with zero defect bounds, obtain the logarithmic and reciprocal lower bounds, the inequality
for b, and the logarithmic upper bound at the Part 2 cutoff. The proof specializes the general
comparison and simplifies subtraction of the zero defect-bound parameters. -/
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
  simpa only [Real.log_pow, Nat.cast_ofNat, tsub_le_iff_right, one_div, sub_zero] using h

end PseudoPrime.LLS
