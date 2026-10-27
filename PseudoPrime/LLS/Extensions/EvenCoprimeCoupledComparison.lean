/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.QNeOneReciprocalTransfer
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogTrivialSupport
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ReciprocalTrivialSupport
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogLevelChange
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ReciprocalLevelChange

/-! # Coupled signed support costs with retained real prime-power sums -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- The common-factor logarithmic cost minus the signed primitive level change.
The cutoff and level character are arbitrary; both terms are finite sums.
Under prime triviality this equals the primitive logarithmic defect, retaining
cancellation before any prime-support estimate is made. -/
noncomputable def coprimeLogSupportDefect {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x q -
    AnalyticNumberTheory.Arithmetic.primitiveLogLevelChangeCorrection x χ

/-- The common-factor reciprocal cost minus the signed primitive level change.
Both finite sums use the supplied cutoff and level character.
Under prime triviality this equals the primitive reciprocal defect and supplies
the reciprocal component of the coupled local cost. -/
noncomputable def coprimeReciprocalSupportDefect {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum x q -
    AnalyticNumberTheory.Arithmetic.primitiveReciprocalLevelChangeCorrection x χ

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- At positive cutoff and prime triviality outside the level, the primitive
logarithmic defect equals the exact signed support cost.
Combine the original-level support identity with the primitive level change.
This removes character sums from the local loss without bounding each part. -/
theorem weightedLogDefect_eq_coprimeSupport {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {x : ℝ} (hx : 0 < x)
    (ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    weightedLogDefect χ.primitiveCharacter x = coprimeLogSupportDefect χ x := by
  have hs := characterLogWeightedSum_re_eq_sub_common_of_prime_trivial x χ hx ht
  have hp := characterLogWeightedSum_re_primitive_eq_add_levelChangeCorrection x χ
  unfold weightedLogDefect coprimeLogSupportDefect
  linarith only [hs, hp]

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- At positive cutoff and prime triviality outside the level, the primitive
reciprocal defect equals the exact signed support cost.
Split the unsigned sum into coprime and common-factor support and retain the
primitive level change. This is the reciprocal half of the coupled ledger. -/
theorem weightedReciprocalDefect_eq_coprimeSupport {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {x : ℝ} (hx : 0 < x)
    (ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    weightedReciprocalDefect χ.primitiveCharacter x = coprimeReciprocalSupportDefect χ x := by
  have hs := characterReciprocalWeightedSum_re_eq_coprime_of_prime_trivial x χ hx ht
  have hc := reciprocalWeightedMangoldtSum_eq_coprime_add_common x q
  have hp := characterReciprocalWeightedSum_re_primitive_eq_add_levelChangeCorrection x χ
  unfold weightedReciprocalDefect coprimeReciprocalSupportDefect
  linarith only [hs, hc, hp]

/-- The multiplier (2y+2+2log y)/(1-1/y)^2 in the even comparison.
It is defined for every real y and is positive in the analytic range y at least
eight. It weights the reciprocal part of the coupled support cost. -/
noncomputable def evenCoprimeReciprocalMultiplier (y : ℝ) : ℝ :=
  (2 * y + 2 + 2 * Real.log y) / (1 - 1 / y) ^ 2

/-- The exact logarithmic support defect plus its reciprocal counterpart
weighted by the even comparison multiplier, both at cutoff y squared.
It retains the original level, conductor quotient and signed primitive values.
Later scalar majorants can bound this combined finite quantity directly. -/
noncomputable def evenCoprimeLocalCost {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) : ℝ :=
  coprimeLogSupportDefect χ (y ^ 2) +
    evenCoprimeReciprocalMultiplier y * coprimeReciprocalSupportDefect χ (y ^ 2)

/-- The even upper envelope with no local support cost and with the actual
nonnegative Riemann reciprocal prime-power sum retained.
The real conductor allowance f and reciprocal main error e remain parameters.
This avoids replacing that sum by a scale-independent logarithmic loss. -/
noncomputable def evenCoprimeBaseUpper (y f e : ℝ) : ℝ :=
  qNeOneReciprocalUpper y f
    (2 * Real.log y - AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (y ^ 2) + e +
      4 / 5)
    0

/-- The even upper comparison at the actual conductor, plus the exact
coupled local cost of the level character. Inputs are a real root and a
reciprocal main-error bound. A strict comparison with the unsigned logarithmic
sum is a sufficient condition for a coprime non-one prime witness. -/
noncomputable def evenCoprimeUpper {q : ℕ} (χ : DirichletCharacter ℂ q) (y e : ℝ) : ℝ :=
  evenCoprimeBaseUpper y (Real.log χ.conductor - Real.log Real.pi) e + evenCoprimeLocalCost χ y

/-- At arbitrary real parameters, adding a reciprocal defect increases the
envelope by exactly the multiplier times that defect.
Expand the definitions and normalize the rational expression.
This preserves the coupled logarithmic and reciprocal cost in one ledger. -/
theorem qNeOneReciprocalUpper_add_defect (y f r d : ℝ) :
    qNeOneReciprocalUpper y f r d =
      qNeOneReciprocalUpper y f r 0 + evenCoprimeReciprocalMultiplier y * d := by
  unfold qNeOneReciprocalUpper evenCoprimeReciprocalMultiplier
  ring

/-- Under GRH, even primitive parity, root at least eight, a certified
reciprocal main error and prime triviality outside the original level, the
unsigned logarithmic sum is at most the exact coprime upper envelope.
Eliminate zero mass using the retained reciprocal sum and combine both signed
support identities. No root-versus-log-level condition or omega bound is used. -/
theorem logWeightedMangoldtSum_le_evenCoprimeUpper_of_prime_trivial {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y e : ℝ} (hy : 8 ≤ y)
    (hE : Analysis.primitiveReciprocalEvenMainError (y ^ 2) ≤ e)
    (ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ y ^ 2 → χ p = 1) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2) ≤ evenCoprimeUpper χ y e := by
  have hx := Analysis.sq_ge_64_of_ge_8 hy
  have hx0 : (0 : ℝ) < y ^ 2 := by linarith only [hx]
  have hp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hf : 2 ≤ χ.conductor := by
    have h0 := NeZero.pos χ.conductor
    have h1 := AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one hp
    exact Nat.succ_le_iff.mpr (Nat.lt_of_le_of_ne h0 (Ne.symm h1))
  have hR :
    Real.log (y ^ 2) -
        (2 * Real.log y - AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (y ^ 2)) ≤
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (y ^ 2) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only
  have hd := weightedReciprocalDefect_eq_coprimeSupport χ hx0 ht
  have hs := weightedLogDefect_eq_coprimeSupport χ hx0 ht
  have hu :=
    evenLogWeighted_le_reciprocalUpper_of_mainError hf χ.primitiveCharacter
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hp heven hGRH hy hE
      (le_refl (Real.log χ.conductor - Real.log Real.pi)) hR hd.le
  rw [qNeOneReciprocalUpper_add_defect] at hu
  unfold weightedLogDefect at hs
  unfold evenCoprimeUpper evenCoprimeBaseUpper evenCoprimeLocalCost
  linarith only [hu, hs]

/-- Under GRH, even primitive parity, root at least eight and a certified
reciprocal main error, a strict exact-envelope gap yields a coprime non-one
prime through the squared root. Negate witness existence and apply the
no-witness inequality. All remaining quantitative input is an explicit real
inequality between finite sums and elementary conductor terms. -/
theorem exists_prime_coprime_ne_one_of_evenCoprimeGap {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y e : ℝ} (hy : 8 ≤ y)
    (hE : Analysis.primitiveReciprocalEvenMainError (y ^ 2) ≤ e)
    (hgap :
      evenCoprimeUpper χ y e < AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2)) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ y ^ 2 := by
  by_contra h
  have ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ y ^ 2 → χ p = 1 := by
    intro p hp hd hb
    by_contra hv
    exact h ⟨p, hp, hd, hv, hb⟩
  exact
    (not_lt_of_ge
        (logWeightedMangoldtSum_le_evenCoprimeUpper_of_prime_trivial χ hne heven hGRH hy hE ht))
      hgap

/-- For arbitrary level character and root, the coupled local cost is the
difference of two finite sums with the same combined logarithmic/reciprocal
weight. Expand the definitions and distribute finite sums. This is the
input for direct prime-power majorants that keep the signed cancellation. -/
theorem evenCoprimeLocalCost_eq_coupled_sums {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) :
    evenCoprimeLocalCost χ y =
      (∑ n ∈ (Finset.Ioc 0 ⌊y ^ 2⌋₊).filter (fun n ↦ ¬Nat.Coprime n q),
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm (y ^ 2) n +
            evenCoprimeReciprocalMultiplier y *
              AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm (y ^ 2) n)) -
        (∑ n ∈ (Finset.Ioc 0 ⌊y ^ 2⌋₊).filter (fun n ↦ ¬Nat.Coprime n (q / χ.conductor)),
          ((AnalyticNumberTheory.Arithmetic.characterLogWeightedTerm (y ^ 2) χ.primitiveCharacter
                n).re +
            evenCoprimeReciprocalMultiplier y *
              (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm (y ^ 2)
                  χ.primitiveCharacter n).re)) := by
  simp only [evenCoprimeLocalCost, coprimeLogSupportDefect, coprimeReciprocalSupportDefect,
    AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum,
    AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum,
    AnalyticNumberTheory.Arithmetic.primitiveLogLevelChangeCorrection,
    AnalyticNumberTheory.Arithmetic.primitiveReciprocalLevelChangeCorrection, mul_sub,
    Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- Under GRH and even primitive parity, a root at least eight and a gap at
main error -179/200 suffice for a coprime non-one prime. Instantiate the generic
error input with its certified even bound. This is the finite-scale public
entry point used for negative quadratic witnesses. -/
theorem exists_prime_coprime_ne_one_of_retainedEvenCoprimeGap {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hgap :
      evenCoprimeUpper χ y (-(179 / 200)) <
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2)) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ y ^ 2 := by
  exact
    exists_prime_coprime_ne_one_of_evenCoprimeGap χ hne heven hGRH hy
      (Analysis.primitiveReciprocalEvenMainError_le_neg_179_div_200 (Analysis.sq_ge_64_of_ge_8 hy))
      hgap

/-- For roots at least eight, the reciprocal cost multiplier is positive.
The numerator and the squared denominator are positive in that range.
This permits one-sided scalar majorants of the combined local cost. -/
theorem evenCoprimeReciprocalMultiplier_pos {y : ℝ} (hy : 8 ≤ y) :
    0 < evenCoprimeReciprocalMultiplier y := by
  have hy0 : 0 < y := by linarith only [hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have hd : 0 < (1 - 1 / y) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr ((div_lt_one hy0).mpr (by linarith only [hy])))
  exact div_pos (by linarith only [hy, hz]) hd

/-- At roots at least eight, upper bounds s and r for the exact signed
logarithmic and reciprocal support costs give the coupled bound s+K r.
Use positivity of the shared multiplier. This is a sufficient scalar-budget
interface; direct bounds on the coupled finite sum may be sharper. -/
theorem evenCoprimeLocalCost_le_of_support_bounds {q : ℕ} (χ : DirichletCharacter ℂ q) {y s r : ℝ}
    (hy : 8 ≤ y) (hS : coprimeLogSupportDefect χ (y ^ 2) ≤ s)
    (hR : coprimeReciprocalSupportDefect χ (y ^ 2) ≤ r) :
    evenCoprimeLocalCost χ y ≤ s + evenCoprimeReciprocalMultiplier y * r := by
  exact add_le_add hS (mul_le_mul_of_nonneg_left hR (evenCoprimeReciprocalMultiplier_pos hy).le)

/-- Under GRH, even primitive parity and a root at least eight, a bound c
for the coupled local cost and a separated base-plus-c gap yield a coprime
non-one prime. Insert the scalar budget into the exact-envelope criterion.
The finite reciprocal Riemann sum is still retained in the base expression. -/
theorem exists_prime_coprime_ne_one_of_evenCoprimeBudget {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y e c : ℝ} (hy : 8 ≤ y)
    (hE : Analysis.primitiveReciprocalEvenMainError (y ^ 2) ≤ e) (hc : evenCoprimeLocalCost χ y ≤ c)
    (hgap :
      evenCoprimeBaseUpper y (Real.log χ.conductor - Real.log Real.pi) e + c <
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2)) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ y ^ 2 := by
  apply exists_prime_coprime_ne_one_of_evenCoprimeGap χ hne heven hGRH hy hE
  unfold evenCoprimeUpper
  linarith only [hc, hgap]

end PseudoPrime.LLS.Extensions
