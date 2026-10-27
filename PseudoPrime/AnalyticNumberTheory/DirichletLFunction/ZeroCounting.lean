/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Meromorphic.RCLike
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import PseudoPrime.AnalyticNumberTheory.Rectangle.Basic
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic

/-!
# Zero counting for Dirichlet `L`-functions

Fully generic facts about the (uncompleted and completed) Dirichlet `L`-function of an arbitrary
nontrivial character: finite meromorphic order everywhere, finiteness of the zero set on any
compact set (in particular any closed rectangle), the resulting finite zero ledgers, and the
positive analytic multiplicity of a completed zero together with its local factorization. None of
this mentions any application-specific contour kernel.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: two complex corners.
Conclusion: the closed axis-aligned rectangle determined by those corners.
Content: this is the shared rectangular box geometry specialized to primitive Dirichlet `L` data.
Role: it indexes finite primitive-zero ledgers used by the later contour-residue identity.
-/
def dirichletCompletedLFunctionRectangleBox (z w : ℂ) : Set ℂ :=
  Rectangle.rectangleClosedBox z w

/--
Input/assumptions: two complex corners.
Conclusion: the primitive contour rectangle is compact.
Content: it is a product of two closed bounded real intervals.
Role: compactness gives finiteness of the primitive `L` zero ledger.
-/
theorem isCompact_dirichletCompletedLFunctionRectangleBox (z w : ℂ) :
    IsCompact (dirichletCompletedLFunctionRectangleBox z w) := by
  exact isCompact_uIcc.reProdIm isCompact_uIcc

/--
Input/assumptions: a nontrivial complex Dirichlet character.
Conclusion: its continued `L`-function has finite meromorphic order at every complex point.
Content: an entire nonzero function has one finite-order nonzero value, and the meromorphic
identity principle propagates finite order globally.
Role: this is the finiteness certificate required by the finite zero-set divisor API.
-/
theorem meromorphicOrderAt_dirichletLFunction_ne_top {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) : meromorphicOrderAt (DirichletCharacter.LFunction χ) s ≠ ⊤ := by
  have hanalytic : AnalyticAt ℂ (DirichletCharacter.LFunction χ) 2 :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt 2
  have htwo : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by
        change (1 : ℝ) ≤ 2
        norm_num only)
  have horder : meromorphicOrderAt (DirichletCharacter.LFunction χ) 2 = 0 :=
    hanalytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr htwo
  have hmero : Meromorphic (DirichletCharacter.LFunction χ) := fun u ↦
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt u |>.meromorphicAt
  apply (hmero.exists_meromorphicOrderAt_ne_top_iff_forall.mp ?_) s
  exact
    ⟨2, by
      rw [horder]
      simp only [ne_eq, LinearOrderedAddCommGroupWithTop.zero_ne_top, not_false_eq_true]⟩

/--
Input/assumptions: a compact complex set and a nontrivial character.
Conclusion: the set of zeros of its continued `L`-function in that compact set is finite.
Content: the entire continuation is in meromorphic normal form and has finite order everywhere.
Role: it supplies the finite zero ledger needed before a primitive rectangle contour is assembled.
-/
theorem finite_dirichletLFunction_zerosOn {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {K : Set ℂ} (hcompact : IsCompact K) :
    (K ∩ DirichletCharacter.LFunction χ ⁻¹' {0}).Finite := by
  have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) K := fun s _ ↦
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have hnormal : MeromorphicNFOn (DirichletCharacter.LFunction χ) K := hanalytic.meromorphicNFOn
  rw [hnormal.zero_set_eq_divisor_support fun u ↦
      meromorphicOrderAt_dirichletLFunction_ne_top χ hχ u]
  exact (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) K).finiteSupport hcompact

/--
Input/assumptions: a nontrivial character and two complex corners.
Conclusion: its continued `L`-zeros in the closed rectangle form a finite set.
Content: specialize compact zero finiteness to the rectangle.
Role: provides the finiteness proof used to define the rectangle's `Finset` ledger.
-/
theorem finite_dirichletLFunction_zerosInRectangle {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (z w : ℂ) :
    (dirichletCompletedLFunctionRectangleBox z w ∩ DirichletCharacter.LFunction χ ⁻¹' {0}).Finite :=
  finite_dirichletLFunction_zerosOn χ hχ (isCompact_dirichletCompletedLFunctionRectangleBox z w)

/--
Input/assumptions: a nontrivial character and closed rectangle.
Conclusion: a finite ledger of exactly the continued `L`-zeros inside that rectangle.
Content: convert the certified finite set of zeros to a `Finset`.
Role: its finite sums will be the primitive zero contributions in the rectangle residue formula.
-/
noncomputable def dirichletLFunctionZerosInRectangle {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (z w : ℂ) : Finset ℂ :=
  (finite_dirichletLFunction_zerosInRectangle χ hχ z w).toFinset

/--
Input/assumptions: a point and a primitive rectangle zero ledger.
Conclusion: membership is equivalent to lying in the rectangle and being an `L`-zero.
Content: unfold the finite-set-to-finset conversion.
Role: lets residue and boundary arguments recover the analytic facts attached to a ledger entry.
-/
theorem mem_dirichletLFunctionZerosInRectangle_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {hχ : χ ≠ 1} {z w ρ : ℂ} :
    ρ ∈ dirichletLFunctionZerosInRectangle χ hχ z w ↔
      ρ ∈ dirichletCompletedLFunctionRectangleBox z w ∧ DirichletCharacter.LFunction χ ρ = 0 := by
  simp only [dirichletLFunctionZerosInRectangle, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

/--
Input/assumptions: a nontrivial Dirichlet character.
Conclusion: its completed `L`-function is nonzero at the Euler-half-plane point two.
Content: if the completed value were zero, the completed-to-uncompleted identity would force
`L(χ,2)=0`, contradicting standard Dirichlet `L` nonvanishing.
Role: supplies the global nonzero witness needed to make completed-`L` zero ledgers finite.
-/
theorem dirichletCompletedLFunction_two_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : DirichletCharacter.completedLFunction χ (2 : ℂ) ≠ 0 := by
  intro hcompleted
  have hL : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by
        change (1 : ℝ) ≤ 2
        norm_num only)
  have hrelation :=
    dirichletLFunction_eq_completed_div_gammaFactor χ (2 : ℂ)
      (Or.inl
        (by
          intro h
          have h' := congrArg Complex.re h
          change (2 : ℝ) = 0 at h'
          norm_num only at h'))
  apply hL
  rw [hrelation, hcompleted]
  simp only [zero_div]

/--
Input/assumptions: a nontrivial Dirichlet character.
Conclusion: its completed `L`-function has finite meromorphic order at every complex point.
Content: entire continuation and the nonzero value at two invoke the connected meromorphic-order
identity principle.
Role: this is the order certificate used by the completed function's compact zero-set ledger.
-/
theorem meromorphicOrderAt_dirichletCompletedLFunction_ne_top {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    meromorphicOrderAt (DirichletCharacter.completedLFunction χ) s ≠ ⊤ := by
  have hanalytic : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) 2 :=
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt 2
  have horder : meromorphicOrderAt (DirichletCharacter.completedLFunction χ) 2 = 0 :=
    hanalytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (dirichletCompletedLFunction_two_ne_zero χ hχ)
  have hmero : Meromorphic (DirichletCharacter.completedLFunction χ) := fun u ↦
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt u |>.meromorphicAt
  apply (hmero.exists_meromorphicOrderAt_ne_top_iff_forall.mp ?_) s
  exact
    ⟨2, by
      rw [horder]
      simp only [ne_eq, LinearOrderedAddCommGroupWithTop.zero_ne_top, not_false_eq_true]⟩

/--
Input/assumptions: a compact complex set and a nontrivial character.
Conclusion: the completed `L`-zeros in that compact set are finite.
Content: entire completed continuation is in meromorphic normal form and has finite order globally.
Role: establishes the finite zero-set side of the completed-function contour ledger using the
nonzero value at two.
-/
theorem finite_dirichletCompletedLFunction_zerosOn {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {K : Set ℂ} (hcompact : IsCompact K) :
    (K ∩ DirichletCharacter.completedLFunction χ ⁻¹' {0}).Finite := by
  have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) K := fun s _ ↦
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt s
  have hnormal : MeromorphicNFOn (DirichletCharacter.completedLFunction χ) K :=
    hanalytic.meromorphicNFOn
  rw [hnormal.zero_set_eq_divisor_support fun u ↦
      meromorphicOrderAt_dirichletCompletedLFunction_ne_top χ hχ u]
  exact (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) K).finiteSupport hcompact

/--
Purpose: list the zeros of a nontrivial completed Dirichlet L-function in a closed rectangle.

Definition: convert the finite zero set in the rectangle to a finite ledger.

Inputs: a nontrivial character and two complex corners.

Output: each distinct zero in the rectangle occurs once; its analytic multiplicity is supplied
separately by `completedZeroMultiplicityCountInRectangle`.

Role: provides a finite domain for multiplicity-weighted zero counts without conflating distinct
zeros with zeros counted according to order.
-/
noncomputable def completedZerosInRectangle {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (z w : ℂ) : Finset ℂ :=
  (finite_dirichletCompletedLFunction_zerosOn χ hχ
      (isCompact_dirichletCompletedLFunctionRectangleBox z w)).toFinset

/--
Inputs: a nontrivial character, rectangle corners, and a complex point.

Claim: ledger membership is equivalent to being a zero of the completed L-function in the box.

Proof: unfold the finite-set conversion and the preimage of `{0}`.

Role: recovers the analytic zero property for each entry in a finite zero ledger.
-/
theorem mem_completedZerosInRectangle_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {hχ : χ ≠ 1} {z w ρ : ℂ} :
    ρ ∈ completedZerosInRectangle χ hχ z w ↔
      ρ ∈ dirichletCompletedLFunctionRectangleBox z w ∧
        DirichletCharacter.completedLFunction χ ρ = 0 := by
  simp only [completedZerosInRectangle, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

/--
Inputs: a nontrivial character and a zero of its completed L-function.

Claim: the analytic multiplicity of that zero is positive.

Proof: analyticity identifies meromorphic and analytic orders; finite meromorphic order excludes
infinite analytic order, while the zero forces the analytic order to be nonzero.

Role: ensures every selected zero contributes at least one to multiplicity-weighted family sums.
-/
theorem analyticOrderNatAt_pos_of_completedLFunction_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {ρ : ℂ}
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0) :
    0 < analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ := by
  have hf : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) ρ :=
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt ρ
  have hmero := meromorphicOrderAt_dirichletCompletedLFunction_ne_top χ hχ ρ
  have horderFinite : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≠ ⊤ := by
    intro htop
    have htop' : meromorphicOrderAt (DirichletCharacter.completedLFunction χ) ρ = ⊤ := by
      rw [hf.meromorphicOrderAt_eq, htop, ENat.map_top]
    exact hmero htop'
  have horderNe : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 :=
    hf.analyticOrderAt_ne_zero.mpr hzero
  have hcast := Nat.cast_analyticOrderNatAt horderFinite
  have hnatNe : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 := by
    intro hz
    apply horderNe
    rw [← hcast, hz]
    norm_num only
  exact Nat.pos_of_ne_zero hnatNe

/--
Purpose: count completed L-function zeros in a rectangle with analytic multiplicity.

Definition: sum `analyticOrderNatAt` over the finite ledger of distinct zeros in the rectangle.

Inputs: a nontrivial character and two complex corners.

Output: a real-valued count in which a zero of order `m` contributes `m`.

Role: supplies the multiplicity convention needed for zero-density estimates; the finite ledger
alone counts distinct complex zeros and is not itself the analytic zero count.
-/
noncomputable def completedZeroMultiplicityCountInRectangle {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w : ℂ) : ℝ :=
  ∑ ρ ∈ completedZerosInRectangle χ hχ z w,
    (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)

/--
Purpose: enumerate completed zeros in a rectangle with one finite index for each unit of analytic
multiplicity.

Definition: pair each distinct zero in `completedZerosInRectangle` with an index below its analytic
order.

Inputs: a nontrivial character and two complex corners.

Output: a finite type whose cardinality counts zeros with analytic multiplicity, retaining distinct
indices for repeated occurrences of the same zero.

Role: provides a finite domain for arguments that must preserve the multiplicity convention.
-/
noncomputable def completedZeroMultiplicityOccurrences {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w : ℂ) :
    Finset (Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)) :=
  (completedZerosInRectangle χ hχ z w).sigma fun _ρ ↦ Finset.univ

/--
Inputs: a nontrivial character and a closed rectangle.

Claim: the multiplicity-weighted zero count equals the cardinality of the occurrence ledger.

Proof: apply the cardinality formula for a dependent finite sum and use that `Fin m` has `m`
elements.

Role: converts analytic multiplicity into an explicit finite counting domain without identifying
the ledger with the set of distinct zero values.
-/
theorem completedZeroMultiplicityCountInRectangle_eq_occurrence_card {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w : ℂ) :
    completedZeroMultiplicityCountInRectangle χ hχ z w =
      (completedZeroMultiplicityOccurrences χ hχ z w).card := by
  rw [completedZeroMultiplicityCountInRectangle, completedZeroMultiplicityOccurrences,
    Finset.card_sigma]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_sum]

/--
Inputs: a nontrivial character and two complex rectangle corners.

Claim: the sum of analytic zero orders over the completed zero set is nonnegative.

Proof: every order is a natural number, so each real summand is nonnegative; apply finite-sum
nonnegativity.

Role: supplies the positivity property used by later zero-counting estimates.
-/
theorem completedZeroMultiplicityCountInRectangle_nonneg {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w : ℂ) :
    0 ≤ completedZeroMultiplicityCountInRectangle χ hχ z w := by
  unfold completedZeroMultiplicityCountInRectangle
  apply Finset.sum_nonneg
  intro ρ hρ
  exact Nat.cast_nonneg _

/--
Purpose: count completed zeros after removing one selected point from the finite zero ledger.

Definition: sum analytic multiplicities over the ledger with `ρ` erased.

Inputs: a nontrivial character, rectangle corners, and the selected complex point `ρ`.

Output: the multiplicity count excluding `ρ`, if it occurs in the rectangle ledger.

Role: isolates a possible exceptional zero before applying ordinary family density bounds.
-/
noncomputable def completedZeroMultiplicityCountInRectangleExcept {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w ρ : ℂ) : ℝ :=
  ∑ ξ ∈ (completedZerosInRectangle χ hχ z w).erase ρ,
    (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ξ : ℝ)

/--
Inputs: a nontrivial character, a rectangle, and a selected point.

Claim: the full multiplicity count is the count with that point erased plus its multiplicity
when it belongs to the ledger.

Proof: split the finite sum using `Finset.add_sum_erase`; if the point is absent, erasing it
leaves the sum unchanged.

Role: gives exact bookkeeping for separating a selected exceptional zero from ordinary zeros.
-/
theorem completedZeroMultiplicityCountInRectangle_eq_except_add_if_mem {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w ρ : ℂ) :
    completedZeroMultiplicityCountInRectangle χ hχ z w =
      completedZeroMultiplicityCountInRectangleExcept χ hχ z w ρ +
        if ρ ∈ completedZerosInRectangle χ hχ z w then
          (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
        else 0 := by
  classical
  unfold completedZeroMultiplicityCountInRectangle completedZeroMultiplicityCountInRectangleExcept
  by_cases hρ : ρ ∈ completedZerosInRectangle χ hχ z w
  · rw [ite_eq_left hρ]
    calc
      (∑ ξ ∈ completedZerosInRectangle χ hχ z w,
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ξ : ℝ)) =
          (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ) +
            ∑ ξ ∈ (completedZerosInRectangle χ hχ z w).erase ρ,
              (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ξ : ℝ) :=
        (Finset.add_sum_erase _ _ hρ).symm
      _ = _ := add_comm _ _
  · rw [ite_eq_right hρ, Finset.erase_eq_of_notMem hρ]
    simp only [add_zero]

/--
Purpose: define the completed Dirichlet L zero-counting function with multiplicity.

Definition: specialize the rectangular count to real parts between `σ` and `1`, and heights
between `-T` and `T`.

Inputs: a nontrivial character, a real-part threshold `σ`, and a height `T`.

Output: a real number that sums the analytic orders of the completed L zeros in the rectangle.
When `σ ≤ 1` and `0 ≤ T`, this is the standard inclusive region `σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T`.

Role: provides the per-character counting function used in the family density estimate.
-/
noncomputable def completedZeroCount {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (σ T : ℝ) : ℝ :=
  completedZeroMultiplicityCountInRectangle χ hχ ((σ : ℂ) - T * Complex.I) ((1 : ℂ) + T * Complex.I)

/--
Inputs: a nontrivial character, a threshold `σ ≤ 1`, a height `T ≥ 0`, and a complex point.

Claim: membership in the finite zero set for `completedZeroCount` means the point is a completed
L zero with `σ ≤ Re ρ ≤ 1` and `|Im ρ| ≤ T`.

Proof: unfold the rectangle membership, use the ordered real intervals, and simplify the corners.

Role: connects the compact zero ledger to the standard zero-counting region.
-/
theorem mem_completedZeroCountRegion_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {hχ : χ ≠ 1} {σ T : ℝ} {ρ : ℂ} (hσ : σ ≤ 1) (hT : 0 ≤ T) :
    ρ ∈ completedZerosInRectangle χ hχ ((σ : ℂ) - T * Complex.I) ((1 : ℂ) + T * Complex.I) ↔
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧ -T ≤ ρ.im ∧ ρ.im ≤ T ∧ DirichletCharacter.completedLFunction χ ρ = 0 := by
  simp only [mem_completedZerosInRectangle_iff, dirichletCompletedLFunctionRectangleBox,
    Rectangle.rectangleClosedBox, Complex.mem_reProdIm, Complex.sub_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, mul_zero, sub_zero, Complex.add_re, Complex.one_re, add_zero,
    Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.add_im, Complex.one_im,
    zero_add, mul_one, zero_sub, Set.uIcc_of_le hσ, Set.uIcc_of_le (neg_le_self hT), Set.mem_Icc,
    and_assoc]

/--
Inputs: a nontrivial character and real parameters `σ` and `T`.

Claim: the completed Dirichlet L zero count is nonnegative.

Proof: this is the nonnegativity theorem for the multiplicity-weighted rectangular sum.

Role: supplies positivity for sums over primitive characters in the density argument.
-/
theorem completedZeroCount_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (σ T : ℝ) : 0 ≤ completedZeroCount χ hχ σ T := by
  exact
    completedZeroMultiplicityCountInRectangle_nonneg χ hχ ((σ : ℂ) - T * Complex.I)
      ((1 : ℂ) + T * Complex.I)

/--
Inputs: a nontrivial character, a real-part threshold at most one, a nonnegative height, and a
positive completed zero count.

Claim: the counted rectangle contains an actual completed L-function zero satisfying the region
bounds.

Proof: positive multiplicity sum forces a nonzero summand in the finite zero ledger; decode its
rectangle membership with `mem_completedZeroCountRegion_iff`.

Role: supplies an actual zero point to local analytic zero-detection arguments.
-/
theorem exists_mem_completedZeroCountRegion_of_pos {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {σ T : ℝ} (hσ : σ ≤ 1) (hT : 0 ≤ T) (hcount : 0 < completedZeroCount χ hχ σ T) :
    ∃ ρ : ℂ,
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧ -T ≤ ρ.im ∧ ρ.im ≤ T ∧ DirichletCharacter.completedLFunction χ ρ = 0 := by
  classical
  let S := completedZerosInRectangle χ hχ ((σ : ℂ) - T * Complex.I) ((1 : ℂ) + T * Complex.I)
  let f := fun ρ : ℂ => (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
  have hsumPos : 0 < ∑ ρ ∈ S, f ρ := by
    simpa only [completedZeroCount, completedZeroMultiplicityCountInRectangle, S, f] using hcount
  have hexists : ∃ ρ ∈ S, f ρ ≠ 0 := by
    by_contra hnot
    have hzero : ∀ ρ ∈ S, f ρ = 0 := by
      intro ρ hρ
      by_contra hne
      exact hnot ⟨ρ, hρ, hne⟩
    have hsum0 : (∑ ρ ∈ S, f ρ) = 0 := by
      apply Finset.sum_eq_zero
      intro ρ hρ
      exact hzero ρ hρ
    linarith only [hsumPos, hsum0]
  obtain ⟨ρ, hρ, hterm⟩ := hexists
  have hmem := (mem_completedZeroCountRegion_iff hσ hT).mp hρ
  exact ⟨ρ, hmem⟩

/--
Inputs: a nontrivial character, thresholds `σ₁ ≤ σ₂ ≤ 1`, and a nonnegative height.

Claim: raising the real-part threshold cannot increase the multiplicity-weighted zero count.

Proof: the zero ledger for `σ₂` is contained in the ledger for `σ₁`; each analytic order is
nonnegative, so the finite sum over the smaller ledger is bounded by the larger one.

Role: permits the real-part interval to be divided into ranges in zero-density estimates.
-/
theorem completedZeroCount_antitone_sigma {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {σ₁ σ₂ T : ℝ} (hσ : σ₁ ≤ σ₂) (h₂ : σ₂ ≤ 1) (hT : 0 ≤ T) :
    completedZeroCount χ hχ σ₂ T ≤ completedZeroCount χ hχ σ₁ T := by
  unfold completedZeroCount completedZeroMultiplicityCountInRectangle
  let S₂ := completedZerosInRectangle χ hχ ((σ₂ : ℂ) - T * Complex.I) ((1 : ℂ) + T * Complex.I)
  let S₁ := completedZerosInRectangle χ hχ ((σ₁ : ℂ) - T * Complex.I) ((1 : ℂ) + T * Complex.I)
  have hsub : S₂ ⊆ S₁ := by
    intro ρ hρ
    have hm := (mem_completedZeroCountRegion_iff h₂ hT).mp hρ
    apply (mem_completedZeroCountRegion_iff (le_trans hσ h₂) hT).mpr
    exact ⟨le_trans hσ hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩
  change
    (∑ ρ ∈ S₂, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)) ≤
      ∑ ρ ∈ S₁, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
  exact
    Finset.sum_le_sum_of_subset_of_nonneg (f := fun ρ : ℂ =>
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)) hsub
      (by
        intro ρ hρ hρ'; exact Nat.cast_nonneg _)

/--
Inputs: a nontrivial character, a real-part threshold at most one, and two nonnegative heights
in increasing order.

Claim: increasing the height bound cannot decrease the completed zero count.

Proof: the smaller rectangle's zero ledger is contained in the larger one; analytic multiplicities
are nonnegative.

Role: supplies monotonicity for height truncation in the finite-character density sums.
-/
theorem completedZeroCount_mono_height {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {σ T₁ T₂ : ℝ} (hσ : σ ≤ 1) (hT₁ : 0 ≤ T₁) (hT : T₁ ≤ T₂) :
    completedZeroCount χ hχ σ T₁ ≤ completedZeroCount χ hχ σ T₂ := by
  unfold completedZeroCount completedZeroMultiplicityCountInRectangle
  let S₁ := completedZerosInRectangle χ hχ ((σ : ℂ) - T₁ * Complex.I) ((1 : ℂ) + T₁ * Complex.I)
  let S₂ := completedZerosInRectangle χ hχ ((σ : ℂ) - T₂ * Complex.I) ((1 : ℂ) + T₂ * Complex.I)
  have hT₂ : 0 ≤ T₂ := le_trans hT₁ hT
  have hsub : S₁ ⊆ S₂ := by
    intro ρ hρ
    have hm := (mem_completedZeroCountRegion_iff hσ hT₁).mp hρ
    apply (mem_completedZeroCountRegion_iff hσ hT₂).mpr
    exact ⟨hm.1, hm.2.1, le_trans (neg_le_neg hT) hm.2.2.1, le_trans hm.2.2.2.1 hT, hm.2.2.2.2⟩
  change
    (∑ ρ ∈ S₁, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)) ≤
      ∑ ρ ∈ S₂, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
  exact
    Finset.sum_le_sum_of_subset_of_nonneg (f := fun ρ : ℂ =>
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)) hsub
      (by
        intro ρ hρ hρ'; exact Nat.cast_nonneg _)

end DirichletLFunction

end AnalyticNumberTheory

end PseudoPrime
