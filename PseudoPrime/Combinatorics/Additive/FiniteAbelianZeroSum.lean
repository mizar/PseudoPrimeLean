/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import PseudoPrime.Data.Finset.FiniteCounting
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import PseudoPrime.Combinatorics.Additive.FiniteAbelianFourier

/-! # Finite abelian zero-sum bounds from character coefficients

This file derives logarithmic and label-preserving zero-sum bounds from finite
Fourier coefficient identities.
-/

@[expose] public section

namespace PseudoPrime.Combinatorics.Additive.FiniteAbelianZeroSum

/--
Inputs: finite sets whose cardinalities are ordered.

Claim: there is an injection from the subtype of the smaller set into the
subtype of the larger set.

Content: the finite sets are represented by equivalent `Fin` types, and the
cardinality inequality gives the coordinate injection.

Proof: transport `Fin.castLE` across the two `Fintype.equivFin` equivalences.

Role: this supplies the injection used to assign coordinates to residual
characters.
-/
theorem exists_embedding_of_card_le {α β : Type} (R : Finset α) (S : Finset β)
    (hcard : R.card ≤ S.card) : Nonempty ({ x // x ∈ R } ↪ { i // i ∈ S }) := by
  classical
  let fR : Fintype { x // x ∈ R } := Fintype.subtype R (fun _ => Iff.rfl)
  let fS : Fintype { i // i ∈ S } := Fintype.subtype S (fun _ => Iff.rfl)
  have hfin : @Fintype.card { x // x ∈ R } fR ≤ @Fintype.card { i // i ∈ S } fS := by
    rw [Fintype.subtype_card R (fun _ => Iff.rfl)]
    rw [Fintype.subtype_card S (fun _ => Iff.rfl)]
    exact hcard
  let eR : { x // x ∈ R } ≃ Fin (@Fintype.card { x // x ∈ R } fR) :=
    @Fintype.equivFin { x // x ∈ R } fR
  let eS : { i // i ∈ S } ≃ Fin (@Fintype.card { i // i ∈ S } fS) :=
    @Fintype.equivFin { i // i ∈ S } fS
  let eFin : Fin (@Fintype.card { x // x ∈ R } fR) ↪ Fin (@Fintype.card { i // i ∈ S } fS) :=
    ⟨Fin.castLE hfin, Fin.castLE_injective hfin⟩
  exact ⟨eR.toEmbedding.trans (eFin.trans eS.symm.toEmbedding)⟩

/--
Inputs: finite sets of characters and coordinates, an injection from the
characters to the coordinates, and nonzero character-coordinate values.

Claim: coefficients can be assigned so every character in the first set
matches its value at its assigned coordinate, while all selected coefficients
remain nonzero.

Content: coordinates outside the injection image receive the coefficient one.

Proof: define each selected coefficient from the unique character mapped to
that coordinate and use injectivity to identify it.

Role: this assigns the final coordinates to the residual characters in
paper95 Theorem 1.1.
-/
theorem exists_coefficients_matching_embedding {α ι : Type} (R : Finset α) (S : Finset ι)
    (e : { x // x ∈ R } ↪ { i // i ∈ S }) (f : α → ι → ℂ) (hf : ∀ x ∈ R, ∀ i ∈ S, f x i ≠ 0) :
    ∃ a : ι → ℂ,
      (∀ i ∈ S, a i ≠ 0) ∧ ∀ x (hx : x ∈ R), f x (e ⟨x, hx⟩).val = a (e ⟨x, hx⟩).val := by
  classical
  let a : ι → ℂ := fun i =>
    if hi : i ∈ S then
      if hmatch : ∃ x : { x // x ∈ R }, (e x).val = i then f (Classical.choose hmatch).val i else 1
    else 1
  refine ⟨a, ?_, ?_⟩
  · intro i hi
    by_cases hmatch : ∃ x : { x // x ∈ R }, (e x).val = i
    · simp only [a, dite_eq_left hi, dite_eq_left hmatch]
      exact hf _ (Classical.choose hmatch).property i hi
    · simp only [a, dite_eq_left hi, dite_eq_right hmatch]
      exact one_ne_zero
  · intro x hx
    let hmatch : ∃ y : { y // y ∈ R }, (e y).val = (e ⟨x, hx⟩).val := ⟨⟨x, hx⟩, rfl⟩
    have hchoose : Classical.choose hmatch = ⟨x, hx⟩ := by
      apply e.injective
      apply Subtype.ext
      exact Classical.choose_spec hmatch
    simp only [a, dite_eq_left (e ⟨x, hx⟩).property, dite_eq_left hmatch]
    rw [hchoose]

/--
Inputs: finite character and coordinate sets, a cardinality bound, and
nonzero values for every character-coordinate pair.

Claim: nonzero coefficients can be chosen so each character matches at some
coordinate.

Content: the cardinality inequality gives an injection, then
`exists_coefficients_matching_embedding` assigns the values.

Proof: compose the finite-set injection with the coefficient assignment lemma.

Role: this is the cardinality form used for the final residual characters.
-/
theorem exists_coefficients_matching_card {α ι : Type} (R : Finset α) (S : Finset ι)
    (hcard : R.card ≤ S.card) (f : α → ι → ℂ) (hf : ∀ x ∈ R, ∀ i ∈ S, f x i ≠ 0) :
    ∃ a : ι → ℂ, (∀ i ∈ S, a i ≠ 0) ∧ ∀ x (_hx : x ∈ R), ∃ i ∈ S, f x i = a i := by
  classical
  obtain ⟨e⟩ := exists_embedding_of_card_le R S hcard
  obtain ⟨a, ha, hmatch⟩ := exists_coefficients_matching_embedding R S e f hf
  refine ⟨a, ha, ?_⟩
  intro x _hx
  refine ⟨(e ⟨x, _hx⟩).val, (e ⟨x, _hx⟩).property, ?_⟩
  exact hmatch x _hx

/--
Inputs: a complex additive character of an additive group and a group element.

Claim: the character value is nonzero.

Content: the values at an element and its inverse multiply to one.

Proof: apply the character addition law to `x + (-x)` and rule out a zero
factor.

Role: this supplies the nonzero-value condition for character-coordinate
coefficient assignments.
-/
theorem addChar_apply_ne_zero {G : Type} [AddCommGroup G] (ψ : AddChar G ℂ) (x : G) : ψ x ≠ 0 := by
  have hmul := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, ψ.map_zero_eq_one] at hmul
  intro hzero
  rw [hzero, zero_mul] at hmul
  exact one_ne_zero hmul

/--
Inputs: a finite set of complex additive characters, a finite coordinate set,
and an indexed family of group elements.

Claim: nonzero complex coefficients can be chosen so each selected character
matches its value at some selected coordinate.

Content: the cardinality bound provides an injection into the coordinates,
and additive character values are nonzero.

Proof: apply `exists_coefficients_matching_card` to character evaluation.

Role: this is the final-coordinate assignment interface in paper95
Theorem 1.1.
-/
theorem exists_character_coefficients_matching_card {G ι : Type} [AddCommGroup G]
    (R : Finset (AddChar G ℂ)) (S : Finset ι) (hcard : R.card ≤ S.card) (g : ι → G) :
    ∃ a : ι → ℂ, (∀ i ∈ S, a i ≠ 0) ∧ ∀ ψ ∈ R, ∃ i ∈ S, ψ (g i) = a i := by
  classical
  apply exists_coefficients_matching_card R S hcard (fun ψ i => ψ (g i))
  intro ψ hψ i hi
  exact addChar_apply_ne_zero ψ (g i)

/--
Inputs: an initial character set, a greedy prefix, and a finite set of
remaining coordinates large enough for the residual characters.

Claim: nonzero tail coefficients can be chosen so every initial character
matches either a prefix root value or a tail coefficient.

Content: characters removed by the prefix match one of its selected values;
residual characters are matched injectively into the tail coordinates.

Proof: split each character according to membership in the residual set and
apply the corresponding matching theorem.

Role: this combines both stages of the paper95 coefficient selection.
-/
theorem exists_character_match_prefix_or_tail {G ι : Type} [AddCommGroup G] (m : ℕ) [NeZero m]
    (hzero : ∀ x : G, m • x = 0) (S : Finset (AddChar G ℂ)) (choices : List (G × rootsOfUnity m ℂ))
    (T : Finset ι) (g : ι → G)
    (hcard : (greedyResidualCharacters m hzero S choices).card ≤ T.card) :
    ∃ a : ι → ℂ,
      (∀ i ∈ T, a i ≠ 0) ∧
        ∀ ψ ∈ S,
          (∃ choice ∈ choices, characterRootValue m hzero ψ choice.1 = choice.2) ∨
            (∃ i ∈ T, ψ (g i) = a i) := by
  classical
  obtain ⟨a, ha, hmatch⟩ :=
    exists_character_coefficients_matching_card (greedyResidualCharacters m hzero S choices) T hcard
      g
  refine ⟨a, ha, ?_⟩
  intro ψ hψ
  by_cases hres : ψ ∈ greedyResidualCharacters m hzero S choices
  · right
    exact hmatch ψ hres
  · left
    exact exists_greedy_prefix_match_of_not_residual m hzero S choices ψ hψ hres

/--
Purpose: index the concatenated prefix coordinates and tail coordinates by a
disjoint sum of finite types.

Definition: use `List.get` on the prefix side and the given coordinate map on
the tail side.

Input: the greedy prefix, a finite tail coordinate set, and its group map.

Output: the group element at each combined index.

Role: this gives one finite index type for the full coefficient construction.
-/
def prefixTailCoordinate {G ι : Type} (choices : List (G × rootsOfUnity m ℂ)) (T : Finset ι)
    (g : ι → G) : Sum (Fin choices.length) { i // i ∈ T } → G
  | .inl i => (choices.get i).1
  | .inr i => g i.val

/--
Purpose: combine root values on the greedy prefix with complex coefficients
on the tail coordinates.

Definition: project a prefix root through its unit and complex values, and
use the supplied scalar on the tail.

Input: the prefix choices, a finite tail coordinate set, and tail
coefficients.

Output: one complex coefficient at every combined index.

Role: this is the coefficient family whose character products are to vanish.
-/
def prefixTailCoefficient {G ι : Type} (choices : List (G × rootsOfUnity m ℂ)) (T : Finset ι)
    (a : ι → ℂ) : Sum (Fin choices.length) { i // i ∈ T } → ℂ
  | .inl i => (choices.get i).2.val.val
  | .inr i => a i.val

/--
Inputs: a finite initial character set, a greedy prefix, and enough tail
coordinates for the residual characters.

Claim: a single nonzero coefficient family on the disjoint union of prefix
and tail indices matches every character at some coordinate.

Content: prefix values match eliminated characters; the assigned tail values
match all residual characters.

Proof: combine the prefix-or-tail matching theorem with nonvanishing of unit
values and the chosen tail coefficients.

Role: this is the finite coefficient system needed for the Fourier
contradiction in paper95 Theorem 1.1.
-/
theorem exists_combined_character_coefficients {G ι : Type} [AddCommGroup G] (m : ℕ) [NeZero m]
    (hzero : ∀ x : G, m • x = 0) (S : Finset (AddChar G ℂ)) (choices : List (G × rootsOfUnity m ℂ))
    (T : Finset ι) (g : ι → G)
    (hcard : (greedyResidualCharacters m hzero S choices).card ≤ T.card) :
    ∃ a : Sum (Fin choices.length) { i // i ∈ T } → ℂ,
      (∀ i, a i ≠ 0) ∧ ∀ ψ ∈ S, ∃ i, ψ (prefixTailCoordinate choices T g i) = a i := by
  classical
  obtain ⟨aTail, haTail, hmatches⟩ :=
    exists_character_match_prefix_or_tail m hzero S choices T g hcard
  refine ⟨prefixTailCoefficient choices T aTail, ?_, ?_⟩
  · intro i
    cases i with
    | inl j => exact Units.ne_zero (choices.get j).2.val
    | inr j => exact haTail j.val j.property
  · intro ψ hψ
    obtain hprefix | htail := hmatches ψ hψ
    · obtain ⟨choice, hchoice, hvalue⟩ := hprefix
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hchoice
      refine ⟨Sum.inl i, ?_⟩
      simp only [prefixTailCoordinate, prefixTailCoefficient]
      rw [hi]
      exact
        (characterRootValue_val m hzero ψ choice.1).symm.trans
          (congrArg (fun z : rootsOfUnity m ℂ => z.val.val) hvalue)
    · obtain ⟨i, hi, hvalue⟩ := htail
      refine ⟨Sum.inr ⟨i, hi⟩, ?_⟩
      exact hvalue

/--
Purpose: form the arbitrary-index version of `characterKillingProduct`.

Definition: multiply `a i · 1 - X^(g i)` over a finite index set.

Inputs: a finite index set, a family of group elements, and complex
coefficients indexed by the same type.

Output: the group-algebra element used to make every character vanish at a
matching coordinate.

Role: the disjoint-sum coordinate type of the combined greedy construction is
not restricted to natural numbers.
-/
noncomputable def indexedCharacterKillingProduct {G ι : Type} [AddCommGroup G] (S : Finset ι)
    (g : ι → G) (a : ι → ℂ) : AddMonoidAlgebra ℂ G :=
  ∏ i ∈ S, (AddMonoidAlgebra.single (g i) (-1 : ℂ) + AddMonoidAlgebra.single (0 : G) (a i))

/--
Inputs: a finite index set, group elements, and complex coefficients.

Claim: `indexedCharacterKillingProduct` expands over the powerset of the
index set, with each term indexed by a subset sum.

Content: each subset contributes its sign and the coefficient product over
its complement.

Proof: expand the finite product of sums and combine basis terms with
`AddMonoidAlgebra.prod_single`.

Role: this gives the identity coefficient formula for arbitrary finite index
types.
-/
theorem indexedCharacterKillingProduct_eq_sum_powerset {G ι : Type} [AddCommGroup G] [DecidableEq ι]
    (S : Finset ι) (g : ι → G) (a : ι → ℂ) :
    indexedCharacterKillingProduct S g a =
      ∑ t ∈ S.powerset,
        AddMonoidAlgebra.single (∑ i ∈ t, g i) ((-1 : ℂ) ^ t.card * ∏ i ∈ S \ t, a i) := by
  rw [indexedCharacterKillingProduct, Finset.prod_add]
  simp only [AddMonoidAlgebra.prod_single, Finset.sum_const_zero, Finset.prod_const,
    AddMonoidAlgebra.single_mul_single, add_zero]

/--
Inputs: a finite index set, group elements, and complex coefficients.

Claim: the identity coefficient of `indexedCharacterKillingProduct` is the
weighted sum over subsets whose group sum is zero.

Content: each subset contributes its signed product of complementary
coefficients exactly when its sum is the identity.

Proof: expand the group-algebra product and evaluate each basis coefficient
at zero.

Role: this is the coefficient formula for the disjoint-sum index family.
-/
theorem coeff_zero_indexedCharacterKillingProduct {G ι : Type} [AddCommGroup G] [DecidableEq G]
    [DecidableEq ι] (S : Finset ι) (g : ι → G) (a : ι → ℂ) :
    (indexedCharacterKillingProduct S g a).coeff 0 =
      ∑ t ∈ S.powerset, if (∑ i ∈ t, g i) = 0 then (-1 : ℂ) ^ t.card * ∏ i ∈ S \ t, a i else 0 := by
  rw [indexedCharacterKillingProduct_eq_sum_powerset]
  rw [AddMonoidAlgebra.coeff_sum]
  rw [Finset.sum_apply' (0 : G)]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/--
Inputs: a finite indexed family with no nonempty zero-sum subset and complex
coefficients on its indices.

Claim: the identity coefficient of `indexedCharacterKillingProduct` is the
product of all coefficients.

Content: under the hypothesis, only the empty subset contributes to the
coefficient formula.

Proof: retain the empty subset in the powerset sum and eliminate every
nonempty subset using the zero-sum hypothesis.

Role: this supplies the nonzero coefficient for the Fourier contradiction on
the combined prefix-tail index type.
-/
theorem coeff_zero_indexedCharacterKillingProduct_eq_prod_of_no_nonempty {G ι : Type}
    [AddCommGroup G] (S : Finset ι) (g : ι → G) (a : ι → ℂ)
    (hNo : ∀ t ∈ S.powerset, (∑ i ∈ t, g i) = 0 → t = ∅) :
    (indexedCharacterKillingProduct S g a).coeff 0 = ∏ i ∈ S, a i := by
  classical
  rw [coeff_zero_indexedCharacterKillingProduct]
  rw [Finset.sum_eq_single_of_mem ∅ (by simp only [Finset.mem_powerset, Finset.empty_subset])]
  · simp only [Finset.sum_empty, Finset.card_empty, pow_zero, one_mul, Finset.sdiff_empty,
      ite_eq_left]
  · intro t ht hne
    by_cases hsum : (∑ i ∈ t, g i) = 0
    · have heq := hNo t ht hsum
      exact (hne heq).elim
    · simp only [ite_eq_right hsum]

/--
Inputs: a finite index set, group elements, complex coefficients, and an
additive character.

Claim: lifting `indexedCharacterKillingProduct` through the character gives
the product of scalar differences.

Content: each coordinate contributes `a i - ψ (g i)`.

Proof: distribute the multiplicative lift over the finite product and each
two-term group-algebra sum.

Role: this formula turns the combined matching property into zero character
evaluations.
-/
theorem lift_indexedCharacterKillingProduct {G ι : Type} [AddCommGroup G] (S : Finset ι) (g : ι → G)
    (a : ι → ℂ) (ψ : AddChar G ℂ) :
    AddMonoidAlgebra.lift ℂ ℂ G ψ.toMonoidHom (indexedCharacterKillingProduct S g a) =
      ∏ i ∈ S, (a i - ψ (g i)) := by
  classical
  simp only [indexedCharacterKillingProduct, map_prod, map_add, AddMonoidAlgebra.lift_single,
    smul_eq_mul, mul_one, neg_one_mul, sub_eq_add_neg, AddChar.toMonoidHom_apply, toAdd_ofAdd,
    AddChar.map_zero_eq_one]
  apply Finset.prod_congr rfl
  intro i hi
  exact add_comm _ _

/--
Inputs: a finite abelian group, a finite indexed family with no nonempty
zero-sum subset, and nonzero complex coefficients.

Claim: some complex additive character evaluates the indexed killing product
to a nonzero value.

Content: the identity coefficient is the nonzero product of the coefficients;
Fourier coefficient detection then forces a nonzero character evaluation.

Proof: assume all evaluations vanish, recover the zero group-algebra element,
and contradict its identity coefficient.

Role: this is the contradiction endpoint for the combined coefficient
construction.
-/
theorem exists_character_eval_ne_zero_of_indexed_no_nonempty {G ι : Type} [AddCommGroup G]
    [Finite G] (S : Finset ι) (g : ι → G) (a : ι → ℂ)
    (hNo : ∀ t ∈ S.powerset, (∑ i ∈ t, g i) = 0 → t = ∅) (ha : ∀ i ∈ S, a i ≠ 0) :
    ∃ ψ : AddChar G ℂ,
      AddMonoidAlgebra.lift ℂ ℂ G ψ.toMonoidHom (indexedCharacterKillingProduct S g a) ≠ 0 := by
  classical
  apply not_forall.mp
  intro hall
  have hz :=
    eq_zero_of_all_character_evaluations_eq_zero (indexedCharacterKillingProduct S g a) hall
  have hc := congrArg (fun x : AddMonoidAlgebra ℂ G => x.coeff 0) hz
  rw [coeff_zero_indexedCharacterKillingProduct_eq_prod_of_no_nonempty S g a hNo] at hc
  simp only [AddMonoidAlgebra.coeff_zero] at hc
  have hprod : ∏ i ∈ S, a i ≠ 0 := Finset.prod_ne_zero_iff.mpr ha
  exact hprod hc

/--
Inputs: a finite additive group, a finite indexed family, nonzero scalar
coefficients, and a matching coordinate for every additive character.

Claim: some nonempty subset of the indexed family has group sum zero.

Content: if no such subset existed, the preceding Fourier theorem would
produce a character with nonzero product evaluation, while its matching
coordinate forces one factor to vanish.

Proof: assume there is no nonempty zero-sum subset and derive the two
contradictory evaluations of `indexedCharacterKillingProduct`.

Role: this turns the combined coefficient family into the finite-group
subset-product conclusion of paper95 Theorem 1.1.
-/
theorem exists_nonempty_zero_sum_of_character_matches {G ι : Type} [AddCommGroup G] [Finite G]
    (S : Finset ι) (g : ι → G) (a : ι → ℂ) (ha : ∀ i ∈ S, a i ≠ 0)
    (hmatches : ∀ ψ : AddChar G ℂ, ∃ i ∈ S, ψ (g i) = a i) :
    ∃ t ∈ S.powerset, t ≠ ∅ ∧ (∑ i ∈ t, g i) = 0 := by
  classical
  by_contra hnone
  have hNo : ∀ t ∈ S.powerset, (∑ i ∈ t, g i) = 0 → t = ∅ := by
    intro t ht hsum
    by_contra hne
    exact hnone ⟨t, ht, hne, hsum⟩
  obtain ⟨ψ, hneval⟩ := exists_character_eval_ne_zero_of_indexed_no_nonempty S g a hNo ha
  have heval :
    AddMonoidAlgebra.lift ℂ ℂ G ψ.toMonoidHom (indexedCharacterKillingProduct S g a) = 0 := by
    rw [lift_indexedCharacterKillingProduct]
    obtain ⟨i, hi, hmatch⟩ := hmatches ψ
    exact Finset.prod_eq_zero hi (sub_eq_zero.mpr hmatch.symm)
  exact hneval heval

/--
Inputs: a finite additive group, a finite initial character set containing
all characters, a greedy prefix, and enough tail coordinates for its
residual characters.

Claim: the disjoint union of prefix and tail coordinates has a nonempty
zero-sum subset.

Content: the combined coefficient family makes every character evaluation of
the indexed killing product zero, while Fourier inversion requires a nonzero
evaluation if no such subset exists.

Proof: apply the combined coefficient construction and the arbitrary-index
Fourier contradiction theorem.

Role: this closes the coefficient-versus-zero-sum contradiction for the two
stages of paper95 Theorem 1.1.
-/
theorem exists_nonempty_zero_sum_of_greedy_prefix {G ι : Type} [AddCommGroup G] [Finite G] (m : ℕ)
    [NeZero m] (hzero : ∀ x : G, m • x = 0) (choices : List (G × rootsOfUnity m ℂ)) (T : Finset ι)
    (g : ι → G)
    (hcard :
      (greedyResidualCharacters m hzero (Finset.univ : Finset (AddChar G ℂ)) choices).card ≤
        T.card) :
    ∃ t ∈ (Finset.univ : Finset (Sum (Fin choices.length) { i // i ∈ T })).powerset,
      t ≠ ∅ ∧ (∑ i ∈ t, prefixTailCoordinate choices T g i) = 0 := by
  classical
  obtain ⟨a, ha, hmatch⟩ :=
    exists_combined_character_coefficients m hzero (Finset.univ : Finset (AddChar G ℂ)) choices T g
      hcard
  apply
    exists_nonempty_zero_sum_of_character_matches
      (Finset.univ : Finset (Sum (Fin choices.length) { i // i ∈ T }))
      (prefixTailCoordinate choices T g) a
  · intro i hi
    exact ha i
  · intro ψ
    obtain ⟨i, hvalue⟩ := hmatch ψ (Finset.mem_univ ψ)
    exact ⟨i, Finset.mem_univ i, hvalue⟩

/--
Inputs: an initial finite character set of size at most `N`, and a coordinate
list of length `floor(m * log(N / m)) + 1` in a group annihilated by `m`.

Claim: greedy values can be chosen along the list so fewer than `m`
characters remain.

Content: the iterated product bound from the prefix theorem and the logarithmic
cutoff imply the residual-cardinality bound.

Proof: apply the prefix construction, enlarge its initial-cardinality bound
to `N`, and use `geometric_product_log_bound`.

Role: this supplies the residual-size hypothesis for the final coordinate
assignment.
-/
theorem exists_greedy_character_prefix_residual_lt {G : Type} [AddCommGroup G] (m N : ℕ) [NeZero m]
    (hm : 0 < m) (hmN : m ≤ N) (hzero : ∀ x : G, m • x = 0) (S : Finset (AddChar G ℂ))
    (hS : S.card ≤ N) (coords : List G)
    (hlen : coords.length = Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) :
    ∃ choices : List (G × rootsOfUnity m ℂ),
      choices.map Prod.fst = coords ∧ (greedyResidualCharacters m hzero S choices).card < m := by
  obtain ⟨choices, hmap, hprefixbound⟩ := exists_greedy_character_prefix m hzero S coords
  rw [hlen] at hprefixbound
  have hbound :=
    hprefixbound.trans
      (Nat.mul_le_mul_left ((m - 1) ^ (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1)) hS)
  exact ⟨choices, hmap, geometric_product_log_bound m N _ hm hmN hbound⟩

/--
Inputs: the logarithmic-length coordinate prefix, a finite character family of
size at most `N`, and a finite tail index set with at least `m - 1` entries.

Claim: some nonempty subset of the combined prefix and tail indices sums to
zero in `G`.

Content: greedy selection leaves fewer than `m` characters, so each remaining
character can be assigned a distinct tail coordinate.

Proof: convert the strict residual bound to the required tail cardinality and
apply `exists_nonempty_zero_sum_of_greedy_prefix`.

Role: this is the quantitative sequence-length interface from paper95,
separated from the later indexing back to one contiguous sequence.
-/
theorem exists_nonempty_zero_sum_of_log_prefix_and_tail {G ι : Type} [AddCommGroup G] [Finite G]
    (m N : ℕ) [NeZero m] (hm : 0 < m) (hmN : m ≤ N) (hzero : ∀ x : G, m • x = 0)
    (hchars : (Finset.univ : Finset (AddChar G ℂ)).card ≤ N) (coords : List G)
    (hlen : coords.length = Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) (T : Finset ι)
    (g : ι → G) (hT : m - 1 ≤ T.card) :
    ∃ choices : List (G × rootsOfUnity m ℂ),
      choices.map Prod.fst = coords ∧
        ∃ t ∈ (Finset.univ : Finset (Sum (Fin choices.length) { i // i ∈ T })).powerset,
          t ≠ ∅ ∧ (∑ i ∈ t, prefixTailCoordinate choices T g i) = 0 := by
  obtain ⟨choices, hmap, hres⟩ :=
    exists_greedy_character_prefix_residual_lt m N hm hmN hzero Finset.univ hchars coords hlen
  refine ⟨choices, hmap, ?_⟩
  exact
    exists_nonempty_zero_sum_of_greedy_prefix m hzero choices T g
      ((Nat.le_sub_one_of_lt hres).trans hT)

/--
Inputs: a prefix of the logarithmic length from paper95, followed by `m - 1`
arbitrary group elements, with the exponent bound and character-count bound.

Claim: the combined indexed sequence has a nonempty zero-sum subset.

Content: the tail supplies one distinct coordinate for each character left by
the greedy prefix.

Proof: instantiate the finite-tail theorem with the full `Fin (m - 1)` index
set.

Role: this is the Fourier-combinatorial conclusion in the segmented indexing
used by the later finite-subsequence extraction.
-/
theorem exists_nonempty_zero_sum_of_log_length_segmented_sequence {G : Type} [AddCommGroup G]
    [Finite G] (m N : ℕ) [NeZero m] (hm : 0 < m) (hmN : m ≤ N) (hzero : ∀ x : G, m • x = 0)
    (hchars : (Finset.univ : Finset (AddChar G ℂ)).card ≤ N) (prefixCoords : List G)
    (hlen : prefixCoords.length = Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1)
    (tail : Fin (m - 1) → G) :
    ∃ choices : List (G × rootsOfUnity m ℂ),
      choices.map Prod.fst = prefixCoords ∧
        ∃
          t ∈
            (Finset.univ :
                Finset
                  (Sum (Fin choices.length)
                    { i // i ∈ (Finset.univ : Finset (Fin (m - 1))) })).powerset,
          t ≠ ∅ ∧ (∑ i ∈ t, prefixTailCoordinate choices Finset.univ tail i) = 0 := by
  have htail : m - 1 ≤ (Finset.univ : Finset (Fin (m - 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
  exact
    exists_nonempty_zero_sum_of_log_prefix_and_tail (G := G) (ι := Fin (m - 1)) (m := m) (N := N) hm
      hmN hzero hchars prefixCoords hlen (T := (Finset.univ : Finset (Fin (m - 1)))) (g := tail)
      (hT := htail)

/--
Inputs: natural parameters `m`, `N`, and `n` with `m ≥ 3`, `m ≤ N`, and
`N ≤ n`.

Claim: the logarithmic prefix length plus the `m - 1` tail positions is at
most `floor(m * log n)`.

Content: `log m ≥ 1` makes `m * (1 + log(N / m)) ≤ m * log n` when `N ≤ n`.

Proof: use `exp 1 < 3 ≤ m`, monotonicity of `log`, and monotonicity of the
natural floor.

Role: this converts the `m * log n` cardinal threshold in reliable.pdf into
the sequence length required by the paper95 Fourier theorem.
-/
theorem log_length_with_tail_le_floor_log (m N n : ℕ) (hm : 3 ≤ m) (hmN : m ≤ N) (hN : N ≤ n) :
    Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + m ≤ Nat.floor ((m : ℝ) * Real.log n) := by
  have hmPos : 0 < m := Nat.lt_of_lt_of_le (by norm_num only) hm
  have hNPos : 0 < N := Nat.lt_of_lt_of_le hmPos hmN
  have hnPos : 0 < n := Nat.lt_of_lt_of_le hNPos hN
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmPos
  have hNPosR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNPos
  have hNnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN
  have hmNR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
  have hm3R : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : 1 ≤ Real.log (m : ℝ) :=
    (Real.le_log_iff_exp_le hmR).2 (Real.exp_one_lt_three.le.trans hm3R)
  have hlogNn : Real.log (N : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log hNPosR hNnR
  have hlogratio : 1 + Real.log ((N : ℝ) / m) ≤ Real.log (n : ℝ) := by
    rw [Real.log_div hNPosR.ne' hmR.ne']
    linarith only [hlogm, hlogNn]
  have hreal : (m : ℝ) * Real.log ((N : ℝ) / m) + (m : ℝ) ≤ (m : ℝ) * Real.log (n : ℝ) := by
    calc
      (m : ℝ) * Real.log ((N : ℝ) / m) + (m : ℝ) = (m : ℝ) * (1 + Real.log ((N : ℝ) / m)) := by ring
      _ ≤ (m : ℝ) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left hlogratio hmR.le
  have hratioOne : (1 : ℝ) ≤ (N : ℝ) / m := (le_div_iff₀ hmR).2 (by simpa only [one_mul] using hmNR)
  have hlogratioNonneg : 0 ≤ Real.log ((N : ℝ) / m) := Real.log_nonneg hratioOne
  have hfloor := Nat.floor_mono hreal
  rw [Nat.floor_add_natCast (mul_nonneg (Nat.cast_nonneg m) hlogratioNonneg) m] at hfloor
  exact hfloor

/--
Inputs: `m ≥ 3`, `m ≤ N ≤ n`, and an integer `r` strictly larger than
`m * log n`.

Claim: `r` is at least the number of coordinates required by the segmented
paper95 sequence.

Content: the preceding floor comparison bounds the required length by
`floor(m * log n)`, which is strictly below `r`.

Proof: apply `Nat.floor_lt` to the strict real threshold, then compose with
`log_length_with_tail_le_floor_log`.

Role: this exposes the cardinal threshold needed to feed a sufficiently large
prime set into the Fourier subsequence construction.
-/
theorem log_length_le_nat_of_real_threshold (m N n r : ℕ) (hm : 3 ≤ m) (hmN : m ≤ N) (hN : N ≤ n)
    (hr : (m : ℝ) * Real.log n < r) : Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + m ≤ r := by
  have hfloor : Nat.floor ((m : ℝ) * Real.log n) < r := by
    apply (Nat.floor_lt (by positivity)).2
    exact_mod_cast hr
  exact (log_length_with_tail_le_floor_log m N n hm hmN hN).trans (Nat.le_of_lt hfloor)

/--
Inputs: a list whose length exceeds `m * log n`, with `m ≥ 3`, `m ≤ N ≤ n`,
and an exponent bound for the finite additive group.

Claim: the initial `floor(m * log(N / m)) + 1` entries and the following
`m - 1` entries contain a nonempty zero-sum subset.

Content: the real threshold supplies enough list entries for the segmented
Fourier subsequence theorem.

Proof: compare the required length with `floor(m * log n)`, then take the
corresponding prefix and index the following tail.

Role: this is the list form needed to apply the paper95 result to a finite set
of primes after choosing an enumeration.
-/
theorem exists_nonempty_zero_sum_of_long_list {G : Type} [AddCommGroup G] [Finite G] (m N n : ℕ)
    [NeZero m] (hm : 3 ≤ m) (hmN : m ≤ N) (hN : N ≤ n) (hzero : ∀ x : G, m • x = 0)
    (hchars : (Finset.univ : Finset (AddChar G ℂ)).card ≤ N) (coords : List G)
    (hlen : (m : ℝ) * Real.log n < coords.length) :
    ∃ choices : List (G × rootsOfUnity m ℂ),
      choices.map Prod.fst = coords.take (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) ∧
        ∃
          t ∈
            (Finset.univ :
                Finset
                  (Sum (Fin choices.length)
                    { i // i ∈ (Finset.univ : Finset (Fin (m - 1))) })).powerset,
          t ≠ ∅ ∧
            (∑ i ∈ t,
                prefixTailCoordinate choices Finset.univ
                  (fun j : Fin (m - 1) =>
                    coords.get
                      ⟨Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1 + j.val, by
                        have hmPos : 0 < m := Nat.lt_of_lt_of_le (by norm_num only) hm
                        have hlength :=
                          log_length_le_nat_of_real_threshold m N n coords.length hm hmN hN hlen
                        have hpred : 1 + (m - 1) = m := by
                          calc
                            1 + (m - 1) = (m - 1) + 1 := Nat.add_comm 1 (m - 1)
                            _ = m := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hmPos)
                        calc
                          Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1 + j.val <
                              (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) + (m - 1) :=
                            Nat.add_lt_add_left j.isLt _
                          _ = Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + m := by
                            rw [Nat.add_assoc, hpred]
                          _ ≤ coords.length := hlength⟩)
                  i) =
              0 := by
  let q := Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1
  have hmPos : 0 < m := Nat.lt_of_lt_of_le (by norm_num only) hm
  have hlength := log_length_le_nat_of_real_threshold m N n coords.length hm hmN hN hlen
  have hpred : 1 + (m - 1) = m := by
    calc
      1 + (m - 1) = (m - 1) + 1 := Nat.add_comm 1 (m - 1)
      _ = m := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hmPos)
  have htotal : q + (m - 1) ≤ coords.length := by
    dsimp [q]
    calc
      (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) + (m - 1) =
          Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + m :=
        by rw [Nat.add_assoc, hpred]
      _ ≤ coords.length := hlength
  have hq : q ≤ coords.length := (Nat.le_add_right q (m - 1)).trans htotal
  have hprefix : (coords.take q).length = q := by rw [List.length_take, Nat.min_eq_left hq]
  have htailValid (j : Fin (m - 1)) : q + j.val < coords.length :=
    (Nat.add_lt_add_left j.isLt q).trans_le htotal
  exact
    exists_nonempty_zero_sum_of_log_length_segmented_sequence m N hmPos hmN hzero hchars
      (coords.take q) (by rw [hprefix]) (fun j => coords.get ⟨q + j.val, htailValid j⟩)

/--
Inputs: a finite set of elements of a finite additive group whose cardinality
exceeds `m * log n`, with `m ≥ 3`, `m ≤ N ≤ n`, and the exponent and character
count bounds.

Claim: the standard enumeration of the set contains an indexed nonempty
zero-sum subset in its first `floor(m * log(N / m)) + m` positions.

Content: `Finset.toList` preserves the set cardinality, so the long-list result
applies directly to this enumeration.

Proof: rewrite the list length as the finset cardinality and apply
`exists_nonempty_zero_sum_of_long_list`.

Role: this is the finite-set input boundary for the reliable.pdf subset-product
construction.
-/
theorem exists_nonempty_zero_sum_of_finset_enumeration {G : Type} [AddCommGroup G] [Finite G]
    (m N n : ℕ) [NeZero m] (hm : 3 ≤ m) (hmN : m ≤ N) (hN : N ≤ n) (hzero : ∀ x : G, m • x = 0)
    (hchars : (Finset.univ : Finset (AddChar G ℂ)).card ≤ N) (S : Finset G)
    (hS : (m : ℝ) * Real.log n < S.card) :
    ∃ choices : List (G × rootsOfUnity m ℂ),
      choices.map Prod.fst = S.toList.take (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) ∧
        ∃
          t ∈
            (Finset.univ :
                Finset
                  (Sum (Fin choices.length)
                    { i // i ∈ (Finset.univ : Finset (Fin (m - 1))) })).powerset,
          t ≠ ∅ ∧
            (∑ i ∈ t,
                prefixTailCoordinate choices Finset.univ
                  (fun j : Fin (m - 1) =>
                    S.toList.get
                      ⟨Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1 + j.val, by
                        have hmPos : 0 < m := Nat.lt_of_lt_of_le (by norm_num only) hm
                        have hlong : (m : ℝ) * Real.log n < S.toList.length := by
                          rw [Finset.length_toList]
                          exact hS
                        have htail :=
                          log_length_le_nat_of_real_threshold m N n S.toList.length hm hmN hN hlong
                        have hpred : 1 + (m - 1) = m := by
                          calc
                            1 + (m - 1) = (m - 1) + 1 := Nat.add_comm 1 (m - 1)
                            _ = m := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hmPos)
                        calc
                          Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1 + j.val <
                              (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) + (m - 1) :=
                            Nat.add_lt_add_left j.isLt _
                          _ = Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + m := by
                            rw [Nat.add_assoc, hpred]
                          _ ≤ S.toList.length := htail⟩)
                  i) =
              0 := by
  have hlen : (m : ℝ) * Real.log n < S.toList.length := by
    rw [Finset.length_toList]
    exact hS
  exact exists_nonempty_zero_sum_of_long_list m N n hm hmN hN hzero hchars S.toList hlen

/--
Inputs: a finite set, a greedy prefix whose first coordinates enumerate an
initial segment of its list, and tail coordinates drawn from that set.

Claim: every combined prefix-tail coordinate belongs to the original set.

Content: the prefix membership follows from the map equality and `List.take`;
tail membership is supplied directly.

Proof: use list membership in the map and the standard `Finset.toList`
membership equivalence.

Role: this recovers the selected prime factors as elements of the finite set
used by the subset-product construction.
-/
theorem prefixTailCoordinate_mem_of_finset_enumeration {G : Type} {m : ℕ} (S : Finset G)
    (choices : List (G × rootsOfUnity m ℂ)) (q : ℕ) (hmap : choices.map Prod.fst = S.toList.take q)
    (tail : Fin (m - 1) → G) (htail : ∀ j, tail j ∈ S) :
    ∀ i : Sum (Fin choices.length) { j // j ∈ (Finset.univ : Finset (Fin (m - 1))) },
      prefixTailCoordinate choices Finset.univ tail i ∈ S := by
  intro i
  cases i with
  | inl j =>
    change (choices.get j).1 ∈ S
    have hmem : (choices.get j).1 ∈ choices.map Prod.fst :=
      List.mem_map.mpr ⟨choices.get j, List.get_mem choices j, rfl⟩
    rw [hmap] at hmem
    exact Finset.mem_toList.mp (List.mem_of_mem_take hmem)
  | inr j =>
    change tail j.val ∈ S
    exact htail j.val

/--
Inputs: a nonempty finite set of indices, an injective map from those indices
to an additive commutative monoid, and a zero sum over the indexed set.

Claim: the image is a nonempty finite subset with the same zero sum.

Content: injectivity prevents distinct selected indices from collapsing to one
element in the image.

Proof: use `Finset.sum_image` to transfer the sum and preserve nonemptiness.

Role: this converts the indexed output of the Fourier argument into the
element subset needed by the prime product construction.
-/
theorem nonempty_zero_sum_image_of_injOn {G I : Type} [AddCommMonoid G] [DecidableEq G] (f : I → G)
    (t : Finset I) (ht : t.Nonempty) (hinj : Set.InjOn f ↑t) (hsum : (∑ i ∈ t, f i) = 0) :
    (t.image f).Nonempty ∧ (∑ x ∈ t.image f, x) = 0 := by
  classical
  refine ⟨(Finset.image_nonempty).2 ht, ?_⟩
  rw [Finset.sum_image hinj]
  exact hsum

/--
Inputs: the greedy prefix matching an initial segment of `S.toList`, tail
coordinates in `S`, and an injective indexed subset with zero sum.

Claim: `S` contains a nonempty finite subset whose elements sum to zero.

Content: the coordinate map sends the selected indices into `S`; injectivity
preserves the sum when the image is formed.

Proof: apply the membership lemma and transfer the indexed sum through the
finite image.

Role: this is the direct bridge from the Fourier output to a subset of the
finite set used by the later prime product construction.
-/
theorem exists_nonempty_zero_sum_subset_of_indexed_subset {G : Type} [AddCommMonoid G] {m : ℕ}
    (S : Finset G) (choices : List (G × rootsOfUnity m ℂ)) (q : ℕ)
    (hmap : choices.map Prod.fst = S.toList.take q) (tail : Fin (m - 1) → G)
    (htail : ∀ j, tail j ∈ S)
    (t : Finset (Sum (Fin choices.length) { j // j ∈ (Finset.univ : Finset (Fin (m - 1))) }))
    (ht : t.Nonempty) (hinj : Set.InjOn (prefixTailCoordinate choices Finset.univ tail) ↑t)
    (hsum : (∑ i ∈ t, prefixTailCoordinate choices Finset.univ tail i) = 0) :
    ∃ u : Finset G, u ⊆ S ∧ u.Nonempty ∧ (∑ x ∈ u, x) = 0 := by
  classical
  let coord := prefixTailCoordinate choices Finset.univ tail
  have hmem : ∀ i, coord i ∈ S :=
    prefixTailCoordinate_mem_of_finset_enumeration S choices q hmap tail htail
  have hsum' : (∑ i ∈ t, coord i) = 0 := by simpa only [coord] using hsum
  obtain ⟨hu, husum⟩ := nonempty_zero_sum_image_of_injOn coord t ht hinj hsum'
  refine ⟨t.image coord, ?_, hu, husum⟩
  intro x hx
  obtain ⟨i, hit, hix⟩ := Finset.mem_image.mp hx
  rw [← hix]
  exact hmem i

/--
Inputs: a coordinate map factored through `S.toList.get`, with an injective
index map into the list positions.

Claim: the coordinate map is injective.

Content: `Finset.toList` has no duplicates, so distinct source positions have
distinct values.

Proof: translate coordinate equality to equality of list entries, use
`List.Nodup.get_inj_iff`, and apply injectivity of the index map.

Role: this reduces the remaining distinctness proof for the Fourier output to
constructing its source list indices.
-/
theorem prefixTailCoordinate_injective_of_list_index {G : Type} {m : ℕ} (S : Finset G)
    (choices : List (G × rootsOfUnity m ℂ)) (tail : Fin (m - 1) → G)
    (idx :
      Sum (Fin choices.length) { j // j ∈ (Finset.univ : Finset (Fin (m - 1))) } →
        Fin S.toList.length)
    (hidx : Function.Injective idx)
    (hcoordinate : ∀ i, prefixTailCoordinate choices Finset.univ tail i = S.toList.get (idx i)) :
    Function.Injective (prefixTailCoordinate choices Finset.univ tail) := by
  intro i j h
  apply hidx
  apply (List.Nodup.get_inj_iff (Finset.nodup_toList S)).mp
  rw [← hcoordinate i, ← hcoordinate j]
  exact h

/--
Inputs: the prefix length `q`, its equality with `choices.length`, and valid
positions for the following `m - 1` tail entries in `S.toList`.

Claim: assigning prefix indices to `0, ..., q - 1` and tail indices to the
following positions defines an injective map into the list positions.

Content: the prefix positions are below `q`, while each tail position is at
least `q`; within each segment, translation preserves distinctness.

Proof: split the disjoint sum into prefix and tail cases and compare natural
number indices.

Role: this is the source-position map used to prove distinctness of the
prefix-tail coordinates selected by the Fourier argument.
-/
theorem prefix_tail_source_index_injective {G : Type} {m q : ℕ} (coords : List G)
    (choices : List (G × rootsOfUnity m ℂ)) (hprefix : choices.length = q) (hq : q ≤ coords.length)
    (hbound : ∀ j : Fin (m - 1), q + j.val < coords.length) :
    Function.Injective
      (fun i : Sum (Fin choices.length) { j // j ∈ (Finset.univ : Finset (Fin (m - 1))) } =>
        match i with
        | .inl j =>
          (⟨j.val, Nat.lt_of_lt_of_le (by simpa only [hprefix] using j.isLt) hq⟩ :
            Fin coords.length)
        | .inr j => (⟨q + j.val, hbound j.val⟩ : Fin coords.length)) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      dsimp only at h
      have hv : i.val = j.val := congrArg (fun x : Fin coords.length => x.val) h
      exact congrArg Sum.inl (Fin.ext hv)
    | inr j =>
      dsimp only at h
      have hv : i.val = q + j.val := congrArg (fun x : Fin coords.length => x.val) h
      have hi : i.val < q := by simpa only [hprefix] using i.isLt
      exact False.elim ((Nat.not_lt_of_ge (Nat.le_add_right q j.val)) (hv ▸ hi))
  | inr i =>
    cases j with
    | inl j =>
      dsimp only at h
      have hv : q + i.val = j.val := congrArg (fun x : Fin coords.length => x.val) h
      have hj : j.val < q := by simpa only [hprefix] using j.isLt
      exact False.elim ((Nat.not_lt_of_ge (Nat.le_add_right q i.val)) (hv.symm ▸ hj))
    | inr j =>
      dsimp only at h
      have hv : q + i.val = q + j.val := congrArg (fun x : Fin coords.length => x.val) h
      exact congrArg Sum.inr (Subtype.ext (Fin.ext (Nat.add_left_cancel hv)))

/--
Inputs: a prefix map equality with `coords.take q`, a bound `q ≤ coords.length`,
and a prefix position `j`.

Claim: the first coordinate of `choices.get j` is the `j`-th element of `coords`.

Content: the map equality identifies prefix entries with the corresponding
entries of the coordinate list.

Proof: compare list lengths, then use `List.getElem_of_eq` and
`List.getElem_take` at the shared position.

Role: this supplies the prefix half of the coordinate factorization through
the source list used in the injectivity proof.
-/
theorem prefix_choice_eq_list_get {G : Type} {m q : ℕ} (coords : List G) (hq : q ≤ coords.length)
    (choices : List (G × rootsOfUnity m ℂ)) (hmap : choices.map Prod.fst = coords.take q)
    (j : Fin choices.length) :
    (choices.get j).1 =
      coords.get
        ⟨j.val,
          Nat.lt_of_lt_of_le
            (by
              have hlen := congrArg List.length hmap
              rw [List.length_map, List.length_take, Nat.min_eq_left hq] at hlen
              rw [← hlen]
              exact j.isLt)
            hq⟩ := by
  have htakeLen : choices.length = (coords.take q).length := by
    have hlen := congrArg List.length hmap
    simpa only [List.length_map] using hlen
  have hchoices : choices.length = q := by
    calc
      choices.length = (coords.take q).length := htakeLen
      _ = min q coords.length := by rw [List.length_take]
      _ = q := Nat.min_eq_left hq
  have jsource : j.val < coords.length := by
    exact
      Nat.lt_of_lt_of_le
        (by
          rw [← hchoices]; exact j.isLt)
        hq
  let jmap : Fin (choices.map Prod.fst).length :=
    ⟨j.val, by simpa only [List.length_map] using j.isLt⟩
  have hget : (choices.get j).1 = (choices.map Prod.fst).get jmap := by
    simp only [List.get_eq_getElem, List.getElem_map]
    rfl
  have hmapElem : (choices.map Prod.fst)[j.val] = (coords.take q)[j.val] :=
    List.getElem_of_eq hmap (i := j.val) (by simpa only [List.length_map] using j.isLt)
  calc
    (choices.get j).1 = (choices.map Prod.fst).get jmap := hget
    _ = (choices.map Prod.fst)[j.val] := by rw [List.get_eq_getElem]
    _ = (coords.take q)[j.val] := hmapElem
    _ = coords[j.val] := by rw [List.getElem_take]
    _ = coords.get ⟨j.val, jsource⟩ := by rw [List.get_eq_getElem]

/--
Inputs: the prefix enumerates the first `q` elements of `S.toList`, and the
tail uses the following `m - 1` valid list positions.

Claim: the combined prefix-tail coordinate map is injective.

Content: prefix coordinates and tail coordinates factor through disjoint
positions of the nodup list `S.toList`.

Proof: construct the source-position map, prove it injective, identify both
coordinate branches with the corresponding list entries, then use nodup.

Role: this discharges the distinctness condition needed to turn the Fourier
zero-sum indices into a finite subset of `S`.
-/
theorem prefixTailCoordinate_injective_of_finset_enumeration {G : Type} {m q : ℕ} (S : Finset G)
    (choices : List (G × rootsOfUnity m ℂ)) (hmap : choices.map Prod.fst = S.toList.take q)
    (hq : q ≤ S.toList.length) (hbound : ∀ j : Fin (m - 1), q + j.val < S.toList.length) :
    Function.Injective
      (prefixTailCoordinate choices Finset.univ
        (fun j : Fin (m - 1) => S.toList.get ⟨q + j.val, hbound j⟩)) := by
  have hprefix : choices.length = q := by
    have hlen := congrArg List.length hmap
    rw [List.length_map, List.length_take, Nat.min_eq_left hq] at hlen
    exact hlen
  let idx :
    Sum (Fin choices.length) { j // j ∈ (Finset.univ : Finset (Fin (m - 1))) } →
      Fin S.toList.length :=
    fun i =>
    match i with
    | .inl j => ⟨j.val, Nat.lt_of_lt_of_le (by simpa only [hprefix] using j.isLt) hq⟩
    | .inr j => ⟨q + j.val, hbound j.val⟩
  have hidx : Function.Injective idx :=
    prefix_tail_source_index_injective S.toList choices hprefix hq hbound
  have hcoordinate :
    ∀ i,
      prefixTailCoordinate choices Finset.univ
          (fun j : Fin (m - 1) => S.toList.get ⟨q + j.val, hbound j⟩) i =
        S.toList.get (idx i) := by
    intro i
    cases i with
    | inl j =>
      change (choices.get j).1 = S.toList.get (idx (Sum.inl j))
      simp only [idx]
      exact prefix_choice_eq_list_get S.toList hq choices hmap j
    | inr j =>
      change S.toList.get ⟨q + j.val, hbound j.val⟩ = S.toList.get (idx (Sum.inr j))
      rfl
  exact
    prefixTailCoordinate_injective_of_list_index S choices
      (fun j : Fin (m - 1) => S.toList.get ⟨q + j.val, hbound j⟩) idx hidx hcoordinate

/--
Inputs: a nodup list of labels, a map from labels to a finite additive group,
an injective source-index map, and a selected set of source indices whose
group coordinates sum to zero.

Claim: the selected labels form a nonempty finite subset of the label list,
and their mapped values sum to zero.

Content: list nodup transfers source-index injectivity to label injectivity,
so the finite image preserves the sum even when group coordinates coincide.

Proof: map the selected indices to their list labels and rewrite the weighted
sum with `Finset.sum_image`.

Role: this preserves distinct prime labels when their residues in the finite
group are not distinct.
-/
theorem exists_nonempty_zero_sum_label_subset_of_indices {G L I : Type} [AddCommMonoid G]
    [DecidableEq L] (labels : List L) (hlabels : labels.Nodup) (φ : L → G)
    (indices : I → Fin labels.length) (t : Finset I) (ht : t.Nonempty)
    (hidx : Function.Injective indices) (coord : I → G)
    (hcoord : ∀ i, coord i = φ (labels.get (indices i))) (hsum : (∑ i ∈ t, coord i) = 0) :
    ∃ U : Finset L, U.Nonempty ∧ (∀ x ∈ U, x ∈ labels.toFinset) ∧ (∑ x ∈ U, φ x) = 0 := by
  classical
  let labelAt := fun i => labels.get (indices i)
  have hlabelAt : Function.Injective labelAt := by
    intro i j h
    apply hidx
    exact (List.Nodup.get_inj_iff hlabels).mp h
  have hlabelAtOn : Set.InjOn labelAt ↑t := by
    intro i hi j hj h
    exact hlabelAt h
  have hsum' : (∑ i ∈ t, φ (labelAt i)) = 0 := by
    calc
      (∑ i ∈ t, φ (labelAt i)) = ∑ i ∈ t, coord i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hcoord i).symm
      _ = 0 := hsum
  refine ⟨t.image labelAt, (Finset.image_nonempty).2 ht, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    rw [← hix]
    exact List.mem_toFinset.mpr (List.get_mem labels (indices i))
  · rw [Finset.sum_image hlabelAtOn]
    exact hsum'

/--
Inputs: a sufficiently long nodup list of labels mapped into a finite
additive group, with exponent `m` and at most `N` characters.

Claim: some nonempty finite subset of the labels has mapped values summing to
zero.

Content: the Fourier subsequence theorem selects source positions; the prefix
and tail positions inject into the original list, whose nodup property keeps
the selected labels distinct even if their group images coincide.

Proof: apply the long-list zero-sum theorem to the mapped list, build its
source-position injection, then transfer the sum to the label image.

Role: this is the label-preserving subset-product input for AGP Proposition
1.3, where distinct primes may have equal residues in the finite group.
-/
theorem exists_nonempty_zero_sum_label_subset_of_long_list {G L : Type} [AddCommGroup G] [Finite G]
    [DecidableEq L] (m N n : ℕ) [NeZero m] (hm : 3 ≤ m) (hmN : m ≤ N) (hN : N ≤ n)
    (hzero : ∀ x : G, m • x = 0) (hchars : (Finset.univ : Finset (AddChar G ℂ)).card ≤ N)
    (labels : List L) (hlabels : labels.Nodup) (φ : L → G)
    (hlen : (m : ℝ) * Real.log n < labels.length) :
    ∃ U : Finset L, U.Nonempty ∧ (∀ x ∈ U, x ∈ labels.toFinset) ∧ (∑ x ∈ U, φ x) = 0 := by
  classical
  let coords := labels.map φ
  have hlenCoords : (m : ℝ) * Real.log n < coords.length := by
    simpa only [coords, List.length_map] using hlen
  obtain ⟨choices, hmap, t, _, htne, hsum⟩ :=
    exists_nonempty_zero_sum_of_long_list m N n hm hmN hN hzero hchars coords hlenCoords
  let q := Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1
  have hmPos : 0 < m := Nat.lt_of_lt_of_le (by norm_num only) hm
  have hlogLength := log_length_le_nat_of_real_threshold m N n coords.length hm hmN hN hlenCoords
  have hpred : 1 + (m - 1) = m := by
    calc
      1 + (m - 1) = (m - 1) + 1 := Nat.add_comm 1 (m - 1)
      _ = m := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hmPos)
  have htotal : q + (m - 1) ≤ coords.length := by
    dsimp [q]
    calc
      (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) + (m - 1) =
          Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + m :=
        by rw [Nat.add_assoc, hpred]
      _ ≤ coords.length := hlogLength
  have hq : q ≤ coords.length := (Nat.le_add_right q (m - 1)).trans htotal
  have hbound (j : Fin (m - 1)) : q + j.val < coords.length :=
    (Nat.add_lt_add_left j.isLt q).trans_le htotal
  let tail : Fin (m - 1) → G := fun j => coords.get ⟨q + j.val, hbound j⟩
  have hprefix : choices.length = q := by
    have hlen := congrArg List.length hmap
    rw [List.length_map, List.length_take, Nat.min_eq_left hq] at hlen
    exact hlen
  let idx :
    Sum (Fin choices.length) { j // j ∈ (Finset.univ : Finset (Fin (m - 1))) } →
      Fin coords.length :=
    fun i =>
    match i with
    | .inl j => ⟨j.val, Nat.lt_of_lt_of_le (by simpa only [hprefix] using j.isLt) hq⟩
    | .inr j => ⟨q + j.val, hbound j.val⟩
  have hidx : Function.Injective idx :=
    prefix_tail_source_index_injective coords choices hprefix hq hbound
  have hmapLen : coords.length = labels.length := by simp only [coords, List.length_map]
  let labelIdx :
    Sum (Fin choices.length) { j // j ∈ (Finset.univ : Finset (Fin (m - 1))) } →
      Fin labels.length :=
    fun i => Fin.cast hmapLen (idx i)
  have hlabelIdx : Function.Injective labelIdx := by
    intro i j h
    exact hidx (Fin.cast_injective hmapLen h)
  have hgetMap (k : Fin coords.length) : coords.get k = φ (labels.get (Fin.cast hmapLen k)) := by
    change (labels.map φ).get k = φ (labels.get (Fin.cast hmapLen k))
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
    rfl
  have hcoord :
    ∀ i, prefixTailCoordinate choices Finset.univ tail i = φ (labels.get (labelIdx i)) := by
    intro i
    cases i with
    | inl j =>
      change (choices.get j).1 = φ (labels.get (labelIdx (Sum.inl j)))
      rw [prefix_choice_eq_list_get coords hq choices hmap j]
      have hidxEq :
        (⟨j.val, Nat.lt_of_lt_of_le (by simpa only [hprefix] using j.isLt) hq⟩ :
            Fin coords.length) =
          idx (Sum.inl j) := by
        apply Fin.ext
        rfl
      rw [hidxEq]
      exact hgetMap (idx (Sum.inl j))
    | inr j =>
      change coords.get ⟨q + j.val, hbound j.val⟩ = φ (labels.get (labelIdx (Sum.inr j)))
      exact hgetMap (idx (Sum.inr j))
  exact
    exists_nonempty_zero_sum_label_subset_of_indices labels hlabels φ labelIdx t
      (Finset.nonempty_iff_ne_empty.mpr htne) hlabelIdx
      (prefixTailCoordinate choices Finset.univ tail) hcoord (by simpa only [q, tail] using hsum)

/--
Inputs: a nodup label list long enough for the logarithmic prefix and the
`m - 1` tail entries in the finite Fourier subsequence theorem.

Claim: the labels contain a nonempty subset whose group values sum to zero.

Content: this uses the sharp prefix length from paper95 and retains the source
labels even when distinct labels have equal group coordinates.

Proof: apply the segmented prefix-tail theorem to the mapped list, inject its
selected coordinates into the source list, then transfer the sum to labels.

Role: this allows one exceptional prime to be removed before applying the
AGP subset-product argument.
-/
theorem exists_nonempty_zero_sum_label_subset_of_segmented_length {G L : Type} [AddCommGroup G]
    [Finite G] [DecidableEq L] (m N : ℕ) [NeZero m] (hm : 0 < m) (hmN : m ≤ N)
    (hzero : ∀ x : G, m • x = 0) (hchars : (Finset.univ : Finset (AddChar G ℂ)).card ≤ N)
    (labels : List L) (hlabels : labels.Nodup) (φ : L → G)
    (hlen : Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + m ≤ labels.length) :
    ∃ U : Finset L, U.Nonempty ∧ (∀ x ∈ U, x ∈ labels.toFinset) ∧ (∑ x ∈ U, φ x) = 0 := by
  classical
  let coords := labels.map φ
  let q := Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1
  have htotal : q + (m - 1) ≤ coords.length := by
    dsimp [q]
    calc
      (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) + (m - 1) =
          Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + m :=
        by
        have hpred : 1 + (m - 1) = m := by
          calc
            1 + (m - 1) = (m - 1) + 1 := Nat.add_comm 1 (m - 1)
            _ = m := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hm)
        rw [Nat.add_assoc, hpred]
      _ ≤ coords.length := by simpa only [coords, List.length_map] using hlen
  have hq : q ≤ coords.length := (Nat.le_add_right q (m - 1)).trans htotal
  have hbound (j : Fin (m - 1)) : q + j.val < coords.length :=
    (Nat.add_lt_add_left j.isLt q).trans_le htotal
  let tail : Fin (m - 1) → G := fun j => coords.get ⟨q + j.val, hbound j⟩
  have hprefixLength :
    (coords.take q).length = Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1 := by
    simp only [List.length_take, Nat.min_eq_left hq, q]
  obtain ⟨choices, hmap, t, _, htne, hsum⟩ :=
    exists_nonempty_zero_sum_of_log_length_segmented_sequence m N hm hmN hzero hchars
      (coords.take q) hprefixLength tail
  have hprefix : choices.length = q := by
    have hlen := congrArg List.length hmap
    rw [List.length_map, List.length_take, Nat.min_eq_left hq] at hlen
    exact hlen
  let idx :
    Sum (Fin choices.length) { j // j ∈ (Finset.univ : Finset (Fin (m - 1))) } →
      Fin coords.length :=
    fun i =>
    match i with
    | .inl j => ⟨j.val, Nat.lt_of_lt_of_le (by simpa only [hprefix] using j.isLt) hq⟩
    | .inr j => ⟨q + j.val, hbound j.val⟩
  have hidx : Function.Injective idx :=
    prefix_tail_source_index_injective coords choices hprefix hq hbound
  have hmapLen : coords.length = labels.length := by simp only [coords, List.length_map]
  let labelIdx :
    Sum (Fin choices.length) { j // j ∈ (Finset.univ : Finset (Fin (m - 1))) } →
      Fin labels.length :=
    fun i => Fin.cast hmapLen (idx i)
  have hlabelIdx : Function.Injective labelIdx := by
    intro i j h
    exact hidx (Fin.cast_injective hmapLen h)
  have hgetMap (k : Fin coords.length) : coords.get k = φ (labels.get (Fin.cast hmapLen k)) := by
    change (labels.map φ).get k = φ (labels.get (Fin.cast hmapLen k))
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
    rfl
  have hcoord :
    ∀ i, prefixTailCoordinate choices Finset.univ tail i = φ (labels.get (labelIdx i)) := by
    intro i
    cases i with
    | inl j =>
      change (choices.get j).1 = φ (labels.get (labelIdx (Sum.inl j)))
      rw [prefix_choice_eq_list_get coords hq choices hmap j]
      have hidxEq :
        (⟨j.val, Nat.lt_of_lt_of_le (by simpa only [hprefix] using j.isLt) hq⟩ :
            Fin coords.length) =
          idx (Sum.inl j) :=
        Fin.ext rfl
      rw [hidxEq]
      exact hgetMap (idx (Sum.inl j))
    | inr j =>
      change coords.get ⟨q + j.val, hbound j.val⟩ = φ (labels.get (labelIdx (Sum.inr j)))
      exact hgetMap (idx (Sum.inr j))
  exact
    exists_nonempty_zero_sum_label_subset_of_indices labels hlabels φ labelIdx t
      (Finset.nonempty_iff_ne_empty.mpr htne) hlabelIdx
      (prefixTailCoordinate choices Finset.univ tail) hcoord (by simpa only [q, tail] using hsum)

/--
Inputs: a finite set indexed by `I` and a map into a commutative monoid.

Claim: applying `Additive.toMul` to the sum of the wrapped values gives their
finite product.

Content: addition on `Additive M` is multiplication on `M`.

Proof: induct over the finite set and unfold its sum and product at each step.

Role: this turns the zero-sum output for wrapped units into the product
congruence required by the Carmichael construction.
-/
theorem additive_toMul_sum_ofMul_eq_prod {I M : Type} [CommMonoid M] (s : Finset I) (f : I → M) :
    Additive.toMul (∑ i ∈ s, Additive.ofMul (f i)) = ∏ i ∈ s, f i := by
  classical
    induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    change f i * Additive.toMul (∑ j ∈ s, Additive.ofMul (f j)) = f i * ∏ j ∈ s, f j
    rw [ih]

/--
Inputs: a commutative monoid-valued map whose `Additive` values sum to zero
over a finite set.

Claim: the corresponding finite product is the identity.

Content: `additive_toMul_sum_ofMul_eq_prod` identifies the image of the sum
with the product.

Proof: rewrite the sum as zero and use injective orientation of the product
identity.

Role: this is the abstract group-to-product step for the AGP subset
construction.
-/
theorem prod_eq_one_of_additive_sum_eq_zero {I M : Type} [CommMonoid M] (s : Finset I) (f : I → M)
    (hsum : (∑ i ∈ s, Additive.ofMul (f i)) = 0) : ∏ i ∈ s, f i = 1 := by
  have hprod := additive_toMul_sum_ofMul_eq_prod s f
  rw [hsum] at hprod
  exact hprod.symm

end PseudoPrime.Combinatorics.Additive.FiniteAbelianZeroSum
