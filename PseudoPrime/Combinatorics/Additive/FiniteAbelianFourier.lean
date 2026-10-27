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

/-! # Coefficient extraction by finite group characters

This file records Fourier inversion for complex-valued functions on finite
abelian groups, using the character orthogonality formula from mathlib.
-/

@[expose] public section

namespace PseudoPrime.Combinatorics.Additive.FiniteAbelianZeroSum

/--
Purpose: encode the sums of all subsets of a finite indexed family in the
additive group algebra over `ℂ`.

Definition: for each index `i`, multiply by the sum of the identity basis term
and the basis term indexed by `g i`.

Input: a finite index set `S` and a map `g` from indices to an additive
commutative group.

Output: the group-algebra product that records the two choices at each index.

Role: its character evaluation factors as a product of `1 + ψ (g i)`, the
expression estimated in the finite abelian-group argument.
-/
noncomputable def subsetGeneratingFunction {G : Type} [AddCommGroup G] (S : Finset ℕ) (g : ℕ → G) :
    AddMonoidAlgebra ℂ G :=
  ∏ i ∈ S, (AddMonoidAlgebra.single (0 : G) (1 : ℂ) + AddMonoidAlgebra.single (g i) (1 : ℂ))

/--
Purpose: encode a product of arbitrary scalar multiples of the identity basis
minus group basis terms in the additive group algebra over `ℂ`.

Definition: multiply `a i · 1 - X^(g i)` over the finite index set `S`.

Inputs: a finite index set, a family of group elements, and scalar
coefficients.

Output: the group-algebra product used to annihilate each character at a
selected coordinate.

Role: this generalizes the subset generator to the product in the proof of
paper95 Theorem 1.1.
-/
noncomputable def characterKillingProduct {G : Type} [AddCommGroup G] (S : Finset ℕ) (g : ℕ → G)
    (a : ℕ → ℂ) : AddMonoidAlgebra ℂ G :=
  ∏ i ∈ S, (AddMonoidAlgebra.single (g i) (-1 : ℂ) + AddMonoidAlgebra.single (0 : G) (a i))

/--
Inputs: a finite index set, group elements, and complex scalar coefficients.

Claim: `characterKillingProduct` expands as a sum over subsets, with each
term indexed by the sum of its selected group elements.

Content: a subset contributes sign `(-1) ^ card(t)` and the product of the
coefficients at indices outside `t`.

Proof: apply `Finset.prod_add` and combine products of group-algebra basis
terms using `AddMonoidAlgebra.prod_single`.

Role: this expansion identifies the identity coefficient needed for the
contradiction in paper95 Theorem 1.1.
-/
theorem characterKillingProduct_eq_sum_powerset {G : Type} [AddCommGroup G] (S : Finset ℕ)
    (g : ℕ → G) (a : ℕ → ℂ) :
    characterKillingProduct S g a =
      ∑ t ∈ S.powerset,
        AddMonoidAlgebra.single (∑ i ∈ t, g i) ((-1 : ℂ) ^ t.card * ∏ i ∈ S \ t, a i) := by
  rw [characterKillingProduct, Finset.prod_add]
  simp only [AddMonoidAlgebra.prod_single, Finset.sum_const_zero, Finset.prod_const,
    AddMonoidAlgebra.single_mul_single, add_zero]

/--
Inputs: a finite index set, group elements, and complex scalar coefficients.

Claim: the identity coefficient of `characterKillingProduct` is the weighted
sum over subsets whose group sum is zero.

Content: a subset contributes its signed product of complementary coefficients
exactly when its selected group elements sum to the identity.

Proof: expand the group-algebra product over the powerset and evaluate each
basis coefficient at zero.

Role: this is the coefficient formula used with Fourier inversion in the
subset-product theorem.
-/
theorem coeff_zero_characterKillingProduct {G : Type} [AddCommGroup G] [DecidableEq G]
    (S : Finset ℕ) (g : ℕ → G) (a : ℕ → ℂ) :
    (characterKillingProduct S g a).coeff 0 =
      ∑ t ∈ S.powerset, if (∑ i ∈ t, g i) = 0 then (-1 : ℂ) ^ t.card * ∏ i ∈ S \ t, a i else 0 := by
  rw [characterKillingProduct_eq_sum_powerset]
  rw [AddMonoidAlgebra.coeff_sum]
  rw [Finset.sum_apply' (0 : G)]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/--
Inputs: a finite indexed family with no nonempty zero-sum subset, and scalar
coefficients on its indices.

Claim: the identity coefficient of `characterKillingProduct` is the product
of all scalar coefficients.

Content: under the hypothesis, only the empty subset contributes to the
coefficient formula.

Proof: use `coeff_zero_characterKillingProduct` and retain only the empty
subset in its powerset sum.

Role: this is the coefficient value compared with the Fourier character sum in
the proof of paper95 Theorem 1.1.
-/
theorem coeff_zero_characterKillingProduct_eq_prod_of_no_nonempty {G : Type} [AddCommGroup G]
    (S : Finset ℕ) (g : ℕ → G) (a : ℕ → ℂ) (hNo : ∀ t ∈ S.powerset, (∑ i ∈ t, g i) = 0 → t = ∅) :
    (characterKillingProduct S g a).coeff 0 = ∏ i ∈ S, a i := by
  classical
  rw [coeff_zero_characterKillingProduct]
  rw [Finset.sum_eq_single_of_mem ∅ (by simp only [Finset.mem_powerset, Finset.empty_subset])]
  · simp only [Finset.sum_empty, Finset.card_empty, pow_zero, one_mul, Finset.sdiff_empty,
      ite_eq_left]
  · intro t ht hne
    by_cases hsum : (∑ i ∈ t, g i) = 0
    · have heq := hNo t ht hsum
      exact (hne heq).elim
    · simp only [ite_eq_right hsum]

/--
Inputs: a finite index set `S` and a family of elements of a finite additive
commutative group.

Claim: the subset generating function is the sum of one group-algebra basis
term for each subset, indexed by the sum of that subset.

Content: this establishes the precise correspondence between choices of
factors in the defining product and subset sums, including multiplicities when
different subsets have the same sum.

Proof: expand the product over `1 + X^(g i)` with `Finset.prod_one_add` and
combine basis terms with `AddMonoidAlgebra.prod_single`.

Role: this is the combinatorial coefficient interpretation needed to extract
zero-sum subsets from the identity coefficient.
-/
theorem subsetGeneratingFunction_eq_sum_powerset {G : Type} [AddCommGroup G] (S : Finset ℕ)
    (g : ℕ → G) :
    subsetGeneratingFunction S g =
      ∑ t ∈ S.powerset, AddMonoidAlgebra.single (∑ i ∈ t, g i) (1 : ℂ) := by
  rw [subsetGeneratingFunction]
  rw [← AddMonoidAlgebra.one_def]
  rw [Finset.prod_one_add]
  simp only [AddMonoidAlgebra.prod_single, Finset.prod_const_one]

/--
Inputs: a finite index set and a family in a finite additive commutative group
with decidable equality.

Claim: the coefficient at the identity of `subsetGeneratingFunction` is the
complex cast of the number of subsets whose group sum is zero.

Content: every subset contributes one basis term in the expanded group-algebra
sum, so subsets with the same sum contribute with their multiplicities.

Proof: use `subsetGeneratingFunction_eq_sum_powerset`, evaluate each basis
coefficient, and rewrite the resulting Boolean sum as a cardinality.

Role: this identifies the identity coefficient that certifies a nonempty
zero-sum subset in the Davenport argument.
-/
theorem coeff_zero_subsetGeneratingFunction {G : Type} [AddCommGroup G] [DecidableEq G]
    (S : Finset ℕ) (g : ℕ → G) :
    (subsetGeneratingFunction S g).coeff 0 =
      (Finset.card {t ∈ S.powerset | (∑ i ∈ t, g i) = 0} : ℂ) := by
  rw [subsetGeneratingFunction_eq_sum_powerset]
  rw [AddMonoidAlgebra.coeff_sum]
  rw [Finset.sum_apply' (0 : G)]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_boole]

/--
Inputs: a finite index set and a family in an additive commutative group with
decidable equality.

Claim: there is a nonempty zero-sum subset exactly when the number of
zero-sum subsets is greater than one.

Content: the empty subset is always a zero-sum subset, so a second member of
the filtered powerset is precisely a nonempty zero-sum subset.

Proof: use `Finset.one_lt_card_iff`; in one direction, distinguish the empty
subset from another member, and in the other, pair the empty subset with the
given nonempty one.

Role: together with `coeff_zero_subsetGeneratingFunction`, this characterizes
when the identity coefficient of the generating function exceeds its empty
subset contribution.
-/
theorem exists_nonempty_zeroSum_subset_iff_one_lt_card {G : Type} [AddCommGroup G] [DecidableEq G]
    (S : Finset ℕ) (g : ℕ → G) :
    1 < Finset.card {t ∈ S.powerset | (∑ i ∈ t, g i) = 0} ↔
      ∃ t ∈ S.powerset, t.Nonempty ∧ (∑ i ∈ t, g i) = 0 := by
  classical
  let A := {t ∈ S.powerset | (∑ i ∈ t, g i) = 0}
  have h0 : ∅ ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and,
      Finset.sum_empty]
  constructor
  · intro hcard
    obtain ⟨a, b, ha, hb, hab⟩ := (Finset.one_lt_card_iff).mp hcard
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    by_cases ha0 : a = ∅
    · subst a
      exact ⟨b, hb'.1, (Finset.nonempty_iff_ne_empty).2 (Ne.symm hab), hb'.2⟩
    · exact ⟨a, ha'.1, (Finset.nonempty_iff_ne_empty).2 ha0, ha'.2⟩
  · rintro ⟨t, ht, hne, hsum⟩
    apply (Finset.one_lt_card_iff).2
    exact ⟨∅, t, h0, Finset.mem_filter.mpr ⟨ht, hsum⟩, (Finset.nonempty_iff_ne_empty.mp hne).symm⟩

/--
Inputs: a finite indexed family in an additive commutative group.

Claim: the only zero-sum subset is empty exactly when the number of zero-sum
subsets is one.

Content: the empty subset contributes one zero-sum subset, and any nonempty
zero-sum subset would make the count strictly larger.

Proof: use the preceding cardinality criterion in one direction; in the other,
the empty subset is the unique member of the filtered powerset.

Role: this gives the no-subsequence condition used to identify the identity
coefficient in the paper's group-ring contradiction.
-/
theorem card_zeroSumSubsets_eq_one_iff_no_nonempty {G : Type} [AddCommGroup G] [DecidableEq G]
    (S : Finset ℕ) (g : ℕ → G) :
    Finset.card {t ∈ S.powerset | (∑ i ∈ t, g i) = 0} = 1 ↔
      ∀ t ∈ S.powerset, (∑ i ∈ t, g i) = 0 → t = ∅ := by
  classical
  constructor
  · intro hcard t ht hsum
    by_contra hne
    have hnonempty : t.Nonempty := (Finset.nonempty_iff_ne_empty).2 hne
    have hgt := (exists_nonempty_zeroSum_subset_iff_one_lt_card S g).2 ⟨t, ht, hnonempty, hsum⟩
    rw [hcard] at hgt
    exact Nat.lt_irrefl 1 hgt
  · intro hnone
    apply (Finset.card_eq_one_iff_existsUnique).2
    refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and,
        Finset.sum_empty]
    · intro t ht
      have ht' := Finset.mem_filter.mp ht
      exact hnone t ht'.1 ht'.2

/--
Inputs: a finite indexed family in an additive commutative group.

Claim: the identity coefficient of `subsetGeneratingFunction` is one exactly
when no nonempty subset has group sum zero.

Content: the coefficient counts zero-sum subsets, including the empty subset.

Proof: rewrite the coefficient as that count and apply
`card_zeroSumSubsets_eq_one_iff_no_nonempty`.

Role: this is the coefficient form of the no-subsequence hypothesis used in
the finite-field group-ring argument.
-/
theorem coeff_zero_subsetGeneratingFunction_eq_one_iff_no_nonempty {G : Type} [AddCommGroup G]
    (S : Finset ℕ) (g : ℕ → G) :
    (subsetGeneratingFunction S g).coeff 0 = (1 : ℂ) ↔
      ∀ t ∈ S.powerset, (∑ i ∈ t, g i) = 0 → t = ∅ := by
  classical
  rw [coeff_zero_subsetGeneratingFunction, Nat.cast_eq_one]
  exact card_zeroSumSubsets_eq_one_iff_no_nonempty S g

open PseudoPrime.Data.Finset in
/--
Inputs: a finite set of complex additive characters, a group element `g`, and
an integer `m > 0` that annihilates every element of the additive group.

Claim: some `m`-th root of unity is the value at `g` of more than
`(S.card - 1) / m` characters in `S`.

Content: the character values at `g` are `m`-th roots of unity, and there are
at most `m` such roots in `ℂ`.

Proof: use `AddChar.map_nsmul_eq_pow` to place each value in `rootsOfUnity`,
then apply the finite-fiber bound to this codomain.

Role: this is the character-specific choice step in the greedy proof of
paper95 Theorem 1.1.
-/
theorem exists_large_character_value_class {G : Type} [AddCommGroup G] (S : Finset (AddChar G ℂ))
    (g : G) (m : ℕ) [NeZero m] (hzero : ∀ x : G, m • x = 0) (hS : 0 < S.card) :
    ∃ z : rootsOfUnity m ℂ,
      (S.filter fun ψ =>
            rootsOfUnity.mkOfPowEq (ψ g)
                (by
                  calc
                    (ψ g) ^ m = ψ (m • g) := (AddChar.map_nsmul_eq_pow ψ m g).symm
                    _ = 1 := by rw [hzero g, ψ.map_zero_eq_one]) =
              z).card >
        (S.card - 1) / m := by
  classical
  let fintypeRoots : Fintype (rootsOfUnity m ℂ) := Fintype.ofFinite (rootsOfUnity m ℂ)
  have hcard : @Fintype.card (rootsOfUnity m ℂ) fintypeRoots ≤ m := by
    rw [← @Nat.card_eq_fintype_card (rootsOfUnity m ℂ) fintypeRoots]
    exact card_rootsOfUnity ℂ m
  let f : AddChar G ℂ → rootsOfUnity m ℂ := fun ψ =>
    rootsOfUnity.mkOfPowEq (ψ g)
      (by
        calc
          (ψ g) ^ m = ψ (m • g) := (AddChar.map_nsmul_eq_pow ψ m g).symm
          _ = 1 := by rw [hzero g, ψ.map_zero_eq_one])
  have hlarge :=
    @exists_fiber_card_gt_div_of_card_le (AddChar G ℂ) (rootsOfUnity m ℂ) fintypeRoots
      (Classical.decEq _) S f m hcard hS
  obtain ⟨z, hz⟩ := hlarge
  refine ⟨z, ?_⟩
  simpa only [f] using hz

open PseudoPrime.Data.Finset in
/--
Inputs: a finite set of complex additive characters, a group element `g`, and
an exponent `m > 0` annihilating every group element.

Claim: some `m`-th root value at `g` leaves at most the factor
`(m - 1) / m` of the characters in the mismatch set.

Content: this is the multiplicative form of the large character-value fiber
bound, with the matching characters removed.

Proof: map each character to its `m`-th root value and apply the finite fiber
contraction theorem.

Role: this is the step iterated over the coordinates in paper95 Theorem 1.1.
-/
theorem exists_character_value_complement_mul_card_le {G : Type} [AddCommGroup G]
    (S : Finset (AddChar G ℂ)) (g : G) (m : ℕ) [NeZero m] (hzero : ∀ x : G, m • x = 0)
    (hS : 0 < S.card) :
    ∃ z : rootsOfUnity m ℂ,
      m *
          (S.filter fun ψ =>
              rootsOfUnity.mkOfPowEq (ψ g)
                  (by
                    calc
                      (ψ g) ^ m = ψ (m • g) := (AddChar.map_nsmul_eq_pow ψ m g).symm
                      _ = 1 := by rw [hzero g, ψ.map_zero_eq_one]) ≠
                z).card ≤
        (m - 1) * S.card := by
  classical
  let fintypeRoots : Fintype (rootsOfUnity m ℂ) := Fintype.ofFinite (rootsOfUnity m ℂ)
  have hcard : @Fintype.card (rootsOfUnity m ℂ) fintypeRoots ≤ m := by
    rw [← @Nat.card_eq_fintype_card (rootsOfUnity m ℂ) fintypeRoots]
    exact card_rootsOfUnity ℂ m
  let f : AddChar G ℂ → rootsOfUnity m ℂ := fun ψ =>
    rootsOfUnity.mkOfPowEq (ψ g)
      (by
        calc
          (ψ g) ^ m = ψ (m • g) := (AddChar.map_nsmul_eq_pow ψ m g).symm
          _ = 1 := by rw [hzero g, ψ.map_zero_eq_one])
  have h :=
    @exists_fiber_complement_mul_card_le (AddChar G ℂ) (rootsOfUnity m ℂ) fintypeRoots
      (Classical.decEq _) S f m (NeZero.pos m) hcard hS
  obtain ⟨z, hz⟩ := h
  refine ⟨z, ?_⟩
  simpa only [f] using hz

/--
Inputs: an exponent annihilating the additive group, a complex additive
character, and a group element.

Claim: `characterRootValue` is the root-of-unity subtype representing the
character value at that element.

Content: the exponent condition makes the character value an `m`-th root of
unity.

Proof: map `m • g = 0` through the character addition law.

Role: this packages the root values used by each greedy coordinate choice.
-/
noncomputable def characterRootValue {G : Type} [AddCommGroup G] (m : ℕ) [NeZero m]
    (hzero : ∀ x : G, m • x = 0) (ψ : AddChar G ℂ) (g : G) : rootsOfUnity m ℂ := by
  exact
    rootsOfUnity.mkOfPowEq (ψ g)
      (by
        calc
          (ψ g) ^ m = ψ (m • g) := (AddChar.map_nsmul_eq_pow ψ m g).symm
          _ = 1 := by rw [hzero g, ψ.map_zero_eq_one])

/--
Inputs: an annihilating exponent, a complex additive character, and a group
element.

Claim: the unit underlying `characterRootValue` has complex value `ψ g`.

Content: the root-of-unity subtype is a subgroup of the unit group, so its
underlying complex value is obtained through two subtype projections.

Proof: the value projection of `rootsOfUnity.mkOfPowEq` reduces to its input.

Role: this converts the prefix root choices into scalar coefficients.
-/
theorem characterRootValue_val {G : Type} [AddCommGroup G] (m : ℕ) [NeZero m]
    (hzero : ∀ x : G, m • x = 0) (ψ : AddChar G ℂ) (g : G) :
    (characterRootValue m hzero ψ g).val.val = ψ g := by rfl

/--
Inputs: a finite character set, a group coordinate, and an exponent that
annihilates the group.

Claim: one can choose a root value whose mismatch set contracts by the
factor `(m - 1) / m`, including when the current set is empty.

Content: the positive-cardinality case is the fiber bound; the empty case
uses the root value `1`.

Proof: split on whether the finite set is empty and apply the fiber theorem
in the nonempty case.

Role: this total one-step choice supports recursive construction of the
greedy coordinate prefix.
-/
theorem exists_greedy_character_coordinate {G : Type} [AddCommGroup G] (S : Finset (AddChar G ℂ))
    (g : G) (m : ℕ) [NeZero m] (hzero : ∀ x : G, m • x = 0) :
    ∃ z : rootsOfUnity m ℂ,
      m * (S.filter fun ψ => characterRootValue m hzero ψ g ≠ z).card ≤ (m - 1) * S.card := by
  classical
  by_cases hS : 0 < S.card
  · obtain ⟨z, hz⟩ := exists_character_value_complement_mul_card_le S g m hzero hS
    refine ⟨z, ?_⟩
    exact hz
  · refine ⟨1, ?_⟩
    have hcard : S.card = 0 := Nat.eq_zero_of_not_pos hS
    have hSempty : S = ∅ := Finset.card_eq_zero.mp hcard
    simp only [hSempty, Finset.filter_empty, Finset.card_empty, Nat.mul_zero]
    exact Nat.le_refl 0

/--
Purpose: retain characters that disagree with each chosen value at every
coordinate in a finite list.

Definition: fold the coordinate/value pairs from left to right, filtering out
characters that agree at the current coordinate.

Input: the initial finite character set and a list of group coordinates
paired with root values.

Output: the residual set after all selected coordinates.

Role: this is the state updated by the paper95 greedy construction.
-/
noncomputable def greedyResidualCharacters {G : Type} [AddCommGroup G] (m : ℕ) [NeZero m]
    (hzero : ∀ x : G, m • x = 0) (S : Finset (AddChar G ℂ)) :
    List (G × rootsOfUnity m ℂ) → Finset (AddChar G ℂ) :=
  List.foldl (fun T choice => T.filter fun ψ => characterRootValue m hzero ψ choice.1 ≠ choice.2) S

/--
Inputs: an initial finite character set, a list of coordinate/value pairs,
and a character.

Claim: the character survives precisely when it starts in the set and
disagrees with every selected value.

Content: this membership criterion identifies the characters eliminated by
the greedy prefix.

Proof: unfold the fold and induct on its list of coordinate/value pairs.

Role: the criterion connects prefix elimination to vanishing factors in the
final group-algebra product.
-/
theorem mem_greedyResidualCharacters_iff {G : Type} [AddCommGroup G] (m : ℕ) [NeZero m]
    (hzero : ∀ x : G, m • x = 0) (S : Finset (AddChar G ℂ)) (choices : List (G × rootsOfUnity m ℂ))
    (ψ : AddChar G ℂ) :
    ψ ∈ greedyResidualCharacters m hzero S choices ↔
      ψ ∈ S ∧ ∀ choice ∈ choices, characterRootValue m hzero ψ choice.1 ≠ choice.2 := by
  classical
    induction choices generalizing S with
  | nil =>
    change
      ψ ∈ S ↔
        ψ ∈ S ∧
          ∀ choice : G × rootsOfUnity m ℂ,
            choice ∈ [] → characterRootValue m hzero ψ choice.1 ≠ choice.2
    constructor
    · intro hψ
      exact
        ⟨hψ, by
          intro choice hchoice; cases hchoice⟩
    · intro hψ
      exact hψ.1
  | cons choice choices
    ih =>
    change
      ψ ∈
          greedyResidualCharacters m hzero
            (S.filter fun χ => characterRootValue m hzero χ choice.1 ≠ choice.2) choices ↔
        ψ ∈ S ∧ ∀ pair ∈ choice :: choices, characterRootValue m hzero ψ pair.1 ≠ pair.2
    rw [ih]
    constructor
    · intro hψ
      rcases hψ with ⟨hfilter, htail⟩
      rcases Finset.mem_filter.mp hfilter with ⟨hS, hfirst⟩
      refine ⟨hS, ?_⟩
      intro pair hpair
      rcases List.mem_cons.mp hpair with heq | hmem
      · subst pair
        exact hfirst
      · exact htail pair hmem
    · intro hψ
      rcases hψ with ⟨hS, hchoices⟩
      have hfirst := hchoices choice List.mem_cons_self
      have htail : ∀ pair ∈ choices, characterRootValue m hzero ψ pair.1 ≠ pair.2 := by
        intro pair hpair
        exact hchoices pair (List.mem_cons_of_mem choice hpair)
      exact ⟨Finset.mem_filter.mpr ⟨hS, hfirst⟩, htail⟩

/--
Inputs: a character in the initial finite set and a greedy prefix it does not
survive.

Claim: the character value matches one of the selected root values.

Content: a character is removed exactly at a coordinate where its value is
the chosen root.

Proof: if every value disagreed, the residual membership criterion would
place the character in the final residual set.

Role: this gives the prefix half of the coefficient matching argument.
-/
theorem exists_greedy_prefix_match_of_not_residual {G : Type} [AddCommGroup G] (m : ℕ) [NeZero m]
    (hzero : ∀ x : G, m • x = 0) (S : Finset (AddChar G ℂ)) (choices : List (G × rootsOfUnity m ℂ))
    (ψ : AddChar G ℂ) (hψ : ψ ∈ S) (hnot : ψ ∉ greedyResidualCharacters m hzero S choices) :
    ∃ choice ∈ choices, characterRootValue m hzero ψ choice.1 = choice.2 := by
  classical
  by_contra hnone
  apply hnot
  apply (mem_greedyResidualCharacters_iff m hzero S choices ψ).2
  refine ⟨hψ, ?_⟩
  intro choice hchoice heq
  exact hnone ⟨choice, hchoice, heq⟩

/--
Inputs: a finite list of group coordinates and an initial finite set of
characters in a group annihilated by `m`.

Claim: one can choose a root value at each coordinate so that the residual
character count contracts by `(m - 1) / m` at every step.

Content: the returned pairs have the prescribed coordinates, and their
residual set satisfies the iterated natural-number contraction bound.

Proof: induct on the coordinate list, use the total one-step choice, then
combine the one-step and induction bounds by multiplication.

Role: this is the finite greedy prefix needed before the paper95 tail
assignment.
-/
theorem exists_greedy_character_prefix {G : Type} [AddCommGroup G] (m : ℕ) [NeZero m]
    (hzero : ∀ x : G, m • x = 0) (S : Finset (AddChar G ℂ)) (coords : List G) :
    ∃ choices : List (G × rootsOfUnity m ℂ),
      choices.map Prod.fst = coords ∧
        m ^ coords.length * (greedyResidualCharacters m hzero S choices).card ≤
          (m - 1) ^ coords.length * S.card := by
  induction coords generalizing S with
  | nil =>
    refine ⟨[], ?_, ?_⟩
    · rfl
    · simp only [List.length_nil, Nat.pow_zero, Nat.one_mul, greedyResidualCharacters,
        List.foldl_nil]
      exact Nat.le_refl _
  | cons g gs ih =>
    obtain ⟨z, hz⟩ := exists_greedy_character_coordinate S g m hzero
    let T := S.filter fun ψ => characterRootValue m hzero ψ g ≠ z
    obtain ⟨tail, htailMap, htailBound⟩ := ih T
    refine ⟨(g, z) :: tail, ?_, ?_⟩
    · simp only [List.map_cons]
      rw [htailMap]
    · have hres :
        greedyResidualCharacters m hzero S ((g, z) :: tail) =
          greedyResidualCharacters m hzero T tail := by
        simp only [greedyResidualCharacters, List.foldl_cons]
        rfl
      rw [List.length_cons, hres]
      calc
        m ^ (gs.length + 1) * (greedyResidualCharacters m hzero T tail).card =
            m * (m ^ gs.length * (greedyResidualCharacters m hzero T tail).card) :=
          by
          rw [Nat.pow_succ]
          ac_rfl
        _ ≤ m * ((m - 1) ^ gs.length * T.card) := Nat.mul_le_mul_left m htailBound
        _ = (m - 1) ^ gs.length * (m * T.card) := by ac_rfl
        _ ≤ (m - 1) ^ gs.length * ((m - 1) * S.card) := Nat.mul_le_mul_left ((m - 1) ^ gs.length) hz
        _ = (m - 1) ^ (gs.length + 1) * S.card := by
          rw [Nat.pow_succ]
          ac_rfl

/--
Inputs: a multiplier `m`, a number of steps `k`, and a sequence of natural
numbers whose successive terms satisfy the one-step contraction inequality.

Claim: after `k` steps, `m ^ k * r k ≤ (m - 1) ^ k * r 0`.

Content: iterating the fiber contraction gives a geometric bound on the
number of residual characters.

Proof: induct on the number of steps and multiply each one-step inequality by
the accumulated power.

Role: this is the discrete estimate used before applying the logarithmic
threshold in paper95 Theorem 1.1.
-/
theorem geometric_contraction_iterate (m k : ℕ) (r : ℕ → ℕ)
    (hstep : ∀ i < k, m * r (i + 1) ≤ (m - 1) * r i) : m ^ k * r k ≤ (m - 1) ^ k * r 0 := by
  induction k with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul]
    exact Nat.le_refl _
  | succ k
    ih =>
    have hprefix : ∀ i < k, m * r (i + 1) ≤ (m - 1) * r i := by
      intro i hi
      exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self k))
    have hih := ih hprefix
    have hstage := hstep k (Nat.lt_succ_self k)
    calc
      m ^ (k + 1) * r (k + 1) = m ^ k * (m * r (k + 1)) := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ m ^ k * ((m - 1) * r k) := Nat.mul_le_mul_left (m ^ k) hstage
      _ = (m - 1) * (m ^ k * r k) := by ac_rfl
      _ ≤ (m - 1) * ((m - 1) ^ k * r 0) := Nat.mul_le_mul_left (m - 1) hih
      _ = (m - 1) ^ (k + 1) * r 0 := by
        rw [Nat.pow_succ]
        ac_rfl

/--
Inputs: natural numbers `m > 0` and `k`.

Claim: the `k`-th power of `1 - 1/m` is at most `exp(-k/m)`.

Content: the exponential estimate converts the discrete contraction into the
logarithmic threshold used in paper95 Theorem 1.1.

Proof: raise `1 - x ≤ exp(-x)` to the natural power `k` and combine the
exponential powers.

Role: this is the analytic estimate for the residual-character bound.
-/
theorem one_sub_inv_nat_pow_le_exp_neg (m k : ℕ) (hm : 0 < m) :
    (1 - 1 / (m : ℝ)) ^ k ≤ Real.exp (-((k : ℝ) / m)) := by
  have hm1Nat : 1 ≤ m := Nat.succ_le_iff.mpr hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by simpa only [Nat.cast_one] using Nat.cast_le.mpr hm1Nat
  have hdiv : 1 / (m : ℝ) ≤ 1 := by
    simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one hm1
  have hbase : 0 ≤ 1 - 1 / (m : ℝ) := sub_nonneg.mpr hdiv
  have hpow := pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg (1 / (m : ℝ))) k
  calc
    (1 - 1 / (m : ℝ)) ^ k ≤ Real.exp (-(1 / (m : ℝ))) ^ k := hpow
    _ = Real.exp (-(1 / (m : ℝ)) * k) := by rw [← Real.exp_nat_mul, mul_comm]
    _ = Real.exp (-((k : ℝ) / m)) := by
      congr 1
      ring

/--
Inputs: natural numbers `m` and `N` with `0 < m` and `m ≤ N`.

Claim: for `k = floor(m * log(N / m)) + 1`, `exp(-k/m) < m/N`.

Content: the floor threshold makes the negative exponent strictly smaller
than the reciprocal of the ratio `N/m`.

Proof: use `Nat.lt_floor_add_one`, divide by positive `m`, and apply strict
monotonicity of the exponential.

Role: this supplies the strict cutoff needed to show fewer than `m` residual
characters remain after the greedy steps.
-/
theorem exp_neg_floor_log_ratio_lt_inv (m N : ℕ) (hm : 0 < m) (hmN : m ≤ N) :
    Real.exp (-(((Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1 : ℕ) : ℝ) / m)) <
      1 / ((N : ℝ) / m) := by
  let u : ℝ := (N : ℝ) / m
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hm hmN)
  have hu : 0 < u := by
    dsimp only [u]
    exact div_pos hNR hmR
  have hk : Real.log u < ((Nat.floor ((m : ℝ) * Real.log u) + 1 : ℕ) : ℝ) / m := by
    rw [lt_div_iff₀ hmR]
    rw [Nat.cast_add, Nat.cast_one]
    calc
      Real.log u * m = m * Real.log u := by rw [mul_comm]
      _ < (Nat.floor ((m : ℝ) * Real.log u) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hexp :
    Real.exp (-(((Nat.floor ((m : ℝ) * Real.log u) + 1 : ℕ) : ℝ) / m)) < Real.exp (-Real.log u) :=
    Real.exp_lt_exp.mpr (neg_lt_neg hk)
  have hlog : Real.exp (-Real.log u) = 1 / u := by rw [Real.exp_neg, Real.exp_log hu, one_div]
  calc
    Real.exp (-(((Nat.floor ((m : ℝ) * Real.log u) + 1 : ℕ) : ℝ) / m)) < Real.exp (-Real.log u) :=
      hexp
    _ = 1 / u := hlog
    _ = 1 / ((N : ℝ) / m) := by dsimp only [u]

/--
Inputs: natural numbers `m > 0` and `N ≥ m`.

Claim: with `k = floor(m * log(N / m)) + 1`,
`(1 - 1/m)^k * N < m`.

Content: the exponential estimate and the floor cutoff combine to make the
geometric residual bound smaller than the group exponent.

Proof: multiply the power-to-exponential estimate and the strict cutoff by
the positive real number `N`.

Role: this is the real inequality needed to finish the residual cardinality
bound for paper95 Theorem 1.1.
-/
theorem one_sub_inv_floor_log_ratio_pow_mul_lt (m N : ℕ) (hm : 0 < m) (hmN : m ≤ N) :
    (1 - 1 / (m : ℝ)) ^ (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) * N < m := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hm hmN)
  have hpow :=
    one_sub_inv_nat_pow_le_exp_neg m (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) hm
  have hcut := exp_neg_floor_log_ratio_lt_inv m N hm hmN
  calc
    (1 - 1 / (m : ℝ)) ^ (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) * N ≤
        Real.exp (-(((Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1 : ℕ) : ℝ) / m)) * N :=
      mul_le_mul_of_nonneg_right hpow (le_of_lt hNR)
    _ < (1 / ((N : ℝ) / m)) * N := mul_lt_mul_of_pos_right hcut hNR
    _ = m := by
      rw [one_div_div]
      exact div_mul_cancel₀ (m : ℝ) hNR.ne'

/--
Inputs: natural numbers `m > 0`, `N ≥ m`, and a residual cardinality `r`.

Claim: if the endpoint contraction bound holds after the logarithmic number
of steps, then `r < m`.

Content: the natural-number product inequality gives the real ratio bound,
which is strictly below `m` by the floor-log estimate.

Proof: cast the endpoint inequality to `ℝ`, divide by `m ^ k`, and apply the
strict exponential cutoff.

Role: this extracts the small residual set directly from the prefix theorem.
-/
theorem geometric_product_log_bound (m N r : ℕ) (hm : 0 < m) (hmN : m ≤ N)
    (hbound :
      m ^ (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) * r ≤
        (m - 1) ^ (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) * N) :
    r < m := by
  let k := Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1
  have hmNat : 1 ≤ m := Nat.succ_le_iff.mpr hm
  have hboundR : (m : ℝ) ^ k * (r : ℝ) ≤ ((m : ℝ) - 1) ^ k * N := by exact_mod_cast hbound
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hmPow : 0 < (m : ℝ) ^ k := pow_pos hmR k
  have hmulR : (r : ℝ) * (m : ℝ) ^ k ≤ ((m : ℝ) - 1) ^ k * N := by
    calc
      (r : ℝ) * (m : ℝ) ^ k = (m : ℝ) ^ k * (r : ℝ) := by rw [mul_comm]
      _ ≤ ((m : ℝ) - 1) ^ k * N := hboundR
  have hratio : (r : ℝ) ≤ (((m : ℝ) - 1) ^ k * N) / (m : ℝ) ^ k := (le_div_iff₀ hmPow).2 hmulR
  have hsub : ((m : ℝ) - 1) / m = 1 - 1 / m := by rw [sub_div, div_self hmR.ne']
  have hfactor : (((m : ℝ) - 1) ^ k * N) / (m : ℝ) ^ k = (1 - 1 / m) ^ k * N := by
    calc
      (((m : ℝ) - 1) ^ k * N) / (m : ℝ) ^ k = (((m : ℝ) - 1) ^ k / (m : ℝ) ^ k) * N := by
        rw [mul_div_right_comm]
      _ = (((m : ℝ) - 1) / m) ^ k * N := by rw [← div_pow]
      _ = (1 - 1 / m) ^ k * N := by rw [hsub]
  rw [hfactor] at hratio
  have hsmall := one_sub_inv_floor_log_ratio_pow_mul_lt m N hm hmN
  exact_mod_cast hratio.trans_lt hsmall

/--
Inputs: `m > 0`, a starting bound `m ≤ N`, and a sequence whose terms
contract by the factor `(m - 1) / m` at each step.

Claim: after `floor(m * log(N / m)) + 1` steps, the sequence term is below
`m`, provided its initial term is at most `N`.

Content: this is the logarithmic residual-character bound in
paper95 Theorem 1.1.

Proof: iterate the natural-number contraction, cast it to `ℝ`, divide by
`m ^ k`, and apply the preceding strict exponential estimate.

Role: this is the quantitative greedy bound before the final coordinate
assignment.
-/
theorem geometric_contraction_log_bound (m N : ℕ) (hm : 0 < m) (hmN : m ≤ N) (r : ℕ → ℕ)
    (hinit : r 0 ≤ N)
    (hstep :
      ∀ i < Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1, m * r (i + 1) ≤ (m - 1) * r i) :
    r (Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1) < m := by
  let k := Nat.floor ((m : ℝ) * Real.log ((N : ℝ) / m)) + 1
  have hiter :=
    geometric_contraction_iterate m k r
      (by
        intro i hi
        exact hstep i (by simpa only [k] using hi))
  have hbound := hiter.trans (Nat.mul_le_mul_left ((m - 1) ^ k) hinit)
  have hmNat : 1 ≤ m := Nat.succ_le_iff.mpr hm
  have hboundR : (m : ℝ) ^ k * (r k : ℝ) ≤ ((m : ℝ) - 1) ^ k * N := by exact_mod_cast hbound
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hmPow : 0 < (m : ℝ) ^ k := pow_pos hmR k
  have hmulR : (r k : ℝ) * (m : ℝ) ^ k ≤ ((m : ℝ) - 1) ^ k * N := by
    calc
      (r k : ℝ) * (m : ℝ) ^ k = (m : ℝ) ^ k * (r k : ℝ) := by rw [mul_comm]
      _ ≤ ((m : ℝ) - 1) ^ k * N := hboundR
  have hratio : (r k : ℝ) ≤ (((m : ℝ) - 1) ^ k * N) / (m : ℝ) ^ k := (le_div_iff₀ hmPow).2 hmulR
  have hsub : ((m : ℝ) - 1) / m = 1 - 1 / m := by rw [sub_div, div_self hmR.ne']
  have hfactor : (((m : ℝ) - 1) ^ k * N) / (m : ℝ) ^ k = (1 - 1 / m) ^ k * N := by
    calc
      (((m : ℝ) - 1) ^ k * N) / (m : ℝ) ^ k = (((m : ℝ) - 1) ^ k / (m : ℝ) ^ k) * N := by
        rw [mul_div_right_comm]
      _ = (((m : ℝ) - 1) / m) ^ k * N := by rw [← div_pow]
      _ = (1 - 1 / m) ^ k * N := by rw [hsub]
  rw [hfactor] at hratio
  have hsmall := one_sub_inv_floor_log_ratio_pow_mul_lt m N hm hmN
  change r k < m
  exact_mod_cast hratio.trans_lt hsmall

/--
Inputs: a finite additive commutative group, a finite set of its complex
additive characters, and an element of the group.

Claim: some value of that element among the characters occurs more than
`(S.card - 1) / exponent(G)` times.

Content: the group exponent annihilates every element, so the preceding
character-value class bound applies with `m = AddMonoid.exponent G`.

Proof: apply `exists_large_character_value_class` with
`AddMonoid.exponent_nsmul_eq_zero`.

Role: this instantiates the greedy fiber choice at the canonical exponent of
the finite abelian group.
-/
theorem exists_large_character_value_class_of_exponent {G : Type} [AddCommGroup G] [Finite G]
    (S : Finset (AddChar G ℂ)) (g : G) (hS : 0 < S.card) :
    ∃ z : rootsOfUnity (AddMonoid.exponent G) ℂ,
      (S.filter fun ψ =>
            rootsOfUnity.mkOfPowEq (ψ g)
                (by
                  calc
                    (ψ g) ^ AddMonoid.exponent G = ψ (AddMonoid.exponent G • g) :=
                      (AddChar.map_nsmul_eq_pow ψ (AddMonoid.exponent G) g).symm
                    _ = 1 := by rw [AddMonoid.exponent_nsmul_eq_zero, ψ.map_zero_eq_one]) =
              z).card >
        (S.card - 1) / AddMonoid.exponent G := by
  exact
    exists_large_character_value_class S g (AddMonoid.exponent G) AddMonoid.exponent_nsmul_eq_zero
      hS

/--
Inputs: a finite indexed family in an additive commutative group and a complex
additive character.

Claim: evaluating `subsetGeneratingFunction` at the character gives the
product of the corresponding factors `1 + ψ (g i)`.

Content: this turns the group-algebra subset generator into the multiplicative
expression used in character estimates.

Proof: use multiplicativity and additivity of `AddMonoidAlgebra.lift`, then
evaluate each single basis term.

Role: this is the product-evaluation interface for the AGP subset-product
argument.
-/
theorem lift_subsetGeneratingFunction {G : Type} [AddCommGroup G] (S : Finset ℕ) (g : ℕ → G)
    (ψ : AddChar G ℂ) :
    AddMonoidAlgebra.lift ℂ ℂ G ψ.toMonoidHom (subsetGeneratingFunction S g) =
      ∏ i ∈ S, (1 + ψ (g i)) := by
  simp only [subsetGeneratingFunction, map_prod, map_add, AddMonoidAlgebra.lift_single, one_smul,
    AddChar.toMonoidHom_apply, toAdd_ofAdd, AddChar.map_zero_eq_one]

/--
Inputs: a finite index set, group elements, scalar coefficients, and a complex
additive character.

Claim: evaluating `characterKillingProduct` at the character gives the
product of scalar differences `a i - ψ (g i)`.

Content: each selected coordinate makes one factor vanish for a matching
character value.

Proof: use multiplicativity and subtraction preservation of the group-algebra
lift, then evaluate each basis term.

Role: this is the character-evaluation interface for the arbitrary-coefficient
product in paper95 Theorem 1.1.
-/
theorem lift_characterKillingProduct {G : Type} [AddCommGroup G] (S : Finset ℕ) (g : ℕ → G)
    (a : ℕ → ℂ) (ψ : AddChar G ℂ) :
    AddMonoidAlgebra.lift ℂ ℂ G ψ.toMonoidHom (characterKillingProduct S g a) =
      ∏ i ∈ S, (a i - ψ (g i)) := by
  simp only [characterKillingProduct, map_prod, map_add, AddMonoidAlgebra.lift_single, smul_eq_mul,
    mul_one, neg_one_mul, sub_eq_add_neg, AddChar.toMonoidHom_apply, toAdd_ofAdd,
    AddChar.map_zero_eq_one]
  apply Finset.prod_congr rfl
  intro i hi
  exact add_comm _ _

/--
Inputs: a finite additive commutative group `G`, a complex-valued function `f`
on `G`, and an element `a` of `G`.

Claim: the value `f a`, multiplied by the cardinality of `G`, is recovered by
summing the character evaluations of `f` against the inverse character value
at `a`.

Content: this is the coefficient extraction identity underlying finite
Fourier inversion. It will detect the identity coefficient of a group algebra
element from its evaluations at all complex characters.

Proof: expand the character-weighted sum, exchange the two finite sums, and
apply `AddChar.sum_apply_eq_ite` to the inner character sum.

Role: this supplies the orthogonality step for formalizing the finite
abelian-group argument in the AGP construction.
-/
theorem fourier_reconstruction {G : Type} [AddCommGroup G] [Fintype G] (f : G → ℂ) (a : G) :
    (Fintype.card G : ℂ) * f a =
      ∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)),
        (∑ g ∈ (Finset.univ : Finset G), f g * ψ g) * ψ (-a) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, ← AddChar.map_add_eq_mul]
  simp_rw [AddChar.sum_apply_eq_ite]
  simp only [add_eq_zero_iff_eq_neg, neg_neg, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, mul_comm]

/--
Inputs: an element of the complex additive group algebra of a finite
commutative group and a complex-valued additive character.

Claim: evaluating the algebra element by lifting the character equals the
finite Fourier sum of its coefficient function.

Content: this identifies mathlib's group-algebra evaluation with the Fourier
transform used by `fourier_reconstruction`.

Proof: expand `AddMonoidAlgebra.lift` as a sum over the finitely supported
coefficients, extend that sum to the finite group, and simplify the character
homomorphism.

Role: this bridges abstract group-algebra elements to the coefficient
extraction results in this file.
-/
theorem addMonoidAlgebra_lift_eq_character_sum {G : Type} [AddCommGroup G] [Fintype G]
    (x : AddMonoidAlgebra ℂ G) (ψ : AddChar G ℂ) :
    AddMonoidAlgebra.lift ℂ ℂ G ψ.toMonoidHom x =
      ∑ g ∈ (Finset.univ : Finset G), x.coeff g * ψ g := by
  rw [AddMonoidAlgebra.lift_apply]
  rw [Finsupp.sum_fintype]
  · simp only [smul_eq_mul, AddChar.toMonoidHom_apply, toAdd_ofAdd]
  · intro i
    simp only [zero_smul]

/--
Inputs: a complex-valued function on a finite additive commutative group, with
zero character sum at every complex-valued additive character.

Claim: the function is identically zero.

Content: this is the coefficient-vanishing consequence of finite Fourier
inversion, and gives an injectivity test for evaluating group-algebra
coefficients at all characters.

Proof: reconstruct each value from its character sums and use that the
cardinality of a finite group is nonzero in `ℂ`.

Role: this lets the AGP group-ring argument detect a nonzero coefficient by at
least one character evaluation.
-/
theorem eq_zero_of_all_character_sums_eq_zero {G : Type} [AddCommGroup G] [Fintype G] (f : G → ℂ)
    (h : ∀ ψ : AddChar G ℂ, ∑ g ∈ (Finset.univ : Finset G), f g * ψ g = 0) : f = 0 := by
  funext a
  change f a = (0 : ℂ)
  have hsum :
    ∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)),
        (∑ g ∈ (Finset.univ : Finset G), f g * ψ g) * ψ (-a) =
      0 := by
    apply Finset.sum_eq_zero
    intro ψ hψ
    rw [h ψ]
    simp only [zero_mul]
  have hrec := fourier_reconstruction f a
  rw [hsum] at hrec
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp hrec).resolve_left hcard

/--
Inputs: an element of the complex additive group algebra of a finite
commutative group, whose evaluation at every complex additive character is
zero.

Claim: the group-algebra element is zero.

Content: the algebra evaluation is the Fourier sum of its coefficient
function. Thus the preceding coefficient-vanishing theorem gives injectivity
of the family of character evaluations.

Proof: rewrite each algebra evaluation as a finite sum of coefficients and
apply `eq_zero_of_all_character_sums_eq_zero`.

Role: this is the group-algebra form of coefficient detection used in the
finite abelian-group argument.
-/
theorem eq_zero_of_all_character_evaluations_eq_zero {G : Type} [AddCommGroup G] [Finite G]
    (x : AddMonoidAlgebra ℂ G)
    (h : ∀ ψ : AddChar G ℂ, AddMonoidAlgebra.lift ℂ ℂ G ψ.toMonoidHom x = 0) : x = 0 := by
  classical
  let fintypeG : Fintype G := Fintype.ofFinite G
  apply AddMonoidAlgebra.coeff_injective
  ext a
  change x.coeff a = 0
  have hfun : (fun g : G => x.coeff g) = 0 :=
    @eq_zero_of_all_character_sums_eq_zero G inferInstance fintypeG (fun g : G => x.coeff g)
      (by
        intro ψ
        rw [← @addMonoidAlgebra_lift_eq_character_sum G inferInstance fintypeG x ψ]
        exact h ψ)
  exact congrFun hfun a

/--
Inputs: a finite abelian group, an indexed sequence with no nonempty
zero-product subset, and nonzero complex coefficients.

Claim: some complex additive character evaluates `characterKillingProduct` to
a nonzero value.

Content: if every character evaluation vanished, Fourier inversion would make
the group-algebra element zero, contradicting its nonzero identity coefficient.

Proof: derive the coefficient from the empty subset and use that a finite
product of nonzero complex numbers is nonzero.

Role: this is the Fourier contradiction interface for the subset-product
theorem.
-/
theorem exists_character_eval_ne_zero_of_no_nonempty {G : Type} [AddCommGroup G] [Finite G]
    (S : Finset ℕ) (g : ℕ → G) (a : ℕ → ℂ) (hNo : ∀ t ∈ S.powerset, (∑ i ∈ t, g i) = 0 → t = ∅)
    (ha : ∀ i ∈ S, a i ≠ 0) :
    ∃ ψ : AddChar G ℂ,
      AddMonoidAlgebra.lift ℂ ℂ G ψ.toMonoidHom (characterKillingProduct S g a) ≠ 0 := by
  classical
  apply not_forall.mp
  intro hall
  have hz := eq_zero_of_all_character_evaluations_eq_zero (characterKillingProduct S g a) hall
  have hc := congrArg (fun x : AddMonoidAlgebra ℂ G => x.coeff 0) hz
  rw [coeff_zero_characterKillingProduct_eq_prod_of_no_nonempty S g a hNo] at hc
  simp only [AddMonoidAlgebra.coeff_zero] at hc
  have hprod : ∏ i ∈ S, a i ≠ 0 := Finset.prod_ne_zero_iff.mpr ha
  exact hprod hc

end PseudoPrime.Combinatorics.Additive.FiniteAbelianZeroSum
