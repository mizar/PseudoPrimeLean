/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelBounds
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Subgroup orthogonality for smoothed Mangoldt sums

The annihilator of a subgroup has cardinality equal to its index. Summing its
characters selects exactly the unit residues in the subgroup. These identities
provide the arithmetic lower bound used in Section 6 of the LLS paper.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- For a unit natural residue, subgroup membership is membership of its canonical unit.
Injectivity of the coercion from units identifies any witness with that unit.
This converts the paper's residue predicate to the orthogonality hypotheses. -/
theorem residueInSubgroup_iff_unit_mem (H : Subgroup (ZMod q)ˣ) {n : ℕ} (hn : IsUnit (n : ZMod q)) :
    residueInSubgroup q H n ↔ hn.unit ∈ H := by
  constructor
  · rintro ⟨u, hu, he⟩
    have hunit : u = hn.unit := Units.val_injective (he.trans hn.unit_spec.symm)
    exact hunit ▸ hu
  · intro hu
    exact ⟨hn.unit, hu, hn.unit_spec⟩

omit [NeZero q] in
/-- A nonunit natural residue cannot belong to the image of `H`.
A witness would express it as the value of a unit. This handles primes dividing
the modulus when the character average is written as a subgroup indicator. -/
theorem not_residueInSubgroup_of_not_isUnit (H : Subgroup (ZMod q)ˣ) {n : ℕ}
    (hn : ¬IsUnit (n : ZMod q)) : ¬residueInSubgroup q H n := by
  rintro ⟨u, _, he⟩
  apply hn
  rw [← he]
  exact u.isUnit

/-- The annihilator sum vanishes at every nonunit natural residue.
Every Dirichlet character vanishes there. This removes nonunits from the
smoothed sum, independently of subgroup membership or GRH. -/
theorem sum_subgroupAnnihilator_eq_zero_of_not_isUnit (H : Subgroup (ZMod q)ˣ) {n : ℕ}
    (hn : ¬IsUnit (n : ZMod q)) :
    ∑ χ : NumberTheory.subgroupAnnihilator H, χ.val (n : ZMod q) = 0 := by
  exact Finset.sum_eq_zero (fun χ _ ↦ χ.val.map_nonunit hn)

/-- At a natural residue in `H`, the annihilator sum equals the subgroup index.
Use its witness unit and the unit orthogonality formula. This is the selected
part of the arithmetic sum in Proposition 6.1. -/
theorem sum_subgroupAnnihilator_eq_index_of_residue (H : Subgroup (ZMod q)ˣ) {n : ℕ}
    (hn : residueInSubgroup q H n) :
    ∑ χ : NumberTheory.subgroupAnnihilator H, χ.val (n : ZMod q) = (H.index : ℂ) := by
  obtain ⟨u, hu, he⟩ := hn
  rw [← he]
  exact NumberTheory.sum_subgroupAnnihilator_eq_index H hu

/-- At a natural residue outside the image of `H`, the annihilator sum is zero.
For a unit, use character cancellation; for a nonunit, every character vanishes.
This excludes all other arithmetic terms from the averaged sum. -/
theorem sum_subgroupAnnihilator_eq_zero_of_not_residue (H : Subgroup (ZMod q)ˣ) {n : ℕ}
    (hm : ¬residueInSubgroup q H n) :
    ∑ χ : NumberTheory.subgroupAnnihilator H, χ.val (n : ZMod q) = 0 := by
  by_cases hn : IsUnit (n : ZMod q)
  · rw [← hn.unit_spec]
    exact
      NumberTheory.sum_subgroupAnnihilator_eq_zero H
        (fun hu ↦ hm ((residueInSubgroup_iff_unit_mem H hn).mpr hu))
  · exact sum_subgroupAnnihilator_eq_zero_of_not_isUnit H hn

/-- The complete subgroup orthogonality relation at every natural index: the
annihilator sum is the index times the subgroup indicator. Combine the membership
and cancellation clauses. This identity is valid without GRH. -/
theorem sum_subgroupAnnihilator_eq_indicator (H : Subgroup (ZMod q)ˣ) (n : ℕ) :
    ∑ χ : NumberTheory.subgroupAnnihilator H, χ.val (n : ZMod q) =
      {m : ℕ | residueInSubgroup q H m}.indicator (fun _ ↦ (H.index : ℂ)) n := by
  classical
  by_cases hm : residueInSubgroup q H n
  · rw [Set.indicator_of_mem (s := {m : ℕ | residueInSubgroup q H m}) hm]
    exact sum_subgroupAnnihilator_eq_index_of_residue H hm
  · rw [Set.indicator_of_notMem (s := {m : ℕ | residueInSubgroup q H m}) hm]
    exact sum_subgroupAnnihilator_eq_zero_of_not_residue H hm

omit [NeZero q] in
/-- Subgroup membership of a natural residue is preserved by taking any natural power.
Raise its witness unit to the same power and use subgroup closure. This extends
prime membership to every prime-power term in the Mangoldt support. -/
theorem residueInSubgroup_pow (H : Subgroup (ZMod q)ˣ) {n : ℕ} (hn : residueInSubgroup q H n)
    (k : ℕ) : residueInSubgroup q H (n ^ k) := by
  obtain ⟨u, hu, he⟩ := hn
  refine ⟨u ^ k, H.pow_mem hu k, ?_⟩
  rw [Units.val_pow_eq_pow_val, he, Nat.cast_pow]

omit [NeZero q] in
/-- If all eligible primes up to `X` lie in `H`, every prime power up to `X`
coprime to the modulus also lies in `H`. Its prime base is no larger and remains
coprime to the modulus; subgroup closure then handles the exponent. This identifies
all nonzero principal-character Mangoldt terms below the cutoff. -/
theorem residueInSubgroup_of_primePow_of_noSmallPrimes (H : Subgroup (ZMod q)ˣ) {X : ℝ}
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) {n : ℕ}
    (hn : IsPrimePow n) (hc : n.Coprime q) (hbound : (n : ℝ) ≤ X) : residueInSubgroup q H n := by
  obtain ⟨p, k, hp, hk, he⟩ := (isPrimePow_nat_iff n).mp hn
  have hpc : p.Coprime q := Nat.Coprime.of_dvd_left (he ▸ dvd_pow_self p (Nat.ne_of_gt hk)) hc
  have hple : (p : ℝ) ≤ X := (Nat.cast_le.mpr ((Nat.le_pow hk).trans_eq he)).trans hbound
  exact he ▸ residueInSubgroup_pow H (hsmall p hp (hp.coprime_iff_not_dvd.mp hpc) hple) k

namespace MellinKernel

/-- At a residue in `H`, averaging the smoothed summand over its annihilator gives
the index times the principal-character summand. All relevant character values
are one, so the finite sum is constant. This selects the arithmetic main terms. -/
theorem sum_summand_of_residue (K : MellinKernel) (H : Subgroup (ZMod q)ˣ) (x : ℝ) {n : ℕ}
    (hm : residueInSubgroup q H n) :
    ∑ χ : NumberTheory.subgroupAnnihilator H, K.summand χ.val x n =
      (H.index : ℂ) * K.summand (1 : DirichletCharacter ℂ q) x n := by
  obtain ⟨u, hu, he⟩ := hm
  have hχ : ∀ χ : NumberTheory.subgroupAnnihilator H, χ.val (n : ZMod q) = 1 := fun χ ↦
    he ▸ (NumberTheory.mem_subgroupAnnihilator_iff H χ.val).mp χ.property u hu
  have h1 : (1 : DirichletCharacter ℂ q) (n : ZMod q) = 1 := he ▸ MulChar.one_apply_coe u
  simp only [summand, hχ, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    NumberTheory.card_subgroupAnnihilator]

/-- Outside the subgroup image, the averaged smoothed summand is zero.
Separate the zero index, then factor the common weight out of the character sum
and apply orthogonality. This excludes the other terms from the kernel average. -/
theorem sum_summand_of_not_residue (K : MellinKernel) (H : Subgroup (ZMod q)ˣ) (x : ℝ) {n : ℕ}
    (hm : ¬residueInSubgroup q H n) :
    ∑ χ : NumberTheory.subgroupAnnihilator H, K.summand χ.val x n = 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [summand, ite_true, Finset.sum_const_zero]
  · simp only [summand, ite_eq_right hn, ← Finset.sum_mul, ← Finset.mul_sum,
      sum_subgroupAnnihilator_eq_zero_of_not_residue H hm, mul_zero, zero_mul]

/-- The character average of each smoothed Mangoldt term is the subgroup indicator
times the index and principal-character term. Combine the selected and cancelled
cases. This pointwise identity is the basis for finite and infinite sum comparisons. -/
theorem sum_summand_eq_indicator (K : MellinKernel) (H : Subgroup (ZMod q)ˣ) (x : ℝ) (n : ℕ) :
    ∑ χ : NumberTheory.subgroupAnnihilator H, K.summand χ.val x n =
      (H.index : ℂ) *
        {m : ℕ | residueInSubgroup q H m}.indicator (K.summand (1 : DirichletCharacter ℂ q) x)
          n := by
  classical
  by_cases hm : residueInSubgroup q H n
  · rw [Set.indicator_of_mem (s := {m : ℕ | residueInSubgroup q H m}) hm]
    exact sum_summand_of_residue K H x hm
  · rw [Set.indicator_of_notMem (s := {m : ℕ | residueInSubgroup q H m}) hm, mul_zero]
    exact sum_summand_of_not_residue K H x hm

/-- For a positive cutoff, the sum of the actual smoothed series over the annihilator
is the index times the principal-character series restricted to the subgroup.
Absolute convergence permits exchanging the finite character sum with the infinite
arithmetic sum. This connects subgroup orthogonality to the series in Lemma 6.1. -/
theorem sum_tsum_eq_subgroup_indicator (K : MellinKernel) (H : Subgroup (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x) :
    ∑ χ : NumberTheory.subgroupAnnihilator H, ∑' n : ℕ, K.summand χ.val x n =
      (H.index : ℂ) *
        ∑' n : ℕ,
          {m : ℕ | residueInSubgroup q H m}.indicator (K.summand (1 : DirichletCharacter ℂ q) x)
            n := by
  have he :=
    Summable.tsum_finsetSum (s := Finset.univ) (f :=
      fun (χ : NumberTheory.subgroupAnnihilator H) n ↦ K.summand χ.val x n)
      (fun χ _ ↦ summable_summand K χ.val hx)
  rw [← he, tsum_congr (sum_summand_eq_indicator K H x), tsum_mul_left]

/-- At a positive cutoff, every principal-character smoothed term has nonnegative
real part. Unit residues have character value one and a nonnegative kernel transform;
nonunits and the zero index contribute zero. This permits discarding the tail. -/
theorem principal_summand_re_nonneg (K : MellinKernel) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    0 ≤ (K.summand (1 : DirichletCharacter ℂ q) x n).re := by
  by_cases hn : n = 0
  · subst n
    simp only [summand, ite_true, Complex.zero_re, le_refl]
  · by_cases hu : IsUnit (n : ZMod q)
    · have h1 : (1 : DirichletCharacter ℂ q) (n : ZMod q) = 1 :=
        hu.unit_spec ▸ MulChar.one_apply_coe hu.unit
      simp only [summand, ite_eq_right hn, h1, mul_one, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact
        mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
          (K.mellin_nonneg _ (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx))
    · simp only [summand, ite_eq_right hn, MulChar.map_nonunit _ hu, mul_zero, zero_mul,
        Complex.zero_re, le_refl]

/-- For a positive cutoff, the sum of real parts of the character series is the
index times the subgroup-restricted real principal series. Apply the real-part
map to the absolutely convergent orthogonality identity. This is the real form
needed to compare the two sides of Proposition 6.1. -/
theorem sum_re_tsum_eq_subgroup_indicator (K : MellinKernel) (H : Subgroup (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x) :
    ∑ χ : NumberTheory.subgroupAnnihilator H, (∑' n : ℕ, K.summand χ.val x n).re =
      (H.index : ℝ) *
        ∑' n : ℕ,
          {m : ℕ | residueInSubgroup q H m}.indicator
            (fun n ↦ (K.summand (1 : DirichletCharacter ℂ q) x n).re) n := by
  have hs :=
    (summable_summand K (1 : DirichletCharacter ℂ q) hx).indicator {m : ℕ | residueInSubgroup q H m}
  rw [← Complex.re_sum, sum_tsum_eq_subgroup_indicator K H hx, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero, Complex.re_tsum hs]
  apply congrArg (fun z : ℝ ↦ (H.index : ℝ) * z)
  apply tsum_congr
  intro n
  exact
    congrFun
      (Set.indicator_comp_of_zero (s := {m : ℕ | residueInSubgroup q H m}) (f :=
          K.summand (1 : DirichletCharacter ℂ q) x) (g := Complex.re) rfl).symm
      n

/-- The nonnegative subgroup-restricted finite principal sum is at most the real
annihilator average of the full series, for any finite set and positive cutoff.
Apply the nonnegative-tail inequality to the absolutely convergent indicator series.
This is the arithmetic lower bound before using the no-small-prime hypothesis. -/
theorem subgroup_indicator_sum_le_average (K : MellinKernel) (H : Subgroup (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x) (s : Finset ℕ) :
    (H.index : ℝ) *
        ∑ n ∈ s,
          {m : ℕ | residueInSubgroup q H m}.indicator
            (fun n ↦ (K.summand (1 : DirichletCharacter ℂ q) x n).re) n ≤
      ∑ χ : NumberTheory.subgroupAnnihilator H, (∑' n : ℕ, K.summand χ.val x n).re := by
  rw [sum_re_tsum_eq_subgroup_indicator K H hx]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg H.index)
  apply Summable.sum_le_tsum s
  · intro n _
    exact Set.indicator_nonneg (fun m _ ↦ principal_summand_re_nonneg K hx m) n
  · exact (Complex.reCLM.summable (summable_summand K (1 : DirichletCharacter ℂ q) hx)).indicator _

omit [NeZero q] in
/-- A smoothed character term vanishes outside the prime-power support of Mangoldt.
Use the exact support criterion and the defining weight. This removes arithmetic
indices that do not occur in the no-small-prime argument. -/
theorem summand_eq_zero_of_not_primePow (K : MellinKernel) (χ : DirichletCharacter ℂ q) (x : ℝ)
    {n : ℕ} (hn : ¬IsPrimePow n) : K.summand χ x n = 0 := by
  simp only [summand, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div,
    Complex.ofReal_zero, zero_mul, ite_self]

omit [NeZero q] in
/-- The principal-character smoothed term vanishes at every nonunit residue.
Use the character's vanishing on nonunits in the defining product. This excludes
prime powers sharing a factor with the modulus from the finite lower sum. -/
theorem principal_summand_eq_zero_of_not_isUnit (K : MellinKernel) (x : ℝ) {n : ℕ}
    (hn : ¬IsUnit (n : ZMod q)) : K.summand (1 : DirichletCharacter ℂ q) x n = 0 := by
  simp only [summand, MulChar.map_nonunit _ hn, mul_zero, zero_mul, ite_self]

omit [NeZero q] in
/-- Under the no-small-prime hypothesis, a principal term at an index at most `X`
outside the subgroup image is zero. Nonzero terms would be coprime prime powers,
whose prime bases and powers already lie in `H`. This removes the indicator below `X`. -/
theorem principal_summand_eq_zero_of_not_residue_of_noSmallPrimes (K : MellinKernel)
    (H : Subgroup (ZMod q)ˣ) (x : ℝ) {X : ℝ}
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) {n : ℕ}
    (hbound : (n : ℝ) ≤ X) (hm : ¬residueInSubgroup q H n) :
    K.summand (1 : DirichletCharacter ℂ q) x n = 0 := by
  by_cases hp : IsPrimePow n
  · by_cases hu : IsUnit (n : ZMod q)
    · exact
        False.elim
          (hm
            (residueInSubgroup_of_primePow_of_noSmallPrimes H hsmall hp
              ((ZMod.isUnit_iff_coprime n q).mp hu) hbound))
    · exact principal_summand_eq_zero_of_not_isUnit K x hu
  · exact summand_eq_zero_of_not_primePow K _ x hp

omit [NeZero q] in
/-- Under the no-small-prime hypothesis, the subgroup indicator does not change
any real principal term below `X`. Inside `H` it acts as the identity; outside,
the principal term is zero. This identifies the entire finite Mangoldt sum. -/
theorem subgroup_indicator_eq_principal_of_noSmallPrimes (K : MellinKernel) (H : Subgroup (ZMod q)ˣ)
    (x : ℝ) {X : ℝ} (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p)
    {n : ℕ} (hbound : (n : ℝ) ≤ X) :
    {m : ℕ | residueInSubgroup q H m}.indicator
        (fun n ↦ (K.summand (1 : DirichletCharacter ℂ q) x n).re) n =
      (K.summand (1 : DirichletCharacter ℂ q) x n).re := by
  by_cases hm : residueInSubgroup q H n
  · exact Set.indicator_of_mem (s := {m : ℕ | residueInSubgroup q H m}) hm _
  · rw [Set.indicator_of_notMem (s := {m : ℕ | residueInSubgroup q H m}) hm,
      principal_summand_eq_zero_of_not_residue_of_noSmallPrimes K H x hsmall hbound hm,
      Complex.zero_re]

/-- If every eligible prime up to `X` lies in `H`, its index times the principal
finite smoothed sum is at most the real annihilator average of the full series.
The prime-power support removes the indicator below `X`; positivity discards
the remaining tail. This supplies the arithmetic side of Proposition 6.1. -/
theorem principal_sum_le_average_of_noSmallPrimes (K : MellinKernel) (H : Subgroup (ZMod q)ˣ)
    {x X : ℝ} (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re ≤
      ∑ χ : NumberTheory.subgroupAnnihilator H, (∑' n : ℕ, K.summand χ.val x n).re := by
  have he :
    ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        {m : ℕ | residueInSubgroup q H m}.indicator
          (fun n ↦ (K.summand (1 : DirichletCharacter ℂ q) x n).re) n =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re := by
    apply Finset.sum_congr rfl
    intro n hn
    have hle : (n : ℝ) ≤ X :=
      (Nat.le_floor_iff' (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1)).mp
        (Finset.mem_Icc.mp hn).2
    exact subgroup_indicator_eq_principal_of_noSmallPrimes K H x hsmall hle
  rw [← he]
  exact subgroup_indicator_sum_le_average K H hx _

end MellinKernel

end PseudoPrime.LLS.PaperStatements
