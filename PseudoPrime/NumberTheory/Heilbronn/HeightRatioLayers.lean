/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeightPairCounting

/-! # Canonical-height layers of actual Heilbronn ratios -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For H<p, a raw height-H Heilbronn residue remains a bounded residue at
any upper bound T for its canonical height. The raw denominator is a unit;
cancel its reduction factor before using the canonical numerator and denominator.
This makes the product-growth bound available separately at each height layer. -/
theorem boundedRationalResidue_of_canonical_height {p H T : ℕ} [Fact p.Prime] {q : ℚ}
    {u : ZMod (p ^ 2)} (hHp : H < p) (hq : boundedRationalResidue (p ^ 2) H q u)
    (hT : rationalPairHeight q ≤ T) : boundedRationalResidue (p ^ 2) T q u := by
  have hpos := (boundedRationalResidue_canonical_height hq).1
  obtain ⟨a, b, _, _, hb, hbH, he, hu⟩ := hq
  have hbu : IsUnit (b : ZMod (p ^ 2)) := by
    simpa only [Int.cast_natCast] using
      intCast_isUnit_of_natAbs_lt (p := p) (b : ℤ) (Int.natCast_ne_zero.mpr (ne_of_gt hb))
        (show (b : ℤ).natAbs < p by simpa only [Int.natAbs_natCast] using hbH.trans_lt hHp)
  have hr :=
    rationalResidue_divInt (a : ℤ) (b : ℤ) (Int.natCast_ne_zero.mpr (ne_of_gt hb))
      (show IsUnit ((b : ℤ) : ZMod (p ^ 2)) by simpa only [Int.cast_natCast] using hbu)
      (show ((b : ℤ) : ZMod (p ^ 2)) * u = ((a : ℤ) : ZMod (p ^ 2)) by
        simpa only [Int.cast_natCast] using hu)
  have hrep : q = Rat.divInt a b := by
    rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast]
    exact he
  rw [← hrep] at hr
  refine
    ⟨q.num.natAbs, q.den, Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hpos)),
      (le_max_left _ _).trans hT, Rat.den_pos _, (le_max_right _ _).trans hT,
      positive_rat_nat_fraction hpos, ?_⟩
  have hn : (q.num.natAbs : ℤ) = q.num := by
    rw [Int.natCast_natAbs, abs_of_pos (Rat.num_pos.mpr hpos)]
  change (q.den : ZMod (p ^ 2)) * u = (q.num : ZMod (p ^ 2)) at hr
  rw [← hn, Int.cast_natCast] at hr
  exact hr

/-- Distinct actual positive ratios from the H-square whose canonical height
is at most T. The original H is retained only to identify the congruence family;
product-set growth is applied at the smaller layer height T. -/
noncomputable def heightRestrictedRatioSet (p H T : ℕ) [Fact p.Prime] : Finset ℚ := by
  classical exact (positiveRatioSet p H).filter (fun q ↦ rationalPairHeight q ≤ T)

/-- Every member of a restricted ratio layer has an actual Heilbronn subgroup
representative at height T, provided H<p. Normalize the existing raw residue
before applying the canonical-height cutoff. -/
theorem heightRestrictedRatioSet_has_residues {p H T : ℕ} [Fact p.Prime] (hHp : H < p) :
    ∀ q ∈ heightRestrictedRatioSet p H T,
      ∃ u : heilbronnSubgroup p, boundedRationalResidue (p ^ 2) T q (u.val : ZMod (p ^ 2)) := by
  classical
  intro q hq
  have hm := Finset.mem_filter.mp hq
  obtain ⟨u, hu⟩ := positiveRatioSet_has_residues q hm.1
  exact ⟨u, boundedRationalResidue_of_canonical_height hHp hu hm.2⟩

/-- For positive layer height T and positive product parameters m,n, the
restricted ratio count satisfies the same growth inequality at height T,
even if its original pairs have the larger bound H. Normalize each subgroup
residue and apply product growth and modular injectivity at T^(2m)<p². -/
theorem heightRestrictedRatioSet_power_growth_bound {p H T m n : ℕ} [Fact p.Prime] (hHp : H < p)
    (hT : 0 < T) (hm : 0 < m) (hn : 0 < n) (hmod : T ^ (2 * m) < p ^ 2) :
    (heightRestrictedRatioSet p H T).card ^ (n * m) ≤
      quotientPowerConstant (T ^ (2 * m)) ^ (n ^ 2 * (m - 1)) * T ^ ((m - 1) * m) *
        (p - 1) ^ n := by
  have hr := heightRestrictedRatioSet_has_residues (T := T) hHp
  have hg :=
    rationalProductSet_power_growth_explicit hT hm hn
      (fun q hq ↦ boundedRationalResidue_canonical_height (Exists.choose_spec (hr q hq)))
  exact
    hg.trans
      (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (card_rationalProductSet_le_heilbronn _ hmod hr) n))

/-- A single layer J<height(q)<=T contributes at most the number of restricted
ratios times floor(H/(J+1)). Its ratio count can therefore use product growth
at T rather than at the original pair bound H. All multiplicities are retained. -/
theorem height_layer_weight_sum_le (p H J T : ℕ) [Fact p.Prime] :
    ∑
        q ∈
          (positiveRatioSet p H).filter
            (fun q ↦ J < rationalPairHeight q ∧ rationalPairHeight q ≤ T),
        H / rationalPairHeight q ≤
      (heightRestrictedRatioSet p H T).card * (H / (J + 1)) := by
  classical
  let S :=
    (positiveRatioSet p H).filter (fun q ↦ J < rationalPairHeight q ∧ rationalPairHeight q ≤ T)
  have hw : (∑ q ∈ S, H / rationalPairHeight q) ≤ S.card * (H / (J + 1)) := by
    calc
      _ ≤ ∑ _q ∈ S, H / (J + 1) := by
        apply Finset.sum_le_sum
        intro q hq
        exact Nat.div_le_div_left (Finset.mem_filter.mp hq).2.1 (Nat.succ_pos J)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  apply hw.trans
  apply Nat.mul_le_mul_right
  apply Finset.card_le_card
  intro q hq
  have h := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨h.1, h.2.2⟩

/-- Any finite collection of height intervals covering the ratios above J
controls their weighted sum by the sum of the individual layer bounds.
Intervals may overlap; nonnegative weights make exact disjointness unnecessary.
This supports both a few chosen degrees and the finite 36-layer construction. -/
theorem height_tail_weight_sum_le_layers {ι : Type*} (I : Finset ι) (lower upper : ι → ℕ)
    {p H J : ℕ} [Fact p.Prime]
    (hcover :
      ∀ q ∈ positiveRatioSet p H,
        J < rationalPairHeight q →
          ∃ i ∈ I, lower i < rationalPairHeight q ∧ rationalPairHeight q ≤ upper i) :
    (∑ q ∈ (positiveRatioSet p H).filter (fun q ↦ J < rationalPairHeight q),
        H / rationalPairHeight q) ≤
      ∑ i ∈ I, (heightRestrictedRatioSet p H (upper i)).card * (H / (lower i + 1)) := by
  classical
  let R := positiveRatioSet p H
  let W : ℚ → ι → ℕ := fun q i ↦
    if lower i < rationalPairHeight q ∧ rationalPairHeight q ≤ upper i then H / rationalPairHeight q
    else 0
  have hc :
    ∀ q ∈ R.filter (fun q ↦ J < rationalPairHeight q),
      H / rationalPairHeight q ≤ ∑ i ∈ I, W q i := by
    intro q hq
    have h := Finset.mem_filter.mp hq
    obtain ⟨i, hi, he⟩ := hcover q h.1 h.2
    have hs := Finset.single_le_sum (s := I) (f := W q) (fun j hj ↦ Nat.zero_le _) hi
    simpa only [W, ite_eq_left he] using hs
  have hsum := Finset.sum_le_sum hc
  have hsub :=
    Finset.sum_le_sum_of_subset (f := fun q ↦ ∑ i ∈ I, W q i)
      (Finset.filter_subset (fun q ↦ J < rationalPairHeight q) R)
  apply (hsum.trans hsub).trans
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  change
    (∑ q ∈ R,
        if lower i < rationalPairHeight q ∧ rationalPairHeight q ≤ upper i then
          H / rationalPairHeight q
        else 0) ≤
      _
  rw [← Finset.sum_filter]
  exact height_layer_weight_sum_le p H (lower i) (upper i)

/-- A finite height cover yields an unconditional bound for the actual signed
Heilbronn congruence count when p is odd and H<p. Combine the small-height
divisor term and the layer-specific restricted ratio counts; no counting
estimate is assumed as an extra hypothesis. -/
theorem boundedCongruenceCount_le_height_layers {ι : Type*} (I : Finset ι) (lower upper : ι → ℕ)
    {p H J : ℕ} [Fact p.Prime] (hodd : Odd p) (hHp : H < p)
    (hcover :
      ∀ q ∈ positiveRatioSet p H,
        J < rationalPairHeight q →
          ∃ i ∈ I, lower i < rationalPairHeight q ∧ rationalPairHeight q ≤ upper i) :
    boundedCongruenceCount p H ≤
      4 *
        (J * H * maxDivisorCount H +
          ∑ i ∈ I, (heightRestrictedRatioSet p H (upper i)).card * (H / (lower i + 1))) := by
  exact
    (boundedCongruenceCount_le_height_split hodd hHp).trans
      (Nat.mul_le_mul_left 4
        (Nat.add_le_add_left (height_tail_weight_sum_le_layers I lower upper hcover) _))

end PseudoPrime.NumberTheory.Heilbronn
