/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalProductGrowth

/-! # Explicit growth bounds for positive Heilbronn ratios -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For positive naturals a,b bounded by H, their rational quotient is positive and its
canonical numerator and denominator are at most H. Extract the common normalization factor
and use its nonzero absolute value to bound both canonical components. -/
theorem positive_fraction_canonical_height {a b H : ℕ} (ha : 0 < a) (hb : 0 < b) (haH : a ≤ H)
    (hbH : b ≤ H) : 0 < (a : ℚ) / b ∧ ((a : ℚ) / b).num.natAbs ≤ H ∧ ((a : ℚ) / b).den ≤ H := by
  let q : ℚ := (a : ℚ) / b
  have he : q = Rat.divInt a b := by rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast]
  obtain ⟨c, hnum, hden⟩ := Rat.num_den_mk (Int.natCast_ne_zero.mpr (ne_of_gt hb)) he
  have hc : c ≠ 0 := by
    intro hc
    rw [hc, zero_mul] at hden
    exact (Int.natCast_ne_zero.mpr (ne_of_gt hb)) hden
  have hcn : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  have hn := congrArg Int.natAbs hnum
  have hd := congrArg Int.natAbs hden
  simp only [Int.natAbs_natCast, Int.natAbs_mul] at hn hd
  have hnq := (Nat.le_mul_of_pos_left q.num.natAbs hcn).trans_eq hn.symm
  have hdq := (Nat.le_mul_of_pos_left q.den hcn).trans_eq hd.symm
  exact ⟨div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb), hnq.trans haH, hdq.trans hbH⟩

/-- A bounded rational residue at height H is a positive rational of canonical height at most H.
Discard the modular equality and reduce its raw positive numerator-denominator representation. -/
theorem boundedRationalResidue_canonical_height {m H : ℕ} {q : ℚ} {u : ZMod m}
    (hq : boundedRationalResidue m H q u) : 0 < q ∧ q.num.natAbs ≤ H ∧ q.den ≤ H := by
  obtain ⟨a, b, ha, haH, hb, hbH, rfl, he⟩ := hq
  exact positive_fraction_canonical_height ha hb haH hbH

/-- Every actual positive bounded Heilbronn ratio is positive with canonical height at most H.
Use its already constructed subgroup residue representation and the raw-height reduction lemma. -/
theorem positiveRatioSet_canonical_height {p H : ℕ} [Fact p.Prime] :
    ∀ q ∈ positiveRatioSet p H, 0 < q ∧ q.num.natAbs ≤ H ∧ q.den ≤ H := by
  intro q hq
  obtain ⟨u, hu⟩ := positiveRatioSet_has_residues q hq
  exact boundedRationalResidue_canonical_height hu

/-- For prime p, positive H,m,n and H^(2m) less than p^2, bound the actual positive ratio count
raised to n*m by quotientPowerConstant(H^(2m))^(n^2*(m-1))*H^((m-1)*m)*(p-1)^n.
Combine proved rational product growth with the subgroup product-set cardinality upper bound.
No rational growth hypothesis is supplied; integer-pair multiplicities are not counted here. -/
theorem positive_ratio_power_growth_bound {p H m n : ℕ} [Fact p.Prime] (hH : 0 < H) (hm : 0 < m)
    (hn : 0 < n) (hmod : H ^ (2 * m) < p ^ 2) :
    (positiveRatioSet p H).card ^ (n * m) ≤
      quotientPowerConstant (H ^ (2 * m)) ^ (n ^ 2 * (m - 1)) * H ^ ((m - 1) * m) *
        (p - 1) ^ n := by
  have h :=
    rationalProductSet_power_growth_explicit hH hm hn (positiveRatioSet_canonical_height (p := p))
  exact
    h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (card_positive_ratio_products_le hmod) n))

/-- Under the same positive-height and subgroup-injectivity conditions, extract a real root to
bound the m-th power of the positive ratio count by the explicit divisor/logarithmic loss,
the height root H^((m-1)*m/n), and p-1. This removes the former growth premise for distinct
positive rational ratios, while leaving integer-pair multiplicity and signs to a separate count. -/
theorem positive_ratio_root_growth_bound {p H m n : ℕ} [Fact p.Prime] (hH : 0 < H) (hm : 0 < m)
    (hn : 0 < n) (hmod : H ^ (2 * m) < p ^ 2) :
    ((positiveRatioSet p H).card : ℝ) ^ m ≤
      (quotientPowerConstant (H ^ (2 * m)) : ℝ) ^ (n * (m - 1)) *
        ((H ^ ((m - 1) * m) : ℕ) : ℝ) ^ ((n : ℝ)⁻¹) *
        (p - 1 : ℕ) := by
  have h := positive_ratio_power_growth_bound hH hm hn hmod
  have hp :
    ((positiveRatioSet p H).card ^ m) ^ n ≤
      (quotientPowerConstant (H ^ (2 * m)) ^ (m - 1)) ^ (n ^ 2) * H ^ ((m - 1) * m) *
        (p - 1) ^ n := by
    simpa only [← pow_mul, Nat.mul_comm] using h
  have hr := root_of_natural_power_bound hn hp
  simpa only [Nat.cast_pow, ← pow_mul, Nat.mul_comm] using hr

end PseudoPrime.NumberTheory.Heilbronn
