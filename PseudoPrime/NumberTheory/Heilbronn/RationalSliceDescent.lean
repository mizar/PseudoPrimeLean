/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalDivisorIncidence

/-! # Height descent of rational divisor slices -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For a positive reduced rational divisible by r in its numerator and s in its denominator,
scaling by s/r gives the fraction of the corresponding natural cofactors. Cancel only the
external rational factors, retaining the original canonical numerator and denominator. -/
theorem scaled_slice_fraction {q : ℚ} {r s : ℕ} (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (hrq : r ∣ q.num.natAbs) (hsq : s ∣ q.den) :
    (s : ℚ) / r * q = (q.num.natAbs / r : ℕ) / (q.den / s : ℕ) := by
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hr)
  have hs0 : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hs)
  calc
    _ = (s : ℚ) / r * ((q.num.natAbs : ℚ) / q.den) :=
      congrArg (fun t : ℚ ↦ (s : ℚ) / r * t) (positive_rat_nat_fraction hq)
    _ = _ := by
      rw [Nat.cast_div hrq hr0, Nat.cast_div hsq hs0]
      field_simp [hr0, hs0]

/-- For positive r,s dividing the canonical numerator and denominator, identify exactly the
canonical numerator and denominator after scaling by s/r. Cofactors inherit coprimality. -/
theorem scaled_slice_num_den {q : ℚ} {r s : ℕ} (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (hrq : r ∣ q.num.natAbs) (hsq : s ∣ q.den) :
    (((s : ℚ) / r * q).num.natAbs = q.num.natAbs / r) ∧ (((s : ℚ) / r * q).den = q.den / s) := by
  rw [scaled_slice_fraction hq hr hs hrq hsq]
  exact
    num_den_of_coprime_nat (Nat.div_pos (Nat.le_of_dvd q.den_pos hsq) hs)
      (Nat.Coprime.of_dvd (Nat.div_dvd_of_dvd hrq) (Nat.div_dvd_of_dvd hsq) q.reduced)

/-- For a rational in a bounded divisor slice, scaling by s/r gives a positive rational with
numerator at most Q/r and denominator at most D/s. This provides the induction height descent. -/
theorem scaled_slice_height {A : Finset ℚ} {Q D r s : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) (hr : 0 < r) (hs : 0 < s) {q : ℚ}
    (hq : q ∈ divisorSlice A r s) :
    0 < (s : ℚ) / r * q ∧ ((s : ℚ) / r * q).num.natAbs ≤ Q / r ∧ ((s : ℚ) / r * q).den ≤ D / s := by
  classical
  have hm := Finset.mem_filter.mp hq
  have ha := hA q hm.1
  have he := scaled_slice_num_den ha.1 hr hs hm.2.1 hm.2.2
  exact
    ⟨mul_pos (div_pos (Nat.cast_pos.mpr hs) (Nat.cast_pos.mpr hr)) ha.1,
      he.1 ▸ Nat.div_le_div_right ha.2.1, he.2 ▸ Nat.div_le_div_right ha.2.2⟩

/-- Multiplication by a nonzero rational preserves the cardinality of any finite rational family.
Use injectivity of multiplication; this transfers slice cardinalities without a loss. -/
theorem card_scaled_family (A : Finset ℚ) {c : ℚ} (hc : c ≠ 0) :
    (A.image (fun q ↦ c * q)).card = A.card :=
  Finset.card_image_of_injective A (mul_right_injective₀ hc)

/-- Scaling two rational families by the same nonzero rational preserves their quotient set.
Cancel the common scalar in each represented quotient, in both directions. -/
theorem scaled_quotientSet {A B : Finset ℚ} {c : ℚ} (hc : c ≠ 0) :
    rationalQuotientSet (A.image (fun q ↦ c * q)) (B.image (fun q ↦ c * q)) =
      rationalQuotientSet A B := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨ab, hab, he⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp (Finset.mem_product.mp hab).1
    obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp (Finset.mem_product.mp hab).2
    apply Finset.mem_image.mpr
    refine ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩
    change ab.1 / ab.2 = z at he
    rw [← hea, ← heb, mul_div_mul_left a b hc] at he
    exact he
  · intro hz
    obtain ⟨ab, hab, he⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    refine
      ⟨(c * ab.1, c * ab.2),
        Finset.mem_product.mpr
          ⟨Finset.mem_image.mpr ⟨ab.1, (Finset.mem_product.mp hab).1, rfl⟩,
            Finset.mem_image.mpr ⟨ab.2, (Finset.mem_product.mp hab).2, rfl⟩⟩,
        ?_⟩
    exact (mul_div_mul_left ab.1 ab.2 hc).trans he

/-- For positive r,s, the quotient set of the two scaled divisor slices is contained in the
original quotient set. Cancel the scalar and use membership in the two original families. -/
theorem scaled_slice_quotientSet_subset (A B : Finset ℚ) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    rationalQuotientSet ((divisorSlice A r s).image (fun q ↦ (s : ℚ) / r * q))
        ((divisorSlice B r s).image (fun q ↦ (s : ℚ) / r * q)) ⊆
      rationalQuotientSet A B := by
  classical
  rw [scaled_quotientSet (ne_of_gt (div_pos (Nat.cast_pos.mpr hs) (Nat.cast_pos.mpr hr)))]
  intro z hz
  obtain ⟨ab, hab, he⟩ := Finset.mem_image.mp hz
  exact
    Finset.mem_image.mpr
      ⟨ab,
        Finset.mem_product.mpr
          ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hab).1).1,
            (Finset.mem_filter.mp (Finset.mem_product.mp hab).2).1⟩,
        he⟩

/-- Every element of a scaled divisor slice has positive value and canonical heights at most
Q/r and D/s. Unpack image membership and apply the pointwise height descent. -/
theorem scaled_slice_family_height {A : Finset ℚ} {Q D r s : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) (hr : 0 < r) (hs : 0 < s) :
    ∀ q ∈ (divisorSlice A r s).image (fun q ↦ (s : ℚ) / r * q),
      0 < q ∧ q.num.natAbs ≤ Q / r ∧ q.den ≤ D / s := by
  classical
  intro q hq
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
  exact scaled_slice_height hA hr hs ht

/-- For positive bounded families and positive divisor indices, a quotient bound valid at the
smaller heights Q/r,D/s bounds the original slice product with the original quotient cardinality.
Scale both slices, preserve their cardinalities, and use quotient-set containment.
This transfers the recursive hypothesis to the large-slice branch without an additional loss. -/
theorem slice_product_le_of_recursive_bound {A B : Finset ℚ} {Q D r s K : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) (hr : 0 < r) (hs : 0 < s)
    (hrec :
      ∀ A' B' : Finset ℚ,
        (∀ q ∈ A', 0 < q ∧ q.num.natAbs ≤ Q / r ∧ q.den ≤ D / s) →
          (∀ q ∈ B', 0 < q ∧ q.num.natAbs ≤ Q / r ∧ q.den ≤ D / s) →
          A'.card * B'.card ≤ K * (rationalQuotientSet A' B').card) :
    (divisorSlice A r s).card * (divisorSlice B r s).card ≤ K * (rationalQuotientSet A B).card := by
  classical
  have hc : (s : ℚ) / r ≠ 0 := ne_of_gt (div_pos (Nat.cast_pos.mpr hs) (Nat.cast_pos.mpr hr))
  have ht :=
    hrec ((divisorSlice A r s).image (fun q ↦ (s : ℚ) / r * q))
      ((divisorSlice B r s).image (fun q ↦ (s : ℚ) / r * q)) (scaled_slice_family_height hA hr hs)
      (scaled_slice_family_height hB hr hs)
  rw [card_scaled_family _ hc, card_scaled_family _ hc] at ht
  exact
    ht.trans
      (Nat.mul_le_mul_left K (Finset.card_le_card (scaled_slice_quotientSet_subset A B hr hs)))

/-- For positive divisors r,s, the product of the two floor-reduced heights is at most
floor(Q*D/(r*s)). Multiply by r*s and use the two floor-division inequalities. -/
theorem slice_height_product_le {Q D r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (Q / r) * (D / s) ≤ (Q * D) / (r * s) := by
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos hr hs)).mpr
  have h := Nat.mul_le_mul (Nat.div_mul_le_self Q r) (Nat.div_mul_le_self D s)
  nlinarith only [h]

/-- The maximum divisor count up to U is at most that up to V whenever U is at most V.
Use inclusion of the finite indexing ranges; no divisor-count monotonicity is assumed. -/
theorem maxDivisorCount_mono {U V : ℕ} (hUV : U ≤ V) : maxDivisorCount U ≤ maxDivisorCount V :=
  Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hUV 1))

/-- The divisor-count maximum at the product of reduced heights is bounded by the original
maximum. Floor division decreases each height, including zero-divisor conventions. -/
theorem slice_maxDivisorCount_le (Q D r s : ℕ) :
    maxDivisorCount ((Q / r) * (D / s)) ≤ maxDivisorCount (Q * D) :=
  maxDivisorCount_mono (Nat.mul_le_mul (Nat.div_le_self Q r) (Nat.div_le_self D s))

end PseudoPrime.NumberTheory.Heilbronn
