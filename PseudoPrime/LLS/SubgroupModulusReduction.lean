/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TheoreticalPrimeBounds
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-! # Transporting subgroup prime bounds through modulus reduction

A reduction with unchanged prime support preserves the eligible prime set
when its kernel lies in the subgroup. The gamma bound then uses the smaller
modulus. Power lifting is an explicit premise, not an additional axiom.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a cyclic unit group, divisibility of the reduced totient by the subgroup
index implies that the reduction kernel lies in the subgroup. Surjectivity
identifies the kernel index with the reduced totient; cyclic subgroup inclusion
is equivalent to reversed index divisibility. This removes power-lifting
premises in the cyclic case, including odd prime-power moduli. -/
theorem reduction_kernel_le_subgroup_of_cyclic {q m : ℕ} [NeZero q] [NeZero m] [IsCyclic (ZMod q)ˣ]
    (hm : m ∣ q) (H : Subgroup (ZMod q)ˣ) (hh : H.index ∣ Nat.totient m) :
    (ZMod.unitsMap hm).ker ≤ H := by
  apply IsCyclic.subgroup_le_iff_index_dvd.mpr
  rw [Subgroup.index_ker,
    (ZMod.unitsMap hm).range_eq_top_of_surjective (ZMod.unitsMap_surjective hm), Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  exact hh

/-- If every element of a reduction kernel is an `h`th power, then the kernel
lies in every subgroup of index `h`. Powers of the subgroup index belong to the
subgroup in the abelian unit group. This isolates the local power-lifting
condition needed to descend a subgroup to a smaller modulus. -/
theorem reduction_kernel_le_subgroup {q m h : ℕ} (hm : m ∣ q) (H : Subgroup (ZMod q)ˣ)
    (hH : H.index = h) (hk : ∀ u ∈ (ZMod.unitsMap hm).ker, ∃ v : (ZMod q)ˣ, v ^ h = u) :
    (ZMod.unitsMap hm).ker ≤ H := by
  intro u hu
  obtain ⟨v, hv⟩ := hk u hu
  rw [← hv, ← hH]
  exact H.pow_index_mem v

/-- For a unit residue and a divisor modulus whose reduction kernel lies in
`H`, residue membership is equivalent to membership in the image subgroup.
Coercions commute with reduction, and the preimage of the image is `H`.
This transports subgroup membership without choosing new prime witnesses. -/
theorem residueInSubgroup_reduction_iff {q m n : ℕ} (hm : m ∣ q) (H : Subgroup (ZMod q)ˣ)
    (hk : (ZMod.unitsMap hm).ker ≤ H) (hn : IsUnit (n : ZMod q)) :
    residueInSubgroup q H n ↔ residueInSubgroup m (H.map (ZMod.unitsMap hm)) n := by
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨ZMod.unitsMap hm u, Subgroup.mem_map.mpr ⟨u, hu, rfl⟩, ?_⟩
    rw [ZMod.unitsMap_val, he, ZMod.cast_natCast hm]
  · rintro ⟨w, hw, he⟩
    have hu : ZMod.unitsMap hm hn.unit = w := by
      apply Units.ext
      rw [ZMod.unitsMap_val, hn.unit_spec, ZMod.cast_natCast hm, he]
    have hv : hn.unit ∈ H := by
      rw [← Subgroup.comap_map_eq_self hk, Subgroup.mem_comap, hu]
      exact hw
    exact ⟨hn.unit, hv, hn.unit_spec⟩

/-- A divisor modulus with the same prime support preserves the entire set
of eligible primes outside a subgroup containing the reduction kernel.
Prime support preserves the excluded divisors, and unit membership descends.
Consequently the least outside prime is unchanged under this reduction. -/
theorem primesOutside_reduction {q m : ℕ} (hm : m ∣ q) (H : Subgroup (ZMod q)ˣ)
    (hk : (ZMod.unitsMap hm).ker ≤ H) (hs : ∀ p : ℕ, p.Prime → (p ∣ q ↔ p ∣ m)) :
    primesOutside q H = primesOutside m (H.map (ZMod.unitsMap hm)) := by
  ext p
  constructor
  · rintro ⟨hp, hq, hH⟩
    have hn : IsUnit (p : ZMod q) :=
      (ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hq)
    exact
      ⟨hp, fun hm' ↦ hq ((hs p hp).mpr hm'), fun hmem ↦
        hH ((residueInSubgroup_reduction_iff hm H hk hn).mpr hmem)⟩
  · rintro ⟨hp, hm', hH⟩
    have hq : ¬p ∣ q := fun hq' ↦ hm' ((hs p hp).mp hq')
    have hn : IsUnit (p : ZMod q) :=
      (ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hq)
    exact ⟨hp, hq, fun hmem ↦ hH ((residueInSubgroup_reduction_iff hm H hk hn).mp hmem)⟩

/-- Under GRH, a divisor modulus with the same prime support and reduction
kernel contained in the subgroup gives a least-prime bound in terms of the
smaller modulus: `659/1000 * (log m)^2`, once `m` exceeds a fixed threshold.
Surjectivity preserves the subgroup index, and equality of eligible prime
sets transports the gamma bound. Small reduced moduli require a separate
finite-existence argument; this theorem does not assume that argument. -/
theorem gamma_prime_bound_659_of_reduction
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 4 ≤ h) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q m : ℕ) [NeZero q] [NeZero m],
          Q ≤ m →
            ∀ hm : m ∣ q,
              ∀ H : Subgroup (ZMod q)ˣ,
                H.index = h →
                  (ZMod.unitsMap hm).ker ≤ H →
                  (∀ p : ℕ, p.Prime → (p ∣ q ↔ p ∣ m)) →
                  ∃ p : ℕ,
                    IsLeast (primesOutside q H) p ∧ (p : ℝ) ≤ (659 / 1000) * (Real.log m) ^ 2 := by
  obtain ⟨Q, hQ2, hQ⟩ := gamma_prime_bound_659 hg h hh
  refine ⟨Q, hQ2, ?_⟩
  intro q m _ _ hmQ hm H hH hk hs
  have hi : (H.map (ZMod.unitsMap hm)).index = h :=
    (H.index_map_eq (ZMod.unitsMap_surjective hm) hk).trans hH
  obtain ⟨p, hp, hb⟩ := hQ m hmQ (H.map (ZMod.unitsMap hm)) hi
  rw [← primesOutside_reduction hm H hk hs] at hp
  exact ⟨p, hp, hb⟩

/-- Under GRH, cyclic unit groups admit the reduced-modulus gamma bound whenever
the divisor modulus has the same prime support and its totient is divisible by
the fixed subgroup index. The cyclic inclusion criterion discharges the kernel
premise of the reduction theorem. This gives a directly checkable arithmetic
condition for the smaller logarithmic bound. -/
theorem gamma_prime_bound_659_of_cyclic_reduction
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 4 ≤ h) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q m : ℕ) [NeZero q] [NeZero m] [IsCyclic (ZMod q)ˣ],
          Q ≤ m →
            m ∣ q →
            ∀ H : Subgroup (ZMod q)ˣ,
              H.index = h →
                h ∣ Nat.totient m →
                (∀ p : ℕ, p.Prime → (p ∣ q ↔ p ∣ m)) →
                ∃ p : ℕ,
                  IsLeast (primesOutside q H) p ∧ (p : ℝ) ≤ (659 / 1000) * (Real.log m) ^ 2 := by
  obtain ⟨Q, hQ2, hQ⟩ := gamma_prime_bound_659_of_reduction hg h hh
  refine ⟨Q, hQ2, ?_⟩
  intro q m _ _ _ hmQ hm H hH hdiv hs
  exact hQ q m hmQ hm H hH (reduction_kernel_le_subgroup_of_cyclic hm H (hH.symm ▸ hdiv)) hs

end PseudoPrime.LLS.PaperStatements
