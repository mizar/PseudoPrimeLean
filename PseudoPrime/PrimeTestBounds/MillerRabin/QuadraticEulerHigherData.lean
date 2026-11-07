/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaFiniteEulerIntervals

/-! # Separate higher-prime-power payload through 50000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Prime and exponent-minus-one pairs for the 84 higher powers through
50000. Exponent-one prime terms are deliberately excluded. The next check
compares with bounded exponent and prime-base enumeration. -/
def centerHigherPowers : List (ℕ × ℕ) :=
  [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1),
    (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1),
    (79, 1), (83, 1), (89, 1), (97, 1), (101, 1), (103, 1), (107, 1), (109, 1), (113, 1), (127, 1),
    (131, 1), (137, 1), (139, 1), (149, 1), (151, 1), (157, 1), (163, 1), (167, 1), (173, 1),
    (179, 1), (181, 1), (191, 1), (193, 1), (197, 1), (199, 1), (211, 1), (223, 1), (2, 2), (3, 2),
    (5, 2), (7, 2), (11, 2), (13, 2), (17, 2), (19, 2), (23, 2), (29, 2), (31, 2), (2, 3), (3, 3),
    (5, 3), (7, 3), (11, 3), (13, 3), (2, 4), (3, 4), (5, 4), (7, 4), (2, 5), (3, 5), (5, 5),
    (2, 6), (3, 6), (2, 7), (3, 7), (2, 8), (3, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13),
    (2, 14)]

/-- Bounded enumeration uses exponents two through fifteen and prime bases
below 224. Kernel evaluation checks the concrete higher-power payload.
A separate support theorem must justify these bounds for arbitrary inputs. -/
theorem centerHigherPowers_eq :
    centerHigherPowers =
      (List.range' 2 14).flatMap
        (fun e ↦
          (((List.range 224).filter (fun p ↦ @decide p.Prime (Nat.decidablePrime' p))).filter
                (fun p ↦ decide (p ^ e ≤ 50000))).map
            (fun p ↦ (p, e - 1))) := by
  decide +kernel

/-- A higher prime power through 50000 has prime base below 224 and
exponent below 16. Monotonicity of natural powers reduces violations to
224 squared or two to the sixteenth. These bounds justify the finite payload. -/
theorem higher_power_cutoff_bounds {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) (hpow : p ^ e ≤ 50000) :
    p < 224 ∧ e < 16 := by
  constructor
  · by_contra h
    have hl : 224 ≤ p := Nat.le_of_not_gt h
    have hb := (Nat.pow_le_pow_left hl 2).trans ((Nat.pow_le_pow_right hp.pos he).trans hpow)
    exact (by decide : ¬224 ^ 2 ≤ 50000) hb
  · by_contra h
    have hl : 16 ≤ e := Nat.le_of_not_gt h
    have hb :=
      (Nat.pow_le_pow_left hp.two_le 16).trans ((Nat.pow_le_pow_right hp.pos hl).trans hpow)
    exact (by decide : ¬2 ^ 16 ≤ 50000) hb

/-- Every prime power of exponent at least two through 50000 occurs in the
separate higher-power payload. Use the proved base and exponent bounds,
then transfer membership through the certified bounded enumeration.
This proves completeness without scanning all composite integers. -/
theorem mem_higher_payload_of_power {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) (hpow : p ^ e ≤ 50000) :
    (p, e - 1) ∈ centerHigherPowers := by
  obtain ⟨hpB, heB⟩ := higher_power_cutoff_bounds hp he hpow
  rw [centerHigherPowers_eq]
  apply List.mem_flatMap.mpr
  refine ⟨e, List.mem_range'_1.mpr ⟨he, heB⟩, ?_⟩
  apply List.mem_map.mpr
  refine ⟨p, ?_, rfl⟩
  apply List.mem_filter.mpr
  refine ⟨List.mem_filter.mpr ⟨List.mem_range.mpr hpB, ?_⟩, ?_⟩
  · let : Decidable p.Prime := Nat.decidablePrime' p
    exact (decide_eq_true_eq).mpr hp
  · exact (decide_eq_true_eq).mpr hpow

/-- Every higher-power payload entry has prime base, exponent at least two
and value at most 50000. Unpack the bounded enumeration certificate. This
excludes extraneous terms when transferring the finite weighted sum. -/
theorem higher_payload_sound {pk : ℕ × ℕ} (h : pk ∈ centerHigherPowers) :
    pk.1.Prime ∧ 1 ≤ pk.2 ∧ pk.1 ^ (pk.2 + 1) ≤ 50000 := by
  rw [centerHigherPowers_eq] at h
  obtain ⟨e, he, hm⟩ := List.mem_flatMap.mp h
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hm
  rw [← heq]
  have he2 := (List.mem_range'_1.mp he).1
  have hpouter := List.mem_filter.mp hp
  have hpinner := List.mem_filter.mp hpouter.1
  let : Decidable p.Prime := Nat.decidablePrime' p
  have hprime : p.Prime := of_decide_eq_true hpinner.2
  have hpow : p ^ e ≤ 50000 := of_decide_eq_true hpouter.2
  have he1 : 1 ≤ e := (by decide : 1 ≤ 2).trans he2
  refine ⟨hprime, Nat.le_sub_of_add_le he2, ?_⟩
  simpa only [Nat.sub_add_cancel he1] using hpow

/-- The payload image consists exactly of the positive composite prime
powers through 50000. Combine soundness with the base/exponent completeness
bounds and exclude exponent one using nonprimality. This identifies the
higher-power contribution in the actual Euler prefix decomposition. -/
theorem higher_payload_support (m : ℕ) :
    (∃ pk ∈ centerHigherPowers, pk.1 ^ (pk.2 + 1) = m) ↔
      0 < m ∧ m ≤ 50000 ∧ IsPrimePow m ∧ ¬m.Prime := by
  constructor
  · rintro ⟨pk, hpk, rfl⟩
    obtain ⟨hp, hk, hb⟩ := higher_payload_sound hpk
    refine ⟨Nat.pow_pos hp.pos, hb, ?_, Nat.Prime.not_prime_pow (Nat.succ_le_succ hk)⟩
    exact (isPrimePow_nat_iff _).mpr ⟨pk.1, pk.2 + 1, hp, Nat.succ_pos _, rfl⟩
  · rintro ⟨_, hb, hpow, hnp⟩
    obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff m).mp hpow
    have hne : e ≠ 1 := fun h ↦ hnp (by simpa only [h, pow_one] using hp)
    have he2 : 2 ≤ e := Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.one_le_of_lt he) (Ne.symm hne))
    refine ⟨(p, e - 1), mem_higher_payload_of_power hp he2 hb, ?_⟩
    exact congrArg (fun k ↦ p ^ k) (Nat.sub_add_cancel (Nat.one_le_of_lt he))

/-- The image of the checked higher-power payload is exactly the
composite-prime-power support through 50000. Transfer the list support
equivalence to finite-set membership. This fixes the support of finite sums. -/
theorem higher_payload_finset :
    centerHigherPowers.toFinset.image (fun pk ↦ pk.1 ^ (pk.2 + 1)) =
      (Finset.Ioc 0 50000).filter (fun m ↦ IsPrimePow m ∧ ¬m.Prime) := by
  ext m
  simpa only [Finset.mem_image, List.mem_toFinset, Finset.mem_filter, Finset.mem_Ioc,
    and_assoc] using higher_payload_support m

/-- Any real weighted sum on the composite-prime-power support through
50000 equals the sum on the 84 checked payload pairs. Prime-power uniqueness
makes the indexing injective. This transfers Euler and Chebyshev weights
without repeating the support computation. -/
theorem higher_payload_sum (f : ℕ → ℝ) :
    (∑ m ∈ (Finset.Ioc 0 50000).filter (fun m ↦ IsPrimePow m ∧ ¬m.Prime), f m) =
      ∑ pk ∈ centerHigherPowers.toFinset, f (pk.1 ^ (pk.2 + 1)) := by
  rw [← higher_payload_finset]
  apply Finset.sum_image
  intro a ha b hb hab
  have hp := (higher_payload_sound (List.mem_toFinset.mp ha)).1
  have hq := (higher_payload_sound (List.mem_toFinset.mp hb)).1
  exact Prod.ext (hp.pow_inj hq hab).1 (hp.pow_inj hq hab).2

end PseudoPrime.PrimeTestBounds.MillerRabin
