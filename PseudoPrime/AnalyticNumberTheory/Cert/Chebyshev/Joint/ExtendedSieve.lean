/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.SegmentSieve
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PowerLookup
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.GCD.BigOperators

/-! # Segmented prime and higher-power rows through 1,600,000 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def extendedBases : Array ℕ :=
  ((List.range 1265).filter (fun p ↦ decide p.Prime)).toArray

private theorem mem_extended_bases {p : ℕ} : p ∈ extendedBases ↔ p < 1265 ∧ p.Prime := by
  simp only [extendedBases, List.mem_toArray, List.mem_filter, List.mem_range, decide_eq_true_eq]

/-- A segment of the shared sieve with enough bases for all input integers
up to 1,600,000. The output uses the offset from the left endpoint. -/
public def extendedSieve (a b : ℕ) : Array Bool :=
  sieve a b extendedBases

/-- Every flag at an in-range offset in the extended sieve is exact. -/
public theorem extended_sieve_iff {a b n : ℕ} (ha : a ≤ n) (hb : n < b) (hn : n ≤ 1600000) :
    (extendedSieve a b)[n - a]? = some true ↔ n.Prime := by
  change (sieve a b extendedBases)[n - a]? = some true ↔ n.Prime
  apply sieve_get_true_iff ha hb extendedBases
  intro h2 hc
  apply mem_extended_bases.mpr
  refine ⟨?_, Nat.minFac_prime (show n ≠ 1 by linarith only [h2])⟩
  by_contra! h
  have hs := Nat.minFac_sq_le_self ((zero_lt_two.trans_le h2)) hc
  exact (by decide : ¬1265 ^ 2 ≤ 1600000) ((Nat.pow_le_pow_left h 2).trans (hs.trans hn))

private theorem extended_gcd_one_iff {n : ℕ} (hl : 1264 < n) (hu : n ≤ 1600000) :
    n.gcd extendedBases.toList.prod = 1 ↔ n.Prime := by
  constructor
  · intro hg
    by_contra hp
    have hn : 0 < n := (by decide : 0 < 1264).trans hl
    have hs := Nat.minFac_sq_le_self hn hp
    have hb : n.minFac < 1265 := by
      by_contra! h
      exact (by decide : ¬1265 ^ 2 ≤ 1600000) ((Nat.pow_le_pow_left h 2).trans (hs.trans hu))
    have hf := Nat.minFac_prime (show n ≠ 1 by linarith only [hl])
    have hm := mem_extended_bases.mpr ⟨hb, hf⟩
    exact
      hf.not_dvd_one
        (hg ▸ Nat.dvd_gcd (Nat.minFac_dvd n) (List.dvd_prod (Array.mem_toList_iff.mpr hm)))
  · intro hp
    apply Nat.coprime_list_prod_right_iff.mpr
    intro q hq
    have h := mem_extended_bases.mp (Array.mem_toList_iff.mp hq)
    exact
      hp.coprime_iff_not_dvd.mpr
        (fun hd ↦
          (Nat.not_le.mpr (Nat.lt_of_lt_of_le h.1 (Nat.succ_le_of_lt hl)))
            (Nat.le_of_dvd h.2.pos hd))

private def extendedPowerEntries : List (ℕ × ℕ) :=
  extendedBases.toList.flatMap fun p ↦
    ((List.range 19).map fun i ↦ (p ^ (i + 2), p)).filter (fun v ↦ decide (v.1 ≤ 1600000))

private theorem mem_extended_powers {n p : ℕ} :
    (n, p) ∈ extendedPowerEntries ↔
      n ≤ 1600000 ∧ p < 1265 ∧ p.Prime ∧ ∃ i < 19, p ^ (i + 2) = n := by
  rw [extendedPowerEntries, List.mem_flatMap]
  simp only [List.mem_filter, List.mem_map, List.mem_range, Prod.mk.injEq, Array.mem_toList_iff,
    decide_eq_true_eq, mem_extended_bases]
  constructor
  · rintro ⟨q, ⟨hq, hp⟩, ⟨i, hi, he, rfl⟩, hn⟩
    exact ⟨hn, hq, hp, i, hi, he⟩
  · rintro ⟨hn, hq, hp, i, hi, he⟩
    exact ⟨p, ⟨hq, hp⟩, ⟨i, hi, he, rfl⟩, hn⟩

private theorem extended_composite_power {n : ℕ} (hn : n ≤ 1600000) (hc : ¬n.Prime)
    (hp : IsPrimePow n) : ∃ p k : ℕ, p < 1265 ∧ 2 ≤ k ∧ k < 21 ∧ p.Prime ∧ p ^ k = n := by
  obtain ⟨p, k, hpr, hk, he⟩ := (isPrimePow_nat_iff n).mp hp
  have hk' : 2 ≤ k := by
    by_contra! h
    have hk1 : k = 1 := by linarith only [hk, h]
    exact hc ((by simpa only [hk1, pow_one] using he : p = n) ▸ hpr)
  have hsq := (Nat.pow_le_pow_right hpr.pos hk').trans (he.le.trans hn)
  have hb : p < 1265 := by
    by_contra! hh
    exact (by decide : ¬1265 ^ 2 ≤ 1600000) ((Nat.pow_le_pow_left hh 2).trans hsq)
  have ht : k < 21 := by
    by_contra! hh
    exact
      (by decide : ¬2 ^ 21 ≤ 1600000)
        (((Nat.pow_le_pow_left hpr.two_le 21).trans (Nat.pow_le_pow_right hpr.pos hh)).trans
          (he.le.trans hn))
  exact ⟨p, k, hb, hk', ht, hpr, he⟩

/-- Return the base of a higher prime power in a segment or zero if absent. -/
public def extendedPowerAt (a b : ℕ) : ℕ → ℕ :=
  lookupPower extendedPowerEntries a b

/-- For an in-range composite, the higher-power lookup either supplies its
prime base and exponent, or certifies that it is not a prime power. -/
public theorem extended_power_spec {a b n : ℕ} (ha : a ≤ n) (hb : n < b) (hu : n ≤ 1600000)
    (hc : ¬n.Prime) :
    (extendedPowerAt a b n = 0 → ¬IsPrimePow n) ∧
      (extendedPowerAt a b n ≠ 0 →
        (extendedPowerAt a b n).Prime ∧ ∃ k ≥ 2, (extendedPowerAt a b n) ^ k = n) := by
  unfold extendedPowerAt lookupPower
  split
  next v hv =>
    obtain ⟨q, p⟩ := v
    have he : q = n := eq_of_beq (List.find?_some (p := fun v : ℕ × ℕ ↦ v.1 == n) hv)
    subst q
    have hmem := (List.mem_filter.mp (List.mem_of_find?_eq_some hv)).1
    obtain ⟨_, _, hp, i, _, hi⟩ := mem_extended_powers.mp hmem
    exact ⟨fun hz ↦ False.elim (hp.ne_zero hz), fun _ ↦ ⟨hp, i + 2, Nat.le_add_left 2 i, hi⟩⟩
  next hn =>
    constructor
    · intro _ hh
      obtain ⟨p, k, hp, hk, ht, hpr, he⟩ := extended_composite_power hu hc hh
      have hrow : (n, p) ∈ extendedPowerEntries :=
        mem_extended_powers.mpr
          ⟨hu, hp, hpr, k - 2, Nat.sub_lt_sub_right hk ht, by rwa [Nat.sub_add_cancel hk]⟩
      exact
        List.find?_eq_none.mp hn (n, p) (List.mem_filter.mpr ⟨hrow, decide_eq_true ⟨ha, hb⟩⟩)
          (beq_self_eq_true n)
    · intro h
      exact False.elim (h rfl)

private def extendedPrimeFlag (a b : ℕ) : ℕ → Bool :=
  if 1264 < a then
    let product := extendedBases.toList.prod
    fun n ↦ decide (n.gcd product = 1)
  else
    let flags := extendedSieve a b
    fun n ↦ decide (flags[n - a]? = some true)

private theorem extended_prime_flag_iff {a b n : ℕ} (ha : a ≤ n) (hb : n < b) (hu : n ≤ 1600000) :
    extendedPrimeFlag a b n = true ↔ n.Prime := by
  unfold extendedPrimeFlag
  split
  next h =>
    rw [decide_eq_true_eq]
    exact extended_gcd_one_iff (h.trans_le ha) hu
  next _ =>
    rw [decide_eq_true_eq]
    exact extended_sieve_iff ha hb hu

/-- Return the prime base of an in-range prime power, with zero as the
marker for an integer that has zero Mangoldt weight. -/
public def extendedMangoldtBase (a b : ℕ) : ℕ → ℕ :=
  let flags := extendedPrimeFlag a b
  let power := extendedPowerAt a b
  fun n ↦ if flags n then n else power n

/-- The scalar row lookup yields the exact logarithmic Mangoldt weight.
This is the soundness step for accumulating a single shared psi prefix. -/
public theorem extended_mangoldt_weight {a b n : ℕ} (ha : a ≤ n) (hb : n < b) (hu : n ≤ 1600000) :
    Real.log (extendedMangoldtBase a b n : ℝ) = ArithmeticFunction.vonMangoldt n := by
  simp only [extendedMangoldtBase]
  split
  · rename_i h
    have hp := (extended_prime_flag_iff ha hb hu).mp h
    exact (ArithmeticFunction.vonMangoldt_apply_prime hp).symm
  · rename_i h
    have hc : ¬n.Prime := fun hp ↦ h ((extended_prime_flag_iff ha hb hu).mpr hp)
    obtain ⟨hz, hp⟩ := extended_power_spec ha hb hu hc
    by_cases he : extendedPowerAt a b n = 0
    · rw [he, Nat.cast_zero, Real.log_zero, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (hz he)]
    · obtain ⟨hprime, k, hk, hkn⟩ := hp he
      have hv := congrArg (fun m ↦ ArithmeticFunction.vonMangoldt m) hkn
      rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt (zero_lt_two.trans_le hk)),
        ArithmeticFunction.vonMangoldt_apply_prime hprime] at hv
      exact hv

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
