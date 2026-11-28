/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.SegmentSieve
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! # Complete prime-power support for section 137 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def sieveBases : Array ℕ :=
  ((List.range 1232).filter (fun p ↦ @decide p.Prime (Nat.decidablePrime' p))).toArray

private theorem mem_sieve_bases (p : ℕ) : p ∈ sieveBases ↔ p < 1232 ∧ p.Prime := by
  unfold sieveBases
  rw [← Array.mem_toList_iff, List.toList_toArray, List.mem_filter, List.mem_range]
  exact
    and_congr_right fun _ ↦
      ⟨@of_decide_eq_true p.Prime (Nat.decidablePrime' p),
        @decide_eq_true p.Prime (Nat.decidablePrime' p)⟩

private theorem minfac_lt {n : ℕ} (hn : 0 < n) (hU : n ≤ 1517026) (hp : ¬n.Prime) :
    n.minFac < 1232 := by
  have h := Nat.minFac_sq_le_self hn hp
  by_contra h'
  have hh := Nat.pow_le_pow_left (le_of_not_gt h') 2
  have hcut : ¬1232 ^ (2 : ℕ) ≤ 1517026 := by decide
  exact hcut (hh.trans (h.trans hU))

/-- A single sieve on the requested integer window gives every prime in it
when its upper endpoint is at most 1517026. -/
def quarterSievedPrimes663 (L U : ℕ) : Finset ℕ :=
  let flags := AnalyticNumberTheory.Cert.Chebyshev.Joint.sieve (L + 1) (U + 1) sieveBases
  (Finset.Ioc L U).filter (fun n ↦ (flags[n - (L + 1)]?).getD false)

/-- The computed segment contains exactly the primes in the window. -/
theorem quarter_sieved_prime_iff_663 {L U n : ℕ} (hU : U ≤ 1517026) :
    n ∈ quarterSievedPrimes663 L U ↔ n ∈ Finset.Ioc L U ∧ n.Prime := by
  unfold quarterSievedPrimes663
  rw [Finset.mem_filter]
  apply and_congr_right
  intro hn
  obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hn
  have hbase (h₂ : 2 ≤ n) (hp : ¬n.Prime) : n.minFac ∈ sieveBases := by
    exact
      (mem_sieve_bases _).mpr
        ⟨minfac_lt (by linarith only [h₂]) (hu.trans hU) hp,
          Nat.minFac_prime (by linarith only [h₂] : n ≠ 1)⟩
  have h :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.sieve_get_true_iff (Nat.succ_le_of_lt hl)
      (Nat.lt_succ_of_le hu) sieveBases hbase
  rw [← h]
  cases
    (AnalyticNumberTheory.Cert.Chebyshev.Joint.sieve (L + 1) (U + 1) sieveBases)[n - (L + 1)]? with
  | none => decide
  | some v => simp only [Option.getD_some, Option.some.injEq]

/-- Enumerate powers with exponent at least two from the same prime bases
as the sieve. Only the selected window is kept. -/
def quarterProperPowers663 (L U : ℕ) : List ℕ :=
  sieveBases.toList.flatMap fun p ↦
    ((List.range' 2 19).map (fun k ↦ p ^ k)).filter (fun n ↦ decide (L < n ∧ n ≤ U))

private theorem proper_power_iff {L U n : ℕ} (hU : U ≤ 1517026) :
    n ∈ quarterProperPowers663 L U ↔
      n ∈ Finset.Ioc L U ∧ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k := by
  simp only [quarterProperPowers663, List.mem_flatMap, Array.mem_toList_iff, mem_sieve_bases,
    List.mem_filter, List.mem_map, List.mem_range'_1, decide_eq_true_eq]
  constructor
  · intro hn
    obtain ⟨p, hp, hpow⟩ := hn
    obtain ⟨⟨k, hk, hEq⟩, hb⟩ := hpow
    exact ⟨Finset.mem_Ioc.mpr hb, p, k, hp.2, hk.1, hEq.symm⟩
  · rintro ⟨hn, p, k, hp, hk, rfl⟩
    have hu := (Finset.mem_Ioc.mp hn).2.trans hU
    have hp' : p < 1232 := by
      by_contra h
      have hh := Nat.pow_le_pow_left (le_of_not_gt h) 2
      have ht := Nat.pow_le_pow_right hp.pos hk
      exact (by decide : ¬1232 ^ (2 : ℕ) ≤ 1517026) (hh.trans (ht.trans hu))
    have hk' : k ≤ 20 := by
      by_contra h
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_of_lt (lt_of_not_ge h))
      have ht := Nat.pow_le_pow_left hp.two_le k
      exact (by decide : ¬2 ^ (21 : ℕ) ≤ 1517026) (hh.trans (ht.trans hu))
    exact ⟨p, ⟨hp', hp⟩, ⟨⟨k, ⟨hk, Nat.lt_succ_of_le hk'⟩, rfl⟩, Finset.mem_Ioc.mp hn⟩⟩

/-- Combine the segmented prime sieve with proper powers of bases below
1232. Each index is retained once by the finite union. -/
def quarterSievedPowers663 (L U : ℕ) : Finset ℕ :=
  quarterSievedPrimes663 L U ∪ (quarterProperPowers663 L U).toFinset

/-- The complete computed support contains every and only prime power
in the requested segment of the section 137 Mangoldt table. -/
theorem quarter_sieved_power_iff_663 {L U n : ℕ} (hU : U ≤ 1517026) :
    n ∈ quarterSievedPowers663 L U ↔ n ∈ Finset.Ioc L U ∧ IsPrimePow n := by
  rw [quarterSievedPowers663, Finset.mem_union, quarter_sieved_prime_iff_663 hU, List.mem_toFinset,
    proper_power_iff hU]
  constructor
  · rintro (⟨hn, hp⟩ | ⟨hn, p, k, hp, hk, he⟩)
    · exact ⟨hn, (isPrimePow_nat_iff n).mpr ⟨n, 1, hp, by decide, pow_one n⟩⟩
    · exact ⟨hn, (isPrimePow_nat_iff n).mpr ⟨p, k, hp, by linarith only [hk], he.symm⟩⟩
  · rintro ⟨hn, h⟩
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp h
    by_cases he : k = 1
    · simpa only [he, pow_one] using
        (Or.inl ⟨by simpa only [he, pow_one] using hn, hp⟩ : (p ∈ Finset.Ioc L U ∧ p.Prime) ∨ _)
    · exact Or.inr ⟨hn, p, k, hp, lt_of_le_of_ne hk (Ne.symm he), rfl⟩

/-- Index the live flags of the shared sieve in increasing order. The flag
array is constructed before the scan of the requested block. -/
def quarterSievePrimeIndices663 (L U : ℕ) : List ℕ :=
  let flags := AnalyticNumberTheory.Cert.Chebyshev.Joint.sieve (L + 1) (U + 1) sieveBases
  (List.range' (L + 1) (U - L)).filter (fun n ↦ (flags[n - (L + 1)]?).getD false)

/-- Equality with the sieve's live index list gives the exact prime
support. No comparison of finite sets is required to check the data. -/
theorem quarter_sieve_indices_iff_663 {L U n : ℕ} (hU : U ≤ 1517026) :
    n ∈ quarterSievePrimeIndices663 L U ↔ n ∈ Finset.Ioc L U ∧ n.Prime := by
  rw [← quarter_sieved_prime_iff_663 (n := n) (L := L) hU]
  unfold quarterSievePrimeIndices663 quarterSievedPrimes663
  simp only [List.mem_filter, List.mem_range'_1, Finset.mem_filter, Finset.mem_Ioc]
  have h : (L + 1 ≤ n ∧ n < L + 1 + (U - L)) ↔ L < n ∧ n ≤ U := by
    constructor
    · intro hn
      have hLU : L ≤ U := by
        by_contra h'
        rw [Nat.sub_eq_zero_of_le (le_of_not_ge h'), Nat.add_zero] at hn
        exact hn.2.not_ge hn.1
      have he : L + 1 + (U - L) = U + 1 := by rw [Nat.add_right_comm, Nat.add_sub_of_le hLU]
      exact ⟨hn.1, Nat.lt_succ_iff.mp (by simpa only [he] using hn.2)⟩
    · intro hn
      have he : L + 1 + (U - L) = U + 1 := by
        rw [Nat.add_right_comm, Nat.add_sub_of_le (hn.1.le.trans hn.2)]
      exact ⟨hn.1, he.symm ▸ Nat.lt_succ_of_le hn.2⟩
  rw [h]

/-- Enumerate primes in a short window by independent primality decisions.
This version avoids array reduction when the kernel checks a closed list. -/
def quarterTrialPrimeIndices663 (L U : ℕ) : List ℕ :=
  (List.range' (L + 1) (U - L)).filter (fun n ↦ @decide n.Prime (Nat.decidablePrime' n))

/-- Within the certified cutoff, the trial decisions and segmented sieve
retain exactly the same elements of the increasing integer list. -/
theorem quarter_trial_eq_sieve_663 {L U : ℕ} (hU : U ≤ 1517026) :
    quarterTrialPrimeIndices663 L U = quarterSievePrimeIndices663 L U := by
  unfold quarterTrialPrimeIndices663
  change _ = (List.range' (L + 1) (U - L)).filter _
  apply List.filter_congr
  intro n hn
  have h := quarter_sieve_indices_iff_663 (L := L) (n := n) hU
  unfold quarterSievePrimeIndices663 at h
  rw [List.mem_filter] at h
  have hu : n ∈ Finset.Ioc L U := by
    have hl := List.mem_range'_1.mp hn
    have hLU : L ≤ U := by
      by_contra h'
      rw [Nat.sub_eq_zero_of_le (le_of_not_ge h'), Nat.add_zero] at hl
      exact hl.2.not_ge hl.1
    rw [Nat.add_right_comm, Nat.add_sub_of_le hLU] at hl
    exact Finset.mem_Ioc.mpr ⟨hl.1, Nat.lt_succ_iff.mp hl.2⟩
  apply Bool.eq_iff_iff.mpr
  exact
    ⟨fun hp ↦ (h.mpr ⟨hu, @of_decide_eq_true n.Prime (Nat.decidablePrime' n) hp⟩).2, fun hf ↦
      @decide_eq_true n.Prime (Nat.decidablePrime' n) (h.mp ⟨hn, hf⟩).2⟩

/-- Concatenating the two lists gives the exact prime-power support, so
checking the two lists needs no equality test on a large finite set. -/
theorem quarter_power_indices_iff_663 {L U n : ℕ} (hU : U ≤ 1517026) :
    n ∈ quarterSievePrimeIndices663 L U ++ quarterProperPowers663 L U ↔
      n ∈ Finset.Ioc L U ∧ IsPrimePow n := by
  rw [← quarter_sieved_power_iff_663 (L := L) hU, quarterSievedPowers663, Finset.mem_union,
    List.mem_append, List.mem_toFinset, quarter_sieve_indices_iff_663 hU,
    quarter_sieved_prime_iff_663 hU]

end PseudoPrime.PrimeTestBounds.MillerRabin
