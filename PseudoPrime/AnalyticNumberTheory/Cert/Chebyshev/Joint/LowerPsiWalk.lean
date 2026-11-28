/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.SignedWalk

/-! # One-sided Chebyshev checks beyond the joint sieve -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def lowerPrimeProduct : ℕ :=
  86360143912176549371762936127893 * 10 ^ 884 +
    99758854834000184866434231611655648781324347928793955481144610431160 * 10 ^ 816 +
    15118377805865193522120086706316321951351032176975965822867012479442 * 10 ^ 748 +
    93831249335628094125644117289430898021013666159587802185333259260322 * 10 ^ 680 +
    96330649051500147980096906067736196617654390275221620593045790531300 * 10 ^ 612 +
    56685402237803016073270605287578831382243378099934802591187829263246 * 10 ^ 544 +
    79535761224962551308095703350615564721615397209712940891095133910152 * 10 ^ 476 +
    49844018651462357507184398925705174262853956882293747485862485133339 * 10 ^ 408 +
    96665283527487803567855482963181612047621394153182677537353366027 * 10 ^ 340 +
    15039585855347593092745752379236374967054082440331146832819076211971 * 10 ^ 272 +
    74768797148512378648594592504773193455369022558004914114555475840539 * 10 ^ 204 +
    3897550812060687657367264529937803873087242873641016124777606535053 * 10 ^ 136 +
    59167337486534403666850733630663710864467351334967414697660990810654 * 10 ^ 68 +
    15353634271254563936167526400000000000000000000000000000000000000000

private theorem lower_prime_product_eq :
    baseProduct * ((List.range 165).map fun j ↦ 1001 + j).prod = lowerPrimeProduct := by
  decide +kernel

private theorem prime_dvd_lower_product {p : ℕ} (hp : p.Prime) (hb : p ≤ 1165) :
    p ∣ lowerPrimeProduct := by
  rw [← lower_prime_product_eq]
  by_cases h : p ≤ 1000
  · have hm := (baseHas_iff p).2 ⟨Nat.lt_succ_of_le h, hp⟩
    have hd : p ∣ baseProduct :=
      List.dvd_prod (l := basePrimes.toList)
        (Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hm))
    exact dvd_mul_of_dvd_left hd (((List.range 165).map fun j ↦ 1001 + j).prod)
  have hm : p ∈ (List.range 165).map (fun j ↦ 1001 + j) := by
    apply List.mem_map.mpr
    exact
      ⟨p - 1001,
        List.mem_range.mpr
          ((Nat.sub_le_sub_right hb 1001).trans_lt (by decide : 1165 - 1001 < 165)),
        Nat.add_sub_of_le (Nat.succ_le_of_lt (lt_of_not_ge h))⟩
  have hd : p ∣ ((List.range 165).map fun j ↦ 1001 + j).prod :=
    List.dvd_prod (l := (List.range 165).map (fun j ↦ 1001 + j)) hm
  exact dvd_mul_of_dvd_right hd baseProduct

private theorem prime_of_lower_gcd {n : ℕ} (hn : 1 < n) (hu : n ≤ 1165 ^ 2)
    (hg : n.gcd lowerPrimeProduct = 1) : n.Prime := by
  by_contra hp
  have hf := Nat.minFac_prime (ne_of_gt hn)
  have hsq := Nat.minFac_sq_le_self (Nat.zero_lt_of_lt hn) hp
  have hle : n.minFac ≤ 1165 := by
    by_contra h
    have hle := Nat.pow_le_pow_left (Nat.succ_le_of_lt (lt_of_not_ge h)) 2
    exact (by decide : ¬1166 ^ 2 ≤ 1165 ^ 2) (hle.trans (hsq.trans hu))
  have hdiv := prime_dvd_lower_product hf hle
  exact hf.not_dvd_one (hg ▸ Nat.dvd_gcd (Nat.minFac_dvd n) hdiv)

private def eventPrimeCheck (p : ℕ) : Bool :=
  if p ≤ 1165 then decide p.Prime else decide (1 < p ∧ p ≤ 1165 ^ 2 ∧ p.gcd lowerPrimeProduct = 1)

private theorem event_prime_of_check {p : ℕ} (h : eventPrimeCheck p = true) : p.Prime := by
  unfold eventPrimeCheck at h
  split at h
  · exact of_decide_eq_true h
  · obtain ⟨h1, h2, h3⟩ := of_decide_eq_true h
    exact prime_of_lower_gcd h1 h2 h3

/-- A certified prime-power event advances to its integer and adds a lower log tick.
Consecutive tested integers bound the intervening real interval by monotonicity of psi. -/
def lowerPsiEvents (floor : ℤ) (stop : ℕ) : ℕ → ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, ticks, [] => decide (floor + (scale : ℤ) * stop ≤ (ticks : ℤ))
  | a, ticks, (b, p, k) :: rows =>
    decide
        (a < b ∧
          b ≤ stop ∧
          floor + (scale : ℤ) * b ≤ (ticks : ℤ) ∧ eventPrimeCheck p = true ∧ k ≠ 0 ∧ p ^ k = b) &&
      lowerPsiEvents floor stop b (ticks + (certifiedTicks p).1) rows

private theorem lower_floor_on_gap {floor : ℤ} {a b ticks : ℕ} {x : ℝ}
    (ht : (ticks : ℝ) ≤ scale * Chebyshev.psi a) (hf : floor + (scale : ℤ) * b ≤ (ticks : ℤ))
    (hx : (a : ℝ) ≤ x) (hy : x ≤ b) : (floor : ℝ) / scale ≤ Chebyshev.psi x - x := by
  have hC : (floor : ℝ) + (scale : ℝ) * (b : ℝ) ≤ (ticks : ℝ) := by exact_mod_cast hf
  have hp : (0 : ℝ) < scale := by norm_num only [scale, Nat.cast_ofNat]
  apply (div_le_iff₀ hp).mpr
  linarith only [hC, ht, mul_le_mul_of_nonneg_left (Chebyshev.psi_mono hx) hp.le,
    mul_le_mul_of_nonneg_left hy hp.le]

private theorem lower_event_ticks {a b p k ticks : ℕ} (hab : a < b) (hp : p.Prime) (hk : k ≠ 0)
    (hb : p ^ k = b) (ht : (ticks : ℝ) ≤ scale * Chebyshev.psi a) :
    ((ticks + (certifiedTicks p).1 : ℕ) : ℝ) ≤ scale * Chebyshev.psi b := by
  have hbs : b - 1 + 1 = b := Nat.sub_add_cancel (Nat.zero_lt_of_lt hab)
  have hψ := psi_next (b - 1)
  rw [hbs, ← hb, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp, hb] at hψ
  have hm := Chebyshev.psi_mono (Nat.cast_le.mpr (Nat.le_sub_one_of_lt hab) : (a : ℝ) ≤ (b - 1 : ℕ))
  rw [Nat.cast_add, hψ, mul_add]
  exact
    add_le_add (ht.trans (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg scale)))
      (primeTicks_sound hp.ne_zero).1

/-- A successful event check proves the signed floor on the entire closed
interval starting at a certified prefix. Events may omit nonnegative contributions. -/
theorem lower_psi_events_sound {floor : ℤ} {stop : ℕ} (rows : List (ℕ × ℕ × ℕ)) {a ticks : ℕ}
    (ht : (ticks : ℝ) ≤ scale * Chebyshev.psi a)
    (hc : lowerPsiEvents floor stop a ticks rows = true) {x : ℝ} (hx : (a : ℝ) ≤ x)
    (hy : x ≤ stop) : (floor : ℝ) / scale ≤ Chebyshev.psi x - x := by
  induction rows generalizing a ticks with
  | nil => exact lower_floor_on_gap ht (of_decide_eq_true hc) hx hy
  | cons row rows ih =>
    obtain ⟨b, p, k⟩ := row
    rw [lowerPsiEvents, Bool.and_eq_true_iff] at hc
    obtain ⟨hab, _, hf, hp, hk, hb⟩ := of_decide_eq_true hc.1
    by_cases hxb : x ≤ b
    · exact lower_floor_on_gap ht hf hx hxb
    · exact ih (lower_event_ticks hab (event_prime_of_check hp) hk hb ht) hc.2 (le_of_not_ge hxb)

/-- Recover a scalar lower prefix at the batch endpoint from the same checked
events used to establish the signed floor over the batch. -/
theorem lower_psi_events_exit {floor : ℤ} {stop : ℕ} (rows : List (ℕ × ℕ × ℕ)) {a ticks : ℕ}
    (ha : a ≤ stop) (ht : (ticks : ℝ) ≤ scale * Chebyshev.psi a)
    (hc : lowerPsiEvents floor stop a ticks rows = true) :
    ((rows.foldl (fun total row ↦ total + (certifiedTicks row.2.1).1) ticks : ℕ) : ℝ) ≤
      scale * Chebyshev.psi stop := by
  induction rows generalizing a ticks with
  | nil =>
    exact
      ht.trans
        (mul_le_mul_of_nonneg_left (Chebyshev.psi_mono (Nat.cast_le.mpr ha))
          (Nat.cast_nonneg scale))
  | cons row rows ih =>
    obtain ⟨b, p, k⟩ := row
    rw [lowerPsiEvents, Bool.and_eq_true_iff] at hc
    obtain ⟨hab, hstop, _, hp, hk, hb⟩ := of_decide_eq_true hc.1
    exact ih hstop (lower_event_ticks hab (event_prime_of_check hp) hk hb ht) hc.2

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
