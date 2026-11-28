/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.SieveBounds
import Mathlib.Tactic.Linarith

/-! # Segmented prime sieve with a scalar primality specification -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Mark the in-range multiples with multipliers from lo through lo + count - 1. -/
def clear (a p lo : ℕ) : ℕ → Array Bool → Array Bool
  | 0, xs => xs
  | k + 1, xs =>
    let m := (lo + k) * p
    clear a p lo k (if a ≤ m then xs.setIfInBounds (m - a) false else xs)

private theorem read_clear_one {xs : Array Bool} {i j : ℕ} :
    (xs.setIfInBounds j false)[i]? = some true ↔ xs[i]? = some true ∧ j ≠ i := by
  by_cases h : j = i
  · subst i
    rw [Array.getElem?_setIfInBounds]
    by_cases hj : j < xs.size <;>
      simp only [ite_true, hj, ite_false, ne_self_iff_false, and_false, reduceCtorEq,
        Bool.false_eq_true, Option.some.injEq]
  · rw [Array.getElem?_setIfInBounds_ne h, and_iff_left h]

private theorem read_clear {a p lo count i : ℕ} {xs : Array Bool} :
    (clear a p lo count xs)[i]? = some true ↔
      xs[i]? = some true ∧ ∀ k < count, a ≤ (lo + k) * p → (lo + k) * p - a ≠ i := by
  induction count generalizing xs with
  | zero => simp only [clear, Nat.not_lt_zero, false_implies, implies_true, and_true]
  | succ k ih =>
    rw [clear, ih, Nat.forall_lt_succ_right]
    by_cases h : a ≤ (lo + k) * p
    · rw [ite_eq_left h, read_clear_one]
      exact ⟨fun v ↦ ⟨v.1.1, v.2, fun _ ↦ v.1.2⟩, fun v ↦ ⟨⟨v.1, v.2.2 h⟩, v.2.1⟩⟩
    · rw [ite_eq_right h]
      exact ⟨fun v ↦ ⟨v.1, v.2, fun ha ↦ False.elim (h ha)⟩, fun v ↦ ⟨v.1, v.2.1⟩⟩

/-- Mark multiples of the given base starting no earlier than its square. -/
def strike (a b : ℕ) (xs : Array Bool) (p : ℕ) : Array Bool :=
  let lo := max p (a / p)
  if 2 ≤ p then clear a p lo (b / p + 1 - lo) xs else xs

private theorem read_strike {a b n p : ℕ} {xs : Array Bool} (ha : a ≤ n) (hb : n < b) :
    (strike a b xs p)[n - a]? = some true ↔
      xs[n - a]? = some true ∧ (2 ≤ p → ∀ m, p ≤ m → m * p ≠ n) := by
  by_cases h : 2 ≤ p
  · rw [strike, ite_eq_left h, read_clear]
    apply and_congr_right
    intro _
    let lo := max p (a / p)
    have hp : 0 < p := Nat.zero_lt_of_lt h
    constructor
    · intro hits _ m hpm he
      have hdiv : n / p = m := he ▸ Nat.mul_div_cancel m hp
      have hlo : lo ≤ m := max_le hpm (hdiv ▸ Nat.div_le_div_right ha)
      have hm : m < b / p + 1 := Nat.lt_succ_of_le (hdiv ▸ Nat.div_le_div_right hb.le)
      have hit := hits (m - lo) (Nat.sub_lt_sub_right hlo hm)
      rw [show max p (a / p) + (m - lo) = m from Nat.add_sub_of_le hlo, he] at hit
      exact hit ha rfl
    · intro ok k _ ham he
      have eq := congrArg (fun v ↦ v + a) he
      rw [Nat.sub_add_cancel ham, Nat.sub_add_cancel ha] at eq
      exact ok h _ ((Nat.le_max_left _ _).trans (Nat.le_add_right _ k)) eq
  · rw [strike, ite_eq_right h]
    exact ⟨fun hx ↦ ⟨hx, fun hh ↦ False.elim (h hh)⟩, And.left⟩

private theorem read_fold {a b n : ℕ} (ha : a ≤ n) (hb : n < b) (ps : List ℕ) (xs : Array Bool) :
    (ps.foldl (strike a b) xs)[n - a]? = some true ↔
      xs[n - a]? = some true ∧ ∀ p ∈ ps, 2 ≤ p → ∀ m, p ≤ m → m * p ≠ n := by
  induction ps generalizing xs with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, false_implies, implies_true, and_true]
  | cons p ps ih =>
    rw [List.foldl_cons, ih, read_strike ha hb, List.forall_mem_cons]
    exact ⟨fun v ↦ ⟨v.1.1, v.1.2, v.2⟩, fun v ↦ ⟨⟨v.1, v.2.1⟩, v.2.2⟩⟩

/-- Sieve the half-open segment with the supplied bases, initializing only n ≥ 2 as live. -/
def sieve (a b : Nat) (bases : Array Nat) : Array Bool :=
  bases.foldl (strike a b) (Array.ofFn fun j : Fin (b - a) ↦ decide (2 ≤ a + j.val))

private theorem read_sieve {a b n : ℕ} (ha : a ≤ n) (hb : n < b) (ps : Array ℕ) :
    (sieve a b ps)[n - a]? = some true ↔ 2 ≤ n ∧ ∀ p ∈ ps, 2 ≤ p → ∀ m, p ≤ m → m * p ≠ n := by
  rw [sieve, ← Array.foldl_toList, read_fold ha hb]
  have hidx := Nat.sub_lt_sub_right ha hb
  simp only [Array.getElem?_ofFn, hidx, dite_true, Nat.add_sub_of_le ha, Option.some.injEq,
    decide_eq_true_eq, Array.mem_toList_iff]

private theorem prime_avoids {n p m : ℕ} (hn : n.Prime) (hp : 2 ≤ p) (hm : p ≤ m) : m * p ≠ n := by
  intro he
  have hdiv : p ∣ n := he ▸ dvd_mul_left p m
  rcases (Nat.dvd_prime hn).mp hdiv with h | h
  · linarith only [hp, h]
  · have hh : m * p ≤ 1 * p := by rw [he, h, Nat.one_mul]
    have hle := Nat.le_of_mul_le_mul_right hh (Nat.zero_lt_of_lt hp)
    linarith only [hle, hp, hm]

/-- On a half-open segment the sieve characterizes primality if every
composite in the segment has its least prime factor among the supplied bases.
Bases beyond the least factors need no primality hypothesis. -/
theorem sieve_get_true_iff {a b n : ℕ} (ha : a ≤ n) (hb : n < b) (ps : Array ℕ)
    (hbase : 2 ≤ n → ¬n.Prime → n.minFac ∈ ps) : (sieve a b ps)[n - a]? = some true ↔ n.Prime := by
  rw [read_sieve ha hb]
  constructor
  · intro h
    by_contra hc
    have hn₀ : 0 < n := by linarith only [h.1]
    have hp := Nat.minFac_prime (show n ≠ 1 by linarith only [h.1])
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hs := Nat.minFac_sq_le_self hn₀ hc
    have hm' : n = m * n.minFac := hm.trans (Nat.mul_comm _ _)
    have hmul : n.minFac * n.minFac ≤ m * n.minFac :=
      (by simpa only [pow_two] using hs : n.minFac * n.minFac ≤ n).trans_eq hm'
    exact h.2 n.minFac (hbase h.1 hc) hp.two_le m (Nat.le_of_mul_le_mul_right hmul hp.pos) hm'.symm
  · exact fun hp ↦ ⟨hp.two_le, fun _ _ h _ hm ↦ prime_avoids hp h hm⟩

/-- Scalar query of the shared sieve at an absolute integer index. -/
def sieveFlag (a b n : ℕ) : Bool :=
  ((sieve a b basePrimes)[n - a]?).getD false

/-- On its segment through one million the computed flag characterizes primality exactly. -/
theorem sieveFlag_iff {a b n : ℕ} (ha : a ≤ n) (hb : n < b) (hu : n ≤ 1000000) :
    sieveFlag a b n = true ↔ n.Prime := by
  have he : sieveFlag a b n = true ↔ (sieve a b basePrimes)[n - a]? = some true := by
    unfold sieveFlag
    cases (sieve a b basePrimes)[n - a]? with
    | none => decide
    | some v => simp only [Option.getD_some, Option.some.injEq]
  rw [he, read_sieve ha hb]
  constructor
  · intro h
    by_contra hc
    obtain ⟨p, hmem, hsq, m, hm⟩ := composite_has_base h.1 hu hc
    have hpr := ((baseHas_iff p).mp hmem).2
    rw [hm, pow_two, Nat.mul_comm p m] at hsq
    exact
      h.2 p (Array.contains_iff_mem.mp hmem) hpr.two_le m (Nat.le_of_mul_le_mul_right hsq hpr.pos)
        ((Nat.mul_comm m p).trans hm.symm)
  · exact fun hp ↦ ⟨hp.two_le, fun _ _ h _ hm ↦ prime_avoids hp h hm⟩

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
