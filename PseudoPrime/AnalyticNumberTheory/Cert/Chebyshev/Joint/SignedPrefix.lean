/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.ExtendedSieve
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PrimeTicks
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Prefix
import Mathlib.Tactic

/-! # Shared fixed-point lower prefixes for the extended Chebyshev sieve -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def lowerLogTick (p : ℕ) : ℕ :=
  if p = 0 then 0 else (primeTicks gridTicks (gridTicks 32) p).1

private theorem lower_log_tick_le (p : ℕ) : (lowerLogTick p : ℝ) ≤ scale * Real.log p := by
  by_cases hp : p = 0
  · subst p
    simp only [lowerLogTick, ite_true, Nat.cast_zero, Real.log_zero, mul_zero, le_refl]
  · rw [lowerLogTick, ite_eq_right hp]
    exact (primeTicks_sound hp).1

private def sumPsiTicks (tick : ℕ → ℕ) (a : ℕ) : ℕ → ℕ → ℕ
  | 0, s => s
  | k + 1, s => sumPsiTicks tick (a + 1) k (s + tick (a + 1))

private theorem sum_psi_ticks_le (tick : ℕ → ℕ) (a k s : ℕ) (hs : (s : ℝ) ≤ scale * Chebyshev.psi a)
    (ht : ∀ n, a < n → n ≤ a + k → (tick n : ℝ) ≤ scale * ArithmeticFunction.vonMangoldt n) :
    (sumPsiTicks tick a k s : ℝ) ≤ scale * Chebyshev.psi (a + k : ℕ) := by
  induction k generalizing a s with
  | zero => simpa only [sumPsiTicks, Nat.add_zero] using hs
  | succ k
    ih =>
    have h :=
      ht (a + 1) (Nat.lt_succ_self a) (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) a)
    have hs' : ((s + tick (a + 1) : ℕ) : ℝ) ≤ scale * Chebyshev.psi (a + 1 : ℕ) := by
      rw [Nat.cast_add, psi_next, mul_add]
      exact add_le_add hs h
    have he : a + (k + 1) = (a + 1) + k := by rw [Nat.add_assoc, Nat.add_comm 1 k]
    rw [sumPsiTicks, he]
    exact ih (a + 1) _ hs' (fun n hn hnk ↦ ht n ((Nat.le_succ a).trans_lt hn) (he ▸ hnk))

/-- Extend a lower prefix through a contiguous block using the certified
fixed-point logarithms. One sieve and one higher-power lookup serve the block. -/
public def signedPsiPrefix (a b s : ℕ) : ℕ :=
  let base := extendedMangoldtBase (a + 1) (b + 1)
  sumPsiTicks (fun n ↦ lowerLogTick (base n)) a (b - a) s

/-- A starting lower tick remains a lower bound after the entire block,
provided the end is in the verified range of the extended sieve. -/
public theorem signed_psi_prefix_le {a b s : ℕ} (hab : a ≤ b) (hb : b ≤ 1600000)
    (hs : (s : ℝ) ≤ scale * Chebyshev.psi a) :
    (signedPsiPrefix a b s : ℝ) ≤ scale * Chebyshev.psi b := by
  let tick := fun n ↦ lowerLogTick (extendedMangoldtBase (a + 1) (b + 1) n)
  have ht (n : ℕ) (ha : a < n) (hn : n ≤ a + (b - a)) :
    (tick n : ℝ) ≤ scale * ArithmeticFunction.vonMangoldt n := by
    rw [Nat.add_sub_of_le hab] at hn
    have he := extended_mangoldt_weight ha (Nat.lt_succ_of_le hn) (hn.trans hb)
    simpa only [tick, he] using lower_log_tick_le (extendedMangoldtBase (a + 1) (b + 1) n)
  have h := sum_psi_ticks_le tick a (b - a) s hs ht
  rw [Nat.add_sub_of_le hab] at h
  exact h

/-- A zero-based replay certifies a lower tick for any covered integer
prefix. This scalar statement keeps the sieve arrays out of the interface. -/
public theorem signed_psi_prefix_zero_le {b : ℕ} (hb : b ≤ 1600000) :
    (signedPsiPrefix 0 b 0 : ℝ) ≤ scale * Chebyshev.psi b := by
  apply signed_psi_prefix_le (Nat.zero_le b) hb
  simp only [Nat.cast_zero, Chebyshev.psi_zero, mul_zero, le_refl]

/-- Subtract the real right endpoint from a checked fixed-point prefix.
This supplies the endpoint row of the signed interval certificate. -/
public theorem signed_psi_endpoint {b s : ℕ} {u : ℝ} (hbu : (b : ℝ) ≤ u)
    (hs : (s : ℝ) ≤ scale * Chebyshev.psi b) : (s : ℝ) / scale - u ≤ Chebyshev.psi u - u := by
  have hscale : 0 < (scale : ℝ) := Nat.cast_pos.mpr (by decide : 0 < scale)
  have hp : (s : ℝ) / scale ≤ Chebyshev.psi b := by
    rw [div_le_iff₀ hscale, mul_comm]
    exact hs
  exact sub_le_sub_right (hp.trans (Chebyshev.psi_mono hbu)) _

private def checkPsiTicks (tick : ℕ → ℕ) (e : ℤ) (a : ℕ) : ℕ → ℕ → Option ℕ
  | 0, s => if e + (scale : ℤ) * (a : ℤ) ≤ (s : ℤ) then some s else none
  | k + 1, s =>
    if e + (scale : ℤ) * (a + 1 : ℕ) ≤ (s : ℤ) then
      checkPsiTicks tick e (a + 1) k (s + tick (a + 1))
    else none

private theorem psi_tick_cell {a s : ℕ} {e : ℤ} {x u : ℝ} (hs : (s : ℝ) ≤ scale * Chebyshev.psi a)
    (he : (e : ℝ) + scale * u ≤ s) (ha : (a : ℝ) ≤ x) (hx : x ≤ u) :
    (e : ℝ) / scale ≤ Chebyshev.psi x - x := by
  have hscale : 0 < (scale : ℝ) := Nat.cast_pos.mpr (by decide : 0 < scale)
  have hp := mul_le_mul_of_nonneg_left (Chebyshev.psi_mono ha) hscale.le
  rw [div_le_iff₀ hscale, sub_mul, mul_comm (Chebyshev.psi x), mul_comm x]
  linarith only [he, hs, hp, mul_le_mul_of_nonneg_left hx hscale.le]

private theorem check_psi_ticks_sound (tick : ℕ → ℕ) (e : ℤ) (a k s t : ℕ)
    (hs : (s : ℝ) ≤ scale * Chebyshev.psi a)
    (ht : ∀ n, a < n → n ≤ a + k → (tick n : ℝ) ≤ scale * ArithmeticFunction.vonMangoldt n)
    (hc : checkPsiTicks tick e a k s = some t) :
    (t : ℝ) ≤ scale * Chebyshev.psi (a + k : ℕ) ∧
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (a + k : ℕ) → (e : ℝ) / scale ≤ Chebyshev.psi x - x := by
  induction k generalizing a s with
  | zero =>
    rw [checkPsiTicks] at hc
    split at hc
    next h =>
      have he := Option.some.inj hc
      subst t
      refine ⟨by simpa only [Nat.add_zero] using hs, ?_⟩
      intro x ha hx
      exact
        psi_tick_cell (u := (a : ℝ)) hs (by exact_mod_cast h) ha
          (by simpa only [Nat.add_zero] using hx)
    next _ => cases hc
  | succ k ih =>
    rw [checkPsiTicks] at hc
    split at hc
    next h =>
      have he : a + (k + 1) = (a + 1) + k := by rw [Nat.add_assoc, Nat.add_comm 1 k]
      have hstep :=
        ht (a + 1) (Nat.lt_succ_self a) (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) a)
      have hs' : ((s + tick (a + 1) : ℕ) : ℝ) ≤ scale * Chebyshev.psi (a + 1 : ℕ) := by
        rw [Nat.cast_add, psi_next, mul_add]
        exact add_le_add hs hstep
      have hrest :=
        ih (a + 1) _ hs' (fun n hn hnk ↦ ht n ((Nat.le_succ a).trans_lt hn) (he ▸ hnk)) hc
      rw [he]
      refine ⟨hrest.1, ?_⟩
      intro x ha hx
      by_cases hxu : x ≤ (a + 1 : ℕ)
      · exact psi_tick_cell hs (by exact_mod_cast h) ha hxu
      · exact hrest.2 x (le_of_not_ge hxu) hx
    next _ => cases hc

/-- Check the signed floor throughout the block and return the outgoing
fixed-point prefix on success. The sieve and the prefix scan each run once. -/
public def signedPsiScan (a b s : ℕ) (e : ℤ) : Option ℕ :=
  let base := extendedMangoldtBase (a + 1) (b + 1)
  checkPsiTicks (fun n ↦ lowerLogTick (base n)) e a (b - a) s

/-- A successful scan certifies both the outgoing prefix and the signed
floor on the closed real interval, so the next block can reuse the prefix. -/
public theorem signed_psi_scan_sound {a b s t : ℕ} {e : ℤ} (hab : a ≤ b) (hb : b ≤ 1600000)
    (hs : (s : ℝ) ≤ scale * Chebyshev.psi a) (hc : signedPsiScan a b s e = some t) :
    (t : ℝ) ≤ scale * Chebyshev.psi b ∧
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → (e : ℝ) / scale ≤ Chebyshev.psi x - x := by
  let tick := fun n ↦ lowerLogTick (extendedMangoldtBase (a + 1) (b + 1) n)
  have ht (n : ℕ) (hn : a < n) (hnb : n ≤ a + (b - a)) :
    (tick n : ℝ) ≤ scale * ArithmeticFunction.vonMangoldt n := by
    rw [Nat.add_sub_of_le hab] at hnb
    have he := extended_mangoldt_weight hn (Nat.lt_succ_of_le hnb) (hnb.trans hb)
    simpa only [tick, he] using lower_log_tick_le (extendedMangoldtBase (a + 1) (b + 1) n)
  simpa only [Nat.add_sub_of_le hab] using check_psi_ticks_sound tick e a (b - a) s t hs ht hc

/-- Return whether the block scan certifies the signed floor. -/
public def signedPsiCheck (a b s : ℕ) (e : ℤ) : Bool :=
  (signedPsiScan a b s e).isSome

/-- A successful Boolean scan certifies the floor on the closed real interval. -/
public theorem signed_psi_check_sound {a b s : ℕ} {e : ℤ} (hab : a ≤ b) (hb : b ≤ 1600000)
    (hs : (s : ℝ) ≤ scale * Chebyshev.psi a) (hc : signedPsiCheck a b s e = true) {x : ℝ}
    (ha : (a : ℝ) ≤ x) (hx : x ≤ b) : (e : ℝ) / scale ≤ Chebyshev.psi x - x := by
  cases he : signedPsiScan a b s e with
  | none => simp only [signedPsiCheck, he, Option.isSome_none, Bool.false_eq_true] at hc
  | some t => exact (signed_psi_scan_sound hab hb hs he).2 x ha hx

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
