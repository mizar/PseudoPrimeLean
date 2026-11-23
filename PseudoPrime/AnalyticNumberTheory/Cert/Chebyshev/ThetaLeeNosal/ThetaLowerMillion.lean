/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighMillion
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment

/-! # Certified lower theta bound immediately above one million -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Multiply consecutive integers in a balanced tree. -/
private def product : Nat → Nat → Nat
  | 0, s => s
  | d + 1, s => product d s * product d (s + 2 ^ d)

/-- Every integer in the subtree divides its product. -/
private theorem dvd_product (d s m : Nat) (lo : s ≤ m) (hi : m < s + 2 ^ d) : m ∣ product d s := by
  induction d generalizing s with
  | zero =>
    have h : m = s := Nat.le_antisymm (Nat.le_of_lt_succ hi) lo
    exact h ▸ dvd_refl s
  | succ d ih =>
    by_cases h : m < s + 2 ^ d
    · exact dvd_mul_of_dvd_left (ih s lo h) _
    · have e : s + 2 ^ (d + 1) = s + 2 ^ d + 2 ^ d := by rw [pow_succ, Nat.mul_two, Nat.add_assoc]
      exact dvd_mul_of_dvd_right (ih _ (Nat.le_of_not_lt h) (e ▸ hi)) _

/-- Coprimality to a product containing all possible small divisors proves primality. -/
private theorem prime_of_coprime {n P B : Nat} (hn : 2 ≤ n) (hs : n.sqrt ≤ B)
    (cover : ∀ m, 2 ≤ m → m ≤ B → m ∣ P) (hc : n.gcd P = 1) : n.Prime :=
  Nat.prime_def_le_sqrt.mpr
    ⟨hn, fun m hm hms hmn => by
      have hd := Nat.dvd_gcd hmn (cover m hm (hms.trans hs))
      exact (Nat.ne_of_gt hm) (Nat.eq_one_of_dvd_one (hc ▸ hd))⟩

/-- Count coprime integers above the left endpoint, including the right endpoint. -/
private def count (P top : Nat) : Nat → Nat → Nat
  | 0, a => if a + 1 ≤ top ∧ (a + 1).gcd P = 1 then 1 else 0
  | d + 1, a => count P top d a + count P top d (a + 2 ^ d)

/-- Transport the scalar count into a lower theta increment by splitting the interval. -/
private theorem lower {P top : Nat} (ok : ∀ n, 2 ≤ n → n ≤ top → n.gcd P = 1 → n.Prime)
    (d a lo : Nat) (hlo : 1 ≤ lo) (ha : lo ≤ a) :
    (count P top d a : ℝ) * Real.log lo ≤
      Chebyshev.theta (a + 2 ^ d : Nat) - Chebyshev.theta a := by
  induction d generalizing a with
  | zero =>
    by_cases h : a + 1 ≤ top ∧ (a + 1).gcd P = 1
    · have hp := ok (a + 1) (Nat.succ_le_succ (hlo.trans ha)) h.1 h.2
      have he :=
        PseudoPrime.AnalyticNumberTheory.Arithmetic.theta_prefix_add_interval (Nat.le_succ a)
      simp only [Nat.Ioc_succ_singleton, Finset.filter_singleton, hp, ite_true,
        Finset.sum_singleton] at he
      have hl :=
        Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hlo) : (0 : ℝ) < lo)
          (Nat.cast_le.mpr (ha.trans (Nat.le_succ a)))
      simp only [count, ite_eq_left h, Nat.cast_one, one_mul, pow_zero]
      simp only [Nat.succ_eq_add_one] at he hl
      rw [← he, add_sub_cancel_left]
      exact hl
    · simp only [count, ite_eq_right h, Nat.cast_zero, zero_mul, pow_zero, sub_nonneg]
      exact Chebyshev.theta_mono (Nat.cast_le.mpr (Nat.le_succ a))
  | succ d ih =>
    have h₁ := ih a ha
    have h₂ := ih (a + 2 ^ d) (ha.trans (Nat.le_add_right _ _))
    rw [count, Nat.cast_add, add_mul, pow_succ, Nat.mul_two, ← Nat.add_assoc]
    linarith only [h₁, h₂]

/-- Shared integer product for the first direct cell. -/
private def common : Nat :=
  [0x0000000000000000000000000002022f598887b1b677793eea7338140b96,
        0xedd924fcab3a183421f3dcfe257e91fdb9fbda6fdc765c78087e0afb0469,
        0xee9dc04e88b57dbc8a8850c431640a70a5553f274cf95cf31ef50ff773bb,
        0x46b4f14badbef976885d017edb30ca9d17100464466d8e2c424c4eb35a8a,
        0xd96698ab9da18c5941a808585b16d700ea60fe4742b55d151d2fa72fb531,
        0x4bf93374f6ba357b7e7b81928b2fcef3b564380dc3bd2d0d3580a28d5aea,
        0xd0d707cdd521cb09f953e45849e4ea04445db770f4473bfd62494ba215e1,
        0x370df02adb30f0aec0dc9adccc96284cf6d8ffed1dd2833033d53dbb87f6,
        0x02c4c286f1c03b25795d45d8fd8d989a47ec52b856055b878c7329f655f4,
        0x87052c38bcd4a790b30277c68153bcb18a167e393143051e069b23b51d05,
        0xcb8b0040c7086c76707d0d69400443d00223aaa1c24dc6aa22eeb60f1402,
        0xefea0babf3f916fe20dfeca617d4a72b2818db64445eb896f589524c9803,
        0xc6b97c05803e5333357ef9281627249eba91582c91ef846f3f0a84b92a07,
        0x9c62b33dd2419af649fbcc579686ae8fb54746b82b83fc3402833941f035,
        0xb655216b02bb7a0b42ba292f70af8fd3c6922a2c065dd523c7723b37f1bb,
        0xa4f2411f9d917091b4c99c676242826777b15c868fa3e528596e5ce1ebe1,
        0x634565a393a60c8d7daaa16b1bd7679f6f5e923569eefc0fbcea6da292fe,
        0xf18f19bc4b6306fc70161c9f19b75c55710ddd3a2d4edfa892b7184e2a60,
        0x1bf85b047b9b256a8338739e257ee896dadbfa43e08360591f78cd6a3d40,
        0xe8c04beebd2e22f357d2fcf22ec25cb48ed2cee17f7a638ce99a83b6db18,
        0xa25e6418e162c55479577a5b781703c46174b9b929095e732845329dde20,
        0xb46d0ec7e74e90aff69906f485a24d40bae6190296d0218ce544d19db6fc,
        0xdc55a624493b698ecbb01751e1a1ad46d2cf590df06e631bb6048680bd61,
        0x6f3e4d80b5c562d5660cf611154ad88ef87290d24ba9e89eebc2fd3cce85,
        0x60a034f23134f9813c48debd014e2ccda5d947ecf35e2f40464199f5fa75,
        0x900d1a2c47c50d1982caea69002fb8057c97f6eec6e1040202741885d11a,
        0xd136965f70bbaa24ee85dd09dace0b2bc1008b3180a501be1e791f016fbf,
        0x750ce18f1a4352b2caf0f01fa1d7020ea70f9bb3cdfce1b26b73172809e1,
        0xdfa5ef33f4c89a3f6e4219d024f29cf91ecf25ae7620cdd6453351bf2e64,
        0xe97212b56d7bdeb9c7fa700468ab881cda84380998f47e46a537948431b4,
        0x7f258fd092c739d207eeb3b91fe231adab484d6161b750c2cd6f77f650f7,
        0x6a8deac564d2da13a26650ee9aa992797601b1629d7ac4e540699eeb6618,
        0x3724dede658673e0a3b3b5c06a3c741c1c4aa746d7458000000000000000,
        0x000000000000000000000000000000000000000000000000000000000000,
        0x000000000000000000000000000000000000000000000000000000000000,
        0x000000000000000000000000000000000000000000000000000000000000,
        0x000000000000000000000000000000000000000000000000000000000000].foldl
    (fun n c => n * 2 ^ 240 + c) 0

/-- Check the shared integer against its balanced multiplication tree. -/
private theorem common_eq : product 10 1 = common := by decide +kernel

/-- Exclude every possible small divisor of a counted integer. -/
private theorem valid {n : Nat} (hn : 2 ≤ n) (hb : n ≤ 1002048) (hc : n.gcd common = 1) : n.Prime :=
  prime_of_coprime hn
    ((Nat.sqrt_le_sqrt hb).trans
      (Nat.le_of_lt_succ (Nat.sqrt_lt.mpr (by decide : 1002048 < 1025 * 1025))))
    (fun m hm h => common_eq ▸ dvd_product 10 1 m (Nat.le_of_lt hm) (Nat.lt_succ_of_le h)) hc

/-- Recompute the 153 admissible integers in the first 2048 positions. -/
private theorem computed : count common 1002048 11 1000000 = 153 := by decide +kernel

/-- Give a uniform lower logarithm at the first endpoint. -/
private theorem log_lower : (12 : ℝ) ≤ Real.log 1000000 := by
  apply (Real.le_log_iff_exp_le (by norm_num only)).2
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 12
  rw [← Real.exp_natCast_mul] at h
  norm_num only [Nat.cast_ofNat, mul_one] at h
  exact h.trans (by norm_num only)

/-- Recover the certified theta entrance from the million theorem. -/
private theorem entry : (998060 : ℝ) ≤ Chebyshev.theta 1000000 := by
  have h :=
    PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.high_closed
      PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.prefix3500.1
      PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.high_million (x := 1000000)
      (by norm_num only) le_rfl
  have hl := (abs_le.mp h.2).1
  have hs : Real.sqrt 1000000 = 1000 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num only) (by norm_num only)).2 (by norm_num only)
  rw [hs] at hl
  linarith only [hl]

/-- Add the verified prime logarithms to the entrance value. -/
private theorem exit_bound : (999896 : ℝ) ≤ Chebyshev.theta 1002048 := by
  have h :=
    lower (P := common) (top := 1002048) (fun _ => valid) 11 1000000 1000000 (by decide) le_rfl
  rw [computed] at h
  change (153 : ℝ) * Real.log 1000000 ≤ Chebyshev.theta 1002048 - Chebyshev.theta 1000000 at h
  linarith only [entry, log_lower, h]

/-- Compare the constant five with the Lee–Nosal coefficient. -/
private theorem coeff {x : ℝ} (hx : 1000000 ≤ x) :
    5 ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) :=
  PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.coefficient_from_ticks (n := 1000000) (m :=
    13000) (by decide) hx (by decide +kernel) (by norm_num only) (by norm_num only)
    (by norm_num only)

/-- The two joined real cells above one million satisfy the lower Lee–Nosal bound. -/
theorem theta_lower_million_1004800 {x : ℝ} (hx : 1000000 ≤ x) (hy : x ≤ 1004800) :
    (x - Chebyshev.theta x) / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  have hs : 1000 ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le ((by norm_num only : (1000 : ℝ) ^ 2 ≤ 1000000).trans hx)
  have hd : x - Chebyshev.theta x ≤ 5 * Real.sqrt x := by
    rcases le_total x 1002048 with h | h
    · linarith only [entry, Chebyshev.theta_mono hx, hs, h]
    · linarith only [exit_bound, Chebyshev.theta_mono h, hs, hy]
  exact ((div_le_iff₀ (by linarith only [hs])).2 hd).trans (coeff hx)

/-- Join the finite bound below one million to the two lower-bound cells above it. -/
theorem theta_lower_2657_1004800 {x : ℝ} (hx : 2657 ≤ x) (hy : x ≤ 1004800) :
    (x - Chebyshev.theta x) / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  rcases le_total x 1000000 with h | h
  · have hp := Joint.theta_million_of_segment Joint.high_million hx h
    have he := (neg_le_abs (Chebyshev.theta x - x))
    rw [neg_sub] at he
    exact (div_le_div_of_nonneg_right he (Real.sqrt_nonneg x)).trans hp
  · exact theta_lower_million_1004800 h hy

/-- All primes counted in this range contribute at least 69/5 to theta. -/
private theorem million_log_floor : (69 / 5 : ℝ) ≤ Real.log 1000000 := by
  have h :=
    PseudoPrime.Analysis.rationalLogIntervalCheck_sound
      (show PseudoPrime.Analysis.rationalLogIntervalCheck 1000000 20 12 (69 / 5) 14 = true from by
        decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h.1

/-- A scalar coprime count and two rational budget checks certify a dyadic real segment. -/
private theorem direct_tile (a t d b k : ℕ) (e f : ℚ) (heq : a + 2 ^ (t + d) = b) (ha : 1000000 ≤ a)
    (hb : b < 1025 * 1025) (hc : tiledPrimeCount common 200560490130 t d a = k)
    (hf : f ≤ e + k * (69 / 5)) (hw : (b : ℚ) ≤ e + 5000) : ThetaLowerSegment a b e f := by
  apply
    theta_segment_of_count (P := common) (B := 1024)
      (fun m hm hm' => common_eq ▸ dvd_product 10 1 m (Nat.le_of_lt hm) (Nat.lt_succ_of_le hm')) a b
      t d k 200560490130 1000 e f (69 / 5) ha hb heq hc
      (by
        norm_num only; exact ha)
      _ hf
      (by
        norm_num only [Nat.cast_ofNat]; exact hw)
  have h :=
    million_log_floor.trans
      (Real.log_le_log (by norm_num only : (0 : ℝ) < 1000000)
        (by exact_mod_cast ha : (1000000 : ℝ) ≤ a))
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

private theorem direct1000000 : ThetaLowerSegment 1000000 1002048 998060 (5000857 / 5) := by
  exact
    direct_tile 1000000 7 4 1002048 153 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1002048 : ThetaLowerSegment 1002048 1004096 (5000857 / 5) (5011828 / 5) := by
  exact
    direct_tile 1002048 7 4 1004096 159 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1004096 : ThetaLowerSegment 1004096 1006144 (5011828 / 5) 1004270 := by
  exact
    direct_tile 1004096 7 4 1006144 138 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1006144 : ThetaLowerSegment 1006144 1008192 1004270 (5032459 / 5) := by
  exact
    direct_tile 1006144 7 4 1008192 161 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1008192 : ThetaLowerSegment 1008192 1010240 (5032459 / 5) (5043154 / 5) := by
  exact
    direct_tile 1008192 7 4 1010240 155 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1010240 : ThetaLowerSegment 1010240 1012288 (5043154 / 5) (5053366 / 5) := by
  exact
    direct_tile 1010240 7 4 1012288 148 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1012288 : ThetaLowerSegment 1012288 1014336 (5053366 / 5) 1012757 := by
  exact
    direct_tile 1012288 7 4 1014336 151 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1014336 : ThetaLowerSegment 1014336 1016384 1012757 (5074066 / 5) := by
  exact
    direct_tile 1014336 7 4 1016384 149 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1016384 : ThetaLowerSegment 1016384 1018432 (5074066 / 5) (5083657 / 5) := by
  exact
    direct_tile 1016384 7 4 1018432 139 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1018432 : ThetaLowerSegment 1018432 1020480 (5083657 / 5) 1018898 := by
  exact
    direct_tile 1018432 7 4 1020480 157 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1020480 : ThetaLowerSegment 1020480 1022528 1018898 (5105254 / 5) := by
  exact
    direct_tile 1020480 7 4 1022528 156 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1022528 : ThetaLowerSegment 1022528 1024576 (5105254 / 5) (5114776 / 5) := by
  exact
    direct_tile 1022528 7 4 1024576 138 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1024576 : ThetaLowerSegment 1024576 1026624 (5114776 / 5) (5125609 / 5) := by
  exact
    direct_tile 1024576 7 4 1026624 157 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1026624 : ThetaLowerSegment 1026624 1028672 (5125609 / 5) (5135683 / 5) := by
  exact
    direct_tile 1026624 7 4 1028672 146 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1028672 : ThetaLowerSegment 1028672 1030720 (5135683 / 5) (5145619 / 5) := by
  exact
    direct_tile 1028672 7 4 1030720 144 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1030720 : ThetaLowerSegment 1030720 1032768 (5145619 / 5) (5155417 / 5) := by
  exact
    direct_tile 1030720 7 4 1032768 142 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1032768 : ThetaLowerSegment 1032768 1034816 (5155417 / 5) 1033181 := by
  exact
    direct_tile 1032768 7 4 1034816 152 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1034816 : ThetaLowerSegment 1034816 1036864 1033181 1035251 := by
  exact
    direct_tile 1034816 7 4 1036864 150 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1036864 : ThetaLowerSegment 1036864 1038912 1035251 (5186053 / 5) := by
  exact
    direct_tile 1036864 7 4 1038912 142 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1038912 : ThetaLowerSegment 1038912 1040960 (5186053 / 5) 1039184 := by
  exact
    direct_tile 1038912 7 4 1040960 143 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1040960 : ThetaLowerSegment 1040960 1043008 1039184 (5205994 / 5) := by
  exact
    direct_tile 1040960 7 4 1043008 146 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1043008 : ThetaLowerSegment 1043008 1045056 (5205994 / 5) (5216689 / 5) := by
  exact
    direct_tile 1043008 7 4 1045056 155 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1045056 : ThetaLowerSegment 1045056 1047104 (5216689 / 5) 1045256 := by
  exact
    direct_tile 1045056 7 4 1047104 139 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1047104 : ThetaLowerSegment 1047104 1049152 1045256 (5236837 / 5) := by
  exact
    direct_tile 1047104 7 4 1049152 153 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1049152 : ThetaLowerSegment 1049152 1050176 (5236837 / 5) (5241943 / 5) := by
  exact
    direct_tile 1049152 7 3 1050176 74 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1050176 : ThetaLowerSegment 1050176 1050432 (5241943 / 5) 1048637 := by
  exact
    direct_tile 1050176 7 1 1050432 18 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1050432 : ThetaLowerSegment 1050432 1050560 1048637 (5243737 / 5) := by
  exact
    direct_tile 1050432 7 0 1050560 8 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem direct1050560 : ThetaLowerSegment 1050560 1050624 (5243737 / 5) (5243944 / 5) := by
  exact
    direct_tile 1050560 6 0 1050624 3 _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem first_direct_segment : ThetaLowerSegment 1000000 1050624 998060 (5243944 / 5) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join (ThetaLowerSegment.join direct1000000 direct1002048)
            (ThetaLowerSegment.join direct1004096 direct1006144))
          (ThetaLowerSegment.join (ThetaLowerSegment.join direct1008192 direct1010240)
            (ThetaLowerSegment.join direct1012288 direct1014336)))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join (ThetaLowerSegment.join direct1016384 direct1018432)
            (ThetaLowerSegment.join direct1020480 direct1022528))
          (ThetaLowerSegment.join (ThetaLowerSegment.join direct1024576 direct1026624)
            (ThetaLowerSegment.join direct1028672 direct1030720))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join (ThetaLowerSegment.join direct1032768 direct1034816)
            (ThetaLowerSegment.join direct1036864 direct1038912))
          (ThetaLowerSegment.join (ThetaLowerSegment.join direct1040960 direct1043008)
            (ThetaLowerSegment.join direct1045056 direct1047104)))
        (ThetaLowerSegment.join (ThetaLowerSegment.join direct1049152 direct1050176)
          (ThetaLowerSegment.join direct1050432 direct1050560))))

/-- Exit lower bound supplied to the next directly certified segment. -/
theorem theta_entry_1050624 : ((5243944 / 5) : ℝ) ≤ Chebyshev.theta 1050624 := by
  have h := first_direct_segment (by simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using entry)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using h.1

/-- The direct prime counts extend the unconditional lower estimate to 1050624. -/
theorem theta_lower_2657_1050624 {x : ℝ} (hx : 2657 ≤ x) (hy : x ≤ 1050624) :
    (x - Chebyshev.theta x) / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  rcases le_total x 1000000 with h | h
  · exact theta_lower_2657_1004800 hx (h.trans (by norm_num only))
  exact
    (first_direct_segment (by simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using entry)).2 x
      (by simpa only [Nat.cast_ofNat] using h) (by simpa only [Nat.cast_ofNat] using hy)

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
