/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.DirectPrimeCount
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.EnvelopeTransfer

/-! # Scalar certificates for direct lower theta segments -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- A balanced least common multiple of the integers in a dyadic interval starting at s. -/
def divisorBase (d s : ℕ) : ℕ :=
  match d with
  | 0 => s
  | k + 1 => (divisorBase k s).lcm (divisorBase k (s + 2 ^ k))

/-- The balanced base is divisible by each integer in its half-open defining interval. -/
theorem dvd_divisorBase (d s m : ℕ) (hl : s ≤ m) (hr : m < s + 2 ^ d) : m ∣ divisorBase d s := by
  induction d generalizing s with
  | zero => exact (Nat.le_antisymm (Nat.le_of_lt_succ hr) hl) ▸ dvd_refl s
  | succ d ih =>
    rw [divisorBase]
    by_cases h : m < s + 2 ^ d
    · exact (ih s hl h).trans (Nat.dvd_lcm_left _ _)
    · apply Dvd.dvd.trans _ (Nat.dvd_lcm_right _ _)
      apply ih _ (Nat.le_of_not_lt h)
      simpa only [pow_succ, Nat.mul_two, Nat.add_assoc] using hr

/-- An entry theta lower bound implies an exit lower bound and real-interval coverage. -/
def ThetaLowerSegment (a b : ℕ) (e f : ℚ) : Prop :=
  (e : ℝ) ≤ Chebyshev.theta a →
    (f : ℝ) ≤ Chebyshev.theta b ∧
      ∀ x : ℝ,
        (a : ℝ) ≤ x →
          x ≤ (b : ℝ) →
          (x - Chebyshev.theta x) / Real.sqrt x ≤
            Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)

/-- Adjacent closed segments compose when the left exit supplies the right entry. -/
theorem ThetaLowerSegment.join {a b c : ℕ} {e f g : ℚ} (hl : ThetaLowerSegment a b e f)
    (hr : ThetaLowerSegment b c f g) : ThetaLowerSegment a c e g := by
  intro h
  obtain ⟨hf, hleft⟩ := hl h
  obtain ⟨hg, hright⟩ := hr hf
  refine ⟨hg, fun x hx hy => ?_⟩
  rcases le_total x (b : ℝ) with hb | hb
  · exact hleft x hx hb
  · exact hright x hb hy

/-- Certify a dyadic tile from a shared factor base, a prime count and rational endpoint bounds.
The logarithmic floor establishes the gain, and the square-root floor establishes real coverage. -/
theorem theta_segment_of_count {P B : ℕ} (cover : ∀ m, 2 ≤ m → m ≤ B → m ∣ P) (a b t d k w r : ℕ)
    (e f q : ℚ) (ha : 1000000 ≤ a) (hb : b < (B + 1) * (B + 1)) (he : a + 2 ^ (t + d) = b)
    (hc : tiledPrimeCount P w t d a = k) (hs : r ^ 2 ≤ a) (hq : (q : ℝ) ≤ Real.log a)
    (hf : f ≤ e + k * q) (hw : (b : ℚ) ≤ e + 5 * r) : ThetaLowerSegment a b e f := by
  intro hentry
  have ha1 : 1 ≤ a := (by decide : 1 ≤ 1000000).trans ha
  have hg := tiled_prime_increment w t d a a ha1 le_rfl (he ▸ hb) cover
  rw [he, hc] at hg
  have hk := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg (α := ℝ) k)
  have hf' := (Rat.cast_le (K := ℝ)).2 hf
  have hw' := (Rat.cast_le (K := ℝ)).2 hw
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at hf' hw'
  refine ⟨by linarith only [hf', hk, hg, hentry], fun x hax hxb => ?_⟩
  have hx : 1000000 ≤ x := (show (1000000 : ℝ) ≤ a by exact_mod_cast ha).trans hax
  have hr := Real.le_sqrt_of_sq_le ((show (r : ℝ) ^ 2 ≤ a by exact_mod_cast hs).trans hax)
  have ht : (5 : ℝ) ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) :=
    Joint.coefficient_from_ticks (n := 1000000) (m := 13000) (by decide) hx (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only)
  apply le_trans _ ht
  apply (div_le_iff₀ (Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num only) hx))).2
  linarith only [hw', hr, hxb, hentry, Chebyshev.theta_mono hax]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
