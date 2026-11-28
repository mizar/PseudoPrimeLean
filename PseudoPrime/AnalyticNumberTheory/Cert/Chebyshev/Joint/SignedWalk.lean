/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Signed lower bounds from a joint Chebyshev walk -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Check a signed lower bound in fixed-point ticks at every cursor of a
local walk. Each cursor uses the sum through its preceding integer. -/
def signedWalk (step : Edge → Edge) (lower : ℕ → ℤ) : ℕ → Edge → Bool
  | 0, _ => true
  | k + 1, s =>
    decide (lower s.n + (scale : ℤ) * s.n ≤ (s.psiLo : ℤ)) && signedWalk step lower k (step s)

/-- A successful signed walk covers each closed interval between successive
integers. Positivity of the Mangoldt terms extends the prefix lower bound
across the interval. -/
theorem signed_walk_sound {a b : ℕ} (lower : ℕ → ℤ) (k : ℕ) (s : Edge) (hs : Valid s) (ha : a ≤ s.n)
    (hb : s.n + k ≤ b) (hu : b ≤ 1000001) (hc : signedWalk (gcdStep a b) lower k s = true) :
    ∀ n,
      s.n ≤ n →
        n < s.n + k →
        ∀ x : ℝ, (↑(n - 1) : ℝ) ≤ x → x ≤ n → (lower n : ℝ) / scale ≤ Chebyshev.psi x - x := by
  induction k generalizing s with
  | zero =>
    intro n hn hlt
    exact False.elim ((Nat.not_lt_of_ge hn) (Nat.add_zero s.n ▸ hlt))
  | succ k ih =>
    intro n hn hlt x hx hy
    rw [signedWalk, Bool.and_eq_true_iff] at hc
    rcases eq_or_lt_of_le hn with he | hlt'
    · subst n
      have h := hs.2.psiLo
      have hC : (lower s.n : ℝ) + (scale : ℝ) * (s.n : ℝ) ≤ (s.psiLo : ℝ) := by
        exact_mod_cast (of_decide_eq_true hc.1 : lower s.n + (scale : ℤ) * s.n ≤ (s.psiLo : ℤ))
      have hm := mul_le_mul_of_nonneg_left (Chebyshev.psi_mono hx) (Nat.cast_nonneg scale)
      have hp : (0 : ℝ) < scale := by norm_num only [scale, Nat.cast_ofNat]
      apply (div_le_iff₀ hp).mpr
      linarith only [hC, h, hm, mul_le_mul_of_nonneg_left hy hp.le]
    · have ht := walk_valid (a := a) (b := b) 1 s hs ha (by linarith only [hb]) hu
      change (segmentStep a b s).n = s.n + 1 ∧ Valid (segmentStep a b s) at ht
      rw [← gcdStep_eq] at ht
      exact
        ih (gcdStep a b s) ht.2 (by linarith only [ha, ht.1]) (by linarith only [hb, ht.1]) hc.2 n
          (by linarith only [hlt', ht.1]) (by linarith only [hlt, ht.1]) x hx hy

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
