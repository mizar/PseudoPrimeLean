/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenNumerics

/-! # Certified anchors for the local even-character envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The twenty rational radii, corrections and binary logarithm scales used
for the local even-character envelope. Each correction has an additional
positive margin in the certificate checked below. -/
def localEvenAnchors : List (ℚ × ℚ × ℕ) :=
  [(8, 324969 / 100000, 3), (12, 193673 / 50000, 4), (16, 85669 / 20000, 4),
    (24, 241969 / 50000, 5), (32, 65379 / 12500, 5), (48, 579107 / 100000, 6),
    (64, 310121 / 50000, 6), (96, 680743 / 100000, 7), (128, 725627 / 100000, 7),
    (160, 76157 / 10000, 8), (192, 158329 / 20000, 8), (208, 402521 / 50000, 8),
    (216, 811399 / 100000, 8), (220, 814499 / 100000, 8), (222, 81603 / 10000, 8),
    (224, 204387 / 25000, 8), (256, 420161 / 50000, 8), (320, 879033 / 100000, 9),
    (512, 192591 / 20000, 9), (1024, 1091423 / 100000, 10)]

set_option maxRecDepth 8192 in
/-- Every local anchor passes the exact rational correction check with a
positive margin of one ten-millionth. Kernel reduction checks the finite list;
the soundness theorem transfers these checks to real corrections. -/
theorem localEvenAnchors_checked :
    localEvenAnchors.all (fun x ↦ localCorrectionCheck x.1 (x.2.1 + 1 / 10000000) x.2.2) =
      true := by
  decide +kernel

/-- Every listed rational correction is strictly below the even endpoint
correction at its radius. The checked rational margin gives strictness after
casting to the reals. This supplies the finite local envelope candidates. -/
theorem localEvenAnchor_lt {b d : ℚ} {j : ℕ} (hm : (b, d, j) ∈ localEvenAnchors) :
    (d : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (b : ℝ) := by
  have hc := (List.all_eq_true.mp localEvenAnchors_checked) (b, d, j) hm
  have h := localCorrectionCheck_sound hc
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  linarith only [h]

/-- Under GRH, every listed anchor bounds a prime rejecting an odd input whose
local passing residues lie in a proper subgroup at a divisor `q` with `log q ≤ s`.
The finite check supplies the radius domain and strict correction margin; the
general local transfer supplies the actual rejecting prime. -/
theorem exists_prime_reject_of_local_anchor {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b d : ℚ} {j : ℕ}
    (hm : (b, d, j) ∈ localEvenAnchors) {s : ℝ} (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (max (b : ℝ) (s - d)) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hc := (List.all_eq_true.mp localEvenAnchors_checked) (b, d, j) hm
  have hbq : (8 : ℚ) ≤ b := (of_decide_eq_true hc).1
  have hb : (8 : ℝ) ≤ b := by exact_mod_cast hbq
  exact exists_prime_reject_of_local_shift hn ho hqn H hH hpass hGRH hb (localEvenAnchor_lt hm) hs

end PseudoPrime.PrimeTestBounds.MillerRabin
