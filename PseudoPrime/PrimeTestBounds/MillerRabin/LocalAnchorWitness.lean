/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenWitness

/-! # Certified local correction anchors and witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational radii, strict correction lower bounds and logarithm scales for
the eight local intervals from scale 15 to 39.4. These anchors are consumed
by the local witness theorem after their correction checks are verified. -/
def localCorrectionAnchors : List (ℚ × ℚ × ℕ) :=
  [(8, 324969 / 100000, 3), (12, 193673 / 50000, 4), (16, 85669 / 20000, 4),
    (19, 452097 / 100000, 5), (20, 5739 / 1250, 5), (21, 465779 / 100000, 5),
    (107 / 5, 9367 / 2000, 5), (43 / 2, 93797 / 20000, 5)]

set_option maxRecDepth 8192 in
/-- Each local correction exceeds its rational anchor. Kernel evaluation
checks an additional positive margin using the existing logarithm certificates. -/
theorem localCorrectionAnchors_checked :
    localCorrectionAnchors.all (fun x ↦ localCorrectionCheck x.1 (x.2.1 + 1 / 10000000) x.2.2) =
      true := by
  decide +kernel

/-- A listed correction is strictly below the even endpoint correction at its
radius. The checked positive margin converts the rational certificate to a
strict real inequality for the local witness theorem. -/
theorem localCorrectionAnchor_lt {b d : ℚ} {j : ℕ} (hm : (b, d, j) ∈ localCorrectionAnchors) :
    (d : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (b : ℝ) := by
  have hc := (List.all_eq_true.mp localCorrectionAnchors_checked) (b, d, j) hm
  have h := localCorrectionCheck_sound hc
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  linarith only [h]

/-- Under GRH, any listed anchor bounds a rejecting prime when all passing
residues belong to a proper subgroup at a divisor with logarithm at most `s`.
The finite certificate supplies the hypotheses of the local shift theorem. -/
theorem exists_prime_reject_local_anchor {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b d : ℚ} {j : ℕ}
    (hm : (b, d, j) ∈ localCorrectionAnchors) {s : ℝ} (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (max (b : ℝ) (s - d)) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hc := (List.all_eq_true.mp localCorrectionAnchors_checked) (b, d, j) hm
  have hbq : (8 : ℚ) ≤ b := (of_decide_eq_true hc).1
  have hb : (8 : ℝ) ≤ b := by exact_mod_cast hbq
  exact
    exists_prime_reject_of_local_shift hn ho hqn H hH hpass hGRH hb (localCorrectionAnchor_lt hm) hs

end PseudoPrime.PrimeTestBounds.MillerRabin
