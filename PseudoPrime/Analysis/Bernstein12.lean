/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.BernsteinBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Power-to-Bernstein conversion in degree twelve -/

public section

namespace PseudoPrime.Analysis

/-- The degree-twelve power polynomial equals the displayed linear combination of
Bernstein basis functions on the unit interval. The coefficients implement the
standard power-to-Bernstein transform. This identity is shared by all degree-twelve
finite interval certificates. -/
theorem bernstein12_power_identity (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : ℝ)
    (t : Set.Icc (0 : ℝ) 1) :
    a0 + a1 * (t : ℝ) ^ 1 + a2 * (t : ℝ) ^ 2 + a3 * (t : ℝ) ^ 3 + a4 * (t : ℝ) ^ 4 +
        a5 * (t : ℝ) ^ 5 +
        a6 * (t : ℝ) ^ 6 +
        a7 * (t : ℝ) ^ 7 +
        a8 * (t : ℝ) ^ 8 +
        a9 * (t : ℝ) ^ 9 +
        a10 * (t : ℝ) ^ 10 +
        a11 * (t : ℝ) ^ 11 +
        a12 * (t : ℝ) ^ 12 =
      (a0) * bernstein 12 0 t + (a0 + (1 / 12 : ℝ) * a1) * bernstein 12 1 t +
        (a0 + (2 / 12 : ℝ) * a1 + (1 / 66 : ℝ) * a2) * bernstein 12 2 t +
        (a0 + (3 / 12 : ℝ) * a1 + (3 / 66 : ℝ) * a2 + (1 / 220 : ℝ) * a3) * bernstein 12 3 t +
        (a0 + (4 / 12 : ℝ) * a1 + (6 / 66 : ℝ) * a2 + (4 / 220 : ℝ) * a3 + (1 / 495 : ℝ) * a4) *
          bernstein 12 4 t +
        (a0 + (5 / 12 : ℝ) * a1 + (10 / 66 : ℝ) * a2 + (10 / 220 : ℝ) * a3 + (5 / 495 : ℝ) * a4 +
            (1 / 792 : ℝ) * a5) *
          bernstein 12 5 t +
        (a0 + (6 / 12 : ℝ) * a1 + (15 / 66 : ℝ) * a2 + (20 / 220 : ℝ) * a3 + (15 / 495 : ℝ) * a4 +
            (6 / 792 : ℝ) * a5 +
            (1 / 924 : ℝ) * a6) *
          bernstein 12 6 t +
        (a0 + (7 / 12 : ℝ) * a1 + (21 / 66 : ℝ) * a2 + (35 / 220 : ℝ) * a3 + (35 / 495 : ℝ) * a4 +
            (21 / 792 : ℝ) * a5 +
            (7 / 924 : ℝ) * a6 +
            (1 / 792 : ℝ) * a7) *
          bernstein 12 7 t +
        (a0 + (8 / 12 : ℝ) * a1 + (28 / 66 : ℝ) * a2 + (56 / 220 : ℝ) * a3 + (70 / 495 : ℝ) * a4 +
            (56 / 792 : ℝ) * a5 +
            (28 / 924 : ℝ) * a6 +
            (8 / 792 : ℝ) * a7 +
            (1 / 495 : ℝ) * a8) *
          bernstein 12 8 t +
        (a0 + (9 / 12 : ℝ) * a1 + (36 / 66 : ℝ) * a2 + (84 / 220 : ℝ) * a3 + (126 / 495 : ℝ) * a4 +
            (126 / 792 : ℝ) * a5 +
            (84 / 924 : ℝ) * a6 +
            (36 / 792 : ℝ) * a7 +
            (9 / 495 : ℝ) * a8 +
            (1 / 220 : ℝ) * a9) *
          bernstein 12 9 t +
        (a0 + (10 / 12 : ℝ) * a1 + (45 / 66 : ℝ) * a2 + (120 / 220 : ℝ) * a3 +
            (210 / 495 : ℝ) * a4 +
            (252 / 792 : ℝ) * a5 +
            (210 / 924 : ℝ) * a6 +
            (120 / 792 : ℝ) * a7 +
            (45 / 495 : ℝ) * a8 +
            (10 / 220 : ℝ) * a9 +
            (1 / 66 : ℝ) * a10) *
          bernstein 12 10 t +
        (a0 + (11 / 12 : ℝ) * a1 + (55 / 66 : ℝ) * a2 + (165 / 220 : ℝ) * a3 +
            (330 / 495 : ℝ) * a4 +
            (462 / 792 : ℝ) * a5 +
            (462 / 924 : ℝ) * a6 +
            (330 / 792 : ℝ) * a7 +
            (165 / 495 : ℝ) * a8 +
            (55 / 220 : ℝ) * a9 +
            (11 / 66 : ℝ) * a10 +
            (1 / 12 : ℝ) * a11) *
          bernstein 12 11 t +
        (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12) *
          bernstein 12 12 t := by
  simp only [bernstein_apply]
  norm_num only [Nat.choose, Nat.reduceSub, Nat.cast_ofNat, pow_zero, pow_one]
  ring

/-- If the thirteen supplied coefficients are the Bernstein transforms of the
power coefficients and each is at most `M`, the polynomial is at most `M`
on the unit interval. The transformation identity is reused from
`bernstein12_power_identity`, and the common upper bound follows from the
nonnegative Bernstein basis. -/
theorem bernstein12_power_le (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : ℝ) (t : Set.Icc (0 : ℝ) 1)
    (d : Fin 13 → ℝ) (M : ℝ) (h0 : d 0 = a0) (h1 : d 1 = a0 + (1 / 12 : ℝ) * a1)
    (h2 : d 2 = a0 + (2 / 12 : ℝ) * a1 + (1 / 66 : ℝ) * a2)
    (h3 : d 3 = a0 + (3 / 12 : ℝ) * a1 + (3 / 66 : ℝ) * a2 + (1 / 220 : ℝ) * a3)
    (h4 :
      d 4 = a0 + (4 / 12 : ℝ) * a1 + (6 / 66 : ℝ) * a2 + (4 / 220 : ℝ) * a3 + (1 / 495 : ℝ) * a4)
    (h5 :
      d 5 =
        a0 + (5 / 12 : ℝ) * a1 + (10 / 66 : ℝ) * a2 + (10 / 220 : ℝ) * a3 + (5 / 495 : ℝ) * a4 +
          (1 / 792 : ℝ) * a5)
    (h6 :
      d 6 =
        a0 + (6 / 12 : ℝ) * a1 + (15 / 66 : ℝ) * a2 + (20 / 220 : ℝ) * a3 + (15 / 495 : ℝ) * a4 +
          (6 / 792 : ℝ) * a5 +
          (1 / 924 : ℝ) * a6)
    (h7 :
      d 7 =
        a0 + (7 / 12 : ℝ) * a1 + (21 / 66 : ℝ) * a2 + (35 / 220 : ℝ) * a3 + (35 / 495 : ℝ) * a4 +
          (21 / 792 : ℝ) * a5 +
          (7 / 924 : ℝ) * a6 +
          (1 / 792 : ℝ) * a7)
    (h8 :
      d 8 =
        a0 + (8 / 12 : ℝ) * a1 + (28 / 66 : ℝ) * a2 + (56 / 220 : ℝ) * a3 + (70 / 495 : ℝ) * a4 +
          (56 / 792 : ℝ) * a5 +
          (28 / 924 : ℝ) * a6 +
          (8 / 792 : ℝ) * a7 +
          (1 / 495 : ℝ) * a8)
    (h9 :
      d 9 =
        a0 + (9 / 12 : ℝ) * a1 + (36 / 66 : ℝ) * a2 + (84 / 220 : ℝ) * a3 + (126 / 495 : ℝ) * a4 +
          (126 / 792 : ℝ) * a5 +
          (84 / 924 : ℝ) * a6 +
          (36 / 792 : ℝ) * a7 +
          (9 / 495 : ℝ) * a8 +
          (1 / 220 : ℝ) * a9)
    (h10 :
      d 10 =
        a0 + (10 / 12 : ℝ) * a1 + (45 / 66 : ℝ) * a2 + (120 / 220 : ℝ) * a3 + (210 / 495 : ℝ) * a4 +
          (252 / 792 : ℝ) * a5 +
          (210 / 924 : ℝ) * a6 +
          (120 / 792 : ℝ) * a7 +
          (45 / 495 : ℝ) * a8 +
          (10 / 220 : ℝ) * a9 +
          (1 / 66 : ℝ) * a10)
    (h11 :
      d 11 =
        a0 + (11 / 12 : ℝ) * a1 + (55 / 66 : ℝ) * a2 + (165 / 220 : ℝ) * a3 + (330 / 495 : ℝ) * a4 +
          (462 / 792 : ℝ) * a5 +
          (462 / 924 : ℝ) * a6 +
          (330 / 792 : ℝ) * a7 +
          (165 / 495 : ℝ) * a8 +
          (55 / 220 : ℝ) * a9 +
          (11 / 66 : ℝ) * a10 +
          (1 / 12 : ℝ) * a11)
    (h12 : d 12 = a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12)
    (hc : ∀ i, d i ≤ M) :
    a0 + a1 * (t : ℝ) ^ 1 + a2 * (t : ℝ) ^ 2 + a3 * (t : ℝ) ^ 3 + a4 * (t : ℝ) ^ 4 +
        a5 * (t : ℝ) ^ 5 +
        a6 * (t : ℝ) ^ 6 +
        a7 * (t : ℝ) ^ 7 +
        a8 * (t : ℝ) ^ 8 +
        a9 * (t : ℝ) ^ 9 +
        a10 * (t : ℝ) ^ 10 +
        a11 * (t : ℝ) ^ 11 +
        a12 * (t : ℝ) ^ 12 ≤
      M := by
  have heq :
    a0 + a1 * (t : ℝ) ^ 1 + a2 * (t : ℝ) ^ 2 + a3 * (t : ℝ) ^ 3 + a4 * (t : ℝ) ^ 4 +
        a5 * (t : ℝ) ^ 5 +
        a6 * (t : ℝ) ^ 6 +
        a7 * (t : ℝ) ^ 7 +
        a8 * (t : ℝ) ^ 8 +
        a9 * (t : ℝ) ^ 9 +
        a10 * (t : ℝ) ^ 10 +
        a11 * (t : ℝ) ^ 11 +
        a12 * (t : ℝ) ^ 12 =
      ∑ i : Fin 13, d i * bernstein 12 i.val t := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero]
    change
      _ =
        d 0 * bernstein 12 0 t +
          (d 1 * bernstein 12 1 t +
            (d 2 * bernstein 12 2 t +
              (d 3 * bernstein 12 3 t +
                (d 4 * bernstein 12 4 t +
                  (d 5 * bernstein 12 5 t +
                    (d 6 * bernstein 12 6 t +
                      (d 7 * bernstein 12 7 t +
                        (d 8 * bernstein 12 8 t +
                          (d 9 * bernstein 12 9 t +
                            (d 10 * bernstein 12 10 t +
                              (d 11 * bernstein 12 11 t + (d 12 * bernstein 12 12 t))))))))))))
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
    convert bernstein12_power_identity a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 t using 1
    ring
  rw [heq]
  exact bernstein_sum_le 12 d t M hc

end PseudoPrime.Analysis
