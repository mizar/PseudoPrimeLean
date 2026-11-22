/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Bernstein12
import Mathlib.Tactic.Linarith

/-! # Centered coordinates for degree-twelve polynomials -/

public section

namespace PseudoPrime.Analysis

/-- Change the centered coordinate `2 * s - 1` to the unit coordinate `s`
in a polynomial of degree at most twelve. The displayed integer coefficients
are shared by all cell certificates; no numerical zero data is assumed. -/
theorem power12_center_shift (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 s : ℝ) :
    b0 + b1 * (2 * s - 1) ^ 1 + b2 * (2 * s - 1) ^ 2 + b3 * (2 * s - 1) ^ 3 + b4 * (2 * s - 1) ^ 4 +
        b5 * (2 * s - 1) ^ 5 +
        b6 * (2 * s - 1) ^ 6 +
        b7 * (2 * s - 1) ^ 7 +
        b8 * (2 * s - 1) ^ 8 +
        b9 * (2 * s - 1) ^ 9 +
        b10 * (2 * s - 1) ^ 10 +
        b11 * (2 * s - 1) ^ 11 +
        b12 * (2 * s - 1) ^ 12 =
      (b0 + (-1 : ℝ) * b1 + b2 + (-1 : ℝ) * b3 + b4 + (-1 : ℝ) * b5 + b6 + (-1 : ℝ) * b7 + b8 +
            (-1 : ℝ) * b9 +
            b10 +
            (-1 : ℝ) * b11 +
            b12) *
          s ^ 0 +
        ((2 : ℝ) * b1 + (-4 : ℝ) * b2 + (6 : ℝ) * b3 + (-8 : ℝ) * b4 + (10 : ℝ) * b5 +
            (-12 : ℝ) * b6 +
            (14 : ℝ) * b7 +
            (-16 : ℝ) * b8 +
            (18 : ℝ) * b9 +
            (-20 : ℝ) * b10 +
            (22 : ℝ) * b11 +
            (-24 : ℝ) * b12) *
          s ^ 1 +
        ((4 : ℝ) * b2 + (-12 : ℝ) * b3 + (24 : ℝ) * b4 + (-40 : ℝ) * b5 + (60 : ℝ) * b6 +
            (-84 : ℝ) * b7 +
            (112 : ℝ) * b8 +
            (-144 : ℝ) * b9 +
            (180 : ℝ) * b10 +
            (-220 : ℝ) * b11 +
            (264 : ℝ) * b12) *
          s ^ 2 +
        ((8 : ℝ) * b3 + (-32 : ℝ) * b4 + (80 : ℝ) * b5 + (-160 : ℝ) * b6 + (280 : ℝ) * b7 +
            (-448 : ℝ) * b8 +
            (672 : ℝ) * b9 +
            (-960 : ℝ) * b10 +
            (1320 : ℝ) * b11 +
            (-1760 : ℝ) * b12) *
          s ^ 3 +
        ((16 : ℝ) * b4 + (-80 : ℝ) * b5 + (240 : ℝ) * b6 + (-560 : ℝ) * b7 + (1120 : ℝ) * b8 +
            (-2016 : ℝ) * b9 +
            (3360 : ℝ) * b10 +
            (-5280 : ℝ) * b11 +
            (7920 : ℝ) * b12) *
          s ^ 4 +
        ((32 : ℝ) * b5 + (-192 : ℝ) * b6 + (672 : ℝ) * b7 + (-1792 : ℝ) * b8 + (4032 : ℝ) * b9 +
            (-8064 : ℝ) * b10 +
            (14784 : ℝ) * b11 +
            (-25344 : ℝ) * b12) *
          s ^ 5 +
        ((64 : ℝ) * b6 + (-448 : ℝ) * b7 + (1792 : ℝ) * b8 + (-5376 : ℝ) * b9 + (13440 : ℝ) * b10 +
            (-29568 : ℝ) * b11 +
            (59136 : ℝ) * b12) *
          s ^ 6 +
        ((128 : ℝ) * b7 + (-1024 : ℝ) * b8 + (4608 : ℝ) * b9 + (-15360 : ℝ) * b10 +
            (42240 : ℝ) * b11 +
            (-101376 : ℝ) * b12) *
          s ^ 7 +
        ((256 : ℝ) * b8 + (-2304 : ℝ) * b9 + (11520 : ℝ) * b10 + (-42240 : ℝ) * b11 +
            (126720 : ℝ) * b12) *
          s ^ 8 +
        ((512 : ℝ) * b9 + (-5120 : ℝ) * b10 + (28160 : ℝ) * b11 + (-112640 : ℝ) * b12) * s ^ 9 +
        ((1024 : ℝ) * b10 + (-11264 : ℝ) * b11 + (67584 : ℝ) * b12) * s ^ 10 +
        ((2048 : ℝ) * b11 + (-24576 : ℝ) * b12) * s ^ 11 +
        ((4096 : ℝ) * b12) * s ^ 12 := by
  ring

/-- A centered coordinate in `[-1,1]` is `2 * s - 1` for some unit-interval
coordinate `s`. This supplies the domain change used with the shared
degree-twelve coefficient transformation. -/
theorem exists_center_coord {t : ℝ} (h0 : -1 ≤ t) (h1 : t ≤ 1) :
    ∃ s : Set.Icc (0 : ℝ) 1, t = 2 * (s : ℝ) - 1 := by
  let s : Set.Icc (0 : ℝ) 1 := ⟨(t + 1) / 2, by constructor <;> linarith only [h0, h1]⟩
  refine ⟨s, ?_⟩
  change t = 2 * ((t + 1) / 2) - 1
  ring

/-- A unit-interval upper bound for the transformed coefficients bounds the
same degree-twelve polynomial throughout the centered interval. This combines
the shared coordinate identity with its domain conversion for cell checks. -/
theorem power12_center_le (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 t M : ℝ) (ht0 : -1 ≤ t)
    (ht1 : t ≤ 1)
    (hunit :
      ∀ s : Set.Icc (0 : ℝ) 1,
        (b0 + (-1 : ℝ) * b1 + b2 + (-1 : ℝ) * b3 + b4 + (-1 : ℝ) * b5 + b6 + (-1 : ℝ) * b7 + b8 +
                (-1 : ℝ) * b9 +
                b10 +
                (-1 : ℝ) * b11 +
                b12) *
              (s : ℝ) ^ 0 +
            ((2 : ℝ) * b1 + (-4 : ℝ) * b2 + (6 : ℝ) * b3 + (-8 : ℝ) * b4 + (10 : ℝ) * b5 +
                (-12 : ℝ) * b6 +
                (14 : ℝ) * b7 +
                (-16 : ℝ) * b8 +
                (18 : ℝ) * b9 +
                (-20 : ℝ) * b10 +
                (22 : ℝ) * b11 +
                (-24 : ℝ) * b12) *
              (s : ℝ) ^ 1 +
            ((4 : ℝ) * b2 + (-12 : ℝ) * b3 + (24 : ℝ) * b4 + (-40 : ℝ) * b5 + (60 : ℝ) * b6 +
                (-84 : ℝ) * b7 +
                (112 : ℝ) * b8 +
                (-144 : ℝ) * b9 +
                (180 : ℝ) * b10 +
                (-220 : ℝ) * b11 +
                (264 : ℝ) * b12) *
              (s : ℝ) ^ 2 +
            ((8 : ℝ) * b3 + (-32 : ℝ) * b4 + (80 : ℝ) * b5 + (-160 : ℝ) * b6 + (280 : ℝ) * b7 +
                (-448 : ℝ) * b8 +
                (672 : ℝ) * b9 +
                (-960 : ℝ) * b10 +
                (1320 : ℝ) * b11 +
                (-1760 : ℝ) * b12) *
              (s : ℝ) ^ 3 +
            ((16 : ℝ) * b4 + (-80 : ℝ) * b5 + (240 : ℝ) * b6 + (-560 : ℝ) * b7 + (1120 : ℝ) * b8 +
                (-2016 : ℝ) * b9 +
                (3360 : ℝ) * b10 +
                (-5280 : ℝ) * b11 +
                (7920 : ℝ) * b12) *
              (s : ℝ) ^ 4 +
            ((32 : ℝ) * b5 + (-192 : ℝ) * b6 + (672 : ℝ) * b7 + (-1792 : ℝ) * b8 + (4032 : ℝ) * b9 +
                (-8064 : ℝ) * b10 +
                (14784 : ℝ) * b11 +
                (-25344 : ℝ) * b12) *
              (s : ℝ) ^ 5 +
            ((64 : ℝ) * b6 + (-448 : ℝ) * b7 + (1792 : ℝ) * b8 + (-5376 : ℝ) * b9 +
                (13440 : ℝ) * b10 +
                (-29568 : ℝ) * b11 +
                (59136 : ℝ) * b12) *
              (s : ℝ) ^ 6 +
            ((128 : ℝ) * b7 + (-1024 : ℝ) * b8 + (4608 : ℝ) * b9 + (-15360 : ℝ) * b10 +
                (42240 : ℝ) * b11 +
                (-101376 : ℝ) * b12) *
              (s : ℝ) ^ 7 +
            ((256 : ℝ) * b8 + (-2304 : ℝ) * b9 + (11520 : ℝ) * b10 + (-42240 : ℝ) * b11 +
                (126720 : ℝ) * b12) *
              (s : ℝ) ^ 8 +
            ((512 : ℝ) * b9 + (-5120 : ℝ) * b10 + (28160 : ℝ) * b11 + (-112640 : ℝ) * b12) *
              (s : ℝ) ^ 9 +
            ((1024 : ℝ) * b10 + (-11264 : ℝ) * b11 + (67584 : ℝ) * b12) * (s : ℝ) ^ 10 +
            ((2048 : ℝ) * b11 + (-24576 : ℝ) * b12) * (s : ℝ) ^ 11 +
            ((4096 : ℝ) * b12) * (s : ℝ) ^ 12 ≤
          M) :
    b0 + b1 * t ^ 1 + b2 * t ^ 2 + b3 * t ^ 3 + b4 * t ^ 4 + b5 * t ^ 5 + b6 * t ^ 6 + b7 * t ^ 7 +
        b8 * t ^ 8 +
        b9 * t ^ 9 +
        b10 * t ^ 10 +
        b11 * t ^ 11 +
        b12 * t ^ 12 ≤
      M := by
  obtain ⟨s, rfl⟩ := exists_center_coord ht0 ht1
  rw [power12_center_shift]
  exact hunit s

end PseudoPrime.Analysis
