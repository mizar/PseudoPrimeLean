/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.UnitPhaseSteps
public import PseudoPrime.Analysis.IntegerIntervalPhase
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Checked integer centers for unit-phase rotations -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Interpret the integer coordinate pair (a,b) at common scale G as
a complex number. Positive scale is required by the soundness lemmas,
rather than stored in the coordinates used by phase-walk certificates. -/
noncomputable def integerComplexPoint (G a b : ℤ) : ℂ :=
  ⟨(a : ℝ) / G, (b : ℝ) / G⟩

/-- At positive integer scale, an integer L1 coordinate bound controls
the complex norm. This converts cheap integer checks to the norm bounds
needed by the additive unit-rotation error estimate. -/
theorem integer_point_norm_le {G a b r : ℤ} (hg : 0 < G) (hb : |a| + |b| ≤ r) :
    ‖integerComplexPoint G a b‖ ≤ (r : ℝ) / G := by
  have hg' : (0 : ℝ) < G := (Int.cast_pos (R := ℝ)).mpr hg
  have hc : |(a : ℝ)| + |(b : ℝ)| ≤ (r : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).mpr hb
    simpa only [Int.cast_add, Int.cast_abs] using h
  calc
    ‖integerComplexPoint G a b‖ ≤ |(a : ℝ) / G| + |(b : ℝ) / G| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = (|(a : ℝ)| + |(b : ℝ)|) / G := by rw [abs_div, abs_div, abs_of_pos hg', add_div]
    _ ≤ (r : ℝ) / G := div_le_div_of_nonneg_right hc hg'.le

/-- Multiplying two scaled integer centers and subtracting a proposed
rounded center gives exact integer residual coordinates at squared scale.
The identity feeds the executable rounding-error check. -/
theorem integer_point_mul_sub {G a b c d u v : ℤ} (hg : 0 < G) :
    integerComplexPoint G a b * integerComplexPoint G c d - integerComplexPoint G u v =
      integerComplexPoint (G * G) (a * c - b * d - u * G) (a * d + b * c - v * G) := by
  have hg' : (G : ℝ) ≠ 0 := ((Int.cast_pos (R := ℝ)).mpr hg).ne'
  apply Complex.ext <;>
    simp only [integerComplexPoint, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Int.cast_sub, Int.cast_mul, Int.cast_add, div_mul_div_comm, sub_div, add_div,
      mul_div_mul_right _ _ hg']

/-- Check positive scale, nonnegative rounding radius, a center L1 bound
of2*G, and the L1 product residual at most eta*G. Pairs (a,b), (c,d),
and (u,v) are the input center, rotation, and proposed rounded output.
Successful checks supply the norm-two and eta/G bounds for phase steps. -/
def integerRotationCheck (G a b c d u v η : ℤ) : Bool :=
  decide
    (0 < G ∧ 0 ≤ η ∧ |a| + |b| ≤ 2 * G ∧ |a * c - b * d - u * G| + |a * d + b * c - v * G| ≤ η * G)

/-- A successful integer rotation check proves both the center norm bound
of two and the proposed complex rounding error eta/G. All multiplication
and rounding witnesses remain integer data, without external tables. -/
theorem integerRotationCheck_sound {G a b c d u v η : ℤ}
    (hc : integerRotationCheck G a b c d u v η = true) :
    ‖integerComplexPoint G a b‖ ≤ 2 ∧
      ‖integerComplexPoint G a b * integerComplexPoint G c d - integerComplexPoint G u v‖ ≤
        (η : ℝ) / G := by
  have h := of_decide_eq_true hc
  have hg : (G : ℝ) ≠ 0 := ((Int.cast_pos (R := ℝ)).mpr h.1).ne'
  constructor
  · have hn := integer_point_norm_le h.1 h.2.2.1
    simpa only [Int.cast_mul, Int.cast_ofNat, mul_div_cancel_right₀ _ hg] using hn
  · rw [integer_point_mul_sub h.1]
    have hn := integer_point_norm_le (mul_pos h.1 h.1) h.2.2.2
    simpa only [Int.cast_mul, mul_div_mul_right _ _ hg] using hn

/-- A checked integer rotation transfers a true phase approximation at t to t+h.
The new integer radius is r+2*e+eta, using norm-two center control from
the executable check and the genuine small-step phase error e/G. -/
theorem integer_phase_step {t h : ℝ} {G a b c d u v r e η : ℤ}
    (hc : integerRotationCheck G a b c d u v η = true)
    (h0 : ‖Complex.exp ((t : ℂ) * Complex.I) - integerComplexPoint G a b‖ ≤ (r : ℝ) / G)
    (hp : ‖Complex.exp ((h : ℂ) * Complex.I) - integerComplexPoint G c d‖ ≤ (e : ℝ) / G) :
    ‖Complex.exp (((t + h : ℝ) : ℂ) * Complex.I) - integerComplexPoint G u v‖ ≤
      ((r + 2 * e + η : ℤ) : ℝ) / G := by
  have hs := integerRotationCheck_sound hc
  have hb := phase_step_error hs.1 h0 hp hs.2
  norm_num only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  rw [add_div, add_div, mul_div_assoc]
  exact hb

/-- Check every rotation in a finite block of a natural-indexed center function.
The block starts at start and contains count transitions. Integer pairs are
read through the supplied function, with no list indexing or table exposure. -/
def integerPhaseBlockCheck (G c d η : ℤ) (start count : ℕ) (w : ℕ → ℤ × ℤ) : Bool :=
  decide
    (∀ i : Fin count,
      integerRotationCheck G (w (start + i.val)).1 (w (start + i.val)).2 c d
          (w (start + i.val + 1)).1 (w (start + i.val + 1)).2 η =
        true)

/-- A successful finite block check supplies every checked transition in the
block. The finite-index interface lets generated bounded functions discharge
individual blocks before assembling a longer phase walk. -/
theorem integerPhaseBlockCheck_sound {G c d η : ℤ} {start count : ℕ} {w : ℕ → ℤ × ℤ}
    (hc : integerPhaseBlockCheck G c d η start count w = true) :
    ∀ i : Fin count,
      integerRotationCheck G (w (start + i.val)).1 (w (start + i.val)).2 c d
          (w (start + i.val + 1)).1 (w (start + i.val + 1)).2 η =
        true := by
  exact of_decide_eq_true hc

/-- Through horizon N, checked integer rotations and certified initial/step
phases enclose every center with radius r+n*(2*e+eta) at scale G. Only
transitions below N are required; finite tables need no continuation beyond N. -/
theorem integer_phase_steps_le {t h : ℝ} {G c d r e η : ℤ} (N : ℕ) (w : ℕ → ℤ × ℤ)
    (h0 : ‖Complex.exp ((t : ℂ) * Complex.I) - integerComplexPoint G (w 0).1 (w 0).2‖ ≤ (r : ℝ) / G)
    (hp : ‖Complex.exp ((h : ℂ) * Complex.I) - integerComplexPoint G c d‖ ≤ (e : ℝ) / G)
    (hc :
      ∀ n, n < N → integerRotationCheck G (w n).1 (w n).2 c d (w (n + 1)).1 (w (n + 1)).2 η = true)
    {n : ℕ} (hn : n ≤ N) :
    ‖Complex.exp (((t + (n : ℝ) * h : ℝ) : ℂ) * Complex.I) -
          integerComplexPoint G (w n).1 (w n).2‖ ≤
      ((r + (n : ℤ) * (2 * e + η) : ℤ) : ℝ) / G := by
  have hb :=
    phase_steps_error_le N (fun k ↦ integerComplexPoint G (w k).1 (w k).2)
      (integerComplexPoint G c d) h0 hp (fun k hk ↦ (integerRotationCheck_sound (hc k hk)).1)
      (fun k hk ↦ (integerRotationCheck_sound (hc k hk)).2) n hn
  calc
    _ ≤ (r : ℝ) / G + (n : ℝ) * (2 * ((e : ℝ) / G) + (η : ℝ) / G) := hb
    _ = _ := by
      norm_num only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
      ring

/-- An interval enclosed by integer endpoints a-r and a+r gives absolute
error at most r/G from the scaled center a/G. Positive scale and explicit
endpoint comparisons are the only arithmetic assumptions. -/
theorem interval_point_error_le {R : IntegerInterval} {G a r : ℤ} {x : ℝ} (hg : 0 < G)
    (hx : R.Contains G x) (hl : a - r ≤ R.lower) (hu : R.upper ≤ a + r) :
    |x - (a : ℝ) / G| ≤ (r : ℝ) / G := by
  have hg' : (0 : ℝ) < G := (Int.cast_pos (R := ℝ)).mpr hg
  have hlo := div_le_div_of_nonneg_right ((Int.cast_le (R := ℝ)).mpr hl) hg'.le
  have hhi := div_le_div_of_nonneg_right ((Int.cast_le (R := ℝ)).mpr hu) hg'.le
  norm_num only [Int.cast_sub, Int.cast_add, sub_div, add_div] at hlo hhi
  exact abs_le.mpr ⟨by linarith only [hlo, hx.1], by linarith only [hhi, hx.2]⟩

/-- Real and imaginary interval certificates give a complex norm error from
an integer center. The two integer coordinate radii add, allowing existing
Taylor rectangles to initialize a norm-controlled phase walk. -/
theorem complex_interval_error_to_point {R I : IntegerInterval} {G a b r s : ℤ} {z : ℂ} (hg : 0 < G)
    (hz : complexIntervalContains R I G z) (hr : a - r ≤ R.lower ∧ R.upper ≤ a + r)
    (hi : b - s ≤ I.lower ∧ I.upper ≤ b + s) :
    ‖z - integerComplexPoint G a b‖ ≤ ((r + s : ℤ) : ℝ) / G := by
  have h1 := interval_point_error_le hg hz.1 hr.1 hr.2
  have h2 := interval_point_error_le hg hz.2 hi.1 hi.2
  calc
    _ ≤ |z.re - (a : ℝ) / G| + |z.im - (b : ℝ) / G| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (r : ℝ) / G + (s : ℝ) / G := add_le_add h1 h2
    _ = _ := by rw [Int.cast_add, add_div]

/-- A complex norm error r/G from an integer center supplies independent
coordinate intervals widened by r. This bridge feeds the existing continuous
phase-cell certificates with centers obtained by checked rotation walks. -/
theorem integer_point_error_contains {G a b r : ℤ} {z : ℂ}
    (hz : ‖z - integerComplexPoint G a b‖ ≤ (r : ℝ) / G) :
    complexIntervalContains ⟨a - r, a + r⟩ ⟨b - r, b + r⟩ G z := by
  have hr : (IntegerInterval.mk a a).Contains G (integerComplexPoint G a b).re :=
    ⟨le_refl _, le_refl _⟩
  have hi : (IntegerInterval.mk b b).Contains G (integerComplexPoint G a b).im :=
    ⟨le_refl _, le_refl _⟩
  exact complex_error_contains hr hi hz

end PseudoPrime.Analysis
