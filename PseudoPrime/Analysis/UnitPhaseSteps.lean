/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Linear error budgets for successive unit-phase rotations -/

public section

namespace PseudoPrime.Analysis

/-- A unit rotation transfers a complex center error e with only additive
rotation and rounding errors M*epsilon and eta, provided the approximate
center has norm at most M. The identity splits the three error sources and
avoids repeated rectangular widening in long phase walks. -/
theorem unit_rotation_step {z w r p u : ℂ} {e M ε η : ℝ} (hr : ‖r‖ = 1) (hw : ‖w‖ ≤ M)
    (hz : ‖z - w‖ ≤ e) (hp : ‖r - p‖ ≤ ε) (hu : ‖w * p - u‖ ≤ η) : ‖z * r - u‖ ≤ e + M * ε + η := by
  have h1 : ‖(z - w) * r‖ ≤ e := by
    rw [Complex.norm_mul, hr, mul_one]
    exact hz
  have h2 : ‖w * (r - p)‖ ≤ M * ε := by
    rw [Complex.norm_mul]
    exact mul_le_mul hw hp (norm_nonneg _) ((norm_nonneg _).trans hw)
  calc
    ‖z * r - u‖ = ‖((z - w) * r + w * (r - p)) + (w * p - u)‖ := by
      congr 1
      ring
    _ ≤ ‖(z - w) * r‖ + ‖w * (r - p)‖ + ‖w * p - u‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ e + M * ε + η := add_le_add (add_le_add h1 h2) hu

/-- Adding a real phase increment transfers an existing center approximation
with the additive unit-rotation error bound. The exact exponential addition
identity and norm-one phase factor discharge the analytic rotation premise. -/
theorem phase_step_error {a d : ℝ} {w p u : ℂ} {e M ε η : ℝ} (hw : ‖w‖ ≤ M)
    (hz : ‖Complex.exp ((a : ℂ) * Complex.I) - w‖ ≤ e)
    (hp : ‖Complex.exp ((d : ℂ) * Complex.I) - p‖ ≤ ε) (hu : ‖w * p - u‖ ≤ η) :
    ‖Complex.exp (((a + d : ℝ) : ℂ) * Complex.I) - u‖ ≤ e + M * ε + η := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]
  exact unit_rotation_step (Complex.norm_exp_ofReal_mul_I d) hw hz hp hu

/-- For a sequence of approximate phase centers with uniform norm bound M,
initial error E, rotation error epsilon and per-step rounding eta, the nth
center has error at most E+n*(M*epsilon+eta). A natural-indexed function
supports sequential certificates without accessing values in a list by index. -/
theorem phase_steps_error {c d E M ε η : ℝ} (w : ℕ → ℂ) (p : ℂ)
    (h0 : ‖Complex.exp ((c : ℂ) * Complex.I) - w 0‖ ≤ E)
    (hp : ‖Complex.exp ((d : ℂ) * Complex.I) - p‖ ≤ ε) (hw : ∀ n, ‖w n‖ ≤ M)
    (hs : ∀ n, ‖w n * p - w (n + 1)‖ ≤ η) :
    ∀ n : ℕ,
      ‖Complex.exp (((c + (n : ℝ) * d : ℝ) : ℂ) * Complex.I) - w n‖ ≤
        E + (n : ℝ) * (M * ε + η) := by
  intro n
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_mul, add_zero] using h0
  | succ n ih =>
    have h := phase_step_error (hw n) ih hp (hs n)
    have he : c + ((n + 1 : ℕ) : ℝ) * d = (c + (n : ℝ) * d) + d := by
      rw [Nat.cast_succ]
      ring
    rw [he]
    simp only [Nat.cast_succ]
    linarith only [h]

/-- The linear phase error estimate through a finite horizon N needs
center and rounding bounds only at indices below N. This form consumes
finite executable checks without inventing assumptions after the last center. -/
theorem phase_steps_error_le {c d E M ε η : ℝ} (N : ℕ) (w : ℕ → ℂ) (p : ℂ)
    (h0 : ‖Complex.exp ((c : ℂ) * Complex.I) - w 0‖ ≤ E)
    (hp : ‖Complex.exp ((d : ℂ) * Complex.I) - p‖ ≤ ε) (hw : ∀ n, n < N → ‖w n‖ ≤ M)
    (hs : ∀ n, n < N → ‖w n * p - w (n + 1)‖ ≤ η) :
    ∀ n : ℕ,
      n ≤ N →
        ‖Complex.exp (((c + (n : ℝ) * d : ℝ) : ℂ) * Complex.I) - w n‖ ≤
          E + (n : ℝ) * (M * ε + η) := by
  intro n
  induction n with
  | zero =>
    intro _
    simpa only [Nat.cast_zero, zero_mul, add_zero] using h0
  | succ n ih =>
    intro hn
    have hlt : n < N := Nat.lt_of_succ_le hn
    have h := phase_step_error (hw n hlt) (ih hlt.le) hp (hs n hlt)
    have he : c + ((n + 1 : ℕ) : ℝ) * d = (c + (n : ℝ) * d) + d := by
      rw [Nat.cast_succ]
      ring
    rw [he]
    simp only [Nat.cast_succ]
    linarith only [h]

end PseudoPrime.Analysis
