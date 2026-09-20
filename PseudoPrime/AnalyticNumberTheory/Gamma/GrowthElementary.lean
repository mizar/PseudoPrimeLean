/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Elementary real-axis Gamma bounds

For `x ≥ 1`, log-convexity and the factorial bound give `log Γ(x) ≤ x log x`.
The Gamma recurrence also gives upper and lower bounds for `Γ(3/2+n)`, divergence
along natural shifts, and estimates for the even and odd subsequences.
Together with a complex Gamma norm comparison, these bounds control xi growth.
-/

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- `t ↦ t * log t` is monotone on `[1, ∞)`. -/
theorem mul_log_mono_of_one_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a * Real.log a ≤ b * Real.log b := by
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have hlb : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have h1b : 1 ≤ b := ha.trans hab
  have hlb0 : 0 ≤ Real.log b := Real.log_nonneg h1b
  calc
    a * Real.log a ≤ b * Real.log a := by apply mul_le_mul_of_nonneg_right hab hla
    _ ≤ b * Real.log b := by apply mul_le_mul_of_nonneg_left hlb (by linarith)

/-- Elementary real-axis growth bound for `Real.Gamma`, via log-convexity (Bohr-Mollerup) and the
trivial factorial bound `n! ≤ n^n` — no Stirling asymptotics needed. -/
theorem log_Gamma_le_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.log (Real.Gamma x) ≤ x * Real.log x := by
  set m : ℕ := ⌊x - 1⌋₊ with hm_def
  have hm_nonneg : (0 : ℝ) ≤ x - 1 := by linarith
  have hmx1 : (m : ℝ) ≤ x - 1 := Nat.floor_le hm_nonneg
  have hx1m1 : x - 1 < m + 1 := Nat.lt_floor_add_one (x - 1)
  -- x ∈ [m+1, m+2)
  have hxlb : (m : ℝ) + 1 ≤ x := by linarith
  have hxub : x < (m : ℝ) + 2 := by linarith
  set θ : ℝ := x - ((m : ℝ) + 1) with hθ_def
  have hθ0 : 0 ≤ θ := by
    rw [hθ_def]; linarith
  have hθ1 : θ < 1 := by
    rw [hθ_def]; linarith
  have hxeq : x = θ * ((m : ℝ) + 2) + (1 - θ) * ((m : ℝ) + 1) := by
    rw [hθ_def]; ring
  have hmem1 : (m : ℝ) + 1 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by positivity)
  have hmem2 : (m : ℝ) + 2 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by positivity)
  rcases eq_or_lt_of_le hθ0 with hθ0' | hθ0'
  · -- θ = 0, x = m+1
    have hxeq' : x = (m : ℝ) + 1 := by
      rw [hxeq, ← hθ0']; ring
    rw [hxeq']
    rw [Real.Gamma_nat_eq_factorial]
    have h1 : Nat.factorial m ≤ m ^ m := Nat.factorial_le_pow m
    calc
      Real.log ((Nat.factorial m : ℕ) : ℝ) ≤ Real.log ((m : ℝ) ^ m) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast h1
      _ = m * Real.log (m : ℝ) := by rw [Real.log_pow]
      _ ≤ ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1) := by
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · simp only [hm0, CharP.cast_eq_zero, Real.log_zero, mul_zero, zero_add, Real.log_one,
            Std.le_refl]
        · exact mul_log_mono_of_one_le (by exact_mod_cast hmpos) (by linarith)
  · -- θ > 0: use convexity between m+1 and m+2
    have hC : ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1) ≤ x * Real.log x :=
      mul_log_mono_of_one_le (by linarith) hxlb
    have hlogGamma_m1 :
      Real.log (Real.Gamma ((m : ℝ) + 1)) ≤ ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1) := by
      rw [Real.Gamma_nat_eq_factorial]
      have h1 : Nat.factorial m ≤ (m + 1) ^ (m + 1) :=
        (Nat.factorial_le_pow m).trans
          (Nat.pow_le_pow_left (by omega) m |>.trans (Nat.pow_le_pow_right (by omega) (by omega)))
      calc
        Real.log ((Nat.factorial m : ℕ) : ℝ) ≤ Real.log (((m : ℝ) + 1) ^ (m + 1)) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast h1
        _ = ((m : ℕ) + 1) * Real.log ((m : ℝ) + 1) := by
          rw [Real.log_pow]; push_cast; ring
    have hlogGamma_m2 :
      Real.log (Real.Gamma ((m : ℝ) + 2)) ≤ ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1) := by
      rw [show ((m : ℝ) + 2) = ((m + 1 : ℕ) : ℝ) + 1 from by
          push_cast; ring,
        Real.Gamma_nat_eq_factorial]
      have h1 : Nat.factorial (m + 1) ≤ (m + 1) ^ (m + 1) := Nat.factorial_le_pow (m + 1)
      calc
        Real.log ((Nat.factorial (m + 1) : ℕ) : ℝ) ≤ Real.log (((m : ℝ) + 1) ^ (m + 1)) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast h1
        _ = ((m : ℕ) + 1) * Real.log ((m : ℝ) + 1) := by
          rw [Real.log_pow]; push_cast; ring
    have hsum : θ + (1 - θ) = 1 := by ring
    have hconv := Real.convexOn_log_Gamma.2 hmem2 hmem1 hθ0'.le (by linarith) hsum
    simp only [Function.comp_apply, smul_eq_mul] at hconv
    have hgx : Real.Gamma x = Real.Gamma (θ * ((m : ℝ) + 2) + (1 - θ) * ((m : ℝ) + 1)) := by
      rw [← hxeq]
    calc
      Real.log (Real.Gamma x) =
          Real.log (Real.Gamma (θ * ((m : ℝ) + 2) + (1 - θ) * ((m : ℝ) + 1))) :=
        by rw [hgx]
      _ ≤ θ * Real.log (Real.Gamma ((m : ℝ) + 2)) + (1 - θ) * Real.log (Real.Gamma ((m : ℝ) + 1)) :=
        hconv
      _ ≤
          θ * (((m : ℝ) + 1) * Real.log ((m : ℝ) + 1)) +
            (1 - θ) * (((m : ℝ) + 1) * Real.log ((m : ℝ) + 1)) :=
        by gcongr
      _ = ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1) := by ring
      _ ≤ x * Real.log x := hC

/-- `Γ(3/2 + n) ≥ (3/2)^n · Γ(3/2)`, via the recurrence `Γ(z+1) = z·Γ(z)` applied `n` times
(each factor `3/2 + k ≥ 3/2`). Used only to show `Γ` is unbounded along `n : ℕ`, without any
Stirling-type quantitative growth rate. -/
theorem Gamma_three_half_add_nat_ge (n : ℕ) :
    (3 / 2 : ℝ) ^ n * Real.Gamma (3 / 2) ≤ Real.Gamma (3 / 2 + n) := by
  induction n with
  | zero => simp only [pow_zero, one_mul, CharP.cast_eq_zero, add_zero, Std.le_refl]
  | succ n ih =>
    have hne : (3 / 2 + (n : ℝ)) ≠ 0 := by positivity
    have heq : (3 / 2 + ((n : ℝ) + 1) : ℝ) = (3 / 2 + n) + 1 := by ring
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 from by
        push_cast; ring,
      heq, Real.Gamma_add_one hne]
    have h32le : (3 / 2 : ℝ) ≤ 3 / 2 + n := le_add_of_nonneg_right (Nat.cast_nonneg n)
    have hGamma32pos : (0 : ℝ) < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num only)
    have hpow_nonneg : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ n * Real.Gamma (3 / 2) := by positivity
    calc
      (3 / 2 : ℝ) ^ (n + 1) * Real.Gamma (3 / 2) =
          (3 / 2 : ℝ) * ((3 / 2) ^ n * Real.Gamma (3 / 2)) :=
        by ring
      _ ≤ (3 / 2 + n) * Real.Gamma (3 / 2 + n) := mul_le_mul h32le ih hpow_nonneg (by linarith)

/-- The upper-bound mirror of `PseudoPrime.AnalyticNumberTheory.Gamma.Gamma_three_half_add_nat_ge`:
`Γ(3/2+n)≤(n+2)^n·Γ(3/2)`, via the
same recurrence, using that each of the `n` shift factors `3/2+k` (`k<n`) is `≤n+2`. This is a
*crude, elementary* bound (no Stirling asymptotic). It bounds the logarithm of Gamma by a
quantity of order `n·log n` and supplies the even and odd subsequence estimates below. -/
theorem Gamma_three_half_add_nat_le (n : ℕ) :
    Real.Gamma (3 / 2 + n) ≤ ((n : ℝ) + 2) ^ n * Real.Gamma (3 / 2) := by
  induction n with
  | zero => simp only [CharP.cast_eq_zero, add_zero, zero_add, pow_zero, one_mul, Std.le_refl]
  | succ n ih =>
    have hne : (3 / 2 + (n : ℝ)) ≠ 0 := by positivity
    have heq : (3 / 2 + ((n : ℝ) + 1) : ℝ) = (3 / 2 + n) + 1 := by ring
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 from by
        push_cast; ring,
      heq, Real.Gamma_add_one hne]
    have h32le : (3 / 2 + (n : ℝ)) ≤ (n : ℝ) + 2 := by linarith
    have hGamma32pos : (0 : ℝ) < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num only)
    have hGamman_pos : (0 : ℝ) ≤ Real.Gamma (3 / 2 + n) :=
      (Real.Gamma_pos_of_pos (by positivity)).le
    calc
      (3 / 2 + (n : ℝ)) * Real.Gamma (3 / 2 + n) ≤
          ((n : ℝ) + 2) * (((n : ℝ) + 2) ^ n * Real.Gamma (3 / 2)) :=
        mul_le_mul h32le ih hGamman_pos (by positivity)
      _ = ((n : ℝ) + 2) ^ (n + 1) * Real.Gamma (3 / 2) := by ring
      _ ≤ ((n : ℝ) + 1 + 2) ^ (n + 1) * Real.Gamma (3 / 2) := by
        apply mul_le_mul_of_nonneg_right _ hGamma32pos.le
        exact pow_le_pow_left₀ (by positivity) (by linarith) (n + 1)

/-- `Γ(3/2 + n)` tends to infinity along natural numbers: the recurrence lower bound
is geometric with positive coefficient. Used to prove divergence of Gamma envelopes. -/
theorem tendsto_Real_Gamma_three_half_add_atTop :
    Filter.Tendsto (fun n : ℕ => Real.Gamma (3 / 2 + n)) Filter.atTop Filter.atTop := by
  have hGamma32pos : (0 : ℝ) < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num only)
  have h1 :
    Filter.Tendsto (fun n : ℕ => (3 / 2 : ℝ) ^ n * Real.Gamma (3 / 2)) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num only : (1 : ℝ) < 3 / 2)).atTop_mul_const
      hGamma32pos
  exact Filter.tendsto_atTop_mono Gamma_three_half_add_nat_ge h1

/-- The maximum of `Γ(1)`, `Γ(2)`, `Γ(2m+3/2)`, and `Γ(2m+5/2)` tends to infinity.
It dominates the last term, whose recurrence lower bound diverges. -/
theorem tendsto_max_Gamma_halfInteger_atTop :
    Filter.Tendsto
      (fun m : ℕ =>
        max (max (Real.Gamma 1) (Real.Gamma 2))
          (max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2))))
      Filter.atTop Filter.atTop := by
  have hcomp :
    Filter.Tendsto (fun m : ℕ => Real.Gamma (2 * (m : ℝ) + 5 / 2)) Filter.atTop Filter.atTop := by
    have hn : Filter.Tendsto (fun m : ℕ => 2 * m + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono
        (fun m => by
          simp only [id_eq]; omega)
        Filter.tendsto_id
    have := tendsto_Real_Gamma_three_half_add_atTop.comp hn
    refine this.congr (fun m => ?_)
    simp only [Function.comp_apply]
    have heq : (3 / 2 + ((2 * m + 1 : ℕ) : ℝ)) = 2 * (m : ℝ) + 5 / 2 := by
      push_cast; ring
    rw [heq]
  refine Filter.tendsto_atTop_mono (fun m => ?_) hcomp
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- `Γ(2m + 3/2) ≤ (2m + 2)^{2m} · Γ(3/2)`, a corollary of
`PseudoPrime.AnalyticNumberTheory.Gamma.Gamma_three_half_add_nat_le` at
`n := 2m`. -/
theorem Gamma_two_mul_add_three_half_le (m : ℕ) :
    Real.Gamma (2 * (m : ℝ) + 3 / 2) ≤ (2 * (m : ℝ) + 2) ^ (2 * m) * Real.Gamma (3 / 2) := by
  have h := Gamma_three_half_add_nat_le (2 * m)
  rwa [show (3 / 2 + ((2 * m : ℕ) : ℝ)) = 2 * (m : ℝ) + 3 / 2 from by
      push_cast; ring,
    show (((2 * m : ℕ) : ℝ) + 2) = 2 * (m : ℝ) + 2 from by
      push_cast; ring] at h

/-- `Γ(2m + 5/2) ≤ (2m + 3)^{2m+1} · Γ(3/2)`, a corollary of
`PseudoPrime.AnalyticNumberTheory.Gamma.Gamma_three_half_add_nat_le` at
`n := 2m + 1`. -/
theorem Gamma_two_mul_add_five_half_le (m : ℕ) :
    Real.Gamma (2 * (m : ℝ) + 5 / 2) ≤ (2 * (m : ℝ) + 3) ^ (2 * m + 1) * Real.Gamma (3 / 2) := by
  have h := Gamma_three_half_add_nat_le (2 * m + 1)
  rwa [show (3 / 2 + ((2 * m + 1 : ℕ) : ℝ)) = 2 * (m : ℝ) + 5 / 2 from by
      push_cast; ring,
    show (((2 * m + 1 : ℕ) : ℝ) + 2) = 2 * (m : ℝ) + 3 from by
      push_cast; ring] at h

end PseudoPrime.AnalyticNumberTheory.Gamma
