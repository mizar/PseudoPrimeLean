/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal101Sharp
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone

/-! # A two-cell Lee–Nosal psi certificate -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The two adjoining cells store psi and envelope bounds in thousandths for
`[101, 104)` and `[104, 108)`. The finite data is local to this certificate. -/
private def lowCells : List LeeNosalCell :=
  [⟨101, 104, 98500, 104000, 5500, 5500⟩, ⟨104, 108, 102500, 109000, 5500, 5500⟩]

/-- Since 104 is not a prime power, its Mangoldt increment vanishes and the
psi prefixes through 103 and 104 coincide. -/
private theorem psi_104_eq_103 : Chebyshev.psi 104 = Chebyshev.psi 103 := by
  exact Arithmetic.psi_succ_of_not_prime_power (n := 103) (by decide +kernel)

/-- The lcm certificates bound `psi 103` above and `psi 104` below. -/
private theorem psi_103_104_bounds :
    Chebyshev.psi 103 ≤ (104 : ℝ) ∧ (205 / 2 : ℝ) ≤ Chebyshev.psi 104 := by
  have hl103 : 2 ^ 149 ≤ Nat.lcmUpto 103 := by decide +kernel
  have hu103 : Nat.lcmUpto 103 ≤ 2 ^ (149 + 1) := by decide +kernel
  have h103 := Arithmetic.psi_bounds_of_lcm_pow_two hl103 hu103
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h103
  rw [psi_104_eq_103]
  constructor <;> linarith only [h103.1, h103.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The lcm certificate bounds `psi 107` above. -/
private theorem psi_107_upper : Chebyshev.psi 107 ≤ (109 : ℝ) := by
  have hl107 : 2 ^ 155 ≤ Nat.lcmUpto 107 := by decide +kernel
  have hu107 : Nat.lcmUpto 107 ≤ 2 ^ (155 + 1) := by decide +kernel
  have h107 := Arithmetic.psi_bounds_of_lcm_pow_two hl107 hu107
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h107
  linarith only [h107.2, Real.log_two_lt_d9]

/-- The endpoint envelope bound at 101 extends to every `t ≥ 101`. -/
private theorem low_envelope {t : ℝ} (ht : 101 ≤ t) :
    (11 / 2 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) :=
  lee_nosal_envelope_101_lower.trans
    (lee_nosal_envelope_mono (x := 101) (y := t) (Real.exp_one_lt_three.le.trans (by norm_num only))
      ht)

/-- Each checked cell has a valid psi lower bound at its left endpoint. -/
private theorem lowCells_lower : ∀ r ∈ lowCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [lowCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change (98500 : ℝ) / 1000 ≤ Chebyshev.psi 101
    norm_num only
    exact psi_101_lower
  · change (102500 : ℝ) / 1000 ≤ Chebyshev.psi 104
    norm_num only
    exact psi_103_104_bounds.2

/-- Each checked cell has a valid psi upper bound at the integer before its right endpoint. -/
private theorem lowCells_upper :
    ∀ r ∈ lowCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [lowCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change Chebyshev.psi 103 ≤ (104000 : ℝ) / 1000
    norm_num only
    exact psi_103_104_bounds.1
  · change Chebyshev.psi 107 ≤ (109000 : ℝ) / 1000
    norm_num only
    exact psi_107_upper

/-- Each checked cell has a valid envelope lower bound at its left endpoint. -/
private theorem lowCells_left :
    ∀ r ∈ lowCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [lowCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change
      (5500 : ℝ) / 1000 ≤
        Real.sqrt 101 * (Real.log 101 * (Real.log 101 - Real.log (Real.log 101)) / (8 * Real.pi))
    norm_num only
    exact low_envelope (by norm_num only)
  · change
      (5500 : ℝ) / 1000 ≤
        Real.sqrt 104 * (Real.log 104 * (Real.log 104 - Real.log (Real.log 104)) / (8 * Real.pi))
    norm_num only
    exact low_envelope (by norm_num only)

/-- Each checked cell has a valid envelope lower bound at its right endpoint. -/
private theorem lowCells_right :
    ∀ r ∈ lowCells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [lowCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change
      (5500 : ℝ) / 1000 ≤
        Real.sqrt 104 * (Real.log 104 * (Real.log 104 - Real.log (Real.log 104)) / (8 * Real.pi))
    norm_num only
    exact low_envelope (by norm_num only)
  · change
      (5500 : ℝ) / 1000 ≤
        Real.sqrt 108 * (Real.log 108 * (Real.log 108 - Real.log (Real.log 108)) / (8 * Real.pi))
    norm_num only
    exact low_envelope (by norm_num only)

/-- The Lee–Nosal psi error bound holds unconditionally on `[101, 108)`.
Two cells pass the chain checker, and their endpoint and envelope bounds are certified. -/
theorem psi_lee_nosal_101_108 {x : ℝ} (ha : 101 ≤ x) (hb : x < 108) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      lowCells_lower lowCells_upper lowCells_left lowCells_right ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
