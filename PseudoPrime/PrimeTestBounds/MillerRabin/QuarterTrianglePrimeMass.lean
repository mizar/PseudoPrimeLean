/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleFiniteWindow
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrimeWindow576
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTrianglePowers

/-! # Prime mass in the finite translated triangle window -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The normalized Mellin profile is the shifted triangle in logarithmic coordinates. -/
theorem triangle_profile_shift {t : ℝ} (ht : 0 < t) (v : ℝ) :
    (2 / 5) * LLS.PaperStatements.triangularKernelProfile (5 / 4) (t / Real.exp (v + 5 / 2)) =
      shiftedTriangle (5 / 2) (Real.log t - v) := by
  unfold LLS.PaperStatements.triangularKernelProfile shiftedTriangle
  rw [Real.log_div ht.ne' (Real.exp_pos _).ne', Real.log_exp, ← sub_sub,
    mul_max_of_nonneg _ _ (by norm_num only), mul_zero]
  congr 1
  ring

/-- Over the full integer window the normalized triangle weight splits into
the two logarithmic branches used in Abel summation, with any arithmetic multiplier. -/
theorem triangle_branch_sum (v : ℝ) (w : ℕ → ℝ) :
    let l := Real.exp v
    let m := Real.exp (v + 5 / 2)
    let u := Real.exp (v + 5)
    (∑ n ∈ Finset.Ioc ⌊l⌋₊ ⌊u⌋₊, shiftedTriangle (5 / 2) (Real.log n - v) / Real.sqrt n * w n) =
      (∑ n ∈ Finset.Ioc ⌊l⌋₊ ⌊m⌋₊, triangleLogBranch (-(2 * v / 5)) (2 / 5) n * w n) +
        (∑ n ∈ Finset.Ioc ⌊m⌋₊ ⌊u⌋₊, triangleLogBranch (2 + 2 * v / 5) (-(2 / 5)) n * w n) := by
  intro l m u
  have hlog {a b : ℝ} {n : ℕ} (hn : n ∈ Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊) :
    a < Real.log n ∧ Real.log n ≤ b := by
    obtain ⟨ha, hb⟩ := Finset.mem_Ioc.mp hn
    have h := (Nat.floor_lt (Real.exp_pos _).le).mp ha
    exact
      ⟨(Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans h)).mpr h,
        (Real.log_le_iff_le_exp ((Real.exp_pos _).trans h)).mpr
          ((Nat.le_floor_iff (Real.exp_pos _).le).mp hb)⟩
  rw [←
    Finset.sum_Ioc_consecutive _
      (Nat.floor_mono (show l ≤ m from Real.exp_le_exp.mpr (by linarith only)))
      (Nat.floor_mono (show m ≤ u from Real.exp_le_exp.mpr (by linarith only)))]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨ha, hb⟩ := hlog hn
    unfold shiftedTriangle triangleLogBranch
    rw [abs_of_nonpos (by linarith only [hb]), max_eq_right (by linarith only [ha])]
    ring
  · apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨ha, hb⟩ := hlog hn
    unfold shiftedTriangle triangleLogBranch
    rw [abs_of_nonneg (by linarith only [ha]), max_eq_right (by linarith only [hb])]
    ring

/-- Under RH the prime indices alone contribute more than 3943r/400 minus five
to the normalized translated triangle throughout the radius interval [287,288]. -/
theorem triangle_prime_mass_576 (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) :
    let v := 2 * Real.log r
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    3943 / 400 * r - 5 <
      ∑ n ∈ s.filter Nat.Prime,
        shiftedTriangle (5 / 2) (Real.log n - v) / Real.sqrt n *
          ArithmeticFunction.vonMangoldt n := by
  intro v s
  let f (n : ℕ) :=
    shiftedTriangle (5 / 2) (Real.log n - v) / Real.sqrt n * ArithmeticFunction.vonMangoldt n
  have ha := triangle_mangoldt_lower_576 hRH hl hu
  have he := triangle_branch_sum v (fun n => ArithmeticFunction.vonMangoldt n)
  have ht : 3943 / 400 * r < ∑ n ∈ s, f n := ha.trans_eq he.symm
  have hr : 0 < r := by linarith only [hl]
  have heq : Real.exp v = r ^ 2 := by
    dsimp only [v]
    rw [two_mul, Real.exp_add, Real.exp_log hr, sq]
  have hn :=
    triangle_mangoldt_nonprime_576 hl hu (s.filter (fun n => ¬n.Prime))
      (fun n h => (Finset.mem_filter.mp h).2) (fun n => Real.log n - v)
      (fun n h =>
        heq ▸
          (Nat.floor_lt (Real.exp_pos _).le).mp (Finset.mem_Ioc.mp (Finset.mem_filter.mp h).1).1)
      (fun n h => by
        rw [← heq, mul_comm, ← Real.exp_add]
        exact
          (Nat.le_floor_iff (Real.exp_pos _).le).mp
            (Finset.mem_Ioc.mp (Finset.mem_filter.mp h).1).2)
  have hsplit := Finset.sum_filter_add_sum_filter_not s Nat.Prime f
  change _ < ∑ n ∈ s.filter Nat.Prime, f n
  simp_rw [mul_comm (ArithmeticFunction.vonMangoldt _) _] at hn
  change (∑ n ∈ s.filter (fun n => ¬n.Prime), f n) < 5 at hn
  linarith only [hsplit, ht, hn]

end PseudoPrime.PrimeTestBounds.MillerRabin
