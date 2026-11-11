/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundPhase
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundZeroWeight
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundPairWeights

/-! # Jensen budgets for Backlund phase levels -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Combine the level count, the reflected-pair count and the Jensen budget.
The positive factors allow division by the exponent and by the single-zero
weight. This is the scalar step used after constructing the phase grid. -/
private theorem phase_budget_algebra (N A B K L m p k : ℝ) (hN : 0 < N) (hL : 0 < L)
    (hc : N * A ≤ m + 1) (hp : m - k ≤ p) (hk : k ≤ N * B + 3) (hj : (m + p) * L ≤ N * K) :
    A ≤ K / (2 * L) + B / 2 + 5 / (2 * N) := by
  have hm : 2 * N * A ≤ m + p + N * B + 5 := by nlinarith only [hc, hp, hk]
  have hmL := mul_le_mul_of_nonneg_right hm hL.le
  have hn : 0 < 2 * N * L := mul_pos (mul_pos (by norm_num only) hN) hL
  have hK : K / (2 * L) * (2 * N * L) = N * K := by
    calc
      _ = (K / (2 * L) * (2 * L)) * N := by ring
      _ = _ := by
        rw [div_mul_cancel₀ _ (mul_ne_zero (by norm_num only) hL.ne')]; ring
  have hB : B / 2 * (2 * N * L) = N * B * L := by
    calc
      _ = (B / 2 * 2) * (N * L) := by ring
      _ = _ := by
        rw [div_mul_cancel₀ _ (by norm_num only : (2 : ℝ) ≠ 0)]; ring
  have h5 : 5 / (2 * N) * (2 * N * L) = 5 * L := by
    calc
      _ = (5 / (2 * N) * (2 * N)) * L := by ring
      _ = _ := by rw [div_mul_cancel₀ _ (mul_ne_zero (by norm_num only) hN.ne')]
  apply (mul_le_mul_iff_left₀ hn).mp
  rw [add_mul, add_mul, hK, hB, h5]
  nlinarith only [hmL, hj]

/-- At a good height at least 17, any finite family of cosine-zero phase
levels between the endpoint arguments admits distinct first-attainment
zeros whose total Jensen weight is bounded by the explicit circle budget.
The real interval must lie within `[-1/2, 3/2]`. -/
theorem exists_backlund_level_budget {T a : ℝ} (hT : 17 ≤ T) (ha : -(1 / 2 : ℝ) ≤ a)
    (hab : a ≤ 3 / 2) (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc a (3 / 2)) ∧
        ∀ N : ℕ,
          ∀ s : Finset ℝ,
            (∀ y ∈ s, y ∈ Set.uIcc (φ a) (φ (3 / 2)) ∧ Real.cos ((N : ℝ) * (y - φ (3 / 2))) = 0) →
              ∃ x : ℝ → ℝ,
                Set.InjOn x s ∧
                  (∀ y ∈ s,
                    x y ∈ Set.Icc a (3 / 2) ∧
                      φ (x y) = y ∧
                      backlundAux T N (x y : ℂ) = 0 ∧ ∀ z ∈ Set.Icc a (3 / 2), φ z = y → x y ≤ z) ∧
                  (∑ y ∈ s, Real.log (2 * ‖(((3 / 2 : ℝ) : ℂ)) - (x y : ℂ)‖⁻¹)) ≤
                    (N : ℝ) *
                      ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T +
                        3 / (T - 2) ^ 2) := by
  obtain ⟨φ, hcont, hchoose⟩ := exists_backlund_zeros_at_levels (by linarith only [hT]) hab hgood
  refine ⟨φ, hcont, ?_⟩
  intro N s hs
  obtain ⟨x, hi, hx⟩ := hchoose N s hs
  refine ⟨x, hi, hx, ?_⟩
  apply backlundAux_indexed_weights_budget hT ha N s x hi
  intro y hy
  exact ⟨(hx y hy).1, (hx y hy).2.2.1⟩

/-- Any injectively indexed finite family of real auxiliary zeros in
`[1/2, 3/2]` contributes at least `log 2` per zero to the Jensen sum.
The explicit circle budget therefore bounds the number of these zeros. -/
theorem backlund_right_zero_count_budget {T : ℝ} (hT : 17 ≤ T) (N : ℕ) (s : Finset ℝ) (x : ℝ → ℝ)
    (hinj : Set.InjOn x s)
    (hx : ∀ y ∈ s, x y ∈ Set.Icc (1 / 2) (3 / 2) ∧ backlundAux T N (x y : ℂ) = 0) :
    (s.card : ℝ) * Real.log 2 ≤
      (N : ℝ) * ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) := by
  have hlower :
    (s.card : ℝ) * Real.log 2 ≤ ∑ y ∈ s, Real.log (2 * ‖(((3 / 2 : ℝ) : ℂ)) - (x y : ℂ)‖⁻¹) := by
    calc
      (s.card : ℝ) * Real.log 2 = ∑ _y ∈ s, Real.log 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ s, Real.log (2 * ‖(((3 / 2 : ℝ) : ℂ)) - (x y : ℂ)‖⁻¹) := by
        apply Finset.sum_le_sum
        intro y hy
        have hr := (hx y hy).1
        have hne : x y ≠ 3 / 2 := by
          intro h
          have hz := (hx y hy).2
          rw [h] at hz
          exact backlundAux_center_ne_zero T N hz
        have hp : 0 < (3 / 2 : ℝ) - x y := by
          have hlt : x y < 3 / 2 := lt_of_le_of_ne hr.2 hne
          linarith only [hlt]
        have hle : (3 / 2 : ℝ) - x y ≤ 1 := by linarith only [hr.1]
        have hw := backlund_single_weight hp hle
        have hnorm : ‖(((3 / 2 : ℝ) : ℂ)) - (x y : ℂ)‖ = (3 / 2 : ℝ) - x y := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
        rw [hnorm, ← div_eq_mul_inv]
        exact hw
  apply hlower.trans
  apply backlundAux_indexed_weights_budget hT (a := 1 / 2) (by norm_num only) N s x hinj
  exact hx

/-- Two injectively indexed families of auxiliary zeros on opposite sides
of `1/2` have combined Jensen weight at most the circle budget. Their
images are disjoint, so both families can be included in one zero sum. -/
theorem backlund_two_weights_budget {T : ℝ} (hT : 17 ≤ T) (N : ℕ) (s t : Finset ℝ) (x y : ℝ → ℝ)
    (hix : Set.InjOn x s) (hiy : Set.InjOn y t)
    (hx : ∀ i ∈ s, (1 / 2 : ℝ) < x i ∧ x i ≤ 3 / 2 ∧ backlundAux T N (x i : ℂ) = 0)
    (hy : ∀ i ∈ t, -(1 / 2 : ℝ) ≤ y i ∧ y i < 1 / 2 ∧ backlundAux T N (y i : ℂ) = 0) :
    (∑ i ∈ s, Real.log (2 * ‖(((3 / 2 : ℝ) : ℂ)) - (x i : ℂ)‖⁻¹)) +
        (∑ i ∈ t, Real.log (2 * ‖(((3 / 2 : ℝ) : ℂ)) - (y i : ℂ)‖⁻¹)) ≤
      (N : ℝ) * ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) := by
  classical
  let f : ℝ → ℂ := fun i => (x i : ℂ)
  let g : ℝ → ℂ := fun i => (y i : ℂ)
  have hfi : Set.InjOn f s := fun _ ha _ hb h => hix ha hb (Complex.ofReal_injective h)
  have hgi : Set.InjOn g t := fun _ ha _ hb h => hiy ha hb (Complex.ofReal_injective h)
  have hdis : Disjoint (s.image f) (t.image g) := by
    apply Finset.disjoint_left.mpr
    intro z hz hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hw
    have heq' : x i = y j := Complex.ofReal_injective heq.symm
    linarith only [(hx i hi).1, (hy j hj).2.1, heq']
  have hmem :
    ∀ z ∈ s.image f ∪ t.image g,
      z ∈ Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2 ∧ backlundAux T N z = 0 := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hr := hx i hi
      constructor
      · change (x i : ℂ) ∈ Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2
        rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith only [hr.1, hr.2.1]
      · exact hr.2.2
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hr := hy i hi
      constructor
      · change (y i : ℂ) ∈ Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2
        rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith only [hr.1, hr.2.1]
      · exact hr.2.2
  have h := backlundAux_zero_weights_budget hT N (s.image f ∪ t.image g) hmem
  rw [Finset.sum_union hdis, Finset.sum_image hfi, Finset.sum_image hgi] at h
  exact h

/-- For a finite family of distinct right-side auxiliary zeros and a subset
with distinct reflected left-side partners satisfying `0 < v ≤ u < 1`,
the circle budget is at least `log 2` per right zero plus `log 2` per pair.
The two disjoint zero families are counted together in the Jensen sum. -/
theorem backlund_partial_pair_count_budget {T : ℝ} (hT : 17 ≤ T) (N : ℕ) (s t : Finset ℝ)
    (hts : t ⊆ s) (u v : ℝ → ℝ) (hiu : Set.InjOn u s) (hiv : Set.InjOn v t)
    (hu : ∀ i ∈ s, 0 < u i ∧ u i < 1) (hv : ∀ i ∈ t, 0 < v i ∧ v i ≤ u i)
    (huz : ∀ i ∈ s, backlundAux T N (((1 / 2 + u i : ℝ) : ℂ)) = 0)
    (hvz : ∀ i ∈ t, backlundAux T N (((1 / 2 - v i : ℝ) : ℂ)) = 0) :
    ((s.card : ℝ) + (t.card : ℝ)) * Real.log 2 ≤
      (N : ℝ) * ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) := by
  let x : ℝ → ℝ := fun i => 1 / 2 + u i
  let y : ℝ → ℝ := fun i => 1 / 2 - v i
  have hix : Set.InjOn x s := by
    intro i hi j hj h
    apply hiu hi hj
    dsimp only [x] at h
    linarith only [h]
  have hiy : Set.InjOn y t := by
    intro i hi j hj h
    apply hiv hi hj
    dsimp only [y] at h
    linarith only [h]
  have hx : ∀ i ∈ s, (1 / 2 : ℝ) < x i ∧ x i ≤ 3 / 2 ∧ backlundAux T N (x i : ℂ) = 0 := by
    intro i hi
    have h := hu i hi
    exact
      ⟨by
        dsimp only [x]; linarith only [h.1], by
        dsimp only [x]; linarith only [h.2], huz i hi⟩
  have hy : ∀ i ∈ t, -(1 / 2 : ℝ) ≤ y i ∧ y i < 1 / 2 ∧ backlundAux T N (y i : ℂ) = 0 := by
    intro i hi
    have h := hv i hi
    have hu' := hu i (hts hi)
    exact
      ⟨by
        dsimp only [y]; linarith only [h.2, hu'.2], by
        dsimp only [y]; linarith only [h.1], hvz i hi⟩
  have hbudget := backlund_two_weights_budget hT N s t x y hix hiy hx hy
  have hs :=
    backlund_partial_pair_weights s t hts u v hu (fun i hi => ⟨(hv i hi).1.le, (hv i hi).2⟩)
  apply hs.trans
  convert hbudget using 1
  · apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro i hi
    · have hp : 0 < (1 : ℝ) - u i := by linarith only [(hu i hi).2]
      have he : ‖(((3 / 2 : ℝ) : ℂ)) - (x i : ℂ)‖ = 1 - u i := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        dsimp only [x]
        rw [abs_of_pos (by linarith only [hp] : 0 < (3 / 2 : ℝ) - (1 / 2 + u i))]
        ring
      rw [he, ← div_eq_mul_inv]
    · have hp : 0 < (1 : ℝ) + v i := by linarith only [(hv i hi).1]
      have he : ‖(((3 / 2 : ℝ) : ℂ)) - (y i : ℂ)‖ = 1 + v i := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        dsimp only [y]
        rw [abs_of_pos (by linarith only [hp] : 0 < (3 / 2 : ℝ) - (1 / 2 - v i))]
        ring
      rw [he, ← div_eq_mul_inv]

/-- Given a phase-level count and a reflected-pair count with the stated
loss, the Backlund circle budget yields the corresponding phase bound. The
remaining hypotheses isolate the construction of the level grid and its
reflected partners; no limit of Jensen sums is used. -/
theorem backlund_phase_bound_of_pairs {T : ℝ} (hT : 17 ≤ T) {N : ℕ} (hN : 0 < N) (s t : Finset ℝ)
    (hts : t ⊆ s) (u v : ℝ → ℝ) (hiu : Set.InjOn u s) (hiv : Set.InjOn v t)
    (hu : ∀ i ∈ s, 0 < u i ∧ u i < 1) (hv : ∀ i ∈ t, 0 < v i ∧ v i ≤ u i)
    (huz : ∀ i ∈ s, backlundAux T N (((1 / 2 + u i : ℝ) : ℂ)) = 0)
    (hvz : ∀ i ∈ t, backlundAux T N (((1 / 2 - v i : ℝ) : ℂ)) = 0) (A B k : ℝ)
    (hcount : (N : ℝ) * A ≤ (s.card : ℝ) + 1) (hpair : (s.card : ℝ) - k ≤ (t.card : ℝ))
    (hloss : k ≤ (N : ℝ) * B + 3) :
    A ≤
      ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
          (2 * Real.log 2) +
        B / 2 +
        5 / (2 * (N : ℝ)) := by
  apply
    phase_budget_algebra (N : ℝ) A B _ (Real.log 2) s.card t.card k (Nat.cast_pos.mpr hN)
      (Real.log_pos (by norm_num only)) hcount hpair hloss
  exact backlund_partial_pair_count_budget hT N s t hts u v hiu hiv hu hv huz hvz

/-- A reflected phase error and a sufficiently separated family of distinct
left-side levels supply the partners needed by the Jensen phase bound.
The right-side level count and the number of discarded levels remain explicit
inputs, ready for the arithmetic construction of the phase grid. -/
theorem backlund_phase_bound_of_reflection {T : ℝ} (hT : 17 ≤ T) {N : ℕ} (hN : 0 < N)
    (s t : Finset ℝ) (hts : t ⊆ s) (u level f g : ℝ → ℝ) (E : ℝ) (hiu : Set.InjOn u s)
    (hlevinj : Set.InjOn level t) (hu : ∀ i ∈ s, 0 < u i ∧ u i < 1)
    (huz : ∀ i ∈ s, backlundAux T N (((1 / 2 + u i : ℝ) : ℂ)) = 0)
    (hg : ContinuousOn g (Set.Icc 0 1)) (hg0 : g 0 = 0) (hneg : ∀ i ∈ t, level i < 0)
    (herror : ∀ i ∈ t, f (u i) + g (u i) ≤ E) (hlevel : ∀ i ∈ t, E - level i ≤ f (u i))
    (hzero :
      ∀ i ∈ t, ∀ v ∈ Set.Icc 0 1, g v = level i → backlundAux T N (((1 / 2 - v : ℝ) : ℂ)) = 0)
    (A B k : ℝ) (hcount : (N : ℝ) * A ≤ (s.card : ℝ) + 1) (hpair : (s.card : ℝ) - k ≤ (t.card : ℝ))
    (hloss : k ≤ (N : ℝ) * B + 3) :
    A ≤
      ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
          (2 * Real.log 2) +
        B / 2 +
        5 / (2 * (N : ℝ)) := by
  have hu' : ∀ i ∈ t, u i ∈ Set.Icc 0 1 := by
    intro i hi
    exact ⟨(hu i (hts hi)).1.le, (hu i (hts hi)).2.le⟩
  obtain ⟨v, hiv, hv⟩ :=
    exists_reflected_phase_partners t u level f g E hg hg0 hlevinj hu' hneg herror hlevel
  apply
    backlund_phase_bound_of_pairs hT hN s t hts u v hiu hiv hu
      (fun i hi => ⟨(hv i hi).1, (hv i hi).2.1⟩) huz ?_ A B k hcount hpair hloss
  intro i hi
  apply hzero i hi (v i)
  · exact ⟨(hv i hi).1.le, le_trans (hv i hi).2.1 (hu' i hi).2⟩
  · exact (hv i hi).2.2

/-- At a good height at least 17, the number of distinct cosine-zero
levels between the arguments at `1/2` and `3/2` is bounded by the explicit
Jensen budget divided by `log 2`. First-attainment points provide distinct
zeros in the right half of the Jensen disk. -/
theorem exists_right_phase_count_budget {T : ℝ} (hT : 17 ≤ T)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc (1 / 2) (3 / 2)) ∧
        ∀ N : ℕ,
          ∀ s : Finset ℝ,
            (∀ y ∈ s,
                y ∈ Set.uIcc (φ (1 / 2)) (φ (3 / 2)) ∧ Real.cos ((N : ℝ) * (y - φ (3 / 2))) = 0) →
              (s.card : ℝ) * Real.log 2 ≤
                (N : ℝ) *
                  ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T +
                    3 / (T - 2) ^ 2) := by
  obtain ⟨φ, hcont, hselect⟩ :=
    exists_backlund_zeros_at_levels (by linarith only [hT]) (a := 1 / 2) (by norm_num only) hgood
  refine ⟨φ, hcont, ?_⟩
  intro N s hs
  obtain ⟨x, hinj, hx⟩ := hselect N s hs
  apply backlund_right_zero_count_budget hT N s x hinj
  intro y hy
  exact ⟨(hx y hy).1, (hx y hy).2.2.1⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
