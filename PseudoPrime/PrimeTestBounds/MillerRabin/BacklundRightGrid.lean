/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundPhase
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundGrid

/-! # Right-side phase levels for the Backlund argument -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A continuous zeta argument and its cosine-zero property yield distinct
right-side auxiliary zeros at an open grid of phase levels. The number of
levels is at least the absolute endpoint phase variation divided by the grid
spacing, minus one. Endpoints are excluded, so every distance lies in `(0,1)`. -/
theorem exists_backlund_right_grid {T : ℝ} {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (1 / 2) (3 / 2)))
    (hzero :
      ∀ x ∈ Set.Icc (1 / 2) (3 / 2),
        ∀ N : ℕ, Real.cos ((N : ℝ) * (φ x - φ (3 / 2))) = 0 → backlundAux T N (x : ℂ) = 0)
    {N : ℕ} (hN : 0 < N) :
    ∃ s : Finset ℝ,
      ∃ u : ℝ → ℝ,
        Set.InjOn u s ∧
          (∀ i ∈ s,
            0 < u i ∧
              u i < 1 ∧ φ (1 / 2 + u i) = i ∧ backlundAux T N (((1 / 2 + u i : ℝ) : ℂ)) = 0) ∧
          (∀ i ∈ s,
            i ∈ Set.uIcc (φ (1 / 2)) (φ (3 / 2)) ∧ Real.cos ((N : ℝ) * (i - φ (3 / 2))) = 0) ∧
          (N : ℝ) * (|φ (3 / 2) - φ (1 / 2)| / Real.pi) ≤ (s.card : ℝ) + 1 := by
  classical
  let a : ℝ := φ (1 / 2)
  let b : ℝ := φ (3 / 2)
  obtain ⟨s, hs, hcard⟩ := exists_cos_phase_grid (min a b) (max a b) b hN
  have hlevels :
    ∀ y ∈ s, y ∈ Set.uIcc (φ (1 / 2)) (φ (3 / 2)) ∧ Real.cos ((N : ℝ) * (y - φ (3 / 2))) = 0 := by
    intro y hy
    have hy' := hs y hy
    constructor
    · change y ∈ Set.Icc (min a b) (max a b)
      exact ⟨hy'.1.le, hy'.2.1.le⟩
    · exact hy'.2.2
  obtain ⟨x, hxi, hx⟩ :=
    select_backlund_level_zeros N (by norm_num only) hcont (fun x hx => hzero x hx N) s hlevels
  let u : ℝ → ℝ := fun i => x i - 1 / 2
  have hui : Set.InjOn u s := by
    intro i hi j hj he
    apply hxi hi hj
    dsimp only [u] at he
    linarith only [he]
  refine ⟨s, u, hui, ?_, hlevels, ?_⟩
  · intro i hi
    have hx' := hx i hi
    have hs' := hs i hi
    have hne1 : x i ≠ 1 / 2 := by
      intro he
      have hia : i = a := by
        dsimp only [a]
        rw [← hx'.2.1, he]
      rcases le_total a b with hab | hba
      · rw [min_eq_left hab, hia] at hs'
        exact (lt_irrefl a) hs'.1
      · rw [max_eq_left hba, hia] at hs'
        exact (lt_irrefl a) hs'.2.1
    have hne2 : x i ≠ 3 / 2 := by
      intro he
      have hib : i = b := by
        dsimp only [b]
        rw [← hx'.2.1, he]
      rcases le_total a b with hab | hba
      · rw [max_eq_right hab, hib] at hs'
        exact (lt_irrefl b) hs'.2.1
      · rw [min_eq_right hba, hib] at hs'
        exact (lt_irrefl b) hs'.1
    have hlo : (1 / 2 : ℝ) < x i := lt_of_le_of_ne hx'.1.1 (Ne.symm hne1)
    have hhi : x i < 3 / 2 := lt_of_le_of_ne hx'.1.2 hne2
    have he : (1 / 2 : ℝ) + u i = x i := by
      dsimp only [u]; ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [u]; linarith only [hlo]
    · dsimp only [u]; linarith only [hhi]
    · rw [he]; exact hx'.2.1
    · rw [he]; exact hx'.2.2.1
  · rw [max_sub_min_eq_abs] at hcard
    rw [← mul_div_assoc]
    linarith only [hcard]

end PseudoPrime.PrimeTestBounds.MillerRabin
