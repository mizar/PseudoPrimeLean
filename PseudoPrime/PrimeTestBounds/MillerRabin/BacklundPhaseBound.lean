/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundRightGrid
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundLevelBudget
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundGrid

/-! # Phase bounds from reflected Backlund zeros -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a continuous argument whose endpoint variation is nonnegative, a
uniform reflected phase error `E` gives the finite-exponent Backlund phase
bound. The cosine grid, reflected partners and Jensen budget are constructed
from the stated hypotheses; the reflected error itself remains an input. -/
theorem backlund_phase_bound_nonneg {T E : ℝ} (hT : 17 ≤ T) (hE : 0 ≤ E) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hzero :
      ∀ x ∈ Set.Icc (-(1 / 2)) (3 / 2),
        ∀ N : ℕ, Real.cos ((N : ℝ) * (φ x - φ (3 / 2))) = 0 → backlundAux T N (x : ℂ) = 0)
    (herror :
      ∀ u ∈ Set.Icc (0 : ℝ) 1, |(φ (1 / 2 + u) - φ (1 / 2)) + (φ (1 / 2 - u) - φ (1 / 2))| ≤ E)
    (horder : φ (1 / 2) ≤ φ (3 / 2)) {N : ℕ} (hN : 0 < N) :
    |φ (3 / 2) - φ (1 / 2)| / Real.pi ≤
      ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
          (2 * Real.log 2) +
        (E / Real.pi) / 2 +
        5 / (2 * (N : ℝ)) := by
  let m : ℝ := φ (1 / 2)
  let θ : ℝ := φ (3 / 2)
  let f : ℝ → ℝ := fun u => φ (1 / 2 + u) - m
  let g : ℝ → ℝ := fun u => φ (1 / 2 - u) - m
  have hright : Set.Icc (1 / 2 : ℝ) (3 / 2) ⊆ Set.Icc (-(1 / 2)) (3 / 2) :=
    Set.Icc_subset_Icc (by norm_num only) (le_refl _)
  obtain ⟨s, u, hiu, hu, hs, hcount⟩ :=
    exists_backlund_right_grid (hcont.mono hright) (fun x hx N h => hzero x (hright hx) N h) hN
  obtain ⟨D, hED, hD, hshift⟩ := exists_cos_reflection_shift_above m θ E hN
  have hD0 : 0 ≤ D := le_trans hE hED
  have hs' : ∀ y ∈ s, m ≤ y ∧ Real.cos ((N : ℝ) * (y - θ)) = 0 := by
    intro y hy
    have h := hs y hy
    have hm : y ∈ Set.Icc m θ := by simpa only [Set.uIcc_of_le horder] using h.1
    exact ⟨hm.1, h.2⟩
  obtain ⟨t, hts, hfar, hpair⟩ := exists_cos_grid_far_above m θ D hN hD0 s hs'
  let level : ℝ → ℝ := fun i => m - i + D
  have hlevelinj : Set.InjOn level t := by
    intro i hi j hj he
    dsimp only [level] at he
    linarith only [he]
  have hg : ContinuousOn g (Set.Icc 0 1) := by
    have hm : Set.MapsTo (fun v : ℝ => 1 / 2 - v) (Set.Icc 0 1) (Set.Icc (-(1 / 2)) (3 / 2)) := by
      intro v hv
      constructor <;> linarith only [hv.1, hv.2]
    have hc := hcont.comp (continuous_const.sub continuous_id).continuousOn hm
    exact hc.sub continuousOn_const
  have hg0 : g 0 = 0 := by simp only [g, m, sub_zero, sub_self]
  have hneg : ∀ i ∈ t, level i < 0 := by
    intro i hi
    dsimp only [level]
    linarith only [hfar i hi]
  have herr : ∀ i ∈ t, f (u i) + g (u i) ≤ E := by
    intro i hi
    have hu' := hu i (hts hi)
    exact (abs_le.mp (herror (u i) ⟨hu'.1.le, hu'.2.1.le⟩)).2
  have hlev : ∀ i ∈ t, E - level i ≤ f (u i) := by
    intro i hi
    have hv := (hu i (hts hi)).2.2.1
    dsimp only [f, level]
    rw [hv]
    linarith only [hED]
  have hleftzero :
    ∀ i ∈ t, ∀ v ∈ Set.Icc 0 1, g v = level i → backlundAux T N (((1 / 2 - v : ℝ) : ℂ)) = 0 := by
    intro i hi v hv hgv
    refine hzero (1 / 2 - v) ?_ N ?_
    · constructor <;> linarith only [hv.1, hv.2]
    · have hcos := hshift i (hs' i (hts hi)).2
      have he : φ (1 / 2 - v) = 2 * m - i + D := by
        dsimp only [g, level] at hgv
        linarith only [hgv]
      rw [he]
      exact hcos
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hcoeff : 0 < (N : ℝ) / Real.pi := div_pos hn Real.pi_pos
  have hmul := mul_lt_mul_of_pos_left hD hcoeff
  have he : ((N : ℝ) / Real.pi) * (2 * (Real.pi / (N : ℝ))) = 2 := by
    calc
      _ = 2 * (((N : ℝ) * (Real.pi / (N : ℝ))) / Real.pi) := by ring
      _ = 2 := by
        rw [mul_div_cancel₀ Real.pi hn.ne', div_self Real.pi_ne_zero]; ring
  have hloss : (N : ℝ) * D / Real.pi + 1 ≤ (N : ℝ) * (E / Real.pi) + 3 := by
    simp only [div_eq_mul_inv] at hmul he ⊢
    nlinarith only [hmul, he]
  apply
    backlund_phase_bound_of_reflection hT hN s t hts u level f g E hiu hlevelinj
      (fun i hi => ⟨(hu i hi).1, (hu i hi).2.1⟩) (fun i hi => (hu i hi).2.2.2) hg hg0 hneg herr hlev
      hleftzero (|φ (3 / 2) - φ (1 / 2)| / Real.pi) (E / Real.pi) ((N : ℝ) * D / Real.pi + 1) hcount
      hpair hloss

/-- A continuous argument with reflected phase error at most `E` satisfies
the finite-exponent Backlund phase bound for either sign of its endpoint
variation. Negating the argument reduces the negative case to the
nonnegative case, since cosine and absolute value are even. -/
theorem backlund_phase_bound {T E : ℝ} (hT : 17 ≤ T) (hE : 0 ≤ E) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hzero :
      ∀ x ∈ Set.Icc (-(1 / 2)) (3 / 2),
        ∀ N : ℕ, Real.cos ((N : ℝ) * (φ x - φ (3 / 2))) = 0 → backlundAux T N (x : ℂ) = 0)
    (herror :
      ∀ u ∈ Set.Icc (0 : ℝ) 1, |(φ (1 / 2 + u) - φ (1 / 2)) + (φ (1 / 2 - u) - φ (1 / 2))| ≤ E)
    {N : ℕ} (hN : 0 < N) :
    |φ (3 / 2) - φ (1 / 2)| / Real.pi ≤
      ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
          (2 * Real.log 2) +
        (E / Real.pi) / 2 +
        5 / (2 * (N : ℝ)) := by
  rcases le_total (φ (1 / 2)) (φ (3 / 2)) with h | h
  · exact backlund_phase_bound_nonneg hT hE hcont hzero herror h hN
  · let ψ : ℝ → ℝ := fun x => -φ x
    have hψ : ContinuousOn ψ (Set.Icc (-(1 / 2)) (3 / 2)) := hcont.neg
    have hz :
      ∀ x ∈ Set.Icc (-(1 / 2)) (3 / 2),
        ∀ N : ℕ, Real.cos ((N : ℝ) * (ψ x - ψ (3 / 2))) = 0 → backlundAux T N (x : ℂ) = 0 := by
      intro x hx n hc
      apply hzero x hx n
      have he : (n : ℝ) * (ψ x - ψ (3 / 2)) = -((n : ℝ) * (φ x - φ (3 / 2))) := by
        dsimp only [ψ]; ring
      rw [he, Real.cos_neg] at hc
      exact hc
    have herr :
      ∀ u ∈ Set.Icc (0 : ℝ) 1, |(ψ (1 / 2 + u) - ψ (1 / 2)) + (ψ (1 / 2 - u) - ψ (1 / 2))| ≤ E := by
      intro u hu
      have he :
        (ψ (1 / 2 + u) - ψ (1 / 2)) + (ψ (1 / 2 - u) - ψ (1 / 2)) =
          -((φ (1 / 2 + u) - φ (1 / 2)) + (φ (1 / 2 - u) - φ (1 / 2))) := by
        dsimp only [ψ]; ring
      rw [he, abs_neg]
      exact herror u hu
    have horder : ψ (1 / 2) ≤ ψ (3 / 2) := neg_le_neg h
    have hb := backlund_phase_bound_nonneg hT hE hψ hz herr horder hN
    have he : ψ (3 / 2) - ψ (1 / 2) = -(φ (3 / 2) - φ (1 / 2)) := by
      dsimp only [ψ]; ring
    rw [he, abs_neg] at hb
    exact hb

/-- A continuous argument with reflected error at most `E` satisfies the
Backlund phase bound without an exponent-dependent remainder. Apply the
finite-exponent estimate for every positive integer and send `1/N` to zero;
no convergence assertion for the Jensen sums is needed. -/
theorem backlund_phase_bound_limit {T E : ℝ} (hT : 17 ≤ T) (hE : 0 ≤ E) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hzero :
      ∀ x ∈ Set.Icc (-(1 / 2)) (3 / 2),
        ∀ N : ℕ, Real.cos ((N : ℝ) * (φ x - φ (3 / 2))) = 0 → backlundAux T N (x : ℂ) = 0)
    (herror :
      ∀ u ∈ Set.Icc (0 : ℝ) 1, |(φ (1 / 2 + u) - φ (1 / 2)) + (φ (1 / 2 - u) - φ (1 / 2))| ≤ E) :
    |φ (3 / 2) - φ (1 / 2)| / Real.pi ≤
      ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
          (2 * Real.log 2) +
        (E / Real.pi) / 2 := by
  let K : ℝ :=
    ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
        (2 * Real.log 2) +
      (E / Real.pi) / 2
  have ht : Filter.Tendsto (fun n : ℕ => K + ((5 / 2 : ℝ) / (n : ℝ))) Filter.atTop (nhds K) := by
    simpa only [add_zero] using (tendsto_const_div_atTop_nhds_zero_nat (5 / 2 : ℝ)).const_add K
  apply ge_of_tendsto ht
  filter_upwards [Nat.eventually_pos] with n hn
  simpa only [K, div_div] using backlund_phase_bound hT hE hcont hzero herror hn

/-- A continuous polar argument for zeta on the Backlund horizontal segment
obeys the explicit phase bound whenever its reflected variation is bounded
by `E`. The polar identities supply the auxiliary-zero condition internally. -/
theorem backlund_zeta_phase_bound {T E : ℝ} (hT : 17 ≤ T) (hE : 0 ≤ E) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hpolar :
      ∀ x : ℝ,
        x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
          riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I))
    (herror :
      ∀ u ∈ Set.Icc (0 : ℝ) 1, |(φ (1 / 2 + u) - φ (1 / 2)) + (φ (1 / 2 - u) - φ (1 / 2))| ≤ E) :
    |φ (3 / 2) - φ (1 / 2)| / Real.pi ≤
      ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
          (2 * Real.log 2) +
        (E / Real.pi) / 2 := by
  apply backlund_phase_bound_limit hT hE hcont ?_ herror
  intro x hx N hc
  apply backlundAux_eq_zero_of_cos T x N (φ (3 / 2)) (φ x)
  · exact hpolar _ ⟨by norm_num only, le_refl _⟩
  · exact hpolar x hx
  · exact hc

end PseudoPrime.PrimeTestBounds.MillerRabin
