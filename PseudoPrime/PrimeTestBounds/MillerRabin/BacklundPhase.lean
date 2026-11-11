/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.Analysis.ContinuousLogInterval
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GoodHeight
public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundAuxiliary

/-! # Continuous zeta arguments at good heights -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A level attained by a continuous real function on a closed interval has
a first point of attainment. Its level set is a nonempty compact subset of
the interval, so it has a least element. -/
theorem exists_first_phase_level {a b y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (h : ∃ x ∈ Set.Icc a b, f x = y) :
    ∃ x ∈ Set.Icc a b, f x = y ∧ ∀ z ∈ Set.Icc a b, f z = y → x ≤ z := by
  let S := Set.Icc a b ∩ f ⁻¹' {y}
  have hclosed : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed (fun _ hz => hz.1)
  have hne : S.Nonempty := by
    obtain ⟨x, hx, heq⟩ := h
    exact ⟨x, hx, heq⟩
  obtain ⟨x, hx, hmin⟩ := hcompact.exists_isLeast hne
  exact ⟨x, hx.1, hx.2, fun z hz hz' => hmin ⟨hz, hz'⟩⟩

/-- If two levels lie strictly above the initial value and are increasing,
the first attainment of the lower level precedes every attainment of the
higher level. The intermediate value theorem rules out the opposite order. -/
theorem first_phase_level_lt {a b y z : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (h : f a < y) (hyz : y < z) {u v : ℝ} (hv : v ∈ Set.Icc a b) (hfu : f u = y) (hfv : f v = z)
    (hfirst : ∀ t ∈ Set.Icc a b, f t = y → u ≤ t) : u < v := by
  by_contra hn
  have hvu : v ≤ u := le_of_not_gt hn
  have hfa : f a ≤ y := h.le
  have hfcont : ContinuousOn f (Set.Icc a v) := hf.mono (Set.Icc_subset_Icc (le_refl a) hv.2)
  have him : y ∈ f '' Set.Icc a v :=
    intermediate_value_Icc hv.1 hfcont
      ⟨hfa, by
        rw [hfv]; exact hyz.le⟩
  obtain ⟨t, ht, htval⟩ := him
  have htu : u ≤ t := hfirst t ⟨ht.1, le_trans ht.2 hv.2⟩ htval
  have huv : u = v := le_antisymm (le_trans htu ht.2) hvu
  rw [huv, hfv] at hfu
  linarith only [hyz, hfu]

/-- If the sum of two reflected phase variations is at most `E` at a
right-side point and its variation reaches `E - y` for a negative level `y`,
the left-side variation attains `y` no later than that point. Continuity and
the zero initial value give a strictly positive point of attainment. -/
theorem exists_reflected_phase_level {u a b E y : ℝ} {g : ℝ → ℝ} (hu : 0 ≤ u)
    (hg : ContinuousOn g (Set.Icc 0 u)) (hg0 : g 0 = 0) (hleft : g u = b) (herror : a + b ≤ E)
    (hy : y < 0) (hlevel : E - y ≤ a) : ∃ v ∈ Set.Icc 0 u, 0 < v ∧ g v = y := by
  have hby : b ≤ y := by linarith only [herror, hlevel]
  have himage : y ∈ g '' Set.Icc 0 u := by
    apply intermediate_value_Icc' hu hg
    constructor
    · rw [hleft]; exact hby
    · rw [hg0]; exact hy.le
  obtain ⟨v, hv, hvy⟩ := himage
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, hg0] at hvy
    linarith only [hvy, hy]
  exact ⟨v, hv, lt_of_le_of_ne hv.1 (Ne.symm hv0), hvy⟩

/-- If distinct negative levels satisfy the reflected phase error inequality
at prescribed right-side points, choose distinct positive left-side points
at those levels, each no farther from the midpoint. The intermediate value
theorem gives each point, and distinct levels force distinct choices. -/
theorem exists_reflected_phase_partners (t : Finset ℝ) (u level : ℝ → ℝ) (f g : ℝ → ℝ) (E : ℝ)
    (hg : ContinuousOn g (Set.Icc 0 1)) (hg0 : g 0 = 0) (hlevinj : Set.InjOn level t)
    (hu : ∀ i ∈ t, u i ∈ Set.Icc 0 1) (hneg : ∀ i ∈ t, level i < 0)
    (herror : ∀ i ∈ t, f (u i) + g (u i) ≤ E) (hlevel : ∀ i ∈ t, E - level i ≤ f (u i)) :
    ∃ v : ℝ → ℝ, Set.InjOn v t ∧ ∀ i ∈ t, 0 < v i ∧ v i ≤ u i ∧ g (v i) = level i := by
  classical
  have hex : ∀ i : ℝ, ∃ v : ℝ, i ∈ t → 0 < v ∧ v ≤ u i ∧ g v = level i := by
    intro i
    by_cases hi : i ∈ t
    · have hgi : ContinuousOn g (Set.Icc 0 (u i)) :=
        hg.mono (Set.Icc_subset_Icc (le_refl 0) (hu i hi).2)
      obtain ⟨v, hv, hvpos, hvlevel⟩ :=
        exists_reflected_phase_level (hu i hi).1 hgi hg0 (rfl) (herror i hi) (hneg i hi)
          (hlevel i hi)
      exact ⟨v, fun _ => ⟨hvpos, hv.2, hvlevel⟩⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  let v := fun i => Classical.choose (hex i)
  have hv : ∀ i ∈ t, 0 < v i ∧ v i ≤ u i ∧ g (v i) = level i := by
    intro i hi
    exact Classical.choose_spec (hex i) hi
  refine ⟨v, ?_, hv⟩
  intro i hi j hj hij
  apply hlevinj hi hj
  calc
    level i = g (v i) := (hv i hi).2.2.symm
    _ = g (v j) := congrArg g hij
    _ = level j := (hv j hj).2.2

/-- At a positive height that is not the ordinate of a nontrivial zero,
zeta has a continuous real argument on every nonempty closed horizontal
interval. The zero-free path admits a continuous logarithm, whose imaginary
part gives the displayed polar identity. -/
theorem exists_zeta_horizontal_arg {T a b : ℝ} (hT : 0 < T) (hab : a ≤ b)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc a b) ∧
        ∀ x ∈ Set.Icc a b,
          riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I) := by
  apply Analysis.exists_continuous_arg_Icc hab
  · intro x hx
    have h1 : (x : ℂ) + (T : ℂ) * Complex.I ≠ 1 := by
      intro h
      have hi := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, zero_mul, mul_one, add_zero, zero_add, Complex.one_im] at hi
      linarith only [hT, hi]
    have hc : ContinuousAt (fun y : ℝ ↦ (y : ℂ) + (T : ℂ) * Complex.I) x :=
      (Complex.continuous_ofReal.add continuous_const).continuousAt
    have hd : ContinuousAt riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) :=
      (differentiableAt_riemannZeta h1).continuousAt
    have hcomp := ContinuousAt.comp (f := fun y : ℝ ↦ (y : ℂ) + (T : ℂ) * Complex.I) hd hc
    exact hcomp.continuousWithinAt
  · intro x hx hz
    have hi : ((x : ℂ) + (T : ℂ) * Complex.I).im = T := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, zero_mul, mul_one, add_zero, zero_add]
    have hre :=
      AnalyticNumberTheory.RiemannZeta.riemannZeta_zero_re_nonneg_of_im_ne_zero hz
        (by
          rw [hi]; exact hT.ne')
    exact hgood _ hz hre hi

/-- If the rotated phase has zero cosine, the Backlund auxiliary function
vanishes on the real axis. The polar identities give the relative phase at
the point and at the center; conjugate terms cancel at a cosine zero. -/
theorem backlundAux_eq_zero_of_cos (T x : ℝ) (N : ℕ) (α β : ℝ)
    (hα :
      riemannZeta (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I) =
        (‖riemannZeta (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ) *
          Complex.exp ((α : ℂ) * Complex.I))
    (hβ :
      riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) =
        (‖riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ) * Complex.exp ((β : ℂ) * Complex.I))
    (hc : Real.cos ((N : ℝ) * (β - α)) = 0) : backlundAux T N (x : ℂ) = 0 := by
  let w := riemannZeta (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)
  let z := riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)
  change w = (‖w‖ : ℂ) * Complex.exp ((α : ℂ) * Complex.I) at hα
  change z = (‖z‖ : ℂ) * Complex.exp ((β : ℂ) * Complex.I) at hβ
  have hw : w ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
    norm_num only
  have h0 : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
  have hconj := congrArg (starRingEnd ℂ) hα
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I, mul_neg] at hconj
  have hp :
    (starRingEnd ℂ) w / (‖w‖ : ℂ) * z =
      (‖z‖ : ℂ) * Complex.exp (((β - α : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [hconj, hβ, mul_div_cancel_left₀ _ h0]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hz : riemannZeta ((x : ℂ) - (T : ℂ) * Complex.I) = (starRingEnd ℂ) z := by
    dsimp only [z]
    rw [← riemannZeta_conj]
    congr 1
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, sub_eq_add_neg]
  have hsum (r θ : ℝ) (h : Real.cos θ = 0) :
    ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) +
        (starRingEnd ℂ) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) =
      0 := by
    rw [Complex.add_conj]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
      Real.exp_zero, h, Complex.ofReal_zero]
  change
    (((starRingEnd ℂ) w / (‖w‖ : ℂ)) ^ N * z ^ N +
          (starRingEnd ℂ) (((starRingEnd ℂ) w / (‖w‖ : ℂ)) ^ N) *
            riemannZeta ((x : ℂ) - (T : ℂ) * Complex.I) ^ N) /
        2 =
      0
  rw [hz, ← map_pow, ← map_mul, ← mul_pow, hp, mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow]
  have he :
    (N : ℂ) * (((β - α : ℝ) : ℂ) * Complex.I) = (((N : ℝ) * (β - α) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, hsum _ _ hc, zero_div]

/-- At a positive good height, a continuous argument on any interval
containing `3/2` turns every zero of the relative-phase cosine into a real
zero of the corresponding Backlund auxiliary function. This connects the
continuous phase to the zeros used in the Jensen estimate. -/
theorem exists_arg_backlund_zeros {T a b : ℝ} (hT : 0 < T) (ha : a ≤ 3 / 2) (hb : 3 / 2 ≤ b)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc a b) ∧
        ∀ x ∈ Set.Icc a b,
          ∀ N : ℕ, Real.cos ((N : ℝ) * (φ x - φ (3 / 2))) = 0 → backlundAux T N (x : ℂ) = 0 := by
  obtain ⟨φ, hcont, hpolar⟩ := exists_zeta_horizontal_arg hT (le_trans ha hb) hgood
  refine ⟨φ, hcont, ?_⟩
  intro x hx N hc
  exact backlundAux_eq_zero_of_cos T x N _ _ (hpolar _ ⟨ha, hb⟩) (hpolar _ hx) hc

/-- Every cosine-zero level between the endpoint arguments is attained at
an auxiliary-function zero. The intermediate value theorem supplies the
point, while the relative-phase identity supplies the zero. -/
theorem exists_backlund_zero_at_level {T a : ℝ} (hT : 0 < T) (ha : a ≤ 3 / 2)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc a (3 / 2)) ∧
        ∀ y ∈ Set.uIcc (φ a) (φ (3 / 2)),
          ∀ N : ℕ,
            Real.cos ((N : ℝ) * (y - φ (3 / 2))) = 0 →
              ∃ x ∈ Set.Icc a (3 / 2), φ x = y ∧ backlundAux T N (x : ℂ) = 0 := by
  obtain ⟨φ, hcont, hzero⟩ := exists_arg_backlund_zeros hT ha (le_refl _) hgood
  refine ⟨φ, hcont, ?_⟩
  intro y hy N hc
  have himage : y ∈ φ '' Set.Icc a (3 / 2) := by
    rcases le_total (φ a) (φ (3 / 2)) with h | h
    · exact intermediate_value_Icc ha hcont (by simpa only [Set.uIcc_of_le h] using hy)
    · exact intermediate_value_Icc' ha hcont (by simpa only [Set.uIcc_of_ge h] using hy)
  obtain ⟨x, hx, hxy⟩ := himage
  exact
    ⟨x, hx, hxy,
      hzero x hx N
        (by
          rw [hxy]; exact hc)⟩

/-- On a closed interval, select the first attainment of each level in a
finite set. If every cosine-zero level gives an auxiliary zero, the selected
points are distinct auxiliary zeros. This form permits restrictions of one
continuous argument to different subintervals. -/
theorem select_backlund_level_zeros {T a b θ : ℝ} {φ : ℝ → ℝ} (N : ℕ) (hab : a ≤ b)
    (hcont : ContinuousOn φ (Set.Icc a b))
    (hzero : ∀ x ∈ Set.Icc a b, Real.cos ((N : ℝ) * (φ x - θ)) = 0 → backlundAux T N (x : ℂ) = 0)
    (s : Finset ℝ) (hs : ∀ y ∈ s, y ∈ Set.uIcc (φ a) (φ b) ∧ Real.cos ((N : ℝ) * (y - θ)) = 0) :
    ∃ x : ℝ → ℝ,
      Set.InjOn x s ∧
        ∀ y ∈ s,
          x y ∈ Set.Icc a b ∧
            φ (x y) = y ∧ backlundAux T N (x y : ℂ) = 0 ∧ ∀ z ∈ Set.Icc a b, φ z = y → x y ≤ z := by
  classical
  have hex :
    ∀ y : ℝ,
      ∃ x : ℝ,
        y ∈ s →
          x ∈ Set.Icc a b ∧
            φ x = y ∧ backlundAux T N (x : ℂ) = 0 ∧ ∀ z ∈ Set.Icc a b, φ z = y → x ≤ z := by
    intro y
    by_cases hy : y ∈ s
    · have hp : ∃ x ∈ Set.Icc a b, φ x = y := by
        have himage : y ∈ φ '' Set.Icc a b := by
          rcases le_total (φ a) (φ b) with h | h
          · exact
              intermediate_value_Icc hab hcont (by simpa only [Set.uIcc_of_le h] using (hs y hy).1)
          · exact
              intermediate_value_Icc' hab hcont (by simpa only [Set.uIcc_of_ge h] using (hs y hy).1)
        exact himage
      obtain ⟨x, hx, hxy, hfirst⟩ := exists_first_phase_level hcont hp
      have hxzero : backlundAux T N (x : ℂ) = 0 := by
        apply hzero x hx
        rw [hxy]
        exact (hs y hy).2
      exact ⟨x, fun _ => ⟨hx, hxy, hxzero, hfirst⟩⟩
    · exact ⟨0, fun h => (hy h).elim⟩
  let x := fun y => Classical.choose (hex y)
  have hx :
    ∀ y ∈ s,
      x y ∈ Set.Icc a b ∧
        φ (x y) = y ∧ backlundAux T N (x y : ℂ) = 0 ∧ ∀ z ∈ Set.Icc a b, φ z = y → x y ≤ z := by
    intro y hy
    exact Classical.choose_spec (hex y) hy
  refine ⟨x, ?_, hx⟩
  intro y hy z hz hyz
  calc
    y = φ (x y) := (hx y hy).2.1.symm
    _ = φ (x z) := congrArg φ hyz
    _ = z := (hx z hz).2.1

/-- For every finite set of distinct cosine-zero levels between the endpoint
arguments, choose their first points of attainment. They are distinct real
zeros of the auxiliary function, because equality of two chosen points forces
equality of their phase levels. -/
theorem exists_backlund_zeros_at_levels {T a : ℝ} (hT : 0 < T) (ha : a ≤ 3 / 2)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc a (3 / 2)) ∧
        ∀ N : ℕ,
          ∀ s : Finset ℝ,
            (∀ y ∈ s, y ∈ Set.uIcc (φ a) (φ (3 / 2)) ∧ Real.cos ((N : ℝ) * (y - φ (3 / 2))) = 0) →
              ∃ x : ℝ → ℝ,
                Set.InjOn x s ∧
                  ∀ y ∈ s,
                    x y ∈ Set.Icc a (3 / 2) ∧
                      φ (x y) = y ∧
                      backlundAux T N (x y : ℂ) = 0 ∧
                      ∀ z ∈ Set.Icc a (3 / 2), φ z = y → x y ≤ z := by
  obtain ⟨φ, hcont, hzero⟩ := exists_arg_backlund_zeros hT ha (le_refl _) hgood
  refine ⟨φ, hcont, ?_⟩
  intro N s hs
  exact select_backlund_level_zeros N ha hcont (fun x hx => hzero x hx N) s hs

end PseudoPrime.PrimeTestBounds.MillerRabin
