/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Int.Interval

/-! # Integer phase grids for the Backlund argument -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A cosine-zero phase has an integral coordinate on the grid of odd
half-multiples of `π`. This is the coordinate used to count arbitrary finite
sets of grid points. -/
private theorem cos_phase_index (θ y : ℝ) {N : ℕ} (hy : Real.cos ((N : ℝ) * (y - θ)) = 0) :
    ∃ k : ℤ, (N : ℝ) * (y - θ) / Real.pi - 1 / 2 = (k : ℝ) := by
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hy
  refine ⟨k, ?_⟩
  have he : (N : ℝ) * (y - θ) = ((k : ℝ) + 1 / 2) * Real.pi := by
    rw [hk]
    ring
  have hd : (N : ℝ) * (y - θ) / Real.pi = (k : ℝ) + 1 / 2 := (div_eq_iff Real.pi_ne_zero).2 he
  linarith only [hd]

/-- An open real interval contains a finite set of integers with cardinality
at least its length minus one. The integers between the floor of the lower
endpoint and the ceiling of the upper endpoint give the required set. -/
theorem exists_integer_grid (x y : ℝ) :
    ∃ s : Finset ℤ, (∀ k ∈ s, x < (k : ℝ) ∧ (k : ℝ) < y) ∧ y - x - 1 ≤ (s.card : ℝ) := by
  let a : ℤ := ⌊x⌋ + 1
  let b : ℤ := ⌈y⌉
  let s : Finset ℤ := Finset.Ico a b
  refine ⟨s, ?_, ?_⟩
  · intro k hk
    have hk' := Finset.mem_Ico.mp hk
    constructor
    · apply Int.floor_lt.mp
      have hk1 : ⌊x⌋ + 1 ≤ k := hk'.1
      exact Int.add_one_le_iff.mp hk1
    · apply Int.lt_ceil.mp
      exact hk'.2
  · by_cases hab : a ≤ b
    · have hc := Int.card_Ico_of_le a b hab
      have hc' : (s.card : ℝ) = (b : ℝ) - (a : ℝ) := by exact_mod_cast hc
      have hfloor := Int.floor_le x
      have hceil := Int.le_ceil y
      dsimp only [a, b] at hc'
      push_cast at hc'
      linarith only [hc', hfloor, hceil]
    · have hab' : b < a := lt_of_not_ge hab
      have hb : b ≤ ⌊x⌋ := by
        dsimp only [a] at hab'
        exact Int.lt_add_one_iff.mp hab'
      have hb' : (b : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hb
      have hx := Int.floor_le x
      have hy := Int.le_ceil y
      have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
      linarith only [hb', hx, hy, hcard]

/-- A finite set of cosine-zero levels in a closed interval contains at most
one point per grid spacing, plus one endpoint. Each level has an integer
coordinate, and these distinct coordinates lie between the ceiling and floor
of the scaled interval endpoints. -/
theorem cos_phase_grid_card_le (lo hi θ : ℝ) {N : ℕ} (hN : 0 < N) (hlohi : lo ≤ hi) (s : Finset ℝ)
    (hs : ∀ y ∈ s, lo ≤ y ∧ y ≤ hi ∧ Real.cos ((N : ℝ) * (y - θ)) = 0) :
    (s.card : ℝ) ≤ (N : ℝ) * (hi - lo) / Real.pi + 1 := by
  classical
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let c : ℝ → ℝ := fun y => (N : ℝ) * (y - θ) / Real.pi - 1 / 2
  let l : ℝ := c lo
  let r : ℝ := c hi
  have hmono : ∀ x y : ℝ, x ≤ y → c x ≤ c y := by
    intro x y hxy
    dsimp only [c]
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hxy θ) hn.le
    have hd := div_le_div_of_nonneg_right hm Real.pi_pos.le
    linarith only [hd]
  have hex : ∀ y : ℝ, ∃ k : ℤ, y ∈ s → c y = (k : ℝ) := by
    intro y
    by_cases hy : y ∈ s
    · obtain ⟨k, hk⟩ := cos_phase_index θ y (hs y hy).2.2
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => (hy h).elim⟩
  let z : ℝ → ℤ := fun y => Classical.choose (hex y)
  have hz : ∀ y ∈ s, c y = (z y : ℝ) := by
    intro y hy
    exact Classical.choose_spec (hex y) hy
  have hzi : Set.InjOn z s := by
    intro x hx y hy he
    have hc : c x = c y := by rw [hz x hx, hz y hy, he]
    dsimp only [c] at hc
    have hd : (N : ℝ) * (x - θ) / Real.pi = (N : ℝ) * (y - θ) / Real.pi := by linarith only [hc]
    have hm := congrArg (fun q : ℝ => q * Real.pi) hd
    rw [div_mul_cancel₀ _ Real.pi_ne_zero, div_mul_cancel₀ _ Real.pi_ne_zero] at hm
    have hm' := mul_left_cancel₀ hn.ne' hm
    linarith only [hm']
  have hsub : s.image z ⊆ Finset.Icc ⌈l⌉ ⌊r⌋ := by
    intro k hk
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.ceil_le.mpr
      rw [← hz y hy]
      exact hmono lo y (hs y hy).1
    · apply Int.le_floor.mpr
      rw [← hz y hy]
      exact hmono y hi (hs y hy).2.1
  have hlr : l ≤ r := hmono lo hi hlohi
  have hceil : ⌈l⌉ ≤ ⌊r⌋ + 1 := by
    apply Int.ceil_le.mpr
    push_cast
    exact le_trans hlr (Int.lt_floor_add_one r).le
  have hc := Int.card_Icc_of_le ⌈l⌉ ⌊r⌋ hceil
  have hc' : ((Finset.Icc ⌈l⌉ ⌊r⌋).card : ℝ) = (⌊r⌋ : ℝ) + 1 - (⌈l⌉ : ℝ) := by exact_mod_cast hc
  have hcard : (s.card : ℝ) ≤ ((Finset.Icc ⌈l⌉ ⌊r⌋).card : ℝ) := by
    have hc0 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hzi] at hc0
    exact_mod_cast hc0
  have hr := Int.floor_le r
  have hl := Int.le_ceil l
  have hdiff : r - l = (N : ℝ) * (hi - lo) / Real.pi := by
    dsimp only [r, l, c]
    simp only [div_eq_mul_inv]
    ring
  linarith only [hcard, hc', hr, hl, hdiff]

/-- From nondecreasing-side cosine-zero levels, retain those farther than
`D` above the midpoint. At most `ND/π + 1` levels are discarded, by the
closed-interval grid count. -/
theorem exists_cos_grid_far_above (m θ D : ℝ) {N : ℕ} (hN : 0 < N) (hD : 0 ≤ D) (s : Finset ℝ)
    (hs : ∀ y ∈ s, m ≤ y ∧ Real.cos ((N : ℝ) * (y - θ)) = 0) :
    ∃ t : Finset ℝ,
      t ⊆ s ∧ (∀ y ∈ t, D < y - m) ∧ (s.card : ℝ) - ((N : ℝ) * D / Real.pi + 1) ≤ (t.card : ℝ) := by
  classical
  let p : ℝ → Prop := fun y => D < y - m
  let t := s.filter p
  let r := s.filter (fun y => ¬p y)
  have hr : ∀ y ∈ r, m ≤ y ∧ y ≤ m + D ∧ Real.cos ((N : ℝ) * (y - θ)) = 0 := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    have h := hs y hy'.1
    refine ⟨h.1, ?_, h.2⟩
    dsimp only [p] at hy'
    have hn : y - m ≤ D := le_of_not_gt hy'.2
    linarith only [hn]
  have hbound := cos_phase_grid_card_le m (m + D) θ hN (by linarith only [hD]) r hr
  have hbound' : (r.card : ℝ) ≤ (N : ℝ) * D / Real.pi + 1 := by
    have he : m + D - m = D := by ring
    rw [he] at hbound
    exact hbound
  have hc := Finset.card_filter_add_card_filter_not p (s := s)
  have hc' : (t.card : ℝ) + (r.card : ℝ) = (s.card : ℝ) := by exact_mod_cast hc
  refine ⟨t, Finset.filter_subset p s, ?_, ?_⟩
  · intro y hy
    exact (Finset.mem_filter.mp hy).2
  · linarith only [hc', hbound']

/-- For a positive exponent, an open interval contains a finite set of
cosine-zero phase levels whose cardinality is at least its length divided by
the grid spacing `π/N`, minus one. Translate and scale an integer grid;
the affine map is injective and each level gives an odd multiple of `π/2`. -/
theorem exists_cos_phase_grid (lo hi θ : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ s : Finset ℝ,
      (∀ y ∈ s, lo < y ∧ y < hi ∧ Real.cos ((N : ℝ) * (y - θ)) = 0) ∧
        (N : ℝ) * (hi - lo) / Real.pi - 1 ≤ (s.card : ℝ) := by
  classical
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let l : ℝ := (N : ℝ) * (lo - θ) / Real.pi - 1 / 2
  let r : ℝ := (N : ℝ) * (hi - θ) / Real.pi - 1 / 2
  let z : ℤ → ℝ := fun k => θ + (((k : ℝ) + 1 / 2) * Real.pi) / (N : ℝ)
  obtain ⟨S, hS, hcard⟩ := exists_integer_grid l r
  have hz : Function.Injective z := by
    intro i j hij
    have he :
      (((i : ℝ) + 1 / 2) * Real.pi) / (N : ℝ) = (((j : ℝ) + 1 / 2) * Real.pi) / (N : ℝ) := by
      dsimp only [z] at hij
      linarith only [hij]
    have he' := congrArg (fun x : ℝ => x * (N : ℝ)) he
    rw [div_mul_cancel₀ _ hn.ne', div_mul_cancel₀ _ hn.ne'] at he'
    have he'' := mul_right_cancel₀ Real.pi_ne_zero he'
    apply (Int.cast_injective : Function.Injective (fun k : ℤ => (k : ℝ)))
    linarith only [he'']
  refine ⟨S.image z, ?_, ?_⟩
  · intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    have hk' := hS k hk
    have hlo : (N : ℝ) * (lo - θ) / Real.pi < (k : ℝ) + 1 / 2 := by
      dsimp only [l] at hk'
      linarith only [hk'.1]
    have hhi : (k : ℝ) + 1 / 2 < (N : ℝ) * (hi - θ) / Real.pi := by
      dsimp only [r] at hk'
      linarith only [hk'.2]
    have hlo' := (div_lt_iff₀ Real.pi_pos).mp hlo
    have hhi' := (lt_div_iff₀ Real.pi_pos).mp hhi
    have hlo'' : lo - θ < (((k : ℝ) + 1 / 2) * Real.pi) / (N : ℝ) :=
      (lt_div_iff₀ hn).mpr (by nlinarith only [hlo'])
    have hhi'' : (((k : ℝ) + 1 / 2) * Real.pi) / (N : ℝ) < hi - θ :=
      (div_lt_iff₀ hn).mpr (by nlinarith only [hhi'])
    have he : (N : ℝ) * (z k - θ) = ((k : ℝ) + 1 / 2) * Real.pi := by
      dsimp only [z]
      have hcancel := div_mul_cancel₀ (((k : ℝ) + 1 / 2) * Real.pi) hn.ne'
      nlinarith only [hcancel]
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [z]
      linarith only [hlo'']
    · dsimp only [z]
      linarith only [hhi'']
    · rw [he]
      have heq : ((k : ℝ) + 1 / 2) * Real.pi = Real.pi / 2 + (k : ℝ) * Real.pi := by ring
      rw [heq, Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero]
  · rw [Finset.card_image_of_injective _ hz]
    dsimp only [l, r] at hcard
    have heq :
      ((N : ℝ) * (hi - θ) / Real.pi - 1 / 2) - ((N : ℝ) * (lo - θ) / Real.pi - 1 / 2) =
        (N : ℝ) * (hi - lo) / Real.pi := by
      simp only [div_eq_mul_inv]
      ring
    linarith only [hcard, heq]

/-- A cosine-zero grid reflected about any midpoint differs from the
original grid by a downward shift smaller than one grid spacing. Taking the
fractional part of `2N(m - θ)/π` determines a single shift that works for
every level. -/
theorem exists_cos_reflection_shift (m θ : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ δ : ℝ,
      0 ≤ δ ∧
        δ < Real.pi / (N : ℝ) ∧
        ∀ y : ℝ,
          Real.cos ((N : ℝ) * (y - θ)) = 0 → Real.cos ((N : ℝ) * ((2 * m - y - δ) - θ)) = 0 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let h : ℝ := Real.pi / (N : ℝ)
  let q : ℝ := 2 * (N : ℝ) * (m - θ) / Real.pi
  let k : ℤ := ⌊q⌋
  let δ : ℝ := (q - (k : ℝ)) * h
  have hh : 0 < h := div_pos Real.pi_pos hn
  have hfrac : 0 ≤ q - (k : ℝ) ∧ q - (k : ℝ) < 1 := by
    constructor
    · exact sub_nonneg.mpr (Int.floor_le q)
    · have hhf := Int.lt_floor_add_one q
      dsimp only [k]
      linarith only [hhf]
  have hqh : q * h = 2 * (m - θ) := by
    dsimp only [q, h]
    calc
      _ = (2 * (N : ℝ) * (m - θ) / Real.pi * Real.pi) / (N : ℝ) := by ring
      _ = (N : ℝ) * (2 * (m - θ)) / (N : ℝ) := by
        rw [div_mul_cancel₀ _ Real.pi_ne_zero]
        ring
      _ = _ := mul_div_cancel_left₀ (2 * (m - θ)) hn.ne'
  have hNh : (N : ℝ) * h = Real.pi := by
    dsimp only [h]
    exact mul_div_cancel₀ Real.pi hn.ne'
  have hdelta : (N : ℝ) * δ = 2 * (N : ℝ) * (m - θ) - (k : ℝ) * Real.pi := by
    dsimp only [δ]
    have hqN := congrArg (fun x : ℝ => (N : ℝ) * x) hqh
    have hkN := congrArg (fun x : ℝ => (k : ℝ) * x) hNh
    nlinarith only [hqN, hkN]
  refine ⟨δ, mul_nonneg hfrac.1 hh.le, ?_, ?_⟩
  · have hlt := mul_lt_mul_of_pos_right hfrac.2 hh
    simpa only [one_mul] using hlt
  · intro y hy
    have he : (N : ℝ) * ((2 * m - y - δ) - θ) = (k : ℝ) * Real.pi - (N : ℝ) * (y - θ) := by
      nlinarith only [hdelta]
    rw [he, Real.cos_int_mul_pi_sub, hy, mul_zero]

/-- The reflected cosine-zero grid also admits an upward shift smaller than
one grid spacing. Apply the downward-shift result after negating the
midpoint, center and phase level, using the evenness of cosine. -/
theorem exists_cos_reflection_shift_up (m θ : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ δ : ℝ,
      0 ≤ δ ∧
        δ < Real.pi / (N : ℝ) ∧
        ∀ y : ℝ,
          Real.cos ((N : ℝ) * (y - θ)) = 0 → Real.cos ((N : ℝ) * ((2 * m - y + δ) - θ)) = 0 := by
  obtain ⟨δ, hδ0, hδ, hcos⟩ := exists_cos_reflection_shift (-m) (-θ) hN
  refine ⟨δ, hδ0, hδ, ?_⟩
  intro y hy
  have hy' : Real.cos ((N : ℝ) * (-y - -θ)) = 0 := by
    have he : (N : ℝ) * (-y - -θ) = -((N : ℝ) * (y - θ)) := by ring
    rw [he, Real.cos_neg, hy]
  have hz := hcos (-y) hy'
  have he : (N : ℝ) * ((2 * -m - -y - δ) - -θ) = -((N : ℝ) * ((2 * m - y + δ) - θ)) := by ring
  rw [he, Real.cos_neg] at hz
  exact hz

/-- For any error allowance `E`, choose an upward reflection shift between
`E` and `E + 2π/N` that preserves cosine-zero levels. A ceiling multiple of
the grid spacing raises the basic shift above `E` without losing the grid. -/
theorem exists_cos_reflection_shift_above (m θ E : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ D : ℝ,
      E ≤ D ∧
        D < E + 2 * (Real.pi / (N : ℝ)) ∧
        ∀ y : ℝ,
          Real.cos ((N : ℝ) * (y - θ)) = 0 → Real.cos ((N : ℝ) * ((2 * m - y + D) - θ)) = 0 := by
  obtain ⟨δ, hδ0, hδ, hcos⟩ := exists_cos_reflection_shift_up m θ hN
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let h : ℝ := Real.pi / (N : ℝ)
  have hh : 0 < h := div_pos Real.pi_pos hn
  let k : ℤ := ⌈E / h⌉
  have hlo := Int.le_ceil (E / h)
  have hhi := Int.ceil_lt_add_one (E / h)
  have hlo' := mul_le_mul_of_nonneg_right hlo hh.le
  have hhi' := mul_lt_mul_of_pos_right hhi hh
  have hcancel := div_mul_cancel₀ E hh.ne'
  refine ⟨δ + (k : ℝ) * h, ?_, ?_, ?_⟩
  · dsimp only [k] at *
    dsimp only [h] at *
    nlinarith only [hlo', hcancel, hδ0]
  · dsimp only [k] at *
    dsimp only [h] at *
    nlinarith only [hhi', hcancel, hδ]
  · intro y hy
    have hmul : (N : ℝ) * h = Real.pi := by
      dsimp only [h]
      exact mul_div_cancel₀ Real.pi hn.ne'
    have he :
      (N : ℝ) * ((2 * m - y + (δ + (k : ℝ) * h)) - θ) =
        (N : ℝ) * ((2 * m - y + δ) - θ) + (k : ℝ) * Real.pi := by
      have hk := congrArg (fun x : ℝ => (k : ℝ) * x) hmul
      nlinarith only [hk]
    rw [he, Real.cos_add_int_mul_pi, hcos y hy, mul_zero]

/-- The corresponding downward shift can also absorb an arbitrary error
allowance while adding less than two grid spacings. Negating the phase
coordinates transfers the upward-shift result. -/
theorem exists_cos_reflection_shift_below (m θ E : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ D : ℝ,
      E ≤ D ∧
        D < E + 2 * (Real.pi / (N : ℝ)) ∧
        ∀ y : ℝ,
          Real.cos ((N : ℝ) * (y - θ)) = 0 → Real.cos ((N : ℝ) * ((2 * m - y - D) - θ)) = 0 := by
  obtain ⟨D, hDE, hD, hcos⟩ := exists_cos_reflection_shift_above (-m) (-θ) E hN
  refine ⟨D, hDE, hD, ?_⟩
  intro y hy
  have hy' : Real.cos ((N : ℝ) * (-y - -θ)) = 0 := by
    have he : (N : ℝ) * (-y - -θ) = -((N : ℝ) * (y - θ)) := by ring
    rw [he, Real.cos_neg, hy]
  have hz := hcos (-y) hy'
  have he : (N : ℝ) * ((2 * -m - -y + D) - -θ) = -((N : ℝ) * ((2 * m - y - D) - θ)) := by ring
  rw [he, Real.cos_neg] at hz
  exact hz

end PseudoPrime.PrimeTestBounds.MillerRabin
