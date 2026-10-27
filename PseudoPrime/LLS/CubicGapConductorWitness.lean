/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExcludedCharacterDefect
public import PseudoPrime.LLS.CubicGapRationalBounds
public import PseudoPrime.LLS.ReciprocalGapAmbientArithmetic
public import PseudoPrime.LLS.SelectedReciprocalConductorBounds

/-! # Cubic-gap conductor bounds with arbitrary prime exclusions -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- For nonzero m and x ≥ 1, prime triviality outside m bounds the unnormalized
cubic defect by (2/3)sum(log p)+12sqrt x. Verify the cubic weights and identify
the exact finite defect. The character level is independent of m; no RH is needed. -/
theorem sqrt_mul_cubic_defect_le {f m : ℕ} (χ : DirichletCharacter ℂ f) (hm : m ≠ 0) {x : ℝ}
    (hx : 1 ≤ x) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬p ∣ m → χ p = 1) :
    Real.sqrt x *
        ((reciprocalGapCharacterSum 3 (1 : DirichletCharacter ℂ 1) x).re -
          (reciprocalGapCharacterSum 3 χ x).re) ≤
      (2 / 3 : ℝ) * (∑ p ∈ m.primeFactors, Real.log p) + 12 * Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  let w := fun n : ℕ ↦ (1 - ((n : ℝ) / x) ^ 3) / 3
  have hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, 0 ≤ w n ∧ w n ≤ 1 / 3 := by
    intro n hn
    have hn0 : 0 ≤ (n : ℝ) / x := div_nonneg (Nat.cast_nonneg n) hx0.le
    have hnle : (n : ℝ) ≤ x :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx0.le)
    have hr : (n : ℝ) / x ≤ 1 := (div_le_one hx0).mpr hnle
    have hp : ((n : ℝ) / x) ^ 3 ≤ 1 := pow_le_one₀ hn0 hr
    dsimp only [w]
    constructor <;> nlinarith only [hp, pow_nonneg hn0 3]
  have hb := weighted_character_defect_le_excluded χ hm hx w hw hsmall
  have he :
    Real.sqrt x *
        ((reciprocalGapCharacterSum 3 (1 : DirichletCharacter ℂ 1) x).re -
          (reciprocalGapCharacterSum 3 χ x).re) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w n := by
    rw [reciprocalGap_principal_re_eq_sum, reciprocalGapCharacterSum_re_eq_weighted, ←
      Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [reciprocalGapPrincipalWeight, Real.rpow_ofNat]
    dsimp only [w]
    field_simp [hs]
  rw [he]
  exact hb

/-- Under primitive nonprincipal GRH, strict separation of the cubic principal,
character and excluded-support budgets yields a prime outside m where chi is not one.
Assume the contrary and combine the three proved estimates. This generic criterion
is independent of the closed form chosen for the radius. -/
theorem exists_prime_outside_of_cubic_separation {f m : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hf : 2 ≤ f) (hm : m ≠ 0) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) {x : ℝ} (hx : 1 < x)
    (hgap :
      ((5 / 13 : ℝ) * Real.log f + 257 / 130) * Real.sqrt x + (2 / 5 : ℝ) * Real.log f +
          122917 / 15000 +
          (2 / 3 : ℝ) * (∑ p ∈ m.primeFactors, Real.log p) +
          12 * Real.sqrt x <
        x / 4 - 3 * Real.sqrt x) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬p ∣ m → χ p = 1 := by
    intro p hp hpx hpm
    by_contra hv
    exact hn ⟨p, hp, hpx, hpm, hv⟩
  have hd := sqrt_mul_cubic_defect_le χ hm hx.le ht
  have hu :=
    sqrt_mul_reciprocalGapCharacterSum_three_re_le hf hGRH hp hne (fun h ↦ hne (inv_eq_one.mp h))
      hx.le
  have hl :=
    mul_le_mul_of_nonneg_left (reciprocalGap_principal_three_ge hGRH.riemann hx)
      (Real.sqrt_nonneg x)
  nlinarith only [hd, hu, hl, Real.sq_sqrt (zero_lt_one.trans hx).le, hgap]

/-- The cubic conductor radius A+sqrt(A²+B), where A=(10/13)G+34 and
B=(8/5)G+33+(8/3)sum over distinct excluded primes of log p.
The witness bound is its square. Later applications require G ≥ log f and m ≠ 0. -/
noncomputable def cubicConductorRadius (G : ℝ) (m : ℕ) : ℝ :=
  ((10 / 13 : ℝ) * G + 34) +
    Real.sqrt
      ((((10 / 13 : ℝ) * G + 34) ^ 2) + (8 / 5 : ℝ) * G + 33 +
        (8 / 3 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p)

/-- For a nonnegative conductor envelope, the cubic radius is at least 34 and
solves the exact quadratic relation. Nonnegative excluded-prime logarithms
ensure the radicand is nonnegative. These facts certify strict separation. -/
theorem cubicConductorRadius_data {G : ℝ} (hG : 0 ≤ G) (m : ℕ) :
    34 ≤ cubicConductorRadius G m ∧
      (cubicConductorRadius G m) ^ 2 =
        2 * ((10 / 13 : ℝ) * G + 34) * cubicConductorRadius G m + (8 / 5 : ℝ) * G + 33 +
          (8 / 3 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p := by
  have he : 0 ≤ ∑ p ∈ m.primeFactors, Real.log (p : ℝ) :=
    Finset.sum_nonneg fun p hp ↦
      Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have hr :
    0 ≤
      (((10 / 13 : ℝ) * G + 34) ^ 2) + (8 / 5 : ℝ) * G + 33 +
        (8 / 3 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p := by
    nlinarith only [sq_nonneg ((10 / 13 : ℝ) * G + 34), hG, he]
  have hs := Real.sq_sqrt hr
  unfold cubicConductorRadius
  constructor
  · linarith only [hG,
      Real.sqrt_nonneg
        ((((10 / 13 : ℝ) * G + 34) ^ 2) + (8 / 5 : ℝ) * G + 33 +
          (8 / 3 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p)]
  · nlinarith only [hs]

/-- Primitive nonprincipal GRH and a conductor envelope G give an excluded-prime
witness below the square of the cubic radius. Its quadratic identity supplies
strict separation of the three budgets. This is the explicit R3 extraction. -/
theorem exists_prime_outside_le_cubicConductorRadius_sq {f m : ℕ} [NeZero f]
    (χ : DirichletCharacter ℂ f) (hf : 2 ≤ f) (hm : m ≠ 0)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) {G : ℝ} (hlog : Real.log f ≤ G) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (cubicConductorRadius G m) ^ 2 ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  have hf0 : 0 ≤ Real.log (f : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hf.trans' (by decide : 1 ≤ 2))
  have hd := cubicConductorRadius_data (hf0.trans hlog) m
  have hr : 0 ≤ cubicConductorRadius G m := (by norm_num only : (0 : ℝ) ≤ 34).trans hd.1
  have hx : 1 < (cubicConductorRadius G m) ^ 2 := by nlinarith only [hd.1]
  have hs := Real.sqrt_sq hr
  have hmul := mul_le_mul_of_nonneg_right hlog hr
  apply exists_prime_outside_of_cubic_separation χ hf hm hGRH hp hne hx
  rw [hs]
  nlinarith only [hd.1, hd.2, hlog, hmul]

/-- For G at least 16, the cubic squared radius improves the selected reciprocal
envelope for every excluded integer. Compare the two nonnegative radii and their
radicands, retaining the smaller coefficient of the exclusion cost. -/
theorem cubicConductorRadius_sq_le_selected {G : ℝ} (hG : 16 ≤ G) (m : ℕ) :
    (cubicConductorRadius G m) ^ 2 ≤ selectedReciprocalWitnessBound G m := by
  have hl := Real.log_nonneg (show 1 ≤ G by linarith only [hG])
  have he : 0 ≤ ∑ p ∈ m.primeFactors, Real.log (p : ℝ) :=
    Finset.sum_nonneg fun p hp ↦
      Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have ha : (10 / 13 : ℝ) * G + 34 ≤ selectedReciprocalRadius G := by
    dsimp only [selectedReciprocalRadius]
    linarith only [hG, hl]
  have hr :
    (((10 / 13 : ℝ) * G + 34) ^ 2) + (8 / 5 : ℝ) * G + 33 +
        (8 / 3 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p ≤
      (selectedReciprocalRadius G) ^ 2 + (14 / 5 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p := by
    dsimp only [selectedReciprocalRadius]
    nlinarith only [hG, hl, he, sq_nonneg (Real.log G)]
  have hb := add_le_add ha (Real.sqrt_le_sqrt hr)
  have hn := (cubicConductorRadius_data (by linarith only [hG]) m).1
  change
    (cubicConductorRadius G m) ^ 2 ≤
      (selectedReciprocalRadius G +
          Real.sqrt
            ((selectedReciprocalRadius G) ^ 2 + (14 / 5 : ℝ) * ∑ p ∈ m.primeFactors, Real.log p)) ^
        2
  change cubicConductorRadius G m ≤ _ at hb
  nlinarith only [hb, hn]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character has a unit-prime non-one witness below
the cubic radius for any envelope of its conductor logarithm. Apply the primitive
extraction with excluded level q and transfer character values on units. -/
theorem exists_prime_ne_one_le_cubic_conductor_radius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ}
    (hlog : Real.log χ.conductor ≤ G) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (PaperStatements.cubicConductorRadius G q) ^ 2 ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  have hn := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_outside_le_cubicConductorRadius_sq χ.primitiveCharacter
      (le_trans (by decide : 2 ≤ 3) hc) (NeZero.ne q) hGRH χ.primitiveCharacter_isPrimitive hn hlog
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- A nonprincipal character trivial on H gives a unit prime outside H under GRH,
with the cubic conductor radius. Transfer the non-one value to nonmembership.
No lower threshold on the conductor envelope is required. -/
theorem exists_prime_outside_le_cubic_conductor_radius {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ}
    (hlog : Real.log χ.conductor ≤ G) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ (PaperStatements.cubicConductorRadius G q) ^ 2 ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_cubic_conductor_radius χ hχ hGRH hlog
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

end PseudoPrime.LLS
