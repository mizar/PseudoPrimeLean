/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGapBox
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPairCharacterData
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltFactors

/-! # Rejecting prime on the first compressed Gaussian cell -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real sum of the three Jacobi pair characters lies between minus one and three. -/
private theorem uniform_pair_re_range {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (k : ℕ) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    (a k).re + (b k).re + (c k).re ∈ Set.Icc (-1) 3 := by
  intro a b c
  refine ⟨?_, ?_⟩
  · simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  · linarith only [(Complex.re_le_norm _).trans (a.norm_le_one k),
      (Complex.re_le_norm _).trans (b.norm_le_one k),
      (Complex.re_le_norm _).trans (c.norm_le_one k)]

/-- A contradiction for the pair characters gives a rejecting prime for a uniform triple. -/
theorem uniform_witness_of_pair_false {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) {X : ℝ}
    (hcompare :
      ∀ {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] {a : DirichletCharacter ℂ p}
        {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r},
        (a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) →
          (b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even) →
          (c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) →
          2 ≤ p →
          2 ≤ q →
          2 ≤ r →
          Real.log p + Real.log q + Real.log r = 2 * Real.log n →
          (∀ k : ℕ, (a k).re + (b k).re + (c k).re ∈ Set.Icc (-1) 3) →
          (∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1 ∧ b l = 1 ∧ c l = 1) → False) :
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  classical
  by_contra h
  have hall : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
    intro l hl' hlX
    exact Classical.byContradiction (fun hf ↦ h ⟨l, hl', hlX, hf⟩)
  obtain ⟨p, q, r, hp, hq, hr, _, _, hnprod⟩ := uniformKorselt_ordered_factors hu
  have hpD : p ∣ n := ⟨q * r, hnprod.trans (Nat.mul_assoc _ _ _)⟩
  have hqD : q ∣ n := ⟨p * r, hnprod.trans (by ac_rfl)⟩
  have hrD : r ∣ n := ⟨p * q, hnprod.trans (by ac_rfl)⟩
  have hpO := Odd.of_dvd_nat ho hpD
  have hqO := Odd.of_dvd_nat ho hqD
  have hrO := Odd.of_dvd_nat ho hrD
  have hp2 : p ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hpO)
  have hq2 : q ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hqO)
  have hr2 : r ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hrO)
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm hq2)⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm hr2)⟩
  obtain ⟨hpq, hpr, hqr, ha, hb, hc, hsmall⟩ :=
    pair_data_of_uniform_pass hn ho hu hnprod hpO hqO hrO X hall
  exact
    hcompare ha hb hc hpq hpr hqr (pair_level_log_sum hnprod)
      (fun k ↦ uniform_pair_re_range hpO hqO hrO k) hsmall

/-- Under GRH, an odd uniform Korselt triple with log in [663, 1327 / 2]
has a prime rejecting base at most the squared K137 scale. -/
theorem uniform_first_gaussian_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 663 (1327 / 2)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ ((250074514713 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  refine uniform_witness_of_pair_false hn ho hu ?_
  intro p q r _ _ _ a b c ha hb hc hp hq hr hlev ht hsmall
  exact
    gaussian_first_cell_abel_false ha hb hc hp hq hr hGRH hL hlev ht
      (fun l hl hX ↦ (hsmall l hl hX).1) (fun l hl hX ↦ (hsmall l hl hX).2.1)
      (fun l hl hX ↦ (hsmall l hl hX).2.2)

/-- On the first compressed cell the rejecting prime lies below the target
Gaussian cutoff. The fixed K137 scale is admissible from log 663 onward. -/
theorem gaussian_first_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 663 (1327 / 2)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ gaussianWitnessCutoff (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  obtain ⟨l, hl, hb, hf⟩ := uniform_first_gaussian_witness hn ho hu hGRH hL
  exact ⟨l, hl, hb.trans (gaussianCutoff_k137_first hL.1), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
