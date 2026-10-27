/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ShortCongruencePairs
public import Mathlib.Data.Rat.Lemmas

/-! # Bounded rational residues and Heilbronn product sets -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Canonical cross-multiplication relation den(q)*u=num(q) modulo m.
This defines reduction without assuming the residue ring is a field. -/
def rationalResidue {m : ℕ} (q : ℚ) (u : ZMod m) : Prop :=
  (q.den : ZMod m) * u = (q.num : ZMod m)

/-- For nonzero integer denominator b that is a unit modulo m, an equation b*u=a
passes to the canonical numerator and denominator of a/b. Cancel the unit reduction factor. -/
theorem rationalResidue_divInt {m : ℕ} (a b : ℤ) (hb : b ≠ 0) {u : ZMod m}
    (hbu : IsUnit (b : ZMod m)) (hu : (b : ZMod m) * u = (a : ZMod m)) :
    rationalResidue (Rat.divInt a b) u := by
  obtain ⟨c, ha, hc⟩ := Rat.num_den_mk hb (rfl : Rat.divInt a b = Rat.divInt a b)
  have hcast : (b : ZMod m) = (c : ZMod m) * ((Rat.divInt a b).den : ZMod m) := by
    have he := congrArg (fun z : ℤ ↦ (z : ZMod m)) hc
    simpa only [Int.cast_mul, Int.cast_natCast] using he
  have hcu : IsUnit (c : ZMod m) := (IsUnit.mul_iff.mp (hcast ▸ hbu)).1
  apply hcu.mul_left_cancel
  change
    (c : ZMod m) * (((Rat.divInt a b).den : ZMod m) * u) =
      (c : ZMod m) * ((Rat.divInt a b).num : ZMod m)
  have hcasta : (a : ZMod m) = (c : ZMod m) * ((Rat.divInt a b).num : ZMod m) := by
    have he := congrArg (fun z : ℤ ↦ (z : ZMod m)) ha
    simpa only [Int.cast_mul] using he
  rw [← mul_assoc, ← hcast, hu, hcasta]

/-- Canonical rational residues multiply whenever both canonical denominators are units.
Use the raw product representation and cancel its canonical normalization factor. -/
theorem rationalResidue_mul {m : ℕ} {q r : ℚ} {u v : ZMod m} (hq : rationalResidue q u)
    (hr : rationalResidue r v) (hqd : IsUnit (q.den : ZMod m)) (hrd : IsUnit (r.den : ZMod m)) :
    rationalResidue (q * r) (u * v) := by
  have hb : (q.den : ℤ) * r.den ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr q.den_ne_zero) (Int.natCast_ne_zero.mpr r.den_ne_zero)
  have hunit : IsUnit (((q.den : ℤ) * r.den : ℤ) : ZMod m) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
    exact hqd.mul hrd
  have he : ((((q.den : ℤ) * r.den : ℤ) : ZMod m)) * (u * v) = ((q.num * r.num : ℤ) : ZMod m) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_mul]
    dsimp only [rationalResidue] at hq hr
    calc
      _ = ((q.den : ZMod m) * u) * ((r.den : ZMod m) * v) := by ring
      _ = _ := by rw [hq, hr]
  have hrep := rationalResidue_divInt (q.num * r.num) ((q.den : ℤ) * r.den) hb hunit he
  have hrat : q * r = Rat.divInt (q.num * r.num) ((q.den : ℤ) * r.den) := by
    rw [Rat.divInt_eq_div, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ←
      div_mul_div_comm, q.num_div_den, r.num_div_den]
  rw [hrat]
  exact hrep

/-- Natural products with all factors at most Q and Q^2<m are equal if equal modulo m.
Bound both products by Q^2 and use canonical natural residues. -/
theorem cross_product_eq_of_small_modulus {m Q : ℕ} {a b c d : ℕ} (ha : a ≤ Q) (hb : b ≤ Q)
    (hc : c ≤ Q) (hd : d ≤ Q) (hQ : Q ^ 2 < m) (he : (a : ZMod m) * d = (c : ZMod m) * b) :
    a * d = c * b := by
  have had : a * d < m := (Nat.mul_le_mul ha hd).trans_lt ((pow_two Q) ▸ hQ)
  have hcb : c * b < m := (Nat.mul_le_mul hc hb).trans_lt ((pow_two Q) ▸ hQ)
  rw [← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt had,
    Nat.mod_eq_of_lt hcb] at he
  exact he

/-- Positive rationals of numerator and denominator at most Q have at most one
representative at a fixed residue when Q^2<m. Cross-multiply and lift the small congruence. -/
theorem rationalResidue_injective_at_height {m Q : ℕ} {q r : ℚ} {u : ZMod m} (hq : 0 < q.num)
    (hr : 0 < r.num) (hqn : q.num.natAbs ≤ Q) (hqd : q.den ≤ Q) (hrn : r.num.natAbs ≤ Q)
    (hrd : r.den ≤ Q) (hQ : Q ^ 2 < m) (hqu : rationalResidue q u) (hru : rationalResidue r u) :
    q = r := by
  have hqz : (q.num.natAbs : ℤ) = q.num := by rw [Int.natCast_natAbs, abs_of_pos hq]
  have hrz : (r.num.natAbs : ℤ) = r.num := by rw [Int.natCast_natAbs, abs_of_pos hr]
  have hqncast : (q.num.natAbs : ZMod m) = (q.num : ZMod m) := by rw [← Int.cast_natCast, hqz]
  have hrncast : (r.num.natAbs : ZMod m) = (r.num : ZMod m) := by rw [← Int.cast_natCast, hrz]
  have he : (q.num.natAbs : ZMod m) * r.den = (r.num.natAbs : ZMod m) * q.den := by
    rw [hqncast, hrncast, ← hqu, ← hru]
    ring
  have hc := cross_product_eq_of_small_modulus hqn hqd hrn hrd hQ he
  apply Rat.eq_iff_mul_eq_mul.mpr
  have hi := congrArg (fun n : ℕ ↦ (n : ℤ)) hc
  simpa only [Nat.cast_mul, hqz, hrz] using hi

/-- A positive rational with a raw numerator and denominator in [1,Q], together
with a residue satisfying denominator*u=numerator modulo m.
Raw witnesses make height growth explicit. -/
def boundedRationalResidue (m Q : ℕ) (q : ℚ) (u : ZMod m) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ a ≤ Q ∧ 0 < b ∧ b ≤ Q ∧ q = (a : ℚ) / b ∧ (b : ZMod m) * u = (a : ZMod m)

/-- Bounded rational residues at heights Q,T multiply to one at height Q*T.
Multiply the raw witnesses and their cross-multiplication identities. -/
theorem boundedRationalResidue_mul {m Q T : ℕ} {q r : ℚ} {u v : ZMod m}
    (hq : boundedRationalResidue m Q q u) (hr : boundedRationalResidue m T r v) :
    boundedRationalResidue m (Q * T) (q * r) (u * v) := by
  obtain ⟨a, b, ha, haQ, hb, hbQ, hq, hu⟩ := hq
  obtain ⟨c, d, hc, hcT, hd, hdT, hr, hv⟩ := hr
  refine
    ⟨a * c, b * d, mul_pos ha hc, Nat.mul_le_mul haQ hcT, mul_pos hb hd, Nat.mul_le_mul hbQ hdT, ?_,
      ?_⟩
  · rw [hq, hr, Nat.cast_mul, Nat.cast_mul, div_mul_div_comm]
  · rw [Nat.cast_mul, Nat.cast_mul]
    calc
      _ = ((b : ZMod m) * u) * ((d : ZMod m) * v) := by ring
      _ = _ := by rw [hu, hv]

/-- The rational and residue one have a bounded representation at height one. -/
theorem boundedRationalResidue_one (m : ℕ) : boundedRationalResidue m 1 1 1 := by
  refine ⟨1, 1, by decide, le_rfl, by decide, le_rfl, ?_, ?_⟩
  · rw [Nat.cast_one, div_one]
  · rw [Nat.cast_one, one_mul]

/-- Products over a finite set of residues of height Q have height Q^card(S).
Induct over S and multiply the raw representations; includes the empty product. -/
theorem boundedRationalResidue_prod {ι : Type*} {m Q : ℕ} (S : Finset ι) (q : ι → ℚ)
    (u : ι → ZMod m) (h : ∀ i ∈ S, boundedRationalResidue m Q (q i) (u i)) :
    boundedRationalResidue m (Q ^ S.card) (∏ i ∈ S, q i) (∏ i ∈ S, u i) := by
  classical
    induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.card_empty, pow_zero, Finset.prod_empty] using boundedRationalResidue_one m
  | @insert i S hi
    ih =>
    rw [Finset.card_insert_of_notMem hi, Finset.prod_insert hi, Finset.prod_insert hi, pow_succ']
    exact
      boundedRationalResidue_mul (h i (Finset.mem_insert_self i S))
        (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

/-- For Q^2<m, positive bounded fractions at the same residue are equal rationals.
Lift the bounded cross-product congruence and use nonzero denominators. -/
theorem boundedRationalResidue_injective {m Q : ℕ} {q r : ℚ} {u : ZMod m}
    (hq : boundedRationalResidue m Q q u) (hr : boundedRationalResidue m Q r u) (hQ : Q ^ 2 < m) :
    q = r := by
  obtain ⟨a, b, ha, haQ, hb, hbQ, hq, hu⟩ := hq
  obtain ⟨c, d, hc, hcQ, hd, hdQ, hr, hv⟩ := hr
  have he : (a : ZMod m) * d = (c : ZMod m) * b := by
    rw [← hu, ← hv]
    ring
  have hn := cross_product_eq_of_small_modulus haQ hbQ hcQ hdQ hQ he
  rw [hq, hr]
  apply
    (div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb))
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))).mpr
  have hh := congrArg (fun n : ℕ ↦ (n : ℚ)) hn
  simpa only [Nat.cast_mul] using hh

end PseudoPrime.NumberTheory.Heilbronn
