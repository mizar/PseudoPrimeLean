/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.FiniteBitMasks
public import PseudoPrime.NumberTheory.PrimeResidueCoverage

/-! Sound bitmap coverage certificates with arbitrary nontrivial divisor masks.
Capped predicate bits are folded into residue positions. Divisor completeness and
primality are unnecessary: checked divisors only exclude known nonunits. -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Bits for all natural indices strictly below q. -/
def fullMask (q : Nat) : Nat :=
  (1 <<< q) - 1

/-- Union the low q bits of any chosen number of consecutive q-bit chunks. -/
def foldChunks (q : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, bits => (bits &&& fullMask q) ||| foldChunks q n (bits >>> q)

/-- Double a finite set of multiples by adjoining one shifted copy. -/
def spreadMultiples : Nat → Nat → Nat → Nat
  | 0, _, bits => bits
  | k + 1, step, bits => spreadMultiples k (2 * step) (bits ||| (bits <<< step))

/-- Each pair is a submitted divisor and an arbitrary doubling level. -/
def badMaskDoubling : List (Nat × Nat) → Nat
  | [] => 0
  | (d, k) :: ds => spreadMultiples k d 1 ||| badMaskDoubling ds

/-- Check only that each submitted divisor is nontrivial and divides q. -/
def divisorLevelCheck (q : Nat) (ds : List (Nat × Nat)) : Bool :=
  ds.all fun entry => Nat.ble 2 entry.1 && (q % entry.1 == 0)

/-- Every residue is either covered by a capped bitmap bit or is a known nonunit. -/
def bitmapCoverageCheck (bits q cap : Nat) (ds : List (Nat × Nat)) : Bool :=
  divisorLevelCheck q ds &&
    (((foldChunks q (cap / q + 1) (bits &&& fullMask (cap + 1)) ||| badMaskDoubling ds) &&&
        fullMask q) ==
      fullMask q)

/-- Any chosen fuel is sound. More fuel is only needed for completeness. -/
theorem foldChunks_testBit_exists {q n bits a : Nat} (h : (foldChunks q n bits).testBit a = true) :
    ∃ j, j < n ∧ bits.testBit (j * q + a) = true := by
  induction n generalizing bits with
  | zero => simp only [foldChunks, Nat.zero_testBit, Bool.false_eq_true] at h
  | succ n ih =>
    rw [foldChunks, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.testBit_and, Bool.and_eq_true] at h
      exact ⟨0, Nat.zero_lt_succ n, by simpa only [Nat.zero_mul, Nat.zero_add] using h.1⟩
    · obtain ⟨j, hj, hb⟩ := ih h
      refine ⟨j + 1, Nat.succ_lt_succ hj, ?_⟩
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.testBit_shiftRight] using hb

/-- Truncation, rather than a fuel bound, supplies the witness cap. -/
theorem truncated_testBit {bits cap p : Nat} (h : (bits &&& fullMask (cap + 1)).testBit p = true) :
    bits.testBit p = true ∧ p ≤ cap := by
  have hf : fullMask (cap + 1) = 2 ^ (cap + 1) - 1 := by
    simp only [fullMask, Nat.shiftLeft_eq, Nat.one_mul]
  rw [Nat.testBit_and, hf, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, Nat.le_of_lt_succ h.2⟩

/-- The bitmap-to-predicate bridge is independent of primality theory. -/
theorem foldChunks_witness {P : Nat → Prop} {q n bits cap a : Nat} (ha : a < q)
    (hbits : ∀ p, bits.testBit p = true → P p)
    (h : (foldChunks q n (bits &&& fullMask (cap + 1))).testBit a = true) :
    ∃ p, P p ∧ p % q = a ∧ p ≤ cap := by
  obtain ⟨j, _, hb⟩ := foldChunks_testBit_exists h
  obtain ⟨hp, hc⟩ := truncated_testBit hb
  refine ⟨j * q + a, hbits _ hp, ?_, hc⟩
  rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt ha]

/-- Coverage can use any known-nonunit mask; exact unit-mask equality is unnecessary. -/
theorem coverage_witness {P : Nat → Prop} {q n bits cap bad a : Nat} (ha : a < q)
    (hbits : ∀ p, bits.testBit p = true → P p) (hbad : bad.testBit a = false)
    (hc :
      ((foldChunks q n (bits &&& fullMask (cap + 1)) ||| bad) &&& fullMask q == fullMask q) =
        true) :
    ∃ p, P p ∧ p % q = a ∧ p ≤ cap := by
  have he : (foldChunks q n (bits &&& fullMask (cap + 1)) ||| bad) &&& fullMask q = fullMask q := by
    exact beq_iff_eq.mp hc
  have hf : (fullMask q).testBit a = true := by
    simp only [fullMask, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one, ha,
      decide_true]
  have hb := congrArg (fun x : Nat => x.testBit a) he
  simp only [Nat.testBit_and, Nat.testBit_or, hf, hbad, Bool.or_false, Bool.and_true] at hb
  exact foldChunks_witness ha hbits hb

/-- OR with a shift by a multiple of d preserves the multiples-only invariant. -/
theorem or_shift_testBit_dvd {d step bits : Nat} (hs : d ∣ step)
    (hm : ∀ a, bits.testBit a = true → d ∣ a) {a : Nat}
    (h : (bits ||| (bits <<< step)).testBit a = true) : d ∣ a := by
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with h | h
  · exact hm a h
  · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
    have hd := Nat.dvd_add hs (hm _ h.2)
    simpa only [Nat.add_sub_of_le h.1] using hd

/-- The doubling loop needs no assertion about how many multiples it covers. -/
theorem spreadMultiples_testBit_dvd {d k step bits a : Nat} (hs : d ∣ step)
    (hm : ∀ a, bits.testBit a = true → d ∣ a) (h : (spreadMultiples k step bits).testBit a = true) :
    d ∣ a := by
  induction k generalizing step bits with
  | zero => exact hm a h
  | succ k ih =>
    exact ih (Nat.dvd_mul_left_of_dvd hs 2) (fun _ hb => or_shift_testBit_dvd hs hm hb) h

/-- A mask starting at the bit for zero only marks multiples of its stride. -/
theorem spreadMultiples_one_testBit_dvd {d k a : Nat}
    (h : (spreadMultiples k d 1).testBit a = true) : d ∣ a := by
  apply spreadMultiples_testBit_dvd (Nat.dvd_refl d) ?_ h
  intro b hb
  have he : b = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hb
  subst b
  exact Nat.dvd_zero d

/-- Unioning submitted divisor masks still supplies an explicit submitted divisor. -/
theorem badMaskDoubling_testBit_exists {ds : List (Nat × Nat)} {a : Nat}
    (h : (badMaskDoubling ds).testBit a = true) : ∃ e, e ∈ ds ∧ e.1 ∣ a := by
  induction ds with
  | nil => simp only [badMaskDoubling, Nat.zero_testBit, Bool.false_eq_true] at h
  | cons e ds ih =>
    rcases e with ⟨d, k⟩
    rw [badMaskDoubling, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨(d, k), List.mem_cons_self, spreadMultiples_one_testBit_dvd h⟩
    · obtain ⟨e, he, hd⟩ := ih h
      exact ⟨e, List.mem_cons_of_mem _ he, hd⟩

/-- Submitted entries need only be nontrivial divisors, not certified prime factors. -/
theorem divisorLevelCheck_spec {q : Nat} {ds : List (Nat × Nat)}
    (h : divisorLevelCheck q ds = true) : ∀ e, e ∈ ds → 1 < e.1 ∧ e.1 ∣ q := by
  intro e he
  have hv := List.all_eq_true.mp h e he
  rw [Bool.and_eq_true] at hv
  exact ⟨Nat.le_of_ble_eq_true hv.1, Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hv.2)⟩

/-- Every unit avoids every checked divisor mask, with arbitrary doubling levels. -/
theorem badMaskDoubling_coprime {q a : Nat} {ds : List (Nat × Nat)}
    (hd : divisorLevelCheck q ds = true) (ha : Nat.Coprime a q) :
    (badMaskDoubling ds).testBit a = false := by
  cases hb : (badMaskDoubling ds).testBit a with
  | false => rfl
  | true =>
    obtain ⟨e, he, hdvd⟩ := badMaskDoubling_testBit_exists hb
    obtain ⟨hgt, hq⟩ := divisorLevelCheck_spec hd e he
    exact False.elim (Nat.not_coprime_of_dvd_of_dvd hgt hdvd hq ha)

/-- Full arithmetic checker soundness, with primality represented by an abstract predicate. -/
theorem bitmapCoverageCheck_witness {P : Nat → Prop} {bits q cap a : Nat} {ds : List (Nat × Nat)}
    (ha : a < q) (hcop : Nat.Coprime a q) (hbits : ∀ p, bits.testBit p = true → P p)
    (hc : bitmapCoverageCheck bits q cap ds = true) : ∃ p, P p ∧ p % q = a ∧ p ≤ cap := by
  rw [bitmapCoverageCheck, Bool.and_eq_true] at hc
  exact coverage_witness ha hbits (badMaskDoubling_coprime hc.1 hcop) hc.2

/-- A sound prime bitmap and a successful coverage check give an integer-bounded
prime representative for every unit modulo a nonzero modulus. Extract the folded
bit witness and identify its residue using `ZMod.val`. The cap remains available
for divisor transfers independently of a later real-number bound. -/
theorem bitmapCoverageCheck_bounded {bits q cap : ℕ} [NeZero q] {ds : List (ℕ × ℕ)}
    (hbits : ∀ p, bits.testBit p = true → p.Prime) (hc : bitmapCoverageCheck bits q cap ds = true) :
    BoundedPrimeResidueCoverage q cap := by
  intro a
  obtain ⟨p, hp, hm, hcap⟩ :=
    bitmapCoverageCheck_witness (ZMod.val_lt (a : ZMod q)) (ZMod.val_coe_unit_coprime a) hbits hc
  exact ⟨p, hp, ZMod.val_injective q ((ZMod.val_natCast q p).trans hm), hcap⟩

end PseudoPrime.NumberTheory
