/-
Copyright (c) 2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Std.Data.BitVec.Basic
import Std.Data.Fin.Lemmas

namespace Std.BitVec

theorem toNat_inj {x y : BitVec w} : x.toNat = y.toNat ↔ x = y :=
  ⟨(match x, y, · with | ⟨_, _⟩,⟨_, _⟩, rfl => rfl), (· ▸ rfl)⟩

theorem toNat_add {x y : BitVec w} :
    (x + y).toNat = (x.toNat + y.toNat) % 2^w :=
  Fin.val_add ..

#check BitVec.ofNat_toNat

-- lemma toNat_ofNat {m} (h : m < 2^w) : (BitVec.ofNat w m).toNat = m := Fin.val_cast_of_lt h

theorem toNat_append {x : BitVec n} {y : BitVec m} :
    (x ++ y).toNat = x.toNat <<< n ||| y.toNat := by
  simp only [(· ++ ·), append, Nat.shiftLeft_eq]
  simp?

theorem msb_cons : (cons msb lsbs).msb = msb := by
  simp [BitVec.msb, cons, getMsb, getLsb, Nat.zero_lt_succ]

/-- There is only one `empty` bitvector, namely, `nil` -/
theorem zero_length_eq_nil :
    ∀ (xs : BitVec 0), xs = nil := by
  intro xs
  apply BitVec.toNat_inj.mp
  conv => { rhs; simp [BitVec.toNat, nil, BitVec.zero, BitVec.ofNat] }
  have : xs.toNat < 2 ^ 0 := xs.toFin.isLt
  cases h : xs.toNat
  · rfl
  · subst h
  simp only [Nat.pow_zero] at this
  have : xs.toNat = nil.toNat := this
  simp only [nil, BitVec.zero, toNat_inj] at this
  simp only [this]

theorem concatMsb_msb_dropMsb {n} (xs : BitVec (n+1)) :
    concatMsb xs.msb xs.dropMsb = xs := by
  simp [concatMsb, BitVec.msb, getMsb, dropMsb, getLsb]
  sorry

/-- A custom recursion principle for bitvectors in terms of `nil` and `consLsb` -/
@[elab_as_elim]
def consRec {motive : {n : Nat} → BitVec n → Sort*}
    (nil : motive nil)
    (consLsb : {n : Nat} → (x : Bool) → (xs : BitVec n) → motive xs → motive (consLsb x xs))
    {n : Nat} (xs : BitVec n) : motive xs :=
  sorry
