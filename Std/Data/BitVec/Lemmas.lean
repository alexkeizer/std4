/-
Copyright (c) 2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Std.Data.BitVec.Basic

section FromMathlib

theorem List.ofFn_succ {n} (f : Fin (n + 1) → α) : List.ofFn f = f 0 :: List.ofFn fun i => f i.succ :=
  sorry

@[simp] theorem Nat.shiftLeft_zero (x : Nat) : x <<< 0 = x :=
  rfl

end FromMathlib

namespace Std.BitVec

/- TODO: these lemmas should probably go in Mathlib -/

#check List.ofFn

@[simp] theorem toNat_cast (x : BitVec w) (h : w = w') :
    (cast h x).toNat = x.toNat :=
  rfl

@[simp] theorem toNat_append (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat <<< n ||| y.toNat := by
  simp only [(· ++ ·), append]
  sorry

theorem getMsb_cons_zero (b : Bool) (x : BitVec w) :
    getMsb (cons b x) 0 = b := by
  sorry

theorem getLsb_cons_zero (b : Bool) (x : BitVec w) :
    getLsb (concat x b) 0 = b := by
  simp [getLsb, concat]
  cases b <;> simp


theorem toLEList_cons (b : Bool) (x : BitVec w) :
    toLEList (cons b x) = b :: x.toLEList := by
  simp [toLEList, List.ofFn_succ]
