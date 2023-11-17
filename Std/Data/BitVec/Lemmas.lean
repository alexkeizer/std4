/-
Copyright (c) 2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Std.Data.BitVec.Basic
import Std.Data.Nat.Lemmas

theorem Nat.mod_two_pow (x n : Nat) :
    x % (2^n) = x &&& 2^n - 1 := by
  sorry

namespace Std.BitVec

variable {w : Nat}

theorem cons_msb_truncate : ∀ (xs : BitVec (w+1)), cons xs.msb (xs.truncate w) = xs
  | ⟨⟨xs, h⟩⟩ => by
      simp [
        cons, BitVec.msb, getMsb, getLsb, truncate, zeroExtend, (· ++ ·), BitVec.append, cast,
        Fin.cast, BitVec.ofNat, Fin.ofNat', -- BitVec.toNat,
        Nat.zero_lt_succ, Nat.succ_sub_one, Nat.mod_two_pow
      ]
