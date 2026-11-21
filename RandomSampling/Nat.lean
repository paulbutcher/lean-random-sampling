/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace RandomSampling

/-- A natural number in `lo..hi`, drawn by Lean's `randNat`; `nat_mem` bounds it when `lo ≤ hi`. -/
def nat {γ : Type} [RandomGen γ] (g : γ) (lo hi : Nat) : Nat × γ :=
  randNat g lo hi

theorem nat_eq {γ : Type} [RandomGen γ] (g : γ) (lo hi : Nat) : nat g lo hi = randNat g lo hi := rfl

theorem nat_mem {γ : Type} [RandomGen γ] (g : γ) (lo hi : Nat) (h : lo ≤ hi) :
    lo ≤ (nat g lo hi).1 ∧ (nat g lo hi).1 ≤ hi := by
  have bound (v : Nat) : lo + v % (hi - lo + 1) ≤ hi := by
    have := Nat.mod_lt v (show 0 < hi - lo + 1 by omega); omega
  unfold nat randNat
  simp only [show ¬ lo > hi by omega, ite_false]
  exact ⟨Nat.le_add_right _ _, bound _⟩

end RandomSampling
