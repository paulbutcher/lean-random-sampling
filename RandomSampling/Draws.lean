/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSampling.Nat

namespace RandomSampling

/-- `n` draws of `sample`, each from the generator the one before returned. -/
def draws {γ α : Type} (n : Nat) (sample : γ → α × γ) (g : γ) : Array α × γ :=
  go n #[] g
where
  go : Nat → Array α → γ → Array α × γ
    | 0, acc, g => (acc, g)
    | k + 1, acc, g =>
      let (x, g) := sample g
      go k (acc.push x) g

private theorem go_eq {γ α : Type} (sample : γ → α × γ) (n : Nat) (acc : Array α) (g : γ) :
    draws.go sample n acc g = (acc ++ (draws n sample g).1, (draws n sample g).2) := by
  induction n generalizing acc g with
  | zero => simp [draws, draws.go]
  | succ k ih =>
    simp only [draws, draws.go] at ih ⊢
    rw [ih (acc.push _), ih (#[].push _)]
    simp

theorem draws_zero {γ α : Type} (sample : γ → α × γ) (g : γ) : draws 0 sample g = (#[], g) := rfl

/-- `n + 1` draws are one draw followed by `n` more from the generator it returns. -/
theorem draws_succ {γ α : Type} (n : Nat) (sample : γ → α × γ) (g : γ) :
    draws (n + 1) sample g =
      let (x, g) := sample g
      let (xs, g) := draws n sample g
      (#[x] ++ xs, g) := by
  show draws.go sample (n + 1) #[] g = _
  simp only [draws.go, go_eq]
  rfl

theorem draws_size {γ α : Type} (n : Nat) (sample : γ → α × γ) (g : γ) : (draws n sample g).1.size = n := by
  induction n generalizing g with
  | zero => rfl
  | succ k ih => rw [draws_succ]; simp [ih]; omega

/-- Every entry satisfies `p` when every draw of `sample` does. -/
theorem draws_forall {γ α : Type} (p : α → Prop) (n : Nat) (sample : γ → α × γ)
    (h : ∀ g, p (sample g).1) (g : γ) : ∀ x ∈ (draws n sample g).1, p x := by
  induction n generalizing g with
  | zero => simp [draws_zero]
  | succ k ih =>
    rw [draws_succ]
    intro x hx
    simp only [Array.mem_append, Array.mem_singleton] at hx
    rcases hx with rfl | hx
    · exact h g
    · exact ih _ x hx

/-- `n` natural numbers in `lo..hi`. -/
def nats {γ : Type} [RandomGen γ] (g : γ) (n lo hi : Nat) : Array Nat × γ :=
  draws n (nat · lo hi) g

theorem nats_eq {γ : Type} [RandomGen γ] (g : γ) (n lo hi : Nat) : nats g n lo hi = draws n (nat · lo hi) g := rfl

theorem nats_size {γ : Type} [RandomGen γ] (g : γ) (n lo hi : Nat) : (nats g n lo hi).1.size = n :=
  draws_size _ _ _

theorem nats_mem {γ : Type} [RandomGen γ] (g : γ) (n lo hi : Nat) (h : lo ≤ hi) :
    ∀ x ∈ (nats g n lo hi).1, lo ≤ x ∧ x ≤ hi :=
  draws_forall _ _ _ (fun g => nat_mem g lo hi h) g

end RandomSampling
