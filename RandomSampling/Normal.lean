/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The Box-Muller step and the skew normal draw follow uPlot's demos/lib/rand.js,
Copyright (c) 2022 Leon Sorokin, released under the MIT license.
-/
import RandomSampling.Uniform

namespace RandomSampling

/-- Two standard normal draws `(u0, v)` from two uniform draws `a` then `b`, by the Box-Muller transform. -/
def boxMuller {γ : Type} [RandomGen γ] (g : γ) : (Float × Float) × γ :=
  let (a, g) := uniform g
  let (b, g) := uniform g
  let r := Float.sqrt (-2 * Float.log a)
  let θ := 2 * 3.141592653589793 * b
  ((r * Float.cos θ, r * Float.sin θ), g)

theorem boxMuller_eq {γ : Type} [RandomGen γ] (g : γ) : boxMuller g =
    let a := (uniform g).1
    let b := (uniform (uniform g).2).1
    let r := Float.sqrt (-2 * Float.log a)
    let θ := 2 * 3.141592653589793 * b
    ((r * Float.cos θ, r * Float.sin θ), (uniform (uniform g).2).2) := rfl

/-- A standard normal draw: the first of `boxMuller`'s pair. -/
def standardNormal {γ : Type} [RandomGen γ] (g : γ) : Float × γ :=
  let ((u0, _), g) := boxMuller g
  (u0, g)

theorem standardNormal_eq {γ : Type} [RandomGen γ] (g : γ) : standardNormal g =
    (Float.sqrt (-2 * Float.log (uniform g).1) * Float.cos (2 * 3.141592653589793 * (uniform (uniform g).2).1),
      (uniform (uniform g).2).2) := rfl

/-- A normal draw with mean `μ` and standard deviation `σ`. -/
def normal {γ : Type} [RandomGen γ] (μ σ : Float) (g : γ) : Float × γ :=
  let (u0, g) := standardNormal g
  (μ + σ * u0, g)

theorem normal_eq {γ : Type} [RandomGen γ] (μ σ : Float) (g : γ) : normal μ σ g =
    (μ + σ * (Float.sqrt (-2 * Float.log (uniform g).1) *
      Float.cos (2 * 3.141592653589793 * (uniform (uniform g).2).1)), (uniform (uniform g).2).2) := rfl

/-- A skew normal draw with location `ξ`, scale `ω` and shape `α`, by Azzalini's method over `boxMuller`'s
pair. Shape 0 is the normal draw. -/
def skewNormal {γ : Type} [RandomGen γ] (ξ ω α : Float) (g : γ) : Float × γ :=
  let ((u0, v), g) := boxMuller g
  if α == 0 then (ξ + ω * u0, g)
  else
    let δ := α / Float.sqrt (1 + α * α)
    let u1 := δ * u0 + Float.sqrt (1 - δ * δ) * v
    (ξ + ω * (if u0 ≥ 0 then u1 else -u1), g)

theorem skewNormal_eq {γ : Type} [RandomGen γ] (ξ ω α : Float) (g : γ) : skewNormal ξ ω α g =
    let a := (uniform g).1
    let b := (uniform (uniform g).2).1
    let r := Float.sqrt (-2 * Float.log a)
    let θ := 2 * 3.141592653589793 * b
    let u0 := r * Float.cos θ
    let v := r * Float.sin θ
    let δ := α / Float.sqrt (1 + α * α)
    let u1 := δ * u0 + Float.sqrt (1 - δ * δ) * v
    (if α == 0 then ξ + ω * u0 else ξ + ω * (if u0 ≥ 0 then u1 else -u1), (uniform (uniform g).2).2) := by
  simp only [skewNormal, boxMuller]
  split <;> rfl

theorem skewNormal_zero {γ : Type} [RandomGen γ] (ξ ω : Float) (g : γ) : skewNormal ξ ω 0 g = normal ξ ω g := by
  simp only [skewNormal, show ((0 : Float) == 0) = true from rfl, ite_true]
  rfl

theorem boxMuller_snd {γ : Type} [RandomGen γ] (g : γ) : (boxMuller g).2 = (uniform (uniform g).2).2 := rfl

theorem standardNormal_snd {γ : Type} [RandomGen γ] (g : γ) :
    (standardNormal g).2 = (uniform (uniform g).2).2 := rfl

theorem normal_snd {γ : Type} [RandomGen γ] (μ σ : Float) (g : γ) : (normal μ σ g).2 = (uniform (uniform g).2).2 := rfl

theorem skewNormal_snd {γ : Type} [RandomGen γ] (ξ ω α : Float) (g : γ) :
    (skewNormal ξ ω α g).2 = (uniform (uniform g).2).2 := by
  simp only [skewNormal]
  split <;> rfl

end RandomSampling
