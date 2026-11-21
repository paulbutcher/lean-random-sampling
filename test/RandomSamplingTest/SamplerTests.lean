/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSampling
import RandomSamplingTest.Harness

/-! What proofs do not cover: the draw order each release must keep, that compiled floats agree with the
model the uniform theorems are about, and the shape of each distribution. -/

namespace RandomSamplingTest.SamplerTests

open RandomSamplingTest RandomSampling

def seed : StdGen := mkStdGen 42

/-- Within `1e-12` relative: `log`, `sin` and `cos` may differ in the last place between platforms. -/
def near (a b : Float) : Bool := (a - b).abs ≤ 1e-12 * (1 + a.abs + b.abs)

def pinnedNear (name : String) (actual : Array Float) (bits : Array UInt64) : TestCase := .mk name do
  check (actual.size == bits.size) s!"{actual.size} draws, expected {bits.size}"
  for (a, b) in actual.zip bits do
    check (near a (Float.ofBits b)) s!"{a} ({a.toBits}), expected {Float.ofBits b} ({b})"

def pinned : List TestCase := [
  .mk "nats keeps its draw order" <|
    check ((nats seed 8 0 100).1 == #[77, 38, 44, 77, 80, 82, 56, 25]) s!"{(nats seed 8 0 100).1}",
  .mk "uniform keeps its draw order, bit for bit" <|
    let bits := (draws 4 uniform seed).1.map Float.toBits
    check (bits == #[4600886775084895856, 4604248663371748788, 4600132504748510770, 4603837602665147223])
      s!"{bits}",
  pinnedNear "standardNormal keeps its draw order" (draws 4 standardNormal seed).1
    #[13827127495208542686, 13830456549450984726, 13819682282571620587, 13827077980960576611],
  pinnedNear "normal keeps its draw order" (draws 4 (normal 3 2) seed).1
    #[4610609379246267938, 4607280325003825898, 4613045040062784483, 4610658893494234013],
  pinnedNear "skewNormal keeps its draw order, positive shape" (draws 4 (skewNormal 10 2 4) seed).1
    #[4622824205707289352, 4623182315505821455, 4622259829349309385, 4622214863506463376],
  pinnedNear "skewNormal keeps its draw order, negative shape" (draws 4 (skewNormal 10 2 (-4)) seed).1
    #[4621470799000020116, 4621021494547081682, 4621826768322329303, 4620873465768272795]
]

def twoPow53 : Float := 9007199254740992

/-- The theorems are about Lean's model of `Float`; these check the compiled float matches it. -/
def compiled : List TestCase := [
  .mk "unitFloat is n * 2^-53 at the ends and the binade edges" do
    for n in [1, 2, 3, 2 ^ 26 + 1, 2 ^ 52 - 1, 2 ^ 52, 2 ^ 52 + 1, 2 ^ 53 - 1] do
      let u := unitFloat n
      check (u.toBits == unitBits n) s!"n = {n}: bits {u.toBits}, expected {unitBits n}"
      check (u == n.toFloat / twoPow53) s!"n = {n}: {u}"
      check (0 < u && u < 1) s!"n = {n}: {u} outside (0, 1)"
  ,
  .mk "every uniform draw is a multiple of 2^-53 strictly inside (0, 1)" do
    for u in (draws 20000 uniform seed).1 do
      let n := u * twoPow53
      check (n.floor == n && 1 ≤ n && n ≤ twoPow53 - 1) s!"{u} ({u.toBits})"
]

def mean (xs : Array Float) : Float := xs.foldl (· + ·) 0 / xs.size.toFloat

/-- The `k`th central moment. -/
def moment (k : Nat) (xs : Array Float) : Float :=
  let m := mean xs
  mean (xs.map fun x => (x - m) ^ k.toFloat)

def within (name : String) (actual expected tol : Float) : Except String Unit :=
  check ((actual - expected).abs ≤ tol) s!"{name} {actual}, expected {expected} ± {tol}"

/-- 20000 draws each; every tolerance is at least four standard errors of the statistic. -/
def shape : List TestCase := [
  .mk "nats reach every value of the range, around its midpoint" do
    let xs := (nats seed 20000 0 100).1
    for v in [0:101] do check (xs.contains v) s!"{v} never drawn"
    within "mean" (mean (xs.map Nat.toFloat)) 50 1
  ,
  .mk "uniform has mean 1/2 and variance 1/12" do
    let xs := (draws 20000 uniform seed).1
    within "mean" (mean xs) 0.5 0.01
    within "variance" (moment 2 xs) (1 / 12) 0.005
  ,
  .mk "normal has its mean and standard deviation, and no skew" do
    let xs := (draws 20000 (normal 3 2) seed).1
    within "mean" (mean xs) 3 0.06
    within "standard deviation" (moment 2 xs).sqrt 2 0.05
    within "skewness" (moment 3 xs / (moment 2 xs) ^ 1.5) 0 0.07
  ,
  .mk "skewNormal has Azzalini's mean and its skew follows the shape" do
    for α in [4, -4] do
      let xs := (draws 20000 (skewNormal 10 2 α) seed).1
      let δ := α / (1 + α * α).sqrt
      within s!"α = {α}: mean" (mean xs) (10 + 2 * δ * (2 / 3.141592653589793).sqrt) 0.05
      let skew := moment 3 xs
      check (if α > 0 then skew > 0 else skew < 0) s!"α = {α}: third moment {skew}"
  ,
  .mk "skewNormal with shape 0 is normal" <|
    check ((draws 100 (skewNormal 3 2 0) seed).1 == (draws 100 (normal 3 2) seed).1) "draws differ"
]

def tests : List TestCase := pinned ++ compiled ++ shape

end RandomSamplingTest.SamplerTests
