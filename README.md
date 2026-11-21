# lean-random-sampling

Seeded, reproducible pseudo-random draws for Lean 4: bounded naturals, uniform floats, and normal and skew normal floats. Every sampler takes a generator and returns its draw with the next generator, so a seed gives the same draws every time. Samplers are written against core's `RandomGen`, so `StdGen` is one generator and any other instance works unchanged. No dependencies beyond Lean core.

| Module | Holds |
| --- | --- |
| `RandomSampling.Nat` | A natural number in `lo..hi`. |
| `RandomSampling.Draws` | `n` draws of any sampler as an array, and `n` naturals in `lo..hi`. |
| `RandomSampling.Uniform` | A float strictly inside (0, 1), at a resolution of `2^-53`. |
| `RandomSampling.Normal` | Standard normal, normal and skew normal floats, by the Box-Muller transform over two uniform draws. |

```lean
import RandomSampling

open RandomSampling

example : Array Nat := (nats (mkStdGen 42) 8 0 100).1

example : Float × StdGen := uniform (mkStdGen 42)

example : Array Float := (draws 1000 (normal 3 2) (mkStdGen 42)).1

example (g : StdGen) : Float × Float :=
  let (x, g) := skewNormal 10 2 4 g
  let (y, _) := skewNormal 10 2 4 g
  (x, y)
```

The skew normal draw uses Azzalini's method, after uPlot's `demos/lib/rand.js`. With shape 0 it is the normal draw.

For a given generator and sampler, the sequence of values is part of the API. A release that changes it is a major version, and says so in the changelog.

## What float results do not promise

`nat` and `uniform` are the same on every platform. `uniform` builds its float from the bit pattern of `n * 2^-53` without float arithmetic.

The normal samplers also use `log`, `sin` and `cos`. These come from the platform (the C library natively, `Math` when compiled to JavaScript) and need not be correctly rounded, so a result may differ in the last place between platforms. That difference carries through the rest of the expression. In `skewNormal` it can also flip the `u0 ≥ 0` test when `u0` is within a rounding error of 0, which changes the sign of the skewed part.

## What is verified

Proved as theorems, for all inputs and every generator, in the library:

- `nat` returns a value in `lo..hi` when `lo ≤ hi`, and is core's `randNat`.
- `draws n` returns `n` entries, and is one draw followed by `n - 1` more from the generator it returns. Any property of every draw holds of every entry, so every entry of `nats` lies in `lo..hi`.
- `uniform` returns a float strictly between 0 and 1 that is exactly `n * 2^-53` for some `n` in `1..2^53-1`. These are statements about Lean's model of `Float`.
- `boxMuller`, `standardNormal`, `normal` and `skewNormal` each equal the float expression of their two uniform draws stated by their `_eq` theorem, and each consumes exactly two uniform draws.
- `skewNormal` with shape 0 is `normal`.

Checked by the tests, not proved:

- That the compiled `uniform` matches the model: the bits of `unitFloat` at both ends of the range and at the edges between exponents, and every one of 20000 draws a multiple of `2^-53` strictly inside (0, 1).
- That each sampler keeps its draw order: a pinned sequence per sampler, exact for `nats` and `uniform`, and within `1e-12` relative for the normal samplers.
- That 20000 draws of `nats` reach every value of `0..100`.
- That the sample statistics of 20000 draws fall within at least four standard errors of the parameters: the mean and variance of `uniform`, and the mean, standard deviation and zero skew of `normal`. For `skewNormal`, Azzalini's mean and a third moment whose sign follows the shape.

Not established either way:

- That the float samplers follow their real distributions. Their results are floats, so they are not proved against the real distributions, and the tests check sample statistics, not the distribution itself.
- That any of this holds for a compiler other than native Lean. The tests are plain Lean: to check another compiler, compile `test/Main.lean` from a checkout of a release tag and run it. It exits non-zero if any test fails.

## Installing

Add to your `lakefile.toml`:

```toml
[[require]]
name = "random-sampling"
git = "https://github.com/paulbutcher/lean-random-sampling"
rev = "v0.1.0"
```

## Building

```
lake build
lake test
```

## License

Apache License 2.0; see [LICENSE](LICENSE). The Box-Muller and skew normal draws follow uPlot's `demos/lib/rand.js`, Copyright (c) 2022 Leon Sorokin, released under the MIT license.
