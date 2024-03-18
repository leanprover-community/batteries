
/-!
# Benchmarking the `omega` tactic

As it's important that `omega` is fast, particularly when it has nothing to do,
this file maintains a benchmark suite for `omega`. It is particularly low-tech,
and currently only reproducible on Scott Morrison's FRO machine;
nevertheless it seems useful to keep the benchmark history in the repository.

The benchmark file consists of the test suite from `omega`'s initial release,
with one test removed (in which a test-for-failure succeeds with today's `omega`).

The benchmark consists of `lake build && hyperfine "lake env lean test/omega/benchmark.lean"`
run on a freshly rebooted machine!

2024-02-06 feat: omega uses Lean.HashMap instead of Std.Data.HashMap (#588)
kim@carica std4 % lake build && hyperfine "lake env lean test/omega/benchmark.lean"
Benchmark 1: lake env lean test/omega/benchmark.lean
  Time (mean ± σ):      2.530 s ±  0.008 s    [User: 2.249 s, System: 0.276 s]
  Range (min … max):    2.513 s …  2.542 s    10 runs

2024-02-03 feat: omega handles min, max, if (#575)
kim@carica std4 % lake build && hyperfine "lake env lean test/omega/benchmark.lean"
Benchmark 1: lake env lean test/omega/benchmark.lean
  Time (mean ± σ):      2.526 s ±  0.009 s    [User: 2.250 s, System: 0.272 s]
  Range (min … max):    2.513 s …  2.542 s    10 runs

2024-02-02 fix: revert OmegaM state when not multiplying out (#570)
kim@carica std4 % lake build && hyperfine "lake env lean test/omega/benchmark.lean"
Benchmark 1: lake env lean test/omega/benchmark.lean
  Time (mean ± σ):      2.569 s ±  0.004 s    [User: 2.291 s, System: 0.273 s]
  Range (min … max):    2.563 s …  2.574 s    10 runs

2024-01-12 feat: omega handles double negation and implication hypotheses (#522)
kim@carica std4 % lake build && hyperfine "lake env lean test/omega/benchmark.lean"
Benchmark 1: lake env lean test/omega/benchmark.lean
  Time (mean ± σ):      2.575 s ±  0.004 s    [User: 2.302 s, System: 0.268 s]
  Range (min … max):    2.570 s …  2.581 s    10 runs

2024-01-10 feat: omega understands Prod.Lex (#511)
kim@carica std4 % lake build && hyperfine "lake env lean test/omega/benchmark.lean"
Benchmark 1: lake env lean test/omega/benchmark.lean
  Time (mean ± σ):      2.567 s ±  0.006 s    [User: 2.295 s, System: 0.268 s]
  Range (min … max):    2.559 s …  2.576 s    10 runs

2024-01-10 feat: omega handles iff and implications (#503)
kim@carica std4 % lake build && hyperfine "lake env lean test/omega/benchmark.lean"
Benchmark 1: lake env lean test/omega/benchmark.lean
  Time (mean ± σ):      2.348 s ±  0.007 s    [User: 2.060 s, System: 0.282 s]
  Range (min … max):    2.335 s …  2.356 s    10 runs

2023-12-21 feat: omega (#463)
kim@carica std4 % lake build && hyperfine "lake env lean test/omega/benchmark.lean"
Benchmark 1: lake env lean test/omega/benchmark.lean
  Time (mean ± σ):      2.362 s ±  0.008 s    [User: 2.080 s, System: 0.277 s]
  Range (min … max):    2.349 s …  2.372 s    10 runs

-/

example : True := by
  fail_if_success omega
  trivial

-- set_option trace.omega true
example (_ : (1 : Int) < (0 : Int)) : False := by omega

example (_ : (0 : Int) < (0 : Int)) : False := by omega
example (_ : (0 : Int) < (1 : Int)) : True := by (fail_if_success omega); trivial

example {x : Int} (_ : 0 ≤ x) (_ : x ≤ 1) : True := by (fail_if_success omega); trivial
example {x : Int} (_ : 0 ≤ x) (_ : x ≤ -1) : False := by omega

example {x : Int} (_ : x % 2 < x - 2 * (x / 2)) : False := by omega
example {x : Int} (_ : x % 2 > 5) : False := by omega

example {x : Int} (_ : 2 * (x / 2) > x) : False := by omega
example {x : Int} (_ : 2 * (x / 2) ≤ x - 2) : False := by omega

example {x : Nat} : x / 0 = 0 := by omega
example {x : Int} : x / 0 = 0 := by omega

example {x : Int} : x / 2 + x / (-2) = 0 := by omega

example (_ : 7 < 3) : False := by omega
example (_ : 0 < 0) : False := by omega

example {x : Nat} (_ : x > 7) (_ : x < 3) : False := by omega
example {x : Nat} (_ : x ≥ 7) (_ : x ≤ 3) : False := by omega

example {x y : Nat} (_ : x + y > 10) (_ : x < 5) (_ : y < 5) : False := by omega

example {x y : Int} (_ : x + y > 10) (_ : 2 * x < 11) (_ : y < 5) : False := by omega
example {x y : Nat} (_ : x + y > 10) (_ : 2 * x < 11) (_ : y < 5) : False := by omega

example {x y : Int} (_ : 2 * x + 4 * y = 5) : False := by omega
example {x y : Nat} (_ : 2 * x + 4 * y = 5) : False := by omega

example {x y : Int} (_ : 6 * x + 7 * y = 5) : True := by (fail_if_success omega); trivial

example {x y : Nat} (_ : 6 * x + 7 * y = 5) : False := by omega

example {x : Nat} (_ : x < 0) : False := by omega

example {x y z : Int} (_ : x + y > z) (_ : x < 0) (_ : y < 0) (_ : z > 0) : False := by omega

example {x y : Nat} (_ : x - y = 0) (_ : x > y) : False := by
  fail_if_success omega (config := { splitNatSub := false })
  omega

example {x y z : Int} (_ : x - y - z = 0) (_ : x > y + z) : False := by omega

example {x y z : Nat} (_ : x - y - z = 0) (_ : x > y + z) : False := by omega

example {a b c d e f : Nat} (_ : a - b - c - d - e - f = 0) (_ : a > b + c + d + e + f) :
    False := by
  omega

example {x y : Nat} (h₁ : x - y ≤ 0) (h₂ : y < x) : False := by omega

example {x y : Int} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by omega

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by omega

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 4) : False := by omega

example {x y : Nat} (_ : x / 2 - y / 3 < x % 2) (_ : 3 * x ≥ 2 * y + 4) : False := by omega

example {x : Int} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by omega

example {x : Nat} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by omega

example {x : Nat} (h₁ : x / 3 ≥ 2) (h₂ : x < 6) : False := by omega

example {x : Int} {y : Nat} (_ : 0 < x) (_ : x + y ≤ 0) : False := by omega

example {a b c : Nat} (_ : a - (b - c) ≤ 5) (_ : b ≥ c + 3) (_ : a + c ≥ b + 6) : False := by omega

example {x : Nat} : 1 < (1 + ((x + 1 : Nat) : Int) + 2) / 2 := by omega

example {x : Nat} : (x + 4) / 2 ≤ x + 2 := by omega

example {x : Int} {m : Nat} (_ : 0 < m) (_ : ¬x % ↑m < (↑m + 1) / 2) : -↑m / 2 ≤ x % ↑m - ↑m := by
  omega


example (h : (7 : Int) = 0) : False := by omega

example (h : (7 : Int) ≤ 0) : False := by omega

example (h : (-7 : Int) + 14 = 0) : False := by omega

example (h : (-7 : Int) + 14 ≤ 0) : False := by omega

example (h : (1 : Int) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 0) : False := by
  omega

example (h : (7 : Int) - 14 = 0) : False := by omega

example (h : (14 : Int) - 7 ≤ 0) : False := by omega

example (h : (1 : Int) - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 = 0) : False := by
  omega

example (h : -(7 : Int) = 0) : False := by omega

example (h : -(-7 : Int) ≤ 0) : False := by omega

example (h : 2 * (7 : Int) = 0) : False := by omega

example (h : (7 : Int) < 0) : False := by omega

example {x : Int} (h : x + x + 1 = 0) : False := by omega

example {x : Int} (h : 2 * x + 1 = 0) : False := by omega

example {x y : Int} (h : x + x + y + y + 1 = 0) : False := by omega

example {x y : Int} (h : 2 * x + 2 * y + 1 = 0) : False := by omega

example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 ≤ 3 - x) : False := by omega

example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 < 4 - x) : False := by omega

example {x : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : 2 * x + 1 ≤ 0) : False := by omega

example {x : Int} (h₁ : 0 < 2 * x + 2) (h₂ : 2 * x + 1 ≤ 0) : False := by omega

example {x y : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : 2 * y + 1 ≤ 0) : False := by omega

example {x y z : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : y = z) (h₄ : 2 * z + 1 ≤ 0) :
    False := by omega

example {x1 x2 x3 x4 x5 x6 : Int} (h : 0 ≤ 2 * x1 + 1) (h : x1 = x2) (h : x2 = x3) (h : x3 = x4)
    (h : x4 = x5) (h : x5 = x6) (h : 2 * x6 + 1 ≤ 0) : False := by omega

example {x : Int} (_ : 1 ≤ -3 * x) (_ : 1 ≤ 2 * x) : False := by omega

example {x y : Int} (_ : 2 * x + 3 * y = 0) (_ : 1 ≤ x) (_ : 1 ≤ y) : False := by omega

example {x y z : Int} (_ : 2 * x + 3 * y = 0) (_ : 3 * y + 4 * z = 0) (_ : 1 ≤ x) (_ : 1 ≤ -z) :
    False := by omega

example {x y z : Int} (_ : 2 * x + 3 * y + 4 * z = 0) (_ : 1 ≤ x + y) (_ : 1 ≤ y + z)
    (_ : 1 ≤ x + z) : False := by omega

example {x y : Int} (_ : 1 ≤ 3 * x) (_ : y ≤ 2) (_ : 6 * x - 2 ≤ y) : False := by omega

example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : 1 ≤ x) : False := by
  omega
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : x ≥ 1) : False := by
  omega
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : 0 < x) : False := by
  omega
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : x > 0) : False := by
  omega

example {x : Nat} (_ : 10 ∣ x) (_ : ¬ 5 ∣ x) : False := by omega
example {x y : Nat} (_ : 5 ∣ x) (_ : ¬ 10 ∣ x) (_ : y = 7) (_ : x - y ≤ 2) (_ : x ≥ 6) : False := by
  omega

example (x : Nat) : x % 4 - x % 8 = 0 := by omega

example {n : Nat} (_ : n > 0) : (2*n - 1) % 2 = 1 := by omega

example (x : Int) (_ : x > 0 ∧ x < -1) : False := by omega
example (x : Int) (_ : x > 7) : x < 0 ∨ x > 3 := by omega

example (_ : ∃ n : Nat, n < 0) : False := by omega
example (_ : { x : Int // x < 0 ∧ x > 0 }) : False := by omega
example {x y : Int} (_ : x < y) (z : { z : Int // y ≤ z ∧ z ≤ x }) : False := by omega

example (a b c d e : Int)
    (ha : 2 * a + b + c + d + e = 4)
    (hb : a + 2 * b + c + d + e = 5)
    (hc : a + b + 2 * c + d + e = 6)
    (hd : a + b + c + 2 * d + e = 7)
    (he : a + b + c + d + 2 * e = 8) : e = 3 := by omega

example (a b c d e : Int)
    (ha : 2 * a + b + c + d + e = 4)
    (hb : a + 2 * b + c + d + e = 5)
    (hc : a + b + 2 * c + d + e = 6)
    (hd : a + b + c + 2 * d + e = 7)
    (he : a + b + c + d + 2 * e = 8 ∨ e = 3) : e = 3 := by
  fail_if_success omega (config := { splitDisjunctions := false })
  omega

example {a b : Int} (h : a < b) (w : b < a) : False := by omega

example (_e b c a v0 v1 : Int) (_h1 : v0 = 5 * a) (_h2 : v1 = 3 * b) (h3 : v0 + v1 + c = 10) :
    v0 + 5 + (v1 - 3) + (c - 2) = 10 := by omega

example (h : (1 : Int) < 0) (_ : ¬ (37 : Int) < 42) (_ : True) (_ : (-7 : Int) < 5) :
    (3 : Int) < 7 := by omega

example (A B : Int) (h : 0 < A * B) : 0 < 8 * (A * B) := by omega

example (A B : Nat) (h : 7 < A * B) : 0 < A*B/8 := by omega
example (A B : Int) (h : 7 < A * B) : 0 < A*B/8 := by omega

example (ε : Int) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε := by omega

example (x y z : Int) (h1 : 2*x < 3*y) (h2 : -4*x + z/2 < 0) (h3 : 12*y - z < 0) : False := by omega

example (ε : Int) (h1 : ε > 0) : ε / 2 < ε := by omega

example (ε : Int) (_ : ε > 0) : ε - 2 ≤ ε / 3 + ε / 3 + ε / 3 := by omega
example (ε : Int) (_ : ε > 0) : ε / 3 + ε / 3 + ε / 3 ≤ ε := by omega
example (ε : Int) (_ : ε > 0) : ε - 2 ≤ ε / 3 + ε / 3 + ε / 3 ∧ ε / 3 + ε / 3 + ε / 3 ≤ ε := by
  omega

example (x : Int) (h : 0 < x) : 0 < x / 1 := by omega

example (x : Int) (h : 5 < x) : 0 < x/2/3 := by omega

example (_a b _c : Nat) (h2 : b + 2 > 3 + b) : False := by omega
example (_a b _c : Int) (h2 : b + 2 > 3 + b) : False := by omega

example (g v V c h : Int) (_ : h = 0) (_ : v = V) (_ : V > 0) (_ : g > 0)
    (_ : 0 ≤ c) (_ : c < 1) : v ≤ V := by omega

example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (h3 : 12 * y - 4 * z < 0) :
    False := by
  omega

example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (_h3 : x * y < 5)
    (h3 : 12 * y - 4 * z < 0) : False := by omega

example (a b c : Int) (h1 : a > 0) (h2 : b > 5) (h3 : c < -10) (h4 : a + b - c < 3) : False := by
  omega

example (_ b _ : Int) (h2 : b > 0) (h3 : ¬ b ≥ 0) : False := by
  omega

example (x y z : Int) (hx : x ≤ 3 * y) (h2 : y ≤ 2 * z) (h3 : x ≥ 6 * z) : x = 3 * y := by
  omega

example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (_h3 : x * y < 5) :
    ¬ 12 * y - 4 * z < 0 := by
  omega

example (x y z : Int) (hx : ¬ x > 3 * y) (h2 : ¬ y > 2 * z) (h3 : x ≥ 6 * z) : x = 3 * y := by
  omega

example (x y : Int) (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3) (h' : (x + 4) * x ≥ 0)
    (h'' : (6 + 3 * y) * y ≥ 0) : False := by omega

example (a : Int) (ha : 0 ≤ a) : 0 * 0 ≤ 2 * a := by omega

example (x y : Int) (h : x < y) : x ≠ y := by omega

example (x y : Int) (h : x < y) : ¬ x = y := by omega

example (prime : Nat → Prop) (x y z : Int) (h1 : 2 * x + ((-3) * y) < 0) (h2 : (-4) * x + 2*  z < 0)
    (h3 : 12 * y + (-4) * z < 0) (_ : prime 7) : False := by omega

example (i n : Nat) (h : (2 : Int) ^ i ≤ 2 ^ n) : (0 : Int) ≤ 2 ^ n - 2 ^ i := by omega

-- Check we use `exfalso` on non-comparison goals.
example (prime : Nat → Prop) (_ b _ : Nat) (h2 : b > 0) (h3 : b < 0) : prime 10 := by
  omega

example (a b c : Nat) (h2 : (2 : Nat) > 3)  : a + b - c ≥ 3 := by omega

-- Verify that we split conjunctions in hypotheses.
example (x y : Int)
    (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3 ∧ (x + 4) * x ≥ 0 ∧ (6 + 3 * y) * y ≥ 0) :
    False := by omega

example (mess : Nat → Nat) (S n : Nat) :
    mess S + (n * mess S + n * 2 + 1) < n * mess S + mess S + (n * 2 + 2) := by omega

example (p n p' n' : Nat) (h : p + n' = p' + n) : n + p' = n' + p := by
  omega

example (a b c : Int) (h1 : 32 / a < b) (h2 : b < c) : 32 / a < c := by omega
