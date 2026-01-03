/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

module
public import Init.Data.Nat

section

/-! # Running Statistics

This module implements Welford's one-pass algorithm for calculating the mean and
standard deviation of a sample or a population. The advantage of this algorithm is
that it is not necessary to store the data.

The algorithm uses the recurrence formulas for the mean `μ`, variance `σ²`
and the sample variance `s²`:
```
  μₖ = μₖ₋₁ + (xₖ − μₖ₋₁)/k
  σ²ₖ = σ²ₖ₋₁*(k-1)/k + (xₖ − μₖ₋₁)*(xₖ − μₖ)/k
  s²ₖ = s²ₖ₋₁*(k-2)/(k-1) + (xₖ - μₖ₋₁)²/k
```
To improve performance, Welford's algorithm keeps track of the two running
quantities:
```
  Mₖ = Mₖ₋₁ + (xₖ - Mₖ₋₁)/k
  Sₖ = Sₖ₋₁ + (xₖ - Mₖ₋₁)*(xₖ - Mₖ)
```
Then: `μₖ = Mₖ`, `σ²ₖ = Sₖ/k`, `s²ₖ = Sₖ/(k-1)`.
-/

namespace Batteries

/-- Compute running statistics of a data stream using Welford's algorithm. -/
public structure RunningStats where
  /-- Initialize running statistics. -/
  init ::
  /-- Number of data points, -/
  count : Nat := 0
  /-- Mean of data points. -/
  mean : Float := 0.0
  /-- Variance of data points times the number of data points. -/
  var : Float := 0.0

namespace RunningStats

/-- Add a new data point to running statistics. -/
@[inline]
public def push (data : Float) (s : RunningStats) : RunningStats :=
  let count := s.count + 1
  let mean := s.mean + (data - s.mean) / count.toFloat
  let var := s.var + (data - s.mean) * (data - mean)
  {count, mean, var}

/-- Variance of running data stream. -/
@[inline]
public def variance (s : RunningStats) : Float :=
  if s.count ≤ 1 then 0.0 else s.var / s.count.toFloat

/-- Unbiased variance of running data stream. -/
@[inline]
public def sampleVariance (s : RunningStats) : Float :=
  if s.count ≤ 2 then 0.0 else s.var / (s.count - 1).toFloat

/-- Standard deviation of running data stream. -/
@[inline]
public def standardDeviation (s : RunningStats) : Float :=
  Float.sqrt s.sampleVariance
