/-
# Lean demo: continuity and derivatives

-/
import Mathlib

namespace Demo
/-
## 1. Reading Lean

Everything in Lean has a *type*.
-/
#check 2
#check (2 : ℝ)
/-

Expressions can be given names.
-/
def two := 2
#check two
/-

Definitional equality can be checked using `rfl`.
-/
example : two = 2 := rfl
/-

A function with an argument.
-/
def sq (x : ℝ) := x^2
#check sq
#check sq 2
/-

The same function written anonymously.
-/
example : sq = fun x => x^2 := rfl
/-

Statements are types too: their type is `Prop`.
-/
#check ∀ x : ℝ, 0 ≤ x ^ 2
/-

A proof of a statement is an element of that type.
A `theorem` has a name, hypotheses, a statement after `:`
and a proof after `:=`. Here `x` is an argument in round brackets:
whoever uses the theorem supplies it.
-/
theorem sq_nonneg (x : ℝ) : 0 ≤ x ^ 2 := by
  positivity
/-

Using a theorem is applying it, like a function.
-/
#check sq_nonneg 5
/-

## 2. Our own definition of continuity

`f` is continuous at `a`.
-/
def ContAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε
/-

Constant functions are continuous. Any `δ > 0` works.
-/
theorem contAt_const (c a : ℝ) : ContAt (fun _ => c) a := by
  intro ε hε          -- let ε > 0
  use 1               -- choose δ = 1
  grind
/-

The function `x ↦ kx + b` is continuous at every point.
Sketch of proof for `k ≠ 0`.
Given `ε`, take `δ = ε / |k|`.
Then `|(kx + b) - (ka + b)| = |k||x - a| < |k|δ = ε`.

Let's do a special case first.
-/
example (a : ℝ) : ContAt (fun x => 2 * x + 1) a := by
  intro ε hε
  use ε / 2
  grind
/-

The general case.
-/
theorem contAt_linear (k b a : ℝ) : ContAt (fun x => k * x + b) a := by
  by_cases hk : k = 0
  · simp [hk]
    exact contAt_const b a
  · intro ε hε
    use ε / |k|
    constructor
    · positivity
    · intro x hx
      simp
      calc
        |k * x - k * a|
        _ = |k * (x - a)| := by grind
        _ = |k| * |x - a| := by grind
        _ < |k| * (ε / |k|) := by
          have hk' : |k| > 0 := by positivity
          nlinarith
        _ = ε := by grind
/-

## 3. Mathlib's definition

Mathlib, Lean's mathematics library, already defines continuity, in a
much more general form (for topological spaces, with filters). We do
not need filters: Mathlib also proves that its definition agrees with
the ε-δ one for real functions.
-/
#print ContinuousAt

theorem contAt_iff_continuousAt (f : ℝ → ℝ) (a : ℝ) : ContAt f a ↔ ContinuousAt f a := by
  simp [Metric.continuousAt_iff]
  simp [Real.dist_eq]
  simp [ContAt]
/-

This equivalence unlocks tools from Mathlib: `fun_prop` proves
continuity of functions built from continuous pieces.
-/
theorem contAt_example (a : ℝ) : ContAt (fun x => x ^ 3 + Real.sin x) a := by
  simp [contAt_iff_continuousAt]
  fun_prop
/-

## 4. Derivatives and junk values

`HasDerivAt f f' a` says: `f` is differentiable at `a` with derivative
`f'`. It is a *statement*. `deriv f a` is a *number*: the derivative,
if it exists. But a function must return something for every input.
What is `deriv f a` when `f` is not differentiable at `a`?

Let's consider first a differentiable function.
-/
theorem hasDerivAt_sq (a : ℝ) : HasDerivAt (fun x => x ^ 2) (2 * a) a := by
  grind [hasDerivAt_pow 2 a]

theorem deriv_sq (a : ℝ) : deriv (fun x => x ^ 2) a = 2 * a := by
  exact (hasDerivAt_sq a).deriv
/-

Lean's answer: `0`, a *junk value*.
-/
theorem deriv_abs_junk : deriv (fun x : ℝ => |x|) 0 = 0 := by
  apply deriv_zero_of_not_differentiableAt
  exact not_differentiableAt_abs_zero
/-

The same happens with division.
-/
theorem div_zero_junk : (1 : ℝ) / 0 = 0 := by
  grind
/-

A theorem about `deriv f a` with no differentiability
hypothesis may still be true, but it may not say what you think. You
have to read the definitions.

## 5. How to work

An AI assistant can write proofs. Lean checks them, but only *you*
can check that the statement says what you meant.
-/
end Demo
