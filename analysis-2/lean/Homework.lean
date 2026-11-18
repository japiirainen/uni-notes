/-
# Lean homework: continuity

A `sorry` marks something for you to fill in.
-/
import Mathlib

namespace Homework
/-

`f` is continuous at `a`, as in the lecture.
-/
def ContAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε
/-

## Problem: the sum of continuous functions

The sum of continuous functions is continuous. Prove it in Lean,
following the `ε/2` argument: given `ε > 0`, take `δ₁` for `f` and
`ε / 2`, `δ₂` for `g` and `ε / 2`, and choose `δ = min δ₁ δ₂`.

Here `f`, `g`, and `a` are implicit arguments: Lean infers them from the
hypotheses `hf` and `hg`, so a user writes `ContAt.add hf hg`.
-/
theorem ContAt.add {f g : ℝ → ℝ} {a : ℝ} (hf : ContAt f a) (hg : ContAt g a) :
    ContAt (fun x => f x + g x) a := by
  sorry

end Homework
