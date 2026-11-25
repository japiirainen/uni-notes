import Mathlib

namespace Homework2

def DerivAt (f : ℝ → ℝ) (f' a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a - f' * (x - a)| ≤ ε * |x - a|

theorem DerivAt.add {f g : ℝ →  ℝ} {f' g' a : ℝ}
    (hf : DerivAt f f' a) (hg : DerivAt g g' a) :
    DerivAt (fun x => f x + g x) (f' + g') a := by
  intro ε hε
  have hε₂ : 0 < ε / 2 := by positivity

  obtain ⟨δ₁, hδ₁, hf_bound⟩ := hf (ε / 2) hε₂
  obtain ⟨δ₂, hδ₂, hg_bound⟩ := hg (ε / 2) hε₂

  let δ := min δ₁ δ₂

  have hδ : 0 < δ := lt_min hδ₁ hδ₂

  use δ, hδ
  intro x hx

  have hx₁ : |x - a| < δ₁ := lt_of_lt_of_le hx (min_le_left δ₁ δ₂)
  have hx₂ : |x - a| < δ₂ := lt_of_lt_of_le hx (min_le_right δ₁ δ₂)

  have hf_small := hf_bound x hx₁
  have hg_small := hg_bound x hx₂

  calc
    |(f x + g x) - (f a + g a) - (f' + g') * (x - a)|
      = |(f x - f a - f' * (x - a)) + (g x - g a - g' * (x - a))|
      := by congr; ring
    _ ≤ |f x - f a - f' * (x - a)| + |g x - g a - g' * (x - a)|
      := abs_add_le _ _
    _ ≤ (ε / 2) * |x - a| + (ε / 2) * |x - a| := add_le_add hf_small hg_small
    _ = ε * |x - a| := by ring

end Homework2
