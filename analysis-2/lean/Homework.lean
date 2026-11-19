import Mathlib

namespace Homework

def ContAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε

theorem ContAt.add {f g : ℝ → ℝ} {a : ℝ} (hf : ContAt f a) (hg : ContAt g a) :
    ContAt (fun x => f x + g x) a := by
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
    |(f x + g x) - (f a + g a)|
      = |(f x - f a) + (g x - g a)| := by congr; ring
    _ ≤ |f x - f a| + |g x - g a| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hf_small hg_small
    _ = ε := by ring

end Homework
