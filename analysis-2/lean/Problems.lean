/-
# Lean problems: continuity and derivatives

The problems are about *reading* Lean: what does a definition or a
statement actually say? Proofs matter less. Work in groups. You may
use AI assistants to write proofs, but check that what you hand in
compiles, and be ready to explain what your definitions and statements
mean.

* Problems 1–3: warm-ups, not graded. Ask for help with them: they
  prepare you for the graded problems.
* Problems 4–7: graded. Problems 4 and 5 are like Problem 1, Problem 6
  is like Problem 2, and Problem 7 is like Problem 3.

A `sorry` marks something for you to fill in. Lean accepts `sorry` with
a warning, so you can work on the problems in any order.
-/
import Mathlib

namespace Problems
/-

`f` is continuous at `a`, as in the lecture.
-/
def ContAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε
/-

## Problem 1 (warm-up): Lipschitz functions

A function `f : ℝ → ℝ` is *Lipschitz continuous* with constant `K` if
`|f(x) - f(y)| ≤ K |x - y|` for all real numbers `x` and `y`.

Replace the `sorry` in the definition below by this condition. The two
theorems after it have complete proofs: your task is done when they
compile without errors. If your definition is right but a proof fails,
read the error message: it shows what the proof expected.
-/
def IsLipschitz (K : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (x y : ℝ), |f x - f y| ≤ K * |x - y|

theorem isLipschitz_linear : IsLipschitz 3 (fun x => 3 * x - 7) := by
  intro x y
  grind

theorem IsLipschitz.contAt {K : ℝ} {f : ℝ → ℝ} (hf : IsLipschitz K f) (a : ℝ) :
    ContAt f a := by
  intro ε hε
  refine ⟨ε / (|K| + 1), by positivity, ?_⟩
  intro x hx
  -- |x - a| < ε / (|K| + 1), so |x - a| (|K| + 1) < ε
  rw [lt_div_iff₀ (by positivity)] at hx
  -- K |x - a| ≤ |K| |x - a|
  have hK : K * |x - a| ≤ |K| * |x - a| :=
    mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _)
  -- the Lipschitz bound for the points x and a, in both orders
  have h₁ := hf x a
  have h₂ := hf a x
  linarith [abs_nonneg (x - a), abs_sub_comm (f x) (f a)]
/-

## Problem 2 (warm-up): a definition that is too strong

A student swapped the order of `ε` and `δ` in the definition of
continuity:
-/
def BadContAt₁ (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ δ > 0, ∀ ε > 0, ∀ x, |x - a| < δ → |f x - f a| < ε
/-

`BadContAt₁ f a` can be characterized as follows. Say in words what
this means.
-/
theorem BadContAt₁.meaning {f : ℝ → ℝ} {a : ℝ} :
    BadContAt₁ f a ↔ ∃ δ > 0, ∀ x, |x - a| < δ → f x = f a := by
  constructor
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun x hx => ?_⟩
    by_contra hne
    have hpos : 0 < |f x - f a| := abs_pos.mpr (sub_ne_zero.mpr hne)
    exact lt_irrefl _ (h _ hpos x hx)
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun ε hε x hx => ?_⟩
    rw [h x hx, sub_self, abs_zero]
    exact hε
/-

The identity function does not satisfy the `BadContAt₁` definition.
-/
theorem not_badContAt₁_id : ¬ BadContAt₁ (fun x => x) 0 := by
  by_contra h
  obtain ⟨δ, hδ, h'⟩ := BadContAt₁.meaning.mp h
  have : δ / 2 = 0 := by
    exact h' (δ / 2) (by grind)
  grind
/-

Show that `BadContAt₁` implies continuity.
-/
theorem BadContAt₁.contAt {f : ℝ → ℝ} {a : ℝ} (hf : BadContAt₁ f a) : ContAt f a := by
  intro ε hε
  obtain ⟨δ, hδ, h'⟩ := hf
  use δ
  grind

/-

## Problem 3 (warm-up): read and judge

Each of `P3a`–`P3d` is a statement. For each one:
1. say in words what it means, *as Lean reads it* (recall junk values
   from the lecture: `x / 0 = 0`, and `deriv f a = 0` when `f` is not
   differentiable at `a`);
2. decide whether it is true, and replace the statement by its negation
   (e.g. `P3a` by `¬ P3a`) if needed;
3. optional: replace the `sorry` by a proof.
-/
def P3a : Prop := ∀ x : ℝ, x / x = 1

def P3b : Prop := deriv (fun x : ℝ => |x|) 0 = 0

def P3c : Prop := ContinuousAt (fun x : ℝ => 1 / x) 0

def P3d : Prop :=
  ∀ f : ℝ → ℝ, (∀ x, deriv f x = 0) → ∀ x y, f x = f y
/-

Answer (in words):
Your answers here.
-/
theorem p3a : ¬ P3a := by
  intro h
  have := h 0
  grind

theorem p3b : P3b := by
  exact deriv_abs_zero

theorem p3c : ¬ P3c := by
  simp [P3c, one_div, NormedField.continuousAt_inv]

theorem p3d : ¬ P3d := by
  intro h
  let f (x : ℝ) : ℝ := if x = 0 then 1 else 0
  have hf : ∀ x, deriv f x = 0 := by
    intro x
    by_cases hx : x = 0
    · subst x
      apply deriv_zero_of_not_differentiableAt
      intro hd
      obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hd.continuousAt 1 zero_lt_one
      have hhalf : 0 < δ / 2 := by positivity
      have hnear : dist (δ / 2) 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hhalf]
        linarith
      have hfar := hclose hnear
      norm_num [f, hhalf.ne', Real.dist_eq] at hfar
    · apply HasDerivAt.deriv
      apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hx] with y hy
      simp [f, hy]
  have heq := h f hf 0 1
  norm_num [f] at heq
/-

## Problem 4: sequential continuity

A function `f` is *sequentially continuous* at `a` if for every sequence
`x` that converges to `a`, the sequence `f(x 0), f(x 1), f(x 2), …`
converges to `f(a)`.

As in Problem 1, write the definition, using `ConvergesTo`, so that
the theorems below compile.

The sequence `x` converges to `L`.
-/
def ConvergesTo (x : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |x n - L| < ε
/-

`f` is sequentially continuous at `a`.
-/
def SeqContAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ (x : ℕ →  ℝ), ConvergesTo x a →  ConvergesTo (f ∘ x) (f a)

theorem ContAt.seqContAt {f : ℝ → ℝ} {a : ℝ} (hf : ContAt f a) : SeqContAt f a := by
  intro x hx ε hε
  obtain ⟨δ, hδ, hδx⟩ := hf ε hε
  obtain ⟨N, hN⟩ := hx δ hδ
  refine ⟨N, fun n hn => ?_⟩
  exact hδx (x n) (hN n hn)

theorem SeqContAt.converges_inv {f : ℝ → ℝ} {a : ℝ} (hf : SeqContAt f a) :
    ConvergesTo (fun n => f (a + 1 / (n + 1))) (f a) := by
  apply hf
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  calc
    |(a + 1 / (n + 1)) - a| = 1 / ((n : ℝ) + 1) := by rw [add_sub_cancel_left, abs_of_pos]; positivity
    _ ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    _ < ε := hN
/-

## Problem 5: uniform continuity

A function `f` is *uniformly continuous* if for every `ε > 0` there is a
`δ > 0` such that `|f(x) - f(y)| < ε` for all `x` and `y` with
`|x - y| < δ`.

As in Problem 1, write the definition and make the theorems below
compile. The last one says that `x ↦ x²` is not uniformly continuous:
think about why it fails.
-/
def UnifCont (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (x y : ℝ), |x - y| < δ →  |f x - f y| < ε

theorem unifCont_linear : UnifCont (fun x => 3 * x - 7) := by
  intro ε hε
  refine ⟨ε / 3, by positivity, ?_⟩
  intro x y hxy
  dsimp only
  -- |(3x - 7) - (3y - 7)| = 3 |x - y|, and the same with x and y swapped
  have h₁ : |3 * x - 7 - (3 * y - 7)| = 3 * |x - y| := by
    rw [show 3 * x - 7 - (3 * y - 7) = 3 * (x - y) by ring, abs_mul]
    norm_num
  have h₂ : |3 * y - 7 - (3 * x - 7)| = 3 * |y - x| := by
    rw [show 3 * y - 7 - (3 * x - 7) = 3 * (y - x) by ring, abs_mul]
    norm_num
  linarith [abs_sub_comm x y]

theorem UnifCont.contAt {f : ℝ → ℝ} (hf : UnifCont f) (a : ℝ) : ContAt f a := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf ε hε
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hx' : |a - x| < δ := by rwa [abs_sub_comm]
  -- apply the definition to the points x and a; `assumption` finds hx or hx'
  have h₁ := h x a (by assumption)
  linarith [abs_sub_comm (f x) (f a)]

theorem not_unifCont_sq : ¬ UnifCont (fun x => x ^ 2) := by
  intro h
  obtain ⟨δ, hδ, h⟩ := h 1 (by norm_num)
  set x : ℝ := 1 / δ with hx
  set y : ℝ := x + δ / 2 with hy
  -- x and y are closer than δ ...
  have hxy : |x - y| < δ := by rw [abs_lt]; constructor <;> linarith
  have hyx : |y - x| < δ := by rwa [abs_sub_comm]
  -- ... but y² - x² = x δ + δ² / 4 = 1 + δ² / 4 is at least 1
  have hxδ : x * δ = 1 := by rw [hx]; field_simp
  have hsq : y ^ 2 - x ^ 2 = 1 + δ ^ 2 / 4 := by rw [hy]; linear_combination hxδ
  have hbad := h x y (by assumption)
  dsimp only at hbad
  have hbig : |y ^ 2 - x ^ 2| = 1 + δ ^ 2 / 4 := by rw [hsq, abs_of_pos (by positivity)]
  linarith [abs_sub_comm (x ^ 2) (y ^ 2), sq_nonneg δ]
/-

## Problem 6: definitions that are too weak

Two more attempts at the definition of continuity; compare Problem 2.
In the first, `δ` may depend on `x`; in the second, `δ = 0` is allowed.
-/
def BadContAt₂ (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∀ x, ∃ δ > 0, |x - a| < δ → |f x - f a| < ε

def BadContAt₃ (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ ≥ 0, ∀ x, |x - a| < δ → |f x - f a| < ε
/-

Show that *every* function satisfies both.
-/
theorem badContAt₂ (f : ℝ → ℝ) (a : ℝ) : BadContAt₂ f a := by
  intro ε hε x
  by_cases h : x = a
  ·
    grind
  ·
    use |x - a|
    grind

theorem badContAt₃ (f : ℝ → ℝ) (a : ℝ) : BadContAt₃ f a := by
  intro ε hε
  use 0
  grind

/-

## Problem 7: read and judge, harder

As in Problem 3.
-/
def P7a : Prop := ∀ (f : ℝ → ℝ) (a : ℝ), deriv f a ≠ 0 → DifferentiableAt ℝ f a

def P7b : Prop :=
  ∀ (f g : ℝ → ℝ) (a : ℝ), deriv (fun x => f x + g x) a = deriv f a + deriv g a

def P7c : Prop := ∀ f : ℝ → ℝ, (∀ x, 0 < deriv f x) → StrictMono f

def P7d : Prop := ∀ f : ℝ → ℝ, StrictMono f → ∀ x, 0 < deriv f x
/-

Answer (in words):
Your answers here.
-/
theorem p7a : P7a := by
  intro f a h
  exact differentiableAt_of_deriv_ne_zero h

theorem p7b : ¬ P7b := by
  intro h
  have hsum : ¬ DifferentiableAt ℝ (fun x : ℝ => |x| + id x) 0 := by
    intro hd
    have hsub := hd.sub (differentiableAt_id (x := (0 : ℝ)))
    apply not_differentiableAt_abs_zero
    simpa [Pi.sub_def] using hsub
  have heq := h (fun x => |x|) id 0
  rw [deriv_zero_of_not_differentiableAt hsum, deriv_abs_zero, deriv_id] at heq
  norm_num at heq

theorem p7c : P7c := by
  intro f hf
  exact strictMono_of_deriv_pos hf

theorem p7d : ¬ P7d := by
  intro h
  have hmono : StrictMono (fun x : ℝ => x ^ 3) :=
    (show Odd (3 : ℕ) by decide).strictMono_pow
  have hpos := h _ hmono 0
  norm_num [deriv_pow_field] at hpos
end Problems
