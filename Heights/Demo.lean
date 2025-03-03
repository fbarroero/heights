import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real BigOperators
noncomputable section

/-
# Example

A sequence `u` of numbers converges to a number `l` if
`∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| < ε`
and a function `f : ℝ → ℝ` is continuous at `x₀` if
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ ⇒ |f(x) - f(x₀)| < ε`

Fact: if `f` is continuous at `x₀` and `u` converges to `x₀` then
`f ∘ u : n ↦ f(u_n)` converges to `f(x₀)`.
-/


/-- The sequence `u` of real numbers converges to `l`. -/
def SequenceHasLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - l| < ε

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε




example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (u_lim : SequenceHasLimit u x₀)
    (f_cont : ContinuousAtPoint f x₀) :
    SequenceHasLimit (f ∘ u) (f x₀) := by
  -- Let ε > 0 be arbitrary
  -- Since `f` is continuous, we can pick a `δ > 0` such that
  -- for all `x`, `|x - x₀| < δ → |f(x) - f(x₀)| < ε`.
  -- Since `u` converges to `x₀`, we can pick a `N` such that
  -- for all `n ≥ N`, `|u_n - x₀| < δ`.
  -- We pick this `N` to show that `f ∘ u` has limit `f(x₀)`.
  -- If `n ≥ N` we have `|u_n - x₀| < δ`,
  -- hence `|f(u_n) - f(x₀)| < ε`.
  -- This finishes the proof.
  sorry



example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (u_lim : SequenceHasLimit u x₀)
    (f_cont : ContinuousAtPoint f x₀) :
    SequenceHasLimit (f ∘ u) (f x₀) := by {
  -- Let ε > 0 be arbitrary
  intro ε hε
  -- Since `f` is continuous, we can pick a `δ > 0` such that
  -- for all `x`, `|x - x₀| < δ → |f(x) - f(x₀)| < ε`.
  obtain ⟨δ, hδ, h1⟩ := f_cont ε hε
  -- Since `u` converges to `x₀`, we can pick a `N` such that
  -- for all `n ≥ N`, `|u_n - x₀| < δ`.
  obtain ⟨N, hN⟩:= u_lim δ hδ
  -- We pick this `N` to show that `f ∘ u` has limit `f(x₀)`.
  use N
  intro n hn
  -- If `n ≥ N` we have `|u_n - x₀| < δ`,
  -- hence `|f(u_n) - f(x₀)| < ε`.
  specialize hN n hn
  specialize h1 (u n) hN
  exact h1
  -- This finishes the proof.
  }

/-!
# How does Lean help you?

* You can use Lean to verify *all* the details of a proof.
* Lean helps you during a proof by
  - displaying all information in the tactic state
  - keeping a proof organized
  - proving parts automatically using AI
* You can explore mathematics using
  Lean's mathematical library `Mathlib`

# General context

Proof assistants software exist since the early 70s.

There is currently a lot of momentum in formalized mathematics, especially Lean:
- AlphaProof
- Terrence Tao has started a few formalization projects
- A proof by Peter Scholze in condensed mathematics was verified in Lean.

Lean exists since 2013, and its mathematical library Mathlib since 2017.
-/



/- Lean is a calculator and programming language -/
#eval 2 + 3

-- compute the sum `0 + 1 + ⋯ + 100`
-- `List.range 101 = [0, 1, ..., 100]`
#eval Id.run do
  let mut sum := 0
  for i in List.range 101 do
    sum := sum + i
  return sum

/- We can also define our own function. -/

def fib : ℕ → ℕ
| 0     => 1
| 1     => 1
| n + 2 => fib n + fib (n + 1)

/- To apply a function `f` to an argument `x`,
you **cannot** write `f(x)` without a space!
You have to write `f (x)`,
with a space between the function and the argument.
You can omit the parentheses in case `x` is a variable: `f x`
-/
#eval fib (6)
#eval fib 13
#eval fib (fib 6)

#eval fib (5) + 5
#eval fib (5 + 5)
-- #eval fib 5 + 5


/-

How does Lean check proofs?

Answer: By giving a type to every mathematical object,
and checking that each function is applied
to an argument with the correct type.

The `#check` command asks Lean to display the type of an object.
Note the colon that means "has type" or "having type"
(think of it as "∈").
-/

#check fib

-- We can also define a function without giving it a name using `fun`.
#check fun x : ℝ ↦ x ^ 3
#check fun n : ℤ ↦ n ^ 3


#check 2

/-
`fib` has type `ℕ → ℕ`, hence it expects natural numbers as inputs,
and produces natural numbers as outputs.

Hence `fib 1` is ok and has type `ℕ`.
-/

#check fib 1

/-
But `fib π` is not ok, we say it doesn't type-check.
-/

-- #check fib π
-- #check fib fib


/- There is a designated type `Prop` that contains all statements.

Unfortunate clash in terminology:
* In math: "Proposition" means
  useful proven statement (less important than a theorem)
* In logic: "Proposition" means
  any statement that can be either true or false.
-/

#check 2 + 2 = 4
#check 3 < π

#check 2 + 2 = 5

def Statement1 : Prop :=
  ∃ p, Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)

def Statement2 : Prop :=
  ∀ n : ℕ, ∃ p ≥ n, Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)

def Statement3 : Prop :=
  ∀ n : ℕ, ∃ p ≥ n, Prime p ∧ Prime (p + 2)

/- Nat.Prime is a predicate on natural numbers, so it has type `ℕ → Prop`. -/

#check Nat.Prime
#check (Nat.Prime)

#check Prime


section primes

open Nat

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  -- Let `N` be an arbitrary natural number
  -- and let `F :=  N ! + 1`.
  -- We set `q` to be the smallest prime factor of `F`.
  -- We have that `q` is a prime number
  -- If we had `q < N`,
  -- `q` would divide `F` and `N`
  -- and therefore divide `1`.
  -- Contradiction!
  sorry

-- In Mathlib we have `minFac` which takes value 1 at 1 (and 2 at 0).

#eval minFac 1
#eval minFac 91

theorem infinitude_of_primes' : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  intro N
  let F := N ! + 1
  let q := minFac F
  use q
  have hq : Nat.Prime q := by
    refine minFac_prime ?_
    simp [F]
    exact factorial_ne_zero N
  constructor
  · by_contra! h
    have h1 : q ∣ F := minFac_dvd F
    have h2 : q ∣ N ! := dvd_factorial (minFac_pos F) (le_of_succ_le h)
    have h3 : q ∣ 1 := by
      exact (Nat.dvd_add_iff_right h2).mpr h1
    have h4 : ¬ q ∣ 1 := by
      refine Nat.Prime.not_dvd_one hq
    contradiction
  · exact hq

-- here's a proof that there are infinitely many primes, as a mathematical theorem
open Nat in
theorem infinitude_of_primes'' : ∀ N, ∃ p ≥ N, Nat.Prime p := by

  intro M
  let F := M ! + 1
  let q := minFac F
  use q

  have qPrime : Nat.Prime q := by
    refine minFac_prime ?_
    have hm : M ! > 0 := by exact factorial_pos M
    omega

  apply And.intro

  { by_contra hqM
    have h1 : q ∣ M ! + 1 := by exact minFac_dvd F
    have hqM2 : q ≤ M := by exact Nat.le_of_not_ge hqM
    have hqM3 : q ∣ M ! := by
      refine dvd_factorial ?_ hqM2
      exact (minFac_pos F)
      --exact (Prime.dvd_factorial qPrime).mpr hqM2
    have hq1 : q ∣ 1 := by exact (Nat.dvd_add_iff_right hqM3).mpr h1
    have hqn1 : ¬ q ∣ 1 := by exact Nat.Prime.not_dvd_one qPrime
    contradiction }

  { exact qPrime }

end primes


/- What is the type of the following definitions? -/

def add_complex_i (y) := y + Complex.I

-- #check add_complex_i

def less_than_pi (x) := x < π

-- #check less_than_pi



/- Notice the difference between the following two types. -/

def less_than (x y : ℝ) : Prop :=
  x < y

#check (less_than)

def differentiable (f : ℝ → ℝ) : Prop :=
  Differentiable ℝ f

#check (differentiable)



/- If we have a statement `A : Prop`, we can prove `A` using *tactics*. -/

/- `rfl` proves equalities that are equal by definition. -/
example : 2 + 2 = 4 := by sorry

/- `ring` proves equalities that follow from the axioms of a ring. -/
example (a b c : ℝ) : (a * b) * c = b * (a * c) := by {
  ring
  }

/- `rw` replaces the left-hand side of `h` with its right-hand side in the goal. -/
example (a b c d : ℝ) (h : a + b = c - d) : 2 * (a + b) = 2 * c - 2 * d := by {
  rw [h]
  ring
  }


section Group

variable {G : Type} [Group G]

theorem abel (H : ∀ (g : G), g ^ 2 = 1) : ∀ g h : G, g * h = h * g := by
  -- Let `g` and `h` be arbitrary elements of `G`.
  -- The hypothesis `H` implies that `g⁻¹ = g`.
  -- We have `g * h = (g * h)⁻¹ = h⁻¹ * g⁻¹ = h * g`.
  sorry

theorem abel' (H : ∀ (g : G), g ^ 2 = 1) : ∀ g h : G, g * h = h * g := by
  have h1 : ∀ g : G, g⁻¹ = g := by
    intro g
    rw [inv_eq_iff_mul_eq_one, ← pow_two]
    exact H g
  intro g h
  rw [← h1 (g * h), mul_inv_rev, h1 g, h1 h]

end Group



--#min_imports
