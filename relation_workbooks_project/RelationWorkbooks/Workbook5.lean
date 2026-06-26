import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

/-!
# Workbook: powers of a relation, paths, reachability, strong components, and transitive closure

This workbook is designed as a *student version*.
The statements are set up for you, but the proofs are left as `sorry`.

The mathematical setting is:
- `A` is a type
- `R : A → A → Prop` is a binary relation

The original exercise is phrased for finite sets. In Lean, it is usually cleaner to first
formalize the definitions for an arbitrary type `A`, and only add finiteness assumptions when
we really need them.

That matters here for two reasons.

1. Powers of a relation are naturally recursive.
   In Lean, the idiomatic way to define them is by recursion on `Nat`.

2. "There is a path from `a` to `b`" can be expressed in several ways.
   We will deliberately build it from relation powers first, because that matches the exercise.
   Later we note how this connects to the standard reflexive-transitive closure in mathlib.

## Design choices in this workbook

There are two common ways to define "reachability".

### Option A. Via powers `R^n`
You define `relPow R n a b` recursively, and then say that `a` reaches `b` if
`∃ n, relPow R n a b`.

Pros:
- closest to the exercise
- makes path length explicit
- good practice with recursive definitions

Cons:
- some proofs require induction on `n`
- composition lemmas must be proved by hand

### Option B. Via mathlib's transitive closure
Mathlib already has closure constructions such as reflexive-transitive closure.
These are often more idiomatic for serious developments.

Pros:
- many lemmas already exist
- graph-theoretic reasoning becomes smoother

Cons:
- hides the path-length structure that the exercise wants you to confront

This workbook uses Option A as the primary formalization, and then asks you to relate it to
mathlib-style closure ideas.

## Important Lean idea: relations are functions
A binary relation on `A` is represented as

`A → A → Prop`

So `R a b` means exactly what mathematicians write as `aRb`.

## Important Lean idea: identity relation
The relation `fun a b => a = b` is the identity relation.
That is the right definition for `R^0`.

## Important Lean idea: composition of relations
If `S` and `T` are relations on `A`, then their composition is the relation
saying there exists an intermediate point.

We define our own relation composition below. Mathlib has related notions,
but writing it once yourself is useful and keeps the structure visible.
-/

universe u

namespace Workbook5

variable {A : Type u}

/-- A binary relation on `A`. This is just a convenient abbreviation. -/
abbrev Rel (A : Type u) := A → A → Prop

/-- The identity relation on `A`. -/
def idRel : Rel A := fun a b => a = b

/-- Composition of relations. Read `compRel S T` as `S ∘ T` in the exercise's sense:
first follow `T`, then `S`. -/
def compRel (S T : Rel A) : Rel A :=
  fun a b => ∃ c, T a c ∧ S c b

/-- Recursive powers of a relation.

`relPow R 0` is the identity relation.
`relPow R (n+1)` is `relPow R n` composed with `R`.

This matches the exercise's recursive definition `R^n = R^(n-1) ∘ R` for `n ≥ 1`.
-/
def relPow (R : Rel A) : Nat → Rel A
  | 0 => idRel
  | n + 1 => compRel (relPow R n) R

/-!
## First block: unfold the definitions

In Lean, many proofs about recursive objects begin with "unfolding" the definition at small values.
These lemmas are basic warm-up exercises and are worth proving explicitly.
-/

@[simp] theorem idRel_iff (a b : A) : idRel a b ↔ a = b := by
  sorry

@[simp] theorem compRel_iff (S T : Rel A) (a b : A) :
    compRel S T a b ↔ ∃ c, T a c ∧ S c b := by
  sorry

@[simp] theorem relPow_zero (R : Rel A) : relPow R 0 = idRel := by
  sorry

@[simp] theorem relPow_succ (R : Rel A) (n : Nat) :
    relPow R (n + 1) = compRel (relPow R n) R := by
  sorry

/-- Unfold `R^1`. -/
theorem relPow_one_eq (R : Rel A) : relPow R 1 = R := by
  sorry

/-- Unfold `R^2` into an existential intermediate vertex. -/
theorem relPow_two_iff (R : Rel A) (a b : A) :
    relPow R 2 a b ↔ ∃ c, R a c ∧ R c b := by
  sorry

/-!
## Second block: paths and reachability

The exercise says there is a path from `a` to `b` of length `n` iff `a R^n b`.
We encode that directly.
-/

/-- A path of length `n` from `a` to `b` along the relation `R`. -/
def HasPathOfLen (R : Rel A) (n : Nat) (a b : A) : Prop :=
  relPow R n a b

/-- Reachability: there exists some finite path from `a` to `b`. -/
def Reachable (R : Rel A) (a b : A) : Prop :=
  ∃ n : Nat, HasPathOfLen R n a b

/-- Mutual reachability. This is the relation called `T` in the exercise. -/
def StronglyConnectedRel (R : Rel A) (a b : A) : Prop :=
  Reachable R a b ∧ Reachable R b a

/-!
## How to think about paths idiomatically in Lean

There is a subtle modeling issue here.

In ordinary mathematics, you may say:
"A path from `a` to `b` of length `n` is a finite sequence
`a = x₀, x₁, ..., xₙ = b` such that `R xᵢ xᵢ₊₁` for all `i`."

In Lean, that sequence-based approach is possible, but it introduces bookkeeping:
- lists or vectors
- endpoint constraints
- adjacency conditions along consecutive entries

For this exercise, the recursive definition of `relPow` is cleaner.
It already *encodes* exactly the existence of such a chain.

So the idiomatic advice here is:
- use recursive relation powers for the foundational development
- only introduce explicit lists of vertices if you later need combinatorial arguments
  about repeating vertices, shortening paths, and finiteness bounds

That is why the next theorem is important: it extracts composition of paths directly from the recursion.
-/

/-- Composition of path lengths: if there is a path of length `m` from `a` to `b`
and a path of length `n` from `b` to `c`, then there is a path of length `m+n`
from `a` to `c`.

This is one of the key structural lemmas in the whole workbook.
-/
theorem relPow_add (R : Rel A) (m n : Nat) (a b c : A) :
    relPow R m a b → relPow R n b c → relPow R (m + n) a c := by
  sorry

/-- Reachability is reflexive because there is always a path of length `0`. -/
theorem reachable_refl (R : Rel A) (a : A) : Reachable R a a := by
  sorry

/-- Every edge is a path of length `1`, hence gives reachability. -/
theorem reachable_of_rel (R : Rel A) {a b : A} :
    R a b → Reachable R a b := by
  sorry

/-- Reachability is transitive. This corresponds to the relation `S` in the exercise. -/
theorem reachable_trans (R : Rel A) {a b c : A} :
    Reachable R a b → Reachable R b c → Reachable R a c := by
  sorry

/-!
## Third block: the relation `T = S ∩ S⁻¹`

We do not define inverse first and then intersect. We define the intended relation directly:
mutual reachability.

This is more transparent in Lean. You can still later show that it agrees with `S ∩ S⁻¹`
if you define inverse and intersection of relations.
-/

theorem stronglyConnectedRel_refl (R : Rel A) (a : A) :
    StronglyConnectedRel R a a := by
  sorry

theorem stronglyConnectedRel_symm (R : Rel A) {a b : A} :
    StronglyConnectedRel R a b → StronglyConnectedRel R b a := by
  sorry

theorem stronglyConnectedRel_trans (R : Rel A) {a b c : A} :
    StronglyConnectedRel R a b → StronglyConnectedRel R b c →
    StronglyConnectedRel R a c := by
  sorry

/-- Mutual reachability is an equivalence relation. -/
theorem stronglyConnectedRel_is_equivalence (R : Rel A) :
    Equivalence (StronglyConnectedRel R) := by
  sorry

/-!
## Fourth block: strong connectedness of the whole relation

The exercise says `(A,R)` is strongly connected if there is just one equivalence class.
On a type, the clean formulation is simply:

`∀ a b, StronglyConnectedRel R a b`

That is equivalent to saying there is a single equivalence class under the relation.
-/

/-- The relation `R` is strongly connected if every pair of points is mutually reachable. -/
def IsStronglyConnected (R : Rel A) : Prop :=
  ∀ a b : A, StronglyConnectedRel R a b

/-- Restatement of strong connectedness. -/
theorem isStronglyConnected_iff (R : Rel A) :
    IsStronglyConnected R ↔ ∀ a b : A, Reachable R a b := by
  sorry

/-!
## Fifth block: transitive closure

Now we get to the conceptual heart of the exercise.

The reachability relation should be the transitive closure of `R`.
In Lean, a good way to package this is:
- `Contains R T := ∀ ⦃a b⦄, R a b → T a b`
- `IsTransitiveClosure R T :=`
    1. `T` contains `R`
    2. `T` is transitive
    3. `T` is minimal among transitive relations containing `R`

This mirrors the mathematical definition closely.
-/

/-- Relation inclusion. -/
def RelSubset (R S : Rel A) : Prop :=
  ∀ ⦃a b : A⦄, R a b → S a b

/-- Transitivity predicate for a relation. -/
def IsTransitive (R : Rel A) : Prop :=
  ∀ ⦃a b c : A⦄, R a b → R b c → R a c

/-- `T` is a transitive closure of `R` if it is transitive, contains `R`,
and is minimal with these properties. -/
def IsTransitiveClosure (R T : Rel A) : Prop :=
  RelSubset R T ∧
  IsTransitive T ∧
  ∀ U : Rel A, RelSubset R U → IsTransitive U → RelSubset T U

/-- Reachability contains the original relation. -/
theorem relSubset_reachable (R : Rel A) : RelSubset R (Reachable R) := by
  sorry

/-- Reachability is transitive. -/
theorem reachable_isTransitive (R : Rel A) : IsTransitive (Reachable R) := by
  sorry

/-- The crucial minimality lemma: any transitive relation containing `R`
contains every finite power of `R`. -/
theorem relPow_subset_of_subset_trans
    (R U : Rel A)
    (hRU : RelSubset R U)
    (hUtrans : IsTransitive U) :
    ∀ n : Nat, RelSubset (relPow R n) U := by
  sorry

/-- Therefore reachability is the transitive closure of `R`. -/
theorem reachable_isTransitiveClosure (R : Rel A) :
    IsTransitiveClosure R (Reachable R) := by
  sorry

/-!
## Sixth block: relation to mathlib closures

At this point, you should notice that `Reachable R` is morally the reflexive-transitive closure of `R`.
Mathlib already has closure machinery for relations. In a larger project, you would often switch to it.

The pedagogical point here is that your hand-built `Reachable` relation is not a toy.
It is a concrete recursive presentation of the same idea.

A good next exercise, once you are comfortable, is to identify the relevant mathlib closure object
and prove equivalence with `Reachable R`.

We do not do that here, because the goal is to keep the recursive and path-length structure visible.
-/

/-!
## Seventh block: finiteness and path shortening

The original problem asks for a finite bound on path length when `A` is finite.
That statement is materially harder in Lean than in pen-and-paper mathematics.
Why?

Because in natural mathematics, you casually say:
"If a path repeats a vertex, delete the loop and obtain a shorter path."

In Lean, you must decide how paths are represented in order to formalize that argument.
The recursive `relPow` presentation is excellent for algebraic reasoning, but not ideal for
loop-erasure arguments.

For that reason, the finiteness part is best approached by introducing an explicit *list-based*
notion of chain.

This workbook now gives you a scaffold for that second encoding, without completing it.
The point is to show you how one usually bridges the two styles.
-/

/-- A list-based chain from `a` to `b` along `R`.

Interpret `ChainFromTo R a l b` as saying that `l` is the list of intermediate vertices between
`a` and `b`.

Examples:
- `ChainFromTo R a [] b` means `R a b`
- `ChainFromTo R a [x₁, x₂] b` means `R a x₁ ∧ R x₁ x₂ ∧ R x₂ b`

This is often the right representation for finiteness and loop-erasure arguments.
-/
inductive ChainFromTo (R : Rel A) : A → List A → A → Prop
  | nil  : ∀ {a b : A}, R a b → ChainFromTo R a [] b
  | cons : ∀ {a x b : A} {xs : List A},
      R a x → ChainFromTo R x xs b → ChainFromTo R a (x :: xs) b

/-- The length of the corresponding path represented by `ChainFromTo`.
If the list of intermediates has length `n`, then the path has length `n+1`.
-/
def ChainLen {R : Rel A} {a b : A} (xs : List A) : Nat := xs.length + 1

/-!
The important meta-point is this:
- `relPow` is better for recursive-algebraic proofs
- `ChainFromTo` is better for explicit path combinatorics

In serious formalization work, it is common to prove translation lemmas in both directions.
-/

/-- A chain gives a nonzero relation power. -/
theorem chain_gives_relPow (R : Rel A) :
    ∀ {a b : A} {xs : List A}, ChainFromTo R a xs b → relPow R (xs.length + 1) a b := by
  sorry

/-- Conversely, a nonzero relation power should give an explicit chain.
This is a good induction exercise on `n`.
-/
theorem relPow_succ_gives_chain (R : Rel A) :
    ∀ {n : Nat} {a b : A}, relPow R (n + 1) a b →
      ∃ xs : List A, xs.length = n ∧ ChainFromTo R a xs b := by
  sorry

/-!
## Finiteness challenge scaffold

A mathematically natural target is:
if `A` is finite and `a` reaches `b`, then there is a path from `a` to `b`
that does not repeat vertices, hence has bounded length.

In Lean, one plausible route is:
1. convert reachability to a list-based chain
2. define what it means for the chain to have no repeated vertices
3. prove a loop-erasure lemma
4. conclude the chain length is bounded by the size of the finite type

This is a substantial formalization exercise. The workbook leaves you the structure,
but not the solution.
-/

section FinitePart

variable [Fintype A]

/-- A possible bound on simple path length in a finite type.
You may want `Fintype.card A`, or perhaps `Fintype.card A - 1`, depending on your exact conventions.
Do not trust the bound until you have checked the indexing carefully.
-/
def pathLengthBound : Nat := Fintype.card A

/-- Placeholder definition for a chain with no repeated intermediate vertices.
You will probably want to refine this by also preventing repetition of endpoints inside the list.
-/
def ChainNoRepeats {R : Rel A} {a b : A} (xs : List A) : Prop :=
  xs.Nodup

/-- Main finite-path challenge.
This is intentionally stated in a rough form. You should inspect whether the bound and hypotheses
need sharpening once you choose your exact chain representation.
-/
theorem finite_reachable_has_bounded_chain
    (R : Rel A) {a b : A} (h : Reachable R a b) :
    ∃ n ≤ pathLengthBound (A := A), relPow R n a b := by
  sorry

end FinitePart

/-!
## Final block: concrete examples

The exercise ends by asking you to compute powers, reachability, mutual reachability,
strong components, and strong connectedness for concrete finite relations.

In Lean, the best way to do these examples is usually:
- define a small inductive type for the vertices, or use `Fin n`
- define the relation by cases
- prove the desired facts by case analysis and simplification

That part is omitted here because the main goal of this workbook is the abstract infrastructure.
But once this file is working, adding examples is the right next step.
-/

/-!
# Suggested work order

1. Prove `relPow_two_iff`.
2. Prove `relPow_add`.
3. Complete the equivalence-relation proofs for mutual reachability.
4. Prove `relPow_subset_of_subset_trans`.
5. Conclude `reachable_isTransitiveClosure`.
6. Work on the list-based chain translation lemmas.
7. Only then attempt the finite bound theorem.

That order mirrors the actual dependency structure.
-/

end Workbook5
