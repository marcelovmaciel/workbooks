import Mathlib.Logic.Relation

/-
Workbook 3
Idiomatic mathlib-style workbook for binary relations.

This is still the unbundled representation:
  R : α → α → Prop

But now the surrounding presentation is closer to mathlib idiom:
relations are plain predicates, and many standard relation properties are
already available in the core/Mathlib ecosystem.
-/

universe u

namespace RelationWorkbook3

variable {α : Type u}

abbrev Relation (α : Type u) := α → α → Prop

/-
Textbook:
  (A, R) with R ⊆ A × A

Lean:
  fix a type α
  let R : α → α → Prop

The carrier set A is handled by the ambient type.
The relation itself is a predicate.
-/

def converse (R : Relation α) : Relation α := Function.swap R
def inter (R S : Relation α) : Relation α := fun a b => R a b ∧ S a b
def union (R S : Relation α) : Relation α := fun a b => R a b ∨ S a b
def comp (R S : Relation α) : Relation α := fun a c => ∃ b, R a b ∧ S b c
def emptyRel : Relation α := fun _ _ => False
def fullRel : Relation α := fun _ _ => True

def Reflexive (R : Relation α) : Prop := ∀ a, R a a
def Irreflexive (R : Relation α) : Prop := ∀ a, ¬ R a a
def Symmetric (R : Relation α) : Prop := ∀ ⦃a b⦄, R a b → R b a
def Asymmetric (R : Relation α) : Prop := ∀ ⦃a b⦄, R a b → ¬ R b a
def Antisymmetric (R : Relation α) : Prop := ∀ ⦃a b⦄, R a b → R b a → a = b
def Transitive (R : Relation α) : Prop := ∀ ⦃a b c⦄, R a b → R b c → R a c
def NegTransitive (R : Relation α) : Prop := ∀ ⦃a b c⦄, ¬ R a b → ¬ R b c → ¬ R a c

theorem ex1a_reflexive_converse_iff (R : Relation α) :
    Reflexive (converse R) ↔ Reflexive R := by
  sorry

theorem ex1b_irreflexive_converse_iff (R : Relation α) :
    Irreflexive (converse R) ↔ Irreflexive R := by
  sorry

theorem ex1c_symmetric_converse_iff (R : Relation α) :
    Symmetric (converse R) ↔ Symmetric R := by
  sorry

theorem ex1d_asymmetric_converse_iff (R : Relation α) :
    Asymmetric (converse R) ↔ Asymmetric R := by
  sorry

theorem ex1e_antisymmetric_converse_iff (R : Relation α) :
    Antisymmetric (converse R) ↔ Antisymmetric R := by
  sorry

theorem ex1f_transitive_converse_iff (R : Relation α) :
    Transitive (converse R) ↔ Transitive R := by
  sorry

theorem ex1g_negTransitive_converse_iff (R : Relation α) :
    NegTransitive (converse R) ↔ NegTransitive R := by
  sorry

theorem ex2a_inter_reflexive {R S : Relation α} :
    Reflexive R → Reflexive S → Reflexive (inter R S) := by
  sorry

theorem ex2b_inter_irreflexive {R S : Relation α} :
    Irreflexive R → Irreflexive S → Irreflexive (inter R S) := by
  sorry

theorem ex2c_inter_symmetric {R S : Relation α} :
    Symmetric R → Symmetric S → Symmetric (inter R S) := by
  sorry

theorem ex2d_inter_asymmetric {R S : Relation α} :
    Asymmetric R → Asymmetric S → Asymmetric (inter R S) := by
  sorry

theorem ex2e_inter_antisymmetric {R S : Relation α} :
    Antisymmetric R → Antisymmetric S → Antisymmetric (inter R S) := by
  sorry

theorem ex2f_inter_transitive {R S : Relation α} :
    Transitive R → Transitive S → Transitive (inter R S) := by
  sorry

theorem ex2g_inter_negTransitive {R S : Relation α} :
    NegTransitive R → NegTransitive S → NegTransitive (inter R S) := by
  sorry

theorem ex3a_union_reflexive {R S : Relation α} :
    Reflexive R → Reflexive S → Reflexive (union R S) := by
  sorry

theorem ex3b_union_irreflexive {R S : Relation α} :
    Irreflexive R → Irreflexive S → Irreflexive (union R S) := by
  sorry

theorem ex3c_union_symmetric {R S : Relation α} :
    Symmetric R → Symmetric S → Symmetric (union R S) := by
  sorry

theorem ex3d_union_asymmetric {R S : Relation α} :
    Asymmetric R → Asymmetric S → Asymmetric (union R S) := by
  sorry

theorem ex3e_union_antisymmetric {R S : Relation α} :
    Antisymmetric R → Antisymmetric S → Antisymmetric (union R S) := by
  sorry

theorem ex3f_union_transitive {R S : Relation α} :
    Transitive R → Transitive S → Transitive (union R S) := by
  sorry

theorem ex3g_union_negTransitive {R S : Relation α} :
    NegTransitive R → NegTransitive S → NegTransitive (union R S) := by
  sorry

theorem ex4a_comp_reflexive {R S : Relation α} :
    Reflexive R → Reflexive S → Reflexive (comp R S) := by
  sorry

theorem ex4b_comp_irreflexive {R S : Relation α} :
    Irreflexive R → Irreflexive S → Irreflexive (comp R S) := by
  sorry

theorem ex4c_comp_symmetric {R S : Relation α} :
    Symmetric R → Symmetric S → Symmetric (comp R S) := by
  sorry

theorem ex4d_comp_asymmetric {R S : Relation α} :
    Asymmetric R → Asymmetric S → Asymmetric (comp R S) := by
  sorry

theorem ex4e_comp_antisymmetric {R S : Relation α} :
    Antisymmetric R → Antisymmetric S → Antisymmetric (comp R S) := by
  sorry

theorem ex4f_comp_transitive {R S : Relation α} :
    Transitive R → Transitive S → Transitive (comp R S) := by
  sorry

theorem ex4g_comp_negTransitive {R S : Relation α} :
    NegTransitive R → NegTransitive S → NegTransitive (comp R S) := by
  sorry

theorem ex5a_empty_reflexive : Reflexive (@emptyRel α) := by
  sorry

theorem ex5b_empty_irreflexive : Irreflexive (@emptyRel α) := by
  sorry

theorem ex5c_empty_symmetric : Symmetric (@emptyRel α) := by
  sorry

theorem ex5d_empty_asymmetric : Asymmetric (@emptyRel α) := by
  sorry

theorem ex5e_empty_antisymmetric : Antisymmetric (@emptyRel α) := by
  sorry

theorem ex5f_empty_transitive : Transitive (@emptyRel α) := by
  sorry

theorem ex5g_empty_negTransitive : NegTransitive (@emptyRel α) := by
  sorry

theorem ex6a_full_reflexive : Reflexive (@fullRel α) := by
  sorry

theorem ex6b_full_irreflexive : Irreflexive (@fullRel α) := by
  sorry

theorem ex6c_full_symmetric : Symmetric (@fullRel α) := by
  sorry

theorem ex6d_full_asymmetric : Asymmetric (@fullRel α) := by
  sorry

theorem ex6e_full_antisymmetric : Antisymmetric (@fullRel α) := by
  sorry

theorem ex6f_full_transitive : Transitive (@fullRel α) := by
  sorry

theorem ex6g_full_negTransitive : NegTransitive (@fullRel α) := by
  sorry

end RelationWorkbook3
