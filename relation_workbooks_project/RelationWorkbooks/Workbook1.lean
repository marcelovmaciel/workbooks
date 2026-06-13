/-
Workbook 1
Type theoretic encoding of binary relations.

This file is a workbook, not a solved sheet.
You should replace each `by sorry` with a proof.
-/
import Mathlib.Tactic.Push
import Mathlib.Tactic.Use
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

universe u



namespace RelationWorkbook1

abbrev Rel (α : Type u) := α → α → Prop

variable {α : Type u}

def converse (R : Rel α) : Rel α := fun a b => R b a
def inter (R S : Rel α) : Rel α := fun a b => R a b ∧ S a b
def union (R S : Rel α) : Rel α := fun a b => R a b ∨ S a b
def comp (R S : Rel α) : Rel α := fun a c => ∃ b, R a b ∧ S b c
def emptyRel : Rel α := fun _ _ => False
def fullRel : Rel α := fun _ _ => True

def Reflexive (R : Rel α) : Prop := ∀ a, R a a
def Irreflexive (R : Rel α) : Prop := ∀ a, ¬ R a a
def Symmetric (R : Rel α) : Prop := ∀ ⦃a b⦄, R a b → R b a
def Asymmetric (R : Rel α) : Prop := ∀ ⦃a b⦄, R a b → ¬ R b a
def Antisymmetric (R : Rel α) : Prop := ∀ ⦃a b⦄, R a b → R b a → a = b
def Transitive (R : Rel α) : Prop := ∀ ⦃a b c⦄, R a b → R b c → R a c
def NegTransitive (R : Rel α) : Prop := ∀ ⦃a b c⦄, ¬ R a b → ¬ R b c → ¬ R a c

theorem ex1a_reflexive_converse_iff (R : Rel α) :
    Reflexive (converse R) ↔ Reflexive R := by
    constructor
    ·
     intro  h a
     specialize h a
     unfold converse at h
     exact h
    ·
      intro h a
      unfold converse
      exact h a

theorem ex1b_irreflexive_converse_iff (R : Rel α) :
    Irreflexive (converse R) ↔ Irreflexive R := by
    constructor
    ·
        intro  h a
        specialize h a
        unfold converse at h
        exact h
    ·
        intro h a
        unfold converse
        exact h a



theorem ex1c_symmetric_converse_iff (R : Rel α) :
    Symmetric (converse R) ↔ Symmetric R := by
  constructor <;> intro h a b hab <;> exact h hab

theorem ex1d_asymmetric_converse_iff (R : Rel α) :
    Asymmetric (converse R) ↔ Asymmetric R := by
    constructor <;> intro h a b hab <;> exact h hab

theorem ex1e_antisymmetric_converse_iff (R : Rel α) :
    Antisymmetric (converse R) ↔ Antisymmetric R := by
    constructor <;> intro h a b hab <;> specialize h hab
    ·

        unfold converse at h
        intro hab'
        specialize h hab'
        exact h.symm
    ·

        intro hab'
        specialize h hab'
        exact h.symm



theorem ex1f_transitive_converse_iff (R : Rel α) :
    Transitive (converse R) ↔ Transitive R := by
    constructor <;> intro h a b c hab hbc
    ·
        have hRba := h hbc hab
        unfold converse at hRba
        exact hRba
    ·
        unfold converse at *
        exact h hbc hab


theorem ex1g_negTransitive_converse_iff (R : Rel α) :
    NegTransitive (converse R) ↔ NegTransitive R := by
    constructor <;> intro h a b c hab hbc
    ·
        have hRba := h hbc hab
        unfold converse at hRba
        exact hRba
    ·
        unfold converse at *
        exact h hbc hab


theorem ex2a_inter_reflexive {R S : Rel α} :
    Reflexive R → Reflexive S → Reflexive (inter R S) := by
    intro hR hS a
    unfold inter
    exact ⟨hR a, hS a⟩

theorem ex2b_inter_irreflexive {R S : Rel α} :
    Irreflexive R → Irreflexive S → Irreflexive (inter R S) := by
    intro hR hS a
    unfold inter
    intro h
    exact hR a h.1

theorem ex2c_inter_symmetric {R S : Rel α} :
    Symmetric R → Symmetric S → Symmetric (inter R S) := by
    intro hR hS a b hab
    unfold inter at *
    exact ⟨hR hab.1, hS hab.2⟩

theorem ex2d_inter_asymmetric {R S : Rel α} :
    Asymmetric R → Asymmetric S → Asymmetric (inter R S) := by
    intro hR hS a b hab
    unfold inter at *
    intro hba
    exact hR hab.1 hba.1
theorem ex2e_inter_antisymmetric {R S : Rel α} :
    Antisymmetric R → Antisymmetric S → Antisymmetric (inter R S) := by
    intro hR hS a b hab andRS
    specialize hR andRS.1
    exact (hR  hab.1).symm

theorem ex2f_inter_transitive {R S : Rel α} :
    Transitive R → Transitive S → Transitive (inter R S) := by
    intro hR hS a b c hab hbc
    unfold inter at *
    exact ⟨hR hab.1 hbc.1, hS hab.2 hbc.2⟩

theorem ex2g_inter_negTransitive_counterexample :
  ∃ (R S : Rel (Fin 3)),
    NegTransitive R ∧
    NegTransitive S ∧
    ¬ NegTransitive (inter R S) := by
    let a : Fin 3 := 0
    let b : Fin 3 := 1
    let c : Fin 3 := 2
    let R : Rel (Fin 3) := fun x y => (x = a ∧ y = b) ∨ (x = a ∧ y = c)
    let S : Rel (Fin 3) := fun x y => (x = b ∧ y = c) ∨ (x = a ∧ y = c)
    have hR : NegTransitive R := by
        intro x y z hRxy hRyz
        fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [R, a, b, c] at *
    have hS : NegTransitive S := by
        intro x y z hSxy hSyz
        fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [S, a, b, c] at *
    have hInter : ¬ NegTransitive (inter R S) := by
        intro h
        have hab : ¬ inter R S a b := by
            simp [inter, R, S, a, b, c]
        have hbc : ¬ inter R S b c := by
            simp [inter, R, S, a, b, c]
        have hac : inter R S a c := by
            simp [inter, R, S, a, b, c]
        exact h hab hbc hac
    exact ⟨R, S, hR, hS, hInter⟩


theorem ex3b_union_irreflexive {R S : Rel α} :
    Irreflexive R → Irreflexive S → Irreflexive (union R S) := by
    intro hR hS a h
    rcases h with hRaa | hSaa
    ·
        exact hR a hRaa
    ·
        exact hS a hSaa




theorem ex3c_union_symmetric {R S : Rel α} :
    Symmetric R → Symmetric S → Symmetric (union R S) := by
    intro hR hS a b hab
    unfold union
    rcases hab with hRab | hSab
    ·
        exact Or.inl (hR hRab)
    ·
        exact Or.inr (hS hSab)

theorem ex3d_union_asymmetric :
  ∃ (R S : Rel (Fin 2)),
    Asymmetric R ∧ Asymmetric S ∧ ¬ Asymmetric (union R S) := by
    let R : Rel (Fin 2) := fun x y => (x = 0 ∧ y = 1)
    let S : Rel (Fin 2) := fun x y => (x = 1 ∧ y = 0)
    have hR : Asymmetric R := by
        intro x y hRxy
        fin_cases x <;> fin_cases y <;> simp [R] at *
    have hS : Asymmetric S := by
        intro x y hSxy
        fin_cases x <;> fin_cases y <;> simp [S] at *
    have hNotAsymm : ¬ Asymmetric (union R S) := by
        intro hAsymm
        have h01 : union R S 0 1 := by
            exact Or.inl ⟨rfl, rfl⟩
        have h10 : union R S 1 0 := by
            exact Or.inr ⟨rfl, rfl⟩
        exact hAsymm h01 h10
    exact ⟨R, S, hR, hS, hNotAsymm⟩











theorem ex3e_union_antisymmetric :
  ∃ (R S : Rel (Fin 2)),
    Antisymmetric R ∧ Antisymmetric S ∧ ¬ Antisymmetric (union R S) := by
    let R : Rel (Fin 2) := fun x y => x = 0 ∧ y = 1
    let S : Rel (Fin 2) := fun x y => x = 1 ∧ y = 0

    have hR : Antisymmetric R := by
        intro x y hxy hyx
        rcases hxy with ⟨rfl, rfl⟩
        simp [R] at hyx

    have hS : Antisymmetric S := by
        intro x y hxy hyx
        rcases hxy with ⟨rfl, rfl⟩
        simp [S] at hyx

    have hNotAntisymm : ¬ Antisymmetric (union R S) := by
        intro hAnti
        have h01 : union R S 0 1 := by
            exact Or.inl ⟨rfl, rfl⟩
        have h10 : union R S 1 0 := by
            exact Or.inr ⟨rfl, rfl⟩
        have hEq : (0 : Fin 2) = 1 := hAnti h01 h10
        norm_num at hEq

    exact ⟨R, S, hR, hS, hNotAntisymm⟩

theorem ex3f_union_transitive :
  ∃ (R S : Rel (Fin 3)),
    Transitive R ∧ Transitive S ∧ ¬ Transitive (union R S) := by
    let R : Rel (Fin 3) := fun x y => x = 0 ∧ y = 1
    let S : Rel (Fin 3) := fun x y => x = 1 ∧ y = 2

    have hR : Transitive R := by
        intro x y z hxy hyz
        fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [R] at *

    have hS : Transitive S := by
        intro x y z hxy hyz
        fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [S] at *

    have hNotTrans : ¬ Transitive (union R S) := by
        intro hTrans
        have h01 : union R S 0 1 := by
            exact Or.inl ⟨rfl, rfl⟩
        have h12 : union R S 1 2 := by
            exact Or.inr ⟨rfl, rfl⟩
        have h02 : union R S 0 2 := hTrans h01 h12
        rcases h02 with hR02 | hS02
        ·
            simp [R] at hR02
        ·
            simp [S] at hS02

    exact ⟨R, S, hR, hS, hNotTrans⟩

theorem ex3g_union_negTransitive {R S : Rel α} :
    NegTransitive R → NegTransitive S → NegTransitive (union R S) := by
    intro hR hS a b c hab hbc
    unfold union at *
    push Not at *
    exact  ⟨ hR hab.left hbc.left, hS hab.right hbc.right⟩


theorem ex4a_comp_reflexive {R S : Rel α} :
    Reflexive R → Reflexive S → Reflexive (comp R S) := by
    intro hR hS a
    unfold comp
    use a
    exact ⟨hR a, hS a⟩


theorem ex4b_comp_irreflexive {R S : Rel α} :
    Irreflexive R → Irreflexive S → Irreflexive (comp R S) := by
    intro hR hS a h
    rcases h with ⟨a, hRab, hSbc⟩

theorem ex4c_comp_symmetric {R S : Rel α} :
    Symmetric R → Symmetric S → Symmetric (comp R S) := by sorry
theorem ex4d_comp_asymmetric {R S : Rel α} :
    Asymmetric R → Asymmetric S → Asymmetric (comp R S) := by sorry
theorem ex4e_comp_antisymmetric {R S : Rel α} :
    Antisymmetric R → Antisymmetric S → Antisymmetric (comp R S) := by sorry
theorem ex4f_comp_transitive {R S : Rel α} :
    Transitive R → Transitive S → Transitive (comp R S) := by sorry
theorem ex4g_comp_negTransitive {R S : Rel α} :
    NegTransitive R → NegTransitive S → NegTransitive (comp R S) := by sorry

theorem ex5a_empty_reflexive [Nonempty α] : ¬ Reflexive (@emptyRel α) := by

    unfold Reflexive emptyRel
    push Not
    rcases ‹Nonempty α› with ⟨a⟩ -- TODO, study this notation!
    use a





theorem ex5b_empty_irreflexive : Irreflexive (@emptyRel α) := by
    unfold Irreflexive emptyRel
    intro a h
    exact h
theorem ex5c_empty_symmetric : Symmetric (@emptyRel α) := by
    unfold Symmetric emptyRel
    intro a b h
    exact h
theorem ex5d_empty_asymmetric : Asymmetric (@emptyRel α) := by sorry


theorem ex5e_empty_antisymmetric : Antisymmetric (@emptyRel α) := by sorry
theorem ex5f_empty_transitive : Transitive (@emptyRel α) := by sorry
theorem ex5g_empty_negTransitive : NegTransitive (@emptyRel α) := by sorry

theorem ex6a_full_reflexive : Reflexive (@fullRel α) := by sorry
theorem ex6b_full_irreflexive : Irreflexive (@fullRel α) := by sorry
theorem ex6c_full_symmetric : Symmetric (@fullRel α) := by sorry
theorem ex6d_full_asymmetric : Asymmetric (@fullRel α) := by sorry
theorem ex6e_full_antisymmetric : Antisymmetric (@fullRel α) := by sorry
theorem ex6f_full_transitive : Transitive (@fullRel α) := by sorry
theorem ex6g_full_negTransitive : NegTransitive (@fullRel α) := by sorry

end RelationWorkbook1
