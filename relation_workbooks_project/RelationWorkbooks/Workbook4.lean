import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Push
/-
Workbook 4

Tema:
diferença entre começar com uma preferência fraca primitiva
e começar com uma preferência estrita primitiva.

Extensão desta versão:
separamos cuidadosamente o que vale

- intuicionisticamente
- com decidibilidade local
- classicamente

IMPORTANTE:
este é um workbook. Os teoremas estão com `sorry`.
Os comentários indicam o que tentar, mas não resolvem por você.
-/

universe u

namespace RelationWorkbook4

variable {α : Type u}

/-!
## Parte 0. Relações básicas
-/

/-- Relação binária em estilo idiomático Lean. -/
abbrev Rel (α : Type u) := α → α → Prop

/-- Conversa de uma relação. -/
def converse (R : Rel α) : Rel α :=
  Function.swap R

/-- União de relações. -/
def union (R S : Rel α) : Rel α :=
  fun a b => R a b ∨ S a b

/-- Interseção de relações. -/
def inter (R S : Rel α) : Rel α :=
  fun a b => R a b ∧ S a b

/--
Complemento simétrico.

`a (symmCompl R) b` significa:
nem `aRb`, nem `bRa`.
-/
def symmCompl (R : Rel α) : Rel α :=
  fun a b => ¬ R a b ∧ ¬ R b a

/--
Comparabilidade efetiva em algum sentido.
-/
def comparable (R : Rel α) : Rel α :=
  union R (converse R)

/--
Não não-comparabilidade.

Isto é a expansão intuicionisticamente correta de
`symmCompl (symmCompl R)`.
-/
def nnComparable (R : Rel α) : Rel α :=
  fun a b => ¬ (¬ R a b ∧ ¬ R b a)

/-!
## Parte I. O que vale intuicionisticamente
-/

/--
O complemento simétrico é sempre simétrico.

Tática sugerida:
`intro`, depois trocar as componentes do par.
-/
theorem symmCompl_symmetric {α : Type u} (R : Rel α) :
    Symmetric (symmCompl R) := by
    intro a b h
    dsimp [symmCompl] at *
    exact ⟨h.2, h.1⟩

/--
Expansão correta do duplo complemento simétrico.

Moral:
construtivamente, o duplo complemento simétrico dá
`nnComparable`, não `comparable`.
-/
theorem symmCompl_symmCompl_iff_nnComparable (R : Rel α) :
    ∀ a b, symmCompl (symmCompl R) a b ↔ nnComparable R a b := by
  intro a b
  constructor
  · intro h
    dsimp [symmCompl] at h
    exact h.1
  · intro h
    dsimp [symmCompl]
    constructor
    · intro hab
      dsimp [nnComparable] at h
      contradiction
    · intro hba
      dsimp [nnComparable] at h
      -- aqui 'e so flip hba dado que A ∧ B 'e o mesmo que B ∧ A
      have hab : ¬ R a b ∧ ¬ R b a := ⟨hba.2, hba.1⟩
      contradiction


/--
Comparabilidade efetiva implica não não-comparabilidade.

Este é o lado construtivamente válido.
A recíproca é o ponto onde a lógica clássica entra.
-/
theorem comparable_imp_nnComparable (R : Rel α) :
    ∀ a b, comparable R a b → nnComparable R a b := by
  intro a b h
  dsimp [comparable] at h
  dsimp [nnComparable]
  intro h2
  dsimp [union] at h
  cases h with
  | inl hab =>
    have hnab := h2.1
    contradiction
  | inr hba =>
    have hnba := h2.2
    contradiction
/--
Versão equivalente via duplo complemento simétrico.

-/
theorem comparable_imp_symmCompl_symmCompl (R : Rel α) :
    ∀ a b, comparable R a b → symmCompl (symmCompl R) a b := by
  intro a b hcomp
  dsimp [comparable, union] at hcomp
  dsimp [symmCompl]
  constructor
  · intro hn_symm_ab
    obtain hab | hconv_ab := hcomp
    ·
      have hnab := hn_symm_ab.1
      contradiction
    ·
      dsimp [converse, Function.swap] at hconv_ab
      have hnba := hn_symm_ab.2
      contradiction
  · intro hn_symm_ba
    obtain hab | hconv_ab := hcomp
    ·
      have hnab := hn_symm_ba.2
      contradiction
    ·
      dsimp [converse, Function.swap] at hconv_ab
      have hnba := hn_symm_ba.1
      contradiction








/-!
## Parte II. O passo adicional: decidibilidade local
-/

/--
Sob decidibilidade local para `R a b` e `R b a`,
não não-comparabilidade implica comparabilidade efetiva.

Este é o ponto lógico delicado.
Sem essas hipóteses, não tente provar isso intuicionisticamente.
-/
theorem nnComparable_imp_comparable_of_decidable
    (R : Rel α)
    (a b : α)
    [Decidable (R a b)] [Decidable (R b a)] :
    nnComparable R a b → comparable R a b := by
  intro h
  dsimp [nnComparable] at h
  dsimp [comparable, union, converse, Function.swap]
  by_cases hab : R a b
  · exact Or.inl hab
  · by_cases hba : R b a
    · exact Or.inr hba
    · exact False.elim (h ⟨hab, hba⟩)
/--
Sob decidibilidade local, o duplo complemento simétrico
vira comparabilidade efetiva.

Tática sugerida:
encadear os teoremas anteriores.
-/
theorem symmCompl_symmCompl_iff_comparable_of_decidable
    (R : Rel α)
    (a b : α)
    [d1 : Decidable (R a b)] [d2 : Decidable (R b a)] :
    symmCompl (symmCompl R) a b ↔ comparable R a b := by
  constructor
  intro h

  obtain n | y := d1
  obtain n' | y' := d2
  ·
   dsimp [comparable, converse, union, Function.swap]
   dsimp [symmCompl] at h
   have hnab := h.1
   have nrab_and_nrba : ¬ R a b ∧ ¬ R b a := ⟨n, n'⟩
   contradiction
  ·
    dsimp [comparable, converse, union, Function.swap]
    dsimp [symmCompl] at h
    right
    exact y'
  ·
    dsimp [comparable, converse, union, Function.swap]
    dsimp [symmCompl] at h
    left
    exact y
  ·
    dsimp [comparable, converse, union, Function.swap]
    intro  h
    dsimp [symmCompl]
    constructor
    intro n
    obtain hab | hconv_ab := h
    have hnab := n.1
    contradiction

    have hnba := n.2
    contradiction
    intro h2
    obtain hab | hconv_ab := h
    have hnab := h2.2
    contradiction
    have hnba := h2.1
    contradiction

theorem symmCompl_symmCompl_iff_comparable_of_decidable'
    (R : Rel α)
    (a b : α)
    [Decidable (R a b)] [Decidable (R b a)] :
    symmCompl (symmCompl R) a b ↔ comparable R a b := by
  constructor
  · intro h
    exact nnComparable_imp_comparable_of_decidable R a b
      ((symmCompl_symmCompl_iff_nnComparable R a b).1 h)
  · intro h
    exact comparable_imp_symmCompl_symmCompl R a b h





/-!
## Parte III. Começando com uma preferência fraca primitiva
-/

variable (W : Rel α)


def strictFromWeak : Rel α :=
  fun a b => W a b ∧ ¬ W b a

/-- Indiferença derivada de `W`. -/
def indiffFromWeak : Rel α :=
  fun a b => W a b ∧ W b a

/-- Incomparabilidade derivada de `W`. -/
def incomparFromWeak : Rel α :=
  fun a b => ¬ W a b ∧ ¬ W b a

/-- Comparabilidade fraca efetiva. -/
def weakComparable : Rel α :=
  fun a b => W a b ∨ W b a

/-- Não não-incomparabilidade fraca. -/
def nnWeakComparable : Rel α :=
  fun a b => ¬ (¬ W a b ∧ ¬ W b a)

/--
A incomparabilidade derivada de `W` é, definicionalmente,
o complemento simétrico de `W`.


-/
theorem incomparFromWeak_iff_symmCompl_weak :
    ∀ a b, incomparFromWeak W a b ↔ symmCompl W a b := by
  intro a b
  rfl


/--
Sob decidibilidade local, o complemento simétrico do estrito derivado
é indiferença OU incomparabilidade.

-/
theorem symmCompl_strictFromWeak_iff_indiff_or_incompar_of_decidable'
    (a b : α)
    [Decidable (W a b)] [Decidable (W b a)] :
    symmCompl (strictFromWeak W) a b ↔
    union (indiffFromWeak W) (incomparFromWeak W) a b := by
  dsimp [symmCompl, strictFromWeak, indiffFromWeak, incomparFromWeak, union]
  by_cases hab : W a b <;> by_cases hba : W b a <;> simp [hab, hba]

/--
Completude de uma relação fraca.
-/
def Complete (R : Rel α) : Prop :=
  ∀ a b, R a b ∨ R b a

theorem incomparFromWeak_empty_if_complete
    (hW : Complete W) :
    ∀ a b, ¬ incomparFromWeak W a b := by
  intro a b h
  dsimp [incomparFromWeak] at h
  have hcomp := hW a b
  cases hcomp with
  | inl hab =>
    have hnab := h.1
    contradiction
  | inr hba =>
    have hnba := h.2
    contradiction

/--
Sob completude e decidibilidade local, o complemento simétrico
do estrito derivado vira exatamente a indiferença.

Estratégia sugerida:
primeiro use o teorema que dá `I ∪ J`.
Depois elimine `J` com o teorema de vacuidade de incomparabilidade.
A volta é por `Or.inl`.

Esta prova é conceitualmente importante:
ela formaliza que, quando a relação fraca é completa,
a zona residual do estrito deixa de misturar indiferença com incomparabilidade.
-/
theorem symmCompl_strictFromWeak_iff_indiff_if_complete_of_decidable
    (hW : Complete W)
    (a b : α)
    [Decidable (W a b)] [Decidable (W b a)] :
    symmCompl (strictFromWeak W) a b ↔ indiffFromWeak W a b := by
  by_cases hab : W a b <;> by_cases hba : W b a <;> dsimp [symmCompl,
   strictFromWeak, indiffFromWeak, incomparFromWeak, union] at * <;> simp [hab, hba]
  have hcomp := hW a b
  cases hcomp with
  | inl hab =>
    contradiction
  | inr hba =>
    contradiction




/-!
## Parte IV. Começando com uma preferência estrita primitiva
-/

variable (P : Rel α)

/--
Zona residual quando só o estrito é primitivo.

Leitura:
isto pode misturar indiferença com incomparabilidade,
porque a estrutura que as distinguiria não foi dada.
-/
def neutralFromStrict : Rel α :=
  symmCompl P

/-- Comparabilidade estrita efetiva. -/
def strictComparability : Rel α :=
  comparable P

/-- Não não-comparabilidade estrita. -/
def nnStrictComparability : Rel α :=
  nnComparable P

/--
Expansão da definição de `neutralFromStrict`.

Tática sugerida:
`rfl`.
-/
theorem neutralFromStrict_iff :
    ∀ a b, neutralFromStrict P a b ↔ (¬ P a b ∧ ¬ P b a) := by
  sorry

/--
Expansão da definição de comparabilidade estrita.

Tática sugerida:
`intro`, `unfold`, `rfl`.
-/
theorem strictComparability_iff :
    ∀ a b, strictComparability P a b ↔ (P a b ∨ P b a) := by
  sorry

/--
Expansão da definição de não não-comparabilidade estrita.

Tática sugerida:
`rfl`.
-/
theorem nnStrictComparability_iff :
    ∀ a b, nnStrictComparability P a b ↔ ¬ (¬ P a b ∧ ¬ P b a) := by
  sorry

/--
Construtivamente, o duplo complemento simétrico do estrito primitivo
dá não não-comparabilidade estrita.

Tática sugerida:
apenas `unfold` e use o teorema geral da Parte I.
-/
theorem symmCompl_neutralFromStrict_iff_nnStrictComparability :
    ∀ a b,
      symmCompl (neutralFromStrict P) a b ↔ nnStrictComparability P a b := by
  sorry

/--
Sob decidibilidade local, o duplo complemento simétrico
vira comparabilidade estrita efetiva.

Tática sugerida:
aplique o teorema geral da Parte II.
-/
theorem symmCompl_neutralFromStrict_iff_strictComparability_of_decidable
    (a b : α)
    [Decidable (P a b)] [Decidable (P b a)] :
    symmCompl (neutralFromStrict P) a b ↔ strictComparability P a b := by
  sorry

/-!
## Parte V. Exercícios de leitura conceitual
-/

/-
Exercício de leitura 1.
Explique em palavras a diferença entre:

- `comparable R a b`
- `nnComparable R a b`

e por que elas colapsam classicamente, mas não intuicionisticamente.
-/

/-
Exercício de leitura 2.
Explique por que começar com `W` como primitiva
permite distinguir `indiffFromWeak W` e `incomparFromWeak W`,
enquanto começar apenas com `P` como primitiva
faz `neutralFromStrict P` colapsar essas duas ideias.
-/

/-
Exercício de leitura 3.
Explique por que o teorema

  symmCompl_strictFromWeak_iff_indiff_or_incompar_of_decidable

precisa de decidibilidade local.
A resposta esperada deve mencionar a análise em quatro casos:
`W a b` / `¬ W a b` e `W b a` / `¬ W b a`.
-/

/-
Exercício de leitura 4.
Explique por que

  symmCompl (symmCompl P)

não recupera a orientação original de `P`,
mesmo quando decidibilidade permite identificá-lo com comparabilidade.
-/

end RelationWorkbook4
