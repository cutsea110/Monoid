module Monoid where

open import Data.Product
open import Function using (_∘_; const)
open import Relation.Binary.PropositionalEquality as PropEq


Op₁ : (A : Set) → Set
Op₁ A = A → A
Op₂ : (A : Set) → Set
Op₂ A = A → A → A

Associativity : ∀ {A : Set} → (_⊕_ : Op₂ A) → Set
Associativity _⊕_ = ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
Left-Identity : ∀ {A : Set} → (_⊕_ : Op₂ A) →  (ε : A) → Set
Left-Identity _⊕_ ε = ∀ x → ε ⊕ x ≡ x
Right-Identity : ∀ {A : Set} → (_⊕_ : Op₂ A) →  (ε : A) → Set
Right-Identity _⊕_ ε = ∀ x → x ⊕ ε ≡ x
Identity : ∀ {A : Set} → (_⊕_ : Op₂ A) →  (ε : A) → Set
Identity _⊕_ ε = Left-Identity _⊕_ ε × Right-Identity _⊕_ ε

record IsSemiGroup {A : Set}(_∙_ : Op₂ A) : Set where
  field
    ∙-assoc : Associativity _∙_

record IsMonoid {A : Set} (_∙_ : Op₂ A) (ε : A) : Set where
  field
    isSemigroup : IsSemiGroup _∙_
    identity : Identity _∙_ ε

record Dual (A : Set) : Set where
  constructor dual
  field
    getDual : A

⇄ : ∀ {A : Set} → Op₂ A → Op₂ (Dual A)
⇄ _⊕_ (dual x) (dual y) = dual (y ⊕ x)

record Endo (A : Set) : Set where
  constructor endo
  field
    appEndo : Op₁ A

_∙_ : ∀ {A : Set} → Op₂ (Endo A)
endo f ∙ endo g = endo (f ∘ g)

postulate
  extentionality : ∀ {a b} → PropEq.Extensionality a b

Arrow : (A B : Set) → Set
Arrow A B = A → B

↦ : ∀ {A B} → Op₂ B → Op₂ (Arrow A B)
↦ _⊕_ f g x = f x ⊕ g x

_|><|_ : {A B : Set} → Op₂ A → Op₂ B → Op₂ (A × B)
_|><|_ _⊕_ _⊗_ (fst₁ , snd₁) (fst₂ , snd₂) = fst₁ ⊕ fst₂ , snd₁ ⊗ snd₂
