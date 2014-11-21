module Endo where

open import Data.Nat
open import Data.Product
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as Eq

record IsSemiGroup {A : Set} (_∙_ : A → A → A) : Set where
  field
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

ℕ+-isSemigroup : IsSemiGroup _+_
ℕ+-isSemigroup = record { assoc = +-assoc }
  where
    +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +-assoc zero y z = refl
    +-assoc (suc x) y z = cong suc (+-assoc x y z)

record IsMonoid {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isSemigroup : IsSemiGroup _∙_
    identity    : (∀ x → ε ∙ x ≡ x) × (∀ x → x ∙ ε ≡ x)

  open IsSemiGroup isSemigroup public

ℕ+0-isMonoid : IsMonoid _+_ 0
ℕ+0-isMonoid = record { isSemigroup = ℕ+-isSemigroup ; identity = (λ x → refl) , n+0≡n }
  where
    n+0≡n : ∀ n → n + 0 ≡ n
    n+0≡n zero = refl
    n+0≡n (suc n) = cong suc (n+0≡n n)

record Endo (A : Set) : Set where
  constructor endo
  field
    appEndo : A → A

_∙_ : {A : Set} → Endo A → Endo A → Endo A
f ∙ g = endo (appEndo f ∘ appEndo g) where open Endo

endo-assoc : {A : Set} → (f g h : Endo A) → (f ∙ g) ∙ h ≡ f ∙ (g ∙ h)
endo-assoc (endo appEndo) (endo appEndo₁) (endo appEndo₂) = refl

Endo-isSemigroup : {A : Set} → IsSemiGroup {Endo A} _∙_
Endo-isSemigroup = record { assoc = endo-assoc }

endo-identity : ∀ {A} → ((x : Endo A) → (endo id) ∙ x ≡ x) × ((x : Endo A) → x ∙ (endo id) ≡ x)
endo-identity = (λ x → refl) , (λ x → refl)

Endo-isMonoid : {A : Set} → IsMonoid {Endo A} _∙_ (endo id)
Endo-isMonoid = record { isSemigroup = Endo-isSemigroup ; identity = endo-identity }
