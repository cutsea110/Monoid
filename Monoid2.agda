module Monoid2 where

open import Data.Product
open import Function using (_∘_; id; const)
open import Relation.Binary.PropositionalEquality as PropEq

Op₂ : (A : Set) → Set
Op₂ A = A → A → A

Associativity : {A : Set} → Op₂ A → Set
Associativity _∙_ = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
Left-Identity : {A : Set} → Op₂ A → A → Set
Left-Identity _∙_ ε = ∀ x → ε ∙ x ≡ x
Right-Identity : {A : Set} → Op₂ A → A → Set
Right-Identity _∙_ ε = ∀ x → x ∙ ε ≡ x
Identity : {A : Set} → Op₂ A → A → Set
Identity _∙_ ε = Left-Identity _∙_ ε × Right-Identity _∙_ ε

record IsSemiGroup {A : Set} (_∙_ : Op₂ A) : Set where
  field
    ∙-assoc : Associativity _∙_

record IsMonoid {A : Set} (_∙_ : Op₂ A) (ε : A) : Set where
  field
    isSemigroup : IsSemiGroup _∙_
    ε-identity : Identity _∙_ ε

open import Data.Nat

ℕ+-isSemigroup : IsSemiGroup {ℕ} _+_
ℕ+-isSemigroup = record { ∙-assoc = ℕ+-assoc }
  where
    ℕ+-assoc : Associativity _+_
    ℕ+-assoc zero y z = refl
    ℕ+-assoc (suc x) y z = cong suc (ℕ+-assoc x y z)

ℕ+0-isMonoid : IsMonoid {ℕ} _+_ 0
ℕ+0-isMonoid = record { isSemigroup = ℕ+-isSemigroup ; ε-identity = 0+x≡x , x+0≡x }
  where
    0+x≡x : Left-Identity _+_ 0
    0+x≡x x = refl
    x+0≡x : Right-Identity _+_ 0
    x+0≡x zero = refl
    x+0≡x (suc x) = cong suc (x+0≡x x)

record Endo (A : Set) : Set where
  constructor endo
  field
    appEndo : A → A

_∙_ : {A : Set} → Op₂ (Endo A)
f ∙ g = endo (appEndo f ∘ appEndo g) where open Endo

Endo-isSemigroup : {A : Set} → IsSemiGroup {Endo A} _∙_
Endo-isSemigroup = record { ∙-assoc = λ x y z → refl }

Endo-isMonoid : {A : Set} → IsMonoid {Endo A} _∙_ (endo id)
Endo-isMonoid = record { isSemigroup = Endo-isSemigroup ; ε-identity = (λ x → refl) , (λ x → refl) }

record Dual (A : Set) : Set where
  constructor dual
  field
    getDual : A

⇄ : {A : Set} → Op₂ A → Op₂ (Dual A)
⇄ _⊕_ (dual x) (dual y) = dual (y ⊕ x)

Dual-isSemigroup : {A : Set}{_⊕_ : Op₂ A} → IsSemiGroup {A} _⊕_ → IsSemiGroup {Dual A} (⇄ _⊕_)
Dual-isSemigroup {_⊕_ = _⊕_} prf = record { ∙-assoc = ⇄-assoc {_⊕_ = _⊕_} (∙-assoc prf) }
  where
    open IsSemiGroup
    open Dual
    ⇄-assoc : ∀ {A} {_⊕_ : Op₂ A} → Associativity _⊕_ → Associativity (⇄ _⊕_)
    ⇄-assoc prf (dual x) (dual y) (dual z) = cong dual (sym (prf z y x))

Dual-isMonoid : {A : Set}{_⊕_ : Op₂ A}{ε : A} →
  IsMonoid {A} _⊕_ ε → IsMonoid {Dual A} (⇄ _⊕_) (dual ε)
Dual-isMonoid {_⊕_ = _⊕_} prf
  = record { isSemigroup = Dual-isSemigroup (isSemigroup prf)
           ; ε-identity = ⇄-identity {_} {_⊕_} (ε-identity prf)
           }
  where
    open IsMonoid
    open Dual
    ⇄-left-id : ∀ {A} {_⊕_ : Op₂ A} {ε : A} → Right-Identity _⊕_ ε → Left-Identity (⇄ _⊕_) (dual ε)
    ⇄-left-id prf (dual x) = cong dual (prf x)
    ⇄-right-id : ∀ {A} {_⊕_ : Op₂ A} {ε : A} → Left-Identity _⊕_ ε → Right-Identity (⇄ _⊕_) (dual ε)
    ⇄-right-id prf (dual x) = cong dual (prf x)
    ⇄-identity : ∀ {A} {_⊕_ : Op₂ A} {ε : A} → Identity _⊕_ ε → Identity (⇄ _⊕_) (dual ε)
    ⇄-identity {_⊕_ = _⊕_} prf = ⇄-left-id {_⊕_ = _⊕_} (proj₂ prf) , ⇄-right-id {_⊕_ = _⊕_} (proj₁ prf)

DualEndo-isSemigroup : {A : Set} → IsSemiGroup {Dual (Endo A)} (⇄ _∙_)
DualEndo-isSemigroup = Dual-isSemigroup Endo-isSemigroup
  
DualEndo-isMonoid : {A : Set} {_⊕_ : Op₂ A} → IsMonoid {Dual (Endo A)} (⇄ _∙_) (dual (endo id))
DualEndo-isMonoid = Dual-isMonoid Endo-isMonoid

open import Data.Maybe

¿ : {A : Set} → Op₂ A → Op₂ (Maybe A)
¿ op (just x) (just y) = just (op x y)
¿ op (just x) nothing = just x
¿ op nothing (just y) = just y
¿ op nothing nothing = nothing

Maybe-isSemigroup : {A : Set}{_⊕_ : Op₂ A} → IsSemiGroup {A} _⊕_ → IsSemiGroup {Maybe A} (¿ _⊕_)
Maybe-isSemigroup prf = record { ∙-assoc = ¿-assoc (∙-assoc prf) }
  where
    open IsSemiGroup
    ¿-assoc : ∀ {A} {_⊕_ : Op₂ A} → Associativity _⊕_ → Associativity (¿ _⊕_)
    ¿-assoc prf (just x) (just y) (just z) = cong just (prf x y z)
    ¿-assoc prf (just x) (just y) nothing = cong just refl
    ¿-assoc prf (just x) nothing (just z) = refl
    ¿-assoc prf (just x) nothing nothing = refl
    ¿-assoc prf nothing (just y) (just z) = refl
    ¿-assoc prf nothing (just y) nothing = refl
    ¿-assoc prf nothing nothing (just z) = refl
    ¿-assoc prf nothing nothing nothing = refl

Maybe-isMonoid : {A : Set} {_⊕_ : Op₂ A}{ε : A} → IsMonoid {A} _⊕_ ε → IsMonoid {Maybe A} (¿ _⊕_) nothing
Maybe-isMonoid prf
  = record { isSemigroup = Maybe-isSemigroup (isSemigroup prf)
           ; ε-identity = ¿-id (ε-identity prf)
           }
  where
    open IsMonoid
    ¿-left-id : ∀ {A} {_⊕_ : Op₂ A} {ε : A} → Left-Identity _⊕_ ε → Left-Identity (¿ _⊕_) nothing
    ¿-left-id prf (just x) = refl
    ¿-left-id prf nothing = refl
    ¿-right-id : ∀ {A} {_⊕_ : Op₂ A} {ε : A} → Right-Identity _⊕_ ε → Right-Identity (¿ _⊕_) nothing
    ¿-right-id prf (just x) = refl
    ¿-right-id prf nothing = refl
    ¿-id : ∀ {A} {_⊕_ : Op₂ A} {ε : A} → Identity _⊕_ ε → Identity (¿ _⊕_) nothing
    ¿-id prf = ¿-left-id (proj₁ prf) , ¿-right-id (proj₂ prf)

Dualℕ-isMonoid : IsMonoid {Dual ℕ} (⇄ _+_) (dual 0)
Dualℕ-isMonoid = Dual-isMonoid ℕ+0-isMonoid

DualMaybeℕ-isMonoid : IsMonoid {Dual (Maybe ℕ)} (⇄ (¿ _+_)) (dual nothing)
DualMaybeℕ-isMonoid = Dual-isMonoid (Maybe-isMonoid ℕ+0-isMonoid)

_|><|_ : {A B : Set} → Op₂ A → Op₂ B → Op₂ (A × B)
(_⊕_ |><| _⊗_) (x₁ , x₂) (y₁ , y₂) = x₁ ⊕ y₁ , x₂ ⊗ y₂

×-isSemiGroup : {A B : Set}{_⊕_ : Op₂ A}{_⊗_ : Op₂ B} →
  IsSemiGroup {A} _⊕_ → IsSemiGroup {B} _⊗_ → IsSemiGroup {A × B} (_⊕_ |><| _⊗_)
×-isSemiGroup {_⊕_ = _⊕_} {_⊗_ = _⊗_} ⊕-prf ⊗-prf
  = record { ∙-assoc = ×-assoc {_}{_}{_⊕_}{_⊗_} (∙-assoc ⊕-prf) (∙-assoc ⊗-prf) }
  where
    open IsSemiGroup
    ×-assoc : ∀ {A B} {_⊕_ : Op₂ A} {_⊗_ : Op₂ B} →
          Associativity _⊕_ → Associativity _⊗_ → Associativity (_⊕_ |><| _⊗_)
    ×-assoc ⊕-assoc ⊗-assoc (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) rewrite ⊕-assoc x₁ y₁ z₁ | ⊗-assoc x₂ y₂ z₂ = refl

×-isMonoid : {A B : Set}{_⊕_ : Op₂ A}{_⊗_ : Op₂ B}{e₁ : A}{e₂ : B} →
  IsMonoid {A} _⊕_ e₁ → IsMonoid {B} _⊗_ e₂ → IsMonoid {A × B} (_⊕_ |><| _⊗_) (e₁ , e₂)
×-isMonoid {_⊕_ = _⊕_} {_⊗_ = _⊗_} prf₁ prf₂
  = record { isSemigroup = ×-isSemiGroup (isSemigroup prf₁) (isSemigroup prf₂)
           ; ε-identity = ×-identity {_⊕_ = _⊕_} {_⊗_ = _⊗_} (ε-identity prf₁) (ε-identity prf₂)
           }
  where
    open IsMonoid
    ×-left-id : ∀ {A B} {_⊕_ : Op₂ A} {_⊗_ : Op₂ B} {e₁ : A} {e₂ : B} →
            Left-Identity _⊕_ e₁ → Left-Identity _⊗_ e₂ → Left-Identity (_⊕_ |><| _⊗_) (e₁ , e₂)
    ×-left-id prf₁ prf₂ (x₁ , x₂) rewrite prf₁ x₁ | prf₂ x₂ = refl
    ×-right-id : ∀ {A B} {_⊕_ : Op₂ A} {_⊗_ : Op₂ B} {e₁ : A} {e₂ : B} →
            Right-Identity _⊕_ e₁ → Right-Identity _⊗_ e₂ → Right-Identity (_⊕_ |><| _⊗_) (e₁ , e₂)
    ×-right-id prf₁ prf₂ (x₁ , x₂) rewrite prf₁ x₁ | prf₂ x₂ = refl
    ×-identity : ∀ {A B} {_⊕_ : Op₂ A} {_⊗_ : Op₂ B} {e₁ : A} {e₂ : B} →
             Identity _⊕_ e₁ → Identity _⊗_ e₂ → Identity (_⊕_ |><| _⊗_) (e₁ , e₂)
    ×-identity {_⊕_ = _⊕_} {_⊗_ = _⊗_} prf₁ prf₂
      = ×-left-id {_⊕_ = _⊕_} {_⊗_ = _⊗_} (proj₁ prf₁) (proj₁ prf₂)
      , ×-right-id {_⊕_ = _⊕_} {_⊗_ = _⊗_} (proj₂ prf₁) (proj₂ prf₂)


open import Data.List

[]-isSemigroup : {A : Set} → IsSemiGroup {List A} _++_
[]-isSemigroup = record { ∙-assoc = []-assoc }
  where
    open IsSemiGroup
    []-assoc : {A : Set} (x y z : List A) → (x ++ y) ++ z ≡ x ++ (y ++ z)
    []-assoc [] ys zs = refl
    []-assoc (x ∷ xs) ys zs = cong (_∷_ x) ([]-assoc xs ys zs)

[]-isMonoid : {A : Set} → IsMonoid {List A} _++_ []
[]-isMonoid = record { isSemigroup = []-isSemigroup ; ε-identity = []-identity }
  where
    open IsMonoid
    []-left-id : {A : Set} (x : List A) → [] ++ x ≡ x
    []-left-id xs = refl
    []-right-id : {A : Set} (x : List A) → x ++ [] ≡ x
    []-right-id [] = refl
    []-right-id (x ∷ xs) = cong (_∷_ x) ([]-right-id xs)
    []-identity : ∀ {A} → Identity {List A} _++_ []
    []-identity = []-left-id , []-right-id

postulate
  extensionality : ∀{a b} → PropEq.Extensionality a b

↦ : {A B : Set} → Op₂ B → Op₂ (A → B)
↦ _⊕_ f g x = f x ⊕ g x

↦-isSemiGroup : {A B : Set} {_⊕_ : Op₂ B} → IsSemiGroup {B} _⊕_ → IsSemiGroup {A → B} (↦ _⊕_) 
↦-isSemiGroup {_⊕_ = _⊕_} prf = record { ∙-assoc = ↦-assoc {_⊕_ = _⊕_} (∙-assoc prf) }
  where
    open IsSemiGroup
    ↦-assoc : ∀ {A B} {_⊕_ : Op₂ B} → Associativity _⊕_ → Associativity (↦ {A} _⊕_)
    ↦-assoc {_⊕_ = _⊕_} prf f g h = extensionality (λ x → prf (f x) (g x) (h x))

↦-isMonoid :  {A B : Set} {_⊕_ : Op₂ B} {ε : B} →
  IsMonoid {B} _⊕_ ε → IsMonoid {A → B} (↦ _⊕_) (const ε)
↦-isMonoid {_⊕_ = _⊕_} prf = record { isSemigroup = ↦-isSemiGroup (isSemigroup prf)
                         ; ε-identity = ↦-identity {_⊕_ = _⊕_} (ε-identity prf)
                         }
  where
    open IsMonoid
    ↦-left-id : ∀ {A B} {_⊕_ : Op₂ B} {ε : B} →
            Left-Identity _⊕_ ε → Left-Identity (↦ {A} _⊕_) (const ε)
    ↦-left-id prf = λ f → extensionality (λ x → prf (f x))
    ↦-right-id : ∀ {A B} {_⊕_ : Op₂ B} {ε : B} →
             Right-Identity _⊕_ ε → Right-Identity (↦ {A} _⊕_) (const ε)
    ↦-right-id prf = λ f → extensionality (λ x → prf (f x))
    ↦-identity : ∀ {A B} {_⊕_ : Op₂ B} {ε : B} →
             Identity _⊕_ ε → Identity (↦ {A} _⊕_) (const ε)
    ↦-identity {_⊕_ = _⊕_} prf
      = ↦-left-id {_⊕_ = _⊕_} (proj₁ prf) , ↦-right-id {_⊕_ = _⊕_} (proj₂ prf)

↦Dualℕ-isMonoid : {A : Set} → IsMonoid (↦ {A} (⇄ _+_)) (const (dual 0))
↦Dualℕ-isMonoid = ↦-isMonoid (Dual-isMonoid ℕ+0-isMonoid)

↦DualMaybeℕ×MaybeDual↦ℕ-isMonoid : {A : Set} →
  IsMonoid (↦ {A} (⇄ (¿ _+_)) |><| ¿ (⇄ (↦ {A} _+_))) ((const (dual nothing)) , nothing)
↦DualMaybeℕ×MaybeDual↦ℕ-isMonoid
  = ×-isMonoid (↦-isMonoid (Dual-isMonoid (Maybe-isMonoid ℕ+0-isMonoid)))
                (Maybe-isMonoid (Dual-isMonoid (↦-isMonoid ℕ+0-isMonoid)))
