module Monoid where

open import Data.Nat
open import Data.Product
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as Eq

record IsSemiGroup {A : Set} (_∙_ : A → A → A) : Set where
  field
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
  _⊕_ : A → A → A
  _⊕_ = _∙_

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

record IsFunctor (F : Set → Set) : Set₁ where
   field
    fmap : ∀ {A B} → (A → B) → F A → F B
    identity : {A : Set} (x : F A) → fmap id x ≡ id x
    homomorphic : ∀ {A B C} {f : B → C} {g : A → B} (x : F A) → (fmap f ∘ fmap g) x ≡ fmap (f ∘ g) x

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

lift : ∀{A B} → (A → B) → Maybe A → Maybe B
lift f nothing = nothing
lift f (just x) = just (f x)

Maybe-isFunctor : IsFunctor Maybe
Maybe-isFunctor = record { fmap = lift; identity = fmap-id; homomorphic = fmap-∘ }
  where
    fmap-id : ∀ {A} (x : Maybe A) → lift id x ≡ x
    fmap-id nothing = refl
    fmap-id (just x) = refl
    fmap-∘ : ∀ {A B C} {f : B → C} {g : A → B}
      (x : Maybe A) → lift f (lift g x) ≡ lift (λ y → f (g y)) x
    fmap-∘ nothing = refl
    fmap-∘ (just x) = refl

lift2 : ∀ {A B C} → (A → B → C) → Maybe A → Maybe B → Maybe C
lift2 f nothing m₂ = nothing
lift2 f m₁ nothing = nothing
lift2 f (just x) (just y) = just (f x y)

maybe-assoc : ∀ {A} {op2 : A → A → A} →
          IsSemiGroup op2 →
          (x y z : Maybe A) →
          lift2 op2 (lift2 op2 x y) z ≡ lift2 op2 x (lift2 op2 y z)
maybe-assoc A-isMonoid nothing my mz = refl
maybe-assoc A-isMonoid (just x) nothing mz = refl
maybe-assoc A-isMonoid (just x) (just y) nothing = refl
maybe-assoc A-isMonoid (just x) (just y) (just z) = cong just (IsSemiGroup.assoc A-isMonoid x y z)

MaybeA-isSemigroup : ∀ {A} {op2 : A → A → A} →
                   (prf : IsSemiGroup op2) → IsSemiGroup (lift2 op2)
MaybeA-isSemigroup prf = record { assoc = maybe-assoc prf }

Maybeℕ+-isSemigroup : IsSemiGroup {Maybe ℕ} (lift2 _+_)
Maybeℕ+-isSemigroup = MaybeA-isSemigroup ℕ+-isSemigroup

{--
Maybeℕ+-isSemigroup : IsSemiGroup {Maybe ℕ} (lift2 _+_)
Maybeℕ+-isSemigroup = record { assoc = maybeℕ-assoc }
  where
    maybeℕ-assoc : ∀ x y z →
               lift2 _+_ (lift2 _+_ x y) z ≡ lift2 _+_ x (lift2 _+_ y z)
    maybeℕ-assoc nothing my mz = refl
    maybeℕ-assoc (just x) nothing mz = refl
    maybeℕ-assoc (just x) (just x₁) nothing = refl
    maybeℕ-assoc (just x) (just y) (just z)
      = cong just (assoc x y z) where open IsSemiGroup ℕ+-isSemigroup
--}
