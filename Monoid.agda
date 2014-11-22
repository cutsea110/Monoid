module Monoid where

open import Data.Bool
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
  _<>_ = _∙_
  
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

_∙_ : ∀ {A} → Endo A → Endo A → Endo A
f ∙ g = endo (appEndo f ∘ appEndo g) where open Endo

endo-assoc : ∀ {A} → (f g h : Endo A) → (f ∙ g) ∙ h ≡ f ∙ (g ∙ h)
endo-assoc (endo appEndo) (endo appEndo₁) (endo appEndo₂) = refl

Endo-isSemigroup : ∀ {A} → IsSemiGroup {Endo A} _∙_
Endo-isSemigroup = record { assoc = endo-assoc }

endo-identity : ∀ {A} → ((x : Endo A) → (endo id) ∙ x ≡ x) × ((x : Endo A) → x ∙ (endo id) ≡ x)
endo-identity = (λ x → refl) , (λ x → refl)

Endo-isMonoid : ∀ {A} → IsMonoid {Endo A} _∙_ (endo id)
Endo-isMonoid = record { isSemigroup = Endo-isSemigroup ; identity = endo-identity }

record IsFunctor (F : Set → Set) : Set₁ where
   field
    fmap : ∀ {A B} → (A → B) → F A → F B
    identity : ∀ {A} → (x : F A) → fmap id x ≡ id x
    homomorphic : ∀ {A B C} {f : B → C} {g : A → B} → (x : F A) → (fmap f ∘ fmap g) x ≡ fmap (f ∘ g) x

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

lift2 : ∀ {A} → (A → A → A) → Maybe A → Maybe A → Maybe A
lift2 f nothing m₂ = m₂
lift2 f m₁ nothing = m₁
lift2 f (just x) (just y) = just (f x y)

MaybeA-isSemigroup : ∀ {A} {op2 : A → A → A} →
                   (prf : IsSemiGroup op2) → IsSemiGroup (lift2 op2)
MaybeA-isSemigroup prf = record { assoc = maybe-assoc prf }
  where
    maybe-assoc : ∀ {A} {op2 : A → A → A} →
              IsSemiGroup op2 →
              (x y z : Maybe A) →
              lift2 op2 (lift2 op2 x y) z ≡ lift2 op2 x (lift2 op2 y z)
    maybe-assoc p nothing my mz = refl
    maybe-assoc p (just x) nothing mz = refl
    maybe-assoc p (just x) (just y) nothing = refl
    maybe-assoc p (just x) (just y) (just z) = cong just (IsSemiGroup.assoc p x y z)

Maybeℕ+-isSemigroup : IsSemiGroup {Maybe ℕ} (lift2 _+_)
Maybeℕ+-isSemigroup = MaybeA-isSemigroup ℕ+-isSemigroup

MaybeEndo-isSemigroup : ∀ {A} → IsSemiGroup {Maybe (Endo A)} (lift2 _∙_)
MaybeEndo-isSemigroup = MaybeA-isSemigroup Endo-isSemigroup

m<>nothing≡m : ∀ {A} {op2 : A → A → A} {x : Maybe A} → lift2 op2 x nothing ≡ x
m<>nothing≡m {x = nothing} = refl
m<>nothing≡m {x = just x} = refl

MaybeA-isMonoid : ∀ {A} {op2 : A → A → A} {ε : A} →
  IsMonoid op2 ε → IsMonoid (lift2 op2) nothing
MaybeA-isMonoid prf
  = record { isSemigroup = MaybeA-isSemigroup (IsMonoid.isSemigroup prf)
           ; identity = (λ x → refl) , (λ x → m<>nothing≡m)
           }

Maybeℕ+0-isMonoid : IsMonoid {Maybe ℕ} (lift2 _+_) nothing
Maybeℕ+0-isMonoid = MaybeA-isMonoid ℕ+0-isMonoid

MaybeEndo-isMonoid : ∀{A} → IsMonoid {Maybe (Endo A)} (lift2 _∙_) nothing
MaybeEndo-isMonoid = MaybeA-isMonoid Endo-isMonoid

record All : Set where
  constructor all
  field
    getAll : Bool

open All

_&&_ : All → All → All
x && y = all (getAll x ∧ getAll y) where open All

&&-assoc : (x y z : All) →
           all ((getAll x ∧ getAll y) ∧ getAll z) ≡ all (getAll x ∧ getAll y ∧ getAll z)
&&-assoc (all x) (all y) (all z) = cong all (∧-assoc x y z)
  where
    ∧-assoc : (x y z : Bool) → (x ∧ y) ∧ z ≡ x ∧ y ∧ z
    ∧-assoc true y z = refl
    ∧-assoc false y z = refl

All-isSemigroup : IsSemiGroup {All} _&&_
All-isSemigroup = record { assoc = &&-assoc }

All-isMonoid : IsMonoid {All} _&&_ (all true)
All-isMonoid = record { isSemigroup = All-isSemigroup ; identity = (λ x → refl) , (λ x → b&&e≡b) }
  where
    b&&e≡b : {x : All} → all (getAll x ∧ true) ≡ x
    b&&e≡b {x = all true} = refl
    b&&e≡b {x = all false} = refl

record Any : Set where
  constructor any
  field
    getAny : Bool

open Any

_||_ : Any → Any → Any
x || y = any (getAny x ∨ getAny y)
||-assoc : (x y z : Any) →
           any ((getAny x ∨ getAny y) ∨ getAny z) ≡ any (getAny x ∨ getAny y ∨ getAny z)
||-assoc (any x) (any y) (any z) = cong any (∨-assoc x y z)
  where
    ∨-assoc : ∀ x y z → (x ∨ y) ∨ z ≡ x ∨ y ∨ z
    ∨-assoc true y z = refl
    ∨-assoc false y z = refl

Any-isSemigroup : IsSemiGroup {Any} _||_
Any-isSemigroup = record { assoc = ||-assoc }

Any-isMonoid : IsMonoid {Any} _||_ (any false)
Any-isMonoid = record { isSemigroup = Any-isSemigroup ; identity = (λ x → refl) , (λ x → b||e≡b) }
  where
    b||e≡b : {x : Any} → any (getAny x ∨ false) ≡ x
    b||e≡b {x = any true} = refl
    b||e≡b {x = any false} = refl
