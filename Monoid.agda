module Monoid where

open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.Unit
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

record Dual (A : Set) : Set where
  constructor dual
  field
    getDual : A

open Dual

transDual : ∀ {A} → (A → A → A) → Dual A → Dual A → Dual A
transDual f (dual x) (dual y) = dual (f y x)

dual-assoc : ∀ {A} {op2 : A → A → A} →
           IsSemiGroup op2 →
           (x y z : Dual A) →
           dual (op2 (getDual z) (op2 (getDual y) (getDual x))) ≡ dual (op2 (op2 (getDual z) (getDual y)) (getDual x))
dual-assoc p (dual x) (dual y) (dual z) = cong dual (sym (IsSemiGroup.assoc p z y x))

dual-identity : ∀ {A} {op2 : A → A → A} {ε : A} →
                (prf : IsMonoid op2 ε) →
                ((x : Dual A) → dual (op2 (getDual x) ε) ≡ x) × ((x : Dual A) → dual (op2 ε (getDual x)) ≡ x)
dual-identity p = rightId p , leftId p
  where
    rightId : ∀ {A} {op2 : A → A → A} {ε : A} →
          (prf : IsMonoid op2 ε) → (x : Dual A) → dual (op2 (getDual x) ε) ≡ x
    rightId p (dual x) = cong dual (proj₂ (IsMonoid.identity p) x)
    leftId : ∀ {A} {op2 : A → A → A} {ε : A} →
         (prf : IsMonoid op2 ε) → (x : Dual A) → dual (op2 ε (getDual x)) ≡ x
    leftId p (dual x) = cong dual (proj₁ (IsMonoid.identity p) x)

DualA-isSemigroup : ∀ {A} {op2 : A → A → A} →
                  (prf : IsSemiGroup {A} op2) → IsSemiGroup (transDual op2)
DualA-isSemigroup prf = record { assoc = dual-assoc prf }

DualA-isMonoid : ∀ {A} {op2 : A → A → A} {ε : A} →
               (prf : IsMonoid {A} op2 ε) → IsMonoid (transDual op2) (dual ε)
DualA-isMonoid p = record { isSemigroup = DualA-isSemigroup (IsMonoid.isSemigroup p)
                          ; identity = dual-identity p
                          }

DualMaybeℕ+0-isMonoid : IsMonoid (transDual (lift2 _+_)) (dual nothing)
DualMaybeℕ+0-isMonoid = DualA-isMonoid (MaybeA-isMonoid ℕ+0-isMonoid)

MaybeDualℕ+0-isMonoid : IsMonoid (lift2 (transDual _+_)) nothing
MaybeDualℕ+0-isMonoid = MaybeA-isMonoid (DualA-isMonoid ℕ+0-isMonoid)

record First (A : Set) : Set where
  constructor first
  field
    getFirst : Maybe A

_<|_ : {A : Set} → First A → First A → First A
fa <| fb with fa
fa <| fb | first nothing = fb
fa <| fb | first (just _) = fa

<|-assoc : {A : Set} → (fx fy fz : First A) → (fx <| fy) <| fz ≡ fx <| (fy <| fz)
<|-assoc (first nothing) fy fz = refl
<|-assoc (first (just x)) fy fz = refl

<|-identity : {A : Set} → ((x : First A) → first nothing <| x ≡ x) × ((x : First A) → x <| first nothing ≡ x)
<|-identity = (λ x → refl) , (λ x → right-id)
  where
    right-id : ∀ {A} {x : First A} → (x <| first nothing) ≡ x
    right-id {x = first nothing} = refl
    right-id {x = first (just x)} = refl

record Last (A : Set) : Set where
  constructor last
  field
    getLast : Maybe A

_|>_ : {A : Set} → Last A → Last A → Last A
fa |> fb with fb
fa |> fb | last nothing = fa
fa |> fb | last (just _) = fb

|>-assoc : {A : Set} → (lx ly lz : Last A) → (lx |> ly) |> lz ≡ lx |> (ly |> lz)
|>-assoc lx ly (last nothing) = refl
|>-assoc lx ly (last (just x)) = refl

|>-identity : ∀ {A} → ((x : Last A) → last nothing |> x ≡ x) × ((x : Last A) → x |> last nothing ≡ x)
|>-identity = (λ x → left-id) , (λ x → refl)
  where
    left-id : ∀ {A} {x : Last A} → last nothing |> x ≡ x
    left-id {x = last nothing} = refl
    left-id {x = last (just x)} = refl


First-isSemigroup : {A : Set} → IsSemiGroup {First A} _<|_
First-isSemigroup = record { assoc = <|-assoc }

Last-isSemigroup : {A : Set} → IsSemiGroup {Last A} _|>_
Last-isSemigroup = record { assoc = |>-assoc }

First-isMonoid : {A : Set} → IsMonoid {First A} _<|_ (first nothing)
First-isMonoid = record { isSemigroup = First-isSemigroup ; identity = <|-identity }

Last-isMonoid : {A : Set} → IsMonoid {Last A} _|>_ (last nothing)
Last-isMonoid = record { isSemigroup = Last-isSemigroup ; identity = |>-identity }

_<u>_ : Unit → Unit → Unit
_ <u> _ = unit
<u>-assoc : (x y z : Unit) → (x <u> y) <u> z ≡ x <u> (y <u> z)
<u>-assoc x y z = refl

Unit-isSemigroup : IsSemiGroup {Unit} _<u>_
Unit-isSemigroup = record { assoc = <u>-assoc }

Unit-isMonoid : IsMonoid {Unit} _<u>_ unit
Unit-isMonoid = record { isSemigroup = Unit-isSemigroup
                       ; identity = (λ x → left-id) , (λ x → right-id)
                       }
              where
                left-id : ∀ {x} → unit ≡ x
                left-id {unit} = refl
                right-id : ∀ {x} → unit ≡ x
                right-id {unit} = refl

data Ord : Set where
  LT : Ord
  EQ : Ord
  GT : Ord

_<o>_ : Ord → Ord → Ord
LT <o> y = LT
EQ <o> y = y
GT <o> y = GT

<o>-assoc : (x y z : Ord) → (x <o> y) <o> z ≡ x <o> (y <o> z)
<o>-assoc LT y z = refl
<o>-assoc EQ y z = refl
<o>-assoc GT y z = refl

ord-identity : (∀ x → EQ <o> x ≡ x) × (∀ x → x <o> EQ ≡ x)
ord-identity = (λ x → refl) , (λ x → riht-id)
  where
    riht-id : ∀ {x} → x <o> EQ ≡ x
    riht-id {LT} = refl
    riht-id {EQ} = refl
    riht-id {GT} = refl

Ord-isSemigroup : IsSemiGroup _<o>_
Ord-isSemigroup = record { assoc = <o>-assoc }

Ord-isMonoid : IsMonoid _<o>_ EQ
Ord-isMonoid = record { isSemigroup = Ord-isSemigroup ; identity = ord-identity }

-- TODO
-- Monoid b => Monoid (a -> b)
-- Monoid a, Monoid b => Monoid (a , b)
-- Monoid [a]
-- (Monoid a , Monoid b) => Monoid (a , b)

