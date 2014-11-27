module Monoid.Instance where

open import Monoid

open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Function using (id; const; flip)
open import Relation.Binary.PropositionalEquality as PropEq

ℕ+-assoc : ∀ x y z → x + y + z ≡ x + (y + z)
ℕ+-assoc zero y z = refl
ℕ+-assoc (suc x) y z = cong suc (ℕ+-assoc x y z)

ℕ+-isSemigroup : IsSemiGroup _+_
ℕ+-isSemigroup = record { ∙-assoc = ℕ+-assoc }

ℕ+0-isMonoid : IsMonoid _+_ 0
ℕ+0-isMonoid = record { isSemigroup = ℕ+-isSemigroup
                       ; identity = 0+x≡x , x+0≡x
                       }
             where
               0+x≡x : ∀ (x : ℕ) → 0 + x ≡ x
               0+x≡x x = refl
               x+0≡x : ∀ (x : ℕ) → x + 0 ≡ x
               x+0≡x zero = refl
               x+0≡x (suc x) = cong suc (x+0≡x x)

_∣_ : ∀ {A : Set} → Maybe A → Maybe A → Maybe A
just x ∣ y = just x
nothing ∣ y = y

∣-assoc : ∀ {A} (x y z : Maybe A) → (x ∣ y) ∣ z ≡ x ∣ (y ∣ z)
∣-assoc (just x) y z = refl
∣-assoc nothing y z = refl

MaybeA∣-isSemigroup : ∀ {A : Set} → IsSemiGroup {Maybe A}  _∣_
MaybeA∣-isSemigroup = record { ∙-assoc = ∣-assoc }

MaybeA∣nothing-isMonoid : ∀ {A : Set} → IsMonoid {Maybe A} _∣_ nothing
MaybeA∣nothing-isMonoid = record { isSemigroup = MaybeA∣-isSemigroup
                                 ; identity = nothing∣x≡x , x∣nothing≡x
                                 }
                        where
                          nothing∣x≡x : ∀ {A} (x : Maybe A) → x ≡ x
                          nothing∣x≡x x = refl
                          x∣nothing≡x : ∀ {A} (x : Maybe A) → x ∣ nothing ≡ x
                          x∣nothing≡x (just x) = refl
                          x∣nothing≡x nothing = refl

DualA-isSemigroup : ∀ {A : Set} {_⊕_ : Op₂ A} →
                  IsSemiGroup _⊕_ → IsSemiGroup (⇄ _⊕_)
DualA-isSemigroup {_⊕_ = _⊕_} A-isSemiGroup
  = record { ∙-assoc = ⇄-assoc {_} {_⊕_} (∙-assoc A-isSemiGroup) }
  where
    open IsSemiGroup
    open Dual
    ⇄-assoc : ∀ {A : Set} {_⊕_ : Op₂ A} → Associativity _⊕_ → Associativity (⇄ _⊕_)
    ⇄-assoc ⊕-assoc (dual x) (dual y) (dual z) = cong dual (sym (⊕-assoc z y x))

DualA-isMonoid : ∀ {A : Set} {_⊕_ : Op₂ A} {ε : A} →
                 IsMonoid _⊕_ ε → IsMonoid (⇄ _⊕_) (dual ε)
DualA-isMonoid {A} {_⊕_} A-isMonoid
  = record { isSemigroup = DualA-isSemigroup (isSemigroup A-isMonoid)
           ; identity = ⇄-left-identity {_} {_⊕_} (proj₂ (identity A-isMonoid)) ,
                        ⇄-right-identity {_} {_⊕_} (proj₁ (identity A-isMonoid))
           }
           where
             open IsMonoid
             open Dual
             ⇄-left-identity : ∀ {A} {_⊕_ : Op₂ A} {ε : A} →
                             Right-Identity _⊕_ ε → Left-Identity (⇄ _⊕_) (dual ε)
             ⇄-left-identity prf (dual x) = cong dual (prf x)
             ⇄-right-identity : ∀ {A} {_⊕_ : Op₂ A} {ε : A} →
                              Left-Identity _⊕_ ε → Right-Identity (⇄ _⊕_) (dual ε)
             ⇄-right-identity prf (dual x) = cong dual (prf x)


EndoA-isSemigroup : ∀ {A : Set} → IsSemiGroup {Endo A} _∙_
EndoA-isSemigroup {A} = record { ∙-assoc = λ f g h → refl }

EndoA-isMonoid : ∀ {A : Set} → IsMonoid {Endo A} _∙_ (endo id)
EndoA-isMonoid = record { isSemigroup = EndoA-isSemigroup
                        ; identity = (λ x → refl) , (λ x → refl)
                        }


↦-isSemigroup : {A B : Set} {_⊕_ : Op₂ B} → IsSemiGroup _⊕_ → IsSemiGroup (↦ {A} _⊕_)
↦-isSemigroup {_⊕_ = _⊕_} prf = record { ∙-assoc = ↦-assoc {_} {_} {_⊕_} (∙-assoc prf) }
  where
    open IsSemiGroup
    ↦-assoc : ∀ {A B} {_⊕_ : Op₂ B} → Associativity _⊕_ → Associativity (↦ {A} _⊕_)
    ↦-assoc prf f g h = extentionality (λ x → prf (f x) (g x) (h x))


↦-isMonoid : {A B : Set} {_⊕_ : Op₂ B} {ε : B} → IsMonoid _⊕_ ε → IsMonoid {Arrow A B} (↦ _⊕_) (const ε)
↦-isMonoid {_⊕_ = _⊕_} prf
  = record { isSemigroup = ↦-isSemigroup (isSemigroup prf)
           ; identity = ↦-identity {_} {_} {_⊕_} (identity prf)
           }
           where
             open IsMonoid
             ↦-left-identity : ∀ {A B} {_⊕_ : Op₂ B} {ε : B} →
                                 Left-Identity _⊕_ ε → Left-Identity (↦ {A} _⊕_) (const ε)
             ↦-left-identity prf = λ f → extentionality (λ x → prf (f x))
             ↦-right-identity : ∀ {A B} {_⊕_ : Op₂ B} {ε : B} →
                                Right-Identity _⊕_ ε → Right-Identity (↦ {A} _⊕_) (const ε)
             ↦-right-identity prf = λ f → extentionality (λ x → prf (f x))
             ↦-identity : ∀ {A B} {_⊕_ : Op₂ B} {ε : B} → Identity _⊕_ ε → Identity (↦ {A} _⊕_) (const ε)
             ↦-identity {_⊕_ = _⊕_ } prf
               = ↦-left-identity {_} {_} {_⊕_} (proj₁ prf) , ↦-right-identity {_} {_} {_⊕_} (proj₂ prf)

×-isSemigroup : {A B : Set}{op₁ : Op₂ A}{op₂ : Op₂ B} →
              IsSemiGroup op₁ → IsSemiGroup op₂ → IsSemiGroup (op₁ |><| op₂)
×-isSemigroup {op₁ = op₁} {op₂ = op₂} prf₁ prf₂
  = record { ∙-assoc = |><|-assoc {_} {_} {op₁} {op₂} (∙-assoc prf₁) (∙-assoc prf₂) }
  where
    open IsSemiGroup
    |><|-assoc : ∀ {A B} {op₁ : Op₂ A} {op₂ : Op₂ B} →
                 Associativity op₁ → Associativity op₂ → Associativity (op₁ |><| op₂)
    |><|-assoc assoc₁ assoc₂ (fst₁ , snd₁) (fst₂ , snd₂) (fst₃ , snd₃)
               rewrite assoc₁ fst₁ fst₂ fst₃ | assoc₂ snd₁ snd₂ snd₃ = refl

×-isMonoid : {A B : Set}{op₁ : Op₂ A}{op₂ : Op₂ B}{ε₁ : A}{ε₂ : B} →
             IsMonoid op₁ ε₁ → IsMonoid op₂ ε₂ → IsMonoid (op₁ |><| op₂) (ε₁ , ε₂)
×-isMonoid {op₁ = op₁} {op₂ = op₂} prf₁ prf₂
  = record { isSemigroup = ×-isSemigroup (isSemigroup prf₁) (isSemigroup prf₂)
           ; identity = ×-identity {_} {_} {op₁} {op₂} (identity prf₁) (identity prf₂)
           }
           where
             open IsMonoid
             |><|-left-identity : ∀ {A B} {op₁ : Op₂ A} {op₂ : Op₂ B} {ε₁ : A} {ε₂ : B} →
                     Left-Identity op₁ ε₁ → Left-Identity op₂ ε₂ →
                     Left-Identity (op₁ |><| op₂) (ε₁ , ε₂)
             |><|-left-identity {op₁ = op₁} {op₂ = op₂} {ε₁ = ε₁} {ε₂ = ε₂} id₁ id₂ (fst , snd)
               rewrite id₁ fst | id₂ snd = refl
             |><|-right-identity : ∀ {A B} {op₁ : Op₂ A} {op₂ : Op₂ B} {ε₁ : A} {ε₂ : B} →
                     Right-Identity op₁ ε₁ → Right-Identity op₂ ε₂ →
                     Right-Identity (op₁ |><| op₂) (ε₁ , ε₂)
             |><|-right-identity {op₁ = op₁} {op₂ = op₂} {ε₁ = ε₁} {ε₂ = ε₂} id₁ id₂ (fst , snd)
               rewrite id₁ fst | id₂ snd = refl
             ×-identity : ∀ {A B} {op₁ : Op₂ A} {op₂ : Op₂ B} {ε₁ : A} {ε₂ : B} →
                        Identity op₁ ε₁ → Identity op₂ ε₂ → Identity (op₁ |><| op₂) (ε₁ , ε₂)
             ×-identity {op₁ = op₁} {op₂ = op₂} id₁ id₂
               = |><|-left-identity {_} {_} {op₁} {op₂} (proj₁ id₁) (proj₁ id₂) ,
                 |><|-right-identity {_} {_} {op₁} {op₂} (proj₂ id₁) (proj₂ id₂)

[]-isSemigroup : {A : Set} → IsSemiGroup {List A} _++_
[]-isSemigroup {A} = record { ∙-assoc = []-assoc }
  where
    []-assoc : {A : Set} → Associativity {List A} _++_
    []-assoc [] ys zs = refl
    []-assoc (x ∷ xs) ys zs = cong (_∷_ x) ([]-assoc xs ys zs)

[]-isMonoid : {A : Set} → IsMonoid {List A} _++_ []
[]-isMonoid = record { isSemigroup = []-isSemigroup
                     ; identity = []-identity
                     }
            where
              []-left-identity : ∀ {A} → Left-Identity {List A} _++_ []
              []-left-identity xs = refl
              []-right-identity : ∀ {A} → Right-Identity {List A} _++_ []
              []-right-identity [] = refl
              []-right-identity (x ∷ xs) = cong (_∷_ x) ([]-right-identity xs)
              []-identity : ∀ {A} → Identity {List A} _++_ []
              []-identity = []-left-identity , []-right-identity
