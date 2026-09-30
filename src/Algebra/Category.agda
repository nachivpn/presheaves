open import Algebra.Lib

module Algebra.Category {𝒞 : Category} (T : Monad 𝒞) where

open import Categories.Category.Construction.EilenbergMoore T
  -- obs. Module⇒ defines a module/algbera homomorphism
  renaming (Module to Algebra ; Module⇒ to Algebra⇒) public

module 𝒞 = Category 𝒞
module ≈ = 𝒞.Equiv
module T = Monad T

open 𝒞

-- Functoriality of T
open T.F using ()
  renaming
    ( F₀ to T₀
    ; F₁ to T₁
    ; F-resp-≈ to T₁-resp-≈
    ; identity to T₁-pres-id
    ; homomorphism to T₁-pres-∘
    ) public

infix  4 _≈̃_ _⇒̃_
infixr 9 _∘̃_

-- plain maps on monad algebras/modules
record _⇒̃_ (X Y : Algebra) : Set where
  constructor plain
  private
    module X = Algebra X
    module Y = Algebra Y
  field
    arr     : X.A 𝒞.⇒ Y.A

open _⇒̃_ public

id∼ : {X : Algebra} → X ⇒̃ X
id∼ = plain 𝒞.id

_∘̃_ : {X Y Z : Algebra} → Y ⇒̃ Z → X ⇒̃ Y → X ⇒̃ Z
f ∘̃ g = plain (f .arr 𝒞.∘ g .arr)

open _⇒̃_

_≈̃_ : {X Y : Algebra} → (f g : X ⇒̃ Y) → Set
f ≈̃ g  = arr f 𝒞.≈ arr g

𝒞̃ : Category
𝒞̃ = record
  { Obj       = Algebra
  ; _⇒_       = _⇒̃_
  ; _≈_       = _≈̃_
  ; id        = id∼
  ; _∘_       = _∘̃_
  ; assoc     = 𝒞.assoc
  ; sym-assoc = 𝒞.sym-assoc
  ; identityˡ = 𝒞.identityˡ
  ; identityʳ = 𝒞.identityʳ
  ; identity² = 𝒞.identity²
  ; equiv     = record
    { refl  = 𝒞.Equiv.refl
    ; sym   = 𝒞.Equiv.sym
    ; trans = 𝒞.Equiv.trans
    }
  ; ∘-resp-≈  = 𝒞.∘-resp-≈
  }

module 𝒞̃ = Category 𝒞̃

𝒥 : Functor 𝒞 𝒞̃
𝒥 = record
  { F₀         = λ X → record
    { A        = T₀ X
    ; action   = T.μ.η X
    ; commute  = T.assoc
    ; identity = T.identityʳ
    }
  ; F₁           = plain ∘ᶠ T₁
  ; identity     = T₁-pres-id
  ; homomorphism = T₁-pres-∘
  ; F-resp-≈     = T₁-resp-≈
  }

∣-∣ : Functor 𝒞̃ 𝒞
∣-∣ = let open Algebra in record
  { F₀           = A
  ; F₁           = arr
  ; identity     = ≈.refl
  ; homomorphism = ≈.refl
  ; F-resp-≈     = idᶠ
  }

module 𝒥 = Functor 𝒥
join  = T.μ.η
point = T.η.η
