open import Algebra.Lib

module Algebra.Category (𝒞 : Category) (T : Monad 𝒞) where

open import Categories.Category.Construction.EilenbergMoore T
  renaming (Module to Algebra ; Module⇒ to AlgebraHom)

module 𝒞 = Category 𝒞
open 𝒞
module ≈ = Equiv {- in 𝒞 -}

module T = Monad T
open T.F renaming (F₀ to T₀ ; F₁ to T₁ ; F-resp-≈ to T₁-resp-≈)

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

open _⇒̃_

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

𝒥 : Functor 𝒞 𝒞̃
𝒥 = record
  { F₀         = λ X → record
    { A        = T₀ X
    ; action   = T.μ.η X
    ; commute  = T.assoc
    ; identity = T.identityʳ
    }
  ; F₁           = plain ∘ᶠ T₁
  ; identity     = identity
  ; homomorphism = homomorphism
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
private
  join  = T.μ.η
  point = T.η.η

module Cartesian∼ (cartesian : Cartesian 𝒞) where

  open import Categories.Object.Terminal public
  open import Categories.Category.BinaryProducts public

  open Cartesian cartesian renaming (η to ×-eta) public

  ⊤̃ : Algebra
  ⊤̃ = record
    { A        = ⊤
    ; action   = !
    ; commute  = ≈.trans
          (≈.sym (!-unique (! ∘ T₁ !)))
          (!-unique (! ∘ join ⊤))
    ; identity = ≈.trans
        (≈.sym (!-unique (! ∘ point ⊤)))
        (!-unique 𝒞.id)
    }

  terminal∼ : Terminal 𝒞̃
  terminal∼ = record
    { ⊤             = ⊤̃
    ; ⊤-is-terminal = record
      { !        = plain !
      ; !-unique = !-unique ∘ᶠ arr
      }
    }

  module _ (X Y : Algebra) where
    private
      module X = Algebra X
      module Y = Algebra Y
      ∣X∣ = X.A
      ∣Y∣ = Y.A

    _×̃_ : Algebra
    _×̃_ = record
      { A        = ∣X∣ × ∣Y∣
      ; action   = ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩
      ; commute  = let open 𝒞.HomReasoning in begin
        ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩ ∘ T₁ ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩
          -- underlying product structure
          ≈⟨ ≈.trans ∘-distribʳ-⟨⟩ (⟨⟩-cong₂ assoc assoc) ⟩
        ⟨ X.action ∘ T₁ π₁ ∘ T₁ ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩
        , Y.action ∘ T₁ π₂ ∘ T₁ ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩ ⟩
          ≈˘⟨ ⟨⟩-cong₂ (∘-resp-≈ʳ homomorphism) (∘-resp-≈ʳ homomorphism) ⟩
        ⟨ X.action ∘ T₁ (π₁ ∘ ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩)
        , Y.action ∘ T₁ (π₂ ∘ ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩) ⟩
          -- underlying product structure
          ≈⟨ ⟨⟩-cong₂ (∘-resp-≈ʳ (T₁-resp-≈ project₁)) (∘-resp-≈ʳ (T₁-resp-≈ project₂)) ⟩
        ⟨ X.action ∘ T₁ (X.action ∘ T₁ π₁) , Y.action ∘ T₁ (Y.action ∘ T₁ π₂) ⟩
          ≈⟨ ⟨⟩-cong₂ (∘-resp-≈ʳ homomorphism) (∘-resp-≈ʳ homomorphism) ⟩
        ⟨ X.action ∘ T₁ X.action ∘ T₁ (T₁ π₁) , Y.action ∘ T₁ Y.action ∘ T₁ (T₁ π₂) ⟩
          ≈⟨ ⟨⟩-cong₂ sym-assoc sym-assoc ⟩
        ⟨ (X.action ∘ T₁ X.action) ∘ T₁ (T₁ π₁) , (Y.action ∘ T₁ Y.action) ∘ T₁ (T₁ π₂) ⟩
          -- `commute` ("action property") of the underlying algebras
          ≈⟨ ⟨⟩-cong₂ (∘-resp-≈ˡ X.commute) (∘-resp-≈ˡ Y.commute) ⟩
        ⟨ (X.action ∘ join ∣X∣) ∘ T₁ (T₁ π₁) , (Y.action ∘ join ∣Y∣) ∘ T₁ (T₁ π₂) ⟩
          ≈⟨ ⟨⟩-cong₂ assoc assoc ⟩
        ⟨ X.action ∘ join ∣X∣ ∘ T₁ (T₁ π₁) , Y.action ∘ join ∣Y∣ ∘ T₁ (T₁ π₂) ⟩
          -- naturality of join
          ≈⟨ ⟨⟩-cong₂ (∘-resp-≈ʳ (T.μ.commute π₁)) (∘-resp-≈ʳ (T.μ.commute π₂)) ⟩
        ⟨ X.action ∘ T₁ π₁ ∘ join (∣X∣ × ∣Y∣) , Y.action ∘ T₁ π₂ ∘ join (∣X∣ × ∣Y∣) ⟩
          -- underlying product structure
          ≈˘⟨ ≈.trans ∘-distribʳ-⟨⟩ (⟨⟩-cong₂ assoc assoc) ⟩
        ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩ ∘ join (∣X∣ × ∣Y∣)
          ∎
      ; identity = let open 𝒞.HomReasoning in begin
        ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩ ∘ point (∣X∣ × ∣Y∣)
          -- underlying product structure
          ≈⟨ ≈.trans ∘-distribʳ-⟨⟩ (⟨⟩-cong₂ 𝒞.assoc assoc) ⟩
        ⟨ X.action ∘ T₁ π₁ ∘ point (∣X∣ × ∣Y∣) , Y.action ∘ T₁ π₂ ∘ point (∣X∣ × ∣Y∣) ⟩
          -- naturality of point
          ≈˘⟨ ⟨⟩-cong₂ (∘-resp-≈ʳ (T.η.commute π₁)) (∘-resp-≈ʳ (T.η.commute π₂)) ⟩
        ⟨ X.action ∘ point ∣X∣ ∘ π₁ , Y.action ∘ point ∣Y∣ ∘ π₂ ⟩
          ≈⟨ ⟨⟩-cong₂ sym-assoc sym-assoc ⟩
        ⟨ (X.action ∘ point ∣X∣) ∘ π₁ , (Y.action ∘ point ∣Y∣) ∘ π₂ ⟩
          -- `identity` ("unit property") of the underlying algebras
          ≈⟨ ⟨⟩-cong₂ (∘-resp-≈ˡ X.identity) (∘-resp-≈ˡ Y.identity) ⟩
        ⟨ 𝒞.id ∘ π₁ , 𝒞.id ∘ π₂ ⟩
          ≈⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟩
        ⟨ π₁ , π₂ ⟩
          -- underlying product structure
          ≈⟨ ×-eta ⟩
        𝒞.id
          ∎
      }

  products∼ : BinaryProducts 𝒞̃
  products∼ = record
    { product = λ {X} {Y} → record
      { A×B      = X ×̃ Y
      ; π₁       = plain π₁
      ; π₂       = plain π₂
      ; ⟨_,_⟩    = λ f g → plain ⟨ f .arr , g .arr ⟩
      ; project₁ = project₁
      ; project₂ = project₂
      ; unique   = unique
      }
    }

  cartesian∼ : Cartesian 𝒞̃
  cartesian∼ = record
    { terminal = terminal∼
    ; products = products∼
    }

module ModeratelyCocartesian∼ (cocartesian : Cocartesian 𝒞) where

  open import Categories.Category.BinaryCoproducts public
  open import Categories.Object.Initial public

  open Cocartesian cocartesian public

  -- define +̃
  module _ (X Y : Algebra) where
    private
      module X = Algebra X ; ∣X∣ = X.A
      module Y = Algebra Y ; ∣Y∣ = Y.A

    _+̃_ : Algebra
    _+̃_ = 𝒥.₀ (∣X∣ + ∣Y∣)

  ⊥̃ : Algebra
  ⊥̃ = 𝒥.₀ ⊥

  module _ {X : Algebra} where
    private
      module X = Algebra X

    ¡̃ : (⊥̃ ⇒̃ X)
    ¡̃ = plain (X.action ∘ T₁ ¡)

  -- (weak) eta rule for the empty type
  η̃₀ : id∼ {⊥̃} ≈̃ ¡̃ {⊥̃}
  η̃₀ = let open 𝒞.HomReasoning in begin
    𝒞.id {T₀ ⊥}
      -- unit law of monad (join ∘ T point ≈ id)
      ≈˘⟨ T.identityˡ ⟩
    join ⊥ ∘ T₁ (point ⊥)
      -- uniqueness of underlying initial obj.
      ≈˘⟨ ∘-resp-≈ʳ (T₁-resp-≈ (¡-unique (point ⊥))) ⟩
    join ⊥ ∘ T₁ ¡
      ∎

  module _ {X Y : Algebra} where
    private
      module X = Algebra X
      module Y = Algebra Y
      ∣X∣ = X.A ; ∣Y∣ = Y.A

    ĩ₁ : X ⇒̃ X +̃ Y
    ĩ₁ = plain (point (∣X∣ + ∣Y∣) ∘ i₁)

    ĩ₂ : Y ⇒̃ X +̃ Y
    ĩ₂ = plain (point (∣X∣ + ∣Y∣) ∘ i₂)

    module _ {Z : Algebra} where
      private
        module Z = Algebra Z ; ∣Z∣ = Z.A

      [_,_]∼ : X ⇒̃ Z → Y ⇒̃ Z → X +̃ Y ⇒̃ Z
      [ f , g ]∼ = plain (Z.action ∘ T₁ [ f .arr , g .arr ])

    -- (weak) eta rule for sum types
    η̃₊ :  id∼ {X +̃ Y} ≈̃ [ ĩ₁ , ĩ₂ ]∼
    η̃₊ = let open 𝒞.HomReasoning in begin
      𝒞.id {T₀ (∣X∣ + ∣Y∣)}
        -- unit law of the monad (join ∘ T point ≈ id)
        -- obs. identical to η̃₀
        ≈˘⟨ T.identityˡ ⟩
      join _ ∘ T₁ (point (∣X∣ + ∣Y∣))
        -- uniqueness of underlying coproduct
        ≈˘⟨ ∘-resp-≈ʳ (T₁-resp-≈ (+-unique Equiv.refl Equiv.refl)) ⟩
      join _ ∘ T₁ [ point _ ∘ i₁ , point _ ∘ i₂ ]
        ∎

  -- permutation conversions
  module _ {Z Z' : Algebra} (hHom : AlgebraHom Z Z') where

    private
      module Z = Algebra Z
      module Z' = Algebra Z'
      ∣Z∣ = Z.A ; ∣Z'∣ = Z'.A

    open AlgebraHom hHom renaming (arr to ∣h∣ ; commute to ∣h∣-hom)

    h : Z ⇒̃ Z'
    h = plain ∣h∣

    -- permutation conversions for the empty type
    π̃₀ᴱ : h ∘̃ ¡̃ {Z} ≈̃ ¡̃ {Z'}
    π̃₀ᴱ = let open 𝒞.HomReasoning in begin
      ∣h∣ ∘ Z.action ∘ T₁ ¡
        ≈⟨ sym-assoc ⟩
      (∣h∣ ∘ Z.action) ∘ T₁ ¡
        -- algebra homomorphism
        ≈⟨ ∘-resp-≈ˡ ∣h∣-hom ⟩
      (Z'.action ∘ T₁ ∣h∣) ∘ T₁ ¡
        ≈⟨ assoc ⟩
      Z'.action ∘ T₁ ∣h∣ ∘ T₁ ¡
        ≈˘⟨ ∘-resp-≈ʳ homomorphism ⟩
      Z'.action ∘ T₁ (∣h∣ ∘ ¡)
        -- uniqueness of initial obj.
        ≈˘⟨ ∘-resp-≈ʳ (T₁-resp-≈ (¡-unique (∣h∣ ∘ ¡))) ⟩
      Z'.action ∘ T₁ ¡
        ∎

    module _ {X Y : Algebra} (f : X ⇒̃ Z) (g : Y ⇒̃ Z) where
      private
        module X = Algebra X ; ∣X∣ = X.A
        module Y = Algebra Y ; ∣Y∣ = Y.A
        ∣f∣ = f .arr  ; ∣g∣ = g .arr

      -- permutation conversions for sum types
      π̃ᴱ₊ : h ∘̃ [ f , g ]∼ ≈̃ [ h ∘̃ f , h ∘̃ g ]∼
      π̃ᴱ₊ = let open 𝒞.HomReasoning in begin
        ∣h∣ ∘ Z.action ∘ T₁ [ ∣f∣ , ∣g∣ ]
          ≈⟨ sym-assoc ⟩
        (∣h∣ ∘ Z.action) ∘ T₁ [ ∣f∣ , ∣g∣ ]
          -- algebra homomorphism
          ≈⟨ ∘-resp-≈ˡ ∣h∣-hom ⟩
        (Z'.action ∘ T₁ ∣h∣) ∘ T₁ [ ∣f∣ , ∣g∣ ]
          ≈⟨ assoc ⟩
        Z'.action ∘ T₁ ∣h∣ ∘ T₁ [ ∣f∣ , ∣g∣ ]
          ≈˘⟨ ∘-resp-≈ʳ homomorphism ⟩
        Z'.action ∘ T₁ (∣h∣ ∘ [ ∣f∣ , ∣g∣ ])
          -- uniqueness of underlying coproduct
          ≈⟨ ∘-resp-≈ʳ (T₁-resp-≈ ∘-distribˡ-[]) ⟩
        Z'.action ∘ T₁ [ ∣h∣ ∘ ∣f∣ , ∣h∣ ∘ ∣g∣ ]
          ∎

open import Categories.Category.Monoidal.Core
open import Categories.Category.Cartesian.Monoidal

module ModeratelyDistributive∼
  (distributive : Distributive 𝒞)
  (let open Distributive distributive)
  (let open CartesianMonoidal cartesian using (monoidal))
  (strength : Strength monoidal T) where

  open Strength strength renaming (strengthen to θ)
  str = θ.η

  -- my modules
  open Cartesian∼ cartesian
  open ModeratelyCocartesian∼ cocartesian

  open Cartesian cartesian∼ using () renaming (_×₁_ to _×̃₁_)

  module _ {X Y Z : Algebra} where
      private
        module X = Algebra X ; ∣X∣ = X.A
        module Y = Algebra Y ; ∣Y∣ = Y.A
        module Z = Algebra Z ; ∣Z∣ = Z.A

      ×̃-distr-+̃ : X ×̃ (Y +̃ Z) ⇒̃ (X ×̃ Y) +̃ (X ×̃ Z)
      ×̃-distr-+̃ = plain (T₁ distributeˡ⁻¹ ∘ str (∣X∣ , ∣Y∣ + ∣Z∣))
