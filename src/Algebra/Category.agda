open import Algebra.Lib

module Algebra.Category (𝒞 : Category) (T : Monad 𝒞) where

open import Categories.Category.Construction.EilenbergMoore T renaming (Module to Algebra)

module 𝒞 = Category 𝒞
open 𝒞
module ≈ = Equiv {- in 𝒞 -}

module T = Monad T
open T.F renaming (F₀ to T₀ ; F₁ to T₁ ; F-resp-≈ to T₁-resp-≈)

-- plain maps on monad algebras/modules
record _⇒̃ᵀ_ (X Y : Algebra) : Set where
  constructor plain
  private
    module X = Algebra X
    module Y = Algebra Y
  field
    arr     : X.A 𝒞.⇒ Y.A

open _⇒̃ᵀ_

𝒞̃ᵀ : Category
𝒞̃ᵀ = record
  { Obj       = Algebra
  ; _⇒_       = _⇒̃ᵀ_
  ; _≈_       = λ f g → arr f 𝒞.≈ arr g
  ; id        = record { arr = 𝒞.id }
  ; _∘_       = λ f g → plain (f .arr 𝒞.∘ g .arr)
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

𝒥 : Functor 𝒞 𝒞̃ᵀ 
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

module 𝒥 = Functor 𝒥

module Cartesian∼ᵀ (cartesianꟲ : Cartesian 𝒞) where

  open import Categories.Object.Terminal
  open import Categories.Category.BinaryProducts
  
  open Cartesian cartesianꟲ
    renaming (_×_ to _×ꟲ_ ; η to ×ᶜ-eta ; _×₁_ to _×-map_ ; ⊤ to ⊤ꟲ)

  join  = T.μ.η
  point = T.η.η

  ⊤̃ᵀ : Algebra
  ⊤̃ᵀ = record
    { A        = ⊤ꟲ
    ; action   = !
    ; commute  = ≈.trans
          (≈.sym (!-unique (! ∘ T₁ !)))
          (!-unique (! ∘ join ⊤ꟲ))
    ; identity = ≈.trans
        (≈.sym (!-unique (! ∘ point ⊤ꟲ)))
        (!-unique 𝒞.id)
    }
  
  terminal∼ᵀ : Terminal 𝒞̃ᵀ
  terminal∼ᵀ = record
    { ⊤             = ⊤̃ᵀ
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
    
    _×̃ᵀ_ : Algebra
    _×̃ᵀ_ = record 
      { A        = ∣X∣ ×ꟲ ∣Y∣
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
          ≈˘⟨ ⟨⟩-cong₂ assoc assoc ⟩
        ⟨ (X.action ∘ T₁ X.action) ∘ T₁ (T₁ π₁) , (Y.action ∘ T₁ Y.action) ∘ T₁ (T₁ π₂) ⟩
          -- `commute` ("action property") of the underlying algebras 
          ≈⟨ ⟨⟩-cong₂ (∘-resp-≈ˡ X.commute) (∘-resp-≈ˡ Y.commute) ⟩
        ⟨ (X.action ∘ join ∣X∣) ∘ T₁ (T₁ π₁) , (Y.action ∘ join ∣Y∣) ∘ T₁ (T₁ π₂) ⟩
          ≈⟨ ⟨⟩-cong₂ assoc assoc ⟩
        ⟨ X.action ∘ join ∣X∣ ∘ T₁ (T₁ π₁) , Y.action ∘ join ∣Y∣ ∘ T₁ (T₁ π₂) ⟩
          -- naturality of join
          ≈⟨ ⟨⟩-cong₂ (∘-resp-≈ʳ (T.μ.commute π₁)) (∘-resp-≈ʳ (T.μ.commute π₂)) ⟩
        ⟨ X.action ∘ T₁ π₁ ∘ join (∣X∣ ×ꟲ ∣Y∣) , Y.action ∘ T₁ π₂ ∘ join (∣X∣ ×ꟲ ∣Y∣) ⟩
          -- underlying product structure
          ≈˘⟨ ≈.trans ∘-distribʳ-⟨⟩ (⟨⟩-cong₂ assoc assoc) ⟩
        ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩ ∘ join (∣X∣ ×ꟲ ∣Y∣)
          ∎
      ; identity = let open 𝒞.HomReasoning in begin
        ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩ ∘ point (∣X∣ ×ꟲ ∣Y∣)
          -- underlying product structure
          ≈⟨ ≈.trans ∘-distribʳ-⟨⟩ (⟨⟩-cong₂ 𝒞.assoc assoc) ⟩
        ⟨ X.action ∘ T₁ π₁ ∘ point (∣X∣ ×ꟲ ∣Y∣) , Y.action ∘ T₁ π₂ ∘ point (∣X∣ ×ꟲ ∣Y∣) ⟩
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
          ≈⟨ ×ᶜ-eta ⟩
        𝒞.id
          ∎
      }

  products∼ᵀ : BinaryProducts 𝒞̃ᵀ
  products∼ᵀ = record
    { product = λ {X} {Y} → record
      { A×B      = X ×̃ᵀ Y
      ; π₁       = plain π₁
      ; π₂       = plain π₂
      ; ⟨_,_⟩    = λ f g → plain ⟨ f .arr , g .arr ⟩
      ; project₁ = project₁
      ; project₂ = project₂
      ; unique   = unique
      }
    }
  
  cartesian∼ᵀ : Cartesian 𝒞̃ᵀ
  cartesian∼ᵀ = record
    { terminal = terminal∼ᵀ
    ; products = products∼ᵀ
    }
    
module Cocartesian∼ᵀ (cocartesianꟲ : Cocartesian 𝒞) where

  open import Categories.Category.BinaryCoproducts public
  open import Categories.Object.Initial public

  open Cocartesian cocartesianꟲ
    renaming (_+_ to _+ꟲ_ ; _+₁_ to _+-map_ ; ⊥ to ⊥ꟲ)

  module _ (X Y : Algebra) where
    private
      module X = Algebra X
      module Y = Algebra Y
      ∣X∣ = X.A
      ∣Y∣ = Y.A
      
    _+̃ᵀ_ : Algebra
    _+̃ᵀ_ = 𝒥.₀ (∣X∣ +ꟲ ∣Y∣)

  ⊥̃ᵀ : Algebra
  ⊥̃ᵀ = 𝒥.₀ ⊥ꟲ

    
