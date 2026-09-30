open import Algebra.Lib

module Algebra.Cartesian {𝒞 : Category} (T : Monad 𝒞) (cartesian : Cartesian 𝒞) where

open import Algebra.Category T
open 𝒞

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
    module X = Algebra X ; ∣X∣ = X.A
    module Y = Algebra Y ; ∣Y∣ = Y.A

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
        ≈˘⟨ ⟨⟩-cong₂ (∘-resp-≈ʳ T₁-pres-∘) (∘-resp-≈ʳ T₁-pres-∘) ⟩
      ⟨ X.action ∘ T₁ (π₁ ∘ ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩)
      , Y.action ∘ T₁ (π₂ ∘ ⟨ X.action ∘ T₁ π₁ , Y.action ∘ T₁ π₂ ⟩) ⟩
        -- underlying product structure
        ≈⟨ ⟨⟩-cong₂ (∘-resp-≈ʳ (T₁-resp-≈ project₁)) (∘-resp-≈ʳ (T₁-resp-≈ project₂)) ⟩
      ⟨ X.action ∘ T₁ (X.action ∘ T₁ π₁) , Y.action ∘ T₁ (Y.action ∘ T₁ π₂) ⟩
        ≈⟨ ⟨⟩-cong₂ (∘-resp-≈ʳ T₁-pres-∘) (∘-resp-≈ʳ T₁-pres-∘) ⟩
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
