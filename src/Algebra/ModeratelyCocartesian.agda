open import Algebra.Lib

module Algebra.ModeratelyCocartesian {𝒞 : Category} (T : Monad 𝒞) (cocartesian : Cocartesian 𝒞)  where

open import Algebra.Category T

open 𝒞
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
module _ {Z Z' : Algebra} (h⇒ : Algebra⇒ Z Z') where

  open Algebra⇒ h⇒ renaming (arr to ∣h∣ ; commute to ∣h∣-hom)

  private
    module Z = Algebra Z
    module Z' = Algebra Z'
    ∣Z∣ = Z.A ; ∣Z'∣ = Z'.A
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
      ≈˘⟨ ∘-resp-≈ʳ T₁-pres-∘ ⟩
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


    ∘̃-distribˡ-[]∼ : h ∘̃ [ f , g ]∼ ≈̃ [ h ∘̃ f , h ∘̃ g ]∼
    ∘̃-distribˡ-[]∼ = let open 𝒞.HomReasoning in begin
      ∣h∣ ∘ Z.action ∘ T₁ [ ∣f∣ , ∣g∣ ]
        ≈⟨ sym-assoc ⟩
      (∣h∣ ∘ Z.action) ∘ T₁ [ ∣f∣ , ∣g∣ ]
        -- algebra T₁-pres-∘
        ≈⟨ ∘-resp-≈ˡ ∣h∣-hom ⟩
      (Z'.action ∘ T₁ ∣h∣) ∘ T₁ [ ∣f∣ , ∣g∣ ]
        ≈⟨ assoc ⟩
      Z'.action ∘ T₁ ∣h∣ ∘ T₁ [ ∣f∣ , ∣g∣ ]
        ≈˘⟨ ∘-resp-≈ʳ T₁-pres-∘ ⟩
      Z'.action ∘ T₁ (∣h∣ ∘ [ ∣f∣ , ∣g∣ ])
        -- uniqueness of underlying coproduct
        ≈⟨ ∘-resp-≈ʳ (T₁-resp-≈ ∘-distribˡ-[]) ⟩
      Z'.action ∘ T₁ [ ∣h∣ ∘ ∣f∣ , ∣h∣ ∘ ∣g∣ ]
        ∎

    -- permutation conversions for sum types
    π̃₊ᴱ = ∘̃-distribˡ-[]∼
