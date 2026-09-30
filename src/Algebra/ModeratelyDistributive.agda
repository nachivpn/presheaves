open import Algebra.Lib

open import Categories.Category.Monoidal.Core
open import Categories.Category.Cartesian.Monoidal

module Algebra.ModeratelyDistributive {𝒞 : Category} (T : Monad 𝒞)
  (distributive : Distributive 𝒞)
  (let open Distributive distributive)
  (let open CartesianMonoidal cartesian using (monoidal))
  (strength : Strength monoidal T)
  where

-- my modules
open import Algebra.Category T
open import Algebra.Cartesian T cartesian
open import Algebra.ModeratelyCocartesian T cocartesian

-- cat lib
open 𝒞
open Strength strength
str = strengthen.η


open Cartesian cartesian∼ using () renaming (_×₁_ to _×̃₁_)

-- (implicit arguments create too much noise here)
module Distr (G X Y : Algebra) where
  private
    module G = Algebra G ; ∣G∣ = G.A
    module X = Algebra X ; ∣X∣ = X.A
    module Y = Algebra Y ; ∣Y∣ = Y.A

  ×̃-distr-+̃ : G ×̃ (X +̃ Y) ⇒̃ (G ×̃ X) +̃ (G ×̃ Y)
  ×̃-distr-+̃ = plain (T₁ distributeˡ⁻¹ ∘ str (∣G∣ , ∣X∣ + ∣Y∣))

  module _ {Z : Algebra} where
    private
      module Z = Algebra Z ; ∣Z∣ = Z.A

    -- a distributive version of [_,_]∼
    [_,_]ᵈ∼ : G ×̃ X ⇒̃ Z → G ×̃ Y ⇒̃ Z → G ×̃ (X +̃ Y) ⇒̃ Z
    [ f , g ]ᵈ∼ = [ f , g ]∼ ∘̃ ×̃-distr-+̃

module _ {G X Y Z Z' : Algebra} (h⇒ : Algebra⇒ Z Z') where
  open Algebra⇒ h⇒ renaming (arr to ∣h∣ ; commute to ∣h∣-hom)

  private
    h : Z ⇒̃ Z'
    h = plain ∣h∣

  open Distr G X Y

  ∘̃-distribˡ-[]ᵈ∼ : (f : G ×̃ X ⇒̃ Z) (g : G ×̃ Y ⇒̃ Z)
    → h ∘̃ [ f , g ]ᵈ∼ ≈̃ [ h ∘̃ f , h ∘̃ g ]ᵈ∼
  ∘̃-distribˡ-[]ᵈ∼ f g = let open 𝒞̃.HomReasoning in begin
    h ∘̃ [ f , g ]∼ ∘̃ ×̃-distr-+̃
      ≈˘⟨ 𝒞̃.assoc {f = ×̃-distr-+̃}  {h = h}⟩
    (h ∘̃ [ f , g ]∼) ∘̃ ×̃-distr-+̃
      -- uses underlying (left) distributivity of ∘̃ over [_,_]∼
      ≈⟨ 𝒞̃.∘-resp-≈ˡ {f = h ∘̃ [ f , g ]∼} {g = ×̃-distr-+̃} (∘̃-distribˡ-[]∼ h⇒ f g) ⟩
    [ h ∘̃ f , h ∘̃ g ]∼ ∘̃ ×̃-distr-+̃
      ≡⟨⟩
    [ h ∘̃ f , h ∘̃ g ]ᵈ∼
      ∎
