{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame

module Presheaf.Properties
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (IF   : IFrame W _⊆_)
  where

open import Presheaf.Base IF

open IFrame IF

open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (isEquivalence to ≡-equiv)
import Relation.Binary.Reasoning.Setoid as EqReasoning

private
  variable
    w w' w'' v v' v'' : W
    𝒫 𝒫' 𝒬 𝒬' : Psh

--
-- 
--

-⊇_ : W → Psh
-⊇ w = record
  { Fam           = w ⊆_
  ; _≋_           = _≡_
  ; ≋-equiv       = λ _ → ≡-equiv
  ; wk            = λ i i' → ⊆-trans i' i
  ; wk-pres-≋     = λ i x≋y → cong₂ ⊆-trans x≋y ≡-refl
  ; wk-pres-refl  = ⊆-trans-unit-right
  ; wk-pres-trans = λ i' i'' i → ≡-sym (⊆-trans-assoc i i' i'')
  }

-⊇-mapᵒ : w ⊆ w' → -⊇ w' →̇ -⊇ w
-⊇-mapᵒ {w} i = record
  { fun     = ⊆-trans i
  ; pres-≋  = cong (⊆-trans i)
  ; natural = λ i' i'' → ⊆-trans-assoc i i'' i'
  }

opaque
  -⊇-mapᵒ-pres-refl : -⊇-mapᵒ ⊆-refl[ w ] ≈̇ id'
  -⊇-mapᵒ-pres-refl = record { proof = ⊆-trans-unit-left }

  -⊇-mapᵒ-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') → -⊇-mapᵒ (⊆-trans i i') ≈̇ -⊇-mapᵒ i ∘ -⊇-mapᵒ i'
  -⊇-mapᵒ-pres-trans i i' = record { proof = ⊆-trans-assoc i i' }

--
-- The comonad ◻ᵢ
--

-- Intuition: for all intuitionistic futures
◻ᵢ_ : Psh → Psh
◻ᵢ 𝒫 = record
  { Fam           = λ w → Hom (-⊇ w) 𝒫
  ; _≋_           = _≈̇_
  ; ≋-equiv       = λ _ → ≈̇-equiv
  ; wk            = λ i f → f ∘ (-⊇-mapᵒ i)
  ; wk-pres-≋     = λ i x≋y → ∘-pres-≈̇-left x≋y (-⊇-mapᵒ i)
  ; wk-pres-refl  = λ f → ≈̇-trans (∘-pres-≈̇-right f -⊇-mapᵒ-pres-refl) (∘-unit-right _ f)
  ; wk-pres-trans = λ i i' f → ≈̇-trans (∘-pres-≈̇-right f (-⊇-mapᵒ-pres-trans i i')) (≈̇-sym (∘-assoc f (-⊇-mapᵒ i) (-⊇-mapᵒ i')) )
  }

◻ᵢ-map_ : {𝒫 𝒬 : Psh} → (t : 𝒫 →̇ 𝒬) → (◻ᵢ 𝒫 →̇ ◻ᵢ 𝒬)
◻ᵢ-map_ {𝒫} {𝒬} t = record
 { fun     = t ∘_
 ; pres-≋  = ∘-pres-≈̇-right t
 ; natural = λ i f → record { proof = λ d → ≋[ 𝒬 ]-refl }
 }

opaque
  ◻ᵢ-map-pres-≈̇ : {𝒫 𝒬 : Psh} {f g : 𝒫 →̇ 𝒬} → f ≈̇ g → ◻ᵢ-map f ≈̇ ◻ᵢ-map g
  ◻ᵢ-map-pres-≈̇ f≈̇g = record { proof = ∘-pres-≈̇-left f≈̇g }

  ◻ᵢ-map-pres-id : {𝒫 : Psh} → ◻ᵢ-map id'[ 𝒫 ] ≈̇ id'
  ◻ᵢ-map-pres-id = record { proof = ∘-unit-left _ }

  ◻ᵢ-map-pres-∘ : {𝒫 𝒬 ℛ : Psh} (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → ◻ᵢ-map (t' ∘ t) ≈̇ ◻ᵢ-map t' ∘ ◻ᵢ-map t
  ◻ᵢ-map-pres-∘ {𝒫} {ℛ = ℛ} t' t = record { proof = ∘-assoc t' t }

-- wk[_] with arguments flipped
wk[_]' : ∀ 𝒫 → 𝒫 →̇ ◻ᵢ 𝒫
wk[_]' 𝒫 = record
  { fun     = λ p → record
    { fun     = λ i → wk[ 𝒫 ] i p
    ; pres-≋  = λ i≋i' → wk[ 𝒫 ]-pres-≡-≋ i≋i' ≋[ 𝒫 ]-refl
    ; natural = λ i i' → ≋[ 𝒫 ]-sym (wk[ 𝒫 ]-pres-trans i' i p)
    }
  ; pres-≋  = λ p≋p' → record { proof = λ i → wk[ 𝒫 ]-pres-≋ i p≋p' }
  ; natural = λ i p → record { proof = λ i' → wk[ 𝒫 ]-pres-trans i i' p }
  }

wk'-natural : (t : 𝒫 →̇ 𝒬) → wk[ 𝒬 ]' ∘ t ≈̇ (◻ᵢ-map t) ∘ wk[ 𝒫 ]'
wk'-natural t = record { proof = λ p → record { proof = λ i → t .natural i p } }

copointᵢ[_] : ∀ 𝒫 → ◻ᵢ 𝒫 →̇ 𝒫
copointᵢ[ 𝒫 ] = record
  { fun = λ f → f .apply ⊆-refl
  ; pres-≋ = λ f≋f' → f≋f' .apply-≋ ⊆-refl
  ; natural = λ i f → ≋[ 𝒫 ]-trans (f .natural i ⊆-refl) (f .apply-≋ (⊆-trans-unit i))
  }

-- TODO: cojoinᵢ[_]
