{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame

module Presheaf.Properties
  {W    : Set}
  {_⊑_  : (w w' : W) → Set}
  (IF   : IFrame W _⊑_)
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
  { Fam           = w ⊑_
  ; _≋_           = _≡_
  ; ≋-equiv       = λ _ → ≡-equiv
  ; wk            = λ i i' → ⊑-trans i' i
  ; wk-pres-≋     = wk-pres-≋
  ; wk-pres-refl  = wk-pres-refl
  ; wk-pres-trans = wk-pres-trans
  }
  where
    opaque
      wk-pres-≋ : {w w' v : W} (i' : w' ⊑ v) {i1 i2 : w ⊑ w'} → i1 ≡ i2 → ⊑-trans i1 i' ≡ ⊑-trans i2 i'
      wk-pres-≋ i x≋y = cong₂ ⊑-trans x≋y ≡-refl

      wk-pres-refl : {w w' : W} (i : w ⊑ w') → ⊑-trans i ⊑-refl ≡ i
      wk-pres-refl = ⊑-trans-unit-right

      wk-pres-trans : (i : w' ⊑ v) (i' : v ⊑ v') (x : w ⊑ w') → ⊑-trans x (⊑-trans i i') ≡ ⊑-trans (⊑-trans x i) i'
      wk-pres-trans i' i'' i = ≡-sym (⊑-trans-assoc i i' i'')

-- deliberately not opaque (causes too many unfoldings, especially at higher levels of abstraction)
-- seems harmless on type-checking performance
-⊇-mapᵒ_ : w ⊑ w' → -⊇ w' →̇ -⊇ w
-⊇-mapᵒ_ {w} {w'} i = record
  { fun     = ⊑-trans i
  ; pres-≋  = -⊇-mapᵒ-pres-≋
  ; natural = -⊇-mapᵒ-natural
  }
  where
    opaque
      -⊇-mapᵒ-pres-≋ : Pres-≋ (-⊇ w') (-⊇ w) (⊑-trans i)
      -⊇-mapᵒ-pres-≋ = cong (⊑-trans i)

      -⊇-mapᵒ-natural : Natural (-⊇ w') (-⊇ w) (⊑-trans i)
      -⊇-mapᵒ-natural i' i'' = ⊑-trans-assoc i i'' i'

opaque
  -⊇-mapᵒ-pres-refl : -⊇-mapᵒ ⊑-refl[ w ] ≈̇ id'
  -⊇-mapᵒ-pres-refl = proof-≈̇ ⊑-trans-unit-left

  -⊇-mapᵒ-pres-trans : (i : w ⊑ w') (i' : w' ⊑ w'') → -⊇-mapᵒ (⊑-trans i i') ≈̇ -⊇-mapᵒ i ∘' -⊇-mapᵒ i'
  -⊇-mapᵒ-pres-trans i i' = proof-≈̇ (⊑-trans-assoc i i')

--
-- The comonad ◻ᵢ
--

-- Intuition: for all intuitionistic futures
◻ᵢ_ : Psh → Psh
◻ᵢ 𝒫 = record
  { Fam           = λ w → Hom (-⊇ w) 𝒫
  ; _≋_           = _≈̇_
  ; ≋-equiv       = λ _ → ≈̇-equiv
  ; wk            = λ i f → f ∘' (-⊇-mapᵒ i)
  ; wk-pres-≋     = wk-pres-≋
  ; wk-pres-refl  = wk-pres-refl
  ; wk-pres-trans = wk-pres-trans
  }
  where
    opaque
      wk-pres-≋ : (i : w ⊑ v) {f g : Hom (-⊇ w) 𝒫} → f ≈̇ g → f ∘' -⊇-mapᵒ i ≈̇ g ∘' -⊇-mapᵒ i
      wk-pres-≋ i x≋y = ∘'-pres-≈̇-left x≋y (-⊇-mapᵒ i)

      wk-pres-refl : (f : Hom (-⊇ w) 𝒫) → f ∘' -⊇-mapᵒ ⊑-refl ≈̇ f
      wk-pres-refl f = ≈̇-trans (∘'-pres-≈̇-right f -⊇-mapᵒ-pres-refl) (∘'-unit-right _ f)

      wk-pres-trans : (i : w ⊑ w') (i' : w' ⊑ w'') (f : Hom (-⊇ w) 𝒫) → f ∘' -⊇-mapᵒ (⊑-trans i i') ≈̇ (f ∘' -⊇-mapᵒ i) ∘' -⊇-mapᵒ i'
      wk-pres-trans i i' f = ≈̇-trans (∘'-pres-≈̇-right f (-⊇-mapᵒ-pres-trans i i')) (≈̇-sym (∘'-assoc f (-⊇-mapᵒ i) (-⊇-mapᵒ i')) )


opaque
  ◻ᵢ-map_ : {𝒫 𝒬 : Psh} → (t : 𝒫 →̇ 𝒬) → (◻ᵢ 𝒫 →̇ ◻ᵢ 𝒬)
  ◻ᵢ-map_ {𝒫} {𝒬} t = record
    { fun     = t ∘'_
    ; pres-≋  = ∘'-pres-≈̇-right t
    ; natural = λ i f → proof-≈̇ (λ d → ≋[ 𝒬 ]-refl)
    }

  ◻ᵢ-map-pres-≈̇ : {𝒫 𝒬 : Psh} {f g : 𝒫 →̇ 𝒬} → f ≈̇ g → ◻ᵢ-map f ≈̇ ◻ᵢ-map g
  ◻ᵢ-map-pres-≈̇ f≈̇g = proof-≈̇ (∘'-pres-≈̇-left f≈̇g)

  ◻ᵢ-map-pres-id : {𝒫 : Psh} → ◻ᵢ-map id'[ 𝒫 ] ≈̇ id'
  ◻ᵢ-map-pres-id = proof-≈̇ (∘'-unit-left _)

  ◻ᵢ-map-pres-∘' : {𝒫 𝒬 ℛ : Psh} (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → ◻ᵢ-map (t' ∘' t) ≈̇ ◻ᵢ-map t' ∘' ◻ᵢ-map t
  ◻ᵢ-map-pres-∘' t' t = proof-≈̇ (∘'-assoc t' t)


-- wk[_] with arguments flipped
wk[_]' : ∀ 𝒫 → 𝒫 →̇ ◻ᵢ 𝒫
wk[_]' 𝒫 = record
  { fun     = wk'-fun
  ; pres-≋  = wk'-pres-≋
  ; natural = wk'-natural
  }
  where
    wk'-fun : 𝒫 ₀ w → (◻ᵢ 𝒫) ₀ w
    wk'-fun p = record
      { fun     = λ i → wk[ 𝒫 ] i p
      ; pres-≋  = λ i≋i' → wk[ 𝒫 ]-pres-≡-≋ i≋i' ≋[ 𝒫 ]-refl
      ; natural = λ i i' → ≋[ 𝒫 ]-sym (wk[ 𝒫 ]-pres-trans i' i p)
      }

    opaque
      wk'-pres-≋ : Pres-≋ 𝒫 (◻ᵢ 𝒫) wk'-fun
      wk'-pres-≋ p≋p' = proof-≈̇ (λ i → wk[ 𝒫 ]-pres-≋ i p≋p')

      wk'-natural : Natural 𝒫 (◻ᵢ 𝒫) wk'-fun
      wk'-natural i p = proof-≈̇ (λ i' → wk[ 𝒫 ]-pres-trans i i' p)

opaque
  unfolding ◻ᵢ-map_

  wk'-natural : (t : 𝒫 →̇ 𝒬) → wk[ 𝒬 ]' ∘' t ≈̇ (◻ᵢ-map t) ∘' wk[ 𝒫 ]'
  wk'-natural t = proof-≈̇ (λ p → proof-≈̇ (λ i → t .natural i p))

copointᵢ[_] : ∀ 𝒫 → ◻ᵢ 𝒫 →̇ 𝒫
copointᵢ[ 𝒫 ] = record
  { fun     = copoint-fun
  ; pres-≋  = copoint-pres-≋
  ; natural = copoint-natural -- λ
  }
  where
    copoint-fun : (◻ᵢ 𝒫) ₀ w → 𝒫 ₀ w
    copoint-fun = λ f → f .apply ⊑-refl

    opaque

      copoint-pres-≋ : Pres-≋ (◻ᵢ 𝒫) 𝒫 copoint-fun
      copoint-pres-≋ {_} {f} {f'} = λ f≋f' → apply-≈̇' f≋f' ≡-refl

      copoint-natural :  Natural (◻ᵢ 𝒫) 𝒫 (copoint-fun)
      copoint-natural i f = ≋[ 𝒫 ]-trans (f .natural i ⊑-refl) (f .apply-≋ (⊑-trans-unit i))

-- TODO: cojoinᵢ[_]
