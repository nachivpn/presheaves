{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame
import Kripke.FDFrame as FDF

module Presheaf.Functor.Possibility.Properties
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  {IF   : IFrame W _⊆_}
  {_R_  : (w v : W) → Set}
  (let open FDF IF _R_)
  (DF   : DFrame)
  where

open import Presheaf.Base IF
open import Presheaf.Properties IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Possibility.Base DF

open DFrame DF
open import Kripke.FDFrame.Properties DF

open import PUtil

open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (isEquivalence to ≡-equiv)

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

private
  variable
    w w' w'' v v' v''     : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' ℛ'' : Psh

-------------------------------------
-- Presheaf determined by relation D
-------------------------------------

-D_ : (v : W) → Psh
-D v = ◇ (-⊇ v)

-D-mapᵒ_ : w ⊆ v → (-D v) →̇ (-D w)
-D-mapᵒ i = ◇-map (-⊇-mapᵒ i)

opaque
  -D-mapᵒ-pres-refl : -D-mapᵒ ⊆-refl[ w ] ≈̇ id'
  -D-mapᵒ-pres-refl = ≈̇-trans (◇-map-pres-≈̇ -⊇-mapᵒ-pres-refl) ◇-map-pres-id

  -D-mapᵒ-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') → -D-mapᵒ (⊆-trans i i') ≈̇ -D-mapᵒ i ∘ -D-mapᵒ i'
  -D-mapᵒ-pres-trans i i' = ≈̇-trans (◇-map-pres-≈̇ (-⊇-mapᵒ-pres-trans i i')) (◇-map-pres-∘ (-⊇-mapᵒ i) (-⊇-mapᵒ i'))

-- observe:
_ : w D v → -D v ₀ w
_ = elem

_ : -D v ₀ w → w D v
_ = triple

-------------------------
-- ◼ is presheaf functor
-------------------------

-- For all D-pasts
◼_ : Psh → Psh
◼_ 𝒫 = record
  { Fam           = λ v → Hom (-D v) 𝒫
  ; _≋_           = _≈̇_
  ; ≋-equiv       = λ _ → ≈̇-equiv
  ; wk            = λ i f → f ∘ -D-mapᵒ i
  ; wk-pres-≋     = wk-pres-≋
  ; wk-pres-refl  = wk-pres-refl
  ; wk-pres-trans = wk-pres-trans
  }
  where
    opaque
      wk-pres-≋ : (i : w ⊆ v) {x y : Hom (-D w) 𝒫} → x ≈̇ y → x ∘ -D-mapᵒ i ≈̇ y ∘ -D-mapᵒ i
      wk-pres-≋ i x≋y = ∘-pres-≈̇-left x≋y (-D-mapᵒ i)

      wk-pres-refl : (f : Hom (-D w) 𝒫) → f ∘ -D-mapᵒ ⊆-refl ≈̇ f
      wk-pres-refl f = ≈̇-trans (∘-pres-≈̇-right f -D-mapᵒ-pres-refl) (∘-unit-right _ f)

      wk-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (f : Hom (-D w) 𝒫) → f ∘ -D-mapᵒ (⊆-trans i i') ≈̇ (f ∘ -D-mapᵒ i) ∘ -D-mapᵒ i'
      wk-pres-trans i i' f = ≈̇-trans (∘-pres-≈̇-right f (-D-mapᵒ-pres-trans i i')) (≈̇-sym (∘-assoc f (-D-mapᵒ i) (-D-mapᵒ i')) )

-- made opaque to speedup type-checking and relying on implementation details
opaque
  ◼-map_ : {𝒫 𝒬 : Psh} → (t : 𝒫 →̇ 𝒬) → (◼ 𝒫 →̇ ◼ 𝒬)
  ◼-map_ {𝒫} {𝒬} t = record
    { fun     = t ∘_
    ; pres-≋  = ∘-pres-≈̇-right t
    ; natural = ◼-map-fun-natural
    }
    where
      opaque
        ◼-map-fun-natural : Natural (◼ 𝒫) (◼ 𝒬) (t ∘_)
        ◼-map-fun-natural i f = proof-≈̇ (λ d → ≋[ 𝒬 ]-refl)

  ◼-map-pres-≈̇ : {𝒫 𝒬 : Psh} {f g : 𝒫 →̇ 𝒬} → f ≈̇ g → ◼-map f ≈̇ ◼-map g
  ◼-map-pres-≈̇ f≈̇g = proof-≈̇ (∘-pres-≈̇-left f≈̇g)

  ◼-map-pres-id : {𝒫 : Psh} → ◼-map id'[ 𝒫 ] ≈̇ id'
  ◼-map-pres-id = proof-≈̇ (∘-unit-left _)

  ◼-map-pres-∘ : {𝒫 𝒬 ℛ : Psh} (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → ◼-map (t' ∘ t) ≈̇ ◼-map t' ∘ ◼-map t
  ◼-map-pres-∘ t' t = proof-≈̇ (∘-assoc t' t)

---------
-- ◇ ⊣ ◼
---------

--
-- Intuition for η:
-- If p holds now, then for all pasts there exists a future where p holds
--
η[_] : ∀ 𝒫 → 𝒫 →̇ ◼ ◇ 𝒫
η[ 𝒫 ] = record
  { fun     = η-fun
  ; pres-≋  = η-pres-≋
  ; natural = η-natural
  }
  where
    η-fun : 𝒫 ₀ w → (◼ (◇ 𝒫)) ₀ w
    η-fun p = ◇-map (wk[ 𝒫 ]' .apply p)

    opaque
      η-pres-≋ : Pres-≋ 𝒫 (◼ (◇ 𝒫)) η-fun
      η-pres-≋ p≋p' = ◇-map-pres-≈̇ (wk[ 𝒫 ]' .apply-≋ p≋p')

      η-natural : Natural 𝒫 (◼ (◇ 𝒫)) η-fun
      η-natural {w} i p = ≈̇-trans
        (≈̇-sym (◇-map-pres-∘ (wk[ 𝒫 ]' .apply p) (-⊇-mapᵒ i)))
        (◇-map-pres-≈̇ (wk[ 𝒫 ]' .natural i p))

opaque
  unfolding ◼-map_ ◇-map_

  η-natural : (t : 𝒫 →̇ 𝒬) → η[ 𝒬 ] ∘ t ≈̇ ◼-map (◇-map t) ∘ η[ 𝒫 ]
  η-natural {𝒫} {𝒬} t = proof-≈̇ (λ p → proof-≈̇ (λ (elem (_ , _ , i)) → proof (≡-refl , ≡-refl , t .natural i p)))

--
-- Intuition for ϵ:
-- If p holds in the future for all pasts, then p holds now
--

ϵ[_] : ∀ 𝒫 → ◇ ◼ 𝒫 →̇ 𝒫
ϵ[ 𝒫 ] = record
  { fun     = ϵ-fun
  ; pres-≋  = ϵ-pres-≋
  ; natural = ϵ-natural
  }
  where
    ϵ-fun : ◇-Fam (◼ 𝒫) w → 𝒫 ₀ w
    ϵ-fun (elem (v , r , f)) = f .apply (elem (R-to-D r))

    opaque
      unfolding ◇-map_

      ϵ-pres-≋ : Pres-≋ (◇ (◼ 𝒫)) 𝒫 ϵ-fun
      ϵ-pres-≋ (proof (≡-refl , ≡-refl , f≋f')) = apply-≈̇' f≋f' ◇-≋-refl

      ϵ-natural : Natural (◇ (◼ 𝒫)) 𝒫 ϵ-fun
      ϵ-natural i (elem (v , r , f)) = ≋[ 𝒫 ]-trans
        (f .natural i (elem (R-to-D r)))
        (f .apply-≋ (proof (-, ≡-refl , ⊆-trans-unit _)))

opaque
  unfolding ◼-map_ ◇-map_

  ϵ-natural : (t : 𝒫 →̇ 𝒬) → t ∘ ϵ[ 𝒫 ] ≈̇ ϵ[ 𝒬 ] ∘ (◇-map (◼-map t))
  ϵ-natural {𝒫} {𝒬} t = proof-≈̇ (λ p → ≋[ 𝒬 ]-refl)

η = λ {𝒫} → η[ 𝒫 ]
ϵ = λ {𝒫} → ϵ[ 𝒫 ]

opaque
  unfolding ◼-map_ ◇-map_

  zig-zag₁ : ϵ[ ◇ 𝒫 ] ∘ ◇-map η[ 𝒫 ] ≈̇  id'[ ◇ 𝒫 ]
  zig-zag₁ {𝒫} = proof-≈̇ (λ _p
    → proof (≡-refl , ≡-refl , wk[ 𝒫 ]-pres-refl _))

  zig-zag₂ : ◼-map ϵ[ 𝒫 ] ∘ η[ ◼ 𝒫 ] ≈̇ id'[ ◼ 𝒫 ]
  zig-zag₂ {𝒫} = proof-≈̇ λ bp → proof-≈̇ λ d
    → bp .apply-≋ (proof (≡-refl , ≡-refl , ⊆-trans-unit-right _))

--
-- Hom-set based characterisation of the adjunction
--

module HomAdj where

  box : (◇ 𝒫 →̇ 𝒬) → (𝒫 →̇ ◼ 𝒬)
  box {𝒫} {𝒬} t = ◼-map t ∘ η[ 𝒫 ]

  unbox : (𝒫 →̇ ◼ 𝒬) → (◇ 𝒫 →̇ 𝒬)
  unbox {𝒫} {𝒬} t = ϵ[ 𝒬 ] ∘ ◇-map t

  opaque
    box-natural : (t : ◇ 𝒫 →̇ 𝒬) (u : 𝒫' →̇ 𝒫) → box t ∘ u ≈̇ box (t ∘ (◇-map u))
    box-natural {𝒫} {𝒬} {𝒫'} t u = let open EqReasoning (→̇-setoid 𝒫' (◼ 𝒬)) in begin
      (◼-map t ∘ η[ 𝒫 ]) ∘ u
        ≈⟨ ∘-assoc (◼-map t) η u ⟩
      ◼-map t ∘ (η[ 𝒫 ] ∘ u)
        ≈⟨ ∘-pres-≈̇-right (◼-map t) (η-natural u) ⟩
      ◼-map t ∘ (◼-map (◇-map u) ∘ η[ 𝒫' ])
        ≈˘⟨ ∘-assoc (◼-map t) (◼-map (◇-map u)) η[ 𝒫' ] ⟩
      (◼-map t ∘ ◼-map (◇-map u)) ∘ η[ 𝒫' ]
        ≈˘⟨ ∘-pres-≈̇-left (◼-map-pres-∘ t (◇-map u)) η[ 𝒫' ] ⟩
      ◼-map (t ∘ ◇-map u) ∘ η[ 𝒫' ]
        ∎
