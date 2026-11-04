{-# OPTIONS --safe --without-K #-}

module Family.Monad (W : Set) where

open import Family.Base W
open import Family.CartesianClosure W

open import PUtil

open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans ; subst to ≡-subst ; cong to ≡-cong)
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (isEquivalence to ≡-equiv)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Data.Product using (∃; Σ; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

private
  variable
    w w' w'' v v' v''     : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' ℛ'' : Psh

-- Cover system
record 𝒞𝒮 : Set₁ where
  field
    -- components
    𝒞₀     : Psh → Psh
    iden   : 𝒫 →̇ 𝒞₀ 𝒫
    trans  : 𝒫 →̇ 𝒞₀ 𝒬 → 𝒞₀ 𝒫 →̇ 𝒞₀ 𝒬 -- "kleisli extension"

    -- setoid condition
    trans-pres-≈ : {f f' : 𝒫 →̇ 𝒞₀ 𝒬} → f ≈̇ f' → trans f ≈̇ trans f'

    -- "kleisli laws"
    trans-assoc      : (f : 𝒬 →̇ 𝒞₀ ℛ) (g : 𝒫 →̇ 𝒞₀ 𝒬) → trans (trans f ∘' g) ≈̇ trans f ∘' trans g
    trans-unit-right : trans {𝒫} iden ≈̇ id'
    trans-unit-left  : (f : 𝒫 →̇ 𝒞₀ 𝒬) → trans f ∘' iden ≈̇ f

  𝒞₁ : 𝒫 →̇ 𝒬 → 𝒞₀ 𝒫 →̇ 𝒞₀ 𝒬
  𝒞₁ f = trans (iden ∘' f)

  𝒞₁-pres-≈ : {f f' : 𝒫 →̇ 𝒬} → f ≈̇ f' → 𝒞₁ f ≈̇ 𝒞₁ f'
  𝒞₁-pres-≈ f≈f' = trans-pres-≈ (∘'-pres-≈̇-right iden f≈f')

  𝒞₁-pres-id : 𝒞₁ (id' {𝒫}) ≈̇ id'
  𝒞₁-pres-id {𝒫} = ≈̇-trans (trans-pres-≈ (∘'-unit-right 𝒫 iden)) trans-unit-right

  𝒞₁-pres-∘' : (f : 𝒫 →̇ 𝒬) (g : 𝒬 →̇ ℛ) → 𝒞₁ (g ∘' f) ≈̇ 𝒞₁ g ∘' 𝒞₁ f
  𝒞₁-pres-∘' f g = let open EqReasoning (→̇-setoid _ _) in begin
    𝒞₁ (g ∘' f)
      ≡⟨⟩
    trans (iden ∘' g ∘' f)
      ≈˘⟨ trans-pres-≈ (∘'-assoc iden g f) ⟩
    trans ((iden ∘' g) ∘' f)
      ≈˘⟨ trans-pres-≈ (∘'-pres-≈̇-left (trans-unit-left (iden ∘' g)) f) ⟩
    trans ((trans (iden ∘' g) ∘' iden) ∘' f)
      ≈⟨ trans-pres-≈ (∘'-assoc (trans (iden ∘' g)) iden f) ⟩
    trans (trans (iden ∘' g) ∘' iden ∘' f)
      ≈⟨ trans-assoc (iden ∘' g) (iden ∘' f) ⟩
    trans (iden ∘' g) ∘' trans (iden ∘' f)
      ≡⟨⟩
    𝒞₁ g ∘' 𝒞₁ f
      ∎

  trans-natʳ : (f : 𝒬 →̇ 𝒬') (g : 𝒫 →̇ 𝒞₀ 𝒬) → 𝒞₁ f ∘' trans g ≈̇ trans (𝒞₁ f ∘' g)
  trans-natʳ f g = ≈̇-sym (trans-assoc (iden ∘' f) g)

  trans-natˡ : (f : 𝒫' →̇ 𝒫) (g : 𝒫 →̇ 𝒞₀ 𝒬) → trans g ∘' 𝒞₁ f ≈̇ trans (g ∘' f)
  trans-natˡ f g = let open EqReasoning (→̇-setoid _ _) in begin
    trans g ∘' 𝒞₁ f
      ≡⟨⟩
    trans g ∘' trans (iden ∘' f)
      ≈˘⟨ trans-assoc g (iden ∘' f) ⟩
    trans (trans g ∘' iden ∘' f)
      ≈˘⟨ trans-pres-≈ (∘'-assoc (trans g) iden f) ⟩
    trans ((trans g ∘' iden) ∘' f)
      ≈⟨ trans-pres-≈ (∘'-pres-≈̇-left (trans-unit-left g) f) ⟩
    trans (g ∘' f)
      ∎

  point : 𝒫 →̇ 𝒞₀ 𝒫
  point = iden

  point[_] : ∀ 𝒫 → 𝒫 →̇ 𝒞₀ 𝒫
  point[ 𝒫 ] = point

  point-natural : (f : 𝒫 →̇ 𝒬) → 𝒞₁ f ∘' point[ 𝒫 ] ≈̇ point[ 𝒬 ] ∘' f
  point-natural {𝒫} {𝒬} f = let open EqReasoning (→̇-setoid _ _) in begin
    𝒞₁ f ∘' point
      ≡⟨⟩
    trans (point ∘' f) ∘' point
      ≈⟨ trans-unit-left (point ∘' f) ⟩
    point ∘' f
      ∎

  join : 𝒞₀ (𝒞₀ 𝒫) →̇ 𝒞₀ 𝒫
  join = trans id'

  join[_] : ∀ 𝒫 → 𝒞₀ (𝒞₀ 𝒫) →̇ 𝒞₀ 𝒫
  join[ 𝒫 ] = join

  join-natural : (f : 𝒫 →̇ 𝒬) → join[ 𝒬 ] ∘' 𝒞₁ (𝒞₁ f) ≈̇ 𝒞₁ f ∘' join[ 𝒫 ]
  join-natural {𝒫} {𝒬} f = let open EqReasoning (→̇-setoid _ _) in begin
    join[ 𝒬 ] ∘' (𝒞₁ (𝒞₁ f))
      ≡⟨⟩
    trans id' ∘' (𝒞₁ (𝒞₁ f))
      ≈⟨ trans-natˡ (𝒞₁ f) id' ⟩
    trans (id' ∘' 𝒞₁ f)
      ≈⟨ trans-pres-≈ (∘'-unit-left (𝒞₀ 𝒬) (𝒞₁ f)) ⟩
    trans (𝒞₁ f)
      ≈˘⟨ trans-pres-≈ (∘'-unit-right (𝒞₀ 𝒫) (𝒞₁ f)) ⟩
    trans (𝒞₁ f ∘' id')
      ≈˘⟨ trans-natʳ f id' ⟩
    𝒞₁ f ∘' trans id'
      ≡⟨⟩
    𝒞₁ f ∘' join[ 𝒫 ]
      ∎

  join-assoc : join[ 𝒫 ] ∘' 𝒞₁ join[ 𝒫 ] ≈̇ join[ 𝒫 ] ∘' join[ 𝒞₀ 𝒫 ]
  join-assoc {𝒫} = let open EqReasoning (→̇-setoid _ _) in begin
    join[ 𝒫 ] ∘' 𝒞₁ join[ 𝒫 ]
      ≡⟨⟩
    trans id' ∘' 𝒞₁ (trans id')
      ≈⟨ trans-natˡ (trans id') id' ⟩
    trans (id' ∘' trans id')
      ≈⟨ trans-pres-≈ (∘'-unit-left (𝒞₀ 𝒫) (trans id')) ⟩
    trans (trans id')
      ≈˘⟨ trans-pres-≈ (∘'-unit-right (𝒞₀ (𝒞₀ 𝒫)) (trans id')) ⟩
    trans (trans id' ∘' id')
      ≈⟨ trans-assoc id' id' ⟩
    trans id' ∘' trans id'
      ≡⟨⟩
    join[ 𝒫 ] ∘' join[ 𝒞₀ 𝒫 ]
      ∎

  join-unit-left : join[ 𝒫 ] ∘' point[ 𝒞₀ 𝒫 ] ≈̇ id'[ 𝒞₀ 𝒫 ]
  join-unit-left {𝒫} = trans-unit-left id'

  join-unit-right : join[ 𝒫 ] ∘' 𝒞₁ point[ 𝒫 ] ≈̇ id'[ 𝒞₀ 𝒫 ]
  join-unit-right {𝒫} = let open EqReasoning (→̇-setoid _ _) in begin
    join ∘' 𝒞₁ point
      ≡⟨⟩
    trans id' ∘' trans (iden ∘' iden)
      ≈˘⟨ ∘'-pres-≈̇-left (trans-pres-≈ trans-unit-right) (trans (iden ∘' iden)) ⟩
    trans (trans iden) ∘' trans (iden ∘' iden)
      ≈˘⟨ trans-assoc (trans iden) (iden ∘' iden) ⟩
    trans (trans (trans iden) ∘' iden ∘' iden)
      ≈˘⟨ trans-pres-≈ (∘'-assoc (trans (trans iden)) iden iden) ⟩
    trans ((trans (trans iden) ∘' iden) ∘' iden)
      ≈⟨ trans-pres-≈ (∘'-pres-≈̇-left (trans-unit-left (trans iden)) iden) ⟩
    trans (trans iden ∘' iden)
      ≈⟨ trans-pres-≈ (trans-unit-left iden) ⟩
    trans iden
      ≈⟨ trans-unit-right ⟩
    id'[ 𝒞₀ 𝒫 ]
      ∎
