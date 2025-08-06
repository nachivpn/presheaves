{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.CFrame as CF

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

module Presheaf.Functor.Cover.Pointed
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (IF   : IFrame W _⊆_)
  (let open CF IF)
  (𝒦   : KPsh)
  (let open KPsh 𝒦)
  (_∈_ : (v : W) {w : W} → K w → Set)
  (let open Core 𝒦 _∈_)
  (CF  : CFrame)
  (PCF : Pointed CF)
  where

open IFrame IF
open CFrame CF
open Pointed PCF

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Cover.Base IF CF

open import PUtil

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; subst to ≡-subst ; subst₂ to ≡-subst₂)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Data.Product
  using (∃; Σ; _×_; _,_; -,_)
  renaming (proj₁ to fst; proj₂ to snd)

private
  variable
    w w' w'' u u' v v' : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' ℛ'' : Psh


point[_] : ∀ 𝒫 → 𝒫 →̇ 𝒞 𝒫
point[ 𝒫 ] = record
  { fun     = point-fun
  ; pres-≋  = point-fun-pres-≋
  ; natural = point-fun-natural
  }
  where

  point-fam : 𝒫 ₀ w → ForAllW pointK[ w ] (𝒫 ₀_)
  point-fam x p = ≡-subst (𝒫 ₀_) (point∈ p) x

  point-fun : 𝒫 ₀ w → 𝒞-Fam 𝒫 w
  point-fun {w} x = elem pointK[ w ] (point-fam x)

  opaque
    point-fun-fam-pres-≋ : {x y : 𝒫 ₀ w} → x ≋[ 𝒫 ] y → ForAllW[ 𝒫 ]≋ pointK[ _ ] (point-fam x) (point-fam y)
    point-fun-fam-pres-≋ {w} x≋y p rewrite point∈ p = x≋y

    point-fun-pres-≋ : {x y : 𝒫 ₀ w} → x ≋[ 𝒫 ] y → point-fun x 𝒞-≋ point-fun y
    point-fun-pres-≋ {x = x} {y} x≋y = proof ≡-refl (point-fun-fam-pres-≋ x≋y)

    point-fun-natural : (i : w ⊆ w') (p : 𝒫 ₀ w)
      → wk[ 𝒞 𝒫 ] i (point-fun p) ≋[ 𝒞 𝒫 ] point-fun (wk[ 𝒫 ] i p)
    point-fun-natural i x = {!!}

point = λ {𝒫} → point[ 𝒫 ]
