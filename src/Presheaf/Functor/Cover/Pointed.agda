{-# OPTIONS --safe #-}

open import Frame.IFrame
import Frame.CFrame as CF

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

module Presheaf.Functor.Cover.Pointed
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (IF   : IFrame W _⊆_)
  (let open CF IF)
  (K   : W → Set)
  (_∈_ : (v : W) {w : W} → K w → Set)
  (let open Core K _∈_)
  (CF  : CFrame)
  (PCF : Pointed CF)
  where

open IFrame IF
open CFrame CF
open Pointed PCF

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Cover.Base IF CF

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; subst to ≡-subst ; subst₂ to ≡-subst₂)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Data.Product
  using (∃; Σ; _×_; _,_; -,_)
  renaming (proj₁ to fst; proj₂ to snd)

open import PEUtil using (subst-application1′)
open import HEUtil using (≅-refl)

private
  variable
    w w' w'' u u' v v' : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' ℛ'' : Psh

pointElFam[_] : (𝒫 : Psh) → 𝒫 ₀ w → ForAllW pointN[ w ] (𝒫 ₀_)
pointElFam[ 𝒫 ]  = singleFam[ 𝒫 ₀_ ]

point[_] : ∀ 𝒫 → 𝒫 →̇ 𝒞 𝒫
point[ 𝒫 ] = record
  { fun     = point-fun
  ; pres-≋  = point-fun-pres-≋
  ; natural = point-fun-natural
  }
  where

  opaque
    pointElFam-pres-≋ : {x y : 𝒫 ₀ w} → x ≋[ 𝒫 ] y → ElFam[ 𝒫 ]≋ (pointElFam[ 𝒫 ] x) (pointElFam[ 𝒫 ] y)
    pointElFam-pres-≋ {w} x≋y {v} {p} {p'} ≅-refl rewrite pointN-bwd-unique p = x≋y

    pointElFam-natural : (i : w ⊆ w') (x : 𝒫 ₀ w)
      → ElFam[ 𝒫 ]≋ (wkElFam[ 𝒫 ] (pointN-pres-≼ i) (pointElFam[ 𝒫 ] x)) (pointElFam[ 𝒫 ] (wk[ 𝒫 ] i x))
    pointElFam-natural {w = w} {w'} i x {v} {p} {.p} ≅-refl
      rewrite pointN-bwd-unique p
      | pointN-bwd-unique pointN-fwd-member[ w ]
      = ≋[ 𝒫 ]-refl
      
  point-fun : 𝒫 ₀ w → 𝒞-Fam 𝒫 w
  point-fun {w} x = elem pointN[ w ] (pointElFam[ 𝒫 ] x)

  opaque

    point-fun-pres-≋ : {x y : 𝒫 ₀ w} → x ≋[ 𝒫 ] y → point-fun x 𝒞-≋ point-fun y
    point-fun-pres-≋ {x = x} {y} x≋y = proof ≡-refl (pointElFam-pres-≋ x≋y)

    point-fun-natural : (i : w ⊆ w') (x : 𝒫 ₀ w) → wk[ 𝒞 𝒫 ] i (point-fun x) ≋[ 𝒞 𝒫 ] point-fun (wk[ 𝒫 ] i x)
    point-fun-natural i x = let (k≡k' , is≋is') = refine-coh-pointN i
      in proof k≡k' λ {v} {p} {p'} p≅p' → let open EqReasoning ≋[ 𝒫 ]-setoid in begin
        wkElFam[ 𝒫 ] (refine i $≼ _) (pointElFam[ 𝒫 ] x) p
          ≈⟨ wkElFam-pres-≋-left {𝒫  = 𝒫} is≋is' (pointElFam[ 𝒫 ] x) p≅p' ⟩
        wkElFam[ 𝒫 ] (pointN-pres-≼ i) (pointElFam[ 𝒫 ] x) p'
          ≈⟨ pointElFam-natural i x ≅-refl ⟩
        pointElFam[ 𝒫 ] (wk[ 𝒫 ] i x) p'
          ∎

point = λ {𝒫} → point[ 𝒫 ]


