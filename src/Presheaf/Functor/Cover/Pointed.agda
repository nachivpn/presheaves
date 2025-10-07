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

open import PUtil

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; subst to ≡-subst ; subst₂ to ≡-subst₂)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Data.Product
  using (∃; Σ; _×_; _,_; -,_)
  renaming (proj₁ to fst; proj₂ to snd)

open import PEUtil using (subst-application1′)

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
  point-fam x p = wk[ 𝒫 ] (pointK-family p) x

  point-fun : 𝒫 ₀ w → 𝒞-Fam 𝒫 w
  point-fun {w} x = elem pointK[ w ] (point-fam x)

  opaque

    point-fun-pres-≋ : {x y : 𝒫 ₀ w} → x ≋[ 𝒫 ] y → point-fun x 𝒞-≋ point-fun y
    point-fun-pres-≋ {x = x} {y} x≋y = proof ≡-refl λ p → wk[ 𝒫 ]-pres-≋ _ x≋y

    point-fam-natural : (i : w ⊆ w') (x : 𝒫 ₀ w)
      → ForAllW[ 𝒫 ]≋ pointK[ w' ] (wkElems[ 𝒫 ] (pointK-pres-⊆ i) (point-fam x) ) (point-fam (wk[ 𝒫 ] i x))
    point-fam-natural {w = w} {w'} i x p = let open EqReasoning ≋[ 𝒫 ]-setoid in begin
      wkElems[ 𝒫 ] (pointK-pres-⊆ i) (point-fam x) p
        ≡⟨⟩
      wk[ 𝒫 ] (⊆-trans i (pointK-family p)) (wk[ 𝒫 ] (pointK-family point∈[ w ]) x)
        ≈⟨ wk[ 𝒫 ]-pres-≋ _ (wk[ 𝒫 ]-pres-≡-≋ pointK-coh[ w ] ≋[ 𝒫 ]-refl) ⟩
      wk[ 𝒫 ] (⊆-trans i (pointK-family p)) (wk[ 𝒫 ] ⊆-refl[ w ] x)
        ≈⟨ wk[ 𝒫 ]-pres-≋ _ (wk[ 𝒫 ]-pres-refl x) ⟩
      wk[ 𝒫 ] (⊆-trans i (pointK-family p)) x
        ≈⟨ wk[ 𝒫 ]-pres-trans i (pointK-family p) x ⟩
      wk[ 𝒫 ] (pointK-family p) (wk[ 𝒫 ] i x)
        ∎

    point-fun-natural : (i : w ⊆ w') (x : 𝒫 ₀ w) → wk[ 𝒞 𝒫 ] i (point-fun x) ≋[ 𝒞 𝒫 ] point-fun (wk[ 𝒫 ] i x)
    point-fun-natural i x = let (k≡k' , is≋is') = factor-pres-point i
      in proof k≡k' λ p → let open EqReasoning ≋[ 𝒫 ]-setoid in begin
        ≡-subst (AllForW (𝒫 ₀_)) k≡k' (wkElems[ 𝒫 ] (factor i $⊆ pointK[ _ ]) (point-fam x)) p
          ≡⟨ ≡-cong (λ z → z p)
              (subst-application1′ {P = _ ⊆k_} {Q = AllForW (_₀_ 𝒫)}  wkElems[ 𝒫 ] {z = point-fam x} k≡k') ⟩
        (wkElems[ 𝒫 ] (≡-subst (_ ⊆k_) k≡k' (factor i $⊆ _ )) (point-fam x)) p
          ≈⟨ wkElems-pres-≋-left {𝒫  = 𝒫} is≋is' (point-fam x) p ⟩
        wkElems[ 𝒫 ] (pointK-pres-⊆ i) (point-fam x) p
          ≈⟨ point-fam-natural i x p ⟩
        point-fam (wk[ 𝒫 ] i x) p
          ∎

point = λ {𝒫} → point[ 𝒫 ]
