{-# OPTIONS --safe #-}

open import Frame.IFrame
import Frame.CFrame as CF

module Presheaf.Functor.Cover.Joinable
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (IF   : IFrame W _⊆_)
  (let open CF IF)
  (K   : W → Set)
  (_∈_ : (v : W) {w : W} → K w → Set)
  (let open Core K _∈_)
  (CF  : CFrame)
  (JCF : Joinable CF)
  where

open IFrame IF
open CFrame CF
open Joinable JCF

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Cover.Base IF CF

open import PUtil
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; cong₂ to ≡-cong₂ ; subst to ≡-subst ; subst₂ to ≡-subst₂)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Data.Product
  using (∃; Σ; _×_; _,_; -,_)
  renaming (proj₁ to fst; proj₂ to snd)

open import PEUtil using (subst-application′′)
open import HEUtil

private
  variable
    w w' w'' u u' v v' : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' ℛ'' : Psh


join[_] : ∀ 𝒫 → 𝒞 𝒞 𝒫 →̇ 𝒞 𝒫
join[ 𝒫 ] = record
  { fun     = join-fun
  ; pres-≋  = join-fun-pres-≋
  ; natural = join-natural
  }
  where

  
  join-fam : {α : K w} (α[_] : ForAllW α K) 
      → ({u : W} (p : u ∈ α) → ForAllW α[ p ] (𝒫 ₀_))
      → ForAllW (⨆ α[_]) (𝒫 ₀_)
  join-fam {α = α} α[_] f {v} r = let (u , p , q) = ⨆-bwd-member α[_] r in f {u} p q
      
  join-fun : 𝒞-Fam (𝒞 𝒫) w → 𝒞-Fam 𝒫 w
  join-fun (elem α fam) = elem (⨆ (cov ∘ fam)) (join-fam (cov ∘ fam) (elems ∘ fam))

  opaque
    
    join-fam-pres-≋ : {α : K w} {α[_] : ForAllW α K} {α[_]' : ForAllW α K}
      → {f  : {u : W} (p : u ∈ α) → ForAllW α[ p ] (𝒫 ₀_)} -- "f" for "fan"
      → {f' : {u : W} (p' : u ∈ α) → ForAllW α[ p' ]' (𝒫 ₀_)}
      → ForAllW≅ α[_] α[_]'
      → ({u u' : W} {p : u ∈ α} {p' : u' ∈ α} → u ≡ u' → p ≅ p' → ForAllW[ 𝒫 ]≋ (f {u} p) (f' {u'} p'))
      → ForAllW[ 𝒫 ]≋ (join-fam α[_] f) (join-fam α[_]' f')
    join-fam-pres-≋  α[-]≋α'[-] f≋f'  r≅r' =
      let (u≡u' , p≅p' , q≅q') = ⨆-bwd-member-pres-≋ α[-]≋α'[-] r≅r' in f≋f' u≡u' p≅p' q≅q'
      
    join-fun-pres-≋ : {cx cx' : 𝒞-Fam (𝒞 𝒫) w}
      → cx 𝒞-≋[ 𝒞 𝒫 ] cx' → join-fun cx 𝒞-≋[ 𝒫 ] join-fun cx'
    join-fun-pres-≋ {cx = elem α fam} {cx' = elem α' fam'} (proof ≡-refl fam≋fam')
      = proof
          (⨆-pres-≋ (≡-refl , cov≋ ∘ fam≋fam') )
          (join-fam-pres-≋ (≡-refl , cov≋ ∘ fam≋fam') (λ { ≡-refl → elems≋ ∘ fam≋fam'}))
    
    join-natural : (i : w ⊆ w') (p : (𝒞 (𝒞 𝒫)) ₀ w) →
      (wk[ 𝒞 𝒫 ] i (join-fun p)) ≋[ 𝒞 𝒫 ] (join-fun (wk[ 𝒞 (𝒞 𝒫) ] i p))
    join-natural i (elem α fam) = {!!}

opaque
  unfolding 𝒞-map_ _≈̇_

  -- join is a natural transformation from the composition of functors 𝒞 ∘' 𝒞 to 𝒞
  join-natural : (t :  𝒫 →̇  𝒬) → join[ 𝒬 ] ∘' (𝒞-map (𝒞-map t)) ≈̇ (𝒞-map t) ∘' join[ 𝒫 ]
  join-natural {𝒫} {𝒬} t = λ _p → proof ≡-refl λ { ≅-refl → ≋[ 𝒬 ]-refl }

  --join-assoc : join[ 𝒫 ] ∘' (𝒞-map join[ 𝒫 ]) ≈̇ join[ 𝒫 ] ∘' join[ 𝒞 𝒫 ]
  --join-assoc {𝒫} (elem α fam) = proof {!!} {!!}

join = λ {𝒫} → join[ 𝒫 ]
