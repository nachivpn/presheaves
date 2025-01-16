{-# OPTIONS --safe --without-K #-}
open import Kripke.IFrame
import Kripke.FDFrame as FDF

module Presheaf.Functor.Possibility.Joinable
  {W   : Set}
  {_⊆_ : (w w' : W) → Set}
  {IF  : IFrame W _⊆_}
  {_R_ : (w v : W) → Set}
  (let open FDF IF _R_)
  (DF  : DFrame)
  (let open Definitions DF)
  where

open DFrame DF

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Presheaf.Base IF
open import Presheaf.Functor.Possibility.Base DF

open import PUtil

private
  variable
    w w' w'' v v' v'' : W
    𝒫 𝒫' 𝒬 𝒬'        : Psh

module Joinable (JDF : JoinableDFrame) where

  open JoinableDFrame JDF

  squash[_] : ∀ 𝒫 → ◇ ◇ ◼ 𝒫 →̇ 𝒫
  squash[ 𝒫 ] = record
    { fun     = squash-fun
    ; pres-≋  = squash-pres-≋
    ; natural = squash-natural
    }
    where
    squash-fun : ◇ (◇ (◼ 𝒫)) ₀ w → 𝒫 ₀ w
    squash-fun (elem (u , r1 , (elem (v , r2 , bp)))) = bp .apply (R-join r1 r2)

    opaque
      squash-pres-≋ : Pres-≋ (◇ (◇ (◼ 𝒫))) 𝒫 squash-fun
      squash-pres-≋ (proof (≡-refl , ≡-refl , (proof (≡-refl , ≡-refl , p≋p')))) = p≋p' .apply-≋ (R-join _ _)

      squash-natural : Natural (◇ (◇ (◼ 𝒫))) 𝒫 squash-fun
      squash-natural i (elem (_u , r1 , (elem (_v , r2 , bp)))) = ≋[ 𝒫 ]-trans (bp .natural i _) (bp .apply-≋ (factor-pres-R-join i r1 r2))

  opaque
    squash-natural : (t : 𝒫 →̇ 𝒬) → t ∘ squash[ 𝒫 ] ≈̇ squash[ 𝒬 ] ∘ (◇-map (◇-map (◼-map t)))
    squash-natural {𝒫} {𝒬} t = record { proof = λ _p → ≋[ 𝒬 ]-refl }

    squash-assoc : squash[ 𝒫 ] ∘ squash[ ◇ ◇ ◼ 𝒫 ] ≈̇ squash[ 𝒫 ] ∘ (◇-map (◇-map (◼-map squash[ 𝒫 ])))
    squash-assoc {𝒫} = squash-natural squash[ 𝒫 ]

  join[_] : ∀ 𝒫 → ◇ ◇ 𝒫 →̇ ◇ 𝒫
  join[ 𝒫 ] = squash[ ◇ 𝒫 ] ∘ ◇-map (◇-map η[ 𝒫 ])

  opaque
    join-natural : (t :  𝒫 →̇  𝒬) → join[ 𝒬 ] ∘ (◇-map (◇-map t)) ≈̇ (◇-map t) ∘ join[ 𝒫 ]
    join-natural {𝒫} {𝒬} t = record { proof = λ _p → proof (≡-refl , ≡-refl , t .natural _ _) }

module Transitive (TDF : TransitiveDFrame) where

  open TransitiveDFrame TDF

  join[_] : ∀ 𝒫 → ◇ ◇ 𝒫 →̇ ◇ 𝒫
  join[ 𝒫 ] = record
    { fun     = ◇-join-fun
    ; pres-≋  = ◇-join-fun-pres-≋
    ; natural = ◇-join-natural
    }
    where
    ◇-join-fun : ◇-Fam (◇ 𝒫) w  → ◇-Fam 𝒫 w
    ◇-join-fun (elem (u , r1 , (elem (v , r2 , p)))) = elem (v , R-trans r1 r2 , p)

    opaque
      ◇-join-fun-pres-≋ : {p p' : ◇-Fam (◇ 𝒫) w}
        → p ◇-≋[ ◇ 𝒫 ] p' → ◇-join-fun p ◇-≋[ 𝒫 ] ◇-join-fun p'
      ◇-join-fun-pres-≋ (proof (≡-refl , ≡-refl , (proof (≡-refl , ≡-refl , p≋p')))) = proof (≡-refl , ≡-refl , p≋p')

      ◇-join-natural : (i : w ⊆ w') (p : (◇ (◇ 𝒫)) ₀ w) →
        (wk[ ◇ 𝒫 ] i (◇-join-fun p)) ≋[ ◇ 𝒫 ] (◇-join-fun (wk[ ◇ (◇ 𝒫) ] i p))
      ◇-join-natural i (elem (_u , r1 , (elem (_v , r2 , _p)))) rewrite factor-pres-R-trans i r1 r2 = ≋[ ◇ 𝒫 ]-refl

  opaque
    -- join is a natural transformation from the composition of functors ◇ ∘ ◇ to ◇
    join-natural : (t :  𝒫 →̇  𝒬) → join[ 𝒬 ] ∘ (◇-map (◇-map t)) ≈̇ (◇-map t) ∘ join[ 𝒫 ]
    join-natural {𝒫} {𝒬} t = record { proof = λ _p → ≋[ ◇ 𝒬 ]-refl }

    join-assoc : join[ 𝒫 ] ∘ (◇-map join[ 𝒫 ]) ≈̇ join[ 𝒫 ] ∘ join[ ◇ 𝒫 ]
    join-assoc {𝒫} = record { proof = λ p → proof (≡-refl , ≡-sym (R-trans-assoc _ _ _) , ≋[ 𝒫 ]-refl) }

  join = λ {𝒫} → join[ 𝒫 ]
