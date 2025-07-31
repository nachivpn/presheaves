{-# OPTIONS --safe --without-K #-}
open import Frame.IFrame
import Frame.FDFrame as FDF

module Presheaf.Functor.Possibility.Strong.Joinable
  {W   : Set}
  {_⊆_ : (w w' : W) → Set}
  {IF  : IFrame W _⊆_}
  {_R_ : (w v : W) → Set}
  (let open FDF IF _R_)
  (DF  : DFrame)
  (let open Definitions DF)
  (IDF : InclusiveDFrame)
  where

open DFrame DF
open InclusiveDFrame IDF

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Possibility.Base DF
open import Presheaf.Functor.Possibility.Strong.Base IDF
open import Presheaf.Functor.Possibility.Joinable DF

private
  variable
    𝒫 𝒬 : Psh

module InclusiveJoinable (TDF : JoinableDFrame) (ITDF : InclusiveJoinableDFrame IDF TDF) where

  open {-Joinable.-}Joinable TDF
  open JoinableDFrame TDF
  open InclusiveJoinableDFrame ITDF

  opaque
    unfolding ◇-map_
    
    ◇-strong-join : join[ 𝒫 ×' 𝒬 ] ∘' (◇-map strength[ 𝒫 , 𝒬 ]) ∘' strength[ 𝒫 , ◇ 𝒬 ] ≈̇ strength[ 𝒫 , 𝒬 ] ∘' (id'[ 𝒫 ] ×'-map join[ 𝒬 ])
    ◇-strong-join {𝒫} {𝒬} = proof-≈̇ (λ x → proof (≡-refl , ≡-refl , proof ((let open EqReasoning ≋[ 𝒫 ]-setoid in begin
      wk[ 𝒫 ] (wit⊆ (R-join _ _)) (wk[ 𝒫 ] (R-to-⊆ _) (wk[ 𝒫 ] (R-to-⊆ _) (π₁' .apply x)))
        ≈˘⟨ wk[ 𝒫 ]-pres-≋ (wit⊆ (R-join _ _)) (wk[ 𝒫 ]-pres-trans _ _ _) ⟩
      wk[ 𝒫 ] (wit⊆ (R-join _ _)) (wk[ 𝒫 ] (⊆-trans (R-to-⊆ _) (R-to-⊆ _)) (π₁' .apply x))
        ≈˘⟨ wk[ 𝒫 ]-pres-trans _ _ _  ⟩
      wk[ 𝒫 ] (⊆-trans (⊆-trans (R-to-⊆ _) (R-to-⊆ _)) (wit⊆ (R-join _ _))) (π₁' .apply x)
        ≡˘⟨ cong (λ z → wk[ 𝒫 ] z (π₁' .apply x)) (R-to-⊆-pres-join _ _)  ⟩
      wk[ 𝒫 ] (R-to-⊆ (witR (R-join _ _))) (π₁' .apply x)
        ∎)
      , ≋[ 𝒬 ]-refl)))

module InclusiveTransitive (TDF : TransitiveDFrame) (ITDF : InclusiveTransitiveDFrame IDF TDF) where

  open {-Joinable.-}Transitive TDF
  open TransitiveDFrame TDF
  open InclusiveTransitiveDFrame ITDF

  opaque
    unfolding ◇-map_
    
    -- c.f. https://en.wikipedia.org/wiki/Strong_monad#/media/File:Strong_monad_multiplication.svg
    ◇-strong-join : join[ 𝒫 ×' 𝒬 ] ∘' (◇-map strength[ 𝒫 , 𝒬 ]) ∘' strength[ 𝒫 , ◇ 𝒬 ] ≈̇ strength[ 𝒫 , 𝒬 ] ∘' (id'[ 𝒫 ] ×'-map join[ 𝒬 ])
    ◇-strong-join {𝒫} {𝒬} = proof-≈̇ (λ x → proof (
      (≡-refl
      , ≡-refl
      , proof
        ((let open EqReasoning ≋[ 𝒫 ]-setoid in begin
          wk[ 𝒫 ] (R-to-⊆ _) (wk[ 𝒫 ] (R-to-⊆ _) (π₁' .apply x))
            ≈˘⟨ wk[ 𝒫 ]-pres-trans _ _ _ ⟩
          wk[ 𝒫 ] (⊆-trans (R-to-⊆ _) (R-to-⊆ _)) (π₁' .apply x)
            ≡˘⟨ cong (λ z → wk[ 𝒫 ] z (π₁' .apply x)) (R-to-⊆-pres-trans _ _) ⟩
          wk[ 𝒫 ] (R-to-⊆ (R-trans _ _)) (π₁' .apply x) ∎)
        , ≋[ 𝒬 ]-refl))))
