{-# OPTIONS --safe --without-K #-}
open import Kripke.IFrame
import Kripke.FDFrame as FDF

module Presheaf.Functor.Possibility.Strong.Pointed
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

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Possibility.Base DF
open import Presheaf.Functor.Possibility.Strong.Base IDF

open import Relation.Binary.PropositionalEquality using (_≡_ ; cong ; cong₂) renaming (refl to ≡-refl ; sym to ≡-sym)
open import Data.Product using (_,_) renaming (proj₁ to fst ; proj₂ to snd)
import Relation.Binary.Reasoning.Setoid as EqReasoning

private
  variable
    𝒫 𝒫' 𝒬 𝒬' : Psh

module Reflexive (RDF : ReflexiveDFrame) (IRDF : InclusiveReflexiveDFrame IDF RDF) where

  open ReflexiveDFrame RDF
  open InclusiveReflexiveDFrame IRDF

  open import Presheaf.Functor.Possibility.Pointed RDF
  
  opaque
    ◇-strong-point : strength[ 𝒫 , 𝒬 ] ∘ id'[ 𝒫 ] ×'-map point[ 𝒬 ] ≈̇ point[ 𝒫 ×' 𝒬 ]
    ◇-strong-point {𝒫} {𝒬} = record { proof = λ p×◇q → let p = π₁' .apply p×◇q in proof
      (≡-refl
      , ≡-refl
      , proof
        ((let open EqReasoning ≋[ 𝒫 ]-setoid in begin
          wk[ 𝒫 ] (R-to-⊆ R-refl) p   ≡⟨ cong₂ wk[ 𝒫 ] R-to-⊆-pres-refl ≡-refl ⟩
          wk[ 𝒫 ] (⊆-refl) p          ≈⟨ wk[ 𝒫 ]-pres-refl p ⟩
          p                           ∎)
        , ≋[ 𝒬 ]-refl)) }
