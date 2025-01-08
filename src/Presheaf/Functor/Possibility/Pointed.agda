{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame
import Kripke.FDFrame as FDF

module Presheaf.Functor.Possibility.Pointed
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  {IF   : IFrame W _⊆_}
  {_R_  : (w v : W) → Set}
  (let open FDF IF _R_)
  {DF   : DFrame}
  (let open Definitions DF)
  (RDF : ReflexiveDFrame)
  where

open DFrame DF
open ReflexiveDFrame RDF

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Possibility.Base DF

open import Relation.Binary.PropositionalEquality using (_≡_ ; cong) renaming (refl to ≡-refl ; sym to ≡-sym)
open import Data.Product using (_,_) renaming (proj₁ to fst ; proj₂ to snd)

private
  variable
    w w' w'' v           : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' ℛ'' : Psh

point[_] : ∀ 𝒫 → 𝒫 →̇ ◇ 𝒫
point[ 𝒫 ] = record
  { fun     = ◇-point-fun
  ; pres-≋  = ◇-point-fun-pres-≋
  ; natural = ◇-point-fun-natural
  }
  where

  ◇-point-fun : 𝒫 ₀ w → ◇-Fam 𝒫 w
  ◇-point-fun x = elem (_ , (R-refl[ _ ] , x))

  opaque
    ◇-point-fun-pres-≋ : {x y : 𝒫 ₀ w} → x ≋[ 𝒫 ] y → ◇-point-fun x ◇-≋ ◇-point-fun y
    ◇-point-fun-pres-≋ x≋y = proof (≡-refl , ≡-refl , x≋y)

    ◇-point-fun-natural : (i : w ⊆ w') (p : 𝒫 ₀ w)
      → wk[ ◇ 𝒫 ] i (◇-point-fun p) ≋[ ◇ 𝒫 ] ◇-point-fun (wk[ 𝒫 ] i p)
    ◇-point-fun-natural w _p rewrite (factor-pres-R-refl w) = proof (≡-refl , ≡-refl , ≋[ 𝒫 ]-refl)

opaque
  -- point is a natural transformation from the identity functor to ◇
  point-natural : (t : 𝒫 →̇ 𝒬) → point[ 𝒬 ] ∘ t ≈̇ ◇-map t ∘ point[ 𝒫 ]
  point-natural {𝒫} {𝒬} t = record { proof = λ _p → ≋[ ◇ 𝒬 ]-refl }

  -- obs: point need not be well-pointed
  -- point-well-pointed : (t : 𝒫 →̇ ◇ 𝒬) → ◇-map point[ 𝒫 ] ≈̇ point[ ◇ 𝒫 ]

  -- obs: "The pointed endofunctor underlying a monad T is
  -- well-pointed if and only if T is idempotent."  [Proposition 3.1.,
  -- https://ncatlab.org/nlab/show/pointed+endofunctor]


point = λ {𝒫} → point[ 𝒫 ]
