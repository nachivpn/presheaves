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
  where

open DFrame DF

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Possibility.Base DF

open import Relation.Binary.PropositionalEquality using (_≡_ ; cong) renaming (refl to ≡-refl ; sym to ≡-sym)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Data.Product using (_,_) renaming (proj₁ to fst ; proj₂ to snd)

open import PUtil

private
  variable
    w w' w'' v           : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' ℛ'' : Psh

module Pointed (PDF : PointedDFrame) where

  open PointedDFrame PDF

  ε[_] : ∀ 𝒫 → ◼ 𝒫 →̇ 𝒫
  ε[ 𝒫 ] = record
    { fun     = λ bp → bp .apply R-point
    ; pres-≋  = λ bp≋bp' → bp≋bp' .apply-≋ R-point
    ; natural = λ i bp → ≋[ 𝒫 ]-trans (bp .natural i R-point) (bp .apply-≋ (factor-pres-point i))
    }

  ε = λ {𝒫} → ε[ 𝒫 ]

  opaque
    ε-natural : (t : 𝒫 →̇ 𝒬) → ε[ 𝒬 ] ∘ (◼-map t) ≈̇ t ∘ ε[ 𝒫 ]
    ε-natural {𝒬 = 𝒬} t = record { proof = λ _bp → ≋[ 𝒬 ]-refl }

  point[_] : ∀ 𝒫 → 𝒫 →̇ ◇ 𝒫
  point[ 𝒫 ] = ε[ ◇ 𝒫 ] ∘ η[ 𝒫 ]

  opaque
    point-natural : (t : 𝒫 →̇ 𝒬) → point[ 𝒬 ] ∘ t ≈̇ ◇-map t ∘ point[ 𝒫 ]
    point-natural {𝒫} {𝒬} t = let open EqReasoning (→̇-setoid 𝒫 (◇ 𝒬)) in begin
      (ε ∘ η) ∘ t
        ≈⟨ ∘-assoc ε η t ⟩
      ε ∘ (η ∘ t)
        ≈⟨ ∘-pres-≈̇-right ε (η-natural t) ⟩
      ε ∘ (◼-map (◇-map t) ∘ η)
        ≈˘⟨ ∘-assoc ε (◼-map (◇-map t)) η ⟩
      (ε ∘ ◼-map (◇-map t)) ∘ η
        ≈⟨ ∘-pres-≈̇-left (ε-natural (◇-map t)) η ⟩
      (◇-map t ∘ ε) ∘ η
        ≈⟨ ∘-assoc (◇-map t) ε η ⟩
      ◇-map t ∘ (ε ∘ η)
        ∎

  point = λ {𝒫} → point[ 𝒫 ]

module Reflexive (RDF  : ReflexiveDFrame) where

  open ReflexiveDFrame RDF

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

  point = λ {𝒫} → point[ 𝒫 ]

  opaque
    -- point is a natural transformation from the identity functor to ◇
    point-natural : (t : 𝒫 →̇ 𝒬) → point[ 𝒬 ] ∘ t ≈̇ ◇-map t ∘ point[ 𝒫 ]
    point-natural {𝒫} {𝒬} t = record { proof = λ _p → ≋[ ◇ 𝒬 ]-refl }

    -- obs: point need not be well-pointed
    -- point-well-pointed : (t : 𝒫 →̇ ◇ 𝒬) → ◇-map point[ 𝒫 ] ≈̇ point[ ◇ 𝒫 ]

    -- obs: "The pointed endofunctor underlying a monad T is
    -- well-pointed if and only if T is idempotent."  [Proposition 3.1.,
    -- https://ncatlab.org/nlab/show/pointed+endofunctor]
