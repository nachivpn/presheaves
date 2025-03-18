{-# OPTIONS --safe --without-K #-}
open import Frame.IFrame
import Frame.FDFrame as FDF

module Presheaf.Functor.Possibility.Monad
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

open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Possibility.Base DF
open import Presheaf.Functor.Possibility.Pointed DF
open import Presheaf.Functor.Possibility.Joinable DF

open import Presheaf.Functor.Possibility.Properties DF

open import PUtil

private
  variable
    𝒫 𝒬 : Psh

module Monadic {PDF : PointedDFrame} {JDF : JoinableDFrame} (MDF : MonadicDFrame PDF JDF) where

  open {-Pointed.-}Pointed PDF
  open {-Joinable.-}Joinable JDF

  open MonadicDFrame MDF

  opaque
    unfolding ◇-map_ ◼-map_

    squash-unit-left : squash[ 𝒫 ] ∘ point[ ◇ ◼ 𝒫 ]  ≈̇ ϵ[ 𝒫 ]
    squash-unit-left = proof-≈̇ λ (elem (w , r , bp))  → bp .apply-≋ (proof (Σ×-≡,≡,≡←≡ (R-join-unit-left r)))

    squash-unit-right : squash[ 𝒫 ] ∘ ◇-map (point[ ◼ 𝒫 ]) ≈̇ ϵ[ 𝒫 ]
    squash-unit-right = proof-≈̇ λ (elem (w , r , bp)) → bp .apply-≋ (proof (Σ×-≡,≡,≡←≡ (R-join-unit-right r)))

  opaque
    unfolding ◇-map_ ◼-map_ _≈̇_

    join-unit-left : join[ 𝒫 ] ∘ point[ ◇ 𝒫 ] ≈̇ id'[ ◇ 𝒫 ]
    join-unit-left {𝒫} = let open EqReasoning (→̇-setoid (◇ 𝒫) (◇ 𝒫)) in begin
      (squash[ ◇ 𝒫 ] ∘ ◇-map (◇-map η[ 𝒫 ])) ∘ point[ ◇ 𝒫 ]
        ≈⟨ ∘-assoc squash[ ◇ 𝒫 ] (◇-map (◇-map η[ 𝒫 ])) point[ ◇ 𝒫 ] ⟩
      squash[ ◇ 𝒫 ] ∘ ◇-map (◇-map η[ 𝒫 ]) ∘ point[ ◇ 𝒫 ]
        ≈˘⟨ ∘-pres-≈̇-right[ point[ ◇ ◼ ◇ 𝒫 ] ∘ ◇-map η[ 𝒫 ] , ◇-map (◇-map η[ 𝒫 ]) ∘ point[ ◇ 𝒫 ] ]
              squash[ ◇ 𝒫 ]
              (point-natural (◇-map η[ 𝒫 ]))
          ⟩
      squash[ ◇ 𝒫 ] ∘ point[ ◇ ◼ ◇ 𝒫 ] ∘ ◇-map η[ 𝒫 ]
        ≈˘⟨ ∘-assoc squash[ ◇ 𝒫 ] point[ ◇ ◼ ◇ 𝒫 ] (◇-map η[ 𝒫 ]) ⟩
      (squash[ ◇ 𝒫 ] ∘ point[ ◇ ◼ ◇ 𝒫 ]) ∘ ◇-map η[ 𝒫 ]
        ≈⟨ ∘-pres-≈̇-left[ squash[ ◇ 𝒫 ] ∘ point[ ◇ (◼ (◇ 𝒫)) ] , ϵ[ ◇ 𝒫 ] ]
             squash-unit-left
             (◇-map η[ 𝒫 ])
         ⟩
      ϵ[ ◇ 𝒫 ] ∘ ◇-map η[ 𝒫 ]
        ≈⟨ zig-zag₁ ⟩
      id'[ ◇ 𝒫 ]
        ∎

    join-unit-right : join[ 𝒫 ] ∘ ◇-map point[ 𝒫 ] ≈̇ id'[ ◇ 𝒫 ]
    join-unit-right {𝒫} = let open EqReasoning (→̇-setoid (◇ 𝒫) (◇ 𝒫)) in begin
      (squash[ ◇ 𝒫 ] ∘ ◇-map (◇-map η[ 𝒫 ])) ∘ ◇-map point[ 𝒫 ]
        ≈⟨ ∘-assoc squash[ ◇ 𝒫 ] (◇-map (◇-map η[ 𝒫 ])) (◇-map point[ 𝒫 ]) ⟩
      squash[ ◇ 𝒫 ] ∘ ◇-map (◇-map η[ 𝒫 ]) ∘ ◇-map point[ 𝒫 ]
        ≈˘⟨ ∘-pres-≈̇-right[ ◇-map (◇-map η[ 𝒫 ] ∘ point[ 𝒫 ]) , ◇-map (◇-map η[ 𝒫 ]) ∘ ◇-map point[ 𝒫 ] ]
              squash[ ◇ 𝒫 ]
              (◇-map-pres-∘ (◇-map η[ 𝒫 ]) point[ 𝒫 ])
          ⟩
      squash[ ◇ 𝒫 ] ∘ ◇-map (◇-map η[ 𝒫 ] ∘ point[ 𝒫 ])
        ≈˘⟨ ∘-pres-≈̇-right[ ◇-map (point[ ◼ ◇ 𝒫  ] ∘ η[ 𝒫 ]) , ◇-map (◇-map η[ 𝒫 ] ∘ point[ 𝒫 ]) ]
              squash[ ◇ 𝒫 ]
              (◇-map-pres-≈̇[ point[ ◼ ◇ 𝒫  ] ∘ η[ 𝒫 ] , ◇-map η[ 𝒫 ] ∘ point[ 𝒫 ] ] (point-natural η[ 𝒫 ]))
          ⟩
      squash[ ◇ 𝒫 ] ∘ ◇-map (point[ ◼ ◇ 𝒫  ] ∘ η[ 𝒫 ])
        ≈⟨ ∘-pres-≈̇-right[ ◇-map (point[ ◼ ◇ 𝒫  ] ∘ η[ 𝒫 ]) , ◇-map point[ ◼ ◇ 𝒫  ] ∘ ◇-map η[ 𝒫 ] ] squash[ ◇ 𝒫 ] (◇-map-pres-∘ point[ ◼ ◇ 𝒫  ] η[ 𝒫 ]) ⟩
      squash[ ◇ 𝒫 ] ∘ ◇-map point[ ◼ ◇ 𝒫  ] ∘ ◇-map η[ 𝒫 ]
        ≈˘⟨ ∘-assoc squash[ ◇ 𝒫 ] (◇-map point[ ◼ ◇ 𝒫  ]) (◇-map η[ 𝒫 ]) ⟩
      (squash[ ◇ 𝒫 ] ∘ ◇-map point[ ◼ ◇ 𝒫  ]) ∘ ◇-map η[ 𝒫 ]
        ≈⟨ ∘-pres-≈̇-left[ squash[ ◇ 𝒫 ] ∘ ◇-map point[ ◼ ◇ 𝒫  ] , ϵ[ ◇ 𝒫 ] ] squash-unit-right (◇-map η[ 𝒫 ]) ⟩
      ϵ[ ◇ 𝒫 ] ∘ ◇-map η[ 𝒫 ]
        ≈⟨ zig-zag₁ ⟩
      id'[ ◇ 𝒫 ]
        ∎

module ReflexiveTransitive {RDF : ReflexiveDFrame} {TDF : TransitiveDFrame} (RTDF : ReflexiveTransitiveDFrame RDF TDF) where

  open {-Pointed.-}Reflexive RDF
  open {-Joinable.-}Transitive TDF

  open ReflexiveTransitiveDFrame RTDF

  opaque
    unfolding ◇-map_

    join-unit-left : join[ 𝒫 ] ∘ point[ ◇ 𝒫 ] ≈̇ id'[ ◇ 𝒫 ]
    join-unit-left {𝒫} = proof-≈̇ λ p → proof
      (≡-refl
      , R-trans-unit-left _
      , ≋[ 𝒫 ]-refl)

    join-unit-right : join[ 𝒫 ] ∘ (◇-map point[ 𝒫 ]) ≈̇ id'[ ◇ 𝒫 ]
    join-unit-right {𝒫} = proof-≈̇ λ p → proof
      (≡-refl
      , R-trans-unit-right _
      , ≋[ 𝒫 ]-refl)
