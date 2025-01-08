{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame
import Kripke.FDFrame as FDF

module Presheaf.Functor.Possibility.1Pointed
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  {IF   : IFrame W _⊆_}
  {_R_  : (w v : W) → Set}
  (let open FDF IF _R_)
  {DF   : DFrame}
  (let open Definitions DF)
  (SDF  : SerialDFrame)
  where

open DFrame DF
open SerialDFrame SDF

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Possibility.Base DF

open import Relation.Binary.PropositionalEquality using (_≡_ ; cong) renaming (refl to ≡-refl ; sym to ≡-sym)
open import Data.Product using (_,_) renaming (proj₁ to fst ; proj₂ to snd)

open import PUtil using (Σ-≡,≡←≡)

point₁ : ⊤' →̇ ◇ ⊤'
point₁ = record
  { fun     = point₁-fun
  ; pres-≋  = point₁-fun-pres-≋
  ; natural = point₁-fun-natural
  }
  where

  point₁-fun : {w : W} → ⊤' ₀ w → ◇-Fam ⊤' w
  point₁-fun {w} x = elem (serialW w , serialR w , _)

  opaque
    point₁-fun-pres-≋ : Pres-≋ ⊤' (◇ ⊤') point₁-fun
    point₁-fun-pres-≋ x≋y = ≋[ ◇ ⊤' ]-refl

    point₁-fun-natural : Natural ⊤' (◇ ⊤') point₁-fun
    point₁-fun-natural i _ = let (p , q) = Σ-≡,≡←≡ (factor-pres-serial' i)
      in proof (p , q , ≡-refl)
