{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame
import Kripke.FDFrame as FDF

module Presheaf.Functor.Possibility.Base
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  {IF   : IFrame W _⊆_}
  {_R_  : (w v : W) → Set}
  (let open FDF IF _R_)
  (DF   : DFrame)
  where

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF

open DFrame DF
open import Kripke.FDFrame.Properties DF

open import PUtil

open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (isEquivalence to ≡-equiv)

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

private
  variable
    w w' w'' v v' v''     : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' ℛ'' : Psh

-- type \di2 for ◇
record ◇-Fam (𝒫 : Psh) (w : W) : Set where
  constructor elem
  field
    triple : w R-× (𝒫 ₀_)

open ◇-Fam public

record _◇-≋_ {𝒫 : Psh} {w : W} (x y : ◇-Fam 𝒫 w) : Set where
  constructor proof
  field
    pw : let (v , r , p) = x .triple ; (v' , r' , p') = y. triple
      in ∃ λ v≡v' → subst (_ R_) v≡v' r ≡ r' × subst (𝒫 ₀_) v≡v' p ≋[ 𝒫 ] p'

open _◇-≋_ public

◇-≋-refl : Reflexive (_◇-≋_ {𝒫} {w})
◇-≋-refl {𝒫} = proof (≡-refl , ≡-refl , ≋[ 𝒫 ]-refl)

◇-≋-sym : Symmetric (_◇-≋_ {𝒫} {w})
◇-≋-sym {𝒫} (proof (≡-refl , ≡-refl , p)) = proof (≡-refl , ≡-refl , ≋[ 𝒫 ]-sym p)

◇-≋-trans : Transitive (_◇-≋_ {𝒫} {w})
◇-≋-trans {𝒫} (proof (≡-refl , ≡-refl , p)) (proof (≡-refl , ≡-refl , q)) = proof (≡-refl , ≡-refl , ≋[ 𝒫 ]-trans p q)

≡-to-◇-≋ : {x y : ◇-Fam 𝒫 w} → x ≡ y → x ◇-≋ y
≡-to-◇-≋ ≡-refl = ◇-≋-refl

◇-≋[]-syn : (𝒫 : Psh) → (x y : ◇-Fam 𝒫 w) → Set
◇-≋[]-syn {w = w} 𝒫 = _◇-≋_ {𝒫} {w}

syntax ◇-≋[]-syn 𝒫 x y = x ◇-≋[ 𝒫 ] y

---------------------
-- ◇ 𝒫 is a presheaf
---------------------

◇_ : (𝒫 : Psh) → Psh
◇ 𝒫 = record
         { Fam           = ◇-Fam 𝒫
         ; _≋_           = _◇-≋_
         ; ≋-equiv       = λ _ → ◇-≋-equiv
         ; wk            = wk-◇
         ; wk-pres-≋     = wk-◇-pres-≋
         ; wk-pres-refl  = wk-◇-pres-refl
         ; wk-pres-trans = wk-◇-pres-trans
         }
   where

   ◇-≋-equiv : IsEquivalence (_◇-≋_ {𝒫} {w})
   ◇-≋-equiv = record
     { refl  = ◇-≋-refl
     ; sym   = ◇-≋-sym
     ; trans = ◇-≋-trans
     }

   wk-◇ : w ⊆ w' → ◇-Fam 𝒫 w → ◇-Fam 𝒫 w'
   wk-◇ i (elem (v , r , p)) = elem (factorW i r , factorR i r , wk[ 𝒫 ] (factor⊆ i r) p)

   opaque
     wk-◇-pres-≋ : (i : w ⊆ w') {x y : ◇-Fam 𝒫 w} → x ◇-≋ y → wk-◇ i x ◇-≋ wk-◇ i y
     wk-◇-pres-≋ _i (proof (≡-refl , ≡-refl , p≋p')) = proof (≡-refl , ≡-refl , wk[ 𝒫 ]-pres-≋ _ p≋p')

     wk-◇-pres-refl : (x : ◇-Fam 𝒫 w) → wk-◇ ⊆-refl x ◇-≋ x
     wk-◇-pres-refl (elem (v , r , p)) rewrite factor-pres-⊆-refl r = proof (≡-refl , (≡-refl , wk[ 𝒫 ]-pres-refl p))

     wk-◇-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (x : ◇-Fam 𝒫 w)
       → wk-◇ (⊆-trans i i') x ◇-≋ wk-◇ i' (wk-◇ i x)
     wk-◇-pres-trans i i' (elem (v , r , p)) rewrite factor-pres-⊆-trans i i' r = proof (≡-refl , (≡-refl , wk[ 𝒫 ]-pres-trans _ _ p))

---------------------------
-- ◇ is a presheaf functor
---------------------------

◇-map-fun : (f : {w : W} → 𝒫 ₀ w → 𝒬 ₀ w) → ({w : W} → ◇-Fam 𝒫 w → ◇-Fam 𝒬 w)
◇-map-fun f (elem (v , r , p)) = elem (v , r , f p)

opaque
  ◇-map-fun-pres-≋ : {f : {w : W} → 𝒫 ₀ w → 𝒬 ₀ w} (f-pres-≋ : Pres-≋ 𝒫 𝒬 f) → Pres-≋ (◇ 𝒫) (◇ 𝒬) (◇-map-fun f)
  ◇-map-fun-pres-≋ f-pres-≋ (proof (≡-refl , ≡-refl , p≋p')) = proof (≡-refl , ≡-refl , f-pres-≋ p≋p')

  ◇-map-natural : {f : {w : W} → 𝒫 ₀ w → 𝒬 ₀ w} (f-natural : Natural 𝒫 𝒬 f) → Natural (◇ 𝒫) (◇ 𝒬) (◇-map-fun f)
  ◇-map-natural f-natural i (elem (v , r , p)) = proof (≡-refl , (≡-refl , f-natural _ p))

  ◇-map-fun-pres-≈̇ : {t t' : 𝒫 →̇ 𝒬} → t ≈̇ t' → (p : ◇-Fam 𝒫 w) → ◇-map-fun (t .apply) p ◇-≋[ 𝒬 ] ◇-map-fun (t' .apply) p
  ◇-map-fun-pres-≈̇ {𝒫} t≈̇t' (elem (v , r , p)) = proof (≡-refl , (≡-refl , apply-sq t≈̇t' ≋[ 𝒫 ]-refl))

◇-map_ : {𝒫 𝒬 : Psh} → (t : 𝒫 →̇ 𝒬) → (◇ 𝒫 →̇ ◇ 𝒬)
◇-map_ {𝒫} {𝒬} t = record
  { fun     = ◇-map-fun (t .apply)
  ; pres-≋  = ◇-map-fun-pres-≋ (t .apply-≋)
  ; natural = ◇-map-natural (t .natural)
  }

opaque
  ◇-map-pres-≈̇ : {𝒫 𝒬 : Psh} {t t' : 𝒫 →̇ 𝒬} → t ≈̇ t' → ◇-map t ≈̇ ◇-map t'
  ◇-map-pres-≈̇ t≈̇t' = record { proof = λ p → ◇-map-fun-pres-≈̇ t≈̇t' p }

  ◇-map-pres-id : {𝒫 : Psh} → ◇-map id'[ 𝒫 ] ≈̇ id'
  ◇-map-pres-id = record { proof = λ p → ◇-≋-refl }

  ◇-map-pres-∘ : {𝒫 𝒬 ℛ : Psh} (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → ◇-map (t' ∘ t) ≈̇ ◇-map t' ∘ ◇-map t
  ◇-map-pres-∘ _t' _t = record { proof = λ p → ◇-≋-refl }

---------------------------------------------------
-- _D is a contravariant presheaf-valued functor
---------------------------------------------------

--
-- Observe: `-D_` might as well have been
--
-- -D_ : (v : W) → Psh
-- -D v = ◇ (v ⊆-)
--
-- TODO: should it be redefined? why (not)?
--

-D_ : (v : W) → Psh
-D v = record
  { Fam           = _D v
  ; _≋_           = _≡_
  ; ≋-equiv       = λ _ → ≡-equiv
  ; wk            = _ᵢ∙_
  ; wk-pres-≋     = λ i → cong (i ᵢ∙_)
  ; wk-pres-refl  = ᵢ∙-pres-⊆-refl
  ; wk-pres-trans = ᵢ∙-pres-⊆-trans
  }

-D-mapᵒ : w ⊆ v → (-D v) →̇ (-D w)
-D-mapᵒ i = record
  { fun     = _∙ᵢ i
  ; pres-≋  = cong (_∙ᵢ i)
  ; natural = λ i' d → ≡-sym (∙-assoc i' d i)
  }

opaque
  -D-mapᵒ-pres-refl : -D-mapᵒ ⊆-refl[ w ] ≈̇ id'
  -D-mapᵒ-pres-refl = record { proof = ∙ᵢ-pres-⊆-refl }

  -D-mapᵒ-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') → -D-mapᵒ (⊆-trans i i') ≈̇ -D-mapᵒ i ∘ -D-mapᵒ i'
  -D-mapᵒ-pres-trans i i' = record { proof = λ d → ∙ᵢ-pres-⊆-trans d i' i }

-------------------------
-- ◼ is presheaf functor
-------------------------

◼_ : Psh → Psh
◼_ 𝒫 = record
  { Fam           = λ v → -D v →̇ 𝒫
  ; _≋_           = _≈̇_
  ; ≋-equiv       = λ _ → ≈̇-equiv
  ; wk            = λ i f → f ∘ -D-mapᵒ i
  ; wk-pres-≋     = λ i x≋y → ∘-pres-≈̇-left x≋y (-D-mapᵒ i)
  ; wk-pres-refl  = λ f → ≈̇-trans (∘-pres-≈̇-right f -D-mapᵒ-pres-refl) (∘-unit-right _ f)
  ; wk-pres-trans = λ i i' f → ≈̇-trans (∘-pres-≈̇-right f (-D-mapᵒ-pres-trans i i')) (≈̇-sym (∘-assoc f (-D-mapᵒ i) (-D-mapᵒ i')) )
  }

◼-map_ : {𝒫 𝒬 : Psh} → (t : 𝒫 →̇ 𝒬) → (◼ 𝒫 →̇ ◼ 𝒬)
◼-map_ {𝒫} {𝒬} t = record
 { fun     = t ∘_
 ; pres-≋  = ∘-pres-≈̇-right t
 ; natural = λ i f → record { proof = λ d → ≋[ 𝒬 ]-refl }
 }

opaque
  ◼-map-pres-≈̇ : {𝒫 𝒬 : Psh} {f g : 𝒫 →̇ 𝒬} → f ≈̇ g → ◼-map f ≈̇ ◼-map g
  ◼-map-pres-≈̇ f≈̇g = record { proof = ∘-pres-≈̇-left f≈̇g }

  ◼-map-pres-id : {𝒫 : Psh} → ◼-map id'[ 𝒫 ] ≈̇ id'
  ◼-map-pres-id = record { proof = ∘-unit-left _ }

  ◼-map-pres-∘ : {𝒫 𝒬 ℛ : Psh} (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → ◼-map (t' ∘ t) ≈̇ ◼-map t' ∘ ◼-map t
  ◼-map-pres-∘ {𝒫} {ℛ = ℛ} t' t = record { proof = ∘-assoc t' t }

---------
-- ◇ ⊣ ◼
---------

η[_] : ∀ 𝒫 → 𝒫 →̇ ◼ ◇ 𝒫
η[ 𝒫 ] = record
  { fun = λ p →
    record
      { fun     = η-fun p
      ; pres-≋  = η-pres-≋ ≋[ 𝒫 ]-refl
      ; natural = λ i d → proof (≡-refl , ≡-refl , ≋[ 𝒫 ]-sym (wk[ 𝒫 ]-pres-trans _ _ p))
      }
  ; pres-≋  = λ p≋p' → record { proof = λ _ → η-pres-≋ p≋p' ≡-refl }
  ; natural = λ i p → record { proof = λ d → proof (≡-refl , ≡-refl , wk[ 𝒫 ]-pres-trans i _ p) }
  }
  where
    η-fun : 𝒫 ₀ v → w D v → ◇-Fam 𝒫 w
    η-fun p d = elem (witW d , witR d , wk[ 𝒫 ] (wit⊆ d) p)

    η-pres-≋ : {d d' : w' D v } {p p' : 𝒫 ₀ v} → p ≋[ 𝒫 ] p' → d ≡ d' → η-fun p d ◇-≋[ 𝒫 ] η-fun p' d'
    η-pres-≋ p≋p' d≡d' rewrite d≡d' = proof (≡-refl , ≡-refl , wk[ 𝒫 ]-pres-≋ _ p≋p')

opaque
  η-natural : (t : 𝒫 →̇ 𝒬) → η[ 𝒬 ] ∘ t ≈̇ (◼-map (◇-map t)) ∘ η[ 𝒫 ]
  η-natural t = record { proof = λ p → record { proof = λ d → proof (≡-refl , ≡-refl , t .natural _ p) } }

ϵ[_] : ∀ 𝒫 → ◇ ◼ 𝒫 →̇ 𝒫
ϵ[ 𝒫 ] = record
  { fun     = ϵ-fun
  ; pres-≋  = ϵ-pres-≋
  ; natural = ϵ-natural
  }
  where
    ϵ-fun : ◇-Fam (◼ 𝒫) w → 𝒫 ₀ w
    ϵ-fun (elem (v , r , f)) = f .apply (R-to-D r)

    ϵ-pres-≋ : Pres-≋ (◇ (◼ 𝒫)) 𝒫 ϵ-fun
    ϵ-pres-≋ (proof (≡-refl , ≡-refl , f≋f')) = f≋f' .apply-≋ _

    ϵ-natural : Natural (◇ (◼ 𝒫)) 𝒫 ϵ-fun
    ϵ-natural i (elem (v , r , f)) = ≋[ 𝒫 ]-trans (f .natural i _) (f .apply-≋ (Σ×-≡,≡,≡→≡ (-, ≡-refl , ⊆-trans-unit _)))

opaque
  ϵ-natural : (t : 𝒫 →̇ 𝒬) → t ∘ ϵ[ 𝒫 ] ≈̇ ϵ[ 𝒬 ] ∘ (◇-map (◼-map t))
  ϵ-natural {𝒫} {𝒬} t = record { proof = λ p → ≋[ 𝒬 ]-refl }

η = λ {𝒫} → η[ 𝒫 ]
ϵ = λ {𝒫} → ϵ[ 𝒫 ]

box : (◇ 𝒫 →̇ 𝒬) → (𝒫 →̇ ◼ 𝒬)
box {𝒫} {𝒬} t = ◼-map t ∘ η[ 𝒫 ]

unbox : (𝒫 →̇ ◼ 𝒬) → (◇ 𝒫 →̇ 𝒬)
unbox {𝒫} {𝒬} t = ϵ[ 𝒬 ] ∘ ◇-map t

opaque
  box-natural : (t : ◇ 𝒫 →̇ 𝒬) (u : 𝒫' →̇ 𝒫) → box t ∘ u ≈̇ box (t ∘ (◇-map u))
  box-natural {𝒫} {𝒬} {𝒫'} t u = let open EqReasoning (→̇-setoid 𝒫' (◼ 𝒬)) in begin
    (◼-map t ∘ η[ 𝒫 ]) ∘ u
      ≈⟨ ∘-assoc (◼-map t) η u ⟩
    ◼-map t ∘ (η[ 𝒫 ] ∘ u)
      ≈⟨ ∘-pres-≈̇-right (◼-map t) (η-natural u) ⟩
    ◼-map t ∘ (◼-map (◇-map u) ∘ η[ 𝒫' ])
      ≈˘⟨ ∘-assoc (◼-map t) (◼-map (◇-map u)) η[ 𝒫' ] ⟩
    (◼-map t ∘ ◼-map (◇-map u)) ∘ η[ 𝒫' ]
      ≈˘⟨ ∘-pres-≈̇-left (◼-map-pres-∘ t (◇-map u)) η[ 𝒫' ] ⟩
    ◼-map (t ∘ ◇-map u) ∘ η[ 𝒫' ] ∎
