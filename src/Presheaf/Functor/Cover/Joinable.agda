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

-- "element tree"
ElTree[_] : (𝒫 : Psh) {α : K w} → (α[_] : ForAllW α K) → Set
ElTree[ 𝒫 ] {α = α} α[_] = ForAll∈ α (AllForW (𝒫 ₀_) ∘ α[_])

-- extensional equivalence for element trees
ElTree[_]≋ : (𝒫 : Psh) {α : K w} {α[_] : ForAllW α K} {α[_]' : ForAllW α K}
  → (f : ElTree[ 𝒫 ] α[_]) (f' : ElTree[ 𝒫 ] α[_]') → Set
ElTree[ 𝒫 ]≋ {α = α} f f' = {u u' : W} {p : u ∈ α} {p' : u' ∈ α}
  → u ≡ u' → p ≅ p' → ForAllW[ 𝒫 ]≋ (f {u} p) (f' {u'} p')

-- congruence for element trees
≋[_]-cong-ElTree : (𝒫 : Psh) {α : K w} {α[_] : ForAllW α K}
  → (f : ElTree[ 𝒫 ] α[_])
  → {u u' : W} (u≡u' : u ≡ u')
  → {p : u ∈ α} {p' : u' ∈ α} (p≅p' : p ≅ p')
  → {v : W} {q : v ∈ α[ p ]} {q' : v ∈ α[ p' ]} (q≅q' : q ≅ q')
  → f {u} p q ≋[ 𝒫 ] f {u'} p' q'
≋[ 𝒫 ]-cong-ElTree f ≡-refl ≅-refl ≅-refl = ≋[ 𝒫 ]-refl

-- weakening/refining element trees
wkElTree[_] : (𝒫 : Psh) {α : K w} {α[_] : ForAllW α K} {α' : K w'}
  → (is : α ≼ α')
  → ElTree[ 𝒫 ]  α[_]
  → ElTree[ 𝒫 ] (wkNFam is α[_])
wkElTree[ 𝒫 ] {α} {α[_]} α≼α' tr {u'} u'∈α' {v'} v'∈α[u'] = let
      (u , u∈α , u⊆u') = α≼α' u'∈α'
      (α'[p] , α[u]≼α'[u']) = refine u⊆u' α[ u∈α ]
      (v , v∈α[u] , v⊆v') = α[u]≼α'[u'] v'∈α[u']
      in wk[ 𝒫 ] v⊆v' (tr u∈α v∈α[u])

join[_] : ∀ 𝒫 → 𝒞 𝒞 𝒫 →̇ 𝒞 𝒫
join[ 𝒫 ] = record
  { fun     = join-fun
  ; pres-≋  = join-fun-pres-≋
  ; natural = join-fun-natural
  }
  where

  join-fam : {α : K w} (α[_] : ForAllW α K)
      → ElTree[ 𝒫 ] α[_]
      → ForAllW (⨆ α[_]) (𝒫 ₀_)
  join-fam {α = α} α[_] tr {v} v∈⨆α[-] = let
    (u , u∈α , v∈α[u]) = ⨆-bwd-member α[_] v∈⨆α[-]
    in tr {u} u∈α v∈α[u]

  join-fun : 𝒞-Fam (𝒞 𝒫) w → 𝒞-Fam 𝒫 w
  join-fun (elem α fam) = elem (⨆ (cov ∘ fam)) (join-fam (cov ∘ fam) (elems ∘ fam))

  opaque

    join-fam-pres-≋ : {α : K w} {α[_] : ForAllW α K} {α[_]' : ForAllW α K}
      → {tr  : ElTree[ 𝒫 ] α[_]} {tr' : ElTree[ 𝒫 ] α[_]'}
      → ForAllW≅ α[_] α[_]' → ElTree[ 𝒫 ]≋ tr tr'
      → ForAllW[ 𝒫 ]≋ (join-fam α[_] tr) (join-fam α[_]' tr')
    join-fam-pres-≋  α[-]≋α'[-] tr≋tr' r≅r' =
      let (u≡u' , p≅p' , q≅q') = ⨆-bwd-member-pres-≋ α[-]≋α'[-] r≅r'
      in tr≋tr' u≡u' p≅p' q≅q'

    join-fun-pres-≋ : {cx cx' : 𝒞-Fam (𝒞 𝒫) w}
      → cx 𝒞-≋[ 𝒞 𝒫 ] cx' → join-fun cx 𝒞-≋[ 𝒫 ] join-fun cx'
    join-fun-pres-≋ {cx = elem α fam} {cx' = elem α' fam'} (proof ≡-refl fam≋fam')
      = proof
          (⨆-pres-≋ (≡-refl , cov≋ ∘ fam≋fam'))
          (join-fam-pres-≋ (≡-refl , cov≋ ∘ fam≋fam') (λ { ≡-refl → elems≋ ∘ fam≋fam'}))

    join-fam-natural : {α : K w} {α' : K w'}
      → {α[_] : ForAllW α K} {tr : ElTree[ 𝒫 ] α[_]}
      → (α≼α' : α ≼ α')
      → ForAllW[ 𝒫 ]≋
          (wkElFam[ 𝒫 ] (⨆-pres-≼ α≼α' α[_]) (join-fam α[_] tr))
          (join-fam (wkNFam α≼α' α[_]) (wkElTree[ 𝒫 ] α≼α' tr))
    join-fam-natural {α = α} {α'} {α[_] = α[_]} {tr} α≼α' {v'} {v'∈⨆α'[-]} ≅-refl = let
      α'[_]                   = wkNFam α≼α' α[_]
      (v , v∈⨆α[-] , v⊆v')    = ⨆-pres-≼ α≼α' α[_] v'∈⨆α'[-] -- uses ⨆-fwd-member
      -- LHS stuff
      (u' , u'∈α' , v'∈α'[u']) = ⨆-bwd-member α'[_] v'∈⨆α'[-]
      (u , u∈α , u⊆u')         = α≼α' u'∈α'
      (α'[u'] , α[u]≼α'[u'])   = refine u⊆u' α[ u∈α ]
      (v , v∈α[u] , v⊆v')      = α[u]≼α'[u'] v'∈α'[u']
      -- RHS stuff
      (zᵤ , zᵤ∈α , v∈α[zᵤ])  = ⨆-bwd-member α[_] v∈⨆α[-]
      -- Equivalence
      (zᵤ≡u , zᵤ∈α≅u∈α , v∈α[zᵤ]≅v∈α[u]) = ⨆-fwd-bwd-id (u , u∈α , v∈α[u])
      open EqReasoning ≋[ 𝒫 ]-setoid in
      begin
        wkElFam[ 𝒫 ] (⨆-pres-≼ α≼α' α[_]) (join-fam α[_] tr) v'∈⨆α'[-]
          ≡⟨⟩ -- expand wkElFam
        wk[ 𝒫 ] v⊆v' (join-fam α[_] tr v∈⨆α[-])
          ≡⟨⟩ -- expand join-fam
        wk[ 𝒫 ] v⊆v' (tr {zᵤ} zᵤ∈α v∈α[zᵤ])
          ≈⟨ wk[ 𝒫 ]-pres-≋ v⊆v' (≋[ 𝒫 ]-cong-ElTree tr zᵤ≡u zᵤ∈α≅u∈α v∈α[zᵤ]≅v∈α[u]) ⟩
        wk[ 𝒫 ] v⊆v' (tr {u} u∈α v∈α[u])
          ≡⟨⟩ -- contract wkElTree
        wkElTree[ 𝒫 ] α≼α' tr u'∈α' v'∈α'[u']
          ≡⟨⟩ -- contract join-fam
        join-fam α'[_] (wkElTree[ 𝒫 ] α≼α' tr) v'∈⨆α'[-]
          ∎

    join-fun-natural : (i : w ⊆ w') (p : (𝒞 (𝒞 𝒫)) ₀ w) →
      wk[ 𝒞 𝒫 ] i (join-fun p) ≋[ 𝒞 𝒫 ] join-fun (wk[ 𝒞 (𝒞 𝒫) ] i p)
    join-fun-natural i (elem α fam) = let
      α[_] : NFam α
      α[_] = cov ∘ fam
      tr : {u : W} (p : u ∈ α) → ForAllW α[ p ] (𝒫 ₀_)
      tr = elems ∘ fam
      (rjα≡jrα , is≋is') = refine-coh-joinN i α α[_]
      in proof rjα≡jrα λ {v} {p} {p'} p≅p' →
        let open EqReasoning ≋[ 𝒫 ]-setoid
        in begin
          wkElFam[ 𝒫 ] (refine i $≼ (⨆ α[_])) (join-fam α[_] tr) p
            ≈⟨ wkElFam-pres-≋-left {𝒫  = 𝒫} is≋is' (join-fam α[_] tr) p≅p' ⟩
          wkElFam[ 𝒫 ] (⨆-pres-≼ (refine i $≼ α) α[_]) (join-fam α[_] tr) p'
            ≈⟨ join-fam-natural {tr = tr} (refine i $≼ α) ≅-refl ⟩
          join-fam (wkNFam (refine i $≼ α) α[_]) (wkElTree[ 𝒫 ] (refine i $≼ α) tr) p'
            ∎

opaque
  unfolding 𝒞-map_ _≈̇_

  -- join is a natural transformation from the composition of functors 𝒞 ∘' 𝒞 to 𝒞
  join-natural : (t :  𝒫 →̇  𝒬) → join[ 𝒬 ] ∘' (𝒞-map (𝒞-map t)) ≈̇ (𝒞-map t) ∘' join[ 𝒫 ]
  join-natural {𝒫} {𝒬} t = λ _p → proof ≡-refl λ { ≅-refl → ≋[ 𝒬 ]-refl }

  open import Presheaf.Functor.Cover.Base as B using ()

  -- join-assoc : join[ 𝒫 ] ∘' (𝒞-map join[ 𝒫 ]) ≈̇ join[ 𝒫 ] ∘' join[ 𝒞 𝒫 ]
  -- join-assoc {𝒫} (elem α fam) = proof joinN-assoc λ x → {!!}

join = λ {𝒫} → join[ 𝒫 ]
